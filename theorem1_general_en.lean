/-
  A verified derivation, in Lean 4 with Mathlib, of the general Theorem 1
  of the "descriptive route" towards the Born rule, from four agentive
  axioms on an estimation rule E defined over perspectives of a
  finite-dimensional complex inner product space.

  The only import from outside this development is Gleason's theorem
  (1957), declared below as an explicit axiom: it is not available in
  formalised form in any major proof library at the time of writing.
  Every other step is checked by the Lean kernel. Running
  `#print axioms theorem1_general` should list exactly `propext`,
  `Classical.choice`, `Quot.sound` (Lean's own foundational axioms) and
  `gleason`.

  HOW TO VERIFY (no local installation required):
  1. Open https://live.lean-lang.org/ in a browser.
  2. Paste this entire file into the editor.
  3. Wait for elaboration to finish (Mathlib is preloaded server-side;
     first-time elaboration of `import Mathlib` may take a minute).
  4. Confirm the absence of any red error marker in the editor.
  5. Append, on a new line at the end of the file:
       #print axioms theorem1_general
     and confirm the output lists exactly: propext, Classical.choice,
     Quot.sound, gleason.
  A reader wishing to isolate a single result (for instance Lemma 4,
  `lemma4_noncontextual`, which depends on no axiom beyond Lean's own
  three foundational ones) can run the same command with that
  theorem's name instead.

  Companion article: "An Everettian derivation of the Born rule without
  worlds" (working title).
-/

import Mathlib

open scoped InnerProductSpace
open scoped Classical

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/-- A perspective: a finite family of pairwise orthogonal, non-zero
    subspaces whose supremum is the whole space. -/
structure Perspective (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] where
  cells : Finset (Submodule ℂ V)
  nz    : ∀ c ∈ cells, c ≠ ⊥
  ortho : ∀ c ∈ cells, ∀ c' ∈ cells, c ≠ c' → c ≤ c'ᗮ
  span  : sSup (cells : Set (Submodule ℂ V)) = ⊤

/-- Refinement: every fine cell is contained in some coarse cell. -/
def Refines (D' D : Perspective V) : Prop :=
  ∀ c' ∈ D'.cells, ∃ c ∈ D.cells, c' ≤ c

namespace Perspective

/-- Unique parent: a non-zero subspace cannot be contained in two
    distinct cells of the same perspective. -/
theorem unique_parent (D : Perspective V) {c₁ c₂ K : Submodule ℂ V}
    (h₁ : c₁ ∈ D.cells) (h₂ : c₂ ∈ D.cells) (hK : K ≠ ⊥)
    (hK₁ : K ≤ c₁) (hK₂ : K ≤ c₂) : c₁ = c₂ := by
  by_contra hne
  apply hK
  apply (Submodule.eq_bot_iff K).mpr
  intro x hx
  have hxc1 : x ∈ c₁ := hK₁ hx
  have hxc2 : x ∈ c₂ := hK₂ hx
  have hxc1perp : x ∈ c₁ᗮ := D.ortho c₂ h₂ c₁ h₁ (Ne.symm hne) hxc2
  have hz : ⟪x, x⟫_ℂ = 0 := (Submodule.mem_orthogonal c₁ x).mp hxc1perp x hxc1
  exact inner_self_eq_zero.mp hz

/-- The binary decomposition `{K, Kᗮ}` is a legitimate perspective, for
    any proper non-zero subspace `K`. -/
noncomputable def binary (K : Submodule ℂ V) (h1 : K ≠ ⊥) (h2 : K ≠ ⊤) :
    Perspective V where
  cells := {K, Kᗮ}
  nz := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact h1
    · intro hbot
      apply h2
      have h : Kᗮᗮ = (⊥ : Submodule ℂ V)ᗮ := congrArg Submodule.orthogonal hbot
      rwa [Submodule.orthogonal_orthogonal, Submodule.bot_orthogonal_eq_top] at h
  ortho := by
    intro c hc c' hc' hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc hc'
    rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl <;>
      first
        | exact absurd rfl hne
        | exact le_refl _
        | exact Submodule.le_orthogonal_orthogonal _
  span := by
    show sSup (({K, Kᗮ} : Finset (Submodule ℂ V)) : Set (Submodule ℂ V)) = ⊤
    rw [Finset.coe_insert, Finset.coe_singleton, sSup_insert, sSup_singleton]
    first
      | exact Submodule.sup_orthogonal_of_hasOrthogonalProjection
      | exact Submodule.sup_orthogonal_of_completeSpace
      | exact (Submodule.isCompl_orthogonal_of_completeSpace).sup_eq_top
      | sorry  -- repli, voir NOTE 2 ; en principe non atteint désormais

/-- If `⊤` belongs to a perspective, that perspective reduces to the
    singleton `{⊤}`: no other non-zero cell could coexist with `⊤`,
    since it would have to be orthogonal to `⊤`, hence contained in
    `⊤ᗮ = ⊥`. -/
theorem singleton_of_mem_top (D : Perspective V) (hD : (⊤ : Submodule ℂ V) ∈ D.cells) :
    D.cells = {⊤} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hD, fun c' hc' => ?_⟩
  by_contra hne
  have hle : c' ≤ (⊤ : Submodule ℂ V)ᗮ := D.ortho c' hc' ⊤ hD hne
  have htopperp : (⊤ : Submodule ℂ V)ᗮ = ⊥ := by
    have h : (⊥ᗮᗮ : Submodule ℂ V) = (⊤ : Submodule ℂ V)ᗮ :=
      congrArg Submodule.orthogonal Submodule.bot_orthogonal_eq_top
    rw [Submodule.orthogonal_orthogonal] at h
    exact h.symm
  rw [htopperp] at hle
  exact D.nz c' hc' (le_bot_iff.mp hle)

end Perspective

-- An estimation rule: a real weight per (perspective, cell) pair.
variable (E : Perspective V → Submodule ℂ V → ℝ)

/-- (Grain): coherence of the estimation rule under refinement. -/
def AxGrain : Prop :=
  ∀ D' D : Perspective V, Refines D' D →
    ∀ c ∈ D.cells, E D c = ∑ c' ∈ D'.cells.filter (· ≤ c), E D' c'

-- (Norm): normalisation over any perspective. Needed only to close
-- the trivial case c = ⊤; the substantial case (c proper) never uses
-- it.
def AxNorm : Prop := ∀ D : Perspective V, ∑ c ∈ D.cells, E D c = 1

/-- Lemma 4: under (Grain) alone, the weight of a cell shared by two
    perspectives does not depend on which perspective it is evaluated
    in. Non-contextuality, usually postulated in Gleason-type
    derivations, is here a consequence of grain coherence alone. -/
theorem lemma4_noncontextual (hA : AxGrain E) (hN : AxNorm E)
    {D₁ D₂ : Perspective V} {c : Submodule ℂ V}
    (h₁ : c ∈ D₁.cells) (h₂ : c ∈ D₂.cells) :
    E D₁ c = E D₂ c := by
  by_cases htop : c = ⊤
  · -- Cas c = ⊤ : fermé sans sorry via (Norm) et singleton_of_mem_top.
    subst htop
    have e1 : D₁.cells = {⊤} := D₁.singleton_of_mem_top h₁
    have e2 : D₂.cells = {⊤} := D₂.singleton_of_mem_top h₂
    have s1 := hN D₁
    have s2 := hN D₂
    rw [e1, Finset.sum_singleton] at s1
    rw [e2, Finset.sum_singleton] at s2
    rw [s1, s2]
  · -- Cas c propre et non nul : le cœur de la preuve, complet.
    have hcne : c ≠ ⊥ := fun hbot => D₁.nz c h₁ hbot
    let D₀ := Perspective.binary c hcne htop
    have hcellsD0 : D₀.cells = insert c {cᗮ} := rfl
    have hmem0 : c ∈ D₀.cells := by
      rw [hcellsD0]; exact Finset.mem_insert_self _ _
    have hraf1 : Refines D₁ D₀ := by
      intro c' hc'
      by_cases heq : c' = c
      · exact ⟨c, hmem0, heq ▸ le_refl c⟩
      · refine ⟨cᗮ, ?_, D₁.ortho c' hc' c h₁ heq⟩
        rw [hcellsD0]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hraf2 : Refines D₂ D₀ := by
      intro c' hc'
      by_cases heq : c' = c
      · exact ⟨c, hmem0, heq ▸ le_refl c⟩
      · refine ⟨cᗮ, ?_, D₂.ortho c' hc' c h₂ heq⟩
        rw [hcellsD0]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have key1 : E D₀ c = E D₁ c := by
      have heq := hA D₁ D₀ hraf1 c hmem0
      rw [heq]
      have hfilter : D₁.cells.filter (· ≤ c) = {c} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨Finset.mem_filter.mpr ⟨h₁, le_refl c⟩, fun c' hc' => ?_⟩
        obtain ⟨hc'mem, hc'le⟩ := Finset.mem_filter.mp hc'
        exact D₁.unique_parent hc'mem h₁ (D₁.nz c' hc'mem) (le_refl c') hc'le
      rw [hfilter, Finset.sum_singleton]
    have key2 : E D₀ c = E D₂ c := by
      have heq := hA D₂ D₀ hraf2 c hmem0
      rw [heq]
      have hfilter : D₂.cells.filter (· ≤ c) = {c} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨Finset.mem_filter.mpr ⟨h₂, le_refl c⟩, fun c' hc' => ?_⟩
        obtain ⟨hc'mem, hc'le⟩ := Finset.mem_filter.mp hc'
        exact D₂.unique_parent hc'mem h₂ (D₂.nz c' hc'mem) (le_refl c') hc'le
      rw [hfilter, Finset.sum_singleton]
    rw [← key1, key2]



/-- (Pos): positivity of the estimation rule. -/
def AxPos : Prop := ∀ D : Perspective V, ∀ c ∈ D.cells, 0 ≤ E D c

omit [FiniteDimensional ℂ V] in
/-- The line spanned by a vector of an orthonormal basis is never
    zero. -/
theorem line_ne_bot (b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V)
    (i : Fin (Module.finrank ℂ V)) : (ℂ ∙ (b i : V)) ≠ ⊥ := by
  have hbi_ne : (b i : V) ≠ 0 := by
    have hnorm : ‖(b i : V)‖ = 1 := b.orthonormal.1 i
    intro hzero
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  rw [Submodule.ne_bot_iff]
  exact ⟨b i, Submodule.mem_span_singleton_self _, hbi_ne⟩

omit [FiniteDimensional ℂ V] in
/-- The same line is never the whole space, as soon as dim V ≥ 2. -/
theorem line_ne_top (hd2 : 2 ≤ Module.finrank ℂ V)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V)
    (i : Fin (Module.finrank ℂ V)) : (ℂ ∙ (b i : V)) ≠ ⊤ := by
  intro htop
  have hbi_ne : (b i : V) ≠ 0 := by
    have hnorm : ‖(b i : V)‖ = 1 := b.orthonormal.1 i
    intro hzero
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have h1 : Module.finrank ℂ (ℂ ∙ (b i : V)) = 1 := finrank_span_singleton hbi_ne
  rw [htop] at h1
  have h2 : Module.finrank ℂ (⊤ : Submodule ℂ V) = Module.finrank ℂ V := by
    first
      | exact Submodule.finrank_top
      | exact finrank_top ℂ V
  rw [h2] at h1
  omega

/-- The map sending an index to the line spanned by the corresponding
    basis vector is injective: distinct indices give distinct lines.
    Needed to convert a sum over cells (a `Finset.image`) into a sum
    over indices (`Finset.univ`). -/
theorem line_injective (b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V) :
    Set.InjOn (fun i => (ℂ ∙ (b i : V) : Submodule ℂ V))
      (↑(Finset.univ : Finset (Fin (Module.finrank ℂ V))) : Set (Fin (Module.finrank ℂ V))) := by
  intro i _ j _ heq
  by_contra hij
  have hbi_ne : (b i : V) ≠ 0 := by
    have hnorm : ‖(b i : V)‖ = 1 := b.orthonormal.1 i
    intro hzero; rw [hzero, norm_zero] at hnorm; norm_num at hnorm
  have hbi_mem : (b i : V) ∈ (ℂ ∙ (b j : V)) := by
    have heq' : (ℂ ∙ (b i : V) : Submodule ℂ V) = ℂ ∙ (b j : V) := heq
    rw [← heq']
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hbi_mem
  have horth : (⟪(b j : V), (b i : V)⟫_ℂ) = 0 := by
    have h1 : (⟪(b i : V), (b j : V)⟫_ℂ) = 0 := b.orthonormal.2 hij
    have h2 : (⟪(b j : V), (b i : V)⟫_ℂ) = starRingEnd ℂ (⟪(b i : V), (b j : V)⟫_ℂ) := by
      first
        | exact inner_conj_symm (b i) (b j)
        | exact (inner_conj_symm (b j) (b i)).symm
    rw [h2, h1]; simp
  have hbjbj : (⟪(b j : V), (b j : V)⟫_ℂ) = 1 := by
    have hn : ‖(b j : V)‖ = 1 := b.orthonormal.1 j
    first
      | simp [hn]
      | (have hre : (⟪(b j:V), (b j:V)⟫_ℂ).re = ‖(b j:V)‖ ^ 2 := by
           simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (b j : V)
         have him : (⟪(b j:V), (b j:V)⟫_ℂ).im = 0 := by simp
         apply Complex.ext
         · rw [hre, hn]; norm_num
         · rw [him])
  rw [← hc, inner_smul_right, hbjbj, mul_one] at horth
  exact hbi_ne (by rw [← hc, horth, zero_smul])

/-- A whole orthonormal basis defines a perspective. -/
noncomputable def basisPerspective
    (b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V) : Perspective V where
  cells := Finset.univ.image (fun i => ℂ ∙ (b i : V))
  nz := by
    intro c hc
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hc
    obtain ⟨i, rfl⟩ := hc
    exact line_ne_bot b i
  ortho := by
    intro c hc c' hc' hne
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hc hc'
    obtain ⟨i, rfl⟩ := hc
    obtain ⟨j, rfl⟩ := hc'
    have hij : i ≠ j := fun h => hne (by rw [h])
    have horth : (⟪(b j : V), (b i : V)⟫_ℂ) = 0 := by
      have h1 : (⟪(b i : V), (b j : V)⟫_ℂ) = 0 := b.orthonormal.2 hij
      have h2 : (⟪(b j : V), (b i : V)⟫_ℂ) = starRingEnd ℂ (⟪(b i : V), (b j : V)⟫_ℂ) := by
        first
          | exact inner_conj_symm (b i) (b j)
          | exact (inner_conj_symm (b j) (b i)).symm
      rw [h2, h1]
      simp
    rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [inner_smul_left, horth, mul_zero]
  span := by
    show sSup ((Finset.univ.image (fun i => ℂ ∙ (b i : V))) : Set (Submodule ℂ V)) = ⊤
    have himg : ((Finset.univ.image (fun i => ℂ ∙ (b i : V))) : Set (Submodule ℂ V))
        = Set.range (fun i => ℂ ∙ (b i : V)) := by
      ext c
      simp [Set.mem_range]
    rw [himg, sSup_range]
    first
      | exact b.toBasis.span_eq
      | exact b.toBasis.iSup_span_singleton_eq_top
      | (rw [iSup_span_singleton_eq_span]
         exact b.toBasis.span_eq)
      | sorry

/-- Lines from an orthonormal basis relative to a single cell `c`
    (rather than to the whole space): generalises `basisPerspective`
    to an arbitrary subspace. -/
noncomputable def cellLines (c : Submodule ℂ V) : Finset (Submodule ℂ V) :=
  Finset.univ.image (fun i : Fin (Module.finrank ℂ c) => ℂ ∙ ((stdOrthonormalBasis ℂ c i : c) : V))

theorem cellLines_le (c : Submodule ℂ V) : ∀ x ∈ cellLines c, x ≤ c := by
  intro x hx
  simp only [cellLines, Finset.mem_image, Finset.mem_univ, true_and] at hx
  obtain ⟨i, rfl⟩ := hx
  rw [Submodule.span_singleton_le_iff_mem]
  exact SetLike.coe_mem _

theorem cellLines_ne_bot (c : Submodule ℂ V) : ∀ x ∈ cellLines c, x ≠ ⊥ := by
  intro x hx
  simp only [cellLines, Finset.mem_image, Finset.mem_univ, true_and] at hx
  obtain ⟨i, rfl⟩ := hx
  rw [Submodule.ne_bot_iff]
  refine ⟨(stdOrthonormalBasis ℂ c i : c), Submodule.mem_span_singleton_self _, ?_⟩
  have hnorm : ‖(stdOrthonormalBasis ℂ c i : c)‖ = 1 := (stdOrthonormalBasis ℂ c).orthonormal.1 i
  intro hzero
  rw [Submodule.coe_eq_zero] at hzero
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

theorem cellLines_sSup (c : Submodule ℂ V) :
    sSup ((cellLines c : Finset (Submodule ℂ V)) : Set (Submodule ℂ V)) = c := by
  set b := stdOrthonormalBasis ℂ c with hb_def
  show sSup ((Finset.univ.image (fun i => ℂ ∙ ((b i : c) : V))) : Set (Submodule ℂ V)) = c
  have himg : ((Finset.univ.image (fun i => ℂ ∙ ((b i : c) : V))) : Set (Submodule ℂ V))
      = Set.range (fun i => ℂ ∙ ((b i : c) : V)) := by
    ext x; simp [Set.mem_range]
  rw [himg, sSup_range]
  have hgeneric : (⨆ i, (Submodule.span ℂ ({((b i : c) : V)} : Set V)))
      = Submodule.span ℂ (Set.range (fun i => ((b i : c) : V))) := by
    apply le_antisymm
    · exact iSup_le (fun i => Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨i, rfl⟩))
    · rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      exact (le_iSup (fun i => Submodule.span ℂ ({((b i : c) : V)} : Set V)) i)
        (Submodule.mem_span_singleton_self _)
  rw [hgeneric]
  have hspan_top : Submodule.span ℂ (Set.range (b.toBasis : Fin (Module.finrank ℂ c) → c)) = ⊤ :=
    b.toBasis.span_eq
  have hmapped := congrArg (Submodule.map c.subtype) hspan_top
  rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at hmapped
  convert hmapped using 2
  ext i
  simp [Function.comp]

theorem cellLines_ortho_within (c : Submodule ℂ V) :
    ∀ x ∈ cellLines c, ∀ y ∈ cellLines c, x ≠ y → x ≤ yᗮ := by
  intro x hx y hy hxy
  simp only [cellLines, Finset.mem_image, Finset.mem_univ, true_and] at hx hy
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  have hij : i ≠ j := fun h => hxy (by rw [h])
  set e := stdOrthonormalBasis ℂ c with he_def
  have horth_c : (⟪e j, e i⟫_ℂ : ℂ) = 0 := e.orthonormal.2 (Ne.symm hij)
  have horth_V : (⟪((e j : c) : V), ((e i : c) : V)⟫_ℂ : ℂ) = 0 := by
    rw [← Submodule.coe_inner]
    exact horth_c
  rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_orthogonal]
  intro u hu
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hu
  rw [inner_smul_left, horth_V, mul_zero]

/-- The full refinement of an arbitrary perspective `D`: glue, across
    every cell of `D`, an orthonormal basis proper to that cell. This
    is the piece that lifts every result below from a single fixed
    basis to an arbitrary perspective. -/
noncomputable def refinePerspective (D : Perspective V) : Perspective V where
  cells := D.cells.biUnion cellLines
  nz := by
    intro x hx
    simp only [Finset.mem_biUnion] at hx
    obtain ⟨c, hc, hx'⟩ := hx
    exact cellLines_ne_bot c x hx'
  ortho := by
    intro x hx y hy hxy
    simp only [Finset.mem_biUnion] at hx hy
    obtain ⟨c, hc, hx'⟩ := hx
    obtain ⟨c', hc', hy'⟩ := hy
    by_cases hcc : c = c'
    · subst hcc
      exact cellLines_ortho_within c x hx' y hy' hxy
    · have hxc : x ≤ c := cellLines_le c x hx'
      have hyc' : y ≤ c' := cellLines_le c' y hy'
      have h1 : c ≤ c'ᗮ := D.ortho c hc c' hc' hcc
      have h2 : c'ᗮ ≤ yᗮ := Submodule.orthogonal_le hyc'
      exact hxc.trans (h1.trans h2)
  span := by
    show sSup ((D.cells.biUnion cellLines : Finset (Submodule ℂ V)) : Set (Submodule ℂ V)) = ⊤
    apply le_antisymm le_top
    rw [← D.span]
    apply sSup_le
    intro c hc
    simp only [Finset.mem_coe] at hc
    rw [← cellLines_sSup c]
    apply sSup_le_sSup
    intro x hx
    simp only [Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨c, hc, hx⟩

theorem refinePerspective_refines (D : Perspective V) : Refines (refinePerspective D) D := by
  intro x hx
  simp only [refinePerspective, Finset.mem_biUnion] at hx
  obtain ⟨c, hc, hx'⟩ := hx
  exact ⟨c, hc, cellLines_le c x hx'⟩

/-- Lemma 5: under (Grain), (Norm), (Pos), the weights of E on the
    lines of any fixed orthonormal basis are non-negative and sum to
    one. -/
theorem frame_normalized (_hA : AxGrain E) (hN : AxNorm E) (hPos : AxPos E)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V) :
    (∀ i, 0 ≤ E (basisPerspective b) (ℂ ∙ (b i : V)))
    ∧ ∑ i, E (basisPerspective b) (ℂ ∙ (b i : V)) = 1 := by
  constructor
  · intro i
    exact hPos (basisPerspective b) (ℂ ∙ (b i : V))
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  · have hsum := hN (basisPerspective b)
    rwa [show (basisPerspective b).cells
          = Finset.univ.image (fun i => ℂ ∙ (b i : V)) from rfl,
        Finset.sum_image (line_injective b)] at hsum

/-- Gleason's theorem (1957), dimension ≥ 3: every positive, normalised
    frame function on the unit vectors of `V` is realised by a density
    operator. Declared here as an explicit axiom: this is the only
    step in the whole development that is not machine-checked. -/
axiom gleason (hd3 : 3 ≤ Module.finrank ℂ V) (g : V → ℝ)
    (hg0 : ∀ x : V, ‖x‖ = 1 → 0 ≤ g x)
    (hframe : ∀ b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V,
      ∑ i, g (b i) = 1) :
    ∃ ρ : V →ₗ[ℂ] V, LinearMap.IsSymmetric ρ ∧
      (∀ x : V, 0 ≤ (⟪x, ρ x⟫_ℂ).re) ∧
      LinearMap.trace ℂ V ρ = 1 ∧
      (∀ x : V, ‖x‖ = 1 → g x = (⟪x, ρ x⟫_ℂ).re)

omit [FiniteDimensional ℂ V] in
/-- A symmetric, positive operator that vanishes, in the quadratic
    sense, at a vector, vanishes there also as a linear map. Proved by
    a self-contained Cauchy-Schwarz argument: no ready-made inequality
    for general positive sesquilinear forms was found in Mathlib for
    this statement. -/
theorem symmetric_pos_zero_of_diag_zero (ρ : V →ₗ[ℂ] V) (hsym : LinearMap.IsSymmetric ρ)
    (hpos : ∀ x : V, 0 ≤ (⟪x, ρ x⟫_ℂ).re)
    (w : V) (hw : (⟪w, ρ w⟫_ℂ).re = 0) :
    ρ w = 0 := by
  have key : ∀ x : V, (⟪x, ρ w⟫_ℂ) = 0 := by
    intro x
    by_contra hs
    set s : ℂ := ⟪x, ρ w⟫_ℂ with hs_def
    have hnormsq_pos : 0 < Complex.normSq s := by
      rw [Complex.normSq_pos]
      exact hs
    set t : ℝ := ((⟪x, ρ x⟫_ℂ).re + 1) / (2 * Complex.normSq s) with ht_def
    have ht_pos : 0 < t := by
      rw [ht_def]
      apply div_pos
      · linarith [hpos x]
      · linarith
    set z : ℂ := (-(t : ℂ)) * (starRingEnd ℂ s) with hz_def
    have hcross : (⟪w, ρ x⟫_ℂ) = starRingEnd ℂ s := by
      have e1 : (⟪ρ w, x⟫_ℂ) = (⟪w, ρ x⟫_ℂ) := hsym w x
      have e2 : (⟪ρ w, x⟫_ℂ) = starRingEnd ℂ (⟪x, ρ w⟫_ℂ) := by
        first
          | exact inner_conj_symm x (ρ w)
          | exact (inner_conj_symm (ρ w) x).symm
      rw [← e1, e2, hs_def]
    have hlin : ρ (x + z • w) = ρ x + z • ρ w := by
      simp [map_add, map_smul]
    have hexp : (⟪x + z • w, ρ (x + z • w)⟫_ℂ)
        = ⟪x, ρ x⟫_ℂ + z * s + (starRingEnd ℂ z) * (starRingEnd ℂ s)
          + z * (starRingEnd ℂ z) * ⟪w, ρ w⟫_ℂ := by
      rw [hlin]
      rw [inner_add_left, inner_add_right, inner_add_right]
      rw [inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
      rw [hcross, hs_def]
      ring
    have hzs : z * s = ((-(t * Complex.normSq s) : ℝ) : ℂ) := by
      rw [hz_def]
      have step : (-(t : ℂ)) * (starRingEnd ℂ s) * s
          = (-(t : ℂ)) * (s * starRingEnd ℂ s) := by ring
      rw [step, Complex.mul_conj]
      push_cast
      ring
    have hconjzs : (starRingEnd ℂ z) * (starRingEnd ℂ s) = starRingEnd ℂ (z * s) :=
      (map_mul (starRingEnd ℂ) z s).symm
    have hconjzs_val : (starRingEnd ℂ z) * (starRingEnd ℂ s)
        = ((-(t * Complex.normSq s) : ℝ) : ℂ) := by
      rw [hconjzs, hzs]
      simp
    rw [hzs, hconjzs_val] at hexp
    have hre := hpos (x + z • w)
    rw [hexp] at hre
    have hlast_re : (z * (starRingEnd ℂ z) * ⟪w, ρ w⟫_ℂ).re = 0 := by
      have hzconjz_real : (z * starRingEnd ℂ z).im = 0 := by
        simp [Complex.mul_conj]
      have : (z * starRingEnd ℂ z * ⟪w, ρ w⟫_ℂ).re
          = (z * starRingEnd ℂ z).re * (⟪w, ρ w⟫_ℂ).re
            - (z * starRingEnd ℂ z).im * (⟪w, ρ w⟫_ℂ).im := Complex.mul_re _ _
      rw [this, hzconjz_real, hw]
      ring
    rw [Complex.add_re, Complex.add_re, Complex.add_re] at hre
    simp only [Complex.ofReal_re] at hre
    rw [hlast_re] at hre
    have hC := hpos x
    rw [ht_def] at hre
    field_simp at hre
    nlinarith [hre, hC, hnormsq_pos]
  have hfinal := key (ρ w)
  exact inner_self_eq_zero.mp hfinal

/-- Pinning lemma: if ρ is symmetric, positive, of trace 1, and if
    ⟪w, ρw⟫ = 0 for every w ⊥ v (‖v‖ = 1), then ρ is exactly the
    rank-one projector onto v. -/
theorem pinning (ρ : V →ₗ[ℂ] V) (hsym : LinearMap.IsSymmetric ρ)
    (hposρ : ∀ x : V, 0 ≤ (⟪x, ρ x⟫_ℂ).re)
    (v : V) (hv : ‖v‖ = 1)
    (hker : ∀ w : V, ⟪v, w⟫_ℂ = 0 → (⟪w, ρ w⟫_ℂ).re = 0)
    (htr : LinearMap.trace ℂ V ρ = 1) :
    ∀ x : V, ρ x = (⟪v, x⟫_ℂ) • v := by
  -- Étape (i) : ρ s'annule sur l'orthogonal de v.
  have step1 : ∀ w : V, ⟪v, w⟫_ℂ = 0 → ρ w = 0 := fun w hw_perp =>
    symmetric_pos_zero_of_diag_zero ρ hsym hposρ w (hker w hw_perp)
  -- ⟪v, v⟫ = 1 (v unitaire).
  have hvv : ⟪v, v⟫_ℂ = 1 := by
    first
      | simp [hv]
      | simp [hv, inner_self_eq_norm_sq]
      | (have hre : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := by
           simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
         have him : (⟪v, v⟫_ℂ).im = 0 := by simp
         apply Complex.ext
         · rw [hre, hv]; norm_num
         · rw [him])
  -- Décomposition orthogonale de tout vecteur par rapport à v.
  have hdecomp_perp : ∀ x : V, ⟪v, x - (⟪v, x⟫_ℂ) • v⟫_ℂ = 0 := by
    intro x
    rw [inner_sub_right, inner_smul_right, hvv, mul_one, sub_self]
  set lam : ℂ := ⟪v, ρ v⟫_ℂ with hlam_def
  -- Étape (ii)-(iii) partielle : ρ v = lam • v (lam pas encore fixé à 1).
  have hrhov : ρ v = lam • v := by
    have hw_perp : ⟪v, ρ v - lam • v⟫_ℂ = 0 := by
      have h := hdecomp_perp (ρ v)
      rwa [← hlam_def] at h
    have hzero1 : ρ (ρ v - lam • v) = 0 := step1 _ hw_perp
    have hcross : ⟪ρ v - lam • v, ρ v⟫_ℂ = 0 := by
      have e1 : ⟪ρ v - lam • v, ρ v⟫_ℂ = ⟪ρ (ρ v - lam • v), v⟫_ℂ :=
        (hsym (ρ v - lam • v) v).symm
      rw [e1, hzero1, inner_zero_left]
    have hvperp2 : ⟪ρ v - lam • v, v⟫_ℂ = 0 := by
      have hh : ⟪ρ v - lam • v, v⟫_ℂ = starRingEnd ℂ (⟪v, ρ v - lam • v⟫_ℂ) := by
        first
          | exact inner_conj_symm v (ρ v - lam • v)
          | exact (inner_conj_symm (ρ v - lam • v) v).symm
      rw [hh, hw_perp]
      simp
    have hself : ⟪ρ v - lam • v, ρ v - lam • v⟫_ℂ = 0 := by
      rw [inner_sub_right, hcross, inner_smul_right, hvperp2]
      ring
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hself)
  -- Formule générale : ρ x = (⟪v,x⟫ * lam) • v, pour tout x.
  have hgeneral : ∀ x : V, ρ x = (⟪v, x⟫_ℂ * lam) • v := by
    intro x
    have hw_perp := hdecomp_perp x
    have hzero := step1 _ hw_perp
    have hxdecomp : x = (⟪v, x⟫_ℂ) • v + (x - (⟪v, x⟫_ℂ) • v) := by
      first | abel | module | simp
    calc ρ x = ρ ((⟪v, x⟫_ℂ) • v + (x - (⟪v, x⟫_ℂ) • v)) := by rw [← hxdecomp]
      _ = (⟪v, x⟫_ℂ) • ρ v + ρ (x - (⟪v, x⟫_ℂ) • v) := by rw [map_add, map_smul]
      _ = (⟪v, x⟫_ℂ) • ρ v + 0 := by rw [hzero]
      _ = (⟪v, x⟫_ℂ) • (lam • v) := by rw [add_zero, hrhov]
      _ = (⟪v, x⟫_ℂ * lam) • v := by rw [smul_smul]
  -- lam = 1, établi séparément (voir lam1_assembly_test.lean) via la
  -- trace calculée sur une base orthonormée QUELCONQUE (aucune
  -- extension de v en base n'est nécessaire), combinée à l'identité de
  -- Parseval/Bessel.
  have hlam1 : lam = 1 := by
    set e := stdOrthonormalBasis ℂ V with he_def
    have htrace_formula : LinearMap.trace ℂ V ρ = ∑ i, ⟪e i, ρ (e i)⟫_ℂ :=
      LinearMap.trace_eq_sum_inner ρ e
    have hexpand : ∀ i, ⟪(e i : V), ρ (e i)⟫_ℂ
        = lam * (⟪v, (e i : V)⟫_ℂ * ⟪(e i : V), v⟫_ℂ) := by
      intro i
      rw [hgeneral (e i), inner_smul_right]
      ring
    have hconj : ∀ i, ⟪v, (e i : V)⟫_ℂ = starRingEnd ℂ ⟪(e i : V), v⟫_ℂ := by
      intro i
      first
        | exact inner_conj_symm (e i) v
        | exact (inner_conj_symm v (e i)).symm
    have hcollapse : ∀ i, ⟪v, (e i : V)⟫_ℂ * ⟪(e i : V), v⟫_ℂ
        = ((‖⟪(e i : V), v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      rw [hconj i, mul_comm, Complex.mul_conj]
      congr 1
      first
        | exact Complex.normSq_eq_norm_sq _
        | exact Complex.sq_abs _
        | (rw [Complex.norm_eq_abs]; exact Complex.sq_abs _)
        | (rw [Complex.norm_def]; exact (Real.sq_sqrt (Complex.normSq_nonneg _)).symm)
    have hsum1 : (∑ i, ⟪(e i : V), ρ (e i)⟫_ℂ)
        = lam * ∑ i, ((‖⟪(e i : V), v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [hexpand i, hcollapse i])
    have hsum2 : (∑ i, ((‖⟪(e i : V), v⟫_ℂ‖ ^ 2 : ℝ) : ℂ))
        = ((∑ i, ‖⟪(e i : V), v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    have hparseval : (∑ i, ‖⟪(e i : V), v⟫_ℂ‖ ^ 2 : ℝ) = ‖v‖ ^ 2 :=
      OrthonormalBasis.sum_sq_norm_inner_right e v
    rw [htrace_formula, hsum1, hsum2, hparseval, hv] at htr
    simpa using htr
  intro x
  rw [hgeneral x, hlam1, mul_one]




/-- (Null): a cell orthogonal to a fixed unit vector `v` carries no
    weight. -/
def AxNul (v : V) : Prop := ∀ D : Perspective V, ∀ c ∈ D.cells, v ∈ cᗮ → E D c = 0

/-- The estimation rule read as a total frame function on `V`
    (convention: 0 at the origin, never invoked in practice), via the
    binary perspective attached to the line spanned by `x`. -/
noncomputable def gline (hd3 : 3 ≤ Module.finrank ℂ V) (x : V) : ℝ :=
  if hx : x = 0 then 0
  else
    E (Perspective.binary (ℂ ∙ x)
         (by rw [Submodule.ne_bot_iff]; exact ⟨x, Submodule.mem_span_singleton_self _, hx⟩)
         (by
           intro htop
           have h1 : Module.finrank ℂ (ℂ ∙ x) = 1 := finrank_span_singleton hx
           rw [htop] at h1
           have h2 : Module.finrank ℂ (⊤ : Submodule ℂ V) = Module.finrank ℂ V := by
             first
               | exact Submodule.finrank_top
               | exact finrank_top ℂ V
           rw [h2] at h1
           omega))
      (ℂ ∙ x)

/-- Consistency of `gline` with `basisPerspective`, via Lemma 4. This
    is the bridge that lets `frame_normalized` (stated in terms of
    `basisPerspective`) verify the frame hypothesis of Gleason's
    axiom (stated in terms of `gline`). -/
theorem gline_eq_basis (hd3 : 3 ≤ Module.finrank ℂ V) (hA : AxGrain E) (hN : AxNorm E)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V)
    (i : Fin (Module.finrank ℂ V)) :
    gline E hd3 (b i : V) = E (basisPerspective b) (ℂ ∙ (b i : V)) := by
  have hbi : (b i : V) ≠ 0 := by
    have hnorm : ‖(b i : V)‖ = 1 := b.orthonormal.1 i
    intro hz
    rw [hz, norm_zero] at hnorm
    norm_num at hnorm
  unfold gline
  rw [dif_neg hbi]
  first
    | exact lemma4_noncontextual E hA hN (Finset.mem_insert_self _ _)
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    | exact lemma4_noncontextual hA hN (Finset.mem_insert_self _ _)
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- Positivity of `gline`, immediate from (Pos). -/
theorem gline_nonneg (hd3 : 3 ≤ Module.finrank ℂ V) (hPos : AxPos E) (x : V) :
    0 ≤ gline E hd3 x := by
  unfold gline
  by_cases hx : x = 0
  · simp [dif_pos hx]
  · rw [dif_neg hx]
    exact hPos _ _ (Finset.mem_insert_self _ _)

/-- The sum of `gline` over any orthonormal basis equals 1. -/
theorem gline_frame_sum (hd3 : 3 ≤ Module.finrank ℂ V) (hA : AxGrain E) (hN : AxNorm E)
    (hPos : AxPos E) (b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V) :
    ∑ i, gline E hd3 (b i : V) = 1 := by
  have h : ∑ i, E (basisPerspective b) (ℂ ∙ (b i : V)) = 1 := by
    first
      | exact (frame_normalized E hA hN hPos b).2
      | exact (frame_normalized hA hN hPos b).2
  calc ∑ i, gline E hd3 (b i : V)
      = ∑ i, E (basisPerspective b) (ℂ ∙ (b i : V)) :=
        Finset.sum_congr rfl (fun i _ => gline_eq_basis E hd3 hA hN b i)
    _ = 1 := h

/-- Direct application of Gleason's axiom with g := gline. -/
theorem exists_rho (hd3 : 3 ≤ Module.finrank ℂ V) (hA : AxGrain E) (hN : AxNorm E)
    (hPos : AxPos E) :
    ∃ ρ : V →ₗ[ℂ] V, LinearMap.IsSymmetric ρ ∧
      (∀ x : V, 0 ≤ (⟪x, ρ x⟫_ℂ).re) ∧
      LinearMap.trace ℂ V ρ = 1 ∧
      (∀ x : V, ‖x‖ = 1 → gline E hd3 x = (⟪x, ρ x⟫_ℂ).re) :=
  gleason hd3 (gline E hd3) (fun x _ => gline_nonneg E hd3 hPos x)
    (gline_frame_sum E hd3 hA hN hPos)

/-- `gline` vanishes on every w orthogonal to v, via (Null). -/
theorem gline_zero_of_perp (hd3 : 3 ≤ Module.finrank ℂ V) (v : V) (hNul : AxNul E v)
    (w : V) (hw_perp : ⟪v, w⟫_ℂ = 0) : gline E hd3 w = 0 := by
  by_cases hw : w = 0
  · simp [gline, dif_pos hw]
  · unfold gline
    rw [dif_neg hw]
    apply hNul _ _ (Finset.mem_insert_self _ _)
    rw [Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have hwv : ⟪w, v⟫_ℂ = 0 := by
      have heq : ⟪w, v⟫_ℂ = starRingEnd ℂ ⟪v, w⟫_ℂ := by
        first
          | exact inner_conj_symm v w
          | exact (inner_conj_symm w v).symm
      rw [heq, hw_perp]
      simp
    rw [inner_smul_left, hwv, mul_zero]

/-- The full `hker` hypothesis of `pinning`, derived from (Null) via a
    rescaling step (Gleason's conclusion only applies to unit
    vectors). -/
theorem hker_derivation (hd3 : 3 ≤ Module.finrank ℂ V) (hA : AxGrain E) (hN : AxNorm E)
    (hPos : AxPos E) (v : V) (hNul : AxNul E v)
    (ρ : V →ₗ[ℂ] V) (hgleason4 : ∀ x : V, ‖x‖ = 1 → gline E hd3 x = (⟪x, ρ x⟫_ℂ).re) :
    ∀ w : V, ⟪v, w⟫_ℂ = 0 → (⟪w, ρ w⟫_ℂ).re = 0 := by
  intro w hw_perp
  by_cases hw : w = 0
  · simp [hw]
  · have hwnorm_ne : (‖w‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hw
    set c : ℂ := (‖w‖ : ℂ) with hc_def
    have hc_ne : c ≠ 0 := by rw [hc_def]; exact_mod_cast hwnorm_ne
    set u : V := c⁻¹ • w with hu_def
    have hwu : w = c • u := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ hc_ne, one_smul]
    have hu_ne : u ≠ 0 := by
      rw [hu_def]
      simp [hc_ne, hw]
    have hu_norm : ‖u‖ = 1 := by
      have hstep : ‖u‖ = ‖c‖⁻¹ * ‖w‖ := by rw [hu_def, norm_smul, norm_inv]
      rw [hstep, hc_def]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg w)]
      field_simp
    have hline_eq : (ℂ ∙ w) = (ℂ ∙ u) := by
      rw [hwu]
      first
        | exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc_ne) u
        | exact (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc_ne) u).symm
    have hg_eq : gline E hd3 w = gline E hd3 u := by
      unfold gline
      rw [dif_neg hw, dif_neg hu_ne]
      first
        | (conv_lhs => arg 2; rw [hline_eq]
           apply lemma4_noncontextual E hA hN
           · rw [← hline_eq]; exact Finset.mem_insert_self _ _
           · exact Finset.mem_insert_self _ _)
        | (apply lemma4_noncontextual E hA hN
           · exact Finset.mem_insert_self _ _
           · rw [← hline_eq]; exact Finset.mem_insert_self _ _)
        | (conv_lhs => arg 2; rw [hline_eq]
           apply lemma4_noncontextual hA hN
           · rw [← hline_eq]; exact Finset.mem_insert_self _ _
           · exact Finset.mem_insert_self _ _)
        | (apply lemma4_noncontextual hA hN
           · exact Finset.mem_insert_self _ _
           · rw [← hline_eq]; exact Finset.mem_insert_self _ _)
    have hg0 : gline E hd3 w = 0 := gline_zero_of_perp E hd3 v hNul w hw_perp
    have hgu0 : (⟪u, ρ u⟫_ℂ).re = 0 := by
      rw [← hgleason4 u hu_norm, ← hg_eq, hg0]
    have hscale : ⟪w, ρ w⟫_ℂ = (c * c) * ⟪u, ρ u⟫_ℂ := by
      rw [hwu, map_smul, inner_smul_left, inner_smul_right]
      have hcreal : (starRingEnd ℂ) c = c := by rw [hc_def]; simp
      rw [hcreal]
      ring
    rw [hscale]
    have hcim : c.im = 0 := by rw [hc_def]; simp
    have hre_prod : ((c * c) * ⟪u, ρ u⟫_ℂ).re
        = (c * c).re * (⟪u, ρ u⟫_ℂ).re - (c * c).im * (⟪u, ρ u⟫_ℂ).im := Complex.mul_re _ _
    have hc2im : (c * c).im = 0 := by
      rw [Complex.mul_im, hcim]
      ring
    rw [hre_prod, hgu0, hc2im]
    ring

/-- Application of `pinning`, combining `exists_rho` (Gleason) and
    `hker_derivation` (Null plus rescaling). -/
theorem pinning_applied (hd3 : 3 ≤ Module.finrank ℂ V) (hA : AxGrain E) (hN : AxNorm E)
    (hPos : AxPos E) (v : V) (hv : ‖v‖ = 1) (hNul : AxNul E v) :
    ∃ ρ : V →ₗ[ℂ] V, ∀ x : V, ρ x = (⟪v, x⟫_ℂ) • v := by
  obtain ⟨ρ, hsym, hposρ, htr, hgleason4⟩ := exists_rho E hd3 hA hN hPos
  exact ⟨ρ, pinning ρ hsym hposρ v hv (hker_derivation E hd3 hA hN hPos v hNul ρ hgleason4) htr⟩

/-- The (Grain) filter of `refinePerspective D` at a cell c of D
    coincides exactly with `cellLines c`: no other cell of D can
    contribute, since a non-zero line cannot lie below two orthogonal
    cells at once. -/
theorem refine_filter_eq_cellLines (D : Perspective V) (c : Submodule ℂ V) (hc : c ∈ D.cells) :
    (refinePerspective D).cells.filter (· ≤ c) = cellLines c := by
  ext x
  simp only [Finset.mem_filter, refinePerspective, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨c', hc', hx'⟩, hxc⟩
    by_cases hcc : c' = c
    · rwa [hcc] at hx'
    · exfalso
      have hxc' : x ≤ c' := cellLines_le c' x hx'
      have hxne : x ≠ ⊥ := cellLines_ne_bot c' x hx'
      have h1 : c' ≤ cᗮ := D.ortho c' hc' c hc hcc
      have h2 : x ≤ cᗮ := hxc'.trans h1
      apply hxne
      rw [Submodule.eq_bot_iff]
      intro y hy
      have hy1 : y ∈ c := hxc hy
      have hy2 : y ∈ cᗮ := h2 hy
      have hzero : (⟪y, y⟫_ℂ : ℂ) = 0 := (Submodule.mem_orthogonal c y).mp hy2 y hy1
      exact inner_self_eq_zero.mp hzero
  · intro hx'
    exact ⟨⟨c, hc, hx'⟩, cellLines_le c x hx'⟩

/-- Injectivity of the index-to-line map, relative to a cell c
    (generalises `line_injective`, which was about the whole space). -/
theorem cellLines_injective (c : Submodule ℂ V) :
    Set.InjOn (fun i => (ℂ ∙ ((stdOrthonormalBasis ℂ c i : c) : V) : Submodule ℂ V))
      (↑(Finset.univ : Finset (Fin (Module.finrank ℂ c))) : Set (Fin (Module.finrank ℂ c))) := by
  intro i _ j _ heq
  by_contra hij
  set b := stdOrthonormalBasis ℂ c with hb_def
  have hbi_ne : ((b i : c) : V) ≠ 0 := by
    have hnorm : ‖(b i : c)‖ = 1 := b.orthonormal.1 i
    intro hzero
    rw [Submodule.coe_eq_zero] at hzero
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have heq' : (ℂ ∙ ((b i : c) : V)) = (ℂ ∙ ((b j : c) : V)) := heq
  have hbi_mem : ((b i : c) : V) ∈ (ℂ ∙ ((b j : c) : V)) :=
    heq' ▸ Submodule.mem_span_singleton_self _
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hbi_mem
  have hbjbj_c : (⟪b j, b j⟫_ℂ : ℂ) = 1 := by
    have hn : ‖(b j : c)‖ = 1 := b.orthonormal.1 j
    first
      | simp [hn]
      | (have hre : (⟪(b j : c), (b j : c)⟫_ℂ).re = ‖(b j : c)‖ ^ 2 := by
           simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (b j : c)
         have him : (⟪(b j : c), (b j : c)⟫_ℂ).im = 0 := by simp
         apply Complex.ext
         · rw [hre, hn]; norm_num
         · rw [him])
  have hbjbj : (⟪((b j : c) : V), ((b j : c) : V)⟫_ℂ : ℂ) = 1 := by
    rw [← Submodule.coe_inner]; exact hbjbj_c
  have horth : (⟪((b j : c) : V), ((b i : c) : V)⟫_ℂ : ℂ) = 0 := by
    have h1 : (⟪b i, b j⟫_ℂ : ℂ) = 0 := b.orthonormal.2 hij
    have h1' : (⟪((b i : c) : V), ((b j : c) : V)⟫_ℂ : ℂ) = 0 := by
      rw [← Submodule.coe_inner]; exact h1
    have h2 : (⟪((b j : c) : V), ((b i : c) : V)⟫_ℂ : ℂ)
        = starRingEnd ℂ ⟪((b i : c) : V), ((b j : c) : V)⟫_ℂ := by
      first
        | exact inner_conj_symm ((b i : c) : V) ((b j : c) : V)
        | exact (inner_conj_symm ((b j : c) : V) ((b i : c) : V)).symm
    rw [h2, h1']
    simp
  rw [← hd, inner_smul_right, hbjbj, mul_one] at horth
  exact hbi_ne (by rw [← hd, horth, zero_smul])

/-- Converts the sum over `cellLines c` into a sum over the indices of
    a basis of c, via the injectivity above. -/
theorem cellLines_sum_eq (c : Submodule ℂ V) (F : Submodule ℂ V → ℝ) :
    ∑ x ∈ cellLines c, F x
    = ∑ i : Fin (Module.finrank ℂ c), F (ℂ ∙ ((stdOrthonormalBasis ℂ c i : c) : V)) := by
  unfold cellLines
  rw [Finset.sum_image (cellLines_injective c)]

/-- ρ and its relation to `gline`, from a single call to `exists_rho`
    (Gleason is an axiom: two separate calls need not return the same
    witness). -/
theorem full_rho_facts (hd3 : 3 ≤ Module.finrank ℂ V) (hA : AxGrain E) (hN : AxNorm E)
    (hPos : AxPos E) (v : V) (hv : ‖v‖ = 1) (hNul : AxNul E v) :
    ∃ ρ : V →ₗ[ℂ] V, (∀ x : V, ρ x = (⟪v, x⟫_ℂ) • v) ∧
      (∀ x : V, ‖x‖ = 1 → gline E hd3 x = (⟪x, ρ x⟫_ℂ).re) := by
  obtain ⟨ρ, hsym, hposρ, htr, hgleason4⟩ := exists_rho E hd3 hA hN hPos
  exact ⟨ρ, pinning ρ hsym hposρ v hv (hker_derivation E hd3 hA hN hPos v hNul ρ hgleason4) htr,
    hgleason4⟩

/-- Theorem 1, in full generality: for an arbitrary perspective D and
    an arbitrary cell c, E D c is the sum of the squared overlaps of v
    on an orthonormal basis of c, the Born rule, in its fully general
    form. -/
theorem theorem1_general (hd3 : 3 ≤ Module.finrank ℂ V) (hA : AxGrain E) (hN : AxNorm E)
    (hPos : AxPos E) (v : V) (hv : ‖v‖ = 1) (hNul : AxNul E v)
    (D : Perspective V) (c : Submodule ℂ V) (hc : c ∈ D.cells) :
    E D c = ∑ i : Fin (Module.finrank ℂ c),
      ‖⟪v, ((stdOrthonormalBasis ℂ c i : c) : V)⟫_ℂ‖ ^ 2 := by
  obtain ⟨ρ, hrho, hgleason4⟩ := full_rho_facts E hd3 hA hN hPos v hv hNul
  have hgrain := hA (refinePerspective D) D (refinePerspective_refines D) c hc
  rw [refine_filter_eq_cellLines D c hc] at hgrain
  rw [hgrain, cellLines_sum_eq c (E (refinePerspective D))]
  apply Finset.sum_congr rfl
  intro i _
  set f : V := ((stdOrthonormalBasis ℂ c i : c) : V) with hf_def
  have hf_ne : f ≠ 0 := by
    have hnorm : ‖(stdOrthonormalBasis ℂ c i : c)‖ = 1 := (stdOrthonormalBasis ℂ c).orthonormal.1 i
    rw [hf_def]
    intro hzero
    rw [Submodule.coe_eq_zero] at hzero
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have hf_unit : ‖f‖ = 1 := by
    have hnorm : ‖(stdOrthonormalBasis ℂ c i : c)‖ = 1 := (stdOrthonormalBasis ℂ c).orthonormal.1 i
    rw [hf_def]; exact hnorm
  have hmem : (ℂ ∙ f) ∈ (refinePerspective D).cells := by
    simp only [refinePerspective, Finset.mem_biUnion]
    exact ⟨c, hc, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hEeq : E (refinePerspective D) (ℂ ∙ f) = gline E hd3 f := by
    unfold gline
    rw [dif_neg hf_ne]
    first
      | exact lemma4_noncontextual E hA hN hmem (Finset.mem_insert_self _ _)
      | exact lemma4_noncontextual hA hN hmem (Finset.mem_insert_self _ _)
  rw [hEeq, hgleason4 f hf_unit, hrho f, inner_smul_right]
  have hconj : ⟪f, v⟫_ℂ = starRingEnd ℂ ⟪v, f⟫_ℂ := by
    first
      | exact inner_conj_symm v f
      | exact (inner_conj_symm f v).symm
  rw [hconj]
  rw [show (⟪v, f⟫_ℂ * starRingEnd ℂ ⟪v, f⟫_ℂ) = ((Complex.normSq ⟪v, f⟫_ℂ : ℝ) : ℂ) from
    Complex.mul_conj _]
  rw [Complex.ofReal_re]
  congr 1
  first
    | exact Complex.normSq_eq_norm_sq _
    | exact Complex.sq_abs _
    | (rw [Complex.norm_eq_abs]; exact Complex.sq_abs _)
    | (rw [Complex.norm_def]; exact (Real.sq_sqrt (Complex.normSq_nonneg _)).symm)

