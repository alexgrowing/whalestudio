import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RpowNegLeNormOfComponent
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlMapStandardLatticeEqIffMemGLintAdicStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlMapDiagUniformizerElementarySublatticeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemCartanDoubleCosetOfLatticeBetweenUniformizerStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.SatHecke

open GlobalTheory.LatHecke GlobalTheory.LFun Formalism.UG

section Lemmas

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

variable {w} in

theorem diagJ_det_ne {n : ℕ} {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (j : ℕ) :
    (diagJ n ϖ j).det ≠ 0 := by
  have h0 : ϖ ≠ 0 := fun e => by simp [IsUnifV, e] at hϖ
  rw [diagJ, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun i _ => by split_ifs <;> simp [h0]

theorem stab_iff (n : ℕ) (g : GL (Fin n) (w.adicCompletion E)) :
    glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 =
      (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ↔ g ∈ GLint (Fin n) (Ov E w) :=
  GlobalTheory.T.glMap_standardLattice_eq_iff_mem_GLint_adic E w n g

theorem coset_of_elem (n : ℕ) (ϖ : w.adicCompletion E) (hϖ : IsUnifV E w ϖ) (j : ℕ) (hj : j ≤ n)
    (g : GL (Fin n) (w.adicCompletion E)) :
    haveI := GlobalTheory.RowSatakeBound.finite_residue w
    glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈
      Subtype.val '' subElem j (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) →
    ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (a : Matrix (Fin n) (Fin n) _) * diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) _) :=
  GlobalTheory.T.mem_cartanDoubleCoset_of_lattice_between_uniformizer E w n ϖ hϖ j hj g

theorem diag_elem (n : ℕ) (ϖ : w.adicCompletion E) (hϖ : IsUnifV E w ϖ) (S : Finset (Fin n))
    (d : GL (Fin n) (w.adicCompletion E))
    (hd : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (fun i => if i ∈ S then ϖ else 1)) :
    haveI := GlobalTheory.RowSatakeBound.finite_residue w
    glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈
      Subtype.val '' subElem S.card (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) :=
  GlobalTheory.T.glMap_diagUniformizer_elementarySublattice E w n ϖ hϖ S d hd

theorem elem_of_coset (n : ℕ) (ϖ : w.adicCompletion E) (hϖ : IsUnifV E w ϖ) (j : ℕ) (hj : j ≤ n)
    (g : GL (Fin n) (w.adicCompletion E)) :
    haveI := GlobalTheory.RowSatakeBound.finite_residue w
    (∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (a : Matrix (Fin n) (Fin n) _) * diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) _)) →
    glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈
      Subtype.val '' subElem j (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) := by
  haveI := GlobalTheory.RowSatakeBound.finite_residue w
  rintro ⟨a, ha, b, hb, e⟩
  set S : Finset (Fin n) := Finset.univ.filter fun i => (i : ℕ) < j
  have hS : S.card = j := by
    have : S = (Finset.range j).attachFin (n := n) (fun m hm => lt_of_lt_of_le (Finset.mem_range.1 hm) hj) := by
      ext i; simp [S]
    rw [this, Finset.card_attachFin, Finset.card_range]
  set D := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagJ n ϖ j) (diagJ_det_ne hϖ j)
  have hg : g = a * D * b := Units.ext (by rw [e]; simp [D, Matrix.GeneralLinearGroup.mkOfDetNeZero])
  obtain ⟨M, hM, hM'⟩ := diag_elem w n ϖ hϖ S D (by simp [D, Matrix.GeneralLinearGroup.mkOfDetNeZero, diagJ, S])
  rw [hS] at hM
  have hstd : ∀ k ∈ GLint (Fin n) (Ov E w), k • std (w.adicCompletionIntegers E) (w.adicCompletion E) n =
      std (w.adicCompletionIntegers E) (w.adicCompletion E) n := fun k hk => GlobalTheory.LatHecke.Lat.ext ((stab_iff w n k).2 hk)
  refine ⟨glLat a M, ?_, ?_⟩
  · have := (smul_mem_subElem_iff a j M (std (w.adicCompletionIntegers E) (w.adicCompletion E) n)).2 hM
    rw [hstd a ha] at this
    exact this
  · rw [hg, glMap_mul, glMap_mul, (stab_iff w n b).2 hb, ← hM']
    rfl

end Lemmas

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}

theorem Tj_eq_dosetInd {n : ℕ} {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (j : ℕ) :
    Tj ℂ n (Ov E w) ϖ j = dosetInd ℂ (GLint (Fin n) (Ov E w))
      (Matrix.GeneralLinearGroup.mkOfDetNeZero (diagJ n ϖ j) (diagJ_det_ne hϖ j)) := by
  unfold Tj dosetInd
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
  refine exists_congr fun a => and_congr_right fun _ => exists_congr fun b => and_congr_right fun _ => ?_
  rw [Units.ext_iff]
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem heckeVec_Tj_eq_sum {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) {x : V} (hx : x ∈ fixed ρ (KGL w n))
    {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {j : ℕ} (hj : j ≤ n)
    (s : Finset (GL (Fin n) (w.adicCompletion E)))
    (hs : haveI := GlobalTheory.RowSatakeBound.finite_residue w
      Set.BijOn (fun g => glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1) s
        (Subtype.val '' subElem j (std (w.adicCompletionIntegers E) (w.adicCompletion E) n))) :
    heckeVec ρ (KGL w n) (Tj ℂ n (Ov E w) ϖ j) x = ∑ g ∈ s, ρ g x := by
  haveI := GlobalTheory.RowSatakeBound.finite_residue w
  set D := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagJ n ϖ j) (diagJ_det_ne hϖ j)
  have hD : ∀ g : GL (Fin n) (w.adicCompletion E), g ∈ DoubleCoset.doubleCoset D (KGL w n : Set _) (KGL w n) ↔
      ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
        (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (a : Matrix (Fin n) (Fin n) _) * diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) _) := by
    intro g
    simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    refine exists_congr fun a => and_congr_right fun _ => exists_congr fun b => and_congr_right fun _ => ?_
    rw [Units.ext_iff]
    simp [D, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  rw [Tj_eq_dosetInd hϖ j]
  refine heckeVec_dosetInd hx (fun γ hγ => (hD γ).2 (coset_of_elem w n ϖ hϖ j hj γ (hs.mapsTo hγ)))
    fun g hg => ?_
  obtain ⟨γ, hγ, e⟩ := hs.surjOn (elem_of_coset w n ϖ hϖ j hj g ((hD g).1 hg))
  have hmem : ∀ γ' : GL (Fin n) (w.adicCompletion E),
      γ'⁻¹ * g ∈ KGL w n ↔ glMap γ' (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 =
        glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 := fun γ' => by
    rw [← stab_iff w n, glMap_mul]
    constructor
    · intro h
      conv_lhs => rw [← h]
      rw [← glMap_mul, mul_inv_cancel, glMap_one]
    · intro h
      rw [← h, ← glMap_mul, inv_mul_cancel, glMap_one]
  refine ⟨γ, ⟨hγ, (hmem γ).2 e⟩, fun γ' ⟨hγ', h'⟩ => hs.injOn hγ' hγ ?_⟩
  exact ((hmem γ').1 h').trans e.symm

end GlobalTheory.SatHecke

namespace GlobalTheory.SatHecke

open GlobalTheory.LatHecke GlobalTheory.LFun Formalism.UG

def formCore {X : Type} [AddCommGroup X] [Module ℂ X] (B : X →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ)
    (hB : ∀ v w, B w v = starRingEnd ℂ (B v w)) (hp : ∀ v, v ≠ 0 → 0 < (B v v).re) :
    InnerProductSpace.Core ℂ X where
  inner x y := B y x
  conj_inner_symm x y := (hB x y).symm
  re_inner_nonneg x := by
    by_cases h : x = 0
    · simp [h]
    · exact (hp x h).le
  add_left x y z := by change B z (x + y) = B z x + B z y; simp
  smul_left x y r := by change B y (r • x) = _ * B y x; simp
  definite x h := by
    by_contra h0
    have := hp x h0
    change B x x = 0 at h
    rw [h] at this
    simp at this

end GlobalTheory.SatHecke

namespace GlobalTheory.SatHecke

theorem isUnitarySatakeAt_of_hasSatake : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ), letI := GlobalTheory.LocalData.complRel w; haveI := GlobalTheory.LocalData.isLocalField w; ∀ (π : Irr (w.adicCompletion E) n) (α : Fin n → ℂˣ), HasSatake π.π α → IsUnitarisable π.π → GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w n (Finset.univ.val.map fun i => (α i : ℂ)) := by
  intro E _ _ w n
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  intro π α hS hU
  have hG : GlobalTheory.LGrp.HasSatakeGL π.π (Finset.univ.val.map α) :=
    (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ π.π _).2 ⟨α, rfl, hS⟩
  obtain ⟨x, hx⟩ := (GlobalTheory.LFun.SatCompare.hasSatGL_of_hasSatakeGL hG).exists_vec
  obtain ⟨B, hB, hpos, hi⟩ := hU
  letI cd : InnerProductSpace.Core ℂ π.V := formCore B hB hpos
  letI : NormedAddCommGroup π.V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ π.V := InnerProductSpace.ofCore cd.toCore
  haveI := GlobalTheory.RowSatakeBound.finite_residue w
  have hn : ∀ y : π.V, ‖y‖ ^ 2 = (B y y).re := fun y => by
    rw [← @inner_self_eq_norm_sq ℂ]
    rfl
  refine ⟨by simp, π.V, inferInstance, inferInstance, π.π, x, fun g y => ?_, hx.1, fun g hg => ?_, fun k hk s hs => ?_⟩
  · have h2 : ‖π.π g y‖ ^ 2 = ‖y‖ ^ 2 := by rw [hn, hn, hi]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  · exact GlobalTheory.LGrp.mem_fixed.1 hx.2.1 g ((stab_iff w n g).1 hg)
  · obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
    rw [← heckeVec_Tj_eq_sum π.π hx.2.1 hϖ hk s hs, hx.2.2.2 ϖ hϖ k hk, GlobalTheory.LFun.satEig, Multiset.map_map]
    congr 2
    rw [GlobalTheory.RowSatakeBound.qRes_eq_normV w]
    have hq : (Formalism.UG.qV E w : ℕ) = normV w := by
      unfold Formalism.UG.qV normV
      rfl
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _), hq]
    push_cast
    rfl

end GlobalTheory.SatHecke
