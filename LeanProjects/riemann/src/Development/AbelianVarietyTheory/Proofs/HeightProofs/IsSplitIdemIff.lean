import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.OmegaUpDownForms
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

namespace GlobalTheory.WeilTieCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gram_mul_inv (V : HSp D) : HeisenbergWeilMatrices.gramA V * HeisenbergWeilMatrices.gramInvA V = 1 := by
  unfold HeisenbergWeilMatrices.gramA HeisenbergWeilMatrices.gramInvA
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem inv_mul_gram (V : HSp D) : HeisenbergWeilMatrices.gramInvA V * HeisenbergWeilMatrices.gramA V = 1 := mul_eq_one_comm.1 (gram_mul_inv V)

theorem gram_conj (V : HSp D) : ((HeisenbergWeilMatrices.gramA V).map (cA D))ᵀ = HeisenbergWeilMatrices.gramA V := by
  ext i j
  exact (DualPairCheck.cA_incA _).trans (congrArg (incA D) (DualPairCheck.gram_star V j i))

theorem gramInv_conj (V : HSp D) : ((HeisenbergWeilMatrices.gramInvA V).map (cA D))ᵀ = HeisenbergWeilMatrices.gramInvA V := by
  have h : HeisenbergWeilMatrices.gramA V * ((HeisenbergWeilMatrices.gramInvA V).map (cA D))ᵀ = 1 := by
    rw [← gram_conj, ← Matrix.transpose_mul, ← Matrix.map_mul, inv_mul_gram,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  calc _ = (HeisenbergWeilMatrices.gramInvA V * HeisenbergWeilMatrices.gramA V) * ((HeisenbergWeilMatrices.gramInvA V).map (cA D))ᵀ := by rw [inv_mul_gram, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, h, Matrix.mul_one]

def kap (A B : HSp D) : WA A B ≃+ WA A B where
  toFun x := HMul.hMul (HeisenbergWeilMatrices.gramInvA A)ᵀ x
  invFun y := HMul.hMul (HeisenbergWeilMatrices.gramA A)ᵀ y
  left_inv x := by
    simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, inv_mul_gram, Matrix.transpose_one, Matrix.one_mul]
  right_inv x := by
    simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, gram_mul_inv, Matrix.transpose_one, Matrix.one_mul]
  map_add' x y := Matrix.mul_add _ _ _

theorem kap_apply (A B : HSp D) (x : WA A B) : kap A B x = HMul.hMul (HeisenbergWeilMatrices.gramInvA A)ᵀ x := rfl

theorem kap_symm_apply (A B : HSp D) (x : WA A B) : (kap A B).symm x = HMul.hMul (HeisenbergWeilMatrices.gramA A)ᵀ x := rfl

def kapT (A B : HSp D) : WA A B ≃+ WA B A := (kap A B).trans (Matrix.transposeAddEquiv _ _ _)

theorem kapT_apply (A B : HSp D) (x : WA A B) : kapT A B x = (kap A B x)ᵀ := rfl

theorem topRing (D : D7) : IsTopologicalRing (AE D) :=
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)

theorem hHom_kap {A B : HSp D} (hr : A.rank ≤ B.rank) (x y : WA A B) :
    hHom A B (kap A B y) (kap A B x) = HeisenbergWeilMatrices.herm x y := by
  have s := DualPairCheck.sum_small (cA D) (HeisenbergWeilMatrices.gramA A) (HeisenbergWeilMatrices.gramA B) (kap A B y) (kap A B x)
  unfold hHom
  rw [if_pos hr]
  refine Eq.trans s ?_
  simp only [kap_apply, HeisenbergWeilMatrices.herm, HeisenbergWeilMatrices.adj, HeisenbergWeilMatrices.colMat, Formalism.UG.cT, Matrix.transpose_transpose, Matrix.map_mul,
    Matrix.transpose_mul, Matrix.transpose_map, gramInv_conj, Matrix.mul_assoc, inv_mul_gram, Matrix.mul_one]
  rfl

theorem actHom_kap {A B : HSp D} (hr : A.rank ≤ B.rank) (g : GA D A) (h : GA D B) (x : WA A B) :
    actHom A B g h (kap A B x) = kap A B (HeisenbergWeilMatrices.act (g, h) x) := by
  have h1 : ((mt A g).map (cA D))ᵀ * HeisenbergWeilMatrices.gramA A * mt A g = HeisenbergWeilMatrices.gramA A := mt_rel A g
  have h2 : mt A g * HeisenbergWeilMatrices.gMat g⁻¹ = 1 := by
    change HeisenbergWeilMatrices.gMat g * _ = 1
    rw [← HeisenbergWeilMatrices.gMat_mul, mul_inv_cancel, HeisenbergWeilMatrices.gMat_one]
  have h3 : HeisenbergWeilMatrices.gramInvA A * ((mt A g).map (cA D))ᵀ = HeisenbergWeilMatrices.gMat g⁻¹ * HeisenbergWeilMatrices.gramInvA A := by
    calc _ = HeisenbergWeilMatrices.gramInvA A * (((mt A g).map (cA D))ᵀ * (HeisenbergWeilMatrices.gramA A * (mt A g * HeisenbergWeilMatrices.gMat g⁻¹) * HeisenbergWeilMatrices.gramInvA A)) := by
          rw [h2, Matrix.mul_one, gram_mul_inv, Matrix.mul_one]
      _ = HeisenbergWeilMatrices.gramInvA A * (((mt A g).map (cA D))ᵀ * HeisenbergWeilMatrices.gramA A * mt A g) * (HeisenbergWeilMatrices.gMat g⁻¹ * HeisenbergWeilMatrices.gramInvA A) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, inv_mul_gram, Matrix.one_mul]
  have h4 := congrArg Matrix.transpose h3
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h4
  unfold actHom
  rw [if_pos hr]
  simp only [kap_apply, HeisenbergWeilMatrices.act, HeisenbergWeilMatrices.colMat, cM, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, h4]
  rfl

def IsChange {A B V W : HSp D} (κ : WA A B ≃+ WA V W) (σ : GA D V × GA D W → GA D A × GA D B) : Prop :=
  Continuous κ ∧ Continuous κ.symm ∧ (∀ x y, symplH V W (κ x) (κ y) = HeisenbergWeilMatrices.hsymp x y) ∧
    (∀ x, κ x ∈ ratL V W ↔ x ∈ HeisenbergWeilMatrices.WQ A B) ∧ (∀ (c : AE D) x, κ (c • x) = c • κ x) ∧
    ∀ g h x, actHom V W g h (κ x) = κ (HeisenbergWeilMatrices.act (σ (g, h)) x)

theorem isChange_kap {A B : HSp D} (hr : A.rank ≤ B.rank) : IsChange (kap A B) id := by
  have := topRing D
  refine ⟨continuous_const.matrix_mul continuous_id, continuous_const.matrix_mul continuous_id, fun x y => ?_,
    fun x => ⟨?_, ?_⟩, fun c x => Matrix.mul_smul (HeisenbergWeilMatrices.gramInvA A)ᵀ c x, actHom_kap hr⟩
  · unfold symplH sympl
    rw [hHom_kap hr]
    rfl
  · rintro ⟨γ, hγ⟩
    refine ⟨A.gramᵀ * γ, ?_⟩
    rw [← (kap A B).symm_apply_apply x, ← hγ]
    exact Matrix.map_mul (f := incA D)
  · rintro ⟨γ, rfl⟩
    exact ⟨(A.gram⁻¹)ᵀ * γ, Matrix.map_mul (f := incA D)⟩

theorem isChange_kapT {A B : HSp D} (hr : A.rank < B.rank) : IsChange (kapT A B) Prod.swap := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := isChange_kap hr.le
  refine ⟨h1.matrix_transpose, h2.comp continuous_id.matrix_transpose, fun x y => ?_, fun x => ?_, fun c x => ?_,
    fun g h x => ?_⟩
  · rw [← h3]
    unfold symplH sympl
    rw [kapT_apply, kapT_apply, hHom_transpose A B hr.ne]
  · rw [← h4]
    constructor
    · rintro ⟨γ, hγ⟩
      exact ⟨γᵀ, congrArg Matrix.transpose hγ⟩
    · rintro ⟨γ, hγ⟩
      exact ⟨γᵀ, congrArg Matrix.transpose hγ⟩
  · rw [kapT_apply, h5]; rfl
  · rw [kapT_apply, actHom_swap A B hr.ne, h6]; rfl

theorem heis_change {A B V W : HSp D} {κ : WA A B ≃+ WA V W} {σ} (hκ : IsChange κ σ) (ψ : AddChar (AF D.host.F) ℂ)
    (u : WA A B) (f : WA V W → ℂ) : Heisenberg₂ ψ V W (κ u) f ∘ κ = HeisenbergWeilMatrices.rho ψ u (f ∘ κ) := by
  funext w
  simp only [Function.comp, Heisenberg₂, HeisenbergWeilMatrices.rho_apply, hκ.2.2.1, map_add]

theorem isSplitIdem_iff (e : AE D) : IsSplitIdem D e ↔ ∃ v, HeisenbergWeilMatrices.IsSplitIdem D v e := by
  classical
  constructor
  · rintro ⟨h1, h2, v, ε, ⟨α, rfl, hv, hv'⟩, h3⟩
    refine ⟨v, h1, h2, h3.trans ?_⟩
    have : α = singleV D.host.F v 1 := by
      refine RestrictedProduct.ext _ _ fun w => ?_
      by_cases hw : w = v
      · subst hw
        exact hv.trans (RestrictedProduct.single_eq_same _ _ _).symm
      · exact (hv' w hw).trans (RestrictedProduct.single_eq_of_ne _ _ hw).symm
    rw [this]; rfl
  · rintro ⟨v, h1, h2, h3⟩
    exact ⟨h1, h2, v, _, ⟨singleV D.host.F v 1, rfl,
      RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) v 1,
      fun w hw => RestrictedProduct.single_eq_of_ne
        (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) 1 hw⟩, h3⟩

theorem suppAt_iff {v} {e : AE D} (he : HeisenbergWeilMatrices.IsSplitIdem D v e) (V : HSp D) (g : GA D V) :
    SuppAt e V g ↔ HeisenbergWeilMatrices.IsAt (HeisenbergWeilMatrices.idemFin D v) g := by
  rw [← he.sum]
  unfold SuppAt HeisenbergWeilMatrices.IsAt
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  change (e + cA D e) * (mt V g i j - (1 : Matrix _ _ (AE D)) i j) = mt V g i j - (1 : Matrix _ _ (AE D)) i j ↔
    (1 - (e + cA D e)) * mt V g i j = (1 - (e + cA D e)) * (1 : Matrix _ _ (AE D)) i j
  constructor <;> intro h <;> linear_combination -h

theorem isDetAt_iff {e : AE D} (he : IsIdempotentElem e) (V : HSp D) (g : GA D V) (x : (AE D)ˣ) :
    IsDetAt e V g x ↔ x = HeisenbergWeilMatrices.atIdem he (HeisenbergWeilMatrices.detA V g) := by
  rw [Units.ext_iff]; rfl

theorem isDetRoot_iff (V : HSp D) (g : GA D V) (x : (AE D)ˣ) :
    IsDetRoot V g x ↔ HeisenbergWeilMatrices.IsRoot D x (HeisenbergWeilMatrices.detA V g) := by
  unfold HeisenbergWeilMatrices.IsRoot
  rw [mul_inv_eq_iff_eq_mul, Units.ext_iff]; rfl

end GlobalTheory.WeilTieCompare

end
