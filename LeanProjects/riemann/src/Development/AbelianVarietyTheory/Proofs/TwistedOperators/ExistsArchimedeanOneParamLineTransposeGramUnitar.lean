import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TransportedLine

variable {D : D7}

theorem exp_mem_UH_of_lie {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit H.det) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : Xᴴ * H + H * X = 0) (t : ℝ) : NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH H := by
  have hu' : IsUnit H := (isUnit_iff_isUnit_det H).2 hu
  have e : (t • X)ᴴ = H * (-(t • X)) * H⁻¹ := by
    have h1 : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
    have h2 : Xᴴ = -(H * X) * H⁻¹ := by rw [← h1, mul_assoc, mul_nonsing_inv _ hu, mul_one]
    rw [conjTranspose_smul, h2]
    simp
  show (NormedSpace.exp (t • X))ᴴ * H * NormedSpace.exp (t • X) = H
  rw [← Matrix.exp_conjTranspose, e, Matrix.exp_conj _ _ hu', mul_assoc _ H⁻¹, nonsing_inv_mul _ hu, mul_one, mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • X)).neg_left, neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem gramAt_det_isUnit (V : HSp D) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ).det := by
  have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det (tauE D τ) V.gram).symm
  rw [this]
  exact ((_root_.map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)).isUnit

variable (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e)

def toUXHom : GA D X →* GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J where
  toFun := GlobalTheory.TripleRead.toUX X e hJ
  map_one' := by
    refine Subtype.ext (Units.ext ?_)
    show (mt X 1).submatrix e e = 1
    simp [Formalism.L2.Theta.mt]
  map_mul' a b := by
    refine Subtype.ext (Units.ext ?_)
    show (mt X (a * b)).submatrix e e = (mt X a).submatrix e e * (mt X b).submatrix e e
    simp [Formalism.L2.Theta.mt, Matrix.submatrix_mul_equiv]

theorem continuous_toUX : Continuous (GlobalTheory.TripleRead.toUX X e hJ) := by
  have hm : Continuous fun g : GA D X => (matHom X g) := continuous_subtype_val
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · have hv : Continuous fun g : GA D X =>
        (matHom X g).1 := Units.continuous_val.comp hm
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply (e j)).comp ((continuous_apply (e i)).comp hv)
  · have hv : Continuous fun g : GA D X =>
        ((matHom X g)⁻¹).1 := Units.continuous_coe_inv.comp hm
    refine continuous_pi fun i => continuous_pi fun j => ?_
    refine ((continuous_apply (e j)).comp ((continuous_apply (e i)).comp hv)).congr fun g => ?_
    show ((matHom X g)⁻¹).1 (e i) (e j) = (mt X g⁻¹) (e i) (e j)
    simp [Formalism.L2.Theta.mt]

def finIncl (F : Type) [Field F] [NumberField F] : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F →ₗ[F] AF F where
  toFun a := ((0, a) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  map_add' a b := by
    show ((0, a + b) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = ((0, a) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) + ((0, b) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
    simp
  map_smul' c a := by
    show ((0, c • a) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = c • ((0, a) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
    simp

theorem smul_eq_zero_of_snd (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : AF F ⊗[F] E) (hx : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x = 0) (u : AF F)
    (hu : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F u = 0) : u • x = 0 := by
  let e : AF F := ((0, 1) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  have h1 : (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).1 = 0 :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  have hu' : u = u * e := by
    refine Prod.ext ?_ ?_
    · show (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).1 = (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).1 * 0
      rw [mul_zero]; exact h1
    · show (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).2 = (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).2 * 1
      rw [mul_one]
  have key : ∀ y : AF F ⊗[F] E,
      e • y = (finIncl F).rTensor E (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
      congr 1
      show ((0, 1) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) * (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from a) =
        ((0, (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from a).2) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
      refine Prod.ext ?_ ?_
      · exact zero_mul _
      · exact one_mul _
    | add y z hy hz => rw [smul_add, hy, hz, map_add, map_add]
  rw [hu', mul_smul, key, hx, map_zero, smul_zero]

theorem toUX_mem_UAt (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k) (hJ : Z.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    {g : GA D X} (hg : g ∈ GinfC X) :
    GlobalTheory.TripleRead.toUX X e hJ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Z (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) := by
  intro u hu
  have h1 : (finHom X g).val = 1 := by rw [show finHom X g = 1 from hg]; rfl
  have hM : ∀ a b, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((Formalism.L2.Theta.mt X g - 1) a b) = 0 := by
    intro a b
    have e2 := congrFun (congrFun h1 a) b
    rw [Matrix.sub_apply, map_sub]
    refine sub_eq_zero.2 ((congrArg id e2).trans ?_)
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.TripleRead.toUX X e hJ g) - 1 = (Formalism.L2.Theta.mt X g - 1).submatrix e e := by
    show (Formalism.L2.Theta.mt X g).submatrix e e - 1 = _
    ext i j
    simp [Matrix.one_apply, e.injective.eq_iff]
  rw [hr]
  ext i j
  rw [Matrix.smul_apply, Matrix.zero_apply, Matrix.submatrix_apply]
  exact smul_eq_zero_of_snd _ _ _ (hM _ _) u hu

theorem continuous_exp_smul {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun t : ℝ => NormedSpace.exp (t • Y) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

end GlobalTheory.TransportedLine

namespace GlobalTheory.TransportedLine

theorem exists_line_toUX_oneP : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank)
    (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k) (hJ : Z.J = D.host.xi0 • (X.gramᵀ).submatrix e e) (τ : D.what₂.Tau),
    ∀ Y ∈ lieAt X τ, ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Z,
      ∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X e hJ (oneP θ X τ Y t) := by
  intro D θ hθ X k e Z hJ τ Y hY
  have hU : ∀ t : ℝ, NormedSpace.exp (t • Y) ∈ Formalism.QuantumDeterminants.UH (gramAt D X τ) :=
    exp_mem_UH_of_lie (gramAt_det_isUnit X τ) hY
  let φ : Multiplicative ℝ →* GA D X :=
    { toFun := fun t => oneP θ X τ Y (Multiplicative.toAdd t)
      map_one' := by
        show atTau θ X τ (NormedSpace.exp ((0 : ℝ) • Y)) = 1
        rw [zero_smul, NormedSpace.exp_zero]
        exact GlobalTheory.PointAtPlaceHom.atTau_one hθ X τ
      map_mul' := fun s t => by
        show atTau θ X τ (NormedSpace.exp ((Multiplicative.toAdd s + Multiplicative.toAdd t) • Y)) =
          atTau θ X τ (NormedSpace.exp (Multiplicative.toAdd s • Y)) * atTau θ X τ (NormedSpace.exp (Multiplicative.toAdd t • Y))
        rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _)]
        exact GlobalTheory.PointAtPlaceHom.atTau_mul hθ X τ (hU _) (hU _) }
  refine ⟨(toUXHom X e hJ).comp φ, ⟨?_, fun t => ?_⟩, fun t => rfl⟩
  · have hc : Continuous fun t : ℝ => oneP θ X τ Y t :=
      (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ X τ).comp_continuous (continuous_exp_smul Y) hU
    exact (continuous_toUX X e hJ).comp (hc.comp continuous_toAdd)
  · exact toUX_mem_UAt X e Z hJ (GlobalTheory.PointAtPlaceHom.atTau_mem X τ _)

end GlobalTheory.TransportedLine

end
