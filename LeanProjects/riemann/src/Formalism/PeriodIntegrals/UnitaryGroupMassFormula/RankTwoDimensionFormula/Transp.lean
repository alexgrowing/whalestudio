import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.DimFormCOfSteps
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem tr_repr_eq (y : (VS D).V) (i : Fin X.B.I.n) : X.bas.repr y i = X.ιE (X.crd y i) := by
  exact (X.ιE.apply_symm_apply (X.bas.repr y i)).symm

theorem tr_crd_injective : Function.Injective X.crd := by
  intro a b h
  apply X.bas.repr.injective
  ext i
  rw [tr_repr_eq X a i, tr_repr_eq X b i, h]

def trLin (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  Matrix.toLin X.bas X.bas (M.map X.ιE)

theorem tr_crd_lin (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    X.crd (trLin X M y) = M *ᵥ X.crd y := by
  have h := LinearMap.toMatrix_mulVec_repr X.bas X.bas (Matrix.toLin X.bas X.bas (M.map X.ιE)) y
  rw [LinearMap.toMatrix_toLin] at h
  funext i
  apply X.ιE.injective
  rw [← tr_repr_eq]
  show X.bas.repr (Matrix.toLin X.bas X.bas (M.map X.ιE) y) i = _
  rw [← h]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, tr_repr_eq]

theorem tr_lin_mul (M N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    (trLin X M).comp (trLin X N) = trLin X (M * N) := by
  have hm : (M * N).map X.ιE = M.map X.ιE * N.map X.ιE := by
    ext i j
    simp [Matrix.mul_apply, map_sum, map_mul]
  unfold trLin
  rw [hm, Matrix.toLin_mul X.bas X.bas X.bas]

theorem tr_lin_one : trLin X 1 = LinearMap.id := by
  unfold trLin
  rw [Matrix.map_one _ (map_zero X.ιE) (map_one X.ιE), Matrix.toLin_one]

def trEquiv (M : GL (Fin X.B.I.n) X.B.I.E) : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (trLin X (M : Matrix _ _ _)) (trLin X ((M⁻¹ : GL _ _) : Matrix _ _ _))
    (by rw [tr_lin_mul, Units.mul_inv, tr_lin_one])
    (by rw [tr_lin_mul, Units.inv_mul, tr_lin_one])

theorem tr_crd (M : GL (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    X.crd (trEquiv X M y) = (M : Matrix _ _ _) *ᵥ X.crd y := tr_crd_lin X _ y

theorem tr_af_nontrivial (F : Type) [Field F] [NumberField F] : Nontrivial (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.mp (NumberField.RingOfIntegers.not_isField F)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨p, hp, hp0⟩
  haveI : Nonempty (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) := ⟨v⟩
  first
    | infer_instance
    | exact (RestrictedProduct.evalRingHom _ v).domain_nontrivial
    | exact ⟨⟨0, 1, fun h => zero_ne_one (congrArg (fun x => x.1 v) h)⟩⟩

attribute [local instance] tr_af_nontrivial

theorem tr_star (a : X.B.I.E) : star (X.ιE a) = X.ιE (star a) :=
  (Formalism.BasicNotions.bridge_star_holds D.R D.host _).trans (X.ιE_conj a).symm

theorem tr_hT (x y : (VS D).V) :
    (VS D).hT x y = X.ιE (star (X.crd x) ⬝ᵥ (X.B.I.J *ᵥ X.crd y)) := by
  conv_lhs => rw [← X.bas.sum_repr x, ← X.bas.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul, starRingEnd_apply, tr_repr_eq, tr_star, ← X.J_eq, dotProduct, Matrix.mulVec,
    Pi.star_apply, map_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem tr_isom (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) :
    trEquiv X M ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
  have hM' : Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * X.B.I.J *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J := hM
  have hH : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)ᴴ =
      Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) := by
    ext i j
    rfl
  show ∀ a b, (VS D).hT (trEquiv X M a) (trEquiv X M b) = (VS D).hT a b
  intro a b
  rw [tr_hT, tr_hT, tr_crd, tr_crd]
  congr 1
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hH, hM']

theorem transport_holds : Transport := by
  intro D X u γ
  have hG : (γ : X.B.I.GA) ∈ X.B.I.GFset := (Subgroup.mem_inf.1 γ.2).1
  obtain ⟨M, hM, -, hf⟩ := hG
  have hH : ∀ y ∈ fixSet X u, X.B.I.fmat (iotaF X u γ : X.B.I.Gf) *ᵥ incl X.B.I y = incl X.B.I y :=
    (iotaF X u γ).2
  have hcoe : ((iotaF X u γ : Hfin X u) : X.B.I.Gf) = (γ : X.B.I.GA).2 := rfl
  have hinc : ∀ v, X.B.I.fmat (γ : X.B.I.GA).2 *ᵥ incl X.B.I v =
      incl X.B.I ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ v) := by
    intro v
    rw [hf]
    funext i
    exact (RingHom.map_mulVec _ _ _ i).symm
  have hfixc : ∀ y ∈ fixSet X u, (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y = y := by
    intro y hy
    have h1 := hH y hy
    rw [hcoe, hinc] at h1
    funext i
    exact Formalism.UG.P.inclE_injective _ _ _ (congrFun h1 i)
  have hfix : ∀ y, X.crd y ∈ fixSet X u → trEquiv X M y = y := by
    intro y hy
    apply tr_crd_injective X
    rw [tr_crd, hfixc _ hy]
  refine ⟨trEquiv X M, ⟨tr_isom X M hM, fun j => ?_, ?_⟩, fun h => ?_⟩
  · show Submodule.map _ (Submodule.span _ _) = Submodule.span _ _
    rw [Submodule.map_span, Set.image_image, X.Fu_e]
    congr 1
    apply Set.image_congr
    intro a _
    exact hfix _ (Or.inl (Or.inl ⟨a, rfl⟩))
  · rw [X.flagZVector]
    exact hfix _ (Or.inr rfl)
  · ext y
    have key : X.B.I.fmat ((iotaF X u γ : X.B.I.Gf))⁻¹ *ᵥ incl X.B.I (X.crd y) =
        incl X.B.I (X.crd ((trEquiv X M).symm y)) := by
      have e1 : incl X.B.I (X.crd y) =
          X.B.I.fmat (iotaF X u γ : X.B.I.Gf) *ᵥ incl X.B.I (X.crd ((trEquiv X M).symm y)) := by
        rw [hcoe, hinc, ← tr_crd, LinearEquiv.apply_symm_apply]
      rw [e1, Matrix.mulVec_mulVec]
      have e2 : X.B.I.fmat ((iotaF X u γ : X.B.I.Gf))⁻¹ * X.B.I.fmat (iotaF X u γ : X.B.I.Gf) =
          X.B.I.fmat (((iotaF X u γ : X.B.I.Gf))⁻¹ * (iotaF X u γ : X.B.I.Gf)) := rfl
      rw [e2, inv_mul_cancel]
      exact Matrix.one_mulVec _
    have e : ((iotaF X u γ : X.B.I.Gf) * h * X.xu u)⁻¹ = (h * X.xu u)⁻¹ * (iotaF X u γ : X.B.I.Gf)⁻¹ := by
      group
    rw [LinearEquiv.image_eq_preimage_symm]
    simp only [latS, Set.mem_ofPred_eq, Set.mem_preimage]
    rw [e]
    have ef : X.B.I.fmat ((h * X.xu u)⁻¹ * (iotaF X u γ : X.B.I.Gf)⁻¹) =
        X.B.I.fmat (h * X.xu u)⁻¹ * X.B.I.fmat ((iotaF X u γ : X.B.I.Gf))⁻¹ := rfl
    rw [ef, ← Matrix.mulVec_mulVec, key]

end PI.UnitaryDimensionFormula
