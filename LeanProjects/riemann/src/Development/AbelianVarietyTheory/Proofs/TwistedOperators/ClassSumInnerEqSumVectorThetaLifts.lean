import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOfClassSums
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLiftFormsFiniteGroupAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicLiftDatumOfConjugateLiftDatumStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftGram

theorem inner_eq_sum_upLift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ U₁ ∈ R.Wall i σ, ∀ U₂ ∈ R.Wall i σ, ∀ z₁ z₂ : H.H,
    (∀ h w, inner ℂ (c.ext (H.e z₁) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) (U₁ fun ρ => v ρ) h) →
    (∀ h w, inner ℂ (c.ext (H.e z₂) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) (U₂ fun ρ => v ρ) h) →
    ∀ {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℂ c.W),
      inner ℂ z₁ z₂ = ∑ k, GlobalTheory.AdelicScalar.l2 (R.νV i A.μ0) (R.fdV i A.μ0) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₁ fun ρ => v ρ)) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₂ fun ρ => v ρ)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hirr hS hI hFo hZ hδ i σ s m μ' η' ω B f₀ f c io H hd hν hy hH v hv U₁ hU₁ U₂ hU₂
    z₁ z₂ h₁ h₂ ι _ b
  have hc : c.Is := hd.2.2.2.2.2.2.2.2.2.1
  refine (GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)).elim fun μ h0 => h0.elim fun 𝓧 hμ => ?_
  have h5 := (hd.1.models.νW i).1.2.2 R.θ hd.1.models.inf
  refine h5.1.elim fun Fr hFr => (h5.2 Fr hFr).1.elim fun mR hmR => ?_
  have hint : ∀ k, IntegrableOn (fun h =>
      GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₁ fun ρ => v ρ) h *
      starRingEnd ℂ (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k)))
        (U₂ fun ρ => v ρ) h)) (R.fdV i A.μ0) (R.νV i A.μ0) := fun k =>
    (hI i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io hd _ _ hν μ 𝓧 hμ Fr hFr mR hmR U₁ hU₁ U₂ hU₂ v v
      (io (PiTensorProduct.tprod ℂ v) (b k)) (io (PiTensorProduct.tprod ℂ v) (b k))).2.1
  have hx := fun z => (SetLike.ext_iff.mp hH.2.1 _).mp (LinearMap.mem_range_self H.e z)
  have e1 := GlobalTheory.AdelicScalar.integral_eq_classSum (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m) hν hy
    (fun h => inner ℂ (c.ext (H.e z₁) h) (c.ext (H.e z₂) h)) fun γ hγ k hk x =>
      (congrArg₂ (inner ℂ) (GlobalTheory.AdelicScalar.ext_law c _ _ (hx z₁) hγ k hk x) (GlobalTheory.AdelicScalar.ext_law c _ _ (hx z₂) hγ k hk x)).trans
        (GlobalTheory.AdelicScalar.inner_law c.ρ hc.2.1 (GlobalTheory.AdelicScalar.norm_levChi _ _ k) _ _ _)
  simp only [GlobalTheory.AdelicScalar.ext_finLift c hc] at e1
  rw [hH.2.2 z₁ z₂]
  unfold Bridge.adInner
  rw [← e1]
  have e2 : ∀ h, inner ℂ (c.ext (H.e z₁) h) (c.ext (H.e z₂) h) = ∑ k,
      GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₁ fun ρ => v ρ) h *
      starRingEnd ℂ (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k)))
        (U₂ fun ρ => v ρ) h) := fun h =>
    (b.sum_inner_mul_inner _ _).symm.trans (Finset.sum_congr rfl fun k _ => congrArg₂ (· * ·) (h₁ h (b k))
      ((inner_conj_symm _ _).symm.trans (congrArg (starRingEnd ℂ) (h₂ h (b k)))))
  refine (congrArg (fun F => ∫ h in R.fdV i A.μ0, F h ∂(R.νV i A.μ0)) (funext e2)).trans ?_
  exact integral_finsetSum _ fun k _ => hint k

end GlobalTheory.LiftGram

end
