import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOfTsumEnormLtTop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsoluteThetaIntegralLeContinuousSeminorm
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitGram

variable {D : D7}

abbrev sg (D : D7) : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)

theorem gramQ_eq (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E) :
    gramQ V x = Formalism.UG.cT (sg D) x * (HSpace.gram V * x) := rfl

theorem gramQ_mul (V : HSp D) {r : ℕ} {δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E}
    (hδ : Formalism.UG.cT (sg D) δ * HSpace.gram V * δ = HSpace.gram V)
    (x : Matrix (Fin V.rank) (Fin r) D.host.E) : gramQ V (δ * x) = gramQ V x := by
  rw [gramQ_eq, gramQ_eq, Formalism.UG.cT_mul]
  calc Formalism.UG.cT (sg D) x * Formalism.UG.cT (sg D) δ * (HSpace.gram V * (δ * x))
      = Formalism.UG.cT (sg D) x * ((Formalism.UG.cT (sg D) δ * HSpace.gram V * δ) * x) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hδ]

theorem gramQ_herm (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E) :
    ((gramQ V x).map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = gramQ V x := by
  have hJ : Formalism.UG.cT (sg D) (HSpace.gram V) = HSpace.gram V := Matrix.ext fun i j => (GlobalTheory.Doubling.isHermND_gram V).1 i j
  have hx : Formalism.UG.cT (sg D) (Formalism.UG.cT (sg D) x) = x := Matrix.ext fun i j => star_star (x i j)
  change Formalism.UG.cT (sg D) (gramQ V x) = gramQ V x
  rw [gramQ_eq, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hx, hJ, Matrix.mul_assoc]

theorem leftInv_subtypeSum {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (V : HSp D) {n : ℕ}
    (f : Mx D V.rank n → M) (p : Matrix (Fin V.rank) (Fin n) D.host.E → Prop)
    (hp : ∀ δ : GL (Fin V.rank) D.host.E, Formalism.UG.cT (sg D) δ.1 * HSpace.gram V * δ.1 = HSpace.gram V →
      ∀ ξ, p ξ → p (δ.1 * ξ)) :
    LeftInv (GQ V) fun h => ∑' ξ : {ξ : Matrix (Fin V.rank) (Fin n) D.host.E // p ξ},
      f (GlobalTheory.SiegelFormula.invPt V h ξ.1) := by
  intro γ hγ h
  obtain ⟨δ, hU, hδ⟩ : ∃ δ : GL (Fin V.rank) D.host.E, _ ∧ Formalism.UG.bc (incA D) δ = Formalism.L2.Theta.matHom V γ⁻¹ := inv_mem hγ
  have hU' : Formalism.UG.cT (sg D) δ.1 * HSpace.gram V * δ.1 = HSpace.gram V := hU
  have hUi : Formalism.UG.cT (sg D) (δ⁻¹).1 * HSpace.gram V * (δ⁻¹).1 = HSpace.gram V :=
    (Formalism.UG.UJ (sg D) (HSpace.gram V)).inv_mem hU
  let e : {ξ : Matrix (Fin V.rank) (Fin n) D.host.E // p ξ} ≃ {ξ : Matrix (Fin V.rank) (Fin n) D.host.E // p ξ} :=
    ⟨fun ξ => ⟨δ.1 * ξ.1, hp δ hU' _ ξ.2⟩, fun ξ => ⟨(δ⁻¹).1 * ξ.1, hp δ⁻¹ hUi _ ξ.2⟩,
      fun ξ => Subtype.ext (by simp), fun ξ => Subtype.ext (by simp)⟩
  have h1 : Formalism.L2.Theta.mt V γ⁻¹ = δ.1.map (incA D) := (congrArg Units.val hδ).symm
  have h2 : Formalism.L2.Theta.mt V (γ * h)⁻¹ = Formalism.L2.Theta.mt V h⁻¹ * Formalism.L2.Theta.mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq fun ξ => f (GlobalTheory.SiegelFormula.invPt V h ξ.1))
  simp only [GlobalTheory.SiegelFormula.invPt, e, Equiv.coe_fn_mk, h2, h1, Matrix.mul_assoc, Matrix.map_mul]

def fibreEquiv (V : HSp D) (r : ℕ) :
    (Σ β : HermE D r, {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1}) ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r} where
  toFun p := ⟨p.2.1, p.2.2.1⟩
  invFun x := ⟨⟨gramQ V x.1, gramQ_herm V x.1⟩, ⟨x.1, x.2, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨b, hb⟩, x, hx, hg⟩
    change gramQ V x = b at hg
    subst hg
    rfl
  right_inv _ := rfl

theorem hasSum_IfrB : ∀ (D : Formalism.BasicNotions.D7) (r : ℕ) (V : Formalism.BasicNotions.TH.HSp D) (θ : InfFam D), IsInfFam θ →
    ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r →
    GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ →
    HasSum (fun β : PositivityTheory.GramSchwartzFunctions.HermE D r => PositivityTheory.GramSchwartzFunctions.BC.IfrB V ν φ β) (PositivityTheory.GramSchwartzFunctions.Ifr V ν φ) := by
  intro D r V θ hθ ν hν φ hφ habs
  have : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hν
  haveI := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
  haveI : Countable (Matrix (Fin V.rank) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin r → D.host.E))
  haveI : Countable (Matrix (Fin r) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin r → Fin r → D.host.E))
  haveI : Countable (HermE D r) :=
    inferInstanceAs (Countable {b : Matrix (Fin r) (Fin r) D.host.E // _})
  have hcont : Continuous φ :=
    (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ φ hφ).1
  have hrank : ∀ (δ : GL (Fin V.rank) D.host.E) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E),
      (δ.1 * ξ).rank = ξ.rank := fun δ ξ =>
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)
  have hA := leftInv_subtypeSum V (fun y => ‖φ y‖ₑ)
    (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r)
    (fun δ _ ξ h => (hrank δ ξ).trans h)
  have hfin : ∫⁻ q, descend (GQ V) (fun g => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r},
      ‖φ (GlobalTheory.SiegelFormula.invPt V g x.1)‖ₑ) q ∂autMeasure V ν < ⊤ := by
    refine (lintegral_mono fun q => ?_).trans_lt habs
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
      (fun ξ => ‖φ (GlobalTheory.SiegelFormula.invPt V q.out ξ)‖ₑ)
  have key := GlobalTheory.CompanionTheory.ThetaOrbit.hasSum_average_descend (Γ := GQ V) (μ := ν) (fibreEquiv V r)
    (fun h x => φ (GlobalTheory.SiegelFormula.invPt V h x.1))
    (fun x => (hcont.comp (GlobalTheory.AbsThetaSemi.continuous_invPt V x.1)).measurable)
    hA
    (fun β => leftInv_subtypeSum V φ
      (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
      (fun δ hδ ξ h => ⟨(hrank δ ξ).trans h.1, (gramQ_mul V hδ ξ).trans h.2⟩))
    hfin
  exact key

end GlobalTheory.CompanionTheory.SplitGram

end
