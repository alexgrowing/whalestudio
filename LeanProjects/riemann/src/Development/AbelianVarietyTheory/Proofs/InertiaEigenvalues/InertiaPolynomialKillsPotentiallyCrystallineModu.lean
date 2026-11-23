import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContMapRepIotaOQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotSemistableOfPotCrystallineDecompositionGroupStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGaloisRepDecompositionInduced
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharPolyInertiaOfPotSemistableEnlargementStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalInertiaEqZeroPotSemistableDieudonneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalKillsPotCrystallineOfKillsPotSemistableStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open TensorProduct

namespace GlobalTheory.KillLocal

theorem actPow {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (g : G) (n : ℕ) (x : V ⊗[Qp] B) :
    actVB PD ρ (g ^ n) x = (actVB PD ρ g ^ n) x := by
  induction n generalizing x with
  | zero =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB]
    | add a b ha hb => rw [map_add, ha, hb, map_add]
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, ← ih]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, map_mul, AlgEquiv.mul_apply]
    | add a b ha hb => rw [map_add, ha, hb, map_add, map_add]

theorem sumAeval {O LL M : Type} [CommRing O] [Field LL] [AddCommGroup M] [Module LL M] (f : O →+* LL)
    (T : Module.End LL M) (p : O[X]) (x : M) :
    ∑ n ∈ Finset.range (p.natDegree + 1), f (p.coeff n) • (T ^ n) x = Polynomial.aeval T (p.map f) x := by
  rw [Polynomial.aeval_eq_sum_range' (n := p.natDegree + 1) (Nat.lt_succ_of_le Polynomial.natDegree_map_le)]
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, Polynomial.coeff_map]

theorem main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) = algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c') (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) → (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (r.comp (decS D.nd w))) → ∀ σ : Gw D.nd w, (σ : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) → ∀ p : (D.nd.O i)[X], p.map (iotaO D.nd D.naut i) = (GlobalTheory.Pst.wdAt (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w)).inePol (σ : GE D.nd) → ∀ d ∈ (pc (D.loc (D.nd.l i)) h hN hF hS).Dpcris ((D.nbr i w hw).rep (r.comp (decS D.nd w))), ∑ n ∈ Finset.range (p.natDegree + 1), (D.nbr i w hw).toLL (p.coeff n) • actVB ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ((D.nbr i w hw).rep (r.comp (decS D.nd w))) ((D.nbr i w hw).e (σ ^ n)) d = 0 := by
  intro D i w hw K' h hN hF hS m r hr hpc σ hσ p hp d hd
  have hPst := GlobalTheory.T.potSemistable_of_potCrystalline_decompositionGroup D i w hw K' h hN hF hS m r hr hpc
  obtain ⟨LL', hL, hV', hchar⟩ := GlobalTheory.T.charPoly_inertia_of_potSemistable_enlargement D i w hw m r hPst
  have hq := hchar σ hσ p hp
  have hkill := GlobalTheory.T.aeval_inertia_eq_zero_potSemistableDieudonne (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) _ hV' ⟨(σ : GE D.nd), hσ⟩ _ hq
  have hinj : Function.Injective (GlobalTheory.PstLine.incV hL m) := by
    intro x y hxy
    funext j
    exact (IntermediateField.inclusion hL).injective (congrFun hxy j)
  have hd' := GlobalTheory.T.aeval_kills_potCrystalline_of_kills_potSemistable (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL LL' h hN hF hS hL _ _ (GlobalTheory.PstLine.incV hL m) hinj (GlobalTheory.PstLine.isMor_incV (D.nbr i w hw) hL m _) _ (p.map (D.nbr i w hw).toLL) hkill d hd
  have hg : GlobalTheory.Pst.weilToGK (D.nbr i w hw) (D.nd.plOm.2 w) (GlobalTheory.WeilDeligne.ineIncl (D.nd.plOm.2 w) ⟨(σ : GE D.nd), hσ⟩) = (D.nbr i w hw).e σ := rfl
  have key : ∑ n ∈ Finset.range (p.natDegree + 1), (D.nbr i w hw).toLL (p.coeff n) • ((actVB ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ((D.nbr i w hw).rep (r.comp (decS D.nd w))) ((D.nbr i w hw).e σ)) ^ n) d = 0 := by
    rw [sumAeval]
    exact hd'
  refine (Finset.sum_congr rfl fun n _ => ?_).trans key
  have e1 : (D.nbr i w hw).e (σ ^ n) = (D.nbr i w hw).e σ ^ n := map_pow _ σ n
  exact congrArg _ ((congrArg (fun g => actVB ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ((D.nbr i w hw).rep (r.comp (decS D.nd w))) g d) e1).trans (actPow _ _ _ _ _))

end GlobalTheory.KillLocal
