import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLatticeStabiliserFixesVacuumNonsplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalPreimageOfSupportedAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairFixedVectorLatticeVacuumOffLevelsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDatumCharactersUnramifiedOffLevelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.GoodFactor

theorem mt_mul' {D : D7} (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_one' {D : D7} (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [map_one, Units.val_one]

theorem mt_inj {D : D7} (V : HSp D) {a b : GA D V} (h : mt V a = mt V b) : a = b :=
  Subtype.val_injective (Units.ext h)

theorem comm_of_supp_triv {D : D7} {V : HSp D} {f : AE D} {a b : GA D V} (ha : SuppF V f a) (hb : TrivAt V f b) :
    a * b = b * a := by
  apply mt_inj
  have hAB : (mt V a - 1) * (mt V b - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha i l, mul_assoc, mul_left_comm, hb l j, mul_zero]
  have hBA : (mt V b - 1) * (mt V a - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha l j, mul_left_comm, ← mul_assoc, hb i l, zero_mul]
  have e1 : mt V a * mt V b = (mt V a - 1) * (mt V b - 1) + mt V a + mt V b - 1 := by noncomm_ring
  have e2 : mt V b * mt V a = (mt V b - 1) * (mt V a - 1) + mt V b + mt V a - 1 := by noncomm_ring
  rw [mt_mul', mt_mul', e1, e2, hAB, hBA, zero_add, zero_add, add_comm (mt V a)]

theorem actO_one_of_trivAt {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f) {γ : GA D T} (hγ : TrivAt T f γ)
    {u : WO S T} (hu : u ∈ latO S T LS LT fun w => w = v) : actO S T 1 γ u = u := by
  obtain ⟨ε, hε, rfl⟩ := hf
  have hu' := GlobalTheory.VecInvInert.idem_smul_eq hε hu
  have hz : algebraMap (AF D.host.F) (AE D) ε • (mt T γ - 1) = 0 := by
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    exact hγ a b
  have h0 : HMul.hMul (mt T γ - 1) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = (0 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    rw [← hu', Matrix.mul_smul, ← Matrix.smul_mul, hz, Matrix.zero_mul]
  unfold actO
  rw [inv_one, mt_one', Matrix.mul_one]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h0
  exact h0

theorem vacFin_om_trivAt {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f) {γ : GA D T} (hγ : TrivAt T f γ)
    {x : WO S T → ℂ} (hx : GlobalTheory.FinZeta.VacFin ψ S T v x) : GlobalTheory.FinZeta.VacFin ψ S T v (om (1, γ) x) := by
  obtain ⟨hth, hl1, hl2⟩ := hx
  refine ⟨hW.om_pres _ _ hth, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · rw [← actO_one_of_trivAt hf hγ (nsmul_mem hu 2), ← hW.om_heis 1 γ _ x hth, hl1 u hu]
  · rw [← actO_one_of_trivAt hf hγ hu, ← hW.om_heis 1 γ _ x hth, hl2 e he u hu hh]

theorem thetaInner_eq_star_l2 {D : D7} {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (x y : WO S T' → ℂ) :
    thetaIP μ 𝓕 x y = star (GlobalTheory.AdelicScalar.l2 μ 𝓕 x y) := by
  unfold thetaIP GlobalTheory.AdelicScalar.l2 Formalism.IndefR.Lift.pet
  show _ = (starRingEnd ℂ) _
  rw [← integral_conj]
  congr 1; funext w
  simp [mul_comm]

theorem finmult_good : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v f, IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → ∀ k, SuppF (Wc D i) f k → ∃ c : ℂ, ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → thetaIP μ 𝓕 (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) = c * thetaIP μ 𝓕 (R.ωP i t (1, γ) (R.vP i t)) (R.vP i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t μ 𝓕 hμ v f hf hoff k hk
  obtain ⟨a, rfl⟩ := GlobalTheory.T.exists_local_preimage_of_supportedAtPlace D (Wc D i) v f hf k hk
  have hW := hL.thP.ωP i t
  have hvac := GlobalTheory.T.pairFixedVector_latticeVacuum_offLevels D G Pl0 T A Ks R F hL i t v f hf hoff
  have hunr := GlobalTheory.T.weilDatumCharacters_unramified_offLevels D G Pl0 T A Ks R F hL i t v f hf hoff
  obtain ⟨φ, -, hc⟩ := GlobalTheory.VacCoef.vac_coef D R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) hW μ 𝓕 hμ v hunr
  refine ⟨star (φ a), fun γ _ hγ => ?_⟩
  have hcomm := comm_of_supp_triv hk hγ
  have hv' := vacFin_om_trivAt hW hf hγ hvac
  have e : R.ωP i t (1, γ * GlobalTheory.FinZeta.embV (Wc D i) v a) (R.vP i t) =
      R.ωP i t (1, GlobalTheory.FinZeta.embV (Wc D i) v a) (R.ωP i t (1, γ) (R.vP i t)) := by
    rw [← hcomm]
    show _ = (R.ωP i t (1, _) * R.ωP i t (1, γ)) (R.vP i t)
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e, thetaInner_eq_star_l2, thetaInner_eq_star_l2 μ 𝓕 (R.ωP i t (1, γ) (R.vP i t)), hc a _ _ hv' hvac, star_mul']

end GlobalTheory.RawLift.GoodFactor

end
