import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFiniteHeisenbergFockVacuumThetaFunctions
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharFiniteIdelesIsAlgebraicOfResEtaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruentPairsFixVacuumWeilDatumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumFinitePairVacuumAlgebraicCombinationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicInvariantFormVacuumSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryPointsMemOfLevelAndSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumIsAlgebraicCombinationDefiniteBottomStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSelfDualLatticesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.BotExpand

section Gen

open GlobalTheory.MovedAlg GlobalTheory.AlgWave GlobalTheory.RawLift

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem vac_ne_zero (hv : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v) :
    v ≠ 0 := by
  rintro rfl
  obtain ⟨p, hp⟩ := hv.2.norm.1
  have := hv.2.norm.2 p hp
  simp [nrm2] at this

theorem alg_self : IsAlgComb ψ S T v v :=
  ⟨1, fun _ => 1, fun _ => 0, fun _ => isAlgebraic_one, fun _ => Matrix.ext fun _ _ => (infPart D).map_zero, by
    simp [GlobalTheory.SplitScalar.heisO_zero]⟩

theorem theta_of_alg (hψ : IsStdChar D ψ (-1)) (hv : IsThetaFunO ψ S T v) {F : WO S T → ℂ} (hF : IsAlgComb ψ S T v F) :
    IsThetaFunO ψ S T F := by
  obtain ⟨n, c, w, -, -, rfl⟩ := hF
  refine Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
    fun p _ => GlobalTheory.OrientedHeis.theta_smul _ ((GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 _ _ hv)

theorem star_mem {a : ℂ} (ha : a ∈ Qb) : star a ∈ Qb :=
  mem_algebraicClosure_iff.2 ((mem_algebraicClosure_iff.1 ha).algHom (starRingEnd ℂ).toRatAlgHom)

variable (hv : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v)
  (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
include hv hS hT

theorem rigid {F F' : WO S T → ℂ} (hF : IsAlgComb ψ S T v F) (hF' : IsAlgComb ψ S T v F') (h0 : F ≠ 0) {c : ℂ}
    (hc : F' = c • F) : IsAlgebraic ℚ c := by
  obtain ⟨p, hp⟩ := hv.2.norm.1
  have h1 := mem_algebraicClosure_iff.2 (GlobalTheory.T.vacuum_self_dual_lattices hv hS hT p.1 p.2 hp F F hF hF)
  have h2 := mem_algebraicClosure_iff.2 (GlobalTheory.T.vacuum_self_dual_lattices hv hS hT p.1 p.2 hp F F' hF hF')
  have h3 := GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hv.1 (theta_of_alg hv.1 hv.2.theta hF) h0 hp
  rw [hc, thetaInner_smul_right] at h2
  have := div_mem h2 h1
  rw [mul_div_cancel_right₀ _ h3] at this
  exact mem_algebraicClosure_iff.1 this

theorem om_scaled (hW : IsWeilDatumO ψ S T χS χT om) {p : GA D S × GA D T} {κ : ℂ} {F₀ : WO S T → ℂ}
    (h0 : IsAlgComb ψ S T v F₀) (hp : om p v = κ • F₀) {F : WO S T → ℂ} (hF : IsAlgComb ψ S T v F) :
    ∃ F₁, IsAlgComb ψ S T v F₁ ∧ om p F = κ • F₁ := by
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  obtain ⟨x, h⟩ := p
  refine ⟨∑ q, c q • heisO ψ S T (actO S T x h (w q)) F₀, IsAlgComb.finsum _ _ hc fun q => IsAlgComb.Heisenberg₂
    (fun a b ha hb => mem_algebraicClosure_iff.1 (GlobalTheory.BotFourier.psiH_mem hv.1 hS hT ha hb))
    (GlobalTheory.FinApprox.actO_fin _ _ (hw q)) h0, ?_⟩
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, hW.om_heis x h (w q) v hv.2.theta, hp, GlobalTheory.VacSchurFin.heisO_smul', smul_comm]

theorem om_alg (hW : IsWeilDatumO ψ S T χS χT om) {p : GA D S × GA D T}
    (h0 : IsAlgComb ψ S T v (om p v)) {F : WO S T → ℂ} (hF : IsAlgComb ψ S T v F) : IsAlgComb ψ S T v (om p F) := by
  obtain ⟨F₁, h1, h2⟩ := om_scaled hv hS hT hW (κ := 1) h0 (one_smul _ _).symm hF
  rwa [h2, one_smul]

theorem om_ne_zero (p : GA D S × GA D T) : om p v ≠ 0 := fun h => vac_ne_zero hv (by
  have : om p⁻¹ (om p v) = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, h, map_zero])

variable (hcS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hcT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
  (hW : IsWeilDatumO ψ S T χS χT om)
include hcS hcT hW

theorem root_closed {x : GA D S} (hx : x ∈ GfC S) {h : GA D T} (hh : h ∈ GfC T) {m : ℕ} (hm : 0 < m)
    (hp : IsAlgComb ψ S T v (om ((x, h) ^ m) v)) : IsAlgComb ψ S T v (om (x, h) v) := by
  obtain ⟨κ, F, hF, e⟩ := GlobalTheory.T.weilDatum_finite_pair_vacuum_algebraic_combination hv hS hT hcS hcT hW x hx h hh
  have key : ∀ k : ℕ, ∃ F₁, IsAlgComb ψ S T v F₁ ∧ om ((x, h) ^ k) v = κ ^ k • F₁ := by
    intro k
    induction k with
    | zero => exact ⟨v, alg_self, by simp⟩
    | succ k ih =>
      obtain ⟨F₁, h1, h2⟩ := ih
      obtain ⟨F₂, h3, h4⟩ := om_scaled hv hS hT hW hF e h1
      exact ⟨F₂, h3, by rw [pow_succ', map_mul, Module.End.mul_apply, h2, map_smul, h4, smul_smul, pow_succ]⟩
  obtain ⟨F₁, h1, h2⟩ := key m
  have h0 : F₁ ≠ 0 := fun h0 => om_ne_zero hv hS hT _ (by rw [h2, h0, smul_zero])
  rw [e]
  exact hF.smul (IsAlgebraic.of_pow hm (rigid hv hS hT h1 hp h0 h2))

def algGroup : Subgroup (GA D S × GA D T) where
  carrier := {p | p.1 ∈ GfC S ∧ p.2 ∈ GfC T ∧ IsAlgComb ψ S T v (om p v)}
  one_mem' := ⟨one_mem _, one_mem _, by rw [map_one]; exact alg_self⟩
  mul_mem' := fun {p q} hp hq => ⟨mul_mem hp.1 hq.1, mul_mem hp.2.1 hq.2.1, by
    rw [map_mul]; exact om_alg hv hS hT hW hp.2.2 hq.2.2⟩
  inv_mem' := fun {p} hp => ⟨inv_mem hp.1, inv_mem hp.2.1, by
    obtain ⟨κ, F, hF, e⟩ := GlobalTheory.T.weilDatum_finite_pair_vacuum_algebraic_combination hv hS hT hcS hcT hW _ (inv_mem hp.1) _ (inv_mem hp.2.1)
    have e' : om p⁻¹ v = κ • F := e
    have h1 : v = κ • om p F := by
      rw [← map_smul, ← e', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h0 : om p F ≠ 0 := fun h0 => vac_ne_zero hv (by rw [h1, h0, smul_zero])
    rw [e']
    exact hF.smul (rigid hv hS hT (om_alg hv hS hT hW hp.2.2 hF) alg_self h0 h1)⟩

omit hv hS hT hcS hcT hW in
theorem mem_GfC_of_suppAt {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V}
    (hg : Formalism.L2.Theta.SuppAt e V g) : g ∈ GfC V := by
  have h1 := GlobalTheory.SplitScalar.infPart_splitIdem he
  have h2 := GlobalTheory.PlaceDatum.infPart_cA h1
  refine MonoidHom.mem_ker.2 (Units.ext ?_)
  change (Formalism.L2.Theta.mt V g).map (infPart D) = 1
  rw [← sub_eq_zero]
  ext i j
  rw [← GlobalTheory.SplitCharTrivial.map_sub_one, ← hg i j, RingHom.map_mul, RingHom.map_add, h1, h2, add_zero, zero_mul]
  rfl

theorem split_alg {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {g : GA D S} {h : GA D T}
    (hg : Formalism.L2.Theta.SuppAt e S g) (hh : Formalism.L2.Theta.SuppAt e T h) : IsAlgComb ψ S T v (om (g, h) v) := by
  obtain ⟨κ, F, hF, eF⟩ := GlobalTheory.T.weilDatum_finite_pair_vacuum_algebraic_combination hv hS hT hcS hcT hW g (mem_GfC_of_suppAt he hg) h (mem_GfC_of_suppAt he hh)
  obtain ⟨x, hx⟩ := GlobalTheory.WeilDetermined.exists_isDetAt he.1 S g
  obtain ⟨y, hy⟩ := GlobalTheory.WeilDetermined.exists_isDetAt he.1 T h
  obtain ⟨r, hr, hℓ⟩ := hW.om_split e he g h hg hh x y hx hy
  have h1 := GlobalTheory.SplitScalar.infPart_splitIdem he
  have hx1 : infPart D (x : Formalism.L2.Theta.AE D) = 1 := by
    rw [hx, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, h1, RingHom.map_one, zero_mul, zero_add, sub_zero]
  have hy1 : infPart D (y : Formalism.L2.Theta.AE D) = 1 := by
    rw [hy, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, h1, RingHom.map_one, zero_mul, zero_add, sub_zero]
  have hz : ((splitFacO χS χT x y : Circle) : ℂ) ∈ Qb := by
    rw [splitFacO, Circle.coe_mul, Circle.coe_inv]
    exact mul_mem (inv_mem (mem_algebraicClosure_iff.2 (GlobalTheory.T.heckeChar_finiteIdeles_isAlgebraic_of_resEta hv.2.inf hW.hecT hW.resT x hx1)))
      (mem_algebraicClosure_iff.2 (GlobalTheory.T.heckeChar_finiteIdeles_isAlgebraic_of_resEta hv.2.inf hW.hecS hW.resS y hy1))
  have hz1 : star ((splitFacO χS χT x y : Circle) : ℂ) * (splitFacO χS χT x y : Circle) = 1 := by
    rw [Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  generalize ((splitFacO χS χT x y : Circle) : ℂ) = z at hℓ hz hz1

  obtain ⟨p, hp⟩ := hv.2.norm.1
  have hF0 : F ≠ 0 := fun h0 => om_ne_zero hv hS hT _ (by rw [eF, h0, smul_zero])
  have n1 := GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om p.1 p.2 hW hp (g, h) v v hv.2.theta hv.2.theta
  rw [eF, thetaInner_smul_left, thetaInner_smul_right, ← mul_assoc] at n1
  have n2 : star κ * κ ∈ Qb := by
    rw [eq_div_of_mul_eq (GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hv.1 (theta_of_alg hv.1 hv.2.theta hF) hF0 hp) n1]
    exact div_mem (mem_algebraicClosure_iff.2 (GlobalTheory.T.vacuum_self_dual_lattices hv hS hT p.1 p.2 hp v v alg_self alg_self))
      (mem_algebraicClosure_iff.2 (GlobalTheory.T.vacuum_self_dual_lattices hv hS hT p.1 p.2 hp F F hF hF))

  obtain ⟨n, c, w, hc, hw, hFe⟩ := id hF
  obtain ⟨ℓ, l1, l2, l3⟩ := GlobalTheory.T.exists_algebraicInvariantForm_vacuum_splitPlace hv hS hT e he n w hw
  have ha : ℓ F ∈ Qb := by
    rw [hFe, map_sum]
    exact sum_mem fun q _ => by
      rw [map_smul, smul_eq_mul]
      exact mul_mem (mem_algebraicClosure_iff.2 (hc q)) (mem_algebraicClosure_iff.2 (l3 q))
  have e1 := hℓ ℓ l1 v hv.2.theta
  rw [eF, map_smul, smul_eq_mul, l2, mul_one] at e1
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have hz0 : z ≠ 0 := right_ne_zero_of_mul_eq_one hz1
  have ha0 : ℓ F ≠ 0 := fun h0 => mul_ne_zero hr0 hz0 (by rw [← e1, h0, mul_zero])
  have e2 : (r : ℂ) ^ 2 = (star κ * κ) * (star (ℓ F) * ℓ F) := by
    have e3 := congrArg star e1
    rw [star_mul', star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.star_def] at e3
    linear_combination (-(r : ℂ) ^ 2) * hz1 - (star κ * star (ℓ F)) * e1 - (r * z) * e3
  have hrq : (r : ℂ) ∈ Qb := mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow two_pos (mem_algebraicClosure_iff.1
    (e2 ▸ mul_mem n2 (mul_mem (star_mem ha) ha))))
  have hκ : κ ∈ Qb := by
    rw [eq_div_of_mul_eq ha0 e1]
    exact div_mem (mul_mem hrq hz) ha
  rw [eF]
  exact hF.smul (mem_algebraicClosure_iff.1 hκ)

omit hv hS hT hcS hcT hW in
theorem finCong_one (V : HSp D) (N : ℕ) : GlobalTheory.Member.FinCong V N 1 := by
  have h := (GlobalTheory.Member.PrincLevel.levelGroup V N).one_mem
  exact h.2

theorem mem_algGroup {p : GA D S × GA D T} :
    p ∈ algGroup hv hS hT hcS hcT hW ↔ p.1 ∈ GfC S ∧ p.2 ∈ GfC T ∧ IsAlgComb ψ S T v (om p v) := Iff.rfl

set_option maxHeartbeats 1000000 in
theorem source_mem {x : GA D S} (hx : x ∈ GfC S) : (x, (1 : GA D T)) ∈ algGroup hv hS hT hcS hcT hW := by
  obtain ⟨N, hN, hlev⟩ := GlobalTheory.T.congruent_pairs_fix_vacuum_weilDatum hv hS hT hcS hcT hW
  refine GlobalTheory.T.finiteUnitaryPoints_mem_of_level_and_split_place S ((algGroup hv hS hT hcS hcT hW).comap (MonoidHom.inl _ _)) N hN (fun g hg m hm hp => ?_)
    (fun k hk hc => ?_) (fun e he g hg => ?_) x hx
  · rw [Subgroup.mem_comap, map_pow, mem_algGroup] at hp
    rw [Subgroup.mem_comap, MonoidHom.inl_apply, mem_algGroup]
    exact ⟨hg, one_mem _, root_closed hv hS hT hcS hcT hW hg (one_mem _) hm hp.2.2⟩
  · rw [Subgroup.mem_comap, MonoidHom.inl_apply, mem_algGroup, hlev k hk 1 (one_mem _) hc (finCong_one T N)]
    exact ⟨hk, one_mem _, alg_self⟩
  · rw [Subgroup.mem_comap, MonoidHom.inl_apply, mem_algGroup]
    exact ⟨mem_GfC_of_suppAt he hg, one_mem _,
      split_alg hv hS hT hcS hcT hW he hg (GlobalTheory.WeilDetermined.suppAt_one e T)⟩

set_option maxHeartbeats 1000000 in
theorem target_mem {h : GA D T} (hh : h ∈ GfC T) : ((1 : GA D S), h) ∈ algGroup hv hS hT hcS hcT hW := by
  obtain ⟨N, hN, hlev⟩ := GlobalTheory.T.congruent_pairs_fix_vacuum_weilDatum hv hS hT hcS hcT hW
  refine GlobalTheory.T.finiteUnitaryPoints_mem_of_level_and_split_place T ((algGroup hv hS hT hcS hcT hW).comap (MonoidHom.inr _ _)) N hN (fun g hg m hm hp => ?_)
    (fun k hk hc => ?_) (fun e he g hg => ?_) h hh
  · rw [Subgroup.mem_comap, map_pow, mem_algGroup] at hp
    rw [Subgroup.mem_comap, MonoidHom.inr_apply, mem_algGroup]
    exact ⟨one_mem _, hg, root_closed hv hS hT hcS hcT hW (one_mem _) hg hm hp.2.2⟩
  · rw [Subgroup.mem_comap, MonoidHom.inr_apply, mem_algGroup, hlev 1 (one_mem _) k hk (finCong_one S N) hc]
    exact ⟨one_mem _, hk, alg_self⟩
  · rw [Subgroup.mem_comap, MonoidHom.inr_apply, mem_algGroup]
    exact ⟨one_mem _, mem_GfC_of_suppAt he hg,
      split_alg hv hS hT hcS hcT hW he (GlobalTheory.WeilDetermined.suppAt_one e S) hg⟩

theorem om_vac_algComb {x : GA D S} (hx : x ∈ GfC S) {h : GA D T} (hh : h ∈ GfC T) :
    IsAlgComb ψ S T v (om (x, h) v) := by
  have h3 := (algGroup hv hS hT hcS hcT hW).mul_mem (source_mem hv hS hT hcS hcT hW hx)
    (target_mem hv hS hT hcS hcT hW hh)
  rw [Prod.mk_mul_mk, mul_one, one_mul, mem_algGroup] at h3
  exact h3.2.2

end Gen

theorem ker'_eq_sum_jets : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ → IsBottomTri W i j X →
    ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW, ∃ (k : ℕ) (c : Fin k → ℂ) (w : Fin k → WO A' WW),
      (∀ l, IsAlgebraic ℚ (c l)) ∧ (∀ l, (w l).map (infPart D) = 0) ∧
      (∀ l, ∃ m : ℕ, 0 < m ∧ m • w l ∈ latO A' WW X.rA'.Λ X.rW.Λ fun _ => True) ∧
      ∀ P : PolF D WW.rank A'.rank, X.ker' W.ψ W.θ t P h x =
        ∑ l, c l * pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (heisO W.ψ A' WW (w l) X.vac') P 0 := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t x hx h hh
  have hW : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
  have hv : IsVacO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.Λ X.rW.Λ X.vac' := hX.is.isVac'
  have hθ : IsInfFam W.θ := hv.2.inf
  have hS : IsSelfDualC A' X.rA'.Λ := hX.is.rigA'.1
  have hT : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hf := GlobalTheory.T.finiteDatum_isAlgebraicCombination_definiteBottom hX t
  obtain ⟨k, c, w, hc, hw, e⟩ := om_alg hv hS hT hW (om_vac_algComb hv hS hT (fun τ => (hX.is.rigA'.2.2 τ).1)
    (fun τ => (hX.is.rigW.2.2 τ).1) hW hx hh) hf
  refine ⟨k, c, w, hc, hw, fun l => GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hS.1 hT.1 _ (hw l), fun P => ?_⟩
  have e1 := (GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ A' WW _ _ (X.ω' t) hW hθ X.rA'.s X.rA'.s X.rA'.B X.rA'.B
    X.rW.s X.rW.s X.rW.B X.rW.B x h
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hx, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hh, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hx, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hh, Matrix.one_mul]) (X.f' t)
    (theta_of_alg hv.1 hv.2.theta hf) P).2
  have e2 := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ A' WW hv.1 hθ X.rA'.s X.rW.s X.rA'.B X.rW.B X.vac'
    hv.2.theta k c w hw P).1
  have ft := (GlobalTheory.FinTranslate.finite_translate D W.ψ W.θ A' WW hv.1 hθ X.vac' hv.2.theta).2
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker' thetaKO
  rw [e1, e, ← e2, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [(ft (w l) (hw l)).2, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.BotExpand

end
