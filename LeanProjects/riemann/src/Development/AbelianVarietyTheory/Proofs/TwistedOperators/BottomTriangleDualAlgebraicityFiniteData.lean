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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleMonomialSupportFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleFiniteDoubleCosets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingSeesawVacuumDefiniteBottom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactActsOnRealVacuaByDetPowers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenSubgroupFixVacuumTranslates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnThetaDefinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped Topology

noncomputable section

namespace GlobalTheory.BotSpanSnd

open Formalism.L2.Fam.ThC (fixSig)

section General

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem isThetaFunO_of_fixSig {f : WO S T → ℂ} (h : IsThetaFunO ψ (fixSig S) (fixSig T) f) : IsThetaFunO ψ S T f :=
  ⟨h.quasi, h.level, h.cont, h.smooth⟩

theorem isWeilDatumO_fixSig (h : IsWeilDatumO ψ S T χS χT om) : IsWeilDatumO ψ (fixSig S) (fixSig T) χS χT om where
  std := h.std
  hecS := h.hecS
  hecT := h.hecT
  resS := h.resS
  resT := h.resT
  om_pres p f hf := GlobalTheory.VacFixTarget.isThetaFunO_fixSig (h.om_pres p f (isThetaFunO_of_fixSig hf))
  om_heis g k w f hf := h.om_heis g k w f (isThetaFunO_of_fixSig hf)
  om_aut g hg k hk f hf := h.om_aut g hg k hk f (isThetaFunO_of_fixSig hf)
  om_cont f hf := h.om_cont f (isThetaFunO_of_fixSig hf)
  om_unit μ F h1 h2 p f hf := h.om_unit μ F h1 h2 p f (isThetaFunO_of_fixSig hf)
  om_split e he g k hg hk x y hx hy := by
    obtain ⟨r, hr, H⟩ := h.om_split e he g k hg hk x y hx hy
    exact ⟨r, hr, fun ℓ hℓ f hf => H ℓ (fun u hu f' hf' => hℓ u hu f' (GlobalTheory.VacFixTarget.isThetaFunO_fixSig hf')) f
      (isThetaFunO_of_fixSig hf)⟩

set_option maxHeartbeats 1000000 in

theorem exists_cong_fix_vac (hW : IsWeilDatumO ψ S T χS χT om)
    (hcS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hcT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (hsdS : IsSelfDualC S ΛS) (hsdT : IsSelfDualC T ΛT) {f₀ : WO S T → ℂ}
    (hvac : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f₀) :
    ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC T, GlobalTheory.Member.FinCong T N k → om (1, k) f₀ = f₀ := by
  have hθ : IsInfFam θ := hvac.2.inf
  have hev := (GlobalTheory.LatNhds.eventually_actO D S T ΛS ΛT hsdS hsdT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hsdS hsdT)).1
  have hpair : Filter.Tendsto (fun x : GA D T => (((1 : GA D S), x) : GA D S × GA D T)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_const.prodMk continuous_id :
      Continuous fun x : GA D T => (((1 : GA D S), x) : GA D S × GA D T))).tendsto 1
    exact this
  have hev' := hpair.eventually hev
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, ∀ x ∈ GfC T, GlobalTheory.Member.FinCong T n.factorial x →
      ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        actO S T 1 x u ∈
          (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
    by_contra hne
    push_neg at hne
    choose k hk hkc u hu hu' using hne
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk hkc
    obtain ⟨n, hn⟩ := (ht.eventually hev').exists
    exact hu' n (hn _ (hu n))
  have hscal : ∀ k ∈ GfC T, GlobalTheory.Member.FinCong T n₁.factorial k → ∃ c : ℂ, ‖c‖ = 1 ∧ om (1, k) f₀ = c • f₀ := by
    intro k hk hc
    have hΛ : ∀ u : WO S T, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
        (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO S T
        (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        u = actO S T 1 k u₀ := by
      intro u
      constructor
      · intro hu
        refine ⟨actO S T 1 k⁻¹ u, hn₁ k⁻¹ (inv_mem hk) (GlobalTheory.Member.PrincLevel.finCong_inv hc) u hu, ?_⟩
        have := GlobalTheory.WeilVacMove.actO_inv_actO (1 : GA D S) k⁻¹ u
        rw [inv_inv, inv_one] at this
        exact this.symm
      · rintro ⟨u₀, hu₀, rfl⟩
        exact hn₁ k hk hc u₀ hu₀
    have hvac' := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T _ _ om hW hθ sS sS sT sT _ _ _ _ 1 k
      (fun τ => GlobalTheory.SmoothVac.comm_compAt_one S θ τ (sS τ))
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hk τ, Matrix.one_mul, Matrix.mul_one]) hΛ f₀ hvac
    exact GlobalTheory.VacUnique.vacUniqueO D ψ θ hvac.1 hθ (fixSig S) (fixSig T) sS sT (Formalism.L2.Fam.ThC.fixSig_ok _)
      (Formalism.L2.Fam.ThC.fixSig_ok _) hcS hcT ΛS ΛT hsdS hsdT f₀ _ (GlobalTheory.VacFixTarget.isVacO_fixSig hvac)
      (GlobalTheory.VacFixTarget.isVacO_fixSig hvac')
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have hcont : Continuous fun k : GA D T => om (1, k) f₀ w₀ :=
    (hW.om_cont _ hvac.2.theta w₀).comp (continuous_const.prodMk continuous_id)
  have key : ∃ n : ℕ, ∀ k ∈ GfC T, GlobalTheory.Member.FinCong T (n₁.factorial * n.factorial) k → om (1, k) f₀ = f₀ := by
    by_contra hne
    push_neg at hne
    choose k hk hkc hkne using hne
    have hpow : ∀ n, ∃ m : ℕ, ∃ c : ℂ, om (1, k n ^ m) f₀ = c • f₀ ∧ ¬ ‖c - 1‖ ≤ 1 / 2 := by
      intro n
      obtain ⟨c, -, hc⟩ := hscal (k n) (hk n) (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc n))
      have hc1 : c ≠ 1 := by
        rintro rfl
        exact hkne n (by rw [hc, one_smul])
      by_contra h
      push_neg at h
      exact hc1 (GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m =>
        h m (c ^ m) (GlobalTheory.VacFixTarget.om_pow_eq_snd _ (k n) _ c hc m))
    choose m c hmc hc using hpow
    have hmem : ∀ n, k n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup T (n₁.factorial * n.factorial) :=
      fun n => pow_mem (show k n ∈ GlobalTheory.Member.PrincLevel.levelGroup T (n₁.factorial * n.factorial) from ⟨hk n, hkc n⟩) _
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k n ^ m n) (fun n => (hmem n).1)
      (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem n).2)
    have h2 := (hcont.tendsto 1).comp ht
    have e1 : om ((1 : GA D S), (1 : GA D T)) f₀ w₀ = f₀ w₀ := by
      show om 1 f₀ w₀ = _
      rw [map_one]
      rfl
    rw [Function.comp_def, e1] at h2
    have hpos : 0 < ‖f₀ w₀‖ / 2 := half_pos (norm_pos_iff.2 hw₀)
    obtain ⟨n, hn⟩ := (h2.eventually (Metric.ball_mem_nhds _ hpos)).exists
    rw [hmc n, Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← sub_one_mul, norm_mul] at hn
    have := hc n
    push_neg at this
    nlinarith [norm_nonneg (f₀ w₀)]
  obtain ⟨n, hn⟩ := key
  exact ⟨_, Nat.mul_pos n₁.factorial_pos n.factorial_pos, hn⟩

set_option maxHeartbeats 1000000 in

theorem eventually_fix (hW : IsWeilDatumO ψ S T χS χT om)
    (hcS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hcT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (hsdS : IsSelfDualC S ΛS) (hsdT : IsSelfDualC T ΛT) {f₀ : WO S T → ℂ}
    (hvac : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f₀)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) :
    ∀ᶠ k in 𝓝 (1 : GA D T), k ∈ GfC T → om (1, k) f = f := by
  have hspan := GlobalTheory.VacuumChar.mem_span (S := fixSig S) (T := fixSig T) (Formalism.L2.Fam.ThC.fixSig_ok _)
    (Formalism.L2.Fam.ThC.fixSig_ok _) hcS hcT hsdS hsdT (f := f) (GlobalTheory.VacFixTarget.isVacO_fixSig hvac)
    ⟨GlobalTheory.VacFixTarget.isThetaFunO_fixSig hf, hv⟩
  obtain ⟨N, hN, h0⟩ := exists_cong_fix_vac hW hcS hcT hsdS hsdT hvac
  have hN' := GlobalTheory.Member.PrincLevel.finCong_mem_nhds T hN
  have hpair : Filter.Tendsto (fun x : GA D T => (((1 : GA D S), x) : GA D S × GA D T)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_const.prodMk continuous_id :
      Continuous fun x : GA D T => (((1 : GA D S), x) : GA D S × GA D T))).tendsto 1
    exact this
  have htr : ∀ y : WO S T, y.map (infPart D) = 0 →
      ∀ᶠ k in 𝓝 (1 : GA D T), k ∈ GfC T → om (1, k) (heisO ψ S T y f₀) = heisO ψ S T y f₀ := by
    intro y hy0
    obtain ⟨M, hM, hy⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_latO hsdS.1 hsdT.1 y hy0
    have hmv := hpair.eventually ((GlobalTheory.LatNhds.eventually_actO D S T ΛS ΛT hsdS hsdT
      (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hsdS hsdT)).2 y hy0 (2 * M) (Nat.mul_pos two_pos hM))
    filter_upwards [hN', hmv] with k hk hm hkf
    obtain ⟨l, hl, e⟩ := hm
    rw [hW.om_heis 1 k y f₀ hvac.2.theta, h0 k hkf hk]
    have e2 : actO S T 1 k y = y + 2 • (M • l) := by rw [smul_smul]; exact e
    rw [e2]
    refine GlobalTheory.AdForm.SplitGen.heisO_add_two ψ (hvac.2.lat.1 _ (AddSubgroup.nsmul_mem _ hl M)) ?_
    rw [GlobalTheory.RatSelfDual.symplO_nsmul]
    exact GlobalTheory.LatVac.char_sympl_eq_one hvac.1 hsdS hsdT hy hl
  clear hf hv
  change f ∈ Submodule.span ℂ (Set.range fun x : GlobalTheory.VacuumChar.finPts S T => heisO ψ S T x f₀) at hspan
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    exact htr y.1 y.2
  | zero => exact Filter.Eventually.of_forall fun k _ => map_zero _
  | add a b _ _ ha hb => filter_upwards [ha, hb] with k h1 h2 hk; rw [map_add, h1 hk, h2 hk]
  | smul c a _ ha => filter_upwards [ha] with k h1 hk; rw [map_smul, h1 hk]

theorem exists_cong_of_eventually {P : GA D T → Prop} (h : ∀ᶠ k in 𝓝 (1 : GA D T), k ∈ GfC T → P k) :
    ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC T, GlobalTheory.Member.FinCong T N k → P k := by
  by_contra hne
  push_neg at hne
  choose k hk hkc hP using fun n : ℕ => hne n.factorial n.factorial_pos
  obtain ⟨n, hn⟩ := ((GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk hkc).eventually h).exists
  exact hP n (hn (hk n))

end General

section Bottom

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
  {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}

theorem weil_snd (hX : IsBottomTri W i j X) (t : T) : ∃ χ χ', IsWeilDatumO W.ψ A' WW χ χ' (X.ω' t) :=
  ⟨_, _, (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hX.is.weil' t)⟩

theorem theta_snd (hX : IsBottomTri W i j X) (t : T) : IsThetaFunO W.ψ A' WW (X.f' t) :=
  GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hX.is.isVac'.1 hX.is.isVac'.2.inf (hX.is.snd t) hX.is.isVac'.2.theta

theorem fock_snd (hX : IsBottomTri W i j X) (t : T) (τ : D.what₂.Tau) :
    IsFockVacAt (heisO W.ψ A' WW) W.θ τ (cplxO (X.rA'.s τ) (X.rW.s τ)) (X.f' t) := by
  have hI := hX.is
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hI.isVac'.1.1.1 hI.isVac'.2.inf ho.conj.infPart_eq ho.conj.conj.infPart_eq
    (hI.snd t) hI.isVac'.2.theta (theta_snd hX t) (hI.isVac'.2.fock τ)

theorem rat_left (hX : IsBottomTri W i j X) (t : T) (P) {γ : GA D WW} (hγ : γ ∈ GQ WW) (x : GA D WW) :
    X.I' W.ψ W.θ t P (γ * x) = X.I' W.ψ W.θ t P x := by
  obtain ⟨χ, χ', hw⟩ := weil_snd hX t
  have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO hX.is.isVac'.1 hX.is.isVac'.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
    (theta_snd hX t) P
  unfold Tri.I'
  congr 1
  funext g
  unfold Tri.ker' thetaKO
  have e2 : ((g, γ * x) : GA D A' × GA D WW) = (1, γ) * (g, x) := by simp
  rw [e2, map_mul, Module.End.mul_apply]
  exact hw.om_aut 1 (one_mem _) γ hγ _ (hw.om_pres _ _ hF)

theorem level_right [Finite T] (hX : IsBottomTri W i j X) :
    ∃ J : Subgroup (GA D WW), IsOpen (J : Set (GA D WW)) ∧
      ∀ t, ∀ κ ∈ J, κ ∈ GfC WW → ∀ P x, X.I' W.ψ W.θ t P (x * κ) = X.I' W.ψ W.θ t P x := by
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac'.2.inf
  have hf : ∀ t, IsThetaFunO W.ψ A' WW (X.f' t) := fun t => (theta_snd hX t)
  choose χ χ' hW using weil_snd hX
  have hev : ∀ᶠ k in 𝓝 (1 : GA D WW), k ∈ GfC WW → ∀ t, X.ω' t (1, k) (X.f' t) = X.f' t := by
    have := Filter.eventually_all.2 fun t => eventually_fix (hW t) (fun τ => (hI.rigA'.2.2 τ).1)
      (fun τ => (hI.rigW.2.2 τ).1) hI.rigA'.1 hI.rigW.1 hI.isVac' (hf t) (fock_snd hX t)
    filter_upwards [this] with k hk hkf t using hk t hkf
  obtain ⟨N, hN, h⟩ := exists_cong_of_eventually hev
  refine ⟨GlobalTheory.VacFixTarget.congGroup WW N, GlobalTheory.VacFixTarget.isOpen_congGroup WW hN, fun t κ hκ hκf P x => ?_⟩
  have hpt := GlobalTheory.OrientedHeis.om_fin_pureTensorO _ _ _ _ _ _ (hW t) W.θ hθ 1 (one_mem _) κ hκf
    X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) P (hf t)
  unfold Tri.I' Tri.ker' thetaKO
  congr 1
  funext g
  have hm : ((g, x * κ) : GA D A' × GA D WW) = (g, x) * (1, κ) := by simp
  rw [hm, map_mul, Module.End.mul_apply, hpt, h κ hκf hκ t]

open Classical in

theorem scalar_exists (hX : IsBottomTri W i j X) (t : T) (τ₀ : D.what₂.Tau) :
    ∃ C w : ℂ, (w = Complex.exp Complex.I ∨ w = (Complex.exp Complex.I)⁻¹) ∧
      ∀ (k : FVar D WW.rank A'.rank →₀ ℕ) (h : GA D WW),
        X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h =
          (C * w ^ (∑ v ∈ k.support with v.1 = τ₀, k v)) * X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h := by
  classical
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac'.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac'.1
  obtain ⟨χ, χ', hom⟩ := weil_snd hX t
  have hsA : ∀ τ, X.rA'.s τ = 1 := fun τ => (hX.std'.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have he : ‖Complex.exp Complex.I‖ = 1 := by simpa using Complex.norm_exp_ofReal_mul_I 1
  obtain ⟨z', hz', -, h1, h2⟩ := GlobalTheory.CentralUnit.exists_central_of_norm_one D W.θ hθ A' τ₀ (Complex.exp Complex.I) he
  set ζ : D.what₂.Tau → ℂ := fun τ => if τ = τ₀ then Complex.exp Complex.I else 1 with hζdef
  have hζ : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt A' z') = ζ τ • (1 : Matrix (Fin A'.rank) (Fin A'.rank) ℂ) := by
    intro τ
    by_cases hτ : τ = τ₀
    · subst hτ
      simp only [hζdef, if_pos rfl, h1]
    · simp only [hζdef, if_neg hτ, h2 τ hτ, one_smul]
  have hζn : ∀ τ, ‖ζ τ‖ = 1 := fun τ => by
    by_cases hτ : τ = τ₀
    · simp only [hζdef, if_pos hτ, he]
    · simp only [hζdef, if_neg hτ, norm_one]
  have hf : IsThetaFunO W.ψ A' WW (X.f' t) := (theta_snd hX t)
  have hfock := fock_snd hX t
  have cS : ∀ τ, IsCartanInv (gramAt D A' τ) (X.rA'.s τ) := fun τ => (hI.rigA'.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hI.rigW.2.2 τ).1
  have one : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt WW 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one WW _
  obtain ⟨C, hC⟩ : ∃ C : ℂ, X.ω' t (z', 1) (X.f' t) = C • X.f' t := by
    obtain ⟨x₁, x₂, y₁, y₂, H⟩ := GlobalTheory.VacuumChar.vacuum_char D W.ψ W.θ (fixSig A') (fixSig WW) χ χ' (X.ω' t)
      (isWeilDatumO_fixSig hom) hθ (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _) X.rA'.s X.rW.s cS cT
    exact ⟨_, H _ (GlobalTheory.VacFixTarget.isThetaFunO_fixSig hf) hfock z' hz' 1 (one_mem _)
      (fun τ => (show X.rA'.s τ * compAt W.θ τ (Formalism.L2.Theta.mt A' z') = compAt W.θ τ (Formalism.L2.Theta.mt A' z') * X.rA'.s τ by
        rw [hsA, Matrix.mul_one, Matrix.one_mul]))
      (fun τ => (show X.rW.s τ * compAt W.θ τ (Formalism.L2.Theta.mt WW 1) = compAt W.θ τ (Formalism.L2.Theta.mt WW 1) * X.rW.s τ by
        rw [hsW, Matrix.mul_one, Matrix.one_mul]))⟩
  have hop : ∀ k : FVar D WW.rank A'.rank →₀ ℕ, _ := fun k =>
    GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ A' WW _ _ (X.ω' t) hom hθ X.rA'.s X.rA'.s
      X.rA'.B (fun τ => ζ τ • X.rA'.B τ) X.rW.s X.rW.s X.rW.B X.rW.B z' 1
      (fun τ => by rw [hζ τ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [one, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [hζ τ, Matrix.smul_mul, Matrix.one_mul])
      (fun τ => by rw [one, Matrix.one_mul]) (X.f' t) hf (MvPolynomial.monomial k 1)
  set w : ℂ := if (X.rA'.s τ₀ = 1 ↔ X.rW.s τ₀ = 1) then (Complex.exp Complex.I)⁻¹ else Complex.exp Complex.I with hw
  have hscal : ∀ k : FVar D WW.rank A'.rank →₀ ℕ,
      X.ω' t (z', 1) (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) (MvPolynomial.monomial k 1)) =
        (C * w ^ (∑ v ∈ k.support with v.1 = τ₀, k v)) •
          pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) (MvPolynomial.monomial k 1) := by
    intro k
    rw [(hop k).2, hC, GlobalTheory.FiniteFock.pureTensorO_smul,
      GlobalTheory.BottomDeg.pureTensorO_scal_pm (S := A') (T := WW) hψ hθ X.rA'.s X.rW.s X.rA'.B X.rW.B (fun τ => Or.inl (hsA τ))
        (fun τ => Or.inl (hsW τ)) (X.f' t) hf ζ hζn k, smul_smul]
    congr 2
    rw [Finset.prod_eq_single τ₀]
    · simp only [hζdef, if_pos rfl, hw]
    · intro ρ _ hρ
      simp only [hζdef, if_neg hρ, inv_one, ite_self, one_pow]
    · simp
  refine ⟨C, w, by rw [hw]; split_ifs; exacts [Or.inr rfl, Or.inl rfl], fun k h => ?_⟩
  set φ := pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) (MvPolynomial.monomial k 1) with hφ
  have hK := GlobalTheory.thetaKO_rat_left_and_eigen_right W.ψ A' WW _ _ (X.ω' t) hom φ (hop k).1
  have hleft : ∀ γ ∈ GQ A', ∀ g, X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) h (γ * g) =
      X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) h g := by
    intro γ hγ g
    have := hK.1 _ hγ 1 (one_mem _) g h
    rwa [one_mul] at this
  have hright : ∀ g, X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) h (g * z') =
      (C * w ^ (∑ v ∈ k.support with v.1 = τ₀, k v)) * X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) h g := by
    intro g
    have := hK.2 z' 1 _ (hscal k) g h
    rwa [mul_one] at this
  show ∫ g in X.fd', X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) h g ∂X.m' =
    _ * ∫ g in X.fd', X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) h g ∂X.m'
  calc _ = ∫ g in X.fd', X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) h (g * z') ∂X.m' :=
        (GlobalTheory.ChainOnto.setIntegral_fd_mul_right D A' X.m' X.fd' hI.meas'.1 hI.meas'.2 _ hleft z').symm
    _ = _ := by
        simp_rw [hright]
        exact integral_const_mul _ _

theorem vanish_off_finite [Finite T] (hX : IsBottomTri W i j X) :
    ∃ K : Finset (FVar D WW.rank A'.rank →₀ ℕ), ∀ t h, ∀ k ∉ K, X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h = 0 := by
  classical
  let Good : T → Set (FVar D WW.rank A'.rank →₀ ℕ) := fun t =>
    {k | ∃ h, X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h ≠ 0}
  have one_of : ∀ {c I : ℂ}, I = c * I → I ≠ 0 → c = 1 := fun {c I} e hI => by
    have h0 : (c - 1) * I = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hI)
  have hfin : ∀ t, (Good t).Finite := by
    intro t
    by_cases hne : (Good t).Nonempty
    · obtain ⟨k₀, h₀, hk₀⟩ := hne
      refine (GlobalTheory.finite_monomials_of_placeDegree D WW.rank A'.rank
        (fun τ => ∑ v ∈ k₀.support with v.1 = τ, k₀ v)).subset fun k hk τ => ?_
      obtain ⟨h, hk⟩ := hk
      obtain ⟨C, w, hw, hI⟩ := scalar_exists hX t τ
      have e1 := one_of (hI k h) hk
      have e0 := one_of (hI k₀ h₀) hk₀
      have hC : C ≠ 0 := fun h0 => by rw [h0, zero_mul] at e1; exact zero_ne_one e1
      exact GlobalTheory.ExpPow.pow_exp_I_or_inv_injective _ _ w hw (mul_left_cancel₀ hC (e1.trans e0.symm))
    · rw [Set.not_nonempty_iff_eq_empty.1 hne]
      exact Set.finite_empty
  have hU : (⋃ t, Good t).Finite := Set.finite_iUnion hfin
  refine ⟨hU.toFinset, fun t h k hk => ?_⟩
  by_contra hne
  exact hk (hU.mem_toFinset.2 (Set.mem_iUnion.2 ⟨t, h, hne⟩))

end Bottom

section Real

theorem coeff_substF_mem {ι : Type} {N n : ℕ} (M : IntermediateField ℚ ℂ) (h : ι → Matrix (Fin N) (Fin N) ℂ)
    (g : ι → Matrix (Fin n) (Fin n) ℂ) (hh : ∀ τ a b, h τ a b ∈ M) (hg : ∀ τ a b, g τ a b ∈ M)
    (k k' : ι × Fin N × Fin n →₀ ℕ) :
    (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1)).coeff k' ∈ M := by
  have hmem : GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1) ∈
      (MvPolynomial.map (σ := ι × Fin N × Fin n) (algebraMap M ℂ)).range := by
    unfold GlobalTheory.CompactHowe.substF
    rw [MvPolynomial.aeval_monomial, map_one, one_mul]
    refine prod_mem fun p _ => pow_mem (sum_mem fun a _ => sum_mem fun b _ => mul_mem ?_ ?_) _
    · exact ⟨MvPolynomial.C ⟨_, mul_mem (hh p.1 a p.2.1) (hg p.1 b p.2.2)⟩, MvPolynomial.map_C _ _⟩
    · exact ⟨MvPolynomial.X _, MvPolynomial.map_X _ _⟩
  obtain ⟨Q, hQ⟩ := hmem
  rw [← hQ, MvPolynomial.coeff_map]
  exact (Q.coeff k').2

theorem det_mem {N : ℕ} (M : IntermediateField ℚ ℂ) (h : Matrix (Fin N) (Fin N) ℂ) (hh : ∀ a b, h a b ∈ M) : h.det ∈ M := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun a _ => hh _ _)

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
  {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}

variable (D) in

def conjField : IntermediateField ℚ ℂ := ⨆ τ : D.what₂.Tau, (tauE D τ).toRatAlgHom.fieldRange

theorem finiteDimensional_conjField : FiniteDimensional ℚ (conjField D) := by
  haveI : ∀ τ : D.what₂.Tau, FiniteDimensional ℚ (tauE D τ).toRatAlgHom.fieldRange := fun τ =>
    (tauE D τ).toRatAlgHom.equivFieldRange.toLinearEquiv.finiteDimensional
  exact IntermediateField.finiteDimensional_iSup_of_finite

theorem compAt_mem {θ : InfFam D} (hθ : IsInfFam θ) {γ r : GA D WW} (hγ : γ ∈ GQ WW) (hr : γ * r ∈ GfC WW) (τ a b) :
    compAt θ τ (Formalism.L2.Theta.mt WW r) a b ∈ conjField D := by
  obtain ⟨m, hm⟩ : ∃ m : Matrix (Fin WW.rank) (Fin WW.rank) D.host.E, Formalism.L2.Theta.mt WW γ⁻¹ = m.map (incA D) := by
    obtain ⟨γ0, -, e0⟩ := inv_mem hγ
    exact ⟨γ0.1, (congrArg Units.val e0).symm⟩
  have e : r = γ⁻¹ * (γ * r) := by group
  have h1 : compAt θ τ (m.map (incA D)) a b = tauE D τ (m a b) := (hθ τ).1 _
  rw [e, GlobalTheory.VacuumChar.compAt_mt_mul, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ WW hr τ, Matrix.mul_one, hm, h1]
  exact (le_iSup (fun τ : D.what₂.Tau => (tauE D τ).toRatAlgHom.fieldRange) τ) ⟨m a b, rfl⟩

theorem integrable_snd (hX : IsBottomTri W i j X) (t : T) (P) (x : GA D WW) :
    IntegrableOn (X.ker' W.ψ W.θ t P x) X.fd' X.m' := by
  obtain ⟨χ, χ', hom⟩ := weil_snd hX t
  have hF := GlobalTheory.Chain.InnerSteps.theta_pureTensorO hX.is.isVac'.1 hX.is.isVac'.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
    (theta_snd hX t) P
  have := GlobalTheory.WeilParts.integrableOn_theta_definite D W.ψ hom.std A' WW χ χ' (X.ω' t) hom
    (GlobalTheory.ConstRatio.posDef_of_std hX.std') ℂ (LinearMap.toSpanSingleton ℂ _ _)
    (fun c => GlobalTheory.OrientedHeis.theta_smul c hF) (fun _ => 1) continuous_const (fun _ _ _ => rfl) X.m' X.fd'
    hX.is.meas'.1 hX.is.meas'.2 x
  simp only [LinearMap.toSpanSingleton_apply, one_smul] at this
  exact this

theorem real_right (hX : IsBottomTri W i j X) (t : T) {γ r : GA D WW} (hγ : γ ∈ GQ WW) (hrI : r ∈ GinfC WW)
    (hr : γ * r ∈ GfC WW) (x : GA D WW) (k : FVar D WW.rank A'.rank →₀ ℕ) :
    ∃ c : MvPolynomial (FVar D WW.rank A'.rank) ℂ, (∀ k', c.coeff k' ∈ conjField D) ∧
      X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) (x * r) =
        ∑ k' ∈ c.support, c.coeff k' * X.I' W.ψ W.θ t (MvPolynomial.monomial k' 1) x := by
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac'.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac'.1
  obtain ⟨χ, χ', hom⟩ := weil_snd hX t
  have hsA : X.rA'.s = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).1
  have hsW : X.rW.s = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).1
  have hBA : X.rA'.B = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).2
  have hBW : X.rW.B = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).2
  have hf : IsThetaFunO W.ψ A' WW (X.f' t) := (theta_snd hX t)
  have hfock := fock_snd hX t
  have cS : ∀ τ, IsCartanInv (gramAt D A' τ) (X.rA'.s τ) := fun τ => (hI.rigA'.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hI.rigW.2.2 τ).1
  have one : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt A' 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one A' _
  have hmem := compAt_mem hθ hγ hr
  have h1mem : ∀ (n : ℕ) (a b : Fin n), (1 : Matrix (Fin n) (Fin n) ℂ) a b ∈ conjField D := fun n a b => by
    rw [Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  obtain ⟨C, hCm, hC⟩ : ∃ C ∈ conjField D, X.ω' t (1, r) (X.f' t) = C • X.f' t := by
    obtain ⟨x₁, x₂, y₁, y₂, H⟩ := GlobalTheory.VacuumChar.vacuum_char D W.ψ W.θ (fixSig A') (fixSig WW) χ χ' (X.ω' t)
      (isWeilDatumO_fixSig hom) hθ (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _) X.rA'.s X.rW.s cS cT
    refine ⟨_, ?_, H _ (GlobalTheory.VacFixTarget.isThetaFunO_fixSig hf) hfock 1 (one_mem _) r hrI
      (fun τ => (show X.rA'.s τ * compAt W.θ τ (Formalism.L2.Theta.mt A' 1) = compAt W.θ τ (Formalism.L2.Theta.mt A' 1) * X.rA'.s τ by
        rw [hsA, Matrix.mul_one, Matrix.one_mul]))
      (fun τ => (show X.rW.s τ * compAt W.θ τ (Formalism.L2.Theta.mt WW r) = compAt W.θ τ (Formalism.L2.Theta.mt WW r) * X.rW.s τ by
        rw [hsW, Matrix.mul_one, Matrix.one_mul]))⟩
    have key : ∀ {n : ℕ} (s m : Matrix (Fin n) (Fin n) ℂ) (y z : ℤ), s = 1 → (∀ a b, m a b ∈ conjField D) →
        ((1 / 2 : ℂ) • (1 + s) * m + (1 / 2 : ℂ) • (1 - s)).det ^ y ∈ conjField D ∧
        ((1 / 2 : ℂ) • (1 - s) * m + (1 / 2 : ℂ) • (1 + s)).det ^ z ∈ conjField D := by
      rintro n _ m y z rfl hm
      have e : (1 / 2 : ℂ) • ((1 : Matrix (Fin n) (Fin n) ℂ) + 1) = 1 := by
        rw [← two_smul ℂ, smul_smul]; norm_num
      rw [e, sub_self, smul_zero, Matrix.one_mul, add_zero, Matrix.zero_mul, zero_add, Matrix.det_one, one_zpow]
      exact ⟨zpow_mem (det_mem _ _ hm) _, one_mem _⟩
    refine prod_mem fun τ _ => ?_
    have k1 := key (X.rW.s τ) (compAt W.θ τ (Formalism.L2.Theta.mt WW r)) (x₁ τ) (x₂ τ) (congrFun hsW τ) (hmem τ)
    have k2 := key (X.rA'.s τ) (compAt W.θ τ (Formalism.L2.Theta.mt A' 1)) (y₁ τ) (y₂ τ) (congrFun hsA τ)
      (by rw [one]; exact h1mem _)
    exact mul_mem (mul_mem (mul_mem k1.1 k1.2) k2.1) k2.2
  set Q : MvPolynomial (FVar D WW.rank A'.rank) ℂ := GlobalTheory.CompactHowe.substF (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt WW r))
    (fun _ => ((1 : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)⁻¹).transpose) (MvPolynomial.monomial k 1) with hQ
  have hQm : ∀ k', Q.coeff k' ∈ conjField D := fun k' =>
    coeff_substF_mem _ _ _ hmem (fun _ => by rw [inv_one, Matrix.transpose_one]; exact h1mem _) k k'
  have hmain : X.ω' t (1, r) (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) (MvPolynomial.monomial k 1)) =
      pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) (C • Q) := by
    rw [hsA, hsW, hBA, hBW, map_smul]
    rw [(GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ A' WW _ _ (X.ω' t) hom hθ (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (fun _ => 1 * 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun τ => 1 * compAt W.θ τ (Formalism.L2.Theta.mt WW r)) 1 r
      (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
      (fun τ => by rw [one]) (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) _ hf _).2, hC,
      GlobalTheory.FiniteFock.pureTensorO_smul, GlobalTheory.FockBaseChange.pureTensorO_subst D W.ψ W.θ A' WW hψ hθ (fun _ => 1) (fun _ => 1)
        (fun _ => 1) _ _ hf]
  refine ⟨C • Q, fun k' => by rw [MvPolynomial.coeff_smul]; exact mul_mem hCm (hQm k'), ?_⟩
  have hker : ∀ g, X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) (x * r) g =
      ∑ k' ∈ (C • Q).support, (C • Q).coeff k' * X.ker' W.ψ W.θ t (MvPolynomial.monomial k' 1) x g := by
    intro g
    unfold Tri.ker' thetaKO
    have hm : ((g, x * r) : GA D A' × GA D WW) = (g, x) * (1, r) := by simp
    rw [hm, map_mul, Module.End.mul_apply, hmain]
    conv_lhs => rw [(C • Q).as_sum, map_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [show MvPolynomial.monomial k' ((C • Q).coeff k') = (C • Q).coeff k' • MvPolynomial.monomial k' (1 : ℂ) by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul, map_smul, Pi.smul_apply, smul_eq_mul]
  unfold Tri.I'
  simp_rw [hker]
  rw [integral_finset_sum _ fun k' _ => (integrable_snd hX t _ x).const_mul _]
  exact Finset.sum_congr rfl fun k' _ => integral_const_mul _ _

end Real

theorem span_classSums' : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (H : Finset (GA D WW)) (K : Finset (FVar D WW.rank A'.rank →₀ ℕ)) (M₀ : IntermediateField ℚ ℂ), FiniteDimensional ℚ M₀ ∧
      (∀ h ∈ H, h ∈ GfC WW) ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, ∃ c : GA D WW → (FVar D WW.rank A'.rank →₀ ℕ) → ℂ, (∀ a b, c a b ∈ M₀) ∧
        X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h =
          ∑ h' ∈ H, ∑ k' ∈ K, c h' k' * X.I' W.ψ W.θ t (MvPolynomial.monomial k' 1) h' := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  classical
  obtain ⟨K, hK⟩ := vanish_off_finite hX
  obtain ⟨J, hJ, hl⟩ := level_right hX
  obtain ⟨H, hH, hc⟩ := GlobalTheory.BotClassFin.exists_reps hP hI hL hX J hJ
  refine ⟨H, K, conjField D, finiteDimensional_conjField, hH, ?_⟩
  intro t h hh k
  obtain ⟨γ, hγ, r, hrI, h₀, hh₀, κ, hκJ, hκf, rfl⟩ := hc h hh
  have hx : h₀ * κ ∈ GfC WW := mul_mem (hH h₀ hh₀) hκf
  have hγr : γ * r ∈ GfC WW := by
    have e : γ * r = (γ * r * h₀ * κ) * (h₀ * κ)⁻¹ := by group
    rw [e]; exact mul_mem hh (inv_mem hx)
  obtain ⟨c, hcM, hcE⟩ := real_right hX t hγ hrI hγr (h₀ * κ) k
  have e1 : X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) (γ * r * h₀ * κ) =
      ∑ k' ∈ c.support, c.coeff k' * X.I' W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀ := by
    have e0 : γ * r * h₀ * κ = γ * ((h₀ * κ) * r) := by
      rw [← GlobalTheory.AdelicSplit.commute_GinfC_GfC WW hrI hx]; simp only [mul_assoc]
    rw [e0, rat_left hX t _ hγ, hcE]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [hl t κ hκJ hκf]
  refine ⟨fun h' k' => if h' = h₀ then c.coeff k' else 0, fun a b => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hcM b
    · exact zero_mem _
  rw [e1, Finset.sum_eq_single_of_mem h₀ hh₀ (fun b _ hb => by simp [hb])]
  simp only [if_true]
  calc ∑ k' ∈ c.support, c.coeff k' * X.I' W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀
      = ∑ k' ∈ c.support ∪ K, c.coeff k' * X.I' W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀ :=
        Finset.sum_subset Finset.subset_union_left fun k' _ hk' => by
          rw [MvPolynomial.notMem_support_iff.1 hk', zero_mul]
    _ = ∑ k' ∈ K, c.coeff k' * X.I' W.ψ W.θ t (MvPolynomial.monomial k' 1) h₀ :=
        (Finset.sum_subset Finset.subset_union_right fun k' _ hk' => by
          rw [hK t h₀ k' hk', mul_zero]).symm

end GlobalTheory.BotSpanSnd

end
