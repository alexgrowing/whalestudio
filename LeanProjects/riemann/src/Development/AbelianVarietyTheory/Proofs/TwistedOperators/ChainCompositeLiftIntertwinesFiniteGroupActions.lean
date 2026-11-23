import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftLowestKTypeCompatibility
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActionPreservesPrincipalFlagMultiplic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftTranslateOfKernelFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicitySpaceEqZeroOfApplyNonzeroTensorZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersRamificationLevelPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnGaLMemGoodPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExistStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastStepVectorLiftPairFlagLevelCharactersStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainLiftEquiv

section Generic

variable {D : D7} {V W : HSp D} {S : D.what₂.Tau → SPar}

theorem multT_left (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (u : SmT M →ₗ[ℂ] (GA D V → ℂ)) (hu : u ∈ MultT θ M J χ) (v : SmT M) (γ : GA D V) (hγ : γ ∈ GQ V) (g : GA D V) :
    u v (γ * g) = u v g := by
  have h1 := (mem_multT θ M J χ u).1 hu
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have h2 := (GlobalTheory.mult_value_left_cont_level θ M J χ _ h1 f).1 γ hγ g
    have h3 : u (PiTensorProduct.tprod ℂ f) (γ * g) = u (PiTensorProduct.tprod ℂ f) g := h2
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, h3]
  | add x y hx hy => rw [map_add, Pi.add_apply, Pi.add_apply, hx, hy]

theorem exists_translate (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (g0 : G0 L.Pg L.r) (κ : GA D V) (hκ : IsLevelLift V β L g0 κ)
    (u : MultT θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L))) :
    ∃ u' : MultT θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)), ∀ v g,
      (u' : SmT M →ₗ[ℂ] (GA D V → ℂ)) v g = (levChi V β (flagL L) κ)⁻¹ * (u : SmT M →ₗ[ℂ] (GA D V → ℂ)) v (g * κ) := by
  have h1 := (mem_multT θ M _ _ u.1).1 u.2
  refine ⟨⟨((levChi V β (flagL L) κ)⁻¹ • LinearMap.funLeft ℂ ℂ (fun g : GA D V => g * κ)) ∘ₗ u.1, ?_⟩, fun v g => rfl⟩
  rw [mem_multT]
  refine GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity θ M hθ β L g0 _ h1 _ fun v => funext fun g => ?_
  have hT : HasType V β (flag1L L) (PiTensorProduct.lift.symm u.1 v) := fun k hk h =>
    (GlobalTheory.mult_value_left_cont_level θ M _ _ _ h1 v).2.2 k hk h
  exact (level_action_spec hT ⟨κ, hκ⟩ κ hκ g).symm

theorem step (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (hom : IsWeilDatumO ψ V W χS χT om)
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) {Ds : Type} [AddCommGroup Ds] [Module ℂ Ds]
    (pt : PolF D W.rank V.rank → (WO V W → ℂ)) (hpt : ∀ P, IsThetaFunO ψ V W (pt P))
    (It : PolF D W.rank V.rank →ₗ[ℂ] Ds →ₗ[ℂ] SmT M) (hIt : It ≠ 0)
    (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    (hS : SchurMult θ M J χ μ 𝓕) (ν : Measure (GA D W)) (𝓖 : Set (GA D W))
    (CCs : Submodule ℂ (Ds →ₗ[ℂ] (GA D W → ℂ)))
    (hleft : ∀ (F : CCs) v, ∀ γ ∈ GQ W, ∀ h, (F : Ds →ₗ[ℂ] (GA D W → ℂ)) v (γ * h) = (F : Ds →ₗ[ℂ] (GA D W → ℂ)) v h)
    (io : CCs →ₗ[ℂ] MultT θ M J χ) (hio : Lift.IsIo ν 𝓖 (thetaKO om) pt It CCs (MultT θ M J χ) io)
    (k : GA D V) (k' : GA D W) (a a' : ℂ) (ha : a ≠ 0) (hk : ∀ P, om (k, k') (pt P) = (a⁻¹ * a') • pt P)
    (hsh : ∀ f : GA D W → ℂ, (∀ γ ∈ GQ W, ∀ h, f (γ * h) = f h) → IntegrableOn f 𝓖 ν →
      ∫ h in 𝓖, f (h * k') ∂ν = ∫ h in 𝓖, f h ∂ν)
    (htr : ∀ u : MultT θ M J χ, ∃ u' : MultT θ M J χ, ∀ v g,
      (u' : SmT M →ₗ[ℂ] (GA D V → ℂ)) v g = a * (u : SmT M →ₗ[ℂ] (GA D V → ℂ)) v (g * k))
    (F F' : CCs) (hF : ∀ v h, (F' : Ds →ₗ[ℂ] (GA D W → ℂ)) v h = a' * (F : Ds →ₗ[ℂ] (GA D W → ℂ)) v (h * k')) (v : SmT M)
    (g : GA D V) :
    (io F' : SmT M →ₗ[ℂ] (GA D V → ℂ)) v g = a * (io F : SmT M →ₗ[ℂ] (GA D V → ℂ)) v (g * k) := by
  obtain ⟨u, hu⟩ := htr (io F)
  have hker := fun P => GlobalTheory.thetaKO_rat_left_and_eigen_right ψ V W χS χT om hom (pt P) (hpt P)
  have hx : ∃ φ w, It φ w ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hIt (LinearMap.ext fun φ => LinearMap.ext fun w => hn φ w)
  obtain ⟨φ0, w0, hx⟩ := hx
  have e := GlobalTheory.thetaLift_translate_of_kernel_fixed ν 𝓖 (thetaKO om) pt It CCs (MultT θ M J χ) io hio
    (fun u hu => Subtype.ext (GlobalTheory.multT_eq_zero_of_apply_eq_zero θ M J χ μ 𝓕 hθ hμ h𝓕 hS u.1 u.2 _ hx (hu φ0 w0)))
    k k' a a' (fun g h φ => by rw [(hker φ).2 k k' _ (hk φ) g h, ← mul_assoc, mul_inv_cancel_left₀ ha])
    (fun F φ v g => hsh (fun h => thetaKO om g h (pt φ) * (F : Ds →ₗ[ℂ] (GA D W → ℂ)) v h) (fun γ hγ h => by
      have h1 := (hker φ).1 1 (GQ V).one_mem γ hγ g h
      rw [one_mul] at h1
      simp only [h1, hleft F v γ hγ h]) (hio.integ F φ v g)) F F' u hF hu
  rw [e]
  exact hu v g

theorem dnFrom_rel {Gp : ℕ → Type} {Dm : ℕ → Type} [∀ j, AddCommGroup (Dm j)] [∀ j, Module ℂ (Dm j)]
    (CC : ∀ j, Submodule ℂ (Dm j →ₗ[ℂ] (Gp j → ℂ))) (io : ∀ k, CC (k + 1) →ₗ[ℂ] CC k) (r : ∀ j, CC j → CC j → Prop) (n : ℕ)
    (h : ∀ k, k < n → ∀ x y, r (k + 1) x y → r k (io k x) (io k y)) (x y : CC n) (hxy : r n x y) :
    r 0 (Lift.dnFrom CC io n x) (Lift.dnFrom CC io n y) := by
  induction n with
  | zero => exact hxy
  | succ n ih => exact ih (fun k hk => h k (Nat.lt_succ_of_lt hk)) _ _ (h n (Nat.lt_succ_self n) x y hxy)

theorem smul_eq_of {X : Type} [AddCommGroup X] [Module ℂ X] {a a' : ℂ} (ha : a ≠ 0) {x y : X} (h : a • x = a' • y) :
    x = (a⁻¹ * a') • y := by
  rw [mul_smul, ← h, inv_smul_smul₀ ha]

end Generic

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem liftsExist_chain (h : R.toLevCh.Is A.μ0) (t : T0) (j : ℕ) (hj : j < D.R.m) :
    LiftsExist (Yc D j) (R.βY j) (R.datYt t j R.triv) := by
  obtain ⟨c, hc⟩ := h.βY j hj
  refine GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hc (fun PP hP PP' hP' => ?_)
    (GlobalTheory.LevelRamif.ramif_at_levels D T0 R.toLevCh A.μ0 h t ⟨j, hj⟩).1
  obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
  rcases hP' with hP' | hP'
  · obtain ⟨k', hk'⟩ := (h.Pg PP').1 hP'
    exact GlobalTheory.ProjectedLift.not_isConjPl R.C.P hk hk'
  · intro hc
    obtain ⟨q, hq, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem (h.Q_pl t) hP'
    exact GlobalTheory.LevelRamif.not_two_primes PP' hq (D.host.g_prime k) (hne k) hm
      (GlobalTheory.LevelRamif.natCast_mem_conj hc (GlobalTheory.LevelRamif.typePrime_mem hk))

theorem meas_chain (h1 : R.models_νY) (h2 : R.models_νY') (t : T0) (j : ℕ) (hj : j < D.R.m) :
    (R.νY t j).IsHaarMeasure ∧ IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
  by_cases h : j + 1 < D.R.m
  · exact ⟨(h1 t j h).1.1, (h1 t j h).2⟩
  · obtain rfl : j = D.R.m - 1 := by omega
    exact ⟨(h2 t).1.1, (h2 t).2⟩

def IsShift (t : T0) (j : ℕ) (κ : GA D (Yc D j)) (u u' : R.CC t j) : Prop :=
  ∀ v g, (u' : SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) v g =
    (levChi (Yc D j) (R.βY j) (flagL (R.datYt t j R.triv)) κ)⁻¹ * (u : SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) v (g * κ)

theorem exists_shift (hθ : R.models_inf) (t : T0) (j : ℕ) (g0 : G0 R.Pg D.R.r) (κ : GA D (Yc D j))
    (hκ : IsLevelLift (Yc D j) (R.βY j) (R.datYt t j R.triv) g0 κ) (u : R.CC t j) : ∃ u', IsShift R t j κ u u' :=
  exists_translate R.θ hθ (R.MY j) (R.βY j) (R.datYt t j R.triv) g0 κ hκ u

theorem stepY (h : R.toLevCh.Is A.μ0) (hM : R.IsModels) (hC : R.IsChain) (t : T0) (k : ℕ) (hk : k + 1 < D.R.m)
    (hS : SchurMult R.θ (R.MY k) (levS _ (R.βY k) (R.datYt t k R.triv)) (levChi _ (R.βY k) (R.datYt t k R.triv))
      (R.νY t k) (R.fdY t k)) (g0 : G0 R.Pg D.R.r) (κ : GA D (Yc D k)) (κ' : GA D (Yc D (k + 1)))
    (hκ : IsLevelLift (Yc D k) (R.βY k) (R.datYt t k R.triv) g0 κ)
    (hκ' : IsLevelLift (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) g0 κ') (u u' : R.CC t (k + 1))
    (hu : IsShift R t (k + 1) κ' u u') : IsShift R t k κ (R.ioY t k u) (R.ioY t k u') := by
  have hm := meas_chain R hM.νY hM.νY' t k (Nat.lt_of_succ_lt hk)
  have hm' := meas_chain R hM.νY hM.νY' t (k + 1) hk
  have ha := inv_ne_zero (levChi_ne_zero (V := Yc D k) (β := R.βY k) (flagL (R.datYt t k R.triv)) κ)
  have hv := smul_eq_of ha (GlobalTheory.T.stepVector_lift_pair_flagLevel_realized_chain R h hM.inf hC.ωY hC.vY t k hk g0 κ κ' hκ hκ')
  have hpt := GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Yc D k) (Yc D (k + 1)) _ _ (R.ωY t k) hM.inf (hC.ωY t k hk)
    _ _ _ _ _ (hC.ptY t k hk) κ hκ.1 κ' hκ'.1 _ hv
  exact step R.ψ R.θ hM.inf _ _ (R.ωY t k) (hC.ωY t k hk) (R.MY k) _ _ (R.ptY t k) (hC.ptY t k hk) (R.ItY k) (hC.ItY t k hk).ne
    (R.νY t k) (R.fdY t k) hm.1 hm.2 hS (R.νY t (k + 1)) (R.fdY t (k + 1)) (R.CC t (k + 1))
    (fun F => multT_left R.θ (R.MY (k + 1)) _ _ F.1 F.2) (R.ioY t k) (hC.ioY t k (Nat.lt_sub_of_add_lt hk)) κ κ' _ _ ha hpt
    (GlobalTheory.ThetaProjEquiv.integral_shift _ (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) g0 κ' hκ' _ hm'.1 _ hm'.2)
    (exists_shift R hM.inf t k g0 κ hκ) u u' hu

theorem toMap_left (hX : R.models_HX) (t : T0) (F : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) (v : SmT R.MX)
    (γ : GA D D.sp.X') (hγ : γ ∈ GQ D.sp.X') (h : GA D D.sp.X') :
    (F : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) v (γ * h) = (F : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) v h := by
  obtain ⟨_, y, rfl⟩ := F
  exact congrArg (fun w => R.prX w v)
    (GlobalTheory.ThetaProjEquiv.ext_left R.cX ((R.HX t).e y) _ _ ((hX t).2.1.le ⟨y, rfl⟩) γ hγ h)

theorem toMap_shift {V : HSp D} (c : CoefA V) (hc : c.Is) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm]
    (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) (κ : GA D V) (hκ : κ ∈ GfC V) (a : ℂ) (ha : a ≠ 0)
    (f f' : Bridge.Gf V → c.W) (hy : ∀ h, f' h = a⁻¹ • f (h * (finHom V).rangeRestrict κ)) (v : Dm) (h : GA D V) :
    c.toMap pr f' v h = a⁻¹ * c.toMap pr f v (h * κ) := by
  have h1 := GlobalTheory.ThetaProjEquiv.ext_shift c hc κ hκ a ha f f' hy h
  show pr (c.ext f' h) v = a⁻¹ * pr (c.ext f (h * κ)) v
  rw [← h1, map_smul, Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ ha]

theorem stepX (h : R.toLevCh.Is A.μ0) (hM : R.IsModels) (hC : R.IsChain) (t : T0)
    (hS : SchurMult R.θ (R.MY (D.R.m - 1)) (levS _ (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv))
      (levChi _ (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv)) (R.νY t (D.R.m - 1)) (R.fdY t (D.R.m - 1)))
    (g0 : G0 R.Pg D.R.r) (κ : GA D (Yc D (D.R.m - 1))) (κ' : GA D D.sp.X')
    (hκ : IsLevelLift (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) g0 κ)
    (hκ' : IsLevelLift D.sp.X' R.βX (R.datXt t) g0 κ') (y y' : (R.HX t).H)
    (hy : ∀ h, (R.HX t).e y' h =
      (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ')⁻¹ • (R.HX t).e y (h * (finHom D.sp.X').rangeRestrict κ')) :
    IsShift R t (D.R.m - 1) κ (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y))
      (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')) := by
  have ha := inv_ne_zero (levChi_ne_zero (V := Yc D (D.R.m - 1)) (β := R.βY (D.R.m - 1))
    (flagL (R.datYt t (D.R.m - 1) R.triv)) κ)
  have hv := smul_eq_of ha (GlobalTheory.T.lastVector_lift_pair_flagLevel_characters R h hM.inf hC.ωX hC.vX t g0 κ κ' hκ hκ')
  have hpt := GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' _ _ (R.ωX t) hM.inf (hC.ωX t)
    _ _ _ _ _ (hC.ptX t) κ hκ.1 κ' hκ'.1 _ hv
  exact step R.ψ R.θ hM.inf _ _ (R.ωX t) (hC.ωX t) (R.MY (D.R.m - 1)) _ _ (R.ptX t) (hC.ptX t) R.ItX (hC.ItX t).ne
    (R.νY t (D.R.m - 1)) (R.fdY t (D.R.m - 1)) (hM.νY' t).1.1 (hM.νY' t).2 hS (R.νX t) (R.fdX t) _
    (toMap_left R hM.HX t) (R.ioX t) (hC.ioX t) κ κ' _ _ ha hpt
    (GlobalTheory.ThetaProjEquiv.integral_shift _ R.βX (R.datXt t) g0 κ' hκ' _ (hM.νX t).1.1 _ (hM.νX t).2)
    (exists_shift R hM.inf t (D.R.m - 1) g0 κ hκ) _ _
    (toMap_shift R.cX hM.cX R.prX κ' hκ'.1 _ (levChi_ne_zero (V := D.sp.X') (β := R.βX) (flagL (R.datXt t)) κ') _ _ hy)

theorem lift_zero (t : T0) (g0 : G0 R.Pg D.R.r) (κ : GA D (Yc D 0))
    (hκ : IsLevelLift (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) g0 κ) :
    IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ ∧
      levChi (Yc D 0) (R.βY 0) (flagL (R.datYt t 0 R.triv)) κ = levChi (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) κ := by
  have hr : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _)]
    simp [Ranks.rankY]
  have e0 := GlobalTheory.levG_twist_trivial_of_rank_eq (Yc D 0) (R.βY 0) D.R.r D.R.t (r_le_Y 0) hr R.Pg (R.Q t) (LevelP.full _ _ _)
    R.chi (R.xiR t)
  have e1 : levG (Yc D 0) (R.βY 0) (flagL (R.datYt t 0 R.triv)) = levG (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) := e0.1
  have e2 : ∀ k ∈ levG (Yc D 0) (R.βY 0) (flagL (R.datYt t 0 R.triv)),
      levChi (Yc D 0) (R.βY 0) (flagL (R.datYt t 0 R.triv)) k = levChi (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) k := e0.2
  have h1 := (GlobalTheory.ParahoricCompact.isCompact_flag_and_lift (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv)).2 g0 κ hκ
  have h2 : κ ∈ levG (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) := e1 ▸ h1
  exact ⟨⟨hκ.1, h2.2.1, hκ.2.2⟩, e2 κ h1⟩

theorem thDn_shift (h : R.toLevCh.Is A.μ0) (hM : R.IsModels) (hC : R.IsChain) (t : T0)
    (hS : ∀ j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv))
      (levChi _ (R.βY j) (R.datYt t j R.triv)) (R.νY t j) (R.fdY t j))
    (g0 : G0 R.Pg D.R.r) (κ' : GA D D.sp.X') (hκ' : IsLevelLift D.sp.X' R.βX (R.datXt t) g0 κ') (y y' : (R.HX t).H)
    (hy : ∀ h, (R.HX t).e y' h =
      (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ')⁻¹ • (R.HX t).e y (h * (finHom D.sp.X').rangeRestrict κ'))
    (κ : GA D (Yc D 0)) (hκ : IsLevelLift (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) g0 κ) (v : SmT (R.MY 0)) (g : GA D (Yc D 0)) :
    R.thDn t y' v g = (levChi (Yc D 0) (R.βY 0) (flagL (R.datYt t 0 R.triv)) κ)⁻¹ * R.thDn t y v (g * κ) := by
  have hm : D.R.m - 1 < D.R.m := Nat.sub_lt (lt_of_lt_of_le two_pos D.R.two_le_m) one_pos
  exact dnFrom_rel (R.CC t) (R.ioY t)
    (fun j u u' => ∀ κ, IsLevelLift (Yc D j) (R.βY j) (R.datYt t j R.triv) g0 κ → IsShift R t j κ u u') (D.R.m - 1)
    (fun k hk u u' hu κ hκ => (liftsExist_chain R h t (k + 1) (Nat.add_lt_of_lt_sub hk) g0).elim fun κ₁ hκ₁ =>
      stepY R h hM hC t k (Nat.add_lt_of_lt_sub hk) (hS k (hk.trans hm)) g0 κ κ₁ hκ hκ₁ u u' (hu κ₁ hκ₁))
    _ _ (fun κ hκ => stepX R h hM hC t (hS _ hm) g0 κ κ' hκ hκ' y y' hy) κ hκ v g

theorem actL_zero (t : T0) (g0 : G0 R.Pg D.R.r) (κ : GA D (Yc D 0))
    (hκ : IsLevelLift (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) g0 κ) (f : GA D (Yc D 0) → ℂ)
    (hT : HasType (Yc D 0) (R.βY 0) (R.dat0 R.triv) f) (x : GA D (Yc D 0)) :
    actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 f x =
      (levChi (Yc D 0) (R.βY 0) (flagL (R.datYt t 0 R.triv)) κ)⁻¹ * f (x * κ) := by
  have h0 := lift_zero R t g0 κ hκ
  have h1 := level_action_spec (V := Yc D 0) (β := R.βY 0) (L := R.dat0 R.triv) hT ⟨κ, h0.1⟩ κ h0.1 x
  exact h1.trans (congrArg (fun c : ℂ => c⁻¹ * f (x * κ)) h0.2.symm)

theorem thDn_type (t : T0) (y : (R.HX t).H) (v : (R.MY 0).Vec) :
    HasType (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.thDn t y (PiTensorProduct.tprod ℂ v)) := fun k hk x =>
  (GlobalTheory.mult_value_left_cont_level R.θ (R.MY 0) _ _ _ (GlobalTheory.ProjectedLift.thDn_mem R t y) v).2.2 k hk x

theorem th_of_thDn (h : R.toLevCh.Is A.μ0) (hr : R.grp_record) (hE : R.models_HE) (hg : R.models_gE) (hT : R.chain_Th)
    (t : T0) (g : G) (y y' : (R.HX t).H) (hact : ∀ v : (R.MY 0).Vec, R.thDn t y' (PiTensorProduct.tprod ℂ v) =
      actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.thDn t y (PiTensorProduct.tprod ℂ v))) :
    R.Th t y' = R.gE g (R.Th t y) := by
  refine hE.1 (MultilinearMap.ext fun v => ?_)
  have e1 : R.HE.e (R.Th t y') v = R.e0 (R.thDn t y' (PiTensorProduct.tprod ℂ v)) :=
    congrArg (fun T : MMap (R.MY 0) => T v) (hT t y')
  have e2 : R.HE.e (R.Th t y) v = R.e0 (R.thDn t y (PiTensorProduct.tprod ℂ v)) :=
    congrArg (fun T : MMap (R.MY 0) => T v) (hT t y)
  have e3 : R.HE.e (R.gE g (R.Th t y)) v = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.HE.e (R.Th t y) v) :=
    congrArg (fun T : MMap (R.MY 0) => T v) (hg g (R.Th t y))
  have e4 := (GlobalTheory.ProjComm.proj_comm R h hr).1 g _ (thDn_type R t y v)
  exact e1.trans ((congrArg R.e0 (hact v)).trans (e4.trans
    ((congrArg (actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)) e2.symm).trans e3.symm)))

end Real

theorem th_intertwines : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ F : Face D A, R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsChain → (∀ t j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv)) (levChi _ (R.βY j) (R.datYt t j R.triv)) (R.νY t j) (R.fdY t j)) → ∀ t g κ, IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ → ∀ y y' : (R.HX t).H, (∀ h, (R.HX t).e y' h = (levChi _ R.βX (flagL (R.datXt t)) κ)⁻¹ • (R.HX t).e y (h * (finHom _).rangeRestrict κ)) → R.Th t y' = R.gE g (R.Th t y) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h hG _ hM hC hS t g κ' hκ' y y' hy
  refine (liftsExist_chain R h t 0 (lt_of_lt_of_le two_pos D.R.two_le_m) (R.eG g)).elim fun κ hκ => ?_
  exact th_of_thDn R h hG.record hM.HE hM.gE hC.Th t g y y' fun v => funext fun x =>
    (thDn_shift R h hM hC t (hS t) (R.eG g) κ' hκ' y y' hy κ hκ _ x).trans
      (actL_zero R t (R.eG g) κ hκ _ (thDn_type R t y v) x).symm

end GlobalTheory.ChainLiftEquiv

end
