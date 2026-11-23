import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActionPreservesPrincipalFlagMultiplic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftTranslateOfKernelFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicitySpaceEqZeroOfApplyNonzeroTensorZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKORatLeftAndEigenRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapMulRightOfMemCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FundamentalDomainSetIntegralMulRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionEqZeroOfNoLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExistStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastStepVectorLiftPairFlagLevelCharactersStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainEquiv

variable {D : D7}

theorem eq_of_natCast_mem {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (h1 : (p : 𝓞 K) ∈ P.asIdeal) (h2 : (q : 𝓞 K) ∈ P.asIdeal) : p = q := by
  by_contra hne
  have hc : IsCoprime (p : 𝓞 K) (q : 𝓞 K) := by
    simpa using (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)).map (Int.castRingHom (𝓞 K))
  obtain ⟨a, b, hab⟩ := hc
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem natCast_mem_of_isConjPl {P P' : Pl D.host.E} (h : Lev.IsConjPl P P') {n : ℕ} (hn : (n : 𝓞 D.host.E) ∈ P.asIdeal) :
    (n : 𝓞 D.host.E) ∈ P'.asIdeal := by
  obtain ⟨c, hc, e⟩ := h _ hn
  have : c = (n : 𝓞 D.host.E) := RingOfIntegers.ext (by rw [e]; simp)
  exact this ▸ hc

theorem conj_smul_of_isConjPl {P P' : Pl D.host.E} (h : Lev.IsConjPl P P') :
    GlobalTheory.Mem.Chr.ConjPl D.host.conj.toRingEquiv P P' := by
  obtain ⟨Q, hQ, -⟩ := GlobalTheory.Mem.Chr.existsUnique_conjPl D.host.conj.toRingEquiv P
  have : Q = P' := by
    apply HeightOneSpectrum.ext
    refine Q.isMaximal.eq_of_le P'.isPrime.ne_top fun y hy => ?_
    let x : 𝓞 D.host.E := (RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv).symm y
    have hxy : (y : D.host.E) = D.host.conj.toRingEquiv (x : D.host.E) :=
      (congrArg (fun z : 𝓞 D.host.E => (z : D.host.E))
        ((RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv).apply_symm_apply y)).symm
    obtain ⟨c, hc, e⟩ := h x (((GlobalTheory.Mem.Chr.conjPl_iff_mem _ _ _).1 hQ x y hxy).2 hy)
    have : c = y := RingOfIntegers.ext (by
      rw [e, hxy]; exact bridge_star_holds D.R D.host (x : D.host.E))
    exact this ▸ hc
  exact this ▸ hQ

theorem places_sep {T : Type} (L : LevCh D T) (μ0 : T) (h : L.Is μ0) (t : T) :
    (∀ PP ∈ L.Pg, ∀ PP', PP' ∈ L.Pg ∨ PP' ∈ L.Q t → ¬ Lev.IsConjPl PP PP') ∧ Disjoint L.Pg (L.Q t) := by
  have hQ : ∀ PP ∈ L.Q t, ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hP k hk
    obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := h.Q_pl t PP hP
    have h1 : (q : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rw [← hc]
      exact Ideal.absNorm_mem PP.asIdeal
    exact hne k (eq_of_natCast_mem PP hq (D.host.g_prime k) h1 hk)
  refine ⟨fun PP hP PP' hP' hc => ?_, Finset.disjoint_left.2 fun PP hP hP' => ?_⟩
  · obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := L.C.P.overP hk
    have h2 := natCast_mem_of_isConjPl hc h1
    rcases hP' with hP' | hP'
    · obtain ⟨k', hk'⟩ := (h.Pg PP').1 hP'
      have h3 := eq_of_natCast_mem PP' (D.host.g_prime k) (D.host.g_prime k') h2 (L.C.P.overP hk')
      have h4 : k = k' := by
        have := D.host.g_ne
        fin_cases k <;> fin_cases k' <;> simp_all
      subst h4
      exact ((GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) PP h1).2.2.2
        (L.C.P.pb k) (L.C.P.pb_over k) PP' (conj_smul_of_isConjPl hc)).2.1 hk hk'
    · exact hQ PP' hP' k h2
  · obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
    exact hQ PP hP' k (L.C.P.overP hk)

theorem lifts_chain {T : Type} (L : LevCh D T) (μ0 : T) (h : L.Is μ0) (t : T) (j : ℕ) (hj : j < D.R.m) :
    LiftsExist (Yc D j) (L.βY j) (L.datYt t j L.triv) := by
  obtain ⟨c, hc⟩ := h.βY j hj
  exact GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hc (places_sep L μ0 h t).1 (places_sep L μ0 h t).2

theorem multT_value {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (u : SmT M →ₗ[ℂ] (GA D V → ℂ)) (hu : u ∈ MultT θ M J χ) (v : SmT M) :
    (∀ γ ∈ GQ V, ∀ g, u v (γ * g) = u v g) ∧ ∀ k ∈ J, ∀ g, u v (g * k) = χ k * u v g := by
  have h0 := GlobalTheory.mult_value_left_cont_level θ M J χ _ ((mem_multT θ M J χ u).1 hu)
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have h1 := h0 f
    simp only [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply] at h1
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_⟩
    · simp only [map_smul, Pi.smul_apply, h1.1 γ hγ g]
    · simp only [map_smul, Pi.smul_apply, h1.2.2 k hk g, smul_eq_mul]; ring
  | add x y hx hy =>
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_⟩
    · simp only [map_add, Pi.add_apply, hx.1 γ hγ g, hy.1 γ hγ g]
    · simp only [map_add, Pi.add_apply, hx.2 k hk g, hy.2 k hk g]; ring

theorem integral_shift_lift (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (g0 : G0 L.Pg L.r)
    (κ : GA D V) (hκ : IsLevelLift V β L g0 κ) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) (𝓕 : Set (GA D V))
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (f : GA D V → ℂ) (hf : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g)
    (hi : IntegrableOn f 𝓕 ν) : ∫ g in 𝓕, f (g * κ) ∂ν = ∫ g in 𝓕, f g ∂ν := by
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  have h7 : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  obtain ⟨h5, h6⟩ := GlobalTheory.ParahoricCompact.isCompact_flag_and_lift V β L
  exact (GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ V) ν 𝓕 h𝓕 κ
    (GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup ν _ h5 κ (h6 g0 κ hκ)) f hf hi).2

theorem step {S T : HSp D} {Sp : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hom : IsWeilDatumO ψ S T χS χT om)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (f : WO S T → ℂ) (hpt : ∀ P, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P))
    (M : DSModel S Sp) (β : GL (Fin S.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (hL : flag1L L = L)
    (μ : Measure (GA D S)) (hμ : μ.IsHaarMeasure) (𝓔 : Set (GA D S)) (h𝓔 : IsFundamentalDomain (GQ S) 𝓔 μ)
    (hS : SchurMult θ M (levS S β L) (levChi S β L) μ 𝓔)
    {Ds : Type} [AddCommGroup Ds] [Module ℂ Ds] (It : PolF D T.rank S.rank →ₗ[ℂ] Ds →ₗ[ℂ] SmT M) (hIt : It ≠ 0)
    (CC : Submodule ℂ (Ds →ₗ[ℂ] (GA D T → ℂ)))
    (hCC : ∀ F : CC, ∀ v, ∀ γ ∈ GQ T, ∀ g, (F : Ds →ₗ[ℂ] (GA D T → ℂ)) v (γ * g) = (F : Ds →ₗ[ℂ] (GA D T → ℂ)) v g)
    (β' : GL (Fin T.rank) (Lev.EAf D)) (L' : LevDat D.host.E ℂ T.rank)
    (ν : Measure (GA D T)) (hν : ν.IsHaarMeasure) (𝓕 : Set (GA D T)) (h𝓕 : IsFundamentalDomain (GQ T) 𝓕 ν)
    (io : CC →ₗ[ℂ] MultT θ M (levS S β L) (levChi S β L))
    (hio : Lift.IsIo ν 𝓕 (thetaKO om) (pureTensorO ψ θ S T sS sT BS BT f) It CC _ io)
    (g0 : G0 L.Pg L.r) (κ : GA D S) (hκ : IsLevelLift S β L g0 κ) (g0' : G0 L'.Pg L'.r) (κ' : GA D T)
    (hκ' : IsLevelLift T β' L' g0' κ') (a' : ℂ) (hf : (levChi S β (flagL L) κ)⁻¹ • om (κ, κ') f = a' • f)
    (F F' : CC) (hF : ∀ v h, (F' : Ds →ₗ[ℂ] (GA D T → ℂ)) v h = a' * (F : Ds →ₗ[ℂ] (GA D T → ℂ)) v (h * κ'))
    (v : SmT M) (g : GA D S) :
    (io F' : SmT M →ₗ[ℂ] (GA D S → ℂ)) v g = (levChi S β (flagL L) κ)⁻¹ * (io F : SmT M →ₗ[ℂ] (GA D S → ℂ)) v (g * κ) := by
  have hc := levChi_ne_zero (β := β) (flagL L) κ
  have hf' : om (κ, κ') f = (levChi S β (flagL L) κ * a') • f := by
    rw [mul_smul, ← hf, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hm : actL S β L g0 ∘ₗ (io F : SmT M →ₗ[ℂ] (GA D S → ℂ)) ∈ MultT θ M (levS S β L) (levChi S β L) := by
    have h1 := GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity θ M hθ β L g0
    rw [hL] at h1
    exact (mem_multT θ M _ _ _).2 (h1 _ ((mem_multT θ M _ _ _).1 (io F).2) _ fun v => rfl)
  have hu : ∀ v g, (actL S β L g0 ∘ₗ (io F : SmT M →ₗ[ℂ] (GA D S → ℂ))) v g =
      (levChi S β (flagL L) κ)⁻¹ * (io F : SmT M →ₗ[ℂ] (GA D S → ℂ)) v (g * κ) := fun v g =>
    level_action_spec (by rw [hL]; exact (multT_value θ M _ _ _ (io F).2 v).2) ⟨κ, hκ⟩ κ hκ g
  have key := GlobalTheory.thetaLift_translate_of_kernel_fixed ν 𝓕 (thetaKO om) _ It CC _ io hio ?_ κ κ'
    (levChi S β (flagL L) κ)⁻¹ a' ?_ ?_ F F' ⟨_, hm⟩ hF hu
  · rw [key]; exact hu v g
  · intro u h0
    obtain ⟨φ, w, hw⟩ : ∃ φ w, It φ w ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hIt (LinearMap.ext fun φ => LinearMap.ext fun w => hn φ w)
    exact Subtype.ext (GlobalTheory.multT_eq_zero_of_apply_eq_zero θ M _ _ μ 𝓔 hθ hμ h𝓔 hS _ u.2 _ hw (h0 φ w))
  · intro g h φ
    rw [(GlobalTheory.thetaKO_rat_left_and_eigen_right ψ S T χS χT om hom _ (hpt φ)).2 κ κ' _
      (GlobalTheory.FiniteFock.om_pureTensorO_of_finite ψ θ S T χS χT om hθ hom sS sT BS BT f hpt κ hκ.1 κ' hκ'.1 _ hf' φ) g h]
    field_simp
  · intro F φ v g
    refine integral_shift_lift T β' L' g0' κ' hκ' ν hν 𝓕 h𝓕
      (fun h => thetaKO om g h (pureTensorO ψ θ S T sS sT BS BT f φ) * (F : Ds →ₗ[ℂ] (GA D T → ℂ)) v h)
      (fun γ hγ h => ?_) (hio.integ F φ v g)
    have h1 := (GlobalTheory.thetaKO_rat_left_and_eigen_right ψ S T χS χT om hom _ (hpt φ)).1 1 (GQ S).one_mem γ hγ g h
    rw [one_mul] at h1
    simp only [h1, hCC F v γ hγ h]

theorem parLev_of_rank {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L L' : LevDat D.host.E ℂ V.rank) (hr : V.rank ≤ L'.r)
    (h1 : L'.Pg = L.Pg) (h2 : L'.r = L.r) (h3 : L'.t = L.t) {x : GL (Fin V.rank) (Lev.EAf D)}
    (hx : x ∈ parLev D.sp.cm V.gram β L) : x ∈ parLev D.sp.cm V.gram β L' := by
  refine ⟨⟨hx.1.1, ?_⟩, ?_⟩
  · rw [h1, h2, h3]; exact hx.1.2
  · refine Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun _ => mem_parah.2 ⟨parLev_St hx, mem_blockTri.2 fun i j hij => ?_⟩
    have hi : i.val < L'.r := lt_of_lt_of_le i.2 hr
    simp [blk2, hi] at hij

theorem determinantBlock_eq_one_of_rank_le {κ : Type} [CommRing κ] {n r : ℕ} (hr : n ≤ r) (x : GL (Fin n) κ) : dBlk (blk2 r) 1 x = 1 := by
  have : IsEmpty {a : Fin n // blk2 r a = 1} := ⟨fun a => by
    have h := a.2
    simp [blk2, lt_of_lt_of_le a.1.2 hr] at h⟩
  by_cases hx : x ∈ blockTri (blk2 r)
  · apply Units.ext
    rw [diag_block_det_val 1 hx, Matrix.det_isEmpty, Units.val_one]
  · unfold dBlk ext1
    rw [dif_neg hx]

theorem rank_zero_le : (Yc D 0).rank ≤ D.R.r := by
  rw [D.sp.Y_rank _ (min_le_right _ _)]
  show D.R.r + min 0 D.R.m * D.R.t ≤ D.R.r
  simp

theorem levChi_zero {T : Type} (L : LevCh D T) (t : T) (P : LevelP L.Pg D.R.r ℂ) (κ : GA D (Yc D 0)) :
    levChi _ (L.βY 0) (L.datYt t 0 P) κ = levChi _ (L.βY 0) (L.dat0 P) κ := by
  unfold levChi levFn
  congr 2
  rw [Finset.prod_eq_one fun PP _ => by rw [determinantBlock_eq_one_of_rank_le (r := (L.datYt t 0 P).r) rank_zero_le, map_one]]
  rfl

theorem coef_left {H Γ W : Type} [Group H] [Group Γ] [AddCommGroup W] [Module ℂ W] (π : H →* Γ) (ρ : H →* Module.End ℂ W)
    (f : Γ → W) (γ z : H) (h : f (π γ * π z) = ρ γ (f (π z))) : ρ (γ * z)⁻¹ (f (π (γ * z))) = ρ z⁻¹ (f (π z)) := by
  rw [map_mul, h, ← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right]

theorem coef_shift {H Γ W : Type} [Group H] [Group Γ] [AddCommGroup W] [Module ℂ W] (π : H →* Γ) (ρ : H →* Module.End ℂ W)
    (f f' : Γ → W) (κ z : H) (hκ : ρ κ⁻¹ = 1) (a : ℂ) (hf : ∀ h, f' h = a • f (h * π κ)) :
    ρ z⁻¹ (f' (π z)) = a • ρ (z * κ)⁻¹ (f (π (z * κ))) := by
  rw [hf, mul_inv_rev, map_mul, map_mul, hκ, one_mul, map_smul]

theorem adForms_left {H Γ W : Type} [Group H] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* H)
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup H) (χ : J →* ℂˣ) (f : H → W) (hf : f ∈ Bridge.AdForms ι ρ J χ) (γ : Γ) (z : H) :
    f (ι γ * z) = ρ γ (f z) := by
  simpa using hf γ z 1

theorem toMap_left {V : HSp D} (c : CoefA V) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm] (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ)
    (J : Subgroup (Bridge.Gf V)) (χ : J →* ℂˣ) (f : Bridge.Gf V → c.W)
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J χ) (w : Dm) (γ : GA D V) (hγ : γ ∈ GQ V) (z : GA D V) :
    c.toMap pr f w (γ * z) = c.toMap pr f w z :=
  congrArg (fun x => pr x w) (coef_left (finHom V).rangeRestrict c.ρ f γ z
    (adForms_left (Bridge.ratF V) c.coef.ρ J χ f hf ⟨γ, hγ⟩ ((finHom V).rangeRestrict z)))

theorem range_left {V : HSp D} (c : CoefA V) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm] (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ)
    (M : HMod (Bridge.Gf V → c.W)) (J : Subgroup (Bridge.Gf V)) (χ : J →* ℂˣ)
    (hM : LinearMap.range M.e = Bridge.AdForms (Bridge.ratF V) c.coef.ρ J χ)
    (U : LinearMap.range (c.toMap pr ∘ₗ M.e)) (w : Dm) (γ : GA D V) (hγ : γ ∈ GQ V) (z : GA D V) :
    (U : Dm →ₗ[ℂ] (GA D V → ℂ)) w (γ * z) = (U : Dm →ₗ[ℂ] (GA D V → ℂ)) w z := by
  have h : ∃ x, (c.toMap pr ∘ₗ M.e) x = (U : Dm →ₗ[ℂ] (GA D V → ℂ)) := U.2
  refine h.elim fun x hx => ?_
  rw [← hx]
  exact toMap_left c pr J χ (M.e x) (hM.le (LinearMap.mem_range_self _ x)) w γ hγ z

theorem toMap_shift {V : HSp D} (c : CoefA V) (hc : c.Is) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm]
    (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) (f f' : Bridge.Gf V → c.W) (κ : GA D V) (hκ : κ ∈ GfC V) (a : ℂ)
    (hf : ∀ h, f' h = a • f (h * (finHom V).rangeRestrict κ)) (w : Dm) (z : GA D V) :
    c.toMap pr f' w z = a * c.toMap pr f w (z * κ) :=
  (congrArg (fun x => pr x w) (coef_shift (finHom V).rangeRestrict c.ρ f f' κ z (hc.1 _ ((GfC V).inv_mem hκ)) a hf)).trans
    (LinearMap.congr_fun (pr.map_smul a _) w)

section Chain

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def Rel (t : T0) (g0 : G0 R.Pg D.R.r) (j : ℕ) (F F' : R.CC t j) : Prop :=
  ∀ κ, IsLevelLift (Yc D j) (R.βY j) (R.datYt t j R.triv) g0 κ → ∀ v h,
    (F' : SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) v h =
      (levChi _ (R.βY j) (flagL (R.datYt t j R.triv)) κ)⁻¹ * (F : SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) v (h * κ)

variable {R}

theorem meas_chain (hY : R.models_νY) (hY' : R.models_νY') (t : T0) (j : ℕ) (hj : j < D.R.m) :
    (R.νY t j).IsHaarMeasure ∧ IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
  by_cases h1 : j + 1 < D.R.m
  · exact ⟨(hY t j h1).1.1, (hY t j h1).2⟩
  · obtain rfl : j = D.R.m - 1 := by omega
    exact ⟨(hY' t).1.1, (hY' t).2⟩

theorem rel_dnFrom (hl : R.toLevCh.Is A.μ0) (hi : R.models_inf) (hY : R.models_νY) (hY' : R.models_νY') (hc : R.IsChain)
    (hS : ∀ t j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv))
      (levChi _ (R.βY j) (R.datYt t j R.triv)) (R.νY t j) (R.fdY t j))
    (t : T0) (g0 : G0 R.Pg D.R.r) (n : ℕ) (hn : n < D.R.m) (F F' : R.CC t n) (hF : Rel R t g0 n F F') :
    Rel R t g0 0 (Lift.dnFrom (R.CC t) (R.ioY t) n F) (Lift.dnFrom (R.CC t) (R.ioY t) n F') := by
  induction n with
  | zero => exact hF
  | succ k ih =>
    have hk : k < D.R.m := by omega
    refine ih hk (R.ioY t k F) (R.ioY t k F') fun κ hκ v g => ?_
    obtain ⟨κ', hκ'⟩ := lifts_chain R.toLevCh _ hl t (k + 1) hn g0
    exact step R.ψ R.θ hi _ _ (R.ωY t k) (hc.ωY t k hn) _ _ _ _ (R.vY t k) (hc.ptY t k hn) (R.MY k)
      (R.βY k) (R.datYt t k R.triv) rfl _ (meas_chain hY hY' t k hk).1 _ (meas_chain hY hY' t k hk).2 (hS t k hk)
      (R.ItY k) (hc.ItY t k hn).ne (R.CC t (k + 1)) (fun U w => (multT_value _ _ _ _ _ U.2 w).1)
      (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) _ (meas_chain hY hY' t (k + 1) hn).1 _ (meas_chain hY hY' t (k + 1) hn).2
      (R.ioY t k) (hc.ioY t k (by omega)) g0 κ hκ g0 κ' hκ' _
      (GlobalTheory.T.stepVector_lift_pair_flagLevel_realized_chain R hl hi hc.ωY hc.vY t k hn g0 κ κ' hκ hκ') F F' (hF κ' hκ') v g

theorem rel_ioX (hl : R.toLevCh.Is A.μ0) (hi : R.models_inf) (hY : R.models_νY) (hY' : R.models_νY') (hc : R.IsChain)
    (hX : R.models_νX) (hcX : R.models_cX) (hHX : R.models_HX)
    (hS : ∀ t j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv))
      (levChi _ (R.βY j) (R.datYt t j R.triv)) (R.νY t j) (R.fdY t j))
    (t : T0) (g0 : G0 R.Pg D.R.r) (κ' : GA D D.sp.X') (hκ' : IsLevelLift D.sp.X' R.βX (R.datXt t) g0 κ') (y y' : (R.HX t).H)
    (hy : ∀ h, (R.HX t).e y' h = (levChi _ R.βX (flagL (R.datXt t)) κ')⁻¹ • (R.HX t).e y (h * (finHom _).rangeRestrict κ')) :
    Rel R t g0 (D.R.m - 1) (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y))
      (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')) := by
  intro κ hκ v g
  have hm : D.R.m - 1 < D.R.m := by have := D.R.two_le_m; omega
  exact step R.ψ R.θ hi _ _ (R.ωX t) (hc.ωX t) _ _ _ _ (R.vX t) (hc.ptX t) (R.MY (D.R.m - 1))
      (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) rfl _ (meas_chain hY hY' t _ hm).1 _ (meas_chain hY hY' t _ hm).2
      (hS t _ hm) R.ItX (hc.ItX t).ne _ (range_left R.cX R.prX (R.HX t) _ _ (hHX t).2.1) R.βX (R.datXt t) _
      (hX t).1.1 _ (hX t).2 (R.ioX t) (hc.ioX t) g0 κ hκ g0 κ' hκ' _
      (GlobalTheory.T.lastVector_lift_pair_flagLevel_characters R hl hi hc.ωX hc.vX t g0 κ κ' hκ hκ') _ _
      (toMap_shift R.cX hcX R.prX _ _ κ' hκ'.1 _ hy) v g

theorem hasType_of_mem (t : T0) (U : R.CC t 0) (v : SmT (R.MY 0)) :
    HasType (Yc D 0) (R.βY 0) (R.dat0 R.triv) ((U : SmT (R.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) v) := fun c hc z => by
  rw [← levChi_zero R.toLevCh t]
  exact (multT_value R.θ (R.MY 0) _ _ _ U.2 v).2 c
    ⟨hc.1, parLev_of_rank _ (R.dat0 R.triv) (R.datYt t 0 R.triv) rank_zero_le rfl rfl rfl hc.2.1, hc.2.2⟩ z

theorem act_of_rel (h : R.toLevCh.Is A.μ0) (t : T0) (g0 : G0 R.Pg D.R.r) (U U' : R.CC t 0) (hU : Rel R t g0 0 U U')
    (v : SmT (R.MY 0)) :
    (U' : SmT (R.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) v =
      actL _ (R.βY 0) (R.dat0 R.triv) g0 ((U : SmT (R.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) v) := by
  obtain ⟨k, hk⟩ := lifts_chain R.toLevCh _ h t 0 (by have := D.R.two_le_m; omega) g0
  have hk0 : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 k :=
    ⟨hk.1, parLev_of_rank _ (R.datYt t 0 R.triv) (R.dat0 R.triv) rank_zero_le rfl rfl rfl hk.2.1, hk.2.2⟩
  funext z
  have h1 := level_action_spec (L := R.dat0 R.triv) (hasType_of_mem t U v) ⟨k, hk0⟩ k hk0 z
  have h2 : levChi _ (R.βY 0) (flagL (R.datYt t 0 R.triv)) k = levChi _ (R.βY 0) (flagL (R.dat0 R.triv)) k :=
    levChi_zero R.toLevCh t (LevelP.full _ _ _) k
  rw [hU k hk v z, h2]
  exact h1.symm

noncomputable def thCC (t : T0) (y : (R.HX t).H) : R.CC t 0 :=
  Lift.dnFrom (R.CC t) (R.ioY t) (D.R.m - 1) (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y))

theorem thDn_eq (t : T0) (y : (R.HX t).H) : R.thDn t y = (thCC t y : SmT (R.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) := rfl

theorem e_Th (hT : R.chain_Th) (t : T0) (x : (R.HX t).H) (v : (R.MY 0).Vec) : R.HE.e (R.Th t x) v =
    R.e0 ((thCC t x : SmT (R.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) (PiTensorProduct.tprod ℂ v)) := by
  rw [hT t x, postOn_apply, thDn_eq t x]
  rfl

end Chain

end GlobalTheory.ChainEquiv
