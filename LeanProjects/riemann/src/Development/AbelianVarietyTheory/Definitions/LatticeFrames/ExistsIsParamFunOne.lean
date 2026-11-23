import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfTwoMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParamTrivialBoundUnitaryGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IntegrableOfIsAniso
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

noncomputable section

namespace GlobalTheory.Core.Rk.IP.Model

open scoped ComplexConjugate Matrix NNReal ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_cartan {m : Type} [Fintype m] [DecidableEq m] {n : ℕ} (e : Fin n ≃ m) {C : Matrix m (Fin n) ℂ}
    {J : Matrix m m ℂ} {G : Matrix (Fin n) (Fin n) ℂ} (hJ : J * J = 1) (hJ' : Jᴴ = J) (hG : IsUnit G.det)
    (h : Cᴴ * J * C = G) : ∃ s, IsCartanInv G s ∧ C * s = J * C := by
  have h1 : G⁻¹ * Cᴴ * J * C = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Cᴴ, h, Matrix.nonsing_inv_mul _ hG]
  generalize G⁻¹ * Cᴴ * J = C' at h1
  have h2 : C * C' = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 h1
  have h3 : C * (C' * J * C) = J * C := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have h4 : G * (C' * J * C) = Cᴴ * C := by
    rw [← h, Matrix.mul_assoc, h3, Matrix.mul_assoc, ← Matrix.mul_assoc J, hJ, Matrix.one_mul]
  refine ⟨C' * J * C, ⟨?_, ?_, ?_⟩, h3⟩
  · rw [Matrix.mul_assoc (C' * J), h3, Matrix.mul_assoc C', ← Matrix.mul_assoc J, hJ, Matrix.one_mul, h1]
  · rw [Matrix.mul_assoc, h4, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h3, Matrix.conjTranspose_mul, hJ', h]
  · rw [h4]
    refine Matrix.PosDef.conjTranspose_mul_self _ fun x y hxy => ?_
    have := congrArg (C' *ᵥ ·) hxy
    simpa [Matrix.mulVec_mulVec, h1] using this

theorem gramAt_unit (V : HSp D) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ).det := by
  have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det _ _).symm
  rw [this]
  exact (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).map _

theorem exists_real {θ : InfFam D} (hθ : IsInfFam θ) (A B : HSp D) (hA : A.SigOK) (h1 : 1 ≤ A.rank) {t : ℕ} (ht : 1 ≤ t)
    (hB : B.rank = A.rank + t) : ∃ sA sB cA a, HidaSetting θ A B sA sB t cA ∧ IsMaj A a ∧
      ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1 := by
  obtain ⟨cA, hc⟩ := exists_isCartanFrame A hA
  choose sA hs hs' using fun τ => exists_cartan (hA (tauE D τ)).choose
    (J := Formalism.UG.Jpq (A.sig (tauE D τ)).1 (A.sig (tauE D τ)).2)
    (by simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]) (by simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose])
    (gramAt_unit A τ) (hc τ)
  obtain ⟨a, ha, -, ha'⟩ := exists_isMaj_frameInv_eq hθ hs
  obtain ⟨b, hb⟩ := exists_isMaj B
  refine ⟨sA, frameInv θ B b, cA, a, ⟨h1, ht, hB, hθ, hA, hc, hs, hb.isCartanInv hθ, hs'⟩, ha, fun τ => ?_⟩
  obtain ⟨ε, hε⟩ := (isMaj_iff hθ).1 ha τ
  rw [← ha' τ, frameInv]
  calc _ = ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1) * ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hε, diagonal_sign_mul_self]

theorem isSplit_two (v : FinPl D) (h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal) : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  have hun : Formalism.MainNotions.SchurIrreducible.IsUnram (E := D.host.E) v := fun P _ => by
    haveI := GlobalTheory.BaseChangeExistsCompare.unram_of_cm D D.sp.cm P
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  rcases (LFun.exists_isInertChart _ (isCMExt_host D) v).1 hun with hs | ⟨w, hw⟩
  · exact hs
  · exfalso
    unfold Formalism.UG.IsInertAt at hw
    obtain ⟨ω, k, hω, hc⟩ := GlobalTheory.SplitIdem.exists_omega D
    let c : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom D.sp.cm.sig.toRingHom
    have hst : ∀ x ∈ w.asIdeal, c x ∈ w.asIdeal := by
      have : w.asIdeal ≤ w.asIdeal.comap c := by
        conv_lhs => rw [← hw]
        refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
        have e : c (algebraMap _ _ a) = algebraMap _ _ a := Subtype.ext (D.sp.cm.sig.commutes a)
        rw [Ideal.mem_comap, Ideal.mem_comap, e, ← hw]
        exact Ideal.mem_map_of_mem _ ha
      exact this
    have hcω : c ω = 1 - ω := RingOfIntegers.ext (by
      change star (ω : D.host.E) = _
      rw [GlobalTheory.SplitIdem.star_eq_conj, hc]; simp)
    have h2' : (2 : 𝓞 D.host.E) ∈ w.asIdeal := by
      rw [← hw, ← map_ofNat (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) 2]
      exact Ideal.mem_map_of_mem _ h2
    have hp : ω * (1 - ω) = 2 * k := RingOfIntegers.ext (by
      push_cast at hω ⊢
      simp only [map_mul, map_sub, map_one, map_ofNat, map_natCast]
      linear_combination -hω)
    have hone : ω ∈ w.asIdeal → False := fun h =>
      w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by have := add_mem h (hcω ▸ hst ω h); rwa [add_sub_cancel] at this))
    rcases w.isPrime.mem_or_mem (hp ▸ Ideal.mul_mem_right _ _ h2') with h | h
    · exact hone h
    · have := hst _ h
      rw [map_sub, map_one, hcω, sub_sub_cancel] at this
      exact hone this

theorem isSphOff_of_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS : RealMat S} {sT : RealMat T}
    {LS : Lat S} {LT : Lat T} {Φ : WO S T → ℂ} (h : IsVacO ψ θ S T sS sT LS LT Φ) (Sf : Finset (FinPl D)) :
    IsFockVec ψ θ S T sS sT Φ ∧ IsSphOff ψ S T LS LT Sf Φ ∧ Φ ≠ 0 := by
  have hle : latO S T LS LT (fun v => v ∉ Sf) ≤ latO S T LS LT fun _ => True :=
    AddSubgroup.closure_mono fun _ ⟨α, h1, _, h3⟩ => ⟨α, h1, fun _ h => absurd trivial h, h3⟩
  refine ⟨⟨h.2.theta, 1, fun l hl => ?_⟩, ⟨fun u hu => h.2.lat.1 u (hle hu), fun e he u hu => h.2.lat.2 e he u (hle hu)⟩, ?_⟩
  · obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hl
    exact h.2.fock p.1 p.2
  · rintro rfl
    obtain ⟨⟨p, hp⟩, h'⟩ := h.2.norm
    simpa [nrm2] using h' p hp

theorem exists_pair_unram (A B : HSp D) (hA : A.SigOK) (hB : B.SigOK) (h1 : 1 ≤ A.rank) {t : ℕ} (ht : 1 ≤ t)
    (hr : B.rank = A.rank + t) (LA : Lat A) (LB : Lat B) (hLA : IsSelfDualC A LA) (hLB : IsSelfDualC B LB) :
    ∃ ψ θ χA χB sA sB cA a om ν 𝓕 Φ, Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 ∧ IsFockVec ψ θ A B sA sB Φ ∧
      wcoef om ν 𝓕 Φ Φ 1 = 1 ∧ ∀ Sf, Unram ψ A B χB LA LB Sf Φ Φ := by
  obtain ⟨⟨θ, hθ⟩, ψ, hψ⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨om, hom, -⟩ := GlobalTheory.WeilProduct.exists_weilDatum_etaTilde D ψ hψ A B θ hθ LA LB hLA hLB η hη
  obtain ⟨sA, sB, cA, a, hs, ha, ha'⟩ := exists_real hθ A B hA h1 ht hr
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne D B.rank A.rank
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ A B sA sB hA hB hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.1 LA LB hLA hLB
  refine ⟨ψ, θ, _, _, sA, sB, cA, a, om, ν, 𝓕, Φ, ⟨hs, ha, ha', hom, hν⟩, (isSphOff_of_vac hΦ ∅).1, ?_, fun Sf =>
    ⟨hLA, hLB, fun v _ => isSplit_two v, fun w _ => ?_, (isSphOff_of_vac hΦ Sf).2.1, (isSphOff_of_vac hΦ Sf).2.1⟩⟩
  · have := hΦ.2.norm.2 (ν, 𝓕) hν
    rw [wcoef, Prod.mk_one_one, map_one, Module.End.one_apply, ip]
    simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, integral_complex_ofReal]
    exact_mod_cast this
  · refine LFun.unrAt_of_unramEverywhere (fun x a b c => ?_) w
    rw [MonoidHom.pow_apply, hη.2.1 x a b c, one_pow]

theorem exists_param_one (V : HSp D) {G : Type} [Group G] (v : FinPl D) (j : Gv V v →* G)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) :
    ∃ B, LFun.IsParamVec D.sp.cm.sig V.gram (frameLat V) h ((PRep.rightReg ℂ G ℂ).comp j) (fun _ => 1) B := by
  have hH := isHermND_gram V
  have hL := isLattice_frameLat_host V
  have hd := GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D V v
  have hun : Formalism.MainNotions.SchurIrreducible.IsUnram (E := D.host.E) v := fun P _ => by
    haveI := GlobalTheory.BaseChangeExistsCompare.unram_of_cm D D.sp.cm P
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have h0 : (fun _ : G => (1 : ℂ)) ≠ 0 := fun e => one_ne_zero (congrFun e 1)
  rcases (LFun.exists_isInertChart _ (isCMExt_host D) v).1 hun with hs | ⟨w', hw'⟩
  · obtain ⟨e, he, -, -⟩ := LFun.SplitChart.exists_isSplitChart (isCMExt_host D) hH hL.fg hL.span_eq_top h hs hd
    obtain ⟨B, hB, -⟩ := GlobalTheory.FinZeta.ParGL.exists_isSatVecGL_bound D.host.E w V.rank ℂ 1
      ⟨(innerₛₗ ℂ : ℂ →ₗ⋆[ℂ] ℂ →ₗ[ℂ] ℂ).flip, fun a b => by simp [mul_comm], fun a ha => by
        have : 0 < ‖a‖ ^ 2 := by positivity
        simpa [← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_pow] using this,
        fun _ _ _ => rfl⟩ 1 one_ne_zero (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl) fun _ _ => ⟨_, (mul_one _).symm⟩
    exact ⟨B, Or.inl ⟨hs, e, he, hB.map (LinearMap.pi fun _ => LinearMap.id) (fun _ _ => rfl) h0⟩⟩
  · have h' : w'.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext (v.isMaximal.eq_of_le
      (Ideal.comap_ne_top _ w'.isPrime.ne_top) (Ideal.map_le_iff_le_comap.1 (le_of_eq hw'))).symm
    obtain ⟨-, -, huniq, -, -⟩ := (LFun.exists_isInertChart _ (isCMExt_host D) v).2 w' h' hw'
    obtain rfl : w = w' := (huniq w).1 h
    obtain ⟨-, ⟨τ, hτ, -⟩, -, -, hconj⟩ := (LFun.exists_isInertChart _ (isCMExt_host D) v).2 w h hw'
    obtain ⟨⟨ϖ, hϖ⟩, hch⟩ := hconj τ hτ
    obtain ⟨e, he, -, -⟩ := hch V.rank V.gram (frameLat V) hH hL.fg hL.span_eq_top hd
    have hq : ((Formalism.UG.qV D.host.F v : ℕ) : ℂ) ≠ 0 := by exact_mod_cast LFun.qV_ne_zero v
    let α : Fin (V.rank / 2) → ℂˣ := fun i => Units.mk0 _ hq ^ ((V.rank : ℤ) - 1 - 2 * (i.val : ℤ))
    have h1 : LFun.IsSatVecU ϖ (Formalism.UG.qV D.host.F v) (PRep.rightReg ℂ (Formalism.UG.GU τ V.rank) ℂ) (fun _ => 1) α :=
      LFun.isSatVecU_of_isSphericalU hϖ (fun b _ _ _ _ => by
        rw [mul_one, Formalism.UG.chiDeltaU]
        refine (Finset.prod_eq_one fun i _ => ?_).symm
        split_ifs
        · simp only [α, Units.val_zpow_eq_zpow_val, Units.val_mk0]
          rw [← zpow_mul, ← zpow_add₀ hq]
          convert zpow_zero _ using 2
          ring
        · rfl) fun e => one_ne_zero (congrFun e 1)
    have h2 : LFun.IsSatVecU ϖ (Formalism.UG.qV D.host.F v) (1 : Representation ℂ (Formalism.UG.GU τ V.rank) ℂ) 1 α :=
      LFun.IsSatVecU.of_map hϖ (LinearMap.pi fun _ => LinearMap.id) (fun _ _ => rfl)
        (fun _ _ e => congrFun e 1) h1
    exact ⟨_, Or.inr ⟨hw', τ, ϖ, e, α, hϖ, he, h2.map hϖ (LinearMap.pi fun _ => LinearMap.id) (fun _ _ => rfl) h0, rfl⟩⟩

theorem exists_isSphCoef_one (V : HSp D) (v : FinPl D) : ∃ par, IsSphCoef V (frameLat V) v par fun _ => 1 := by
  classical
  choose B hB using exists_param_one V v (MonoidHom.id _)
  refine ⟨fun w => if h : w.under (𝓞 D.host.F) = v then B w h else 0, ⟨1, fun _ => by simp⟩, Gv V v → ℂ, inferInstance,
    inferInstance, (PRep.rightReg ℂ _ ℂ).comp (MonoidHom.id _), fun _ => 1, LinearMap.proj 1, fun w h => ?_,
    fun _ _ _ => rfl, fun _ => rfl⟩
  simpa only [dif_pos h] using hB w h

theorem exists_isParamFun_one (V : HSp D) : ∃ par, ∀ Sf : Finset (FinPl D),
    LFun.IsParamFun D.sp.cm.sig V.gram (frameLat V) (Sf : Set (FinPl D)) (fun _ => (1 : ℂ)) par ∧
      SphFun V (frameLat V) Sf fun _ => 1 := by
  choose B hB using fun w : HeightOneSpectrum (𝓞 D.host.E) =>
    exists_param_one V (w.under (𝓞 D.host.F)) (emb D.sp.cm.sig V.gram _) w rfl
  exact ⟨B, fun Sf => ⟨fun v _ w h => by subst h; exact hB w, fun _ _ _ _ _ => rfl⟩⟩

section Coef

variable {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χA χB : (AE D)ˣ →* Circle} {om : WRep A B} {ν : Measure (WO A B)}
  {𝓕 : Set (WO A B)} {Φ₁ Φ₂ : WO A B → ℂ}

theorem measurable_wcoef (hom : IsWeilDatumO ψ A B χA χB om) (hν : IsCovolOne (ratL B A) ν 𝓕)
    (h₁ : IsThetaFunO ψ A B Φ₁) (h₂ : IsThetaFunO ψ A B Φ₂) : StronglyMeasurable (wcoef om ν 𝓕 Φ₁ Φ₂) := by
  have : BorelSpace (WO A B) := ⟨rfl⟩
  have : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hν.2.2]; exact ENNReal.one_lt_top⟩
  have h : Measurable (Function.uncurry fun (g : GA D A) (w : WO A B) => om (g, 1) Φ₁ w * conj (Φ₂ w)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun w => ((hom.om_cont Φ₁ h₁ w).comp (Continuous.prodMk_left 1)).mul continuous_const)
      fun g => ((hom.om_pres _ _ h₁).cont.mul (Complex.continuous_conj.comp h₂.cont)).measurable
  have : SigmaFinite (ν.restrict 𝓕) := IsFiniteMeasure.toSigmaFinite _
  have : SFinite (ν.restrict 𝓕) := instSFiniteOfSigmaFinite
  exact h.stronglyMeasurable.integral_prod_right

theorem bounded_wcoef (hom : IsWeilDatumO ψ A B χA χB om) (hν : IsCovolOne (ratL B A) ν 𝓕)
    (h₁ : IsThetaFunO ψ A B Φ₁) (h₂ : IsThetaFunO ψ A B Φ₂) : ∃ C : ℝ, ∀ g, ‖wcoef om ν 𝓕 Φ₁ Φ₂ g‖ ≤ C := by
  refine ⟨(GlobalTheory.Size.l2O ν 𝓕 Φ₁ * GlobalTheory.Size.l2O ν 𝓕 Φ₂).toReal, fun g => ?_⟩
  have h := GlobalTheory.Size.enorm_ipO_le ν 𝓕 (hom.om_pres (g, 1) _ h₁).cont h₂.cont
  rw [GlobalTheory.Size.l2O_om_apply_eq_of_isThetaFunO hom hν.1 hν.2.1 h₁] at h
  rw [← toReal_enorm]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (GlobalTheory.Size.l2NormOnFundamentalDomain_thetaFunction_ne_top hom.std hν.1 hν.2.1 h₁)
    (GlobalTheory.Size.l2NormOnFundamentalDomain_thetaFunction_ne_top hom.std hν.1 hν.2.1 h₂)) h

end Coef

theorem openOff_empty {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A B : HSp D} {χA χB : (AE D)ˣ →* Circle}
    {sA : RealMat A} {sB : RealMat B} {t : ℕ} {cA : CptF A} {a : GL (Fin A.rank) (AE D)} {om : WRep A B}
    {ν : Measure (WO A B)} {𝓕 : Set (WO A B)} (h : Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕) (hq : ∀ τ, (A.sig τ).2 = 0) :
    openOff A (frameLat A) ∅ = Kmax A a := by
  obtain ⟨-, -, -, hθ, -, hc, -, -, hs⟩ := h.setting
  have h1 : ∀ τ, frameInv θ A a τ = 1 := fun τ => by
    have hJ : Formalism.UG.Jpq (A.sig (tauE D τ)).1 (A.sig (tauE D τ)).2 = 1 := by
      have : IsEmpty (Fin (A.sig (tauE D τ)).2) := by rw [hq]; infer_instance
      rw [Formalism.UG.Jpq, ← Matrix.fromBlocks_one]
      congr 1
      exact Subsingleton.elim _ _
    have h2 : gramAt D A τ * sA τ = gramAt D A τ := by
      conv_lhs => rw [← hc τ, Matrix.mul_assoc, hs τ]
      rw [← hc τ, hJ]; simp
    have h3 := h.maj_eq τ
    rw [h2] at h3
    rw [frameInv, Matrix.mul_assoc]
    exact mul_eq_one_comm.1 h3
  ext g
  rw [SetLike.mem_coe, h.maj.mem_Kmax_iff hθ, mem_levelOpen]
  simp [openOff, h1]

theorem heckeForm_hypotheses (D : D7) {n t : ℕ} (hn : 1 ≤ n) (ht : 1 ≤ t) :
    ∃ (A B : HSp D) (ψ : _) (θ : _) (χA χB : _) (sA : _) (sB : _) (cA : _) (a : _) (om : _) (ν : _) (𝓕 : _) (Φ : _)
      (m : Measure (GA D A)) (par : _), A.rank = n ∧
      Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 ∧ wittIndex B = 0 ∧ IsFockVec ψ θ A B sA sB Φ ∧ wcoef om ν 𝓕 Φ Φ 1 = 1 ∧
      Unram ψ A B χB (frameLat A) (frameLat B) ∅ Φ Φ ∧ m.IsHaarMeasure ∧ (fun _ => (1 : ℂ)) ∈ A0 θ A cA ∧
      LFun.IsParamFun D.sp.cm.sig A.gram (frameLat A) ((∅ : Finset (FinPl D)) : Set (FinPl D)) (fun _ => (1 : ℂ)) par ∧
      SphFun A (frameLat A) ∅ (fun _ => 1) ∧
      ∀ s, IntegrableOn (integrand om m ν 𝓕 (frameLat A) a Φ Φ (fun _ => 1) (fun _ => 1) s) (openOff A (frameLat A) ∅) m := by
  let A : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n
  let B : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral (n + t)
  have hA : IsAniso A := GlobalTheory.ThetaMean.Model.isAniso_posSpace n
  obtain ⟨ψ, θ, χA, χB, sA, sB, cA, a, om, ν, 𝓕, Φ, hP, hΦ, h1, hU⟩ := exists_pair_unram A B (Examples₂.posSpace_sigOK _ _)
    (Examples₂.posSpace_sigOK _ _) hn ht rfl _ _ (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat B)
  obtain ⟨par, hpar⟩ := exists_isParamFun_one A
  have hcc : (fun _ => (1 : ℂ)) ∈ cuspCont A := ⟨continuous_const, fun _ _ _ => rfl, fun r C hC => absurd hC (hA r C)⟩
  refine ⟨A, B, ψ, θ, χA, χB, sA, sB, cA, a, om, ν, 𝓕, Φ, Measure.haar, par, rfl, hP,
    wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.ThetaMean.Model.isAniso_posSpace _), hΦ, h1, hU ∅, inferInstance,
    ⟨⟨isAutFunSm_const θ A 1, .of_invariant fun _ _ _ => rfl⟩, hcc⟩, (hpar ∅).1, (hpar ∅).2, fun s => ?_⟩
  rw [openOff_empty hP fun _ => rfl]
  have hK : IsCompact (Kmax A a : Set (GA D A)) := isCompact_levelAll (isCMExt_host D) _ _ _
  obtain ⟨C, hC⟩ := bounded_wcoef hP.weil hP.covol hΦ.1 hΦ.1
  have h2 : IntegrableOn (wcoef om ν 𝓕 Φ Φ) (Kmax A a) Measure.haar :=
    Measure.integrableOn_of_bounded hK.measure_ne_top
      (measurable_wcoef hP.weil hP.covol hΦ.1 hΦ.1).aestronglyMeasurable (.of_forall hC)
  refine IntegrableOn.congr_fun (h2.mul_const (petersson A Measure.haar (fun _ => 1) fun _ => 1)) (fun g hg => ?_)
    hK.measurableSet
  have h3 : hgtL A (frameLat A) a g = 1 := by
    have := hgt_mul A a 1 ((io_mem_Khat A a).2 ⟨hg, one_mem _⟩)
    change hgt A a (io A (g, 1)) = 1
    simpa using this
  simp only [integrand, h3, one_npow, mul_one]
  rfl

theorem up_smul {A B : HSp D} (om : WRep A B) (m : Measure (GA D A)) (Φ : WO A B → ℂ) (c : ℂ) (u : GA D A → ℂ) :
    up om m Φ (c • u) = c • up om m Φ u := funext fun h => by
  simp only [up, AutomorphicL2Unitary.descend, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  exact integral_congr_ae (.of_forall fun q => by ring)

theorem up_eq_conj_lift {A B : HSp D} (om : WRep A B) (m : Measure (GA D A)) (Φ : WO A B → ℂ) (u : GA D A → ℂ)
    (h : GA D B) : up om m Φ u h = conj (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m (fun g h => conj (thetaKO om g h Φ)) u h) := by
  simp only [up, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift, petersson, pet, AutomorphicL2Unitary.descend, ← integral_conj, map_mul, Complex.conj_conj]

end GlobalTheory.Core.Rk.IP.Model

end
