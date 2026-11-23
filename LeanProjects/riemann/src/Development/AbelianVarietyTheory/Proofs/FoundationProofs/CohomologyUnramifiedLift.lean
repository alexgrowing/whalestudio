import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralTwoCocycleReciprocityTrivialAtLastPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductUnramifiedClassesVanishesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedCocycleKillsRootsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAuxiliaryPrimeFrobeniusNearCommutatorStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductCoboundaryModStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalHeightFrobeniusPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharacterPrimeConductorDegreePrimePowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocyclePairingLocallyConstantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalConditionsIndependentOfPlaceOverStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOfNatCastMem
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CongruenceMulOfUnitFactor
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemOfFinTwo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormAlgebraMapLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenKerAndIsLocallyConstant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColRepApplyOfOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixesRootOfUnity
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

section HtComm

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

private theorem htc_norm_le_one_of_isIntegral (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.GlobalTheory.IntegralAlgebraMapNormBound.main x hx

theorem htc_norm_le_one (c : Coef l) (x : Qbar l) (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  htc_norm_le_one_of_isIntegral x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

theorem htc_continuous_cycBar : Continuous (cycBar ℚ Ω l) :=
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ ℚ Ω l)

theorem htc_dual1_eq_one {W : R2 Ω l} {s : G ℚ Ω} (hs : s ∈ N0g W) : dual1 W s = 1 := by
  obtain ⟨hc, hw⟩ := Subgroup.mem_inf.1 hs
  rw [MonoidHom.mem_ker] at hc hw
  have hd : dt W s = 1 := by simp [dt, hw]
  simp [dual1, tw, hw, hc, hd]

theorem htc_cocycle {W : R2 Ω l} {x : G ℚ Ω → Fin 2 → Qbar l} (hx : x ∈ Z1 (Loc.colRep W)) (s t : G ℚ Ω) :
    x (s * t) = x s + mat W s *ᵥ x t := by
  have := hx.2 s t
  simpa [Loc.colRep, Matrix.toLin'_apply] using this

theorem htc_open_near (f : G ℚ Ω → Qbar l) (hf : Continuous f) (σ : G ℚ Ω) (r : ℝ) (hr : 0 < r) :
    ∃ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) ∧ ∀ a ∈ U, ‖f (σ * a) - f σ‖ < r := by
  have hc : Continuous fun a : G ℚ Ω => ‖f (σ * a) - f σ‖ :=
    ((hf.comp (continuous_const_mul σ)).sub continuous_const).norm
  have h1 : {a : G ℚ Ω | ‖f (σ * a) - f σ‖ < r} ∈ nhds (1 : G ℚ Ω) :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp [hr])
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω _).1 h1
  haveI := hE
  exact ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen, fun a ha => hsub ha⟩

theorem htc_ker_toGS (S : Set Pl) : (toGS Ω S).ker = NS (F := ℚ) Ω S := by
  unfold toGS
  exact QuotientGroup.ker_mk' _

theorem htc_NS_anti {S S' : Set Pl} (h : S ⊆ S') : NS (F := ℚ) Ω S' ≤ NS (F := ℚ) Ω S := by
  unfold NS
  refine Subgroup.topologicalClosure_minimal _ (le_trans (Subgroup.normalClosure_mono ?_)
    (Subgroup.le_topologicalClosure _)) (Subgroup.isClosed_topologicalClosure _)
  intro x hx
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨v, hv, A, hA, hx⟩ := hx
  exact ⟨v, fun h' => hv (h h'), A, hA, hx⟩

theorem htc_Ine_le_NS {S : Set Pl} {v : Pl} (hv : v ∉ S) {B : ValuationSubring Ω} (hB : IsPlaceOver B v) :
    Ine (F := ℚ) B ≤ NS (F := ℚ) Ω S := fun s hs =>
  Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure (by
    simp only [Set.mem_iUnion]
    exact ⟨v, hv, B, hB, hs⟩))

theorem htc_NS_le (S : Set Pl) (H : Subgroup (G ℚ Ω)) [H.Normal] (hc : IsClosed (H : Set (G ℚ Ω)))
    (h : ∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → Ine (F := ℚ) B ≤ H) : NS (F := ℚ) Ω S ≤ H := by
  unfold NS
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hc
  intro s hs
  simp only [Set.mem_iUnion] at hs
  obtain ⟨v, hv, B, hB, hs⟩ := hs
  exact h v hv B hB hs

theorem htc_ht_mem (c : Coef l) (W : R2 Ω l) (y z : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l)
    (hO : ∀ s i j, mat W s i j ∈ c.O) (hyO : ∀ s i, y s i ∈ c.O) (hzO : ∀ s i, z s i ∈ c.O) (huO : ∀ s, u s ∈ c.O)
    (s : G ℚ Ω) : ht W y z u s ∈ c.O :=
  _root_.GlobalTheory.FinTwoMembership.ht_mem c W y z u hO hyO hzO huO s

theorem congruence_mul_of_unit_factor {n : ℕ} {P h un D : Qbar l} (h1 : Cg n (P * h) 0) (h2 : Cg n P (un * D)) (hun : ‖un‖ = 1)
    (hh : ‖h‖ ≤ 1) : Cg n (D * h) 0 :=
  _root_.UpperTheory.Reformulated.B.Yza4.congruence_mul_of_unit_factor h1 h2 hun hh

theorem htc_cocycle_NS (S : Set Pl) (V : R2 Ω l) (H : Subgroup (G ℚ Ω)) (x : G ℚ Ω → Fin 2 → Qbar l) (hN : H.Normal)
    (hc : IsClosed (H : Set (G ℚ Ω))) (hV : ∀ a ∈ H, V a = 1) (hx : x ∈ Z1 (Loc.colRep V))
    (h : ∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ s ∈ Ine (F := ℚ) B, s ∈ H ∧ x s = 0) :
    ∀ a ∈ NS (F := ℚ) Ω S, x a = 0 :=
  _root_.GlobalTheory.ZeroSubmodule.main S V H x hN hc hV hx h

theorem htc_killsMu_open [IsAlgClosure ℚ Ω] (C : Type) [Group C] (N : ℕ) (ψ : G ℚ Ω →* C) (hN : N ≠ 0)
    (h : KillsMu N ψ) : IsOpen (ψ.ker : Set (G ℚ Ω)) ∧ IsLocallyConstant ψ :=
  _root_.GlobalTheory.OpenKernelLocallyConstant.isOpen_ker_and_isLocallyConstant C N ψ hN h

theorem htc_Ine_fix_mu (N : ℕ) (v : Pl) (B : ValuationSubring Ω) (hB : IsPlaceOver B v) (hN : ((N : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    ∀ s ∈ Ine (F := ℚ) B, ∀ ζ : Ω, ζ ^ N = 1 → s ζ = ζ :=
  _root_.GlobalTheory.InertiaRootOfUnity.inertia_fixes_root_of_unity N v B hB hN

theorem htc_places (w : Pl) : normV w ≠ 0 ∧ (∀ v : Pl, v ≠ w → ((normV w : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) ∧
    ∀ (p : ℕ), p.Prime → ∀ v v' : Pl, ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → ((p : ℕ) : 𝓞 ℚ) ∈ v'.asIdeal → v = v' :=
  _root_.UpperTheory.Reformulated.B.Yza3.htc_places w

end HtComm

theorem ht_vanish_commutator : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (y z : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l) (S' : Finset Pl) (n : ℕ), 1 ≤ n → (∀ s i j, mat W s i j ∈ c.O) → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, y s i ∈ c.O) → (∀ s i, z s i ∈ c.O) → Unr W y → (∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c.O) ∧ ∀ s ∈ Ine (F := ℚ) B, z s = mat (dual1 W) s *ᵥ x - x) → (∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c.O) ∧ ∀ s ∈ Dec (F := ℚ) A, z s = mat (dual1 W) s *ᵥ x - x) → (∀ w : Pl, w ∉ S' → l ^ n ∣ normV w - 1 → ∀ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)), KillsMu (normV w) ψ → Function.Surjective ψ → Tame c W y n w ψ) → Continuous u → (∀ s, u s ∈ c.O) → (∀ s, ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cg n (u (s * a)) (u s)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → ∀ σ ∈ ⁅H0g W, H0g W⁆, Cg n ((mat W σ - 1).det * ht W y z u σ) 0 := by
  intro hLit l _ Ω _ _ _ e S A W hW c y z u S' n hn hO hy hz hyO hzO hyU hzq hzl hTame huc huO huS hcup σ hσ
  classical
  have hWc : Continuous W := hW.cont
  have hdet2 : dt W ^ 2 = 1 := hW.det2
  have hAbove : ContainsAbove S l := hW.above
  have hyc : Continuous y := hy.1
  have hzc : Continuous z := hz.1
  have hσH : σ ∈ H0g W := by
    refine (Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_) hσ
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hσcyc : σ ∈ ⁅(cycBar ℚ Ω l).ker, (cycBar ℚ Ω l).ker⁆ := Subgroup.commutator_mono inf_le_left inf_le_left hσ
  have hdtσ : dt W σ = 1 := (Subgroup.mem_inf.1 hσH).2
  set F : G ℚ Ω → Qbar l := fun s => (mat W s - 1).det * ht W y z u s with hF
  have hmatc : Continuous fun s => mat W s := Units.continuous_val.comp hWc
  have hFc : Continuous F := by
    have h1 : Continuous fun s => mat W s - 1 := hmatc.sub continuous_const
    have h2 : Continuous fun s => (mat W s - 1).det := h1.matrix_det
    have h3 : Continuous fun s => (mat W s - 1).adjugate *ᵥ y s := h1.matrix_adjugate.matrix_mulVec hyc
    refine h2.mul ?_
    unfold ht om
    refine (h2.mul huc).sub ?_
    have hz0 := (continuous_apply 0).comp hzc
    have hz1 := (continuous_apply 1).comp hzc
    have h30 := (continuous_apply 0).comp h3
    have h31 := (continuous_apply 1).comp h3
    exact (h30.mul hz1).sub (h31.mul hz0)
  have hr : (0 : ℝ) < ‖((l : ℕ) : Qbar l) ^ n‖ :=
    norm_pos_iff.2 (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
  have hr2 : (0 : ℝ) < ‖(2 : Qbar l)‖ := norm_pos_iff.2 two_ne_zero
  obtain ⟨U₁, hU₁o, hU₁⟩ := htc_open_near F hFc σ _ hr
  obtain ⟨U₂, hU₂o, hU₂⟩ := htc_open_near (fun s => (mat W s).det) hmatc.matrix_det σ _ hr2
  have hdtv : ∀ s, ((dt W s : (Qbar l)ˣ) : Qbar l) = (mat W s).det := fun s => rfl
  obtain ⟨w, B, τ, hwS, hwS', hB, hFrob, hτD, hστ, hdiv, hpow⟩ :=
    GlobalTheory.T.exists_auxiliary_prime_frobenius_near_commutator l Ω n S S' (U₁ ⊓ U₂) σ (by rw [Subgroup.coe_inf]; exact hU₁o.inter hU₂o) hσcyc
  have hdtτ : dt W τ = 1 := by
    have h := congrArg (fun f : G ℚ Ω →* (Qbar l)ˣ => f τ) hdet2
    simp only [pow_two, MonoidHom.mul_apply, MonoidHom.one_apply] at h
    have hsq : ((dt W τ : (Qbar l)ˣ) : Qbar l) * (dt W τ : Qbar l) = 1 := by rw [← Units.val_mul, h, Units.val_one]
    rcases mul_self_eq_one_iff.1 hsq with h1 | h1
    · exact Units.ext h1
    · exfalso
      have h3 := hU₂ _ (Subgroup.mem_inf.1 hστ).2
      simp only [mul_inv_cancel_left] at h3
      rw [← hdtv, ← hdtv, h1, hdtσ, Units.val_one, show (-1 : Qbar l) - 1 = -2 by ring, norm_neg] at h3
      exact lt_irrefl _ h3
  have hwl : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => hwS (hAbove w h)
  obtain ⟨ψ, hKill, hSurj, hIne1, hDecK⟩ := GlobalTheory.T.exists_character_primeConductor_degree_prime_pow l Ω n w hn hdiv
  have hT := hTame w hwS' hdiv ψ hKill hSurj
  obtain ⟨P, un, d, hPO, hun, hPfrob, hdc, hdO, hdrel, hdker, hdq⟩ :=
    GlobalTheory.T.unramified_cocycle_kills_roots l Ω c n S W y w ψ hWc hO hAbove hW.unr hyO hKill hwS hT
  obtain ⟨hNw, hNwv, hpl⟩ := htc_places w
  obtain ⟨hψo, hψlc⟩ := htc_killsMu_open _ (normV w) ψ hNw hKill
  have hψIne : ∀ v, v ≠ w → ∀ B' : ValuationSubring Ω, IsPlaceOver B' v → Ine (F := ℚ) B' ≤ ψ.ker :=
    fun v hv B' hB' s hs => hKill s (fun ζ hζ => htc_Ine_fix_mu (normV w) v B' hB' (hNwv v hv) s hs ζ hζ)

  haveI hN0n : (N0g W).Normal := by unfold N0g; infer_instance
  have hN0c : IsClosed (N0g W : Set (G ℚ Ω)) := by
    unfold N0g
    rw [Subgroup.coe_inf, MonoidHom.coe_ker, MonoidHom.coe_ker]
    exact (isClosed_singleton.preimage htc_continuous_cycBar).inter (isClosed_singleton.preimage hWc)
  have hIneN0 : ∀ v, v ∉ (S : Set Pl) → ∀ B' : ValuationSubring Ω, IsPlaceOver B' v → Ine (F := ℚ) B' ≤ N0g W := by
    intro v hv B' hB' s hs
    have hvl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv (hAbove v h)
    refine Subgroup.mem_inf.2 ⟨?_, hW.unr v hv B' hB' hs⟩
    rw [MonoidHom.mem_ker]
    exact cyc_eq_one_of_mem_Ine hvl hB' hs
  have hNS_N0 : NS (F := ℚ) Ω (S : Set Pl) ≤ N0g W := htc_NS_le _ _ hN0c hIneN0
  have hNSy : ∀ a ∈ NS (F := ℚ) Ω (S : Set Pl), y a = 0 :=
    htc_cocycle_NS _ W (N0g W) y hN0n hN0c (fun a ha => (Subgroup.mem_inf.1 ha).2) hy (by
      intro v hv B' hB' s hs
      have hvl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv (hAbove v h)
      have hWs : W s = 1 := (hIneN0 v hv B' hB' hs).2
      obtain ⟨B0, hB0, hcob⟩ := hyU v hvl
      obtain ⟨x, hx⟩ := (GlobalTheory.T.localConditions_independent_of_place_over l Ω W y hy v B0 B' hB0 hB').1 hcob
      refine ⟨hIneN0 v hv B' hB' hs, ?_⟩
      rw [hx s hs, show mat W s = 1 by simp [mat, hWs], Matrix.one_mulVec, sub_self])
  have hNSz : ∀ a ∈ NS (F := ℚ) Ω (S : Set Pl), z a = 0 :=
    htc_cocycle_NS _ (dual1 W) (N0g W) z hN0n hN0c (fun a ha => htc_dual1_eq_one ha) hz (by
      intro v hv B' hB' s hs
      have hvl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv (hAbove v h)
      have hd1 : dual1 W s = 1 := htc_dual1_eq_one (hIneN0 v hv B' hB' hs)
      obtain ⟨x, -, hx⟩ := hzq v hvl B' hB'
      refine ⟨hIneN0 v hv B' hB' hs, ?_⟩
      rw [hx s hs, show mat (dual1 W) s = 1 by simp [mat, hd1], Matrix.one_mulVec, sub_self])
  set S2 : Finset Pl := insert w S with hS2
  have hsub : (S : Set Pl) ⊆ (S2 : Set Pl) := Finset.coe_subset.2 (Finset.subset_insert _ _)
  have hNSψ : NS (F := ℚ) Ω (S2 : Set Pl) ≤ ψ.ker := by
    refine htc_NS_le _ _ (Subgroup.isClosed_of_isOpen _ hψo) fun v hv B' hB' => hψIne v ?_ B' hB'
    rintro rfl
    exact hv (by simp [hS2])
  have hker2 : (toGS Ω (S2 : Set Pl)).ker ≤ N0g W ⊓ ψ.ker := by
    rw [htc_ker_toGS]
    exact le_inf ((htc_NS_anti hsub).trans hNS_N0) hNSψ
  have hxi := GlobalTheory.T.cocycle_pairing_locally_constant l Ω c n S2 W y z d u P ψ hWc hO hdet2 hker2 hψlc hPO hy hz hyO hzO
    (fun a ha => by
      rw [htc_ker_toGS] at ha
      have ha' := htc_NS_anti hsub ha
      refine ⟨hNSy a ha', hNSz a ha', hdker a ?_⟩
      rw [htc_ker_toGS, ← Finset.coe_insert]
      exact ha)
    huc huO (fun s a ha => huS s a (by rw [htc_ker_toGS] at ha ⊢; exact htc_NS_anti hsub ha)) hcup hdc hdO hdrel

  have hψ0 : ∀ s, ψ s = 1 → (((ψ s).toAdd.val : ℕ) : Qbar l) = 0 := fun s hs => by rw [hs]; simp
  have hDecψ : ∀ v ∈ S, ∀ B' : ValuationSubring Ω, IsPlaceOver B' v → ∀ s ∈ Dec (F := ℚ) B', ψ s = 1 :=
    fun v hv B' hB' s hs => hDecK v (fun h => hwS (h ▸ hv)) (hpow v hv) B' hB' hs
  have hCv : ∀ a : Fin 2 → Qbar l, Cv n a a := fun a i => by simp [Cg]
  have hCocd : ∀ v ∈ S, ∀ B' : ValuationSubring Ω, IsPlaceOver B' v → Coc1 c n W (Dec (F := ℚ) B') d :=
    fun v hv B' hB' => ⟨hdc.continuousOn, hdO, fun s hs t _ => by
      have := hdrel s t
      rw [hψ0 s (hDecψ v hv B' hB' s hs), zero_mul, zero_smul, add_zero] at this
      exact this⟩
  have hCocz : ∀ H : Subgroup (G ℚ Ω), Coc1 c n (dual1 W) H z :=
    fun H => ⟨hzc.continuousOn, hzO, fun s _ t _ => by rw [htc_cocycle hz]; exact hCv _⟩
  set ξ : G ℚ Ω → G ℚ Ω → Qbar l := fun s t => cup W d z s t - (((ψ s).toAdd.val : ℕ) : Qbar l) * P * eps l s * u t
    with hξ
  have hξDec : ∀ v ∈ S, ∀ B' : ValuationSubring Ω, IsPlaceOver B' v → Cob2 c n (Dec (F := ℚ) B') (cup W d z) →
      Cob2 c n (Dec (F := ℚ) B') ξ := by
    rintro v hv B' hB' ⟨x, hx1, hx2, hx3⟩
    refine ⟨x, hx1, hx2, fun s hs t ht => ?_⟩
    have e : ξ s t = cup W d z s t := by
      simp only [hξ, hψ0 s (hDecψ v hv B' hB' s hs), zero_mul, sub_zero]
    rw [e]
    exact hx3 s hs t ht
  have hloc : ∀ v ∈ S2, v ≠ w → ∃ B' : ValuationSubring Ω, IsPlaceOver B' v ∧ Cob2 c n (Dec (F := ℚ) B') ξ := by
    intro v hv hvw
    have hvS : v ∈ S := (Finset.mem_insert.1 hv).resolve_left hvw
    by_cases hvl : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
    · obtain ⟨v', hAv', hlv'⟩ := hW.atL
      have hvv' : v = v' := hpl l (Fact.out : l.Prime) v v' hvl hlv'
      subst hvv'
      refine ⟨A, hAv', hξDec v hvS A hAv' ?_⟩
      obtain ⟨x, hxO, hx⟩ := hzl
      exact GlobalTheory.T.cup_product_coboundary_mod l Ω c n W (Dec (F := ℚ) A) d z hWc hO hdet2 (hCocd v hvS A hAv') (hCocz _)
        (Or.inr ⟨x, hxO, fun s hs => by rw [hx s hs]; exact hCv _⟩)
    · obtain ⟨B', hB', hcobd⟩ := hdq v hvS hvl
      obtain ⟨x, hxO, hx⟩ := hzq v hvl B' hB'
      refine ⟨B', hB', hξDec v hvS B' hB' ?_⟩
      exact GlobalTheory.T.cupProduct_unramifiedClasses_vanishes hLit l Ω c n W v B' d z hWc hO hdet2 hB' hvl (hCocd v hvS B' hB') (hCocz _) hcobd
        ⟨x, hxO, fun s hs => by rw [hx s hs]; exact hCv _⟩
  have hAbove2 : ContainsAbove S2 l := fun v hv => Finset.mem_insert_of_mem (hAbove v hv)
  have hCobw := GlobalTheory.T.integralTwoCocycle_reciprocity_trivial_at_last_place hLit l Ω c n S2 ξ w hW.l_odd hAbove2 hxi (Finset.mem_insert_self w S) hloc B hB
  have hIneB : Ine (F := ℚ) B ≤ NS (F := ℚ) Ω (S : Set Pl) := htc_Ine_le_NS (by exact_mod_cast hwS) hB
  have hlocw := GlobalTheory.T.local_height_frobenius_place l Ω c n W y z d u P ψ w B τ hn hWc hO hdet2 hB hdiv hFrob hτD hdtτ (hW.unr w hwS B hB)
    hψlc (hIne1 B hB) hPO hy hz hyO hzO (fun a ha => ⟨hNSy a (hIneB ha), hNSz a (hIneB ha)⟩) huc huO
    (fun s a ha => huS s a (by rw [htc_ker_toGS]; exact hIneB ha)) hcup hdc hdO hdrel hCobw
  have hFτ : Cg n (F τ) 0 := congruence_mul_of_unit_factor hlocw (hPfrob B τ hB hFrob) hun
    (htc_norm_le_one c _ (htc_ht_mem c W y z u hO hyO hzO huO τ))
  have hFσ := hU₁ _ (Subgroup.mem_inf.1 hστ).1
  simp only [mul_inv_cancel_left] at hFσ
  show ‖F σ - 0‖ ≤ _
  unfold Cg at hFτ
  rw [sub_zero] at hFτ ⊢
  have e : F σ = F τ + -(F τ - F σ) := by ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hFτ ?_)
  rw [norm_neg]
  exact hFσ.le

end GlobalTheory.Ord2
