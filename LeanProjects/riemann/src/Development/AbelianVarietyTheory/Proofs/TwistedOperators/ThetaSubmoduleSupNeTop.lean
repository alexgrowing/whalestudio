import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSubmoduleChainBoundedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.ThetaGLSub
open scoped TensorProduct

namespace GlobalTheory.ThetaGLSub.SumProper

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n m : ℕ}

variable (k n m) in

def rhoS : Representation ℂ (GL (Fin m) k) (SB (Matrix (Fin n) (Fin m) k)) where
  toFun g :=
    { toFun := fun Φ => ⟨om 1 g (1 : GL (Fin n) k) Φ, Model.om_mem_SB 1 g 1 Φ.2⟩
      map_add' := fun Φ Ψ => Subtype.ext (by exact om_add 1 g 1 (Φ : Matrix (Fin n) (Fin m) k → ℂ) Ψ)
      map_smul' := fun c Φ => Subtype.ext (by exact om_smul 1 g 1 c (Φ : Matrix (Fin n) (Fin m) k → ℂ)) }
  map_one' := LinearMap.ext fun Φ => Subtype.ext (Model.om_one 1 Φ.1)
  map_mul' a b := LinearMap.ext fun Φ => Subtype.ext (by
    have := Model.om_mul (1 : kˣ →* ℂˣ) a b (1 : GL (Fin n) k) 1 Φ.1
    rw [mul_one] at this
    exact this)

@[simp] theorem rhoS_apply (g : GL (Fin m) k) (Φ : SB (Matrix (Fin n) (Fin m) k)) :
    ((rhoS k n m g Φ : SB (Matrix (Fin n) (Fin m) k)) : Matrix (Fin n) (Fin m) k → ℂ) =
      om 1 g (1 : GL (Fin n) k) Φ := rfl

def res (M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)) : Submodule ℂ (SB (Matrix (Fin n) (Fin m) k)) :=
  M.comap (SB _).subtype

theorem mem_res {M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)} {Φ : SB (Matrix (Fin n) (Fin m) k)} :
    Φ ∈ res M ↔ (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∈ M := Iff.rfl

def rhoQ (M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ))
    (hM : ∀ g : GL (Fin m) k, ∀ Φ ∈ M, om 1 g (1 : GL (Fin n) k) Φ ∈ M) :
    Representation ℂ (GL (Fin m) k) (SB (Matrix (Fin n) (Fin m) k) ⧸ res M) where
  toFun g := (res M).mapQ (res M) (rhoS k n m g) (fun Φ hΦ => hM g Φ hΦ)
  map_one' := by
    apply Submodule.linearMap_qext
    ext Φ
    simp
  map_mul' a b := by
    apply Submodule.linearMap_qext
    ext Φ
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, map_mul, Module.End.mul_apply]
    rfl

theorem rhoQ_mk (M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ))
    (hM : ∀ g : GL (Fin m) k, ∀ Φ ∈ M, om 1 g (1 : GL (Fin n) k) Φ ∈ M) (g : GL (Fin m) k)
    (Φ : SB (Matrix (Fin n) (Fin m) k)) :
    rhoQ M hM g ((res M).mkQ Φ) = (res M).mkQ (rhoS k n m g Φ) := rfl

variable {χ : GL (Fin n) k →* ℂˣ}

theorem mk_om {M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)} (hM : IsSub χ M) (g : GL (Fin m) k)
    (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin m) k))
    (hΦ : (Φ' : Matrix (Fin n) (Fin m) k → ℂ) = om 1 g h Φ) :
    (res M).mkQ Φ' = (χ h : ℂ) • rhoQ M hM.2.2 g ((res M).mkQ Φ) := by
  rw [rhoQ_mk, ← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, mem_res]
  have e1 : om 1 g h (Φ : Matrix (Fin n) (Fin m) k → ℂ) =
      om 1 (1 : GL (Fin m) k) h (om 1 g (1 : GL (Fin n) k) Φ) := by
    have := Model.om_mul (1 : kˣ →* ℂˣ) (1 : GL (Fin m) k) g h 1 (Φ : Matrix (Fin n) (Fin m) k → ℂ)
    rwa [one_mul, mul_one] at this
  have hmem : om 1 (1 : GL (Fin m) k) h (om 1 g (1 : GL (Fin n) k) Φ) -
      (χ h : ℂ) • om 1 g (1 : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∈ aug m χ :=
    Submodule.subset_span ⟨h, _, Model.om_mem_SB 1 g 1 Φ.2, rfl⟩
  have := hM.1 hmem
  simpa [hΦ, e1] using this

theorem isSmooth_rhoQ (M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ))
    (hM : ∀ g : GL (Fin m) k, ∀ Φ ∈ M, om 1 g (1 : GL (Fin n) k) Φ ∈ M) : IsSmooth (rhoQ M hM) := by
  refine isSmooth_of_nhds fun v => ?_
  obtain ⟨Φ, rfl⟩ := Submodule.mkQ_surjective (res M) v
  have h1 : IsOpen ((1 : kˣ →* ℂˣ).ker : Set kˣ) := by simp
  have hO := (om_isSmoothRepresentation k (Fin m) (Fin n) 1 h1).2.2.2.2 Φ.1 Φ.2
  have hU : IsOpen {g : GL (Fin m) k | om 1 g (1 : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin m) k → ℂ) = Φ} :=
    hO.preimage (continuous_id.prodMk continuous_const)
  refine Filter.mem_of_superset (hU.mem_nhds (Model.om_one 1 _)) fun g hg => ?_
  show rhoQ M hM g ((res M).mkQ Φ) = (res M).mkQ Φ
  rw [rhoQ_mk]
  congr 1
  exact Subtype.ext hg

theorem isIrreducible_rhoQ {M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)} (hM : IsSub χ M)
    (hne : M ≠ SB _) (hmax : ∀ Q, IsSub χ Q → M ≤ Q → Q = M ∨ Q = SB _) :
    (rhoQ M hM.2.2).IsIrreducible := by
  have key : ∀ U : Subrepresentation (rhoQ M hM.2.2),
      IsSub χ ((U.toSubmodule.comap (res M).mkQ).map (SB _).subtype) ∧
        M ≤ (U.toSubmodule.comap (res M).mkQ).map (SB _).subtype := by
    intro U
    have hin : ∀ Φ ∈ M, Φ ∈ (U.toSubmodule.comap (res M).mkQ).map (SB _).subtype := by
      intro Φ hΦ
      refine ⟨⟨Φ, hM.2.1 hΦ⟩, ?_, rfl⟩
      have h0 : (res M).mkQ ⟨Φ, hM.2.1 hΦ⟩ = 0 := (Submodule.Quotient.mk_eq_zero (res M)).2 hΦ
      change (res M).mkQ _ ∈ U.toSubmodule
      rw [h0]; exact U.toSubmodule.zero_mem
    refine ⟨⟨fun z hz => hin z (hM.1 hz), Submodule.map_subtype_le _ _, ?_⟩, hin⟩
    rintro g _ ⟨Ψ, hΨ, rfl⟩
    refine ⟨rhoS k n m g Ψ, ?_, rfl⟩
    change (res M).mkQ Ψ ∈ U.toSubmodule at hΨ
    change (res M).mkQ (rhoS k n m g Ψ) ∈ U.toSubmodule
    rw [← rhoQ_mk M hM.2.2]
    exact U.apply_mem_toSubmodule g hΨ
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => hne ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
  · refine le_antisymm hM.2.1 fun Φ hΦ => ?_
    have h1 : (res M).mkQ ⟨Φ, hΦ⟩ ∈ (⊤ : Subrepresentation (rhoQ M hM.2.2)) := trivial
    rw [← h] at h1
    have h2 : (res M).mkQ ⟨Φ, hΦ⟩ = 0 := h1
    exact (Submodule.Quotient.mk_eq_zero (res M)).1 h2
  · obtain ⟨hQ, hMQ⟩ := key U
    rcases hmax _ hQ hMQ with h | h
    · left
      refine SetLike.ext fun v => ⟨fun hv => ?_, fun hv => ?_⟩
      · obtain ⟨Φ, rfl⟩ := Submodule.mkQ_surjective (res M) v
        have h3 : (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∈ (U.toSubmodule.comap (res M).mkQ).map (SB _).subtype :=
          ⟨Φ, hv, rfl⟩
        rw [h] at h3
        show (res M).mkQ Φ = 0
        exact (Submodule.Quotient.mk_eq_zero (res M)).2 h3
      · have h4 : v = 0 := hv
        rw [h4]
        exact U.toSubmodule.zero_mem
    · right
      refine SetLike.ext fun v => ⟨fun _ => trivial, fun _ => ?_⟩
      obtain ⟨Φ, rfl⟩ := Submodule.mkQ_surjective (res M) v
      have h3 : (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∈ (U.toSubmodule.comap (res M).mkQ).map (SB _).subtype := by
        rw [h]; exact Φ.2
      obtain ⟨Ψ, hΨ, hΨΦ⟩ := h3
      have : Ψ = Φ := Subtype.ext hΨΦ
      rw [← this]
      exact hΨ

def tmap (M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (e : (SB (Matrix (Fin n) (Fin m) k) ⧸ res M) →ₗ[ℂ] V) : SB (Matrix (Fin n) (Fin m) k) →ₗ[ℂ] V ⊗[ℂ] ℂ :=
  (TensorProduct.mk ℂ V ℂ).flip 1 ∘ₗ e ∘ₗ (res M).mkQ

theorem tmap_apply (M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (e : (SB (Matrix (Fin n) (Fin m) k) ⧸ res M) →ₗ[ℂ] V) (Φ : SB (Matrix (Fin n) (Fin m) k)) :
    tmap M e Φ = e ((res M).mkQ Φ) ⊗ₜ[ℂ] (1 : ℂ) := rfl

theorem tmap_eq_zero_iff (M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)) {V : Type} [AddCommGroup V]
    [Module ℂ V] (e : (SB (Matrix (Fin n) (Fin m) k) ⧸ res M) →ₗ[ℂ] V) (he : Function.Injective e)
    (Φ : SB (Matrix (Fin n) (Fin m) k)) : tmap M e Φ = 0 ↔ (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∈ M := by
  rw [tmap_apply]
  constructor
  · intro h
    have h1 := congrArg (TensorProduct.rid ℂ V) h
    rw [TensorProduct.rid_tmul, one_smul, map_zero] at h1
    have h2 : (res M).mkQ Φ = 0 := he (h1.trans (map_zero e).symm)
    exact (Submodule.Quotient.mk_eq_zero (res M)).1 h2
  · intro h
    have h2 : (res M).mkQ Φ = 0 := (Submodule.Quotient.mk_eq_zero (res M)).2 h
    rw [h2, map_zero, TensorProduct.zero_tmul]

theorem tmap_equivariant {M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)} (hM : IsSub χ M) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π' : Representation ℂ (GL (Fin m) k) V)
    (e : (SB (Matrix (Fin n) (Fin m) k) ⧸ res M) →ₗ[ℂ] V)
    (he : ∀ g x, e (rhoQ M hM.2.2 g x) = π' g (e x)) (g : GL (Fin m) k) (h : GL (Fin n) k)
    (Φ Φ' : SB (Matrix (Fin n) (Fin m) k)) (hΦ : (Φ' : Matrix (Fin n) (Fin m) k → ℂ) = om 1 g h Φ) :
    tmap M e Φ' = TensorProduct.map (π' g) (ofChar χ h) (tmap M e Φ) := by
  rw [tmap_apply, tmap_apply, mk_om hM g h Φ Φ' hΦ, map_smul, he, TensorProduct.map_tmul, ofChar_apply,
    TensorProduct.smul_tmul, smul_eq_mul]

theorem exists_max {L : ℕ} (hL : ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, IsSub χ (N i)) → r ≤ L)
    {N : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)} (hN : IsSub χ N) (hne : N ≠ SB _) :
    ∃ M, IsSub χ M ∧ M ≠ SB _ ∧ N ≤ M ∧ ∀ Q, IsSub χ Q → M ≤ Q → Q = M ∨ Q = SB _ := by
  by_contra H
  push_neg at H
  let T := {M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ) // IsSub χ M ∧ M ≠ SB _ ∧ N ≤ M}
  have hstep : ∀ M : T, ∃ Q : T, M.1 < Q.1 := by
    intro M
    obtain ⟨Q, hQ, hMQ, h1, h2⟩ := H M.1 M.2.1 M.2.2.1 M.2.2.2
    exact ⟨⟨Q, hQ, h2, M.2.2.2.trans hMQ⟩, lt_of_le_of_ne hMQ (Ne.symm h1)⟩
  choose step hstep using hstep
  let seq : ℕ → T := fun i => step^[i] ⟨N, hN, hne, le_rfl⟩
  have hmono : StrictMono fun i => (seq i).1 := strictMono_nat_of_lt_succ fun i => by
    simp only [seq, Function.iterate_succ_apply']
    exact hstep _
  have := hL (L + 1) (fun i => (seq i).1) (hmono.comp Fin.val_strictMono) (fun i => (seq i).2.1)
  omega

end GlobalTheory.ThetaGLSub.SumProper

namespace GlobalTheory.ThetaGLSub.SumProper

theorem main : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.MinguezThetaGL → ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n m : ℕ), 1 ≤ n → 1 ≤ m →
    ∀ χ : GL (Fin n) k →* ℂˣ, IsOpen {g | χ g = 1} →
    ∀ N N' : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ), GlobalTheory.ThetaGLSub.IsSub χ N → GlobalTheory.ThetaGLSub.IsSub χ N' →
      N ≠ GlobalTheory.SplitWeil.SB _ → N' ≠ GlobalTheory.SplitWeil.SB _ → N ⊔ N' ≠ GlobalTheory.SplitWeil.SB _ := by
  intro hP hMin k _ _ _ _ n m hn hm χ hχ N N' hN hN' hne hne' hsup
  obtain ⟨L, hL⟩ := GlobalTheory.T.theta_submodule_chain_bounded hP k n m χ hχ
  obtain ⟨M, hM, hMne, hNM, hMmax⟩ := exists_max hL hN hne
  obtain ⟨M', hM', hM'ne, hNM', hM'max⟩ := exists_max hL hN' hne'
  have hout : ∀ {M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)}, IsSub χ M → M ≠ SB _ →
      ∃ Φ : SB (Matrix (Fin n) (Fin m) k), (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∉ M := by
    intro M hM hMne
    by_contra H
    push_neg at H
    exact hMne (le_antisymm hM.2.1 fun φ hφ => H ⟨φ, hφ⟩)
  have hsm : IsSmooth (ofChar χ) := (isSmooth_ofChar_iff χ).2 hχ
  obtain ⟨Φ₀, hΦ₀⟩ := hout hM hMne
  obtain ⟨Φ₁, hΦ₁⟩ := hout hM' hM'ne
  have hx : (res M).mkQ Φ₀ ≠ 0 := fun h => hΦ₀ ((Submodule.Quotient.mk_eq_zero (res M)).1 h)
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero ℂ hx
  have hyp : ∃ f : SB (Matrix (Fin n) (Fin m) k) →ₗ[ℂ] ℂ, f ≠ 0 ∧
      ∀ (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin m) k)),
        (Φ' : Matrix (Fin n) (Fin m) k → ℂ) = om 1 (1 : GL (Fin m) k) h Φ → f Φ' = ofChar χ h (f Φ) := by
    refine ⟨ℓ ∘ₗ (res M).mkQ, fun h0 => hℓ (LinearMap.congr_fun h0 Φ₀), fun h Φ Φ' hΦ => ?_⟩
    simp only [LinearMap.comp_apply, ofChar_apply]
    rw [mk_om hM 1 h Φ Φ' hΦ, map_one, Module.End.one_apply, map_smul, smul_eq_mul]
  obtain ⟨V₀, _, _, π', -, -, -, hU, hprop⟩ := hMin k n m hn hm ℂ (ofChar χ) hsm (isIrreducible_ofChar χ) hyp
  have omq : ∀ {M : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)} (hM : IsSub χ M), M ≠ SB _ →
      OmQuot 1 (rhoQ M hM.2.2) (ofChar χ) := by
    intro M hM hMne
    obtain ⟨Φ, hΦ⟩ := hout hM hMne
    refine ⟨tmap M LinearMap.id, fun h0 => hΦ ((tmap_eq_zero_iff M LinearMap.id Function.injective_id Φ).1
      (LinearMap.congr_fun h0 Φ)), tmap_equivariant hM (rhoQ M hM.2.2) LinearMap.id (fun _ _ => rfl)⟩
  obtain ⟨e⟩ := hU _ (rhoQ M hM.2.2) (isSmooth_rhoQ M hM.2.2) (isIrreducible_rhoQ hM hMne hMmax) (omq hM hMne)
  obtain ⟨e'⟩ := hU _ (rhoQ M' hM'.2.2) (isSmooth_rhoQ M' hM'.2.2) (isIrreducible_rhoQ hM' hM'ne hM'max)
    (omq hM' hM'ne)
  let F := tmap M e.toIntertwiningMap.toLinearMap
  let F' := tmap M' e'.toIntertwiningMap.toLinearMap
  have hF0 : ∀ Φ, F Φ = 0 ↔ (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∈ M :=
    tmap_eq_zero_iff M _ (fun a b h => e.toLinearEquiv.injective h)
  have hF0' : ∀ Φ, F' Φ = 0 ↔ (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∈ M' :=
    tmap_eq_zero_iff M' _ (fun a b h => e'.toLinearEquiv.injective h)
  have hFe := tmap_equivariant hM π' e.toIntertwiningMap.toLinearMap
    (fun g x => LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) x)
  have hFe' := tmap_equivariant hM' π' e'.toIntertwiningMap.toLinearMap
    (fun g x => LinearMap.congr_fun (e'.toIntertwiningMap.isIntertwining' g) x)
  have hFne : F ≠ 0 := fun h0 => hΦ₀ ((hF0 Φ₀).1 (LinearMap.congr_fun h0 Φ₀))
  obtain ⟨c, hc⟩ := hprop F F' (by rintro X (rfl | rfl); exacts [hFe, hFe']) hFne
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hΦ₁ ((hF0' Φ₁).1 (LinearMap.congr_fun hc Φ₁))
  have hker : ∀ Φ : SB (Matrix (Fin n) (Fin m) k),
      (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∈ M ↔ (Φ : Matrix (Fin n) (Fin m) k → ℂ) ∈ M' := by
    intro Φ
    rw [← hF0, ← hF0', hc, LinearMap.smul_apply, smul_eq_zero, or_iff_right hc0]
  have hMM' : M' ≤ M := fun φ hφ => (hker ⟨φ, hM'.2.1 hφ⟩).2 hφ
  apply hMne
  refine le_antisymm hM.2.1 ?_
  rw [← hsup]
  exact sup_le hNM (hNM'.trans hMM')

end GlobalTheory.ThetaGLSub.SumProper
