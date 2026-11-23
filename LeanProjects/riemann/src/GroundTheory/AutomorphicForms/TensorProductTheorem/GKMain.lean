import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.GKTensor

noncomputable section

universe u

namespace GroundTheory.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

open Set Module RestrictedTensor CompactRep TensorProduct

open scoped TensorProduct

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} {h : IsExpLieAlgebra G 𝔤} {K : Subgroup G}
  [CompactSpace K]

def IsExpLieAlgebra.GKModule.IsKAdmissible {W : Type*} [AddCommGroup W] [Module ℂ W]
    (M : h.GKModule K W) : Prop :=
  ∀ (c : Submodule (MonoidAlgebra ℂ K) M.σ.asModule)
    (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) M.σ.asModule),
    FiniteDimensional ℂ (LinearMap.range (kProj M.isKFinite hc))

namespace GKTensor

section Smooth

variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
  [T2Space L] [TotallyDisconnectedSpace L] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {τ : Representation ℂ L V}

theorem isSmooth_mGenSubrep (hτ : IsSmooth τ) (N : Submodule ℂ V) :
    IsSmooth (mGenSubrep τ N).toRepresentation := by
  intro u
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf τ (u : V)) (fun g hg => ?_) (hτ u)
  exact Subtype.ext hg

theorem isSmooth_mGenQuotRep (hτ : IsSmooth τ) (e : End ℂ V) (N : Submodule ℂ V) :
    IsSmooth (mGenQuotRep τ e N) := by
  intro q
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf (mGenSubrep τ N).toRepresentation u)
    (fun g hg => ?_) (isSmooth_mGenSubrep hτ N u)
  show mGenQuotRep τ e N g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u
  rw [mGenQuotRep_mk, hg]

def mGenQuotMap (e : End ℂ V) (N : Submodule ℂ V) :
    Representation.IntertwiningMap (mGenSubrep τ N).toRepresentation (mGenQuotRep τ e N) where
  toLinearMap := (mGenKernel τ e N).mkQ
  isIntertwining' g := LinearMap.ext fun _ => rfl

end Smooth

variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
  [T2Space L] [TotallyDisconnectedSpace L] {V : Type u} [AddCommGroup V] [Module ℂ V]

namespace GKLModule

variable (Mx : GKLModule h K L V)

structure Decomposition where

  W₁ : Type u

  W₂ : Type u
  [instAddCommGroup₁ : AddCommGroup W₁]
  [instModule₁ : Module ℂ W₁]
  [instAddCommGroup₂ : AddCommGroup W₂]
  [instModule₂ : Module ℂ W₂]

  π₁ : h.GKModule K W₁

  π₂ : Representation ℂ L W₂
  isIrreducible₁ : π₁.IsIrreducible
  isKAdmissible₁ : π₁.IsKAdmissible
  isIrreducible₂ : π₂.IsIrreducible
  isAdmissible₂ : GroundTheory.Automorphic.IsAdmissible π₂

  equiv : Mx.fullRep.Equiv (outerTensor π₁.rep π₂)

attribute [instance] Decomposition.instAddCommGroup₁ Decomposition.instModule₁
  Decomposition.instAddCommGroup₂ Decomposition.instModule₂

set_option maxHeartbeats 4000000 in

theorem nonempty_decomposition (hirr : Mx.IsIrreducible) (hadm : Mx.IsAdmissible) :
    Nonempty (Mx.Decomposition) := by
  classical
  obtain ⟨H, hHc, hHo, c, hc, N₁, N₂, hN₁H, hN₂H, hN₂c, hN₁0, hN₂0, -, hπ₁, hπ₂, hequiv⟩ :=
    Mx.exists_equiv_outerTensor_gkl hirr hadm
  have hτ := hadm.1
  have hσK := Mx.gk.isKFinite
  set e₁ := kProj hσK hc
  set e₂ := fixedEnd hτ hHc hHo
  set U₁ := mGenSubrep Mx.gk.rep N₁
  set π₁ := Mx.gk.subQuot U₁ (mGenKernel Mx.gk.rep e₁ N₁) (mGenKernel_le_comap Mx.gk.rep e₁ N₁)
  have hπ₁rep : π₁.rep = mGenQuotRep Mx.gk.rep e₁ N₁ := Mx.gk.subQuot_rep _ _ _
  set π₂ := mGenQuotRep Mx.τ e₂ N₂
  set U₂ := mGenSubrep Mx.τ N₂
  have hπ₂s : IsSmooth π₂ := isSmooth_mGenQuotRep hτ e₂ N₂

  have hU₂c : ∀ u ∈ U₂.toSubmodule, kProj hσK hc u = u := by
    let Y : Subrepresentation Mx.τ :=
      ⟨LinearMap.range (kProj hσK hc), fun g v hv => by
        obtain ⟨w, rfl⟩ := hv
        exact ⟨Mx.τ g w, kProj_comm hσK hc (fun k => (Mx.comm_σ k g).symm) w⟩⟩
    intro u hu
    obtain ⟨w, hw⟩ := mGenSubrep_le Mx.τ (X := Y) hN₂c hu
    rw [← hw, kProj_kProj]

  have hπ₂adm : GroundTheory.Automorphic.IsAdmissible π₂ := by
    refine ⟨hπ₂s, fun H' hH'c hH'o => ?_⟩
    have hfin := hadm.2 H' hH'c hH'o c hc
    have hU₂fin : FiniteDimensional ℂ (fixedVectors U₂.toRepresentation H') := by
      let f : fixedVectors U₂.toRepresentation H' →ₗ[ℂ]
          LinearMap.range (kProj hσK hc ∘ₗ (fixedVectors Mx.τ H').subtype) :=
        LinearMap.codRestrict _ (U₂.toSubmodule.subtype ∘ₗ Submodule.subtype _) fun u => by
          have hu : ((u : U₂.toSubmodule) : V) ∈ fixedVectors Mx.τ H' := fun g hg =>
            congrArg Subtype.val (u.2 g hg)
          exact ⟨⟨_, hu⟩, hU₂c _ (u : U₂.toSubmodule).2⟩
      exact Module.Finite.of_injective f fun a b hab => by
        have := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext this)
    have hsurj := fixedMap_surjective (isSmooth_mGenSubrep hτ N₂) hπ₂s hH'c hH'o
      (f := mGenQuotMap e₂ N₂) (Submodule.mkQ_surjective _)
    exact Module.Finite.of_surjective _ hsurj

  have he₂ : IsWinProj Mx.τ e₂ := isWinProj_fixedEnd hτ hHc hHo
  have hN₂e : N₂ ≤ LinearMap.range e₂ := fun x hx =>
    ⟨x, fixedEnd_apply_of_mem hτ hHc hHo (hN₂H hx)⟩
  obtain ⟨n₂, hn₂, hn₂0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN₂0
  set w := mGenQuotMk Mx.τ e₂ N₂ ⟨n₂, hn₂⟩
  have hw0 : w ≠ 0 := by
    intro h0
    have := mGenQuotMk_injective he₂ hN₂e (a₁ := ⟨n₂, hn₂⟩) (a₂ := 0) (by rw [map_zero]; exact h0)
    exact hn₂0 (congrArg Subtype.val this)
  have hwH : w ∈ fixedVectors π₂ H := by
    intro g hg
    show mGenQuotRep Mx.τ e₂ N₂ g (Submodule.Quotient.mk _) = Submodule.Quotient.mk _
    rw [mGenQuotRep_mk]
    congr 1
    exact Subtype.ext (hN₂H hn₂ g hg)

  have hschur : ∀ T : End ℂ ((mGenSubrep Mx.τ N₂).toSubmodule ⧸ mGenKernel Mx.τ e₂ N₂),
      (∀ b, T * π₂ b = π₂ b * T) → ∃ c : ℂ, T = c • 1 := by
    intro T hT
    haveI := hπ₂
    have hwin := isWinProj_fixedEnd hπ₂s hHc hHo
    have hfinH : FiniteDimensional ℂ (LinearMap.range (fixedEnd hπ₂s hHc hHo)) := by
      rw [range_fixedEnd]
      exact hπ₂adm.2 H hHc hHo
    have hneH : LinearMap.range (fixedEnd hπ₂s hHc hHo) ≠ ⊥ := by
      rw [range_fixedEnd]
      intro hb
      have : w ∈ (⊥ : Submodule ℂ _) := hb ▸ hwH
      exact hw0 ((Submodule.mem_bot ℂ).1 this)
    exact exists_eq_smul_of_commute hwin hneH hT (LinearMap.ext fun v =>
      (fixedEnd_comm hπ₂s hHc hHo hT v).symm)
  obtain ⟨Φ⟩ := hequiv hschur

  have hπ₁adm : π₁.IsKAdmissible := by
    intro c₁ hc₁

    let j : (U₁.toSubmodule ⧸ mGenKernel Mx.gk.rep e₁ N₁) →ₗ[ℂ] V :=
      Φ.symm.toLinearEquiv.toLinearMap ∘ₗ (TensorProduct.mk ℂ _ _).flip w
    have hj : Function.Injective j := fun a b hab => by
      have := Φ.symm.toLinearEquiv.injective hab
      have h2 : (a - b) ⊗ₜ[ℂ] w = 0 := by
        rw [TensorProduct.sub_tmul]
        exact sub_eq_zero.2 this
      by_contra hne
      exact tmul_ne_zero_of (sub_ne_zero.2 hne) hw0 h2
    have hΦs : ∀ p z, Φ.symm (outerTensor (mGenQuotRep Mx.gk.rep e₁ N₁) π₂ p z) =
        Mx.fullRep p (Φ.symm z) := fun p z =>
      Representation.IntertwiningMap.isIntertwining _ _ Φ.symm.toIntertwiningMap p z
    have hjσ : ∀ k x, j (π₁.σ k x) = Mx.gk.σ k (j x) := fun k x => by
      show Φ.symm (π₁.σ k x ⊗ₜ w) = Mx.gk.σ k (Φ.symm (x ⊗ₜ w))
      have : π₁.σ k x ⊗ₜ[ℂ] w =
          outerTensor (mGenQuotRep Mx.gk.rep e₁ N₁) π₂ (FreeMonoid.of (Sum.inr k), 1) (x ⊗ₜ w) := by
        rw [outerTensor_tmul, map_one, Module.End.one_apply]
        rfl
      rw [this, hΦs]
      show Mx.gk.rep (FreeMonoid.of (Sum.inr k)) (Mx.τ 1 _) = _
      rw [map_one, Module.End.one_apply]
      rfl
    have hjH : ∀ x, j x ∈ fixedVectors Mx.τ H := fun x g hg => by
      show Mx.τ g (Φ.symm (x ⊗ₜ w)) = Φ.symm (x ⊗ₜ w)
      have : x ⊗ₜ[ℂ] w = outerTensor (mGenQuotRep Mx.gk.rep e₁ N₁) π₂ (1, g) (x ⊗ₜ w) := by
        rw [outerTensor_tmul, map_one, Module.End.one_apply, hwH g hg]
      conv_rhs => rw [this, hΦs]
      show _ = Mx.gk.rep 1 (Mx.τ g _)
      rw [map_one, Module.End.one_apply]

    let jK : Representation.IntertwiningMap π₁.σ Mx.gk.σ :=
      ⟨j, fun k => LinearMap.ext fun x => hjσ k x⟩
    let jR := Representation.IntertwiningMap.equivLinearMapAsModule π₁.σ Mx.gk.σ jK
    obtain ⟨S, hS, rfl⟩ := hc₁

    have hjR : Function.Injective jR := hj
    let m := S.map jR
    let eS : S ≃ₗ[MonoidAlgebra ℂ K] m := Submodule.equivMapOfInjective jR hjR S
    have hm : IsSimpleModule (MonoidAlgebra ℂ K) m := by
      rw [isSimpleModule_iff_isAtom] at hS ⊢
      refine ⟨fun hb => hS.1 ?_, fun N hN => ?_⟩
      · apply Submodule.map_injective_of_injective hjR
        rw [Submodule.map_bot]
        exact hb
      · have hle : N.comap jR < S := by
          have h1 : N.comap jR ≤ S := by
            intro x hx
            obtain ⟨y, hy, hyx⟩ := hN.le hx
            rw [← hjR hyx]
            exact hy
          refine lt_of_le_of_ne h1 fun heq => hN.ne ?_
          refine le_antisymm hN.le ?_
          show S.map jR ≤ N
          rw [← heq]
          exact Submodule.map_comap_le _ _
        have := hS.2 _ hle
        refine le_antisymm (fun x hx => ?_) bot_le
        obtain ⟨y, hy, rfl⟩ := hN.le hx
        have hy' : y ∈ N.comap jR := hx
        rw [this, Submodule.mem_bot] at hy'
        rw [hy', map_zero]
        exact Submodule.zero_mem _
    set c' := isotypicComponent (MonoidAlgebra ℂ K) Mx.gk.σ.asModule m
    have hc' : c' ∈ isotypicComponents (MonoidAlgebra ℂ K) Mx.gk.σ.asModule := ⟨m, hm, rfl⟩
    have hle := LinearMap.le_comap_isotypicComponent (S := S) jR
    rw [eS.isotypicComponent_eq (M := Mx.gk.σ.asModule)] at hle
    have hfin := hadm.2 H hHc hHo c' hc'
    let f : LinearMap.range (kProj π₁.isKFinite ⟨S, hS, rfl⟩) →ₗ[ℂ]
        LinearMap.range (kProj hσK hc' ∘ₗ (fixedVectors Mx.τ H).subtype) :=
      LinearMap.codRestrict _ (j ∘ₗ Submodule.subtype _) fun x => by
        have hxself : kProj π₁.isKFinite ⟨S, hS, rfl⟩ x.1 = x.1 := by
          obtain ⟨y, hy⟩ := x.2
          rw [← hy]
          exact kProj_kProj _ _ y
        have hx := (kProj_apply_eq_self_iff π₁.isKFinite ⟨S, hS, rfl⟩).1 hxself
        have h1 : j x ∈ c' := hle hx
        exact ⟨⟨j x, hjH x⟩, (kProj_apply_eq_self_iff hσK hc').2 h1⟩
    exact Module.Finite.of_injective f fun a b hab =>
      Subtype.ext (hj (congrArg Subtype.val hab))
  have hirr₁ : π₁.IsIrreducible := by
    show π₁.rep.IsIrreducible
    rw [hπ₁rep]
    exact hπ₁
  have Φ' : Mx.fullRep.Equiv (outerTensor π₁.rep π₂) := by
    rw [hπ₁rep]
    exact Φ
  exact ⟨{
    W₁ := _
    W₂ := _
    π₁ := π₁
    π₂ := π₂
    isIrreducible₁ := hirr₁
    isKAdmissible₁ := hπ₁adm
    isIrreducible₂ := hπ₂
    isAdmissible₂ := hπ₂adm
    equiv := Φ' }⟩

namespace Decomposition

variable {Mx}

theorem nonempty_equiv_arch (D D' : Mx.Decomposition) : Nonempty (D.π₁.rep.Equiv D'.π₁.rep) :=
  nonempty_equiv_fst_of_equiv D.isIrreducible₁ D.isIrreducible₂ D'.isIrreducible₁
    (D.equiv.symm.trans D'.equiv)

theorem nonempty_equiv_fin (D D' : Mx.Decomposition) : Nonempty (D.π₂.Equiv D'.π₂) :=
  nonempty_equiv_snd_of_equiv D.isIrreducible₁ D.isIrreducible₂ D'.isIrreducible₂
    (D.equiv.symm.trans D'.equiv)

end Decomposition

end GKLModule

end GKTensor

end GroundTheory.Automorphic
