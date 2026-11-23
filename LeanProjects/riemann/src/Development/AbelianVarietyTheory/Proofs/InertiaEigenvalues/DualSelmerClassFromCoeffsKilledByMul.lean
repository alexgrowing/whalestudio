import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BkOnLeMapOfSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairingEquivariantStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.DualSub

section Cup

variable {Γ A M M' : Type} [Group Γ] [TopologicalSpace Γ] [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup M']
  [Module A M'] [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace M'] [DiscreteTopology M'] {n : ℕ}
  (χ : Γ → ZMod n) (π : Representation A Γ M) (π' : Representation A Γ M') (P : M →+ M' →+ ZMod n)

omit [TopologicalSpace M] [DiscreteTopology M] in

theorem cupB_left (hP : ∀ g x y, P (π g x) (π' g y) = χ g * P x y) (x x' : Γ → M) (y : Γ → M') (w : M)
    (hy : Continuous y) (hy' : ∀ g h, y (g * h) = y g + π' g (y h)) (hx : ∀ g, x' g = x g + (π g w - w))
    (h : CupB χ (fun g m => π' g m) P x y) : CupB χ (fun g m => π' g m) P x' y := by
  obtain ⟨F, hF, h⟩ := h
  refine ⟨F + fun g => P w (y g), hF.add (((IsLocallyConstant.iff_continuous y).2 hy).comp fun m => P w m), fun g k => ?_⟩
  have h1 := h g k
  simp only [hx, map_add, map_sub, AddMonoidHom.add_apply, AddMonoidHom.sub_apply, Pi.add_apply, hy', hP] at h1 ⊢
  linear_combination h1

theorem cupB_right (hP : ∀ g x y, P (π g x) (π' g y) = χ g * P x y) (x : Γ → M) (y y' : Γ → M') (m : M')
    (hx : Continuous x) (hx' : ∀ g h, x (g * h) = x g + π g (x h)) (hm : Continuous fun g => π' g m)
    (hy : ∀ g, y' g = y g - (π' g m - m))
    (h : CupB χ (fun g m => π' g m) P x y) : CupB χ (fun g m => π' g m) P x y' := by
  obtain ⟨F, hF, h⟩ := h
  refine ⟨F + fun g => P (x g) (π' g m), hF.add (((IsLocallyConstant.iff_continuous _).2 (hx.prodMk hm)).comp
    fun p : M × M' => P p.1 p.2), fun g k => ?_⟩
  have h1 := h g k
  have h2 := hP g (x k) (π' k m)
  simp only [hy, map_add, map_sub, AddMonoidHom.add_apply, Pi.add_apply, hx', map_mul, Module.End.mul_apply] at h1 ⊢
  linear_combination h1 + h2

end Cup

theorem exists_compLeft {A Y Y' : Type} [CommRing A] [AddCommGroup Y] [Module A Y] [AddCommGroup Y'] [Module A Y'] {r : ℕ}
    (e : Y →ₗ[A] Y') (m : Fin r → Y') (h : ∀ a, m a ∈ LinearMap.range e) : ∃ m', e.compLeft (Fin r) m' = m := by
  choose m' hm' using h
  exact ⟨m', funext hm'⟩

theorem dualSel_of_smul_cob : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → NoInvDual i κ ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y' : Type) [AddCommGroup Y'] [Module A Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (Y₂ : Type) [AddCommGroup Y₂] [Module A Y₂] [TopologicalSpace Y₂] [DiscreteTopology Y₂] (Y₂' : Type) [AddCommGroup Y₂'] [Module A Y₂'] [TopologicalSpace Y₂'] [DiscreteTopology Y₂'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))) (β₂ : Y₂ →+ Y₂' →+ ZMod (X.l i ^ (nu X i + 1))) (f : Y →ₗ[A] Y₂) (e : Y₂' →ₗ[A] Y') (c t : A), Bal A β → Bal A β₂ → Function.Surjective f → Function.Injective e → (∀ y', (c * t) • y' = 0 → y' ∈ LinearMap.range e) → (∀ y y', β₂ (f y) y' = β y (e y')) → (∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ Y' g m = m) → t • m = 0) → ∀ y : Z1 (repOn ρ κ⁻¹ Y'), DualSel bkP i s κ ρ β Q y → Cob (repOn ρ κ⁻¹ Y') (fun g => c • y.1 g) → ∃ y₂ : Z1 (repOn ρ κ⁻¹ Y₂'), DualSel bkP i s κ ρ β₂ Q y₂ ∧ Cob (repOn ρ κ⁻¹ Y') (fun g a => y.1 g a - e (y₂.1 g a)) := by
  intro D N X bkP i s A _ _ _ _ κ Q ρ hS hK hD hNI Y _ _ _ _ Y' _ _ _ _ Y₂ _ _ _ _ Y₂' _ _ _ _ β β₂ f e c t hβ hβ₂ hf he hct
    hfe ht y hy hc
  obtain ⟨hcY, hcY', hP, hU⟩ := GlobalTheory.T.pairing_equivariant_alt D N X bkP i s A κ Q ρ hS hK hD Y Y' β hβ
  obtain ⟨-, -, hP₂, -⟩ := GlobalTheory.T.pairing_equivariant_alt D N X bkP i s A κ Q ρ hS hK hD Y₂ Y₂' β₂ hβ₂
  obtain ⟨m, hm⟩ := hc
  have hE : Function.Injective (e.compLeft (Fin D.R.r)) := fun a b hab => funext fun j => he (congrFun hab j)

  have hq := hNI (Y' ⧸ LinearMap.range (c • (LinearMap.id : Y' →ₗ[A] Y')))
    ((Submodule.mkQ _).compLeft (Fin D.R.r) m) fun g => by
      rw [← repOn_map, ← sub_eq_zero, ← map_sub, ← hm g]
      funext a
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨y.1 g a, rfl⟩
  obtain ⟨m', hm'⟩ := exists_compLeft (c • (LinearMap.id : Y' →ₗ[A] Y')) m fun a =>
    (Submodule.Quotient.mk_eq_zero _).1 (congrFun hq a)
  have hm'' : m = c • m' := hm'.symm
  have hcm : Continuous fun g => repOn ρ κ⁻¹ Y' g m' := hcY'.comp (continuous_id.prodMk continuous_const)
  have hkill : ∀ g, c • (y.1 g - (repOn ρ κ⁻¹ Y' g m' - m')) = 0 := fun g => by
    have := hm g
    simp only at this
    rw [smul_sub, this, hm'', map_smul, smul_sub, sub_self]
  have hex : ∀ g, ∃ z, e.compLeft (Fin D.R.r) z = y.1 g - (repOn ρ κ⁻¹ Y' g m' - m') := fun g =>
    exists_compLeft e _ fun a => hct _ (by
      rw [mul_comm, mul_smul]
      have := congrFun (hkill g) a
      rw [Pi.smul_apply] at this
      rw [this, Pi.zero_apply, smul_zero])
  choose z hz using hex
  have hzc : Continuous z := by
    have h1 : IsLocallyConstant fun g => y.1 g - (repOn ρ κ⁻¹ Y' g m' - m') :=
      (IsLocallyConstant.iff_continuous _).2 (y.2.1.sub (hcm.sub continuous_const))
    exact (IsLocallyConstant.iff_continuous _).1 (IsLocallyConstant.desc z (e.compLeft (Fin D.R.r))
      (by rw [show (e.compLeft (Fin D.R.r)) ∘ z = _ from funext hz]; exact h1) hE)
  have hzz : ∀ g h, z (g * h) = z g + repOn ρ κ⁻¹ Y₂' g (z h) := fun g h => hE (by
    rw [map_add, repOn_map, hz, hz, hz, y.2.2, map_mul, Module.End.mul_apply, map_sub, map_sub]
    abel)
  refine ⟨⟨z, hzc, hzz⟩, ⟨fun v h1 h2 h3 τ hτ => hE ?_, fun v hv => ?_, fun v hv x₂ hx₂ => ?_⟩, m', fun g => ?_⟩
  · show e.compLeft _ (z τ) = _
    rw [hz, hy.1 v h1 h2 h3 τ hτ, (hU v h1 h2 h3 _ (N.plOm.2 v) τ hτ).2]
    simp
  · obtain ⟨m₀, hm₀⟩ := hy.2.1 v hv
    have h1 := ht v hv (c • (m₀ - m')) fun g hg => by
      have := hkill g
      rw [hm₀ g hg] at this
      rw [map_smul, map_sub, ← sub_eq_zero, ← smul_sub, ← this]
      congr 1
      abel
    obtain ⟨m₂, hm₂⟩ := exists_compLeft e (m₀ - m') fun a => hct _ (by
      rw [mul_comm, mul_smul]
      exact congrFun h1 a)
    refine ⟨m₂, fun g hg => hE ?_⟩
    show e.compLeft _ (z g) = _
    rw [hz, map_sub, repOn_map, hm₂, hm₀ g hg, map_sub]
    abel
  · obtain ⟨xc, hxc, hxe⟩ := GlobalTheory.T.bkOn_le_map_h1MapSubgroup_of_surjective D N X bkP i s A κ Q hS hK Y Y₂ f hf v hx₂
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ xc
    have h1 := hy.2.2 v hv x hxc
    have h2 := cupB_right _ ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype) ((repOn ρ κ⁻¹ Y').comp (DecV N v).subtype)
      (vecPair D.R.r β) (fun g => hP g.1) x.1 _ (fun g => e.compLeft _ (z g.1)) m' x.2.1 x.2.2
      (hcm.comp continuous_subtype_val) (fun g => hz g.1) h1
    have h3 : (Submodule.Quotient.mk x₂ : H1 _) = Submodule.Quotient.mk (cocycles1MapOfEquivariant _ _ (f.compLeft (Fin D.R.r))
        continuous_of_discreteTopology (fun g m => repOn_map (Tgl i s) κ f g.1 m) x) := hxe.symm
    obtain ⟨w, hw⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.eq _).1 h3)
    refine cupB_left _ ((repOn (Tgl i s) κ Y₂).comp (DecV N v).subtype) ((repOn ρ κ⁻¹ Y₂').comp (DecV N v).subtype)
      (vecPair D.R.r β₂) (fun g => hP₂ g.1) (fun g => f.compLeft _ (x.1 g)) x₂.1 (fun g => z g.1) w
      (hzc.comp continuous_subtype_val) (fun g h => hzz g.1 h.1) (fun g => ?_) ?_
    · rw [← hw g]
      exact (add_sub_cancel _ _).symm
    · obtain ⟨F, hF, h2⟩ := h2
      refine ⟨F, hF, fun g h => ?_⟩
      rw [← h2 g h]
      show vecPair _ β₂ _ (repOn ρ κ⁻¹ Y₂' g.1 (z h.1)) = vecPair _ β _ (repOn ρ κ⁻¹ Y' g.1 (e.compLeft _ (z h.1)))
      rw [← repOn_map, vecPair_apply, vecPair_apply]
      exact Finset.sum_congr rfl fun a _ => hfe _ _
  · have : (fun a => y.1 g a - e (z g a)) = y.1 g - e.compLeft _ (z g) := rfl
    show (fun a => y.1 g a - e (z g a)) = _
    rw [this, hz, sub_sub_cancel]

end GlobalTheory.DualSub
