import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_kill

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {n : ℕ} (G : Grp k n)

theorem PJ_smul {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ)
    (a : ℂ) (v : V) : G.PJ π r (a • v) = a • G.PJ π r v := by
  unfold Grp.PJ
  rw [smul_finsum]
  congr 1
  funext c
  rw [map_smul, smul_comm]

theorem core_mul {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ)
    (hmul : ∀ v : V, (∀ u ∈ KC k n r, π u v = v) → ∀ j ∈ G.JSet, G.PJ π r (π j v) = G.lam j • G.PJ π r v)
    (x : V) (hx : x ∈ G.Eig π) (y : GL (Fin n) k) (hfix : ∀ u ∈ KC k n r, π u (π y x) = π y x)
    (hj : ∃ j ∈ G.JSet, y⁻¹ * j * y ∈ G.JSet ∧ G.lam (y⁻¹ * j * y) ≠ G.lam j) : G.PJ π r (π y x) = 0 := by
  obtain ⟨j, hjJ, hyj, hne⟩ := hj
  have hx' : ∀ g ∈ G.JSet, π g x = G.lam g • x := hx
  have hjw : π j (π y x) = G.lam (y⁻¹ * j * y) • π y x := by
    have e : j * y = y * (y⁻¹ * j * y) := by group
    have e1 : π j (π y x) = π (j * y) x := by rw [map_mul]; rfl
    have e2 : π (y * (y⁻¹ * j * y)) x = π y (π (y⁻¹ * j * y) x) := by rw [map_mul]; rfl
    rw [e1, e, e2, hx' _ hyj, map_smul]
  have key := hmul (π y x) hfix j hjJ
  rw [hjw, PJ_smul] at key
  have h0 : (G.lam (y⁻¹ * j * y) - G.lam j) • G.PJ π r (π y x) = 0 := by
    rw [sub_smul, key, sub_self]
  exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)

theorem core {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ)
    (hPJ : Finite (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) ∧
      ∀ v : V, (∀ u ∈ KC k n r, π u v = v) →
        G.PJ π r v ∈ G.Eig π ∧ (∀ j ∈ G.JSet, G.PJ π r (π j v) = G.lam j • G.PJ π r v) ∧
        (v ∈ G.Eig π → G.PJ π r v = (Nat.card (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) : ℂ) • v))
    (x : V) (hx : x ∈ G.Eig π) (y : GL (Fin n) k) (hfix : ∀ u ∈ KC k n r, π u (π y x) = π y x)
    (hj : ∃ j ∈ G.JSet, y⁻¹ * j * y ∈ G.JSet ∧ G.lam (y⁻¹ * j * y) ≠ G.lam j) : G.PJ π r (π y x) = 0 :=
  core_mul G π r (fun v hv => (hPJ.2 v hv).2.1) x hx y hfix hj

end UpperTheory.TNZ.Grp.P_kill

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {n : ℕ} (G : Grp k n)

theorem step_kill : G.AnnihilationProp := by
  intro hcb hccB hΔU hΔM h1 h2 h3 h4 h5 h6 hPJ V _ _ π r hr x hx y hfix hj
  exact P_kill.core G π r (hPJ hcb hccB hΔU hΔM h1 h2 h3 h4 h5 h6 V π r hr) x hx y hfix hj

end UpperTheory.TNZ.Grp
