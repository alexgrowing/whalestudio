import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SplitFrob

section Proj

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}

theorem isCompl_toSubmodule {S S' : Subrepresentation π} (h : IsCompl S S') :
    IsCompl S.toSubmodule S'.toSubmodule := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff, ← Subrepresentation.toSubmodule_inf, disjoint_iff.mp h.1]
    try rfl
  · rw [codisjoint_iff, ← Subrepresentation.toSubmodule_sup, codisjoint_iff.mp h.2]
    try rfl

def proj {S S' : Subrepresentation π} (h : IsCompl S S') : V →ₗ[ℂ] V :=
  S.toSubmodule.subtype ∘ₗ
    Submodule.projectionOnto S.toSubmodule S'.toSubmodule (isCompl_toSubmodule h)

theorem proj_left {S S' : Subrepresentation π} (h : IsCompl S S') {v : V} (hv : v ∈ S.toSubmodule) :
    proj h v = v := by
  show S.toSubmodule.subtype
    (Submodule.projectionOnto S.toSubmodule S'.toSubmodule (isCompl_toSubmodule h) v) = v
  simp only [Submodule.projectionOnto_apply_of_mem_left _ hv, Submodule.subtype_apply]

theorem proj_right {S S' : Subrepresentation π} (h : IsCompl S S') {v : V}
    (hv : v ∈ S'.toSubmodule) : proj h v = 0 := by
  show S.toSubmodule.subtype
    (Submodule.projectionOnto S.toSubmodule S'.toSubmodule (isCompl_toSubmodule h) v) = 0
  simp only [Submodule.projectionOnto_apply_of_mem_right _ hv, map_zero]

theorem proj_comm {S S' : Subrepresentation π} (h : IsCompl S S') (g : G) (v : V) :
    proj h (π g v) = π g (proj h v) := by
  have htop : S.toSubmodule ⊔ S'.toSubmodule = ⊤ := (isCompl_toSubmodule h).sup_eq_top
  have hv : v ∈ S.toSubmodule ⊔ S'.toSubmodule := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  simp only [map_add, proj_left h hx, proj_right h hy, proj_left h (S.apply_mem_toSubmodule g hx),
    proj_right h (S'.apply_mem_toSubmodule g hy), add_zero]

end Proj

section Induced

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {X : Type} [AddCommGroup X] [Module ℂ X]

def ev (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) : IndSp e ρ →ₗ[ℂ] X where
  toFun f := f.1.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ev_unip (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) {u : GL n k}
    (hu : u ∈ unipRad k e) (f : IndSp e ρ) : ev e ρ (parInd e ρ u f) = ev e ρ f := by
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hu
  rw [MonoidHom.mem_ker] at hp
  have h := f.1.2 p 1
  rw [MonoidHom.comp_apply, hp, map_one, Module.End.one_apply, mul_one] at h
  show f.1.1 (1 * ((parab k e).subtype p)) = f.1.1 1
  rw [one_mul]
  exact h

theorem ev_levi (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) (g : Levi k m)
    (f : IndSp e ρ) :
    ev e ρ (parInd e ρ (leviEmb k e g) f) = (deltaHalf k m g : ℂ) • ρ g (ev e ρ f) := by
  have hmem := leviEmb_mem_parab k e g
  have h := f.1.2 ⟨leviEmb k e g, hmem⟩ 1
  rw [mul_one, MonoidHom.comp_apply, leviProj_leviEmb] at h
  show f.1.1 (1 * leviEmb k e g) = (deltaHalf k m g : ℂ) • ρ g (f.1.1 1)
  rw [one_mul]
  exact h

theorem exists_ev_ne (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) {f : IndSp e ρ}
    (hf : f ≠ 0) : ∃ g, ev e ρ (parInd e ρ g f) ≠ 0 := by
  by_contra hcon
  apply hf
  apply Subtype.ext
  apply Subtype.ext
  funext g
  by_contra hg
  exact hcon ⟨g, by
    change f.1.1 (1 * g) ≠ 0
    rw [one_mul]
    exact hg⟩

variable {e : (Σ a, m a) ≃ n} {ρ : Representation ℂ (Levi k m) X}

def lam {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') : IndSp e ρ →ₗ[ℂ] X :=
  ev e ρ ∘ₗ proj h

theorem lam_apply {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (f : IndSp e ρ) :
    lam h f = ev e ρ (proj h f) := rfl

theorem lam_twKer {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') :
    twKer (parInd e ρ) (unipRad k e) 1 ≤ LinearMap.ker (lam h) := by
  unfold GlobalTheory.PRep.twKer
  refine Submodule.span_le.mpr ?_
  rintro w ⟨u, v, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, MonoidHom.one_apply, Units.val_one, one_smul,
    lam_apply, lam_apply, proj_comm, ev_unip e ρ u.2, sub_self]

def frob {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') :
    (jac e (parInd e ρ)).IntertwiningMap ρ where
  toLinearMap := (twKer (parInd e ρ) (unipRad k e) 1).liftQ (lam h) (lam_twKer h)
  isIntertwining' g := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show (twKer (parInd e ρ) (unipRad k e) 1).liftQ (lam h) (lam_twKer h)
        (jac e (parInd e ρ) g (Submodule.Quotient.mk v)) = ρ g (lam h v)
    rw [jac_mk, ← Submodule.Quotient.mk_smul, Submodule.liftQ_apply, map_smul, lam_apply, proj_comm,
      ev_levi, lam_apply, smul_smul]
    simp

theorem frob_mk {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (v : IndSp e ρ) :
    (frob h).toLinearMap (Submodule.Quotient.mk v) = lam h v := rfl

theorem exists_lam_ne {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (hS : S ≠ ⊥) :
    ∃ v ∈ S.toSubmodule, lam h v ≠ 0 := by
  have hS0 : S.toSubmodule ≠ ⊥ := by
    intro h0
    apply hS
    apply Subrepresentation.ext
    rw [h0]
    try rfl
  obtain ⟨f, hfS, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  obtain ⟨g, hg⟩ := exists_ev_ne e ρ hf0
  refine ⟨parInd e ρ g f, S.apply_mem_toSubmodule g hfS, ?_⟩
  rw [lam_apply, proj_left h (S.apply_mem_toSubmodule g hfS)]
  exact hg

theorem not_dichotomy {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (hS : S ≠ ⊥)
    (hS' : S' ≠ ⊥) :
    ¬ (∀ φ ψ : (jac e (parInd e ρ)).IntertwiningMap ρ,
      φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro hd
  obtain ⟨v, hvS, hv⟩ := exists_lam_ne h hS
  obtain ⟨w, hwS', hw⟩ := exists_lam_ne h.symm hS'
  rcases hd (frob h) (frob h.symm) with h0 | ⟨c, hc⟩
  · apply hv
    rw [← frob_mk h v, h0, LinearMap.zero_apply]
  · have e1 : lam h.symm v = c • lam h v := by
      rw [← frob_mk h.symm v, hc, LinearMap.smul_apply, frob_mk]
    rw [lam_apply, proj_right h.symm hvS, map_zero] at e1
    rcases smul_eq_zero.mp e1.symm with hc0 | hc0
    · apply hw
      rw [← frob_mk h.symm w, hc, hc0, zero_smul, LinearMap.zero_apply]
    · exact hv hc0

end Induced

theorem not_dichotomy_det : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (W W' : Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))), IsCompl W W' → W ≠ ⊥ → W' ≠ ⊥ → ¬ (∀ φ ψ : (jac (two (stdSum (rfl : a + b = a + b))) (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro k _ _ _ _ a b χ₁ χ₂ W W' h hW hW'
  exact not_dichotomy h hW hW'

end GlobalTheory.CompanionTheory.SplitFrob
