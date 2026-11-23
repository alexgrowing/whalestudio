import Mathlib

noncomputable section

namespace Formalism.L2.SG.Pf.PCount.BI

open Submodule

variable {E : Type} [CommRing E] (R : Subring E)

abbrev Rs : Submodule R E := LinearMap.range (Algebra.linearMap R E)

abbrev Qt : Type := E ⧸ Rs R

abbrev IsoT {C C' : Type} [AddCommGroup C] [Module R C] [AddCommGroup C'] [Module R C']
    (e : C) (e' : C') (l : C →ₗ[R] Qt R) (l' : C' →ₗ[R] Qt R) : Type :=
  {φ : C ≃ₗ[R] C' // φ e = e' ∧ ∀ v, l' (φ v) = l v}

variable {R}

theorem mkQ_eq_zero_iff (τ : E) : (Rs R).mkQ τ = 0 ↔ ∃ r : R, (r : E) = τ := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  first
    | exact Iff.rfl
    | (rw [LinearMap.mem_range]; exact Iff.rfl)
    | (simp [Rs]; done)

section G

variable {C : Type} [AddCommGroup C] [Module R C] (α : C →ₗ[R] Qt R)

def NF : Submodule R (C × E) :=
  LinearMap.ker (α.comp (LinearMap.fst R C E) + (Rs R).mkQ.comp (LinearMap.snd R C E))

theorem mem_NF {x : C × E} : x ∈ NF α ↔ α x.1 + (Rs R).mkQ x.2 = 0 := by
  first
    | exact Iff.rfl
    | (rw [NF, LinearMap.mem_ker]; exact Iff.rfl)
    | (simp [NF]; done)

theorem one_mem_NF : ((0 : C), (1 : E)) ∈ NF α := by
  rw [mem_NF]
  show α 0 + (Rs R).mkQ 1 = 0
  rw [map_zero, zero_add]
  exact (mkQ_eq_zero_iff _).2 ⟨1, by first | rfl | simp⟩

def e0 : NF α := ⟨(0, 1), one_mem_NF α⟩

theorem lift_exists (c : C) : ∃ τ : E, (c, τ) ∈ NF α := by
  obtain ⟨τ, hτ⟩ := (Rs R).mkQ_surjective (-α c)
  refine ⟨τ, (mem_NF α).2 ?_⟩
  show α c + (Rs R).mkQ τ = 0
  rw [hτ]
  first | exact add_neg_cancel _ | simp

def liftN (c : C) : NF α := ⟨(c, (lift_exists α c).choose), (lift_exists α c).choose_spec⟩

theorem diff_of_fst {x x' : NF α} (h : (x : C × E).1 = (x' : C × E).1) : ∃ r : R, x - x' = r • e0 α := by
  have hx := (mem_NF α).1 x.2
  have hx' := (mem_NF α).1 x'.2
  rw [h] at hx
  have h0 : (Rs R).mkQ ((x : C × E).2 - (x' : C × E).2) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact add_left_cancel (hx.trans hx'.symm)
  obtain ⟨r, hr⟩ := (mkQ_eq_zero_iff _).1 h0
  refine ⟨r, Subtype.ext (Prod.ext ?_ ?_)⟩
  · first
      | (show (x : C × E).1 - (x' : C × E).1 = r • (0 : C); rw [h, sub_self, smul_zero])
      | (simp [e0, h]; done)
  · first
      | (show (x : C × E).2 - (x' : C × E).2 = (r : E) * 1; rw [mul_one, hr])
      | (simp [e0, hr, Subring.smul_def]; done)
      | (simp [e0, ← hr, Algebra.smul_def]; done)

variable (β : C) (u : E) (hb : α β + (Rs R).mkQ u = 0)

def bN : NF α := ⟨(β, u), (mem_NF α).2 hb⟩

abbrev CG : Type := NF α ⧸ (R ∙ bN α β u hb)

def eG : CG α β u hb := Submodule.Quotient.mk (e0 α)

def lamG (hu : IsUnit u) : CG α β u hb →ₗ[R] Qt R :=
  (R ∙ bN α β u hb).liftQ
    (((Rs R).mkQ.comp ((LinearMap.mulLeft R ((hu.unit⁻¹ : Eˣ) : E)).comp (LinearMap.snd R C E))).comp
      (NF α).subtype)
    (by
      rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, bN, LinearMap.snd_apply,
        LinearMap.mulLeft_apply, Units.inv_mul, IsUnit.unit_spec]
      exact (mkQ_eq_zero_iff _).2 ⟨1, by simp⟩)

theorem lamG_mk (hu : IsUnit u) (x : NF α) :
    lamG α β u hb hu (Submodule.Quotient.mk x) = (Rs R).mkQ (((hu.unit⁻¹ : Eˣ) : E) * (x : C × E).2) := rfl

end G

section Two

variable {C₁ C₂ : Type} [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂]
  {α₁ : C₁ →ₗ[R] Qt R} {α₂ : C₂ →ₗ[R] Qt R} {β₁ : C₁} {β₂ : C₂} {u : E} (hu : IsUnit u)
  {hb₁ : α₁ β₁ + (Rs R).mkQ u = 0} {hb₂ : α₂ β₂ + (Rs R).mkQ u = 0}

include hu in
theorem unit_cancel {r : R} (h : (r : E) * u = 0) : r = 0 := by
  have h' : (r : E) = 0 := by
    first
      | exact hu.mul_left_eq_zero.1 h
      | (obtain ⟨v, rfl⟩ := hu; simpa using h)
  first | exact Subtype.ext h' | exact_mod_cast h' | simpa using h'

include hu in
theorem uniq_N {z z' : NF α₂} (h1 : (Submodule.Quotient.mk z : CG α₂ β₂ u hb₂) = Submodule.Quotient.mk z')
    (h2 : (z : C₂ × E).2 = (z' : C₂ × E).2) : z = z' := by
  rw [Submodule.Quotient.eq, Submodule.mem_span_singleton] at h1
  obtain ⟨r, hr⟩ := h1
  have h3 : (r : E) * u = 0 := by
    have h4 : ((r • bN α₂ β₂ u hb₂ : NF α₂) : C₂ × E).2 = ((z - z' : NF α₂) : C₂ × E).2 := by
      rw [hr]
    simp only [Submodule.coe_smul, Submodule.coe_sub, Prod.smul_snd, Prod.snd_sub, h2, sub_self] at h4
    first
      | exact h4
      | simpa [Subring.smul_def, bN] using h4
      | simpa [Algebra.smul_def, bN] using h4
  have hr0 := unit_cancel hu h3
  rw [hr0, zero_smul] at hr
  exact sub_eq_zero.1 hr.symm

variable (ψ : CG α₁ β₁ u hb₁ →ₗ[R] CG α₂ β₂ u hb₂)
  (hψl : ∀ v, lamG α₂ β₂ u hb₂ hu (ψ v) = lamG α₁ β₁ u hb₁ hu v)

include hψl in
theorem exists_rep (x : NF α₁) : ∃ z : NF α₂, (Submodule.Quotient.mk z : CG α₂ β₂ u hb₂) = ψ (Submodule.Quotient.mk x) ∧
    (z : C₂ × E).2 = (x : C₁ × E).2 := by
  obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (ψ (Submodule.Quotient.mk x))
  have hl := hψl (Submodule.Quotient.mk x)
  rw [← hw, lamG_mk, lamG_mk] at hl
  have h0 : (Rs R).mkQ (((hu.unit⁻¹ : Eˣ) : E) * ((x : C₁ × E).2 - (w : C₂ × E).2)) = 0 := by
    rw [mul_sub, map_sub, hl, sub_self]
  obtain ⟨s, hs⟩ := (mkQ_eq_zero_iff _).1 h0
  have hinv : ((hu.unit⁻¹ : Eˣ) : E) * u = 1 := by
    first | exact hu.val_inv_mul | exact hu.unit.inv_mul | simp
  refine ⟨w + s • bN α₂ β₂ u hb₂, ?_, ?_⟩
  · have hp : (Submodule.Quotient.mk (bN α₂ β₂ u hb₂) : CG α₂ β₂ u hb₂) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self _)
    rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, hp, smul_zero, add_zero, hw]
  · show (w : C₂ × E).2 + (s : E) * u = (x : C₁ × E).2
    linear_combination u * hs + ((x : C₁ × E).2 - (w : C₂ × E).2) * hinv

def Phi (x : NF α₁) : NF α₂ := (exists_rep hu ψ hψl x).choose

theorem Phi_mk (x : NF α₁) :
    (Submodule.Quotient.mk (Phi hu ψ hψl x) : CG α₂ β₂ u hb₂) = ψ (Submodule.Quotient.mk x) := (exists_rep hu ψ hψl x).choose_spec.1

theorem Phi_snd (x : NF α₁) : ((Phi hu ψ hψl x : NF α₂) : C₂ × E).2 = (x : C₁ × E).2 := (exists_rep hu ψ hψl x).choose_spec.2

theorem Phi_add (x y : NF α₁) : Phi hu ψ hψl (x + y) = Phi hu ψ hψl x + Phi hu ψ hψl y := by
  refine uniq_N (β₂ := β₂) (hb₂ := hb₂) hu ?_ ?_
  · first
      | (simp only [Phi_mk, Submodule.Quotient.mk_add, map_add]; done)
      | (simp [Phi_mk]; done)
  · first
      | (simp only [Phi_snd, Submodule.coe_add, Prod.snd_add]; done)
      | (simp [Phi_snd]; done)

theorem Phi_smul (r : R) (x : NF α₁) : Phi hu ψ hψl (r • x) = r • Phi hu ψ hψl x := by
  refine uniq_N (β₂ := β₂) (hb₂ := hb₂) hu ?_ ?_
  · first
      | (simp only [Phi_mk, Submodule.Quotient.mk_smul, map_smul]; done)
      | (simp [Phi_mk]; done)
  · first
      | (simp only [Phi_snd, Submodule.coe_smul, Prod.smul_snd]; done)
      | (simp [Phi_snd]; done)

theorem fiberMap_fiberUnit (hψe : ψ (eG α₁ β₁ u hb₁) = eG α₂ β₂ u hb₂) : Phi hu ψ hψl (e0 α₁) = e0 α₂ := by
  refine uniq_N (β₂ := β₂) (hb₂ := hb₂) hu ?_ ?_
  · rw [Phi_mk]
    exact hψe
  · rw [Phi_snd] <;> rfl

theorem Phi_fst (hψe : ψ (eG α₁ β₁ u hb₁) = eG α₂ β₂ u hb₂) {x x' : NF α₁}
    (h : (x : C₁ × E).1 = (x' : C₁ × E).1) :
    ((Phi hu ψ hψl x : NF α₂) : C₂ × E).1 = ((Phi hu ψ hψl x' : NF α₂) : C₂ × E).1 := by
  obtain ⟨r, hr⟩ := diff_of_fst α₁ h
  have hx : x = x' + r • e0 α₁ := by
    first | exact sub_eq_iff_eq_add'.1 hr | (rw [← hr]; abel)
  rw [hx, Phi_add, Phi_smul, fiberMap_fiberUnit hu ψ hψl hψe]
  first
    | (simp [e0]; done)
    | (show ((Phi hu ψ hψl x' : NF α₂) : C₂ × E).1 + r • (0 : C₂) = _; rw [smul_zero, add_zero])

def phiF (c : C₁) : C₂ := ((Phi hu ψ hψl (liftN α₁ c) : NF α₂) : C₂ × E).1

theorem phiF_of (hψe : ψ (eG α₁ β₁ u hb₁) = eG α₂ β₂ u hb₂) (x : NF α₁) :
    phiF hu ψ hψl (x : C₁ × E).1 = ((Phi hu ψ hψl x : NF α₂) : C₂ × E).1 := Phi_fst hu ψ hψl hψe (x := liftN α₁ (x : C₁ × E).1) (x' := x) rfl

def phiL (hψe : ψ (eG α₁ β₁ u hb₁) = eG α₂ β₂ u hb₂) : C₁ →ₗ[R] C₂ where
  toFun := phiF hu ψ hψl
  map_add' c c' := by
    have h := phiF_of hu ψ hψl hψe (liftN α₁ c + liftN α₁ c')
    simp only [Submodule.coe_add, Prod.fst_add, Phi_add] at h
    rw [show (liftN α₁ c : C₁ × E).1 = c from rfl, show (liftN α₁ c' : C₁ × E).1 = c' from rfl] at h
    rw [h]
    rfl
  map_smul' r c := by
    have h := phiF_of hu ψ hψl hψe (r • liftN α₁ c)
    simp only [Submodule.coe_smul, Prod.smul_fst, Phi_smul] at h
    rw [show (liftN α₁ c : C₁ × E).1 = c from rfl] at h
    rw [h]
    rfl

end Two

section Equiv

variable {C₁ C₂ : Type} [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂]
  {α₁ : C₁ →ₗ[R] Qt R} {α₂ : C₂ →ₗ[R] Qt R} {β₁ : C₁} {β₂ : C₂} {u : E} (hu : IsUnit u)
  (hb₁ : α₁ β₁ + (Rs R).mkQ u = 0) (hb₂ : α₂ β₂ + (Rs R).mkQ u = 0)

omit hu hb₁ hb₂ in
theorem NF_map (φ : C₁ ≃ₗ[R] C₂) (hα : ∀ v, α₂ (φ v) = α₁ v) :
    (NF α₁).map ((φ.prodCongr (LinearEquiv.refl R E)) : C₁ × E →ₗ[R] C₂ × E) = NF α₂ := by
  have hα' : ∀ w, α₁ (φ.symm w) = α₂ w := fun w => by
    rw [← hα (φ.symm w), LinearEquiv.apply_symm_apply]
  ext y
  first
    | (rw [Submodule.mem_map_equiv, mem_NF, mem_NF]
       show α₁ (φ.symm y.1) + (Rs R).mkQ y.2 = 0 ↔ _
       rw [hα'])
    | (rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, mem_NF, mem_NF]
       show α₁ (φ.symm y.1) + (Rs R).mkQ y.2 = 0 ↔ _
       rw [hα'])
    | (simp [Submodule.mem_map_equiv, mem_NF, hα']; done)

omit hu hb₁ hb₂ in

def PhiN (φ : C₁ ≃ₗ[R] C₂) (hα : ∀ v, α₂ (φ v) = α₁ v) : NF α₁ ≃ₗ[R] NF α₂ :=
  LinearEquiv.ofSubmodules (φ.prodCongr (LinearEquiv.refl R E)) (NF α₁) (NF α₂) (NF_map φ hα)

omit hu hb₁ hb₂ in
theorem PhiN_apply (φ : C₁ ≃ₗ[R] C₂) (hα : ∀ v, α₂ (φ v) = α₁ v) (x : NF α₁) :
    ((PhiN φ hα x : NF α₂) : C₂ × E) = (φ (x : C₁ × E).1, (x : C₁ × E).2) := rfl

def Fψ (φ : IsoT R β₁ β₂ α₁ α₂) : IsoT R (eG α₁ β₁ u hb₁) (eG α₂ β₂ u hb₂) (lamG α₁ β₁ u hb₁ hu) (lamG α₂ β₂ u hb₂ hu) :=
  ⟨Submodule.Quotient.equiv _ _ (PhiN φ.1 φ.2.2) (by
      have hb : PhiN φ.1 φ.2.2 (bN α₁ β₁ u hb₁) = bN α₂ β₂ u hb₂ :=
        Subtype.ext (by rw [PhiN_apply]; simp [bN, φ.2.1])
      rw [Submodule.map_span, Set.image_singleton]
      erw [hb]),
    by
      show Submodule.Quotient.mk (PhiN φ.1 φ.2.2 (e0 α₁)) = Submodule.Quotient.mk (e0 α₂)
      congr 1
      exact Subtype.ext (by rw [PhiN_apply]; simp [e0]),
    fun v => by
      induction v using Submodule.Quotient.induction_on with
      | H x =>
        show lamG α₂ β₂ u hb₂ hu (Submodule.Quotient.mk (PhiN φ.1 φ.2.2 x)) = _
        rw [lamG_mk, lamG_mk, PhiN_apply]⟩

theorem Fψ_mk (φ : IsoT R β₁ β₂ α₁ α₂) (x : NF α₁) :
    (Fψ hu hb₁ hb₂ φ).1 (Submodule.Quotient.mk x) = Submodule.Quotient.mk (PhiN φ.1 φ.2.2 x) := rfl

theorem Fψ_injective : Function.Injective (Fψ hu hb₁ hb₂) := by
  intro φ φ' h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro c
  have h1 : (Submodule.Quotient.mk (PhiN φ.1 φ.2.2 (liftN α₁ c)) : CG α₂ β₂ u hb₂) =
      Submodule.Quotient.mk (PhiN φ'.1 φ'.2.2 (liftN α₁ c)) := by
    rw [← Fψ_mk hu hb₁ hb₂ φ, ← Fψ_mk hu hb₁ hb₂ φ', h]
  have h2 := uniq_N hu h1 (by simp only [PhiN_apply])
  have h3 : ((PhiN φ.1 φ.2.2 (liftN α₁ c) : NF α₂) : C₂ × E).1 =
      ((PhiN φ'.1 φ'.2.2 (liftN α₁ c) : NF α₂) : C₂ × E).1 := by
    rw [h2]
  rw [PhiN_apply, PhiN_apply] at h3
  exact h3

theorem Fψ_surjective : Function.Surjective (Fψ hu hb₁ hb₂) := by
  intro Ψ
  obtain ⟨e, he, hl⟩ := Ψ
  have hl0 : ∀ v, lamG α₂ β₂ u hb₂ hu (e.toLinearMap v) = lamG α₁ β₁ u hb₁ hu v := hl
  have hl1 : ∀ v, lamG α₁ β₁ u hb₁ hu (e.symm.toLinearMap v) = lamG α₂ β₂ u hb₂ hu v := by
    intro v
    have h := hl (e.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have he0 : e.toLinearMap (eG α₁ β₁ u hb₁) = eG α₂ β₂ u hb₂ := he
  have he1 : e.symm.toLinearMap (eG α₂ β₂ u hb₂) = eG α₁ β₁ u hb₁ := by
    show e.symm _ = _
    rw [LinearEquiv.symm_apply_eq]
    exact he.symm
  have hinv1 : ∀ x, Phi hu e.symm.toLinearMap hl1 (Phi hu e.toLinearMap hl0 x) = x := by
    intro x
    refine uniq_N (β₂ := β₁) (hb₂ := hb₁) hu ?_ ?_
    · rw [Phi_mk, Phi_mk]
      exact e.symm_apply_apply _
    · rw [Phi_snd, Phi_snd]
  have hinv2 : ∀ y, Phi hu e.toLinearMap hl0 (Phi hu e.symm.toLinearMap hl1 y) = y := by
    intro y
    refine uniq_N (β₂ := β₂) (hb₂ := hb₂) hu ?_ ?_
    · rw [Phi_mk, Phi_mk]
      exact e.apply_symm_apply _
    · rw [Phi_snd, Phi_snd]
  have hfg : ∀ c, phiF hu e.toLinearMap hl0 (phiF hu e.symm.toLinearMap hl1 c) = c := by
    intro c
    have h := phiF_of hu e.toLinearMap hl0 he0 (Phi hu e.symm.toLinearMap hl1 (liftN α₂ c))
    rw [hinv2] at h
    exact h
  have hgf : ∀ c, phiF hu e.symm.toLinearMap hl1 (phiF hu e.toLinearMap hl0 c) = c := by
    intro c
    have h := phiF_of hu e.symm.toLinearMap hl1 he1 (Phi hu e.toLinearMap hl0 (liftN α₁ c))
    rw [hinv1] at h
    exact h
  have hp : Phi hu e.toLinearMap hl0 (bN α₁ β₁ u hb₁) = bN α₂ β₂ u hb₂ := by
    refine uniq_N (β₂ := β₂) (hb₂ := hb₂) hu ?_ ?_
    · rw [Phi_mk]
      have h1 : (Submodule.Quotient.mk (bN α₁ β₁ u hb₁) : CG α₁ β₁ u hb₁) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self _)
      have h2 : (Submodule.Quotient.mk (bN α₂ β₂ u hb₂) : CG α₂ β₂ u hb₂) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self _)
      rw [h1, h2, map_zero]
    · rw [Phi_snd] <;> rfl
  have hβ : phiF hu e.toLinearMap hl0 β₁ = β₂ := by
    have h := phiF_of hu e.toLinearMap hl0 he0 (bN α₁ β₁ u hb₁)
    rw [hp] at h
    exact h
  have hα : ∀ c, α₂ (phiF hu e.toLinearMap hl0 c) = α₁ c := by
    intro c
    have h1 := (mem_NF α₁).1 (liftN α₁ c).2
    have h2 := (mem_NF α₂).1 (Phi hu e.toLinearMap hl0 (liftN α₁ c)).2
    rw [Phi_snd] at h2
    exact add_right_cancel (h2.trans h1.symm)
  refine ⟨⟨LinearEquiv.ofLinear (phiL hu e.toLinearMap hl0 he0)
      (phiL hu e.symm.toLinearMap hl1 he1)
      (LinearMap.ext fun c => hfg c) (LinearMap.ext fun c => hgf c), hβ, fun c => hα c⟩, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | H x =>
    refine (Fψ_mk hu hb₁ hb₂ _ x).trans
      ((congrArg Submodule.Quotient.mk ?_).trans (Phi_mk hu e.toLinearMap hl0 x))
    apply Subtype.ext
    rw [PhiN_apply]
    refine Prod.ext ?_ ?_
    · exact phiF_of hu e.toLinearMap hl0 he0 x
    · exact (Phi_snd hu e.toLinearMap hl0 x).symm

theorem card_isoT_G :
    Nat.card (IsoT R β₁ β₂ α₁ α₂) =
      Nat.card (IsoT R (eG α₁ β₁ u hb₁) (eG α₂ β₂ u hb₂) (lamG α₁ β₁ u hb₁ hu) (lamG α₂ β₂ u hb₂ hu)) :=
  Nat.card_congr (Equiv.ofBijective _
    ⟨Fψ_injective hu hb₁ hb₂, Fψ_surjective hu hb₁ hb₂⟩)

end Equiv

section Congr

variable {A₁ A₂ B₁ B₂ : Type} [AddCommGroup A₁] [Module R A₁] [AddCommGroup A₂] [Module R A₂]
  [AddCommGroup B₁] [Module R B₁] [AddCommGroup B₂] [Module R B₂]
  {a₁ : A₁} {a₂ : A₂} {b₁ : B₁} {b₂ : B₂} {la₁ : A₁ →ₗ[R] Qt R} {la₂ : A₂ →ₗ[R] Qt R}
  {lb₁ : B₁ →ₗ[R] Qt R} {lb₂ : B₂ →ₗ[R] Qt R}

theorem card_isoT_congr (θ₁ : IsoT R a₁ b₁ la₁ lb₁) (θ₂ : IsoT R a₂ b₂ la₂ lb₂) :
    Nat.card (IsoT R a₁ a₂ la₁ la₂) = Nat.card (IsoT R b₁ b₂ lb₁ lb₂) := by
  obtain ⟨t₁, ht₁, hl₁⟩ := θ₁
  obtain ⟨t₂, ht₂, hl₂⟩ := θ₂
  exact Nat.card_congr
    { toFun := fun φ => ⟨(t₁.symm.trans φ.1).trans t₂,
        by
          have h : t₁.symm b₁ = a₁ := by
            rw [LinearEquiv.symm_apply_eq]
            exact ht₁.symm
          show t₂ (φ.1 (t₁.symm b₁)) = b₂
          rw [h, φ.2.1, ht₂],
        fun v => by
          show lb₂ (t₂ (φ.1 (t₁.symm v))) = lb₁ v
          rw [hl₂, φ.2.2, ← hl₁, LinearEquiv.apply_symm_apply]⟩
      invFun := fun ψ => ⟨(t₁.trans ψ.1).trans t₂.symm,
        by
          show t₂.symm (ψ.1 (t₁ a₁)) = a₂
          rw [ht₁, ψ.2.1, LinearEquiv.symm_apply_eq]
          exact ht₂.symm,
        fun v => by
          show la₂ (t₂.symm (ψ.1 (t₁ v))) = la₁ v
          rw [← hl₂, LinearEquiv.apply_symm_apply, ψ.2.2, hl₁]⟩
      left_inv := fun φ => Subtype.ext (LinearEquiv.ext fun v => by
        show t₂.symm (t₂ (φ.1 (t₁.symm (t₁ v)))) = φ.1 v
        rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply])
      right_inv := fun ψ => Subtype.ext (LinearEquiv.ext fun v => by
        show t₂ (t₂.symm (ψ.1 (t₁ (t₁.symm v)))) = ψ.1 v
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]) }

end Congr

end Formalism.L2.SG.Pf.PCount.BI
