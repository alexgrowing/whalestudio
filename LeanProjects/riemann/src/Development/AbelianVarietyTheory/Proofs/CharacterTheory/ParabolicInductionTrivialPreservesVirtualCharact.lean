import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinearStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
namespace GlobalTheory.ParabVirt

open Polynomial in

theorem _root_.GlobalTheory.ParabVirt.sum_fibres {G X : Type} [Group G] [Fintype G] [Fintype X]
    (H : Subgroup G) (π : G → X)
    (hs : Function.Surjective π) (hπ : ∀ s t, π s = π t ↔ s⁻¹ * t ∈ H) (f : X → ℂ) :
    ∑ t, f (π t) = (Nat.card H : ℂ) * ∑ x, f x := by
  classical
  have hcard : ∀ s : G, (Finset.univ.filter (fun t => π t = π s)).card = Nat.card H := by
    intro s
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun t => ⟨s⁻¹ * t.1, (hπ s t.1).1 t.2.symm⟩
        invFun := fun h => ⟨s * h.1, ((hπ s (s * h.1)).2 (by simpa using h.2)).symm⟩
        left_inv := fun t => by ext; simp
        right_inv := fun h => by ext; simp }
  calc ∑ t, f (π t) = ∑ x, ∑ t ∈ Finset.univ.filter (fun t => π t = x), f (π t) :=
        (Finset.sum_fiberwise _ _ _).symm
    _ = ∑ x, (Nat.card H : ℂ) * f x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        obtain ⟨s, rfl⟩ := hs x
        rw [Finset.sum_congr rfl (g := fun _ => f (π s))
          (fun t ht => by rw [(Finset.mem_filter.1 ht).2]), Finset.sum_const, hcard, nsmul_eq_mul]
    _ = _ := (Finset.mul_sum _ _ _).symm

variable {F : Type} [Field F] {n : ℕ}

def lin (x : GL (Fin n) F) : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
  LinearEquiv.ofLinear (Matrix.toLin' (x : Matrix (Fin n) (Fin n) F))
    (Matrix.toLin' ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])

theorem lin_apply (x : GL (Fin n) F) (v : Fin n → F) :
    lin x v = Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v := rfl

open Polynomial in
variable {F : Type} [Field F] {n : ℕ} in
theorem _root_.GlobalTheory.ParabVirt.lin_mul (x y : GL (Fin n) F) (v : Fin n → F) :
    _root_.GlobalTheory.ParabVirt.lin (x * y) v =
      _root_.GlobalTheory.ParabVirt.lin x (_root_.GlobalTheory.ParabVirt.lin y v) := by
  simp only [_root_.GlobalTheory.ParabVirt.lin_apply, Units.val_mul,
    Matrix.toLin'_mul_apply]

open Polynomial in
variable {F : Type} [Field F] {n : ℕ} in
theorem _root_.GlobalTheory.ParabVirt.lin_one (v : Fin n → F) :
    _root_.GlobalTheory.ParabVirt.lin (1 : GL (Fin n) F) v = v := by
  simp [_root_.GlobalTheory.ParabVirt.lin_apply]

theorem lin_inv (x : GL (Fin n) F) (v : Fin n → F) : lin x⁻¹ v = (lin x).symm v := rfl

open Polynomial in
variable {F : Type} [Field F] {n : ℕ} in
theorem _root_.GlobalTheory.ParabVirt.lin_surjective (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    ∃ x : GL (Fin n) F, _root_.GlobalTheory.ParabVirt.lin x = e := by
  refine ⟨⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap, ?_, ?_⟩, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]; simp
  · rw [← LinearMap.toMatrix'_comp]; simp
  · ext v : 1
    simp [_root_.GlobalTheory.ParabVirt.lin_apply]

open Polynomial in
variable {F : Type} [Field F] {n : ℕ} in
theorem _root_.GlobalTheory.ParabVirt.map_eq_of_stable (x : GL (Fin n) F)
    (W : Submodule F (Fin n → F)) (h : ∀ v ∈ W, _root_.GlobalTheory.ParabVirt.lin x v ∈ W) :
    W.map (_root_.GlobalTheory.ParabVirt.lin x).toLinearMap = W := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq _ _)
  rintro _ ⟨v, hv, rfl⟩
  exact h v hv

def stab (W : Submodule F (Fin n → F)) : Subgroup (GL (Fin n) F) where
  carrier := {x | ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W}
  one_mem' := fun v hv => by rw [← lin_apply, lin_one]; exact hv
  mul_mem' := fun {x y} hx hy v hv => by
    rw [← lin_apply, lin_mul]; exact hx _ (hy v hv)
  inv_mem' := fun {x} hx v hv => by
    rw [← lin_apply, lin_inv]
    rw [← map_eq_of_stable x W hx] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    simpa using hw

open Polynomial in
variable {F : Type} [Field F] {n : ℕ} in
theorem _root_.GlobalTheory.ParabVirt.mem_stab (W : Submodule F (Fin n → F)) (x : GL (Fin n) F) :
    x ∈ _root_.GlobalTheory.ParabVirt.stab W ↔
      ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W := Iff.rfl

open Polynomial in
variable {F : Type} [Field F] {n : ℕ} in
private theorem lin_mul_toLinearMap (x y : GL (Fin n) F) :
    (_root_.GlobalTheory.ParabVirt.lin (x * y)).toLinearMap =
      (_root_.GlobalTheory.ParabVirt.lin x).toLinearMap ∘ₗ
        (_root_.GlobalTheory.ParabVirt.lin y).toLinearMap :=
  LinearMap.ext fun v => _root_.GlobalTheory.ParabVirt.lin_mul x y v

open Polynomial in
variable {F : Type} [Field F] {n : ℕ} in
theorem _root_.GlobalTheory.ParabVirt.map_eq_map_iff (W : Submodule F (Fin n → F))
    (s t : GL (Fin n) F) :
    W.map (_root_.GlobalTheory.ParabVirt.lin s).toLinearMap =
        W.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap ↔
      s⁻¹ * t ∈ _root_.GlobalTheory.ParabVirt.stab W := by
  constructor
  · intro h v hv
    rw [← _root_.GlobalTheory.ParabVirt.lin_apply, _root_.GlobalTheory.ParabVirt.lin_mul,
      _root_.GlobalTheory.ParabVirt.lin_inv]
    have hmem : _root_.GlobalTheory.ParabVirt.lin t v ∈
        W.map (_root_.GlobalTheory.ParabVirt.lin s).toLinearMap := h ▸ ⟨v, hv, rfl⟩
    obtain ⟨w, hw, hw'⟩ := hmem
    simpa [← hw'] using hw
  · intro h
    have h' : ∀ v ∈ W, _root_.GlobalTheory.ParabVirt.lin (s⁻¹ * t) v ∈ W := h
    conv_rhs => rw [show t = s * (s⁻¹ * t) by group]
    rw [lin_mul_toLinearMap, Submodule.map_comp,
      _root_.GlobalTheory.ParabVirt.map_eq_of_stable _ W h']

open Polynomial in
variable {F : Type} [Field F] {n : ℕ} in
theorem _root_.GlobalTheory.ParabVirt.conj_mem_stab_iff (W : Submodule F (Fin n → F))
    (x t : GL (Fin n) F) :
    t⁻¹ * x * t ∈ _root_.GlobalTheory.ParabVirt.stab W ↔
      x ∈ _root_.GlobalTheory.ParabVirt.stab (W.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap) := by
  change (∀ v ∈ W, _root_.GlobalTheory.ParabVirt.lin (t⁻¹ * x * t) v ∈ W) ↔
    ∀ v ∈ W.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap, _root_.GlobalTheory.ParabVirt.lin x v ∈
      W.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap
  constructor
  · rintro h _ ⟨w, hw, rfl⟩
    refine ⟨_root_.GlobalTheory.ParabVirt.lin (t⁻¹ * x * t) w, h w hw, ?_⟩
    simp only [LinearEquiv.coe_coe]
    rw [← _root_.GlobalTheory.ParabVirt.lin_mul, ← _root_.GlobalTheory.ParabVirt.lin_mul,
      show t * (t⁻¹ * x * t) = x * t by group]
  · intro h w hw
    obtain ⟨u, hu, hu'⟩ := h (_root_.GlobalTheory.ParabVirt.lin t w) ⟨w, hw, rfl⟩
    have hwu : _root_.GlobalTheory.ParabVirt.lin (t⁻¹ * x * t) w = u := by
      rw [show t⁻¹ * x * t = t⁻¹ * (x * t) by group, _root_.GlobalTheory.ParabVirt.lin_mul,
        _root_.GlobalTheory.ParabVirt.lin_mul, ← hu', LinearEquiv.coe_coe,
        _root_.GlobalTheory.ParabVirt.lin_inv, LinearEquiv.symm_apply_apply]
    rw [hwu]
    exact hu

def resMat {a : ℕ} (W : Submodule F (Fin n → F)) (e : W ≃ₗ[F] (Fin a → F)) :
    stab W →* Matrix (Fin a) (Fin a) F where
  toFun h := LinearMap.toMatrix'
    (e.conj ((Matrix.toLin' ((h : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).restrict h.2))
  map_one' := by
    rw [← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    rw [LinearEquiv.conj_apply_apply, ← LinearEquiv.eq_symm_apply]
    ext1
    simp
  map_mul' x y := by
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp only [LinearEquiv.conj_apply_apply, LinearMap.comp_apply, LinearEquiv.symm_apply_apply]
    congr 1
    ext1
    exact lin_mul x.1 y.1 _

open Polynomial in
variable {F : Type} [Field F] {n : ℕ} in
private theorem exists_gl_map_lin_eq_of_finrank_eq (W₀ W : Submodule F (Fin n → F))
    (h : Module.finrank F W₀ = Module.finrank F W) :
    ∃ t : GL (Fin n) F, W₀.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap = W := by
  obtain ⟨C₀, hC₀⟩ := Submodule.exists_isCompl W₀
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  have h₁ := Submodule.finrank_add_eq_of_isCompl hC₀
  have h₂ := Submodule.finrank_add_eq_of_isCompl hC
  let E : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
    (W₀.prodEquivOfIsCompl C₀ hC₀).symm ≪≫ₗ
      (LinearEquiv.prodCongr (LinearEquiv.ofFinrankEq W₀ W h)
        (LinearEquiv.ofFinrankEq C₀ C (by omega))) ≪≫ₗ W.prodEquivOfIsCompl C hC
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.ParabVirt.lin_surjective E
  refine ⟨t, Submodule.eq_of_le_of_finrank_eq ?_ ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    have hs : (W₀.prodEquivOfIsCompl C₀ hC₀).symm v = (⟨v, hv⟩, 0) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left W₀ C₀ hC₀ ⟨v, hv⟩
    simp [ht, E, hs]
  · rw [LinearEquiv.finrank_map_eq, h]

open Polynomial in
variable {F : Type} [Field F] {n : ℕ} in

theorem _root_.GlobalTheory.ParabVirt.parab_virt : ∀ (F : Type) [Field F] [Finite F] (Φ : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.End F V → ℂ), (∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V), Φ V' (e.conj g) = Φ V g) → ∀ a n : ℕ, (fun x : GL (Fin a) F => Φ (Fin a → F) (Matrix.toLin' (x : Matrix (Fin a) (Fin a) F))) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ (GL (Fin a) F) → (fun x : GL (Fin n) F => ∑ᶠ W : {W : Submodule F (Fin n → F) // Module.finrank F W = a ∧ ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W}, Φ W.1 ((Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)).restrict W.2.2)) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ (GL (Fin n) F) := by
  intro F _ _ Φ hΦ a n hχ
  classical
  have hG := _root_.GlobalTheory.BI.virt_mul_comap_conj_ind_linear (GL (Fin n) F)
  have hGa := _root_.GlobalTheory.BI.virt_mul_comap_conj_ind_linear (GL (Fin a) F)
  by_cases ha : a ≤ n
  swap
  · convert (_root_.GlobalTheory.BI.Virt ℂ ℂ (GL (Fin n) F)).zero_mem using 1
    funext x
    rw [Pi.zero_apply]
    haveI : IsEmpty {W : Submodule F (Fin n → F) // Module.finrank F W = a ∧
        ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W} :=
      ⟨fun W => ha (by
        have h₁ := Submodule.finrank_le W.1
        rw [Module.finrank_fin_fun, W.2.1] at h₁
        exact h₁)⟩
    exact finsum_of_isEmpty _
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : Submodule F (Fin n → F), Module.finrank F W₀ = a := by
    refine ⟨Submodule.span F (Set.range fun i : Fin a => (Pi.single (Fin.castLE ha i) (1 : F) :
      Fin n → F)), ?_⟩
    rw [finrank_span_eq_card, Fintype.card_fin]
    convert (Pi.basisFun F (Fin n)).linearIndependent.comp _ (Fin.castLE_injective ha) using 1
    ext i : 1
    simp
  let e₀ : W₀ ≃ₗ[F] (Fin a → F) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hW₀, Module.finrank_fin_fun])
  let P := _root_.GlobalTheory.ParabVirt.stab W₀
  let ρ : P →* GL (Fin a) F := (_root_.GlobalTheory.ParabVirt.resMat W₀ e₀).toHomUnits
  let χ : GL (Fin a) F → ℂ := fun y => Φ (Fin a → F) (Matrix.toLin' (y : Matrix (Fin a) (Fin a) F))
  have hψ : (fun p : P => χ (ρ p)) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ P := hGa.2.1 χ hχ P ρ
  convert hG.2.2.2.1 P _ hψ using 1
  funext x
  have hval : ∀ p : P, χ (ρ p) =
      Φ W₀ ((Matrix.toLin' ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).restrict p.2) := by
    intro p
    simp only [χ, ρ, MonoidHom.coe_toHomUnits]
    exact (congrArg (Φ (Fin a → F)) (Matrix.toLin'_toMatrix' (e₀.conj
      ((Matrix.toLin' ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).restrict p.2)))).trans
      (hΦ _ _ e₀ _)
  haveI : Fintype (Submodule F (Fin n → F)) := Fintype.ofFinite _
  haveI : Fintype (GL (Fin n) F) := Fintype.ofFinite _
  let π : GL (Fin n) F → {W : Submodule F (Fin n → F) // Module.finrank F W = a} := fun t =>
    ⟨W₀.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap, by
      rw [LinearEquiv.finrank_map_eq, hW₀]⟩
  let f : {W : Submodule F (Fin n → F) // Module.finrank F W = a} → ℂ := fun W =>
    if h : ∀ v ∈ W.1, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W.1 then
      Φ W.1 ((Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)).restrict h) else 0
  let p : {W : Submodule F (Fin n → F) // Module.finrank F W = a} → Prop := fun W =>
    ∀ v ∈ W.1, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W.1
  have hs : Function.Surjective π := fun W => by
    obtain ⟨t, ht⟩ := exists_gl_map_lin_eq_of_finrank_eq W₀ W.1 (by rw [hW₀, W.2])
    exact ⟨t, Subtype.ext ht⟩
  have hπ : ∀ s t, π s = π t ↔ s⁻¹ * t ∈ P := fun s t =>
    Subtype.ext_iff.trans (_root_.GlobalTheory.ParabVirt.map_eq_map_iff W₀ s t)
  have hpt : ∀ t, _root_.GlobalTheory.BI.ext0 P (fun p => χ (ρ p)) (t⁻¹ * x * t) = f (π t) := by
    intro t
    unfold _root_.GlobalTheory.BI.ext0
    by_cases h : t⁻¹ * x * t ∈ P
    · have h' : ∀ v ∈ W₀.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap,
          Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈
            W₀.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap :=
        (_root_.GlobalTheory.ParabVirt.conj_mem_stab_iff W₀ x t).1 h
      rw [dif_pos h]
      show χ (ρ ⟨_, h⟩) = _
      rw [hval]
      simp only [f, π]
      rw [dif_pos h']
      symm
      refine (congrArg (Φ ↥(W₀.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap)) ?_).trans
        (hΦ _ _ ((_root_.GlobalTheory.ParabVirt.lin t).submoduleMap W₀) _)
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      obtain ⟨w, rfl⟩ := ((_root_.GlobalTheory.ParabVirt.lin t).submoduleMap W₀).surjective u
      rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
      simp only [LinearMap.restrict_coe_apply, LinearEquiv.submoduleMap_apply, Subgroup.coe_mk,
        ← _root_.GlobalTheory.ParabVirt.lin_apply]
      change _ = _root_.GlobalTheory.ParabVirt.lin t
        (_root_.GlobalTheory.ParabVirt.lin (t⁻¹ * x * t) (w : Fin n → F))
      simp only [← _root_.GlobalTheory.ParabVirt.lin_mul, Subgroup.coe_mk, mul_assoc,
        mul_inv_cancel_left]
    · have h' : ¬ ∀ v ∈ W₀.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap,
          Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈
            W₀.map (_root_.GlobalTheory.ParabVirt.lin t).toLinearMap :=
        fun h' => h ((_root_.GlobalTheory.ParabVirt.conj_mem_stab_iff W₀ x t).2 h')
      rw [dif_neg h]
      simp only [f, π]
      rw [dif_neg h']
  unfold _root_.GlobalTheory.BI.ind
  rw [finsum_congr hpt, finsum_eq_sum_of_fintype (fun t => f (π t)), _root_.GlobalTheory.ParabVirt.sum_fibres P π hs hπ f,
    ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne'), one_mul,
    finsum_eq_sum_of_fintype,
    ← Fintype.sum_subtype_add_sum_subtype p f]
  have hzero : ∑ W : {W // ¬ p W}, f W = 0 := Finset.sum_eq_zero (fun W _ => dif_neg W.2)
  rw [hzero, add_zero]
  exact (Fintype.sum_equiv (Equiv.subtypeSubtypeEquivSubtypeInter _ _) _ _
    (fun W => dif_pos W.2)).symm

end GlobalTheory.ParabVirt
