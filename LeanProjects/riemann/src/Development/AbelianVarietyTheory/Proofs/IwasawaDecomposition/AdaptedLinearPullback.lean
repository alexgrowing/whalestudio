import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.StepInt

def optionSumEquiv (A B : Type) : Option A ⊕ B ≃ A ⊕ Option B where
  toFun
    | .inl none => .inr none
    | .inl (some a) => .inl a
    | .inr b => .inr (some b)
  invFun
    | .inl a => .inl (some a)
    | .inr none => .inl none
    | .inr (some b) => .inr b
  left_inv := by rintro ((_ | a) | b) <;> rfl
  right_inv := by rintro (a | (_ | b)) <;> rfl

theorem exists_basis_succ {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {k n : ℕ}
    (b : Module.Basis (Fin k ⊕ Fin n) R N) (η : Fin n → R) (c : Fin n) (hc : IsUnit (η c)) :
    ∃ (m : ℕ) (b' : Module.Basis (Fin (k + 1) ⊕ Fin m) R N), (∀ i : Fin k, b' (.inl i.castSucc) = b (.inl i)) ∧
      b' (.inl (Fin.last k)) = ∑ j, η j • b (.inr j) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := c.pos; omega⟩
  have hr : b.repr (∑ j, η j • b (.inr j)) (.inr c) = η c := by
    simp [Finsupp.single_apply]
  have hd : IsUnit (b.det (Function.update b (.inr c) (∑ j, η j • b (.inr j)))) := by
    rw [Module.Basis.det_apply, Module.Basis.toMatrix_update, Module.Basis.toMatrix_self, ← Matrix.cramer_apply,
      Matrix.cramer_one]
    rw [← hr] at hc
    exact hc
  obtain ⟨h1, h2⟩ := (Module.Basis.is_basis_iff_det b).2 hd
  let q : Fin (k + 1) ⊕ Fin m ≃ Fin k ⊕ Fin (m + 1) :=
    (Equiv.sumCongr finSuccEquivLast (Equiv.refl _)).trans
      ((optionSumEquiv _ _).trans (Equiv.sumCongr (Equiv.refl _) (finSuccEquiv' c).symm))
  refine ⟨m, (Module.Basis.mk h1 h2.ge).reindex q.symm, fun i => ?_, ?_⟩
  · have : q (.inl i.castSucc) = .inl i := by simp [q, optionSumEquiv]
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, this, Module.Basis.mk_apply, Function.update_of_ne (by simp)]
  · have : q (.inl (Fin.last k)) = .inr c := by simp [q, optionSumEquiv]
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, this, Module.Basis.mk_apply, Function.update_self]

theorem initSpan_castSucc {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {k : ℕ} (v : Fin (k + 1) → N)
    {j : ℕ} (hj : j ≤ k) : initSpan R v j = initSpan R (fun i : Fin k => v i.castSucc) j := by
  unfold initSpan
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi' : (i : ℕ) < j := hi
    exact ⟨⟨i, by omega⟩, hi', rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.castSucc, hi, rfl⟩

theorem initSpan_succ {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {M k : ℕ} (v : Fin M → N) (hk : k < M) :
    initSpan R v (k + 1) = initSpan R v k ⊔ Submodule.span R {v ⟨k, hk⟩} := by
  unfold initSpan
  rw [← Submodule.span_union, ← Set.image_singleton, ← Set.image_union]
  congr 2
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
  omega

theorem initSpan_step {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {M k n : ℕ}
    (b : Module.Basis (Fin k ⊕ Fin n) R N) (η : Fin n → R) (u : Fin M → N) (hk : k < M)
    (hu : ∀ j ≤ k, initSpan R u j = initSpan R (fun i : Fin k => b (.inl i)) j) (e : Rˣ)
    (he : ∀ i, b.repr (u ⟨k, hk⟩) (.inr i) = (e : R) * η i) (v : Fin (k + 1) → N)
    (hv : ∀ i : Fin k, v i.castSucc = b (.inl i)) (hv' : v (Fin.last k) = ∑ j, η j • b (.inr j)) :
    ∀ j ≤ k + 1, initSpan R u j = initSpan R v j := by
  have h0 : ∀ j ≤ k, initSpan R u j = initSpan R v j := fun j hj => by
    rw [initSpan_castSucc v hj, hu j hj]; simp only [hv]
  intro j hj
  rcases hj.eq_or_lt with rfl | hj
  · rw [initSpan_succ u hk, initSpan_succ v (Nat.lt_succ_self k), h0 k le_rfl]
    have hs : ∑ i : Fin k, b.repr (u ⟨k, hk⟩) (.inl i) • b (.inl i) ∈ initSpan R v k :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.castSucc, i.2, hv i⟩)
    have hw : u ⟨k, hk⟩ = ∑ i : Fin k, b.repr (u ⟨k, hk⟩) (.inl i) • b (.inl i) +
        (e : R) • v ⟨k, Nat.lt_succ_self k⟩ := by
      conv_lhs => rw [← b.sum_repr (u ⟨k, hk⟩), Fintype.sum_sum_type]
      rw [show v ⟨k, Nat.lt_succ_self k⟩ = _ from hv', Finset.smul_sum]
      simp only [he, mul_smul]
    generalize ∑ i : Fin k, b.repr (u ⟨k, hk⟩) (.inl i) • b (.inl i) = s at hs hw
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
    · rw [Submodule.span_singleton_le_iff_mem, hw]
      exact Submodule.add_mem_sup hs (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    · rw [Submodule.span_singleton_le_iff_mem, ← Submodule.smul_mem_iff_of_isUnit _ e.isUnit,
        ← sub_eq_iff_eq_add'.2 hw]
      exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
        (Submodule.mem_sup_left hs)
  · exact h0 j (by omega)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem tanPull_basPull {Y X X' : Scheme.{0}} {t : SAB H Y} {π : X ⟶ Y} {f : X' ⟶ X} {U : X.Opens} {hU : IsAffineOpen U}
    {U' : X'.Opens} {hU' : IsAffineOpen U'} (le : U' ≤ f ⁻¹ᵁ U) {κ : Type} [Finite κ]
    (b : Module.Basis κ Γ(X, U) (TanM (tau hU ≫ π) t.G)) {S : Type} [CommRing S] (w : Sp S ⟶ X')
    (hw : ⊤ ≤ w ⁻¹ᵁ U') {x : Sp S ⟶ Y}
    (e₀ : spMap (ev (tau hU' ≫ f) U (le_preimage_map f le (tau_le hU' le_rfl))) ≫ tau hU ≫ π = tau hU' ≫ f ≫ π)
    (e₁ : spMap (ev w U' hw) ≫ tau hU' ≫ f ≫ π = x)
    (e₂ : spMap (ev (w ≫ f) U (le_preimage_map f le hw)) ≫ tau hU ≫ π = x) (i : κ) :
    tanPull (ev w U' hw) e₁ (basPull _ e₀ b i) = basPull _ e₂ b i := by
  have h1 : spMap (ev w U' hw) ≫ tau hU' ≫ f = w ≫ f := by rw [← Category.assoc, tau, spMap_ev]
  have h2 : (ev w U' hw).comp (ev (tau hU' ≫ f) U (le_preimage_map f le (tau_le hU' le_rfl))) =
      ev (w ≫ f) U (le_preimage_map f le hw) := by
    rw [← ev_spMap _ _ _ _ (h1 ▸ le_preimage_map f le hw)]
    exact FlagMod.ev_congr h1 _ _ _
  rw [basPull_apply, basPull_apply, tanPull_tanPull _ _ _ _ (by rw [h2]; exact e₂)]
  apply tan_ext
  rw [FlagMod.tanPull_left, FlagMod.tanPull_left, h2]

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F} {M : Model Xo c V.subtype}
  {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ} {A : Atlas M π ty} {σ : E →+* ℂ} {k : ℕ}

theorem flag_data {D : Adapted A σ k} {hk : k < Dw.mult σ} {X' : Scheme.{0}} {f : X' ⟶ X} {L : D.C.Line f}
    {ty' : (E →+* ℂ) → Finset ℕ} {A' : Atlas M (f ≫ π) ty'} (h : StepRel D hk L A') (β : L.J) {K : Type} [Field K]
    (w : Sp K ⟶ X') (hw : ⊤ ≤ w ⁻¹ᵁ L.B β) {x : Sp K ⟶ M.X} (e : (w ≫ f) ≫ π = x)
    (e₂ : spMap (ev (w ≫ f) _ (le_preimage_map f (L.le β) hw)) ≫ tau (D.C.aff (L.a β)) ≫ π = x)
    (u : TVecs Dw M.t x) (hu : A'.FlagAt w (up u)) :
    (∀ j ≤ k, initSpan K (u σ) j = initSpan K (fun i : Fin k => basPull _ e₂ (D.b (L.a β)) (.inl i)) j) ∧
      ∃ e : Kˣ, ∀ i, (basPull _ e₂ (D.b (L.a β))).repr (u σ ⟨k, hk⟩) (.inr i) = (e : K) * ev w _ hw (L.η β i) := by
  subst e
  obtain ⟨h1, h2⟩ := (h K w u).1 hu
  refine ⟨D.int (L.a β) K (w ≫ f) _ u h1, ?_⟩
  obtain ⟨e, he⟩ := h2 (L.a β) (le_preimage_map f (L.le β) hw) β hw
  rw [Coc.tr_self, Matrix.one_mulVec] at he
  exact ⟨e, fun i => congrFun he i⟩

theorem intStep_succ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F)
    [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X)
    (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ) (D : Adapted A σ k) (hk : k < Dw.mult σ)
    (X' : Scheme.{0}) (f : X' ⟶ X) (L : D.C.Line f) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas M (f ≫ π) ty')
    (h : StepRel D hk L A') : IntStep A' σ (k + 1) := by
  intro x
  obtain ⟨β, hx⟩ := L.cover x
  obtain ⟨c₀, hc⟩ := L.unit β
  have e₀ : spMap (ev (tau (L.aff β) ≫ f) _ (le_preimage_map f (L.le β) (tau_le (L.aff β) le_rfl))) ≫
      tau (D.C.aff (L.a β)) ≫ π = tau (L.aff β) ≫ f ≫ π := by
    rw [← Category.assoc, tau.eq_1 (D.C.aff (L.a β)), spMap_ev, Category.assoc]
  obtain ⟨m, b', h1, h2⟩ := exists_basis_succ (basPull _ e₀ (D.b (L.a β))) (L.η β) c₀ hc
  refine ⟨L.B β, L.aff β, m, b', hx, fun K _ w hw u hu => ?_⟩
  have e₂ : spMap (ev (w ≫ f) _ (le_preimage_map f (L.le β) hw)) ≫ tau (D.C.aff (L.a β)) ≫ π = w ≫ f ≫ π := by
    rw [← Category.assoc, tau, spMap_ev, Category.assoc]
  obtain ⟨g1, e, g2⟩ := flag_data h β w hw (Category.assoc _ _ _) e₂ u hu
  refine initSpan_step _ _ (u σ) hk g1 e g2 _ (fun i => ?_) ?_
  · rw [basAt, basPull_apply, h1]
    exact tanPull_basPull (L.le β) _ w hw e₀ _ e₂ _
  · rw [basAt, basPull_apply, h2, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smulₛₗ, tanPull_basPull (L.le β) _ w hw e₀ _ e₂ _]

end GlobalTheory.DRFlag.StepInt
