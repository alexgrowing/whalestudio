import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.FrSub

section Lin

variable {K N : Type} [Field K] [AddCommGroup N] [Module K N]

theorem repr_inr_eq_zero_iff {k m : ℕ} (b : Module.Basis (Fin k ⊕ Fin m) K N) (v : N) :
    (∀ j, b.repr v (.inr j) = 0) ↔ v ∈ initSpan K (fun i : Fin k => b (.inl i)) k := by
  have h : initSpan K (fun i : Fin k => b (.inl i)) k = Submodule.span K (b '' Set.range Sum.inl) := by
    rw [initSpan, ← Set.range_comp]
    congr 1
    ext x
    exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, i.2, hi⟩⟩
  rw [h, Module.Basis.mem_span_image]
  constructor
  · rintro h (i | j) hi
    · exact ⟨i, rfl⟩
    · exact absurd (h j) (Finsupp.mem_support_iff.1 hi)
  · intro h j
    by_contra hne
    obtain ⟨i, hi⟩ := h (Finsupp.mem_support_iff.2 hne)
    exact Sum.inl_ne_inr hi

variable {n m k r : ℕ} (q : N →ₗ[K] (Fin m → K)) {u : Fin n → N} (hj : k + r + 1 ≤ n)

theorem eq_zero_of_sum (hu : LinearIndependent K u) (hq : ∀ v, q v = 0 → v ∈ initSpan K u k) (c : Fin (r + 1) → K)
    (hc : ∑ i, c i • q (u ⟨k + i, by omega⟩) = 0) : c = 0 := by
  let e : Fin (r + 1) → Fin n := fun i => ⟨k + i, by omega⟩
  have he : Function.Injective e := fun i i' h => Fin.ext (by have := congrArg Fin.val h; simp only [e] at this; omega)
  have h1 : ∑ i, c i • u (e i) ∈ initSpan K u k := hq _ (by simpa only [map_sum, map_smul] using hc)
  have h2 : ∑ i, c i • u (e i) ∈ Submodule.span K (u '' {j : Fin n | k ≤ (j : ℕ)}) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨e i, Nat.le_add_right _ _, rfl⟩)
  have hd : Disjoint {j : Fin n | (j : ℕ) < k} {j : Fin n | k ≤ (j : ℕ)} :=
    Set.disjoint_left.2 fun j h h' => (not_lt.2 (show k ≤ (j : ℕ) from h')) (show (j : ℕ) < k from h)
  have h3 := Submodule.disjoint_def.1 (hu.disjoint_span_image hd) _ h1 h2
  exact funext (Fintype.linearIndependent_iff.1 (hu.comp e he) c h3)

theorem exists_sum (hq : ∀ v ∈ initSpan K u k, q v = 0) {v : N} (hv : v ∈ initSpan K u (k + r + 1)) :
    ∃ c : Fin (r + 1) → K, ∑ i, c i • q (u ⟨k + i, by omega⟩) = q v := by
  rw [← Submodule.mem_span_range_iff_exists_fun]
  refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap q _)).2 ?_ hv)
  rintro _ ⟨j, hj', rfl⟩
  have hj'' : (j : ℕ) < k + r + 1 := hj'
  show q (u j) ∈ Submodule.span K _
  by_cases h : (j : ℕ) < k
  · rw [hq _ (Submodule.subset_span ⟨j, h, rfl⟩)]
    exact Submodule.zero_mem _
  · refine Submodule.subset_span ⟨⟨j - k, by omega⟩, ?_⟩
    have : (⟨k + (j - k), by omega⟩ : Fin n) = j := Fin.ext (by simp only; omega)
    simp only [this]

theorem initSpan_full (u : Fin n → N) : initSpan K u n = Submodule.span K (Set.range u) := by
  rw [initSpan]
  congr 1
  ext x
  exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, i.2, hi⟩⟩

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F} {M : Model Xo c V.subtype}
  {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ} {A : Atlas M π ty} {σ : E →+* ℂ} {k : ℕ}

def crdL {m : ℕ} {U : X.Opens} {hU : IsAffineOpen U}
    (b : Module.Basis (Fin k ⊕ Fin m) Γ(X, U) (TanM (tau hU ≫ π) M.t.G)) {S : Type} [CommRing S] (z : Sp S ⟶ X)
    (h : ⊤ ≤ z ⁻¹ᵁ U) : TanM (z ≫ π) M.t.G →ₗ[S] (Fin m → S) :=
  LinearMap.pi fun j => (basAt b z h).coord (.inr j)

theorem crdL_apply {m : ℕ} {U : X.Opens} {hU : IsAffineOpen U}
    (b : Module.Basis (Fin k ⊕ Fin m) Γ(X, U) (TanM (tau hU ≫ π) M.t.G)) {S : Type} [CommRing S] (z : Sp S ⟶ X)
    (h : ⊤ ≤ z ⁻¹ᵁ U) (v : TanM (z ≫ π) M.t.G) : crdL b z h v = crd b z h v := rfl

theorem crdL_eq_zero_iff (D : Adapted A σ k) (α : D.C.A) {K : Type} [Field K] (z : Sp K ⟶ X)
    (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α) {u : TVecs Dw M.t (z ≫ π)} (hu : A.FlagAt z (up u)) (v : TanM (z ≫ π) M.t.G) :
    crdL (D.b α) z h v = 0 ↔ v ∈ initSpan K (u σ) k := by
  rw [D.int α K z h u hu k le_rfl, ← repr_inr_eq_zero_iff]
  exact funext_iff

theorem exists_isFrSub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k r : ℕ) (D : Adapted A σ k) (hj : k + r + 1 ≤ Dw.mult σ), (k + r + 1 ∈ ty σ ∨ k + r + 1 = Dw.mult σ) → ∀ α : A.ch.ι → D.C.A, (∀ a, ⊤ ≤ A.ch.χ a ⁻¹ᵁ D.C.B (α a)) → ∃ Sb : D.C.Sub A.ch r, IsFrSub D Sb hj := by
  intro E _ _ _ H Dw l Xo c V _ M X π ty A σ k r D hj hty α hα
  choose u hu using fun a => exists_up (Dw := Dw) (x := A.ch.χ a ≫ π) fun σ i => ((A.frame a).1 σ i).1
  let Mx : ∀ a, Matrix (Fin (D.C.n (α a))) (Fin (r + 1)) (A.ch.R a) := fun a j i =>
    crd (D.b (α a)) (A.ch.χ a) (hα a) (u a σ ⟨k + i, by omega⟩) j
  have key : ∀ (a : A.ch.ι) (S : Type) [CommRing S] (φ : A.ch.R a →+* S) (z : Sp S ⟶ X), spMap φ ≫ A.ch.χ a = z →
      ∀ (h : ⊤ ≤ z ⁻¹ᵁ D.C.B (α a)) (w : TVecs Dw M.t (z ≫ π)), up w = (A.fr a).bc φ →
      ∀ i : Fin (r + 1), (fun j => φ (Mx a j i)) = crd (D.b (α a)) z h (w σ ⟨k + i, by omega⟩) := by
    intro a S _ φ z e h w hw i
    have e' : spMap φ ≫ A.ch.χ a ≫ π = z ≫ π := by rw [← Category.assoc, e]
    have hw' : w = fun σ i => tanPull φ e' (u a σ i) := up_injective (by rw [hw, up_tanPull, hu])
    subst hw'
    funext j
    exact (basAt_repr (D.b (α a)) φ (A.ch.χ a) (hα a) e h e' _ _).symm
  have mul : ∀ (a : A.ch.ι) (K : Type) [Field K] (φ : A.ch.R a →+* K) (z : Sp K ⟶ X), spMap φ ≫ A.ch.χ a = z →
      ∀ (h : ⊤ ≤ z ⁻¹ᵁ D.C.B (α a)) (w : TVecs Dw M.t (z ≫ π)), up w = (A.fr a).bc φ →
      ∀ cf : Fin (r + 1) → K, ((Mx a).map φ).mulVec cf =
        ∑ i, cf i • crdL (D.b (α a)) z h (w σ ⟨k + i, by omega⟩) := by
    intro a K _ φ z e h w hw cf
    funext j
    simp only [crdL_apply, ← key a K φ z e h w hw, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, mul_comm]
  refine ⟨⟨α, hα, Mx, fun a K _ φ => ?_, fun a a' K _ φ φ' z e e' h h' => ?_⟩, key⟩
  · have h : ⊤ ≤ (spMap φ ≫ A.ch.χ a) ⁻¹ᵁ D.C.B (α a) := fun x _ => hα a (Set.mem_univ (spMap φ x))
    obtain ⟨w, hw⟩ := A.exists_up_fr (φ := φ) rfl
    have hf := A.isFrame_bc (φ := φ) rfl
    have hF := A.flagAt_fr (φ := φ) rfl
    rw [← hw] at hf hF
    refine (injective_iff_map_eq_zero ((Mx a).map φ).mulVecLin).2 fun cf hc => ?_
    refine eq_zero_of_sum (crdL (D.b (α a)) _ h) hj ((isFrame_up_iff _ _).1 hf σ).1
      (fun v hv => (crdL_eq_zero_iff D _ _ h hF v).1 hv) cf ?_
    rw [← mul a K φ _ rfl h w hw]
    exact hc
  · obtain ⟨w, hw⟩ := A.exists_up_fr e
    obtain ⟨w', hw'⟩ := A.exists_up_fr e'
    have hf := A.isFrame_bc e
    have hF := A.flagAt_fr e
    have hf' := A.isFrame_bc e'
    have hF' := A.flagAt_fr e'
    rw [← hw] at hf hF
    rw [← hw'] at hf' hF'
    have hs : initSpan K (w' σ) (k + r + 1) = initSpan K (w σ) (k + r + 1) := by
      rcases hty with hty | hty
      · exact hF'.initSpan_eq hF σ hty
      · rw [← A.alg_eq e e'] at hf'
        rw [hty, initSpan_full, initSpan_full, ((isFrame_up_iff _ _).1 hf σ).2, ((isFrame_up_iff _ _).1 hf' σ).2]
    have hm : ∀ i : Fin (r + 1), w' σ ⟨k + i, by omega⟩ ∈ initSpan K (w σ) (k + r + 1) := fun i =>
      hs ▸ Submodule.subset_span ⟨_, by show k + (i : ℕ) < k + r + 1; omega, rfl⟩
    choose cf hcf using fun i => exists_sum (crdL (D.b (α a)) z h) hj
      (fun v hv => (crdL_eq_zero_iff D _ _ h hF v).2 hv) (hm i)
    refine ⟨Matrix.of fun p i => cf i p, ?_⟩
    ext j i
    have h1 := D.coord (α a) (α a') K z h h' (w' σ ⟨k + i, by omega⟩)
    rw [← key a' K φ' z e' h' w' hw' i, ← crdL_apply, ← hcf i, ← mul a K φ z e h w hw] at h1
    exact congrFun h1 j

end GlobalTheory.DRFlag.FrSub
