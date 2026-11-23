import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.AbLaw.CechOne
open SecOn
variable {X : Scheme.{0}} {R : Type} [CommRing R]

def IsCocycle (M : LB X) {I : Type} (O : I → X.Opens) (φ : ∀ a b, SecOn M (O a ⊓ O b)) : Prop :=
  ∀ a b d (W : X.Opens) (ha : W ≤ O a) (hb : W ≤ O b) (hd : W ≤ O d),
    restrict M (le_inf ha hb) (φ a b) + restrict M (le_inf hb hd) (φ b d) =
      restrict M (le_inf ha hd) (φ a d)

def IsCoboundary (M : LB X) {I : Type} (O : I → X.Opens) (φ : ∀ a b, SecOn M (O a ⊓ O b)) : Prop :=
  ∃ ψ : ∀ a, SecOn M (O a), ∀ a b,
    φ a b = restrict M inf_le_left (ψ a) - restrict M inf_le_right (ψ b)

def CechHOneVanishesOnOpen (M : LB X) (V : X.Opens) : Prop :=
  ∀ (I : Type) (O : I → X.Opens), (∀ a, O a ≤ V) → V ≤ ⨆ a, O a →
    ∀ φ : ∀ a b, SecOn M (O a ⊓ O b), IsCocycle M O φ → IsCoboundary M O φ

variable {M : LB X}

theorem le_iSup_inf {J : Type} {P : J → X.Opens} {W : X.Opens} (h : W ≤ ⨆ k, P k) :
    W ≤ ⨆ k, W ⊓ P k := by
  rw [← inf_iSup_eq]; exact le_inf le_rfl h

theorem isCoboundary_of_refine {I J : Type} {O : I → X.Opens} {φ : ∀ a b, SecOn M (O a ⊓ O b)}
    (hφ : IsCocycle M O φ) (P : J → X.Opens) (τ : J → I) (hP : ∀ k, P k ≤ O (τ k))
    (hc : ∀ a, O a ≤ ⨆ k, P k) (ψ' : ∀ k, SecOn M (P k))
    (h : ∀ k l, restrict M (inf_le_inf (hP k) (hP l)) (φ (τ k) (τ l)) =
      restrict M inf_le_left (ψ' k) - restrict M inf_le_right (ψ' l)) :
    IsCoboundary M O φ := by
  have hglue : ∀ a, ∃ ψ : SecOn M (O a), ∀ k, restrict M (inf_le_left : O a ⊓ P k ≤ O a) ψ =
      restrict M (inf_le_inf le_rfl (hP k)) (φ a (τ k)) + restrict M inf_le_right (ψ' k) := by
    intro a
    refine (existsUnique_glue (fun k => O a ⊓ P k) (fun k => inf_le_left) (le_iSup_inf (hc a))
      _ fun k l => ?_).exists
    have hk : O a ⊓ P k ⊓ (O a ⊓ P l) ≤ P k := inf_le_left.trans inf_le_right
    have hl : O a ⊓ P k ⊓ (O a ⊓ P l) ≤ P l := inf_le_right.trans inf_le_right
    have ha : O a ⊓ P k ⊓ (O a ⊓ P l) ≤ O a := inf_le_left.trans inf_le_left
    have h1 := congrArg (restrict M (le_inf hk hl)) (h k l)
    have h2 := hφ a (τ k) (τ l) _ ha (hk.trans (hP k)) (hl.trans (hP l))
    simp only [map_add, map_sub, restrict_restrict] at h1 h2 ⊢
    rw [← h2, h1]
    abel
  choose ψ hψ using hglue
  refine ⟨ψ, fun a b => ext_of_cover (fun k => O a ⊓ O b ⊓ P k) (fun k => inf_le_left)
    (le_iSup_inf (inf_le_left.trans (hc a))) fun k => ?_⟩
  have ha : O a ⊓ O b ⊓ P k ≤ O a := inf_le_left.trans inf_le_left
  have hb : O a ⊓ O b ⊓ P k ≤ O b := inf_le_left.trans inf_le_right
  have hk : O a ⊓ O b ⊓ P k ≤ P k := inf_le_right
  have h1 := congrArg (restrict M (le_inf ha hk)) (hψ a k)
  have h2 := congrArg (restrict M (le_inf hb hk)) (hψ b k)
  have h3 := hφ a b (τ k) _ ha hb (hk.trans (hP k))
  simp only [map_add, map_sub, restrict_restrict] at h1 h2 h3 ⊢
  rw [h1, h2, ← h3]
  abel

theorem h1Zero_iff (hM : M.IsLB) : FirstCohomologyVanishes M ↔ CechHOneVanishesOnOpen M ⊤ := by
  constructor
  · intro H I O _ hc φ hφ
    have hc' : ⨆ p : I × M.ι, O p.1 ⊓ M.U p.2 = ⊤ := by
      refine top_unique (hc.trans (iSup_le fun a => (le_iSup_inf (hM.cover.ge.trans' le_top)).trans
        (iSup_le fun i => le_iSup (fun p : I × M.ι => O p.1 ⊓ M.U p.2) (a, i))))
    obtain ⟨ψ, hψ⟩ := H (I × M.ι) (fun p => O p.1 ⊓ M.U p.2) Prod.snd (fun _ => inf_le_right) hc'
      (fun p q => chart hM p.2 (inf_le_left.trans inf_le_right)
        (restrict M (inf_le_inf inf_le_left inf_le_left) (φ p.1 q.1))) (by
      intro p q r
      rw [← chart_restrict, ← chart_restrict, ← chart_restrict,
        ← chart_change hM p.2 q.2 ((inf_le_left.trans inf_le_left).trans inf_le_right), ← map_add]
      simp only [restrict_restrict]
      exact congrArg _ (hφ p.1 q.1 r.1 _ ((inf_le_left.trans inf_le_left).trans inf_le_left)
        ((inf_le_left.trans inf_le_right).trans inf_le_left) (inf_le_right.trans inf_le_left)))
    refine isCoboundary_of_refine hφ (fun p : I × M.ι => O p.1 ⊓ M.U p.2) Prod.fst
      (fun _ => inf_le_left) (fun _ => le_top.trans hc'.ge)
      (fun p => (chart hM p.2 inf_le_right).symm (ψ p)) fun p q => ?_
    apply (chart hM p.2 (inf_le_left.trans inf_le_right)).injective
    rw [map_sub, chart_restrict hM p.2 inf_le_right, LinearEquiv.apply_symm_apply,
      chart_change hM p.2 q.2 _ (inf_le_right.trans inf_le_right) (restrict M inf_le_right _),
      chart_restrict hM q.2 inf_le_right,
      LinearEquiv.apply_symm_apply]
    exact hψ p q
  · intro H I V c hV hc φ hφ
    obtain ⟨ψ, hψ⟩ := H I V (fun _ => le_top) hc.ge
      (fun a b => (chart hM (c a) (inf_le_left.trans (hV a))).symm (φ a b)) (by
      intro a b d W ha hb hd
      apply (chart hM (c a) (ha.trans (hV a))).injective
      have h := congrArg (rs X (le_inf (le_inf ha hb) hd)) (hφ a b d)
      simp only [map_add, map_mul, rs_rs] at h
      rw [map_add, chart_restrict hM (c a) (inf_le_left.trans (hV a)),
        chart_change hM (c a) (c b) _ (hb.trans (hV b)),
        chart_restrict hM (c b) (inf_le_left.trans (hV b)),
        chart_restrict hM (c a) (inf_le_left.trans (hV a))]
      simpa only [LinearEquiv.apply_symm_apply] using h)
    refine ⟨fun a => chart hM (c a) (hV a) (ψ a), fun a b => ?_⟩
    have h := (LinearEquiv.symm_apply_eq _).1 (hψ a b)
    rw [h, map_sub, chart_restrict hM (c a) (hV a),
      chart_change hM (c a) (c b) _ (inf_le_right.trans (hV b)), chart_restrict hM (c b) (hV b)]

theorem cechHOneVanishesOnOpen_of_cover {κ : Type} {D : κ → X.Opens} {V : X.Opens} (hD : ∀ i, D i ≤ V)
    (hc : V ≤ ⨆ i, D i) (h1 : ∀ i, CechHOneVanishesOnOpen M (D i))
    (h2 : ∀ θ : ∀ i j, SecOn M (D i ⊓ D j), IsCocycle M D θ → IsCoboundary M D θ) :
    CechHOneVanishesOnOpen M V := by
  intro I O hO hcO φ hφ
  choose σ hσ using fun i => h1 i I (fun a => D i ⊓ O a) (fun _ => inf_le_left)
    (le_iSup_inf ((hD i).trans hcO))
    (fun a b => restrict M (inf_le_inf inf_le_right inf_le_right) (φ a b)) (by
      intro a b d W ha hb hd
      simp only [restrict_restrict]
      exact hφ a b d W (ha.trans inf_le_right) (hb.trans inf_le_right) (hd.trans inf_le_right))
  have hσ' : ∀ i a b (W : X.Opens) (hi : W ≤ D i) (ha : W ≤ O a) (hb : W ≤ O b),
      restrict M (le_inf ha hb) (φ a b) =
        restrict M (le_inf hi ha) (σ i a) - restrict M (le_inf hi hb) (σ i b) := by
    intro i a b W hi ha hb
    have h := congrArg (restrict M (le_inf (le_inf hi ha) (le_inf hi hb))) (hσ i a b)
    simpa only [map_sub, restrict_restrict] using h
  have hglue : ∀ i j, ∃ θ : SecOn M (D i ⊓ D j), ∀ a,
      restrict M (inf_le_left : D i ⊓ D j ⊓ O a ≤ D i ⊓ D j) θ =
        restrict M (inf_le_inf_right _ inf_le_left) (σ i a) -
          restrict M (inf_le_inf_right _ inf_le_right) (σ j a) := by
    intro i j
    refine (existsUnique_glue (fun a => D i ⊓ D j ⊓ O a) (fun a => inf_le_left)
      (le_iSup_inf ((inf_le_left.trans (hD i)).trans hcO)) _ fun a b => ?_).exists
    have ha : D i ⊓ D j ⊓ O a ⊓ (D i ⊓ D j ⊓ O b) ≤ O a := inf_le_left.trans inf_le_right
    have hb : D i ⊓ D j ⊓ O a ⊓ (D i ⊓ D j ⊓ O b) ≤ O b := inf_le_right.trans inf_le_right
    have e1 := hσ' i a b _ (inf_le_left.trans (inf_le_left.trans inf_le_left)) ha hb
    have e2 := hσ' j a b _ (inf_le_left.trans (inf_le_left.trans inf_le_right)) ha hb
    simp only [map_sub, restrict_restrict]
    rw [sub_eq_sub_iff_sub_eq_sub, ← e1, ← e2]
  choose θ hθ using hglue
  have hθ' : ∀ i j a (W : X.Opens) (hi : W ≤ D i) (hj : W ≤ D j) (ha : W ≤ O a),
      restrict M (le_inf hi hj) (θ i j) =
        restrict M (le_inf hi ha) (σ i a) - restrict M (le_inf hj ha) (σ j a) := by
    intro i j a W hi hj ha
    have h := congrArg (restrict M (le_inf (le_inf hi hj) ha)) (hθ i j a)
    simpa only [map_sub, restrict_restrict] using h
  obtain ⟨ξ, hξ⟩ := h2 θ (by
    intro i j k W hi hj hk
    refine ext_of_cover (fun a => W ⊓ O a) (fun a => inf_le_left)
      (le_iSup_inf ((hi.trans (hD i)).trans hcO)) fun a => ?_
    simp only [map_add, restrict_restrict]
    rw [hθ' i j a _ (inf_le_left.trans hi) (inf_le_left.trans hj) inf_le_right,
      hθ' j k a _ (inf_le_left.trans hj) (inf_le_left.trans hk) inf_le_right,
      hθ' i k a _ (inf_le_left.trans hi) (inf_le_left.trans hk) inf_le_right]
    abel)
  refine isCoboundary_of_refine hφ (fun p : κ × I => D p.1 ⊓ O p.2) Prod.snd (fun _ => inf_le_right)
    (fun a => (le_iSup_inf ((hO a).trans hc)).trans (iSup_le fun i =>
      (le_inf inf_le_right inf_le_left).trans (le_iSup (fun p : κ × I => D p.1 ⊓ O p.2) (i, a))))
    (fun p => σ p.1 p.2 - restrict M inf_le_left (ξ p.1)) fun p q => ?_
  have hi : D p.1 ⊓ O p.2 ⊓ (D q.1 ⊓ O q.2) ≤ D p.1 := inf_le_left.trans inf_le_left
  have hj : D p.1 ⊓ O p.2 ⊓ (D q.1 ⊓ O q.2) ≤ D q.1 := inf_le_right.trans inf_le_left
  have ha : D p.1 ⊓ O p.2 ⊓ (D q.1 ⊓ O q.2) ≤ O p.2 := inf_le_left.trans inf_le_right
  have hb : D p.1 ⊓ O p.2 ⊓ (D q.1 ⊓ O q.2) ≤ O q.2 := inf_le_right.trans inf_le_right
  have e1 := hσ' p.1 p.2 q.2 _ hi ha hb
  have e2 := hθ' p.1 q.1 q.2 _ hi hj hb
  have e3 := congrArg (restrict M (le_inf hi hj)) (hξ p.1 q.1)
  simp only [map_sub, restrict_restrict] at e3 ⊢
  rw [e1, sub_sub_sub_comm, ← e3, e2]
  abel

theorem exists_extend (hM : M.IsLB) {V U W : X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ V) (i : M.ι)
    (hi : U ≤ M.U i) (t : Γ(X, V)) (hW : W = U ⊓ X.basicOpen t) (φ : SecOn M W) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ ρ : SecOn M U, restrict M (hW.le.trans inf_le_left) ρ =
      rs X ((hW.le.trans inf_le_left).trans hUV) t ^ n • φ := by
  have e : W = X.basicOpen (rs X hUV t) := by rw [hW]; exact (X.basicOpen_res t _).symm
  subst e
  have := hU.isLocalization_basicOpen (rs X hUV t)
  obtain ⟨⟨ρ, _, n₀, rfl⟩, h⟩ := IsLocalization.surj (Submonoid.powers (rs X hUV t))
    (chart hM i ((X.basicOpen_le _).trans hi) φ)
  refine ⟨n₀, fun n hn => ⟨(chart hM i hi).symm (rs X hUV t ^ (n - n₀) * ρ), ?_⟩⟩
  have h' : chart hM i ((X.basicOpen_le _).trans hi) φ * rs X (X.basicOpen_le _) (rs X hUV t ^ n₀) =
      rs X (X.basicOpen_le _) ρ := h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  apply (chart hM i ((X.basicOpen_le _).trans hi)).injective
  rw [chart_restrict hM i hi, LinearEquiv.apply_symm_apply, map_smul, smul_eq_mul,
    map_mul, ← h', map_pow, map_pow, rs_rs, Nat.add_sub_cancel_left]
  ring

theorem exists_kill (hM : M.IsLB) {V U W : X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ V) (i : M.ι)
    (hi : U ≤ M.U i) (t : Γ(X, V)) (hW : W = U ⊓ X.basicOpen t) (φ : SecOn M U)
    (h : restrict M (hW.le.trans inf_le_left) φ = 0) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → rs X hUV t ^ n • φ = 0 := by
  have e : W = X.basicOpen (rs X hUV t) := by rw [hW]; exact (X.basicOpen_res t _).symm
  subst e
  have := hU.isLocalization_basicOpen (rs X hUV t)
  have h₁ := congrArg (chart hM i ((X.basicOpen_le _).trans hi)) h
  rw [chart_restrict hM i hi, map_zero] at h₁
  obtain ⟨⟨_, n₀, rfl⟩, h'⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (rs X hUV t))
    Γ(X, X.basicOpen (rs X hUV t)) _).1 h₁
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  apply (chart hM i hi).injective
  simp only at h'
  rw [map_smul, smul_eq_mul, map_zero]
  linear_combination rs X hUV t ^ d * h'

theorem cechHOneVanishesOnOpen_of_isAffineOpen (hM : M.IsLB) {V : X.Opens} (hT : IsAffineOpen V) :
    CechHOneVanishesOnOpen M V := by
  classical
  intro I O hO hc φ hφ
  have hex : ∀ x : V, ∃ (t : Γ(X, V)) (a : I) (i : M.ι),
      X.basicOpen t ≤ O a ⊓ M.U i ∧ x.1 ∈ X.basicOpen t := by
    intro x
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc x.2)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ x.1))
    obtain ⟨t, h1, h2⟩ := hT.exists_basicOpen_le (V := O a ⊓ M.U i) ⟨x, ha, hi⟩ x.2
    exact ⟨t, a, i, h1, h2⟩
  choose t₀ τ₀ c₀ ht₀ hx₀ using hex
  obtain ⟨S, hS⟩ := hT.isCompact.elim_finite_subcover (fun x : V => (X.basicOpen (t₀ x) : Set X))
    (fun x => (X.basicOpen (t₀ x)).isOpen) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hx₀ ⟨x, hx⟩⟩)
  let t : S → Γ(X, V) := fun k => t₀ k
  let τ : S → I := fun k => τ₀ k
  let D : S → X.Opens := fun k => X.basicOpen (t k)
  have hD : ∀ k, D k ≤ O (τ k) := fun k => (ht₀ k).trans inf_le_left
  have hDU : ∀ k : S, D k ≤ M.U (c₀ k) := fun k => (ht₀ k).trans inf_le_right
  have hDV : ∀ k, D k ≤ V := fun k => X.basicOpen_le _
  have hDc : V ≤ ⨆ k, D k := fun x hx => by
    obtain ⟨k, hk, hx⟩ := Set.mem_iUnion₂.1 (hS hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨k, hk⟩, hx⟩
  have hspan : Ideal.span (Set.range t) = ⊤ := by
    rw [← hT.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun f => X.basicOpen_le _) (hDc.trans (iSup_le fun k => ?_))
    exact le_iSup (fun f : Set.range t => X.basicOpen (f : Γ(X, V))) ⟨t k, k, rfl⟩
  have hA : ∀ k, IsAffineOpen (D k) := fun k => hT.basicOpen _
  have hA₂ : ∀ k l, IsAffineOpen (D k ⊓ D l) := fun k l => by
    rw [← X.basicOpen_mul]; exact hT.basicOpen _
  choose n₁ hn₁ using fun k l => exists_extend hM (hA k) (hDV k) _ (hDU k) (t l) rfl
    (restrict M (inf_le_inf (hD k) (hD l)) (φ (τ k) (τ l)))
  obtain ⟨a₁, ha₁⟩ := (Set.finite_range fun p : S × S => n₁ p.1 p.2).bddAbove
  choose ρ hρ using fun k l => hn₁ k l a₁ (ha₁ ⟨(k, l), rfl⟩)
  have hk : ∀ k l m, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      rs X (inf_le_left.trans (hDV k) : D k ⊓ D l ≤ V) (t m) ^ n •
      (restrict M inf_le_left (ρ k m) - restrict M (inf_le_right : D k ⊓ D l ≤ D l) (ρ l m) -
        rs X (inf_le_left.trans (hDV k) : D k ⊓ D l ≤ V) (t m) ^ a₁ •
          restrict M (inf_le_inf (hD k) (hD l)) (φ (τ k) (τ l))) = 0 := by
    intro k l m
    refine exists_kill hM (hA₂ k l) _ _ (inf_le_left.trans (hDU k)) (t m) rfl _ ?_
    have h1 := congrArg (restrict M (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      D k ⊓ D l ⊓ D m ≤ D k ⊓ D m)) (hρ k m)
    have h2 := congrArg (restrict M (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      D k ⊓ D l ⊓ D m ≤ D l ⊓ D m)) (hρ l m)
    have h3 := hφ (τ k) (τ l) (τ m) (D k ⊓ D l ⊓ D m) ((inf_le_left.trans inf_le_left).trans (hD k))
      ((inf_le_left.trans inf_le_right).trans (hD l)) (inf_le_right.trans (hD m))
    simp only [map_smulₛₗ, map_sub, map_pow, rs_rs, restrict_restrict] at h1 h2 h3 ⊢
    rw [h1, h2, ← h3, smul_add]
    abel
  choose n₂ hn₂ using hk
  obtain ⟨a₂, ha₂⟩ := (Set.finite_range fun p : S × S × S => n₂ p.1 p.2.1 p.2.2).bddAbove
  have hspan' : (1 : Γ(X, V)) ∈ Ideal.span (Set.range fun k => t k ^ (a₂ + a₁)) := by
    have := Ideal.span_pow_eq_top _ hspan (a₂ + a₁)
    rw [← Set.range_comp] at this
    exact this.ge trivial
  obtain ⟨h, hh⟩ := Ideal.mem_span_range_iff_exists_fun.1 hspan'
  refine isCoboundary_of_refine hφ D τ hD (fun a => (hO a).trans hDc)
    (fun k => ∑ m, rs X (hDV k) (h m * t m ^ a₂) • ρ k m) fun k l => ?_
  have h1 := congrArg (rs X (inf_le_left.trans (hDV k) : D k ⊓ D l ≤ V)) hh
  simp only [map_sum, map_smulₛₗ, map_mul, map_pow, map_one, rs_rs] at h1 ⊢
  rw [← Finset.sum_sub_distrib, ← one_smul Γ(X, D k ⊓ D l) (restrict M _ (φ (τ k) (τ l))), ← h1,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h2 := hn₂ k l m a₂ (ha₂ ⟨(k, l, m), rfl⟩)
  rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at h2
  rw [← smul_sub, mul_smul, mul_smul, h2]

theorem add_eq_of_ordered {κ G : Type} [LinearOrder κ] [AddCommGroup G] (F : κ → κ → G)
    (h0 : ∀ a, F a a = 0) (hs : ∀ a b, F b a = -F a b)
    (h : ∀ a b c, a < b → b < c → F a b + F b c = F a c) (a b c : κ) : F a b + F b c = F a c := by
  have key : ∀ a b c, a < b → F a b + F b c = F a c := by
    intro a b c hab
    rcases lt_trichotomy b c with hbc | rfl | hbc
    · exact h a b c hab hbc
    · rw [h0, add_zero]
    · rcases lt_trichotomy a c with hac | rfl | hac
      · rw [← h a c b hac hbc, hs c b]; abel
      · rw [h0, hs a b]; abel
      · rw [hs c b, hs c a, ← h c a b hac hab]; abel
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact key a b c hab
  · rw [h0, zero_add]
  · rw [← key b a c hab, hs b a]; abel

theorem exists_triple {κ : Type} [LinearOrder κ] {t : Finset κ} (ht : t.card = 3) :
    ∃ i j k, i < j ∧ j < k ∧ t = {i, j, k} := by
  refine ⟨t.orderEmbOfFin ht 0, t.orderEmbOfFin ht 1, t.orderEmbOfFin ht 2,
    (t.orderEmbOfFin ht).strictMono (by decide), (t.orderEmbOfFin ht).strictMono (by decide), ?_⟩
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨n, rfl⟩ := (Finset.range_orderEmbOfFin t ht).ge (Finset.mem_coe.2 hx)
    fin_cases n <;> simp
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> exact Finset.orderEmbOfFin_mem _ _ _

theorem exists_pair {κ : Type} [LinearOrder κ] {t : Finset κ} (ht : t.card = 2) :
    ∃ i j, i < j ∧ t = {i, j} := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 ht
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨i, j, h, rfl⟩
  · exact ⟨j, i, h, Finset.pair_comm _ _⟩

theorem d_two_apply_triple {κ : Type} [LinearOrder κ] (A : GlobalTheory.Cube.{0} κ R) (x : GlobalTheory.Cube.Term A 2)
    {i j k : κ} (h : i < j) (h' : j < k) (hc : ({i, j, k} : Finset κ).card = 2 + 1) :
    GlobalTheory.Cube.d A 2 x ⟨{i, j, k}, hc⟩ =
      GlobalTheory.Cube.res A (by simp) (x ⟨{j, k}, Finset.card_pair h'.ne⟩) -
        GlobalTheory.Cube.res A (by simp) (x ⟨{i, k}, Finset.card_pair (h.trans h').ne⟩) +
        GlobalTheory.Cube.res A (by simp [Finset.insert_subset_iff]) (x ⟨{i, j}, Finset.card_pair h.ne⟩) := by
  have h'' := h.trans h'
  rw [GlobalTheory.Cube.d_apply_extend, Finset.sum_insert (by simp [h.ne, h''.ne]), Finset.sum_pair h'.ne,
    ← GlobalTheory.Cube.extend_apply_of_eq A x (Finset.card_pair h'.ne),
    ← GlobalTheory.Cube.extend_apply_of_eq A x (Finset.card_pair h''.ne),
    ← GlobalTheory.Cube.extend_apply_of_eq A x (Finset.card_pair h.ne)]
  have e1 : ({i, j, k} : Finset κ).erase i = {j, k} := Finset.erase_insert (by simp [h.ne, h''.ne])
  have e2 : ({i, j, k} : Finset κ).erase j = {i, k} := by
    rw [Finset.erase_insert_of_ne h.ne, Finset.erase_insert (by simp [h'.ne])]
  have e3 : ({i, j, k} : Finset κ).erase k = {i, j} := by
    rw [Finset.erase_insert_of_ne h''.ne, Finset.erase_insert_of_ne h'.ne, Finset.erase_singleton]
    rfl
  have s1 : cubeSign ({i, j, k} : Finset κ) i = 1 :=
    cubeSign_eq_one_of_forall_le (by simp [h.le, h''.le])
  have s2 : cubeSign ({i, j, k} : Finset κ) j = -1 := by
    have := cubeSign_erase_of_lt (t := {i, j, k}) (by simp) h
    rw [e1, cubeSign_eq_one_of_forall_le (by simp [h'.le])] at this
    omega
  have s3 : cubeSign ({i, j, k} : Finset κ) k = 1 := by
    have h1 := cubeSign_erase_of_lt (t := {i, j, k}) (by simp) h''
    have h2 := cubeSign_erase_of_lt (t := {j, k}) (by simp) h'
    rw [Finset.erase_insert (by simp [h'.ne]), cubeSign_singleton] at h2
    rw [e1] at h1
    omega
  rw [GlobalTheory.Cube.res_congr A _ e1 _ (by simp), GlobalTheory.Cube.res_congr A _ e2 _ (by simp),
    GlobalTheory.Cube.res_congr A _ e3 _ (by simp [Finset.insert_subset_iff])]
  simp only [s1, s2, s3, one_smul, neg_smul, sub_eq_add_neg, add_assoc]

section Cube

variable {κ : Type} (D : κ → X.Opens)

theorem le_single {W : X.Opens} {i : κ} (hi : W ≤ D i) : W ≤ ⨅ l ∈ ({i} : Finset κ), D l := by
  simpa using hi

theorem le_of_mem {s : Finset κ} {i : κ} (hi : i ∈ s) : ⨅ l ∈ s, D l ≤ D i := biInf_le _ hi

variable [LinearOrder κ]

theorem le_pair {W : X.Opens} {i j : κ} (hi : W ≤ D i) (hj : W ≤ D j) :
    W ≤ ⨅ l ∈ ({i, j} : Finset κ), D l := by
  simp [hi, hj]

variable (f : X ⟶ Spec (CommRingCat.of R)) (M)

def comp {p : ℕ} (x : GlobalTheory.Cube.Term (secCube f M D) p) (s : Finset κ) (hs : s.card = p) :
    SecOn M (⨅ l ∈ s, D l) := x ⟨s, hs⟩

variable {D f M}

theorem restrict_d_one (x : GlobalTheory.Cube.Term (secCube f M D) 1) {i j : κ} (h : i < j) {W : X.Opens}
    (hi : W ≤ D i) (hj : W ≤ D j) :
    restrict M (le_pair D hi hj) (comp M D f (GlobalTheory.Cube.d _ 1 x) {i, j} (Finset.card_pair h.ne)) =
      restrict M (le_single D hj) (comp M D f x {j} (Finset.card_singleton j)) -
        restrict M (le_single D hi) (comp M D f x {i} (Finset.card_singleton i)) := by
  have e : comp M D f (GlobalTheory.Cube.d _ 1 x) {i, j} (Finset.card_pair h.ne) =
      restrict M (iInf_le_iInf_of_subset D (by simp)) (comp M D f x {j} (Finset.card_singleton j)) -
      restrict M (iInf_le_iInf_of_subset D (by simp)) (comp M D f x {i} (Finset.card_singleton i)) :=
    GlobalTheory.Cube.d_one_apply_pair _ x h
  rw [e, map_sub, restrict_restrict, restrict_restrict]

theorem restrict_d_two (x : GlobalTheory.Cube.Term (secCube f M D) 2) {i j k : κ} (h : i < j) (h' : j < k)
    (hc : ({i, j, k} : Finset κ).card = 2 + 1) {W : X.Opens}
    (hi : W ≤ D i) (hj : W ≤ D j) (hk : W ≤ D k) :
    restrict M (by simp [hi, hj, hk]) (comp M D f (GlobalTheory.Cube.d _ 2 x) {i, j, k} hc) =
      restrict M (le_pair D hj hk) (comp M D f x {j, k} (Finset.card_pair h'.ne)) -
        restrict M (le_pair D hi hk) (comp M D f x {i, k} (Finset.card_pair (h.trans h').ne)) +
        restrict M (le_pair D hi hj) (comp M D f x {i, j} (Finset.card_pair h.ne)) := by
  have e : comp M D f (GlobalTheory.Cube.d _ 2 x) {i, j, k} hc =
      restrict M (iInf_le_iInf_of_subset D (by simp)) (comp M D f x {j, k} (Finset.card_pair h'.ne)) -
      restrict M (iInf_le_iInf_of_subset D (by simp))
        (comp M D f x {i, k} (Finset.card_pair (h.trans h').ne)) +
      restrict M (iInf_le_iInf_of_subset D (by simp [Finset.insert_subset_iff]))
        (comp M D f x {i, j} (Finset.card_pair h.ne)) :=
    d_two_apply_triple _ x h h' hc
  rw [e, map_add, map_sub, restrict_restrict, restrict_restrict, restrict_restrict]

theorem IsCocycle.diag {I : Type} {O : I → X.Opens} {φ : ∀ a b, SecOn M (O a ⊓ O b)}
    (hφ : IsCocycle M O φ) (a : I) : φ a a = 0 := by
  have h := hφ a a a (O a ⊓ O a) inf_le_left inf_le_left inf_le_left
  rw [restrict_self] at h
  exact add_eq_left.1 h

theorem IsCocycle.swap {I : Type} {O : I → X.Opens} {φ : ∀ a b, SecOn M (O a ⊓ O b)}
    (hφ : IsCocycle M O φ) (a b : I) :
    φ a b = -restrict M (le_inf inf_le_right inf_le_left) (φ b a) := by
  have h := hφ a b a (O a ⊓ O b) inf_le_left inf_le_right inf_le_left
  rw [restrict_self, hφ.diag, map_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem isCoboundary_of_exactAt (h : (cechLB f M D).ExactAt 1)
    (φ : ∀ a b, SecOn M (D a ⊓ D b)) (hφ : IsCocycle M D φ) : IsCoboundary M D φ := by
  have hex := (cechComplex_exactAt_succ_iff (secCube f M D) 0).1 h
  obtain ⟨x, hx⟩ : ∃ x : GlobalTheory.Cube.Term (secCube f M D) 2, ∀ i j (h : i < j),
      comp M D f x {i, j} (Finset.card_pair h.ne) =
        restrict M (le_inf (le_of_mem D (by simp)) (le_of_mem D (by simp))) (φ i j) := by
    have hne : ∀ s : {s : Finset κ // s.card = 2}, s.1.Nonempty := fun s =>
      Finset.card_pos.1 (by rw [s.2]; decide)
    have hcongr : ∀ {i j i' j' : κ} (_ : i = i') (_ : j = j') {W : X.Opens} (e : W ≤ D i ⊓ D j)
        (e' : W ≤ D i' ⊓ D j'), restrict M e (φ i j) = restrict M e' (φ i' j') := by
      rintro _ _ _ _ rfl rfl _ _ _; rfl
    refine ⟨fun s => SecOnR.of f M _ (restrict M (le_inf (le_of_mem D (s.1.min'_mem (hne s)))
      (le_of_mem D (s.1.max'_mem (hne s)))) (φ _ _)), fun i j h => ?_⟩
    exact hcongr (by simp [h.le]) (by simp [h.le]) (le_inf (le_of_mem D (Finset.min'_mem _ (by simp)))
      (le_of_mem D (Finset.max'_mem _ (by simp)))) _
  have hd : GlobalTheory.Cube.d _ 2 x = 0 := by
    funext ⟨t, ht⟩
    obtain ⟨i, j, k, hij, hjk, rfl⟩ := exists_triple ht
    have e := restrict_d_two x hij hjk ht (W := ⨅ l ∈ ({i, j, k} : Finset κ), D l)
      (le_of_mem D (by simp)) (le_of_mem D (by simp)) (le_of_mem D (by simp))
    rw [restrict_self, hx i j hij, hx j k hjk, hx i k (hij.trans hjk), restrict_restrict,
      restrict_restrict, restrict_restrict, ← hφ i j k _ (le_of_mem D (by simp))
        (le_of_mem D (by simp)) (le_of_mem D (by simp))] at e
    exact e.trans (Eq.trans (b := 0) (by abel) rfl)
  obtain ⟨y, hy⟩ := (hex x).1 hd
  let ψ : ∀ a, SecOn M (D a) := fun a =>
    -restrict M (le_single D le_rfl) (comp M D f y {a} (Finset.card_singleton a))
  have hlt : ∀ a b, a < b →
      φ a b = restrict M inf_le_left (ψ a) - restrict M inf_le_right (ψ b) := by
    intro a b hab
    have e := restrict_d_one y hab (W := D a ⊓ D b) inf_le_left inf_le_right
    rw [show GlobalTheory.Cube.d _ 1 y = x from hy, hx a b hab, restrict_restrict, restrict_self] at e
    simp only [ψ, map_neg, restrict_restrict, e]
    abel
  refine ⟨ψ, fun a b => ?_⟩
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact hlt a b hab
  · rw [hφ.diag, sub_self]
  · rw [hφ.swap a b, hlt b a hab, map_sub, restrict_restrict, restrict_restrict, neg_sub]

theorem exactAt_of_isCoboundary
    (h : ∀ φ : ∀ a b, SecOn M (D a ⊓ D b), IsCocycle M D φ → IsCoboundary M D φ) :
    (cechLB f M D).ExactAt 1 := by
  refine (cechComplex_exactAt_succ_iff (secCube f M D) 0).2 fun x => ⟨fun hx => ?_, ?_⟩
  swap
  · rintro ⟨y, rfl⟩
    exact GlobalTheory.Cube.d_d _ _ y
  have hx' : GlobalTheory.Cube.d _ 2 x = 0 := hx
  let φ : ∀ a b, SecOn M (D a ⊓ D b) := fun a b =>
    if h : a < b then
      restrict M (le_pair D inf_le_left inf_le_right) (comp M D f x {a, b} (Finset.card_pair h.ne))
    else if h : b < a then
      -restrict M (le_pair D inf_le_right inf_le_left) (comp M D f x {b, a} (Finset.card_pair h.ne))
    else 0
  have hlt : ∀ a b (h : a < b), φ a b = restrict M (le_pair D inf_le_left inf_le_right)
      (comp M D f x {a, b} (Finset.card_pair h.ne)) := fun a b h => dif_pos h
  have hgt : ∀ a b (h : b < a), φ a b = -restrict M (le_pair D inf_le_right inf_le_left)
      (comp M D f x {b, a} (Finset.card_pair h.ne)) := fun a b h =>
    (dif_neg h.not_gt).trans (dif_pos h)
  have h0 : ∀ a, φ a a = 0 := fun a => (dif_neg (lt_irrefl a)).trans (dif_neg (lt_irrefl a))
  obtain ⟨ψ, hψ⟩ := h φ (by
    intro a b d W ha hb hd
    refine add_eq_of_ordered (κ := {i // W ≤ D i})
      (fun i j => restrict M (le_inf i.2 j.2) (φ i.1 j.1)) (fun i => ?_) (fun i j => ?_)
      (fun i j k hij hjk => ?_) ⟨a, ha⟩ ⟨b, hb⟩ ⟨d, hd⟩
    · rw [h0, map_zero]
    · rcases lt_trichotomy i j with hij | rfl | hij
      · rw [hlt i j hij, hgt j i hij, map_neg, restrict_restrict, restrict_restrict]
      · rw [h0, map_zero, neg_zero]
      · rw [hlt j i hij, hgt i j hij, map_neg, restrict_restrict, restrict_restrict, neg_neg]
    · have hij' : i.1 < j.1 := hij
      have hjk' : j.1 < k.1 := hjk
      have e := restrict_d_two x hij' hjk' (Finset.card_eq_three.2
        ⟨_, _, _, hij'.ne, (hij'.trans hjk').ne, hjk'.ne, rfl⟩) i.2 j.2 k.2
      rw [hx'] at e
      have e' := (map_zero (restrict M _)).symm.trans e
      rw [hlt i j hij, hlt j k hjk, hlt i k (hij.trans hjk), restrict_restrict, restrict_restrict,
        restrict_restrict, ← sub_eq_zero]
      exact Eq.trans (by abel) e'.symm)
  let y := GlobalTheory.Cube.termOneEquiv (secCube f M D) fun a =>
    SecOnR.of f M _ (-restrict M (le_of_mem D (Finset.mem_singleton_self a)) (ψ a))
  have hy : ∀ a, comp M D f y {a} (Finset.card_singleton a) =
      -restrict M (le_of_mem D (Finset.mem_singleton_self a)) (ψ a) := fun a =>
    GlobalTheory.Cube.termOneEquiv_apply _ _ a
  refine ⟨y, ?_⟩
  funext ⟨t, ht⟩
  obtain ⟨i, j, hij, rfl⟩ := exists_pair ht
  have hi : ⨅ l ∈ ({i, j} : Finset κ), D l ≤ D i := le_of_mem D (by simp)
  have hj : ⨅ l ∈ ({i, j} : Finset κ), D l ≤ D j := le_of_mem D (by simp)
  have e := restrict_d_one y hij hi hj
  have e₂ := congrArg (restrict M (le_inf hi hj)) ((hlt i j hij).symm.trans (hψ i j))
  rw [restrict_self, hy, hy] at e
  simp only [map_neg, map_sub, restrict_restrict, restrict_self] at e e₂
  exact e.trans (Eq.trans (by abel) e₂.symm)

end Cube

section Main

variable {κ : Type} [LinearOrder κ] (f : X ⟶ Spec (CommRingCat.of R)) (M) (D : κ → X.Opens)

def toCech {V : X.Opens} (hD : ∀ i, D i ≤ V) : SecOnR f M V →ₗ[R] (cechLB f M D).X 0 :=
  LinearMap.pi fun s : {s : Finset κ // s.card = 0 + 1} => SecOnR.restrict f M (by
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (s.2.symm ▸ Nat.succ_pos 0 : 0 < s.1.card)
    exact (le_of_mem D hi).trans (hD i))

theorem toCech_apply {V : X.Opens} (hD : ∀ i, D i ≤ V) (x : SecOnR f M V)
    (s : {s : Finset κ // s.card = 0 + 1}) (h : ⨅ i ∈ s.1, D i ≤ V) :
    toCech M f D hD x s = SecOnR.restrict f M h x := rfl

variable {D}

theorem toCech_injective {V : X.Opens} (hD : ∀ i, D i ≤ V) (hc : V ≤ ⨆ i, D i) :
    Function.Injective (toCech M f D hD) := by
  intro x y h
  refine SecOnR.ext_of_cover f D hD hc fun i => ?_
  have e := congrArg (SecOnR.restrict f M (le_single D (le_rfl : D i ≤ D i)))
    (congrFun h ⟨{i}, Finset.card_singleton i⟩)
  have hi := (le_of_mem D (Finset.mem_singleton_self i)).trans (hD i)
  exact (SecOnR.restrict_restrict f hi _ x).symm.trans (e.trans (SecOnR.restrict_restrict f hi _ y))

theorem exact_toCech {V : X.Opens} (hD : ∀ i, D i ≤ V) (hc : V ≤ ⨆ i, D i) :
    Function.Exact (toCech M f D hD) ((cechLB f M D).d 0 1).hom := by
  have hd : ∀ x, ((cechLB f M D).d 0 1).hom x = GlobalTheory.Cube.d (secCube f M D) 1 x := fun x =>
    congrArg (fun q => q.hom x) (cechLB_d f M D 0)
  intro x
  rw [hd]
  constructor
  · intro hx
    have hlt : ∀ i j, i < j → ∀ (W : X.Opens) (hi : W ≤ D i) (hj : W ≤ D j),
        restrict M (le_single D hj) (comp M D f x {j} (Finset.card_singleton j)) =
          restrict M (le_single D hi) (comp M D f x {i} (Finset.card_singleton i)) := by
      intro i j hij W hi hj
      have e := restrict_d_one x hij hi hj
      rw [hx] at e
      exact sub_eq_zero.1 ((map_zero (restrict M _)).symm.trans e).symm
    obtain ⟨t, ht, -⟩ := existsUnique_glue D hD hc
      (fun i => restrict M (le_single D le_rfl) (comp M D f x {i} (Finset.card_singleton i)))
      fun i j => by
        rw [restrict_restrict, restrict_restrict]
        rcases lt_trichotomy i j with hij | rfl | hij
        · exact (hlt i j hij _ inf_le_left inf_le_right).symm
        · rfl
        · exact hlt j i hij _ inf_le_right inf_le_left
    refine ⟨SecOnR.of f M V t, ?_⟩
    funext ⟨s, hs⟩
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hs
    have e := congrArg (restrict M (le_of_mem D (Finset.mem_singleton_self i))) (ht i)
    rw [restrict_restrict, restrict_restrict, restrict_self] at e
    exact e
  · rintro ⟨t, rfl⟩
    funext ⟨s, hs⟩
    obtain ⟨i, j, hij, rfl⟩ := exists_pair hs
    have e := restrict_d_one (toCech M f D hD t) hij (W := ⨅ l ∈ ({i, j} : Finset κ), D l)
      (le_of_mem D (by simp)) (le_of_mem D (by simp))
    rw [restrict_self] at e
    exact e.trans (sub_eq_zero.2
      ((restrict_restrict ((le_of_mem D (Finset.mem_singleton_self j)).trans (hD j)) _ _).trans
        (restrict_restrict ((le_of_mem D (Finset.mem_singleton_self i)).trans (hD i)) _ _).symm))

def kerEquiv {V : X.Opens} (hD : ∀ i, D i ≤ V) (hc : V ≤ ⨆ i, D i) :
    SecOnR f M V ≃ₗ[R] LinearMap.ker ((cechLB f M D).d 0 1).hom :=
  LinearEquiv.ofInjective _ (toCech_injective M f hD hc) ≪≫ₗ
    LinearEquiv.ofEq _ _ (exact_toCech M f hD hc).linearMap_ker_eq.symm

@[simp] theorem kerEquiv_val {V : X.Opens} (hD : ∀ i, D i ≤ V) (hc : V ≤ ⨆ i, D i)
    (x : SecOnR f M V) : (kerEquiv M f hD hc x).1 = toCech M f D hD x := rfl

def secKerEquiv (hc : ⨆ i, D i = ⊤) :
    LB.Sec M ≃+ LinearMap.ker ((cechLB f M D).d 0 1).hom :=
  (SecOnR.topEquiv f M).symm.toAddEquiv.trans (kerEquiv M f (fun _ => le_top) hc.ge).toAddEquiv

theorem secKerEquiv_val (hc : ⨆ i, D i = ⊤) (σ : LB.Sec M) (s : {s : Finset κ // s.card = 0 + 1}) :
    (secKerEquiv M f hc σ).1 s = SecOnR.of f M _ (GlobalTheory.LB.ofSec σ (⨅ i ∈ s.1, D i)) :=
  restrict_ofSec σ le_top

theorem secKerEquiv_smul (hc : ⨆ i, D i = ⊤) (r : R) (σ : LB.Sec M) :
    secKerEquiv M f hc (cst f ⊤ r • σ) = r • secKerEquiv M f hc σ :=
  (congrArg (kerEquiv M f (fun _ => le_top) hc.ge)
    ((SecOnR.topEquiv f M).symm.map_smul (cst f ⊤ r) σ)).trans
    ((kerEquiv M f (fun _ => le_top) hc.ge).map_smul r _)

variable {M}

theorem exactAt_one_of_h1ZeroOn {V : X.Opens} (hD : ∀ i, D i ≤ V) (hc : V ≤ ⨆ i, D i)
    (h : CechHOneVanishesOnOpen M V) : (cechLB f M D).ExactAt 1 :=
  exactAt_of_isCoboundary (h κ D hD hc)

theorem exactAt_one_of_h1Zero (hM : M.IsLB) (hc : ⨆ i, D i = ⊤) (h : FirstCohomologyVanishes M) :
    (cechLB f M D).ExactAt 1 :=
  exactAt_one_of_h1ZeroOn f (fun _ => le_top) hc.ge ((h1Zero_iff hM).1 h)

theorem h1ZeroOn_of_exactAt_one (hM : M.IsLB) {V : X.Opens} (hD : ∀ i, D i ≤ V)
    (hc : V ≤ ⨆ i, D i) (hA : ∀ i, IsAffineOpen (D i)) (h : (cechLB f M D).ExactAt 1) :
    CechHOneVanishesOnOpen M V :=
  cechHOneVanishesOnOpen_of_cover hD hc (fun i => cechHOneVanishesOnOpen_of_isAffineOpen hM (hA i)) (isCoboundary_of_exactAt h)

theorem h1Zero_of_exactAt_one (hM : M.IsLB) (hc : ⨆ i, D i = ⊤) (hA : ∀ i, IsAffineOpen (D i))
    (h : (cechLB f M D).ExactAt 1) : FirstCohomologyVanishes M :=
  (h1Zero_iff hM).2 (h1ZeroOn_of_exactAt_one f hM (fun _ => le_top) hc.ge hA h)

end Main

end GlobalTheory.AbLaw.CechOne
