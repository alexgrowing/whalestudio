import Mathlib

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.KuennethOne

variable {Z : Scheme.{0}}

noncomputable def rs {U V : Z.Opens} (h : U ≤ V) : Γ(Z, V) →+* Γ(Z, U) :=
  (Z.presheaf.map (homOfLE h).op).hom

@[simp] theorem rs_rs {U V W : Z.Opens} (h : U ≤ V) (h' : V ≤ W) (x : Γ(Z, W)) :
    rs h (rs h' x) = rs (h.trans h') x := by
  unfold rs
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

@[simp] theorem rs_self {U : Z.Opens} (h : U ≤ U) (x : Γ(Z, U)) : rs h x = x := by
  unfold rs
  have : (homOfLE h).op = 𝟙 (Opposite.op U) := rfl
  rw [this, CategoryTheory.Functor.map_id]
  rfl

@[simp] theorem appLE_rs {T : Scheme.{0}} (f : T ⟶ Z) {U V : Z.Opens} (h : U ≤ V) {N : T.Opens}
    (e : N ≤ f ⁻¹ᵁ U) (x : Γ(Z, V)) :
    (f.appLE U N e).hom (rs h x) = (f.appLE V N (e.trans (f.preimage_mono h))).hom x := by
  unfold rs
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

@[simp] theorem rs_appLE {T : Scheme.{0}} (f : T ⟶ Z) {U : Z.Opens} {N M : T.Opens} (h : M ≤ N)
    (e : N ≤ f ⁻¹ᵁ U) (x : Γ(Z, U)) :
    rs h ((f.appLE U N e).hom x) = (f.appLE U M (h.trans e)).hom x := by
  unfold rs
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem glue {J : Type} (O : Z.Opens) (W : J → Z.Opens) (hW : ∀ j, W j ≤ O) (hc : O ≤ iSup W)
    (sf : ∀ j, Γ(Z, W j))
    (h : ∀ j k, rs (inf_le_left : W j ⊓ W k ≤ W j) (sf j) = rs inf_le_right (sf k)) :
    ∃ s : Γ(Z, O), ∀ j, rs (hW j) s = sf j := by
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' W O (fun j => homOfLE (hW j)) hc sf h
  exact ⟨s, hs⟩

theorem loc {J : Type} {N : Z.Opens} (W : J → Z.Opens) (hc : N ≤ iSup W) (x y : Γ(Z, N))
    (h : ∀ j, rs (inf_le_left : N ⊓ W j ≤ N) x = rs inf_le_left y) : x = y := by
  refine Z.sheaf.eq_of_locally_eq' (fun j => N ⊓ W j) N (fun j => homOfLE inf_le_left) ?_ x y h
  rw [← inf_iSup_eq]
  exact le_inf le_rfl hc

variable {I : Type} (V : I → Z.Opens) (φ : ∀ a b, Γ(Z, V a ⊓ V b))

def IsCocycle : Prop :=
  ∀ a b d (N : Z.Opens) (ha : N ≤ V a) (hb : N ≤ V b) (hd : N ≤ V d),
    rs (le_inf ha hb) (φ a b) + rs (le_inf hb hd) (φ b d) = rs (le_inf ha hd) (φ a d)

def Splits (O : Z.Opens) (ψ : ∀ a, Γ(Z, O ⊓ V a)) : Prop :=
  ∀ a b (N : Z.Opens) (hO : N ≤ O) (ha : N ≤ V a) (hb : N ≤ V b),
    rs (le_inf ha hb) (φ a b) = rs (le_inf hO ha) (ψ a) - rs (le_inf hO hb) (ψ b)

def IsDiff {O O' P : Z.Opens} (ψ : ∀ a, Γ(Z, O ⊓ V a)) (ψ' : ∀ a, Γ(Z, O' ⊓ V a))
    (hO : P ≤ O) (hO' : P ≤ O') (c : Γ(Z, P)) : Prop :=
  ∀ a (M : Z.Opens) (hM : M ≤ P) (ha : M ≤ V a),
    rs hM c = rs (le_inf (hM.trans hO) ha) (ψ a) - rs (le_inf (hM.trans hO') ha) (ψ' a)

variable {V φ}

theorem exists_isDiff (hV : ⨆ a, V a = ⊤) {O O' P : Z.Opens} {ψ : ∀ a, Γ(Z, O ⊓ V a)}
    {ψ' : ∀ a, Γ(Z, O' ⊓ V a)} (h : Splits V φ O ψ) (h' : Splits V φ O' ψ')
    (hO : P ≤ O) (hO' : P ≤ O') : ∃ c : Γ(Z, P), IsDiff V ψ ψ' hO hO' c := by
  obtain ⟨c, hc⟩ := glue P (fun a => P ⊓ V a) (fun a => inf_le_left)
    (by rw [← inf_iSup_eq, hV]; simp)
    (fun a => rs (inf_le_inf_right _ hO) (ψ a) - rs (inf_le_inf_right _ hO') (ψ' a)) (by
      intro a b
      have hP : P ⊓ V a ⊓ (P ⊓ V b) ≤ P := inf_le_left.trans inf_le_left
      have ha : P ⊓ V a ⊓ (P ⊓ V b) ≤ V a := inf_le_left.trans inf_le_right
      have hb : P ⊓ V a ⊓ (P ⊓ V b) ≤ V b := inf_le_right.trans inf_le_right
      have e1 := h a b _ (hP.trans hO) ha hb
      have e2 := h' a b _ (hP.trans hO') ha hb
      simp only [map_sub, rs_rs]
      linear_combination e2 - e1)
  refine ⟨c, fun a M hM ha => ?_⟩
  have := congrArg (rs (le_inf hM ha)) (hc a)
  simpa only [map_sub, rs_rs] using this

theorem splits_glue {J : Type} (O : J → Z.Opens) (ψ : ∀ j a, Γ(Z, O j ⊓ V a))
    (h : ∀ j, Splits V φ (O j) (ψ j)) (g : ∀ j, Γ(Z, O j))
    (hg : ∀ j k a (M : Z.Opens) (hj : M ≤ O j) (hk : M ≤ O k) (ha : M ≤ V a),
      rs (le_inf hj ha) (ψ j a) - rs (le_inf hk ha) (ψ k a) = rs hj (g j) - rs hk (g k))
    (O₀ : Z.Opens) (hc : O₀ ≤ iSup O) : ∃ χ, Splits V φ O₀ χ := by
  have key : ∀ a, ∃ χ : Γ(Z, O₀ ⊓ V a), ∀ j,
      rs (inf_le_left : O₀ ⊓ V a ⊓ O j ≤ O₀ ⊓ V a) χ =
        rs (le_inf inf_le_right (inf_le_left.trans inf_le_right)) (ψ j a) -
          rs inf_le_right (g j) := by
    intro a
    refine glue (O₀ ⊓ V a) (fun j => O₀ ⊓ V a ⊓ O j) (fun j => inf_le_left) ?_ _ ?_
    · rw [← inf_iSup_eq]
      exact le_inf le_rfl (inf_le_left.trans hc)
    · intro j k
      have e := hg j k a (O₀ ⊓ V a ⊓ O j ⊓ (O₀ ⊓ V a ⊓ O k)) (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right) (inf_le_left.trans (inf_le_left.trans inf_le_right))
      simp only [map_sub, rs_rs]
      linear_combination e
  choose χ hχ using key
  refine ⟨χ, fun a b N hO ha hb => loc O (hO.trans hc) _ _ fun j => ?_⟩
  have e1 := congrArg (rs (inf_le_inf_right (O j) (le_inf hO ha))) (hχ a j)
  have e2 := congrArg (rs (inf_le_inf_right (O j) (le_inf hO hb))) (hχ b j)
  have e3 := h j a b (N ⊓ O j) inf_le_right (inf_le_left.trans ha) (inf_le_left.trans hb)
  simp only [map_sub, rs_rs] at e1 e2 ⊢
  linear_combination e3 - e1 + e2

theorem pull_coboundary (hV : ⨆ a, V a = ⊤) {T : Scheme.{0}} (f : T ⟶ Z)
    (ρ : ∀ a, Γ(T, f ⁻¹ᵁ V a))
    (hρ : ∀ a b, (f.app (V a ⊓ V b)).hom (φ a b) =
      rs (f.preimage_mono inf_le_left) (ρ a) - rs (f.preimage_mono inf_le_right) (ρ b))
    {J : Type} (O : J → Z.Opens) (ψ : ∀ j a, Γ(Z, O j ⊓ V a))
    (h : ∀ j, Splits V φ (O j) (ψ j)) (N : J → T.Opens) (hN : ∀ j, N j ≤ f ⁻¹ᵁ O j) :
    ∃ x : ∀ j, Γ(T, N j), ∀ j k (P : Z.Opens) (hj : P ≤ O j) (hk : P ≤ O k) (c : Γ(Z, P)),
      IsDiff V (ψ j) (ψ k) hj hk c → ∀ (M : T.Opens) (hMj : M ≤ N j) (hMk : M ≤ N k)
        (hM : M ≤ f ⁻¹ᵁ P), (f.appLE P M hM).hom c = rs hMj (x j) - rs hMk (x k) := by
  have hV' : ⨆ a, f ⁻¹ᵁ V a = ⊤ := by rw [← f.preimage_iSup, hV]; rfl
  let φ' : ∀ a b, Γ(T, f ⁻¹ᵁ V a ⊓ f ⁻¹ᵁ V b) := fun a b =>
    (f.appLE (V a ⊓ V b) _ (by rw [f.preimage_inf])).hom (φ a b)
  let ρ' : ∀ a, Γ(T, ⊤ ⊓ f ⁻¹ᵁ V a) := fun a => rs inf_le_right (ρ a)
  have h1 : Splits (fun a => f ⁻¹ᵁ V a) φ' ⊤ ρ' := by
    intro a b M _ ha hb
    have hM : M ≤ f ⁻¹ᵁ (V a ⊓ V b) := by rw [f.preimage_inf]; exact le_inf ha hb
    have := congrArg (rs hM) (hρ a b)
    rw [f.app_eq_appLE] at this
    simpa only [φ', ρ', rs_appLE, rs_rs, map_sub] using this
  let ψ' : ∀ j a, Γ(T, N j ⊓ f ⁻¹ᵁ V a) := fun j a =>
    (f.appLE (O j ⊓ V a) _ (by rw [f.preimage_inf]; exact inf_le_inf_right _ (hN j))).hom (ψ j a)
  have h2 : ∀ j, Splits (fun a => f ⁻¹ᵁ V a) φ' (N j) (ψ' j) := by
    intro j a b M hj ha hb
    have hM : M ≤ f ⁻¹ᵁ (O j ⊓ (V a ⊓ V b)) := by
      rw [f.preimage_inf, f.preimage_inf]; exact le_inf (hj.trans (hN j)) (le_inf ha hb)
    have := congrArg (f.appLE _ M hM).hom (h j a b (O j ⊓ (V a ⊓ V b)) inf_le_left
      (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right))
    simpa only [φ', ψ', rs_appLE, appLE_rs, map_sub] using this
  choose x hx using fun j => exists_isDiff hV' (h2 j) h1 le_rfl le_top
  refine ⟨x, fun j k P hj hk c hc M hMj hMk hM => loc (fun a => f ⁻¹ᵁ V a) (by rw [hV']; exact le_top)
    _ _ fun a => ?_⟩
  have e1 := hx j a (M ⊓ f ⁻¹ᵁ V a) (inf_le_left.trans hMj) inf_le_right
  have e2 := hx k a (M ⊓ f ⁻¹ᵁ V a) (inf_le_left.trans hMk) inf_le_right
  have hM' : M ⊓ f ⁻¹ᵁ V a ≤ f ⁻¹ᵁ (P ⊓ V a) := by
    rw [f.preimage_inf]; exact inf_le_inf_right _ hM
  have e3 := congrArg (f.appLE _ _ hM').hom (hc a (P ⊓ V a) inf_le_left inf_le_right)
  simp only [ψ', ρ', rs_appLE, appLE_rs, map_sub, rs_rs] at e1 e2 e3 ⊢
  linear_combination e3 - e1 + e2

theorem exists_splits_of_isAffineOpen (hV : ⨆ a, V a = ⊤) (hφ : IsCocycle V φ) {O : Z.Opens}
    (hO : IsAffineOpen O) : ∃ ψ, Splits V φ O ψ := by
  classical
  have h1 : ∀ x : O, ∃ (f : Γ(Z, O)) (a : I), Z.basicOpen f ≤ V a ∧ x.1 ∈ Z.basicOpen f := by
    intro x
    have : x.1 ∈ ⨆ a, V a := by rw [hV]; trivial
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp this
    obtain ⟨f, hf, hx⟩ := hO.exists_basicOpen_le ⟨x.1, ha⟩ x.2
    exact ⟨f, a, hf, hx⟩
  choose f₀ a₀ hfa₀ hx₀ using h1
  obtain ⟨s, hs⟩ := hO.isCompact.elim_finite_subcover (fun x : O => (Z.basicOpen (f₀ x) : Set Z))
    (fun x => (Z.basicOpen (f₀ x)).2) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hx₀ _⟩)
  let f : s → Γ(Z, O) := fun k => f₀ k.1
  let a : s → I := fun k => a₀ k.1
  let D : s → Z.Opens := fun k => Z.basicOpen (f k)
  have hDa : ∀ k, D k ≤ V (a k) := fun k => hfa₀ k.1
  have hDO : ∀ k, D k ≤ O := fun k => Z.basicOpen_le _
  have hcov : O ≤ iSup D := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Opens.mem_iSup.mpr ⟨⟨k, hk⟩, hxk⟩
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    rw [← hO.self_le_iSup_basicOpen_iff]
    refine hcov.trans (iSup_le fun k => ?_)
    exact le_iSup (fun g : Set.range f => Z.basicOpen g.1) ⟨f k, k, rfl⟩
  have hDaff : ∀ k, IsAffineOpen (D k) := fun k => hO.basicOpen _
  have hbo : ∀ (N : Z.Opens) (hN : N ≤ O) l, Z.basicOpen (rs hN (f l)) = N ⊓ D l :=
    fun N hN l => Z.basicOpen_res _ _

  have h2 : ∀ k l, ∃ (n : ℕ) (u : Γ(Z, D k)), rs (inf_le_left : D k ⊓ D l ≤ D k) u =
      rs (inf_le_left.trans (hDO k)) (f l) ^ n * rs (inf_le_inf (hDa k) (hDa l)) (φ (a k) (a l)) := by
    intro k l
    have e := hbo (D k) (hDO k) l
    obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen Z (D k) (hDaff k) (rs (hDO k) (f l))
      (rs (e.le.trans (inf_le_inf (hDa k) (hDa l))) (φ (a k) (a l)))
    refine ⟨n, y, ?_⟩
    have hy' : rs (Z.basicOpen_le _) y = rs (Z.basicOpen_le _) (rs (hDO k) (f l)) ^ n *
      rs (e.le.trans (inf_le_inf (hDa k) (hDa l))) (φ (a k) (a l)) := hy
    simpa only [rs_rs, map_mul, map_pow] using congrArg (rs e.ge) hy'
  choose n u hu using h2
  obtain ⟨A, hA⟩ := (Set.finite_range fun p : s × s => n p.1 p.2).bddAbove
  have hA' : ∀ k l, n k l ≤ A := fun k l => hA ⟨(k, l), rfl⟩
  let u' : ∀ k l : s, Γ(Z, D k) := fun k l => rs (hDO k) (f l) ^ (A - n k l) * u k l
  have hu' : ∀ k l (M : Z.Opens) (hk : M ≤ D k) (hl : M ≤ D l), rs hk (u' k l) =
      rs (hk.trans (hDO k)) (f l) ^ A * rs (le_inf (hk.trans (hDa k)) (hl.trans (hDa l)))
        (φ (a k) (a l)) := by
    intro k l M hk hl
    have := congrArg (rs (le_inf hk hl)) (hu k l)
    simp only [u', rs_rs, map_mul, map_pow] at this ⊢
    rw [this, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hA' k l)]
  have h3 : ∀ k m l, ∃ n : ℕ, rs ((inf_le_left : D k ⊓ D m ≤ D k).trans (hDO k)) (f l) ^ n *
      (rs inf_le_left (u' k l) - rs inf_le_right (u' m l) -
        rs (inf_le_left.trans (hDO k)) (f l) ^ A *
          rs (inf_le_inf (hDa k) (hDa m)) (φ (a k) (a m))) = 0 := by
    intro k m l
    have haff : IsAffineOpen (D k ⊓ D m) := by
      rw [← hbo (D k) (hDO k) m]; exact (hDaff k).basicOpen _
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen Z haff _ _ ?_
    have e := hbo (D k ⊓ D m) (inf_le_left.trans (hDO k)) l
    have hk := e.le.trans (inf_le_left.trans inf_le_left)
    have hm := e.le.trans (inf_le_left.trans inf_le_right)
    have hl := e.le.trans inf_le_right
    change rs (Z.basicOpen_le _) _ = 0
    have e1 := hu' k l _ hk hl
    have e2 := hu' m l _ hm hl
    have e3 := hφ (a k) (a m) (a l) _ (hk.trans (hDa k)) (hm.trans (hDa m)) (hl.trans (hDa l))
    simp only [rs_rs, map_mul, map_pow, map_sub]
    rw [e1, e2, ← e3]
    ring
  choose n' hn' using h3
  obtain ⟨B, hB⟩ := (Set.finite_range fun p : s × s × s => n' p.1 p.2.1 p.2.2).bddAbove
  have hB' : ∀ k m l, n' k m l ≤ B := fun k m l => hB ⟨(k, m, l), rfl⟩
  have hspan' : Ideal.span (Set.range fun l => f l ^ (B + A)) = ⊤ := by
    have := Ideal.span_pow_eq_top _ hspan (B + A)
    rwa [← Set.range_comp] at this
  obtain ⟨e, he⟩ := (Ideal.mem_span_range_iff_exists_fun).mp
    ((Ideal.eq_top_iff_one _).mp hspan')
  let g : ∀ k, Γ(Z, D k) := fun k => -∑ l, rs (hDO k) (e l * f l ^ B) * u' k l
  let ψ : ∀ k b, Γ(Z, D k ⊓ V b) := fun k b =>
    rs (le_inf inf_le_right (inf_le_left.trans (hDa k))) (φ b (a k))
  refine splits_glue D ψ ?_ g ?_ O hcov
  · intro k b d N hk hb hd
    have := hφ b d (a k) N hb hd (hk.trans (hDa k))
    simp only [ψ, rs_rs]
    linear_combination this
  · intro k m b M hk hm hb
    have e1 := hφ b (a k) (a m) M hb (hk.trans (hDa k)) (hm.trans (hDa m))
    have hM := hk.trans (hDO k)
    have e2 : ∀ l, rs hM (e l * f l ^ B) * rs hk (u' k l) - rs hM (e l * f l ^ B) * rs hm (u' m l) =
        rs hM (e l * f l ^ (B + A)) *
          rs (le_inf (hk.trans (hDa k)) (hm.trans (hDa m))) (φ (a k) (a m)) := by
      intro l
      have := congrArg (rs (le_inf hk hm)) (hn' k m l)
      obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (hB' k m l)
      simp only [rs_rs, map_mul, map_pow, map_sub, map_zero] at this ⊢
      rw [hc]
      linear_combination (rs hM (e l) * rs hM (f l) ^ c) * this
    have e3 := Finset.sum_congr (rfl : (Finset.univ : Finset s) = _) (fun l _ => e2 l)
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← map_sum, he, map_one, one_mul] at e3
    simp only [ψ, g, rs_rs, map_neg, map_sum, map_mul] at e3 ⊢
    linear_combination e3 + e1

end GlobalTheory.KuennethOne
