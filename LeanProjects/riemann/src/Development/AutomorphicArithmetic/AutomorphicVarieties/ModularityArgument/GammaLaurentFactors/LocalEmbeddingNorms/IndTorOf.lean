import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.MatchIndOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Reps

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

private theorem reps {α : Type*} (r : α → α → Prop) (hr : Equivalence r) (A : Finset α) :
    ∃ T : Finset α, T ⊆ A ∧ (∀ t ∈ T, ∀ t' ∈ T, r t t' → t = t') ∧ ∀ a ∈ A, ∃ t ∈ T, r a t :=
  _root_.UpperTheory.Reformulated.B.Qh68.reps r hr A

private theorem swapc {α ι : Type*} (I : Finset ι) (p : ι → α → Prop) (s : Multiset α) :
    ∑ i ∈ I, (s.filter (p i)).card = (s.map fun y => (I.filter fun i => p i y).card).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ← ih, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Multiset.filter_cons, Multiset.card_add]
    split_ifs <;> simp

private theorem allone {α : Type*} (d g : α → ℕ) (F : ℕ) (hF : 0 < F) (s : Multiset α) (hpos : ∀ y ∈ s, 0 < d y)
    (hg : ∀ y ∈ s, g y ≤ F ∧ (d y ≠ 1 → g y = 0)) (h : F * (s.map d).sum ≤ (s.map g).sum) : ∀ y ∈ s, d y = 1 := by
  intro y hy
  by_contra hne
  have hlt : (s.map g).sum < (s.map fun y => F * d y).sum := by
    refine Multiset.sum_lt_sum (fun z hz => (hg z hz).1.trans (Nat.le_mul_of_pos_right _ (hpos z hz))) ⟨y, hy, ?_⟩
    rw [(hg y hy).2 hne]
    exact Nat.mul_pos hF (hpos y hy)
  rw [Multiset.sum_map_mul_left] at hlt
  omega

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem unr_of {a b c : kˣ →* ℂˣ} (ha : IsUnram a) (hb : IsUnram b) (h : ∀ x, a x = 1 → b x = 1 → c x = 1) :
    IsUnram c := fun x hx => h x (ha x hx) (hb x hx)

end

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {k' : Type} [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

private theorem sum_right (N : k'ˣ →* kˣ) (T : Finset (kˣ →* ℂˣ)) (s : Multiset (IrrGL k'))
    (h2 : ∀ t ∈ T, ∀ t' ∈ T, IsUnram ((t * t'⁻¹).comp N) → t = t')
    (h3 : ∀ y ∈ s, ∃ ζ hζ, y = IrrGL.ofChar ζ hζ ∧ ∃ t ∈ T, IsUnram (ζ * t.comp N)) :
    ∑ t ∈ T, cnt s (t.comp N) = s.card := by
  unfold cnt
  rw [swapc T (fun t y => ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * t.comp N)) s]
  rw [Multiset.map_congr rfl (g := fun _ => 1) fun y hy => ?_]
  · simp
  obtain ⟨ζ, hζ, rfl, t, ht, e⟩ := h3 y hy
  refine Finset.card_eq_one.2 ⟨t, Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_filter.2 ⟨ht, ζ, hζ, rfl, e⟩, fun t' ht' => ?_⟩⟩
  obtain ⟨ht', ξ, hξ, e1, e2⟩ := Finset.mem_filter.1 ht'
  obtain rfl := IrrGL.ofChar_inj.1 e1
  refine h2 t' ht' t ht (unr_of e2 e fun x a b => ?_)
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply] at a b ⊢
  rw [mul_inv_eq_one]
  exact mul_left_cancel (a.trans b.symm)

private theorem left_le (N : k'ˣ →* kˣ) (T : Finset (kˣ →* ℂˣ)) (J : Finset ℕ) (e : ℕ → (kˣ →* ℂˣ)) (F : ℕ)
    (hT : ∀ t ∈ T, IsSmoothChar t) (he : ∀ j, IsSmoothChar (e j)) (heN : ∀ j x, e j (N x) = 1)
    (h2 : ∀ t ∈ T, ∀ t' ∈ T, IsUnram ((t * t'⁻¹).comp N) → t = t')
    (hup : ∀ θ : kˣ →* ℂˣ, IsSmoothChar θ → IsUnram θ → IsUnram (θ.comp N))
    (hF : ∀ θ : kˣ →* ℂˣ, IsSmoothChar θ → IsUnram (θ.comp N) → (J.filter fun j => IsUnram (θ * e j)).card = F)
    (y : IrrGL k) :
    ((T ×ˢ J).filter fun p => ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * (p.1 * e p.2))).card ≤ F := by
  rcases Finset.eq_empty_or_nonempty
    ((T ×ˢ J).filter fun p => ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * (p.1 * e p.2))) with h | ⟨p, hp⟩
  · rw [h]; exact Nat.zero_le _
  obtain ⟨hp0, ξ, hξ, rfl, hu⟩ := Finset.mem_filter.1 hp
  have key : ∀ t ∈ T, ∀ j, IsUnram (ξ * (t * e j)) → IsUnram ((ξ * t).comp N) := fun t ht j h => by
    have := hup _ (hξ.mul ((hT t ht).mul (he j))) h
    refine unr_of this this fun x a _ => ?_
    simpa only [MonoidHom.mul_apply, MonoidHom.comp_apply, heN, mul_one] using a
  have hp1 := (Finset.mem_product.1 hp0).1
  have k1 := key p.1 hp1 p.2 hu
  rw [← hF _ (hξ.mul (hT _ hp1)) k1]
  have hall : ∀ q ∈ ((T ×ˢ J).filter fun p => ∃ ξ' hξ', IrrGL.ofChar ξ hξ = IrrGL.ofChar ξ' hξ' ∧
      IsUnram (ξ' * (p.1 * e p.2))), q.1 = p.1 ∧ q.2 ∈ J ∧ IsUnram (ξ * p.1 * e q.2) := fun q hq => by
    obtain ⟨hq, ξ', hξ', e1, e2⟩ := Finset.mem_filter.1 hq
    obtain rfl := IrrGL.ofChar_inj.1 e1
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.1 hq
    have : q.1 = p.1 := by
      refine h2 _ hq1 _ hp1 (unr_of (key _ hq1 _ e2) k1 fun x a b => ?_)
      simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply] at a b ⊢
      rw [mul_inv_eq_one]
      exact mul_left_cancel (a.trans b.symm)
    exact ⟨this, hq2, by rw [mul_assoc, ← this]; exact e2⟩
  refine Finset.card_le_card_of_injOn Prod.snd (fun q hq => ?_) fun q hq q' hq' h => ?_
  · exact Finset.mem_coe.2 (Finset.mem_filter.2 (hall q hq).2)
  · exact Prod.ext ((hall q hq).1.trans (hall q' hq').1.symm) h

private theorem unr_equiv (N : k'ˣ →* kˣ) : Equivalence fun t t' : kˣ →* ℂˣ => IsUnram ((t * t'⁻¹).comp N) := by
  refine ⟨fun t x _ => by simp, fun h => unr_of h h fun x a _ => ?_, fun h h' => unr_of h h' fun x a b => ?_⟩
  · simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, mul_inv_eq_one] at a ⊢
    exact a.symm
  · simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, mul_inv_eq_one] at a b ⊢
    exact a.trans b

end

end UpperTheory.V.Z.Gam

open UpperTheory.V.Z.Gam in
theorem UpperTheory.V.Z.Gam.indTorOf :
    UpperTheory.V.Z.Gam.IndTorOf := by
  intro hS hN hM K M _ _ _ _ _ _ _ hKM P π hI v hv
  haveI : Algebra.IsQuadraticExtension K M := ⟨hKM⟩
  obtain ⟨η, -, hη⟩ := hN K M (hKM ▸ Nat.prime_two)
  obtain ⟨w₀⟩ : Nonempty (PlacesOver M v) := (placesOverEquiv M v).nonempty_congr.2 inferInstance
  obtain ⟨⟨s, hs⟩, -, h3, -⟩ := hS K (2 * 2) (by norm_num) P v
  obtain ⟨hiff, hsum, hpos⟩ := h3 s hs
  choose s' hs' using fun w : PlacesOver M v => (hS M 2 (by norm_num) π w.1).1
  have hone : ∀ w, ∀ y ∈ s' w, y.1 = 1 := fun w =>
    ((hS M 2 (by norm_num) π w.1).2.2.1 _ (hs' w)).1.1 (hv w).1
  have hcard : ∀ w, (s' w).card = 2 := fun w => by
    have := ((hS M 2 (by norm_num) π w.1).2.2.1 _ (hs' w)).2.1
    rw [Multiset.map_congr rfl (g := fun _ => 1) (hone w)] at this
    simpa using this
  have hχ : ∀ (w : PlacesOver M v) (y : IrrGL (w.1.adicCompletion M)), ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ,
      IsSmoothChar χ ∧ (y ∈ s' w → ∃ ζ hζ, y = IrrGL.ofChar ζ hζ ∧ IsUnram (ζ * χ.comp (nm w))) := fun w y => by
    by_cases hy : y ∈ s' w
    · obtain ⟨ζ, hζ, rfl⟩ := TemperedTests.exists_eq_ofChar y (hone w y hy)
      obtain ⟨χ, h1, h2⟩ := (hv w).2 _ (hs' w) ζ hζ hy
      exact ⟨χ, h1, fun _ => ⟨ζ, hζ, rfl, h2⟩⟩
    · exact ⟨1, isSmoothChar_one, fun h => absurd h hy⟩
  choose χ hχs hχ using hχ
  obtain ⟨T, hT1, hT2, hT3⟩ := reps _ (unr_equiv (nm w₀))
    (Finset.univ.biUnion fun w : PlacesOver M v => (s' w).toFinset.image (χ w))
  have hT : ∀ t ∈ T, IsSmoothChar t := fun t ht => by
    obtain ⟨w, -, h⟩ := Finset.mem_biUnion.1 (hT1 ht)
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 h
    exact hχs w y
  have hR : ∀ w, ∑ t ∈ T, cnt (s' w) (t.comp (nm w)) = 2 := fun w => by
    rw [← hcard w]
    refine sum_right (nm w) T (s' w) (fun t ht t' ht' h => hT2 t ht t' ht' ((hη v w).2.1 w₀ _ h)) fun y hy => ?_
    obtain ⟨ζ, hζ, e, hu⟩ := hχ w y hy
    obtain ⟨t, ht, h⟩ := hT3 (χ w y) (Finset.mem_biUnion.2 ⟨w, Finset.mem_univ _,
      Finset.mem_image.2 ⟨y, Multiset.mem_toFinset.2 hy, rfl⟩⟩)
    refine ⟨ζ, hζ, e, t, ht, unr_of hu ((hη v w₀).2.1 w _ h) fun x a b => ?_⟩
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, mul_inv_eq_one] at a b ⊢
    rw [← b]; exact a
  have heN : ∀ (w : PlacesOver M v) (j : ℕ) x, (η ^ j).loc v (nm w x) = 1 := fun w j x => by
    have : η.loc v (nm w x) = 1 := DFunLike.congr_fun (hη v w).1 x
    show η.loc v (nm w x) ^ j = 1
    rw [this, one_pow]
  have hF : 0 < ∑ w : PlacesOver M v, fdeg w := by
    rw [← ((hη v w₀).2.2 1 isSmoothChar_one).2.2 (fun x _ => rfl)]
    exact Finset.card_pos.2 ⟨0, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), fun x _ => by
      show (1 : ℂˣ) * η.loc v x ^ 0 = 1
      simp⟩⟩
  have htot : ∑ p ∈ T ×ˢ Finset.range (Module.finrank K M), cnt s (p.1 * (η ^ p.2).loc v) =
      (∑ w : PlacesOver M v, fdeg w) * (2 * 2) := by
    have h1 : ∀ p ∈ T ×ˢ Finset.range (Module.finrank K M), cnt s (p.1 * (η ^ p.2).loc v) =
        ∑ w : PlacesOver M v, fdeg w * cnt (s' w) (p.1.comp (nm w)) := fun p hp => by
      rw [hM K M hKM P π hI v s s' hs hs' _ ((hT _ (Finset.mem_product.1 hp).1).mul (ParLaws.isSmoothChar_loc _ v))]
      refine Finset.sum_congr rfl fun w _ => ?_
      congr 2
      ext x
      simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, heN, mul_one]
    rw [Finset.sum_congr rfl h1, Finset.sum_product_right]
    simp only [Finset.sum_const, Finset.card_range, hKM, smul_eq_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hR, ← Finset.sum_mul]
    ring
  unfold cnt at htot
  rw [swapc _ (fun (p : ((v.adicCompletion K)ˣ →* ℂˣ) × ℕ) y =>
    ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * (p.1 * (η ^ p.2).loc v))) s, ← hsum] at htot
  refine hiff.2 (allone Sigma.fst _ _ hF s hpos (fun y _ => ⟨?_, fun hy => ?_⟩) htot.ge)
  · exact left_le (nm w₀) T _ (fun j => (η ^ j).loc v) _ hT (fun j => ParLaws.isSmoothChar_loc _ v) (heN w₀) hT2
      (fun θ h => ((hη v w₀).2.2 θ h).2.1) (fun θ h => ((hη v w₀).2.2 θ h).2.2) y
  · refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun p _ => ?_)
    rintro ⟨ξ, hξ, rfl, -⟩
    exact hy rfl
