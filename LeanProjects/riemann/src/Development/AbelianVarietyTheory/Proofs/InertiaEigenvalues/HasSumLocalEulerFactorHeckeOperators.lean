import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivAtOfCfEqOne
open scoped InnerProductSpace BigOperators

noncomputable section

namespace GlobalTheory.UpInj.LocalSum

def dc {Γ : Type} [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) (g : Γ) : Set Γ :=
  {y | ∃ k₁ k₂, k₁ ∈ K ∧ c k₁ = k₁ ∧ k₂ ∈ K ∧ c k₂ = k₂ ∧ y = k₁ * g * k₂}

theorem mem_dc_self {Γ : Type} [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) (g : Γ) : g ∈ dc K c g :=
  ⟨1, 1, K.one_mem, map_one c, K.one_mem, map_one c, by simp⟩

theorem mul_mem_dc {Γ : Type} [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) {g y k : Γ} (h : y ∈ dc K c g)
    (hk : k ∈ K) (hck : c k = k) : y * k ∈ dc K c g := by
  obtain ⟨k₁, k₂, h1, h2, h3, h4, rfl⟩ := h
  exact ⟨k₁, k₂ * k, h1, h2, K.mul_mem h3 hk, by rw [map_mul, h4, hck], by simp [mul_assoc]⟩

theorem dc_eq_of_mem {Γ : Type} [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) {g y : Γ} (h : y ∈ dc K c g) :
    dc K c y = dc K c g := by
  obtain ⟨k₁, k₂, h1, h2, h3, h4, rfl⟩ := h
  ext z
  constructor
  · rintro ⟨l₁, l₂, i1, i2, i3, i4, rfl⟩
    exact ⟨l₁ * k₁, k₂ * l₂, K.mul_mem i1 h1, by rw [map_mul, i2, h2], K.mul_mem h3 i3,
      by rw [map_mul, h4, i4], by simp [mul_assoc]⟩
  · rintro ⟨l₁, l₂, i1, i2, i3, i4, rfl⟩
    exact ⟨l₁ * k₁⁻¹, k₂⁻¹ * l₂, K.mul_mem i1 (K.inv_mem h1), by rw [map_mul, map_inv, i2, h2],
      K.mul_mem (K.inv_mem h3) i3, by rw [map_mul, map_inv, h4, i4], by group⟩

theorem out_mk {Γ : Type} [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) (δ : Γ) :
    ∃ h, c h ∈ K ∧ Quotient.out (QuotientGroup.mk δ : Γ ⧸ K.comap c) = δ * h := by
  have e := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk δ : Γ ⧸ K.comap c))
  refine ⟨δ⁻¹ * Quotient.out (QuotientGroup.mk δ : Γ ⧸ K.comap c), ?_, by group⟩
  have := (K.comap c).inv_mem e
  rw [mul_inv_rev, inv_inv] at this
  exact this

end GlobalTheory.UpInj.LocalSum

open GlobalTheory.UpInj.LocalSum in

theorem GlobalTheory.UpInj.localSum_hasSum : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (a : Γ → ℂ) (B : Γ → (H →L[ℂ] H)) (S : ℝ), (∀ g, c (c g) = c g) → (∀ g k k', k ∈ K → k' ∈ K → a (k * g * k') = a g) → (∀ g k, k ∈ K → B (g * k) = B g) → (∀ g, ‖B g‖ ≤ 1) → (∀ C : Finset Γ, (∀ g ∈ C, c g = g ∧ g ∉ K) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ K → g = g') → ∑ g ∈ C, ‖a g‖ ≤ S) → (∀ α, c α = α → ∃ C, GlobalTheory.UpInj.DCRep c K α C) → (∀ α C, c α = α → GlobalTheory.UpInj.DCRep c K α C → ∀ γ, ∑ δ ∈ C, B (γ * δ) = B γ * ∑ δ ∈ C, B δ) → ∀ γ, HasSum (fun x : Γ ⧸ K.comap c => a (c (Quotient.out x)) • B (γ * c (Quotient.out x))) (B γ * ∑' x : Γ ⧸ K.comap c, a (c (Quotient.out x)) • B (c (Quotient.out x))) := by
  intro Γ _ K c H _ _ _ a B S hc ha hB hB1 hS hex hH γ
  classical
  let r : Γ ⧸ K.comap c → Γ := fun x => c (Quotient.out x)
  have hr_fix : ∀ x, c (r x) = r x := fun x => hc _
  have hr_eq : ∀ x x' : Γ ⧸ K.comap c, (r x)⁻¹ * r x' ∈ K ↔ x = x' := by
    intro x x'
    have e : (r x)⁻¹ * r x' = c ((Quotient.out x)⁻¹ * Quotient.out x') := by simp [r, map_mul, map_inv]
    rw [e, ← Subgroup.mem_comap, ← QuotientGroup.eq, QuotientGroup.out_eq', QuotientGroup.out_eq']
  have hr_one : ∀ x : Γ ⧸ K.comap c, r x ∈ K ↔ x = (QuotientGroup.mk 1 : Γ ⧸ K.comap c) := by
    intro x
    have key : (QuotientGroup.mk 1 : Γ ⧸ K.comap c) = QuotientGroup.mk (Quotient.out x) ↔
        1⁻¹ * Quotient.out x ∈ K.comap c := QuotientGroup.eq
    rw [QuotientGroup.out_eq', inv_one, one_mul, Subgroup.mem_comap] at key
    rw [eq_comm]; exact key.symm
  have ha1 : ∀ g, g ∈ K → a g = a 1 := fun g hg => by simpa using ha 1 g 1 hg K.one_mem
  have hsum : Summable (fun x : Γ ⧸ K.comap c => ‖a (r x)‖) := by
    refine summable_of_sum_le (c := ‖a 1‖ + S) (fun x => norm_nonneg _) (fun u => ?_)
    rw [← Finset.sum_filter_add_sum_filter_not u (fun x => x = (QuotientGroup.mk 1 : Γ ⧸ K.comap c))]
    gcongr ?_ + ?_
    · calc ∑ x ∈ u.filter (fun x => x = QuotientGroup.mk 1), ‖a (r x)‖
            ≤ ∑ x ∈ {(QuotientGroup.mk 1 : Γ ⧸ K.comap c)}, ‖a (r x)‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => by simp [(Finset.mem_filter.1 hx).2])
              (fun _ _ _ => norm_nonneg _)
        _ = ‖a 1‖ := by rw [Finset.sum_singleton, ha1 _ ((hr_one _).2 rfl)]
    · rw [← Finset.sum_image (f := fun g => ‖a g‖) (fun x _ x' _ h => (hr_eq x x').1 (by rw [h, inv_mul_cancel]; exact K.one_mem))]
      apply hS
      · intro g hg
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hg
        exact ⟨hr_fix x, fun h => (Finset.mem_filter.1 hx).2 ((hr_one x).1 h)⟩
      · intro g hg g' hg' h
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hg
        obtain ⟨x', _, rfl⟩ := Finset.mem_image.1 hg'
        rw [(hr_eq x x').1 h]
  have hnorm : ∀ g γ', ‖a g • B (γ' * g)‖ ≤ ‖a g‖ := fun g γ' => by
    rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (hB1 _)
  let F : Γ ⧸ K.comap c → (H →L[ℂ] H) := fun x => a (c (Quotient.out x)) • B (γ * c (Quotient.out x))
  let G : Γ ⧸ K.comap c → (H →L[ℂ] H) := fun x => a (c (Quotient.out x)) • B (c (Quotient.out x))
  have hF : Summable F := Summable.of_norm_bounded hsum (fun x => hnorm _ _)
  have hG : Summable G := Summable.of_norm_bounded hsum (fun x => by simpa using hnorm (r x) 1)
  let q : Γ ⧸ K.comap c → Set Γ := fun x => dc K c (r x)
  have hfib : ∀ b : Set Γ, ∑' y : {x // q x = b}, F y.1 = B γ * ∑' y : {x // q x = b}, G y.1 := by
    intro b
    by_cases hb : ∃ x0, q x0 = b
    swap
    · push_neg at hb
      haveI : IsEmpty {x // q x = b} := ⟨fun y => hb y.1 y.2⟩
      simp [tsum_empty]
    obtain ⟨x0, rfl⟩ := hb
    obtain ⟨C, hC⟩ := hex (r x0) (hr_fix x0)
    have memfib : ∀ x, q x = q x0 ↔ r x ∈ dc K c (r x0) := fun x =>
      ⟨fun h => by rw [← show dc K c (r x) = dc K c (r x0) from h]; exact mem_dc_self K c _,
       fun h => dc_eq_of_mem K c h⟩
    have hval : ∀ δ ∈ C, ∃ k, k ∈ K ∧ c k = k ∧ r (QuotientGroup.mk δ) = δ * k := by
      intro δ hδ
      obtain ⟨h, hh, he⟩ := out_mk K c δ
      exact ⟨c h, hh, hc h, by show c (Quotient.out _) = _; rw [he, map_mul, (hC.1 δ hδ).1]⟩
    have haδ : ∀ δ ∈ C, ∀ k, k ∈ K → a (δ * k) = a (r x0) := by
      intro δ hδ k hk
      obtain ⟨_, k₁, k₂, h1, -, h3, -, hδe⟩ := hC.1 δ hδ
      rw [hδe, ← ha (r x0) k₁ (k₂ * k) h1 (K.mul_mem h3 hk)]
      simp [mul_assoc]
    have hFv : ∀ δ ∈ C, F (QuotientGroup.mk δ) = a (r x0) • B (γ * δ) := by
      intro δ hδ
      obtain ⟨k, hk, -, he⟩ := hval δ hδ
      show a (r _) • B (γ * r _) = _
      rw [he, haδ δ hδ k hk, ← mul_assoc, hB _ _ hk]
    have hGv : ∀ δ ∈ C, G (QuotientGroup.mk δ) = a (r x0) • B δ := by
      intro δ hδ
      obtain ⟨k, hk, -, he⟩ := hval δ hδ
      show a (r _) • B (r _) = _
      rw [he, haδ δ hδ k hk, hB _ _ hk]
    let e : C → {x // q x = q x0} := fun δ => ⟨QuotientGroup.mk δ.1, (memfib _).2 (by
      obtain ⟨k, hk, hck, he⟩ := hval δ.1 δ.2
      rw [he]
      obtain ⟨_, k₁, k₂, h1, h2, h3, h4, hδe⟩ := hC.1 δ.1 δ.2
      exact mul_mem_dc K c ⟨k₁, k₂, h1, h2, h3, h4, hδe⟩ hk hck)⟩
    have hinj : Function.Injective e := by
      rintro ⟨δ, hδ⟩ ⟨δ', hδ'⟩ h
      have h' : (QuotientGroup.mk δ : Γ ⧸ K.comap c) = QuotientGroup.mk δ' := congrArg Subtype.val h
      have hfix : c (δ⁻¹ * δ') = δ⁻¹ * δ' := by rw [map_mul, map_inv, (hC.1 δ hδ).1, (hC.1 δ' hδ').1]
      rw [QuotientGroup.eq, Subgroup.mem_comap, hfix] at h'
      apply Subtype.ext
      exact (hC.2 δ' (hC.1 δ' hδ').2).unique ⟨hδ, h', hfix⟩ ⟨hδ', by simp, by simp⟩
    have hsurj : Function.Surjective e := by
      rintro ⟨x, hx⟩
      obtain ⟨k₁, k₂, h1, h2, h3, h4, hxe⟩ := (memfib x).1 hx
      obtain ⟨δ, ⟨hδ, hK, -⟩, -⟩ := hC.2 (r x) ⟨k₁, k₂, h1, h2, h3, h4, hxe⟩
      refine ⟨⟨δ, hδ⟩, Subtype.ext ?_⟩
      show (QuotientGroup.mk δ : Γ ⧸ K.comap c) = x
      conv_rhs => rw [← QuotientGroup.out_eq' x]
      rw [QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv, (hC.1 δ hδ).1]
      exact hK
    have hT : ∀ f : Γ ⧸ K.comap c → (H →L[ℂ] H),
        ∑' y : {x // q x = q x0}, f y.1 = ∑ δ ∈ C, f (QuotientGroup.mk δ) := by
      intro f
      rw [← Equiv.tsum_eq (Equiv.ofBijective e ⟨hinj, hsurj⟩) (fun y : {x // q x = q x0} => f y.1), tsum_fintype]
      exact Finset.sum_coe_sort C (fun δ => f (QuotientGroup.mk δ))
    rw [hT, hT, Finset.sum_congr rfl hFv, Finset.sum_congr rfl hGv, ← Finset.smul_sum, ← Finset.smul_sum,
      hH (r x0) C (hr_fix x0) hC γ, mul_smul_comm]
  let eσ := Equiv.sigmaFiberEquiv q
  have hFs : HasSum (fun b : Set Γ => ∑' y : {x // q x = b}, F y.1) (∑' x, F x) :=
    HasSum.sigma ((eσ.hasSum_iff).2 hF.hasSum) (fun b => (hF.comp_injective Subtype.val_injective).hasSum)
  have hGs : HasSum (fun b : Set Γ => ∑' y : {x // q x = b}, G y.1) (∑' x, G x) :=
    HasSum.sigma ((eσ.hasSum_iff).2 hG.hasSum) (fun b => (hG.comp_injective Subtype.val_injective).hasSum)
  have hGm := hGs.mul_left (B γ)
  rw [← funext hfib] at hGm
  have := hFs.unique hGm
  show HasSum F _
  rw [← this]
  exact hF.hasSum
