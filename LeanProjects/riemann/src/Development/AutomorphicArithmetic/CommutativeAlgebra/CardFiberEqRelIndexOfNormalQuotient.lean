import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.card_fiber_eq_relIndex_of_normal_quotient :
    ∀ (Γ : Type) [Group Γ] (K₀ H KN Km : Subgroup Γ), Count → Km ≤ KN → KN ≤ K₀ → Km ≤ H → H ≤ K₀ → (∀ k ∈ K₀, ∀ u ∈ Km, k * u * k⁻¹ ∈ Km) → Km.relIndex K₀ ≠ 0 → ∀ (V F : Type) (act : KN → V), Function.Surjective act → (∀ u u' : KN, act u = act u' ↔ (u : Γ)⁻¹ * u' ∈ Km) → ∀ (κ : (K₀ ⧸ KN.subgroupOf K₀) → V → F), Nat.card F = H.relIndex K₀ → (∀ (c₁ c₂ : K₀ ⧸ KN.subgroupOf K₀) (u₁ u₂ : KN), κ c₁ (act u₁) = κ c₂ (act u₂) → ((c₁.out : Γ) * u₁) * ((c₂.out : Γ) * u₂)⁻¹ ∈ H) → ∀ ζ : F, Nat.card {x : (K₀ ⧸ KN.subgroupOf K₀) × V // κ x.1 x.2 = ζ} = Km.relIndex H := by
  intro Γ _ K₀ H KN Km hC hmN hNK hmH hHK hn hidx V F act hs he κ hF sep ζ
  classical
  let cl : K₀ → (K₀ ⧸ KN.subgroupOf K₀) := fun x => ((x⁻¹ : K₀) : K₀ ⧸ KN.subgroupOf K₀)
  have hmem : ∀ x : K₀, ((cl x).out : Γ)⁻¹ * (x : Γ)⁻¹ ∈ KN := by
    intro x
    have h := QuotientGroup.eq.mp (QuotientGroup.out_eq' (cl x))
    simpa [Subgroup.mem_subgroupOf] using h
  let uu : K₀ → KN := fun x => ⟨((cl x).out : Γ)⁻¹ * (x : Γ)⁻¹, hmem x⟩
  have key : ∀ x : K₀, ((cl x).out : Γ) * (uu x : Γ) = (x : Γ)⁻¹ := by
    intro x
    show ((cl x).out : Γ) * (((cl x).out : Γ)⁻¹ * (x : Γ)⁻¹) = (x : Γ)⁻¹
    group
  have hcleq : ∀ x y : K₀, cl x = cl y → (uu x : Γ)⁻¹ * (uu y : Γ) = (x : Γ) * (y : Γ)⁻¹ := by
    intro x y h
    have hx := key x
    have hy := key y
    rw [h] at hx
    rw [eq_inv_mul_iff_mul_eq.mpr hx, eq_inv_mul_iff_mul_eq.mpr hy]
    group

  have hwd : ∀ x y : K₀, (x : Γ)⁻¹ * (y : Γ) ∈ Km → (cl x, act (uu x)) = (cl y, act (uu y)) := by
    intro x y h
    have h1 : (x : Γ) * (y : Γ)⁻¹ ∈ Km := by
      have := hn x x.2 _ (Km.inv_mem h)
      have e : (x : Γ) * ((x : Γ)⁻¹ * (y : Γ))⁻¹ * (x : Γ)⁻¹ = (x : Γ) * (y : Γ)⁻¹ := by group
      rwa [e] at this
    have hc : cl x = cl y := by
      refine QuotientGroup.eq.mpr ?_
      rw [Subgroup.mem_subgroupOf]
      simpa using hmN h1
    refine Prod.ext hc ?_
    show act (uu x) = act (uu y)
    rw [he, hcleq x y hc]
    exact h1
  let f : K₀ → (K₀ ⧸ KN.subgroupOf K₀) × V := fun x => (cl x, act (uu x))
  let Φ : (K₀ ⧸ Km.subgroupOf K₀) → (K₀ ⧸ KN.subgroupOf K₀) × V :=
    Quotient.lift f (fun a b hab => hwd a b (by
      have := QuotientGroup.leftRel_apply.mp hab
      simpa [Subgroup.mem_subgroupOf] using this))
  have hΦ : ∀ x : K₀, Φ (x : K₀ ⧸ Km.subgroupOf K₀) = (cl x, act (uu x)) := fun _ => rfl
  have hinj : Function.Injective Φ := by
    intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [hΦ, hΦ] at hab
    have hc : cl x = cl y := congrArg Prod.fst hab
    have ha : act (uu x) = act (uu y) := congrArg Prod.snd hab
    rw [he, hcleq x y hc] at ha
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    have := hn _ (K₀.inv_mem x.2) _ (Km.inv_mem ha)
    have e : (x : Γ)⁻¹ * ((x : Γ) * (y : Γ)⁻¹)⁻¹ * ((x : Γ)⁻¹)⁻¹ = (x : Γ)⁻¹ * (y : Γ) := by group
    rwa [e] at this
  have hsurj : Function.Surjective Φ := by
    rintro ⟨c, v⟩
    obtain ⟨u, rfl⟩ := hs v
    let x : K₀ := (c.out * (⟨u, hNK u.2⟩ : K₀))⁻¹
    refine ⟨(x : K₀ ⧸ Km.subgroupOf K₀), ?_⟩
    rw [hΦ]
    have hc : cl x = c := by
      have h1 : cl x = ((c.out * (⟨u, hNK u.2⟩ : K₀) : K₀) : K₀ ⧸ KN.subgroupOf K₀) := by
        show (((x⁻¹ : K₀)) : K₀ ⧸ KN.subgroupOf K₀) = _
        simp [x]
      rw [h1, ← QuotientGroup.out_eq' c]
      refine QuotientGroup.eq.mpr ?_
      rw [Subgroup.mem_subgroupOf]
      simp [Subgroup.mem_subgroupOf]
    refine Prod.ext hc ?_
    show act (uu x) = act u
    congr 1
    apply Subtype.ext
    have hx := key x
    rw [hc] at hx
    rw [eq_inv_mul_iff_mul_eq.mpr hx]
    simp [x]
  let E := Equiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hcount := hC Γ K₀ H Km hmH hHK hidx F (fun a => κ (Φ a).1 (Φ a).2) hF (by
    intro x y h
    rw [hΦ, hΦ] at h
    have := sep _ _ _ _ h
    rw [key x, key y] at this
    simpa using this) ζ
  rw [← hcount]
  exact Nat.card_congr (Equiv.subtypeEquiv E (fun a => Iff.rfl)).symm
