import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev

theorem UpperTheory.V.Af.Tw.verGroup :
    UpperTheory.V.Af.Tw.VerGroup := by
  unfold UpperTheory.V.Af.Tw.VerGroup
  intro H Γ B _ _ _ _ _ _ _ _ _ r hr hidx κ hκ
  classical
  set R := r.range with hR
  have hinj : Function.Injective r := hr.injective
  have hrs : ∀ s, r s ∈ R := fun s => MonoidHom.mem_range.mpr ⟨s, rfl⟩
  have hmem : ∀ a b : Γ, a * b ∈ R ↔ (a ∈ R ↔ b ∈ R) := fun a b =>
    Subgroup.mul_mem_iff_of_index_two hidx
  have hnorm : R.Normal := Subgroup.normal_of_index_eq_two hidx
  have hsq : ∀ g, g ∉ R → g * g ∈ R := fun g _ => (hmem g g).mpr Iff.rfl
  obtain ⟨g0, hg0⟩ : ∃ g0 : Γ, g0 ∉ R := by
    by_contra hcon
    push_neg at hcon
    have htop : R = ⊤ := eq_top_iff.mpr fun x _ => hcon x
    rw [htop, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)
  let pre : Γ → H := fun γ => if h : γ ∈ R then (MonoidHom.mem_range.mp h).choose else 1
  have hpre : ∀ γ, γ ∈ R → r (pre γ) = γ := fun γ h => by
    dsimp only [pre]
    rw [dif_pos h]
    exact (MonoidHom.mem_range.mp h).choose_spec
  let k : Γ → B := fun γ => κ (pre γ)
  have kr : ∀ s, k (r s) = κ s := fun s => by
    show κ (pre (r s)) = κ s
    rw [hinj (hpre _ (hrs s))]
  have kmul : ∀ a, a ∈ R → ∀ b, b ∈ R → k (a * b) = k a * k b := by
    intro a ha b hb
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp ha
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hb
    rw [← map_mul, kr, kr, kr, map_mul]
  have kinv : ∀ a, a ∈ R → k a⁻¹ = (k a)⁻¹ := by
    intro a ha
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp ha
    rw [← map_inv, kr, kr, map_inv]
  have k1 : k 1 = 1 := by
    have h := kr 1
    rwa [map_one, map_one] at h
  have L : ∀ g, g ∉ R → ∀ x, x ∈ R → k (g * x * g⁻¹) = k (g0 * x * g0⁻¹) := by
    intro g hg x hx
    have hh : g0⁻¹ * g ∈ R :=
      (hmem _ _).mpr (iff_of_false (fun h => hg0 (by simpa using R.inv_mem h)) hg)
    have hc : g0 * (g0⁻¹ * g) * g0⁻¹ ∈ R := hnorm.conj_mem _ hh g0
    have hx' : g0 * x * g0⁻¹ ∈ R := hnorm.conj_mem _ hx g0
    have e1 : g * x * g⁻¹ = (g0 * (g0⁻¹ * g) * g0⁻¹) * (g0 * x * g0⁻¹) *
        (g0 * (g0⁻¹ * g) * g0⁻¹)⁻¹ := by group
    rw [e1, kmul _ (R.mul_mem hc hx') _ (R.inv_mem hc), kmul _ hc _ hx', kinv _ hc,
      mul_inv_cancel_comm]
  let f : Γ → B := fun γ => if γ ∈ R then k γ * k (g0 * γ * g0⁻¹) else k (γ * γ)
  have fin : ∀ γ, γ ∈ R → f γ = k γ * k (g0 * γ * g0⁻¹) := fun γ h => if_pos h
  have fout : ∀ γ, γ ∉ R → f γ = k (γ * γ) := fun γ h => if_neg h
  have fmul : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    by_cases hx : x ∈ R <;> by_cases hy : y ∈ R
    · have hxy := R.mul_mem hx hy
      have cx := hnorm.conj_mem _ hx g0
      have cy := hnorm.conj_mem _ hy g0
      rw [fin _ hxy, fin _ hx, fin _ hy,
        show g0 * (x * y) * g0⁻¹ = (g0 * x * g0⁻¹) * (g0 * y * g0⁻¹) by group,
        kmul _ hx _ hy, kmul _ cx _ cy, mul_mul_mul_comm]
    · have hxy : x * y ∉ R := fun h => hy (((hmem x y).mp h).mp hx)
      have c1 : y * x * y⁻¹ ∈ R := hnorm.conj_mem _ hx y
      rw [fout _ hxy, fin _ hx, fout _ hy,
        show x * y * (x * y) = x * (y * x * y⁻¹) * (y * y) by group,
        kmul _ (R.mul_mem hx c1) _ (hsq y hy), kmul _ hx _ c1, L y hy x hx]
    · have hxy : x * y ∉ R := fun h => hx (((hmem x y).mp h).mpr hy)
      have c1 : x * y * x⁻¹ ∈ R := hnorm.conj_mem _ hy x
      rw [fout _ hxy, fout _ hx, fin _ hy,
        show x * y * (x * y) = (x * y * x⁻¹) * (x * x) * y by group,
        kmul _ (R.mul_mem c1 (hsq x hx)) _ hy, kmul _ c1 _ (hsq x hx), L x hx y hy,
        mul_comm (k (g0 * y * g0⁻¹)), mul_assoc, mul_comm (k (g0 * y * g0⁻¹))]
    · have hxy : x * y ∈ R := (hmem x y).mpr (iff_of_false hx hy)
      have hyx : y * x ∈ R := (hmem y x).mpr (iff_of_false hy hx)
      have hyy := hsq y hy
      have hxx := hsq x hx
      have c1 : x * (y * y) * x⁻¹ ∈ R := hnorm.conj_mem _ hyy x
      rw [fin _ hxy, fout _ hx, fout _ hy, ← L y hy _ hxy,
        show y * (x * y) * y⁻¹ = y * x by group, ← kmul _ hxy _ hyx,
        show x * y * (y * x) = x * (y * y) * x⁻¹ * (x * x) by group,
        kmul _ c1 _ hxx, L x hx _ hyy, ← L y hy _ hyy,
        show y * (y * y) * y⁻¹ = y * y by group, mul_comm]
  let ν : Γ →* B :=
    { toFun := f
      map_one' := by
        show f 1 = 1
        rw [fin _ R.one_mem, mul_one, mul_inv_cancel, k1, mul_one]
      map_mul' := fmul }
  have hσ : Continuous (fun s : H => pre (g0 * r s * g0⁻¹)) := by
    rw [hr.toIsEmbedding.toIsInducing.continuous_iff]
    have hcomp : (r ∘ fun s : H => pre (g0 * r s * g0⁻¹)) = fun s => g0 * r s * g0⁻¹ :=
      funext fun s => hpre _ (hnorm.conj_mem _ (hrs s) g0)
    rw [hcomp]
    exact (continuous_const.mul hr.continuous).mul continuous_const
  have hνr : (ν ∘ r) = fun s => κ s * κ (pre (g0 * r s * g0⁻¹)) := by
    funext s
    show f (r s) = _
    rw [fin _ (hrs s), kr]
  have hcont : Continuous ν := by
    apply continuous_of_continuousAt_one
    have h1 : ContinuousAt (ν ∘ r) 1 := by
      rw [hνr]
      exact (hκ.mul (hκ.comp hσ)).continuousAt
    rw [hr.continuousAt_iff, map_one] at h1
    exact h1
  refine ⟨ν, hcont, fun g hg => ⟨fun s s' hs => ?_, fun t ht => ?_⟩⟩
  · show κ s * κ s' = f (r s)
    rw [fin _ (hrs s), kr, ← L g hg _ (hrs s), ← hs, kr]
  · show κ t = f g
    rw [fout _ hg, ← ht, kr]
