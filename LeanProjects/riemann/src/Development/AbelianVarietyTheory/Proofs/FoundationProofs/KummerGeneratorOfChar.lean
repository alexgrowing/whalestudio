import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem zeta_pow_val_add {Ω : Type} [Field Ω] {N : ℕ} [NeZero N] {ζ : Ω} (hζN : ζ ^ N = 1) (x y : ZMod N) :
    ζ ^ (x + y).val = ζ ^ x.val * ζ ^ y.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.div_add_mod (x.val + y.val) N, pow_add, pow_mul, hζN, one_pow, one_mul]

theorem kummer_generator_of_char : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → ∀ (E : IntermediateField K Ω) (χ : (Ω ≃ₐ[K] Ω) → ZMod N),
  IsLocallyConstant χ → (∀ g ∈ E.fixingSubgroup, ∀ h ∈ E.fixingSubgroup, χ (g * h) = χ g + χ h) →
  ∃ θ : Ω, θ ≠ 0 ∧ θ ^ N ∈ E ∧ ∀ g ∈ E.fixingSubgroup, g θ = ζ ^ (χ g).val * θ := by
  intro K Ω _ _ _ _ _ N ζ hN hζ hfix E χ hχ hadd
  haveI : NeZero N := ⟨hN.ne'⟩
  classical
  set H := E.fixingSubgroup with hH
  have hζN : ζ ^ N = 1 := hζ.pow_eq_one
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  have h1 : χ 1 = 0 := by
    have := hadd 1 H.one_mem 1 H.one_mem
    simpa using this

  have hV : {g : Ω ≃ₐ[K] Ω | χ g = 0} ∈ nhds (1 : Ω ≃ₐ[K] Ω) := by
    have := (hχ.isOpen_fiber (χ 1)).mem_nhds (show (1 : Ω ≃ₐ[K] Ω) ∈ χ ⁻¹' {χ 1} from rfl)
    simpa [h1] using this
  obtain ⟨F, hFfin, hFV⟩ := (krullTopology_mem_nhds_one_iff K Ω _).mp hV

  let r : (Ω ≃ₐ[K] Ω) → (F →ₐ[K] Ω) := fun g => (g : Ω →ₐ[K] Ω).comp F.val
  have hr : ∀ g x, r g x = g (x : Ω) := fun _ _ => rfl
  have hrχ : ∀ g ∈ H, ∀ h ∈ H, r g = r h → χ g = χ h := by
    intro g hg h hh he
    have hm : h⁻¹ * g ∈ H := H.mul_mem (H.inv_mem hh) hg
    have hF : h⁻¹ * g ∈ F.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have := congrArg (fun φ => φ ⟨x, hx⟩) he
      simp only [hr] at this
      simp [AlgEquiv.mul_apply, this]
    have h0 : χ (h⁻¹ * g) = 0 := hFV hF
    have := hadd h hh (h⁻¹ * g) hm
    rw [mul_inv_cancel_left, h0, add_zero] at this
    exact this
  haveI : FiniteDimensional K F := hFfin
  let ι := {φ : F →ₐ[K] Ω // ∃ g ∈ H, r g = φ}
  haveI : Finite (F →ₐ[K] Ω) := inferInstance
  haveI : Fintype ι := Fintype.ofFinite ι
  let s : ι → (Ω ≃ₐ[K] Ω) := fun i => i.2.choose
  have hsH : ∀ i, s i ∈ H := fun i => i.2.choose_spec.1
  have hsr : ∀ i, r (s i) = i.1 := fun i => i.2.choose_spec.2
  let a : (Ω ≃ₐ[K] Ω) → Ω := fun g => ζ ^ (χ g).val
  have ha0 : ∀ g, a g ≠ 0 := fun g => pow_ne_zero _ hζ0
  have hamul : ∀ g ∈ H, ∀ h ∈ H, a (g * h) = a g * a h := by
    intro g hg h hh
    simp only [a, hadd g hg h hh, zeta_pow_val_add hζN]
  have hafix : ∀ (g h : Ω ≃ₐ[K] Ω), g (a h) = a h := by
    intro g h; simp only [a, map_pow, hfix]
  let w : ι → Ω := fun i => (a (s i))⁻¹

  let v : ι → (F →* Ω) := fun i => (i.1 : F →+* Ω).toMonoidHom
  have hv : Function.Injective v := by
    intro i j hij
    apply Subtype.ext
    apply AlgHom.ext
    intro x
    exact DFunLike.congr_fun hij x
  have hli := (linearIndependent_monoidHom F Ω).comp v hv
  obtain ⟨c, hc⟩ : ∃ c : F, ∑ i, w i * i.1 c ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hz : ∑ i, w i • ((v i : F →* Ω) : F → Ω) = 0 := by
      funext x
      simpa [Finset.sum_apply, v] using hcon x
    have := Fintype.linearIndependent_iff.mp hli w hz ⟨r 1, 1, H.one_mem, rfl⟩
    exact inv_ne_zero (ha0 _) this
  have hmain : ∀ g ∈ H, g (∑ i, w i * i.1 c) = a g * ∑ i, w i * i.1 c := by
    intro g hg
    let e : ι → ι := fun i => ⟨r (g * s i), g * s i, H.mul_mem hg (hsH i), rfl⟩
    have hic : ∀ i : ι, i.1 c = s i (c : Ω) := by
      intro i; rw [← hsr i]; exact hr _ _
    have hec : ∀ i, (e i).1 c = g (i.1 c) := by
      intro i; rw [hic i]; rfl
    have hwe : ∀ i, w i = a g * w (e i) := by
      intro i
      have hχe : χ (s (e i)) = χ (g * s i) :=
        hrχ _ (hsH (e i)) _ (H.mul_mem hg (hsH i)) (hsr (e i))
      have : a (s (e i)) = a g * a (s i) := by
        rw [← hamul g hg (s i) (hsH i)]; simp only [a, hχe]
      simp only [w, this, mul_inv, ← mul_assoc, mul_inv_cancel₀ (ha0 g), one_mul]
    have he : Function.Injective e := by
      intro i j hij
      have h2 : r (g * s i) = r (g * s j) := congrArg Subtype.val hij
      apply Subtype.ext
      rw [← hsr i, ← hsr j]
      apply AlgHom.ext
      intro x
      have := DFunLike.congr_fun h2 x
      simp only [hr, AlgEquiv.mul_apply] at this
      simpa [hr] using g.injective this
    have hb : Function.Bijective e := Finite.injective_iff_bijective.mp he
    rw [map_sum, Finset.mul_sum]
    simp only [map_mul, hfix, w, map_inv₀, hafix]
    refine (Fintype.sum_bijective e hb _ _ ?_)
    intro i
    have h3 := hwe i
    simp only [w] at h3
    rw [h3, ← hec i]; ring
  refine ⟨∑ i, w i * i.1 c, hc, ?_, ?_⟩
  · haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro g hg
    have key := hmain g hg
    rw [map_pow, key, mul_pow]
    have : a g ^ N = 1 := by
      show (ζ ^ (χ g).val) ^ N = 1
      rw [← pow_mul, mul_comm, pow_mul, hζN, one_pow]
    rw [this, one_mul]
  · exact hmain

end GlobalTheory
