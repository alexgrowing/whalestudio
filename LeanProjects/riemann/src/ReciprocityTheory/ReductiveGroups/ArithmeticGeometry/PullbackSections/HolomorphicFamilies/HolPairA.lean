import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetC

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isHolTo_comp {Y Y' : Scheme.{0}} {B : Set V} {y : V → (Sp ℂ ⟶ Y)} (hy : IsHolTo B y) (φ : Y ⟶ Y') :
    IsHolTo B (fun b => y b ≫ φ) := by
  intro U f
  have hpre : ∀ b, (y b ≫ φ) ⁻¹ᵁ U = y b ⁻¹ᵁ (φ ⁻¹ᵁ U) := fun b => by
    first
      | rfl
      | simp
  obtain ⟨h1, h2⟩ := hy (φ ⁻¹ᵁ U) (φ.app U f)
  simp only [hpre]
  refine ⟨h1, ?_⟩
  refine h2.congr (fun b hb => ?_)
  have hb2 : ⊤ ≤ (y b ≫ φ) ⁻¹ᵁ U := by
    rw [hpre]
    exact hb.2
  unfold valAt'
  rw [dif_pos hb2, dif_pos hb.2]
  first
    | rfl
    | simp [Scheme.comp_app]
    | (simp only [Scheme.comp_app]; done)

theorem isHolTo_of_local {Y : Scheme.{0}} {B : Set V} {y : V → (Sp ℂ ⟶ Y)}
    (h : ∀ (U : Y.Opens) (f : Γ(Y, U)) (b₀ : V), b₀ ∈ B → ⊤ ≤ y b₀ ⁻¹ᵁ U →
      ∃ N ∈ nhds b₀, N ⊆ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun b => valAt' (y b) U f) N) :
    IsHolTo B y := by
  unfold IsHolTo
  intro U f
  have hS : IsOpen {b | b ∈ B ∧ ⊤ ≤ y b ⁻¹ᵁ U} := by
    rw [isOpen_iff_mem_nhds]
    intro b hb
    obtain ⟨N, hN, hNS, -⟩ := h U f b hb.1 hb.2
    exact Filter.mem_of_superset hN hNS
  refine ⟨hS, fun b hb => ?_⟩
  obtain ⟨N, hN, -, hd⟩ := h U f b hb.1 hb.2
  exact (hd.differentiableAt hN).differentiableWithinAt

theorem isHolTo_of_affine {T : Scheme.{0}} [IsAffine T] {B : Set V} (hB : IsOpen B) {z : V → (Sp ℂ ⟶ T)}
    (hz : ∀ r : Γ(T, ⊤), DifferentiableOn ℂ (fun b => valAt' (z b) ⊤ r) B) : IsHolTo B z := by
  refine isHolTo_of_local fun U f b₀ hb₀ hU => ?_
  have hmem : (z b₀) cpt ∈ U := hU (Set.mem_univ _)
  obtain ⟨r, hrU, hr0⟩ := (isAffineOpen_top T).exists_basicOpen_le (V := U) ⟨(z b₀) cpt, hmem⟩ trivial
  have htop : ∀ b, ⊤ ≤ z b ⁻¹ᵁ (⊤ : T.Opens) := fun b p _ => trivial

  set N := {b ∈ B | valAt' (z b) ⊤ r ≠ 0} with hNdef
  have hNo : IsOpen N := (hz r).continuousOn.isOpen_inter_preimage hB isOpen_ne
  have hmemD : ∀ b, valAt' (z b) ⊤ r ≠ 0 → ⊤ ≤ z b ⁻¹ᵁ T.basicOpen r := fun b hb =>
    top_le_of_mem ((valAt'_ne_zero_iff (z b) ⊤ (htop b) r cpt).1 hb)
  have hb0N : b₀ ∈ N := ⟨hb₀, (valAt'_ne_zero_iff (z b₀) ⊤ (htop b₀) r cpt).2 hr0⟩

  obtain ⟨⟨hh, s⟩, hk⟩ := IsLocalization.surj (Submonoid.powers r)
    (T.presheaf.map (homOfLE hrU).op f)
  obtain ⟨k, hks⟩ := s.2
  dsimp only at hk
  have hval : ∀ b ∈ N, valAt' (z b) U f * valAt' (z b) ⊤ r ^ k = valAt' (z b) ⊤ hh := by
    intro b hb
    have hD := hmemD b hb.2
    have e := congrArg (valAt' (z b) (T.basicOpen r)) hk
    rw [valAt'_mul, valAt'_res (z b) hrU hD] at e
    have e2 : ∀ x : Γ(T, ⊤), valAt' (z b) (T.basicOpen r) (algebraMap Γ(T, ⊤) Γ(T, T.basicOpen r) x) =
        valAt' (z b) ⊤ x := fun x => valAt'_res (z b) le_top hD x
    rw [e2, e2, ← hks] at e
    have e3 : valAt' (z b) ⊤ (r ^ k) = valAt' (z b) ⊤ r ^ k := map_pow (valHom (z b) ⊤ (htop b)) r k
    rw [e3] at e
    exact e
  refine ⟨N, hNo.mem_nhds hb0N, fun b hb => ⟨hb.1, (hmemD b hb.2).trans (Scheme.Hom.preimage_mono _ hrU)⟩, ?_⟩
  have h1 : DifferentiableOn ℂ (fun b => valAt' (z b) ⊤ hh) N := (hz hh).mono fun b (hb : b ∈ N) => hb.1
  have h2 : DifferentiableOn ℂ ((fun b => valAt' (z b) ⊤ r) ^ k) N :=
    ((hz r).mono fun b (hb : b ∈ N) => hb.1).pow k
  have h3 : DifferentiableOn ℂ ((fun b => valAt' (z b) ⊤ r) ^ k)⁻¹ N :=
    h2.inv fun b (hb : b ∈ N) => by simp only [Pi.pow_apply]; exact pow_ne_zero _ hb.2
  have h4 := h1.mul h3
  refine h4.congr fun b hb => ?_
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply]
  rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hb.2)]
  exact hval b hb

end ReciprocityTheory.ChartRestriction.G.PullbackSections
