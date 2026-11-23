import Formalism.WachLatticeTwists.HerrComplexInjectivity.Statement
import Formalism.WachLatticeTwists.WachProductBases.WachConsequencesFurther
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.DualWByLettersExtended

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

theorem base_case_b : StatBaseB := by
  intro ℓ _ A _ _ S hℓ
  obtain ⟨-, h2, h3⟩ := base_wach_holds ℤ_[ℓ] A S
  obtain ⟨⟨tX, hX⟩, ⟨tQ, hQ⟩, -, -, -, -⟩ := base_facts_holds ℤ_[ℓ] A S
  have hs0 : S.s ≠ 0 := by have := S.hs; omega
  have hu1 : S.u - 1 = (ℓ : ℤ_[ℓ]) ^ S.s * S.c₀ := by simp [HidaSetting.u, hℓ]
  refine ⟨hℓ, S.φ_X, h2, h3, S.hs, fun h => S.hs2 (hℓ.trans h), ?_, ?_, ?_, ?_⟩
  · have h1 : IsUnit (S.u + -((ℓ : ℤ_[ℓ]) ^ S.s * S.c₀)) := by
      rw [← hu1]; simp
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h | h
    · exact h
    · exfalso
      have h' : IsUnit ((ℓ : ℤ_[ℓ]) ^ S.s * S.c₀) := by simpa using h
      have h'' := isUnit_of_mul_isUnit_left h'
      exact PadicInt.prime_p.not_isUnit ((isUnit_pow_iff hs0).1 h'')
  · intro hc
    rw [hu1, PadicInt.valuation_p_pow_mul _ _ hc.ne_zero]
    obtain ⟨d, hd⟩ := hc.exists_right_inv
    have hd0 : d ≠ 0 := by rintro rfl; simp at hd
    have := PadicInt.valuation_mul hc.ne_zero hd0
    rw [hd, PadicInt.valuation_one] at this
    omega
  · show S.Q ∈ mI S
    rw [hQ, hX]
    refine (mI S).add_mem (Ideal.subset_span (by simp)) ?_
    rw [mul_assoc]
    exact (mI S).mul_mem_right _ (Ideal.subset_span (by simp))
  · intro a ha
    show S.φ a ∈ mI S
    have : mI S ≤ (mI S).comap (S.φ : A →+* A) := by
      unfold mI
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · show (S.φ : A →+* A) (S.ℓ : A) ∈ Ideal.span {(S.ℓ : A), S.π}
        rw [map_natCast]
        exact Ideal.subset_span (by simp)
      · show S.φ S.π ∈ Ideal.span {(S.ℓ : A), S.π}
        rw [S.φπ, HidaSetting.one_add_pow_sub_one]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    exact this ha

theorem wach_lattice_holds : StatLattice := by
  intro ℓ _ A _ _ S ι pr D _ _ _ _ W M₀ V hℓ hV
  obtain ⟨hN, hφ, hγ⟩ := hV
  have hmem : ∀ x, x ∈ V.N ↔ ∀ i, x i ∈ W.N i := by
    intro x; rw [hN]; simp [Submodule.mem_pi]
  have hl : ∀ d : D, (ℓ : ℤ_[ℓ]) • d = (S.ℓ : A) • d := by
    intro d; rw [hℓ, ← algebraMap_smul A (ℓ : ℤ_[ℓ]) d, map_natCast]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨-, -, hsat, -⟩ n hn ⟨m, hm, h⟩
    choose m' hm' using fun i => W.Q_bij.2 (m i)
    have hn' : ∀ i, n i = (ℓ : ℤ_[ℓ]) • m' i := by
      intro i
      apply W.Q_bij.1
      show S.Q • n i = S.Q • ((ℓ : ℤ_[ℓ]) • m' i)
      have h1 : S.Q • m' i = m i := hm' i
      rw [smul_comm, h1]
      exact congrFun h i
    refine ⟨m', (hmem _).2 fun i => hsat i _ ?_, funext hn'⟩
    rw [← hl, ← hn']
    exact (hmem _).1 hn i
  · intro hreg n hn ⟨m, hm, h⟩
    choose m' hm' hm'' using fun i =>
      hreg i (n i) ((hmem _).1 hn i) ⟨m i, (hmem _).1 hm i, congrFun h i⟩
    exact ⟨m', (hmem _).2 hm', funext hm''⟩
  · intro h x hx
    funext i
    exact h _ (congrFun hx i)

theorem semilinear_case_b : StatSemiB := by
  intro ℓ _ A _ _ S ι pr D _ _ _ _ W M₀ V R P ρ κ _ _ _ _ _ _ _ L u jumps hRad hV hH hT hj y hy
  obtain ⟨hN, hφ, hγ⟩ := hV
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hH
  have hGQ := (base_wach_holds ℤ_[ℓ] A S).2.2 hRad
  have hmem : ∀ x, x ∈ V.N ↔ ∀ i, x i ∈ W.N i := by
    intro x; rw [hN]; simp [Submodule.mem_pi]
  let loc' : ρ → (ι → D) →ₗ[ℤ_[ℓ]] P := fun x => (L.loc x).comp (LinearMap.proj (L.lt x))
  refine consequence_two_top ℤ_[ℓ] A R S.base M₀ (ι → D) P V u M₀ (eigSet jumps M₀) ρ κ L.t L.γR L.locA
    loc' L.γl L.n L.a hGQ h1 h2 h3 h4 ?_ ?_ h7 ?_ h9 ?_ ?_ y hy
  · rintro x b d ⟨k, hk⟩
    exact h5 x b (d (L.lt x)) ⟨k, (hmem _).1 hk _⟩
  · rintro x d ⟨k, hk⟩
    show L.loc x (V.γ d (L.lt x)) = _
    rw [hγ]
    exact h6 x (d (L.lt x)) ⟨k, (hmem _).1 hk _⟩
  · intro x d hd
    exact h8 x _ ((hmem d).1 hd _)
  · rintro d ⟨k, hk⟩ hall
    refine (hmem d).2 fun i => hT i (d i) ⟨k, (hmem _).1 hk i⟩ ?_
    rintro x rfl
    exact hall x
  · intro x k j hj'
    exact Finset.mem_image.2 ⟨(L.a x k, j), Finset.mem_product.2 ⟨hj x k, hj'⟩, rfl⟩

theorem short_exact_sequence_holds : StatSES := by
  intro O A _ _ _ S ι _ pr D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ E M h M₀ H hR hD a0 a1 a2 b0 b1
    b2 c0 c1 c2 hP6 hM hH
  obtain ⟨-, -, -, -, V₀, V₁, V₂, Sq, n0, n1, n2, p0, g0, p1, g1, p2, g2, hi, hp, -, hX, -⟩ :=
    wach_top_statement O A S ι pr D₀ D₁ D₂ W₀ W₁ W₂ E M h M₀ H H hR hD a0 a1 a2 b0 b1 b2 c0 c1 c2 hP6 hM
      (fun i => by have := hH i; omega) hH
  exact ⟨V₀, V₁, V₂, Sq, ⟨n0, p0, g0⟩, ⟨n1, p1, g1⟩, ⟨n2, p2, g2⟩, hi, hp, hX⟩

theorem wach_ext {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
    {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (V V' : WachMod B M D) (h1 : V.N = V'.N) (h2 : V.φ = V'.φ) (h3 : V.γ = V'.γ) : V = V' := by
  cases V; cases V'
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem product_unique_holds : StatProdUnique := by
  intro O A _ _ _ S ι pr D _ _ _ _ W M₀ V V' hV hV'
  obtain ⟨a, b, c⟩ := hV
  obtain ⟨a', b', c'⟩ := hV'
  exact wach_ext V V' (a.trans a'.symm)
    (LinearMap.ext fun x => funext fun i => (b x i).trans (b' x i).symm)
    (LinearMap.ext fun x => funext fun i => (c x i).trans (c' x i).symm)

theorem extension_holds : StatExt := by
  intro ℓ _ A _ _ S ι _ pr D _ _ _ _ W M₀ V Hh _ _ cl Hf M h H hR hD hV hP2 hP5 hL hM hH hE κ hκ
  obtain ⟨Dp, Dt, i1, i2, i3, i4, i5, i6, i7, i8, Wp, Wt, E, e, p2p, p2t, p5p, p5t, lp, lt, p6, he,
    hφe, hγe, hdict⟩ := hE κ hκ
  obtain ⟨V₀, Vp, Vt, Sq, v0, vp, vt, hi, hp, hX⟩ := short_exact_sequence_holds ℤ_[ℓ] A S ι pr D Dp Dt W Wp Wt E M h
    M₀ H hR hD hP2 p2p p2t hP5 p5p p5t hL lp lt p6 hM hH
  obtain rfl : V₀ = V := product_unique_holds _ _ S ι pr D W M₀ V₀ V v0 hV
  refine ⟨{ Dp := ι → Dp, Dt := ι → Dt, Wp := Vp, Wt := Vt, S := Sq, e := e, e_mem := ?_, φe := ?_,
            γe := ?_ }, hX, ?_⟩
  · rw [vt.1]; simpa [Submodule.mem_pi] using he
  · funext i; exact (vt.2.1 e i).trans (hφe i)
  · funext i; exact (vt.2.2 e i).trans (hγe i)
  · intro c x p h1 h2 h3
    refine hdict c x p (fun i => ?_) (fun i => ?_) (fun i => ?_)
    · have := congrFun h1 i
      rw [hp] at this
      exact this
    · have := congrFun h2 i
      rw [hi] at this
      rw [this]
      show Vp.φ x i - x i = _
      rw [vp.2.1]
    · have := congrFun h3 i
      rw [hi] at this
      rw [this]
      show Vp.γ x i - x i = _
      rw [vp.2.2]

end Formalism.RepresentationBoundsCohomology.JN
