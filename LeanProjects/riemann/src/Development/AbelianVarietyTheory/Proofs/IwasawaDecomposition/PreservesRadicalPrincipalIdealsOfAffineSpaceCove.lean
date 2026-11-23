import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle.AffRad

theorem C_dvd_of_C_dvd_pow {A σ : Type} [CommRing A] {g : A} (hg : ∀ (x : A) (n : ℕ), g ∣ x ^ n → g ∣ x)
    {P : MvPolynomial σ A} {n : ℕ} (h : MvPolynomial.C g ∣ P ^ n) : MvPolynomial.C g ∣ P := by
  have hq : ∀ a : A, Ideal.Quotient.mk (Ideal.span {g}) a = 0 ↔ g ∣ a := fun a => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [MvPolynomial.C_dvd_iff_map_hom_eq_zero _ g hq] at h ⊢
  rw [map_pow] at h
  have hn := (MvPolynomial.isNilpotent_iff).1 ⟨n, h⟩
  ext i
  obtain ⟨k, hk⟩ := hn i
  rw [MvPolynomial.coeff_map] at hk ⊢
  rw [← map_pow, hq] at hk
  rw [MvPolynomial.coeff_zero, hq]
  exact hg _ _ hk

theorem exists_div_of_mem_O {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
    {V : M.Z.Opens} (hV : IsAffineOpen V) {z : M.Z} (hz : z ∈ V) {x : Ω} (hx : x ∈ M.O z) :
    ∃ a b : Ω, a ∈ M.ringOn V ∧ b ∈ M.ringOn V ∧ b ≠ 0 ∧ b⁻¹ ∈ M.O z ∧ x * b = a := by
  obtain ⟨U, f, hU, rfl⟩ := hx
  have hne : (V : Set M.Z).Nonempty := ⟨z, hz⟩
  obtain ⟨g, hgU, hwg⟩ := hV.exists_basicOpen_le (V := U) ⟨z, hU⟩ hz
  have hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hwg⟩
  have := hV.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g (resG M.Z hgU f)
  have h1 := congrArg (M.res _ hg) ha
  have h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t :=
    fun t => M.res_resG (M.Z.basicOpen_le g) hg t
  rw [map_mul, map_pow, h2, h2, RatModel.res_resG, RatModel.res_apply, RatModel.res_apply,
    RatModel.res_apply] at h1
  have hu := (RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hz g).2 hwg)
  refine ⟨_, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩,
    pow_mem ((RatModel.mem_ringOn_iff_exists hne).2 ⟨g, rfl⟩) n, pow_ne_zero _ hu.1, ?_, h1⟩
  rw [← inv_pow]
  exact pow_mem hu.2 n

theorem keepsRad_of_affCover (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r : ℕ)
    (h : AffCover M M' φ f r) : KeepsRad M M' φ f := by
  rintro z' g ⟨hg0, hgO, hg⟩
  obtain ⟨hf, hc⟩ := h
  obtain ⟨U, W, t, hU, -, hz, hW, hinj, hR⟩ := hc z'
  have hφ0 : φ g ≠ 0 := (map_ne_zero φ).2 hg0
  refine ⟨hφ0, hf.map_mem_O hgO, fun x n hx hxn => ?_⟩
  let A := (M.O (f z')).toSubring
  let ψ : MvPolynomial (Fin r) A →+* Ω' := MvPolynomial.eval₂Hom ((φ : Ω →+* Ω').comp A.subtype) t
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    have := hinj (MvPolynomial.map A.subtype P) (by rw [MvPolynomial.eval₂_map]; exact hP)
    exact (map_eq_zero_iff _ (MvPolynomial.map_injective _ A.subtype_injective)).1 this
  have hO : ∀ P, ψ P ∈ M'.O z' := fun P => by
    induction P using MvPolynomial.induction_on with
    | C a => rw [MvPolynomial.eval₂Hom_C]; exact hf.map_mem_O a.2
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      exact mul_mem hp (RatModel.ringOn_le_O hz (hR ▸ Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)))
  have hS : ∀ y ∈ M'.ringOn U, ∃ P, ψ P = y := by
    intro y hy
    rw [hR] at hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with ⟨w, hw, rfl⟩ | ⟨i, rfl⟩
      · exact ⟨MvPolynomial.C ⟨w, RatModel.ringOn_le_O (hW z' hz) hw⟩, MvPolynomial.eval₂Hom_C _ _ _⟩
      · exact ⟨MvPolynomial.X i, MvPolynomial.eval₂Hom_X' _ _ _⟩
    | algebraMap c =>
      exact ⟨MvPolynomial.C ⟨algebraMap F Ω c, (M.O (f z')).algebraMap_mem c⟩,
        (MvPolynomial.eval₂Hom_C _ _ _).trans (φ.commutes c)⟩
    | add a b _ _ ha hb => obtain ⟨P, rfl⟩ := ha; obtain ⟨Q, rfl⟩ := hb; exact ⟨P + Q, map_add _ _ _⟩
    | mul a b _ _ ha hb => obtain ⟨P, rfl⟩ := ha; obtain ⟨Q, rfl⟩ := hb; exact ⟨P * Q, map_mul _ _ _⟩
  have hrad : ∀ (y : A) (k : ℕ), (⟨g, hgO⟩ : A) ∣ y ^ k → (⟨g, hgO⟩ : A) ∣ y := by
    rintro y k ⟨c, hc⟩
    have e : (y : Ω) ^ k = g * c := congrArg Subtype.val hc
    have := hg y k y.2 (by rw [e, mul_div_cancel_left₀ _ hg0]; exact c.2)
    exact ⟨⟨_, this⟩, Subtype.ext (mul_div_cancel₀ _ hg0).symm⟩
  have hC : ψ (MvPolynomial.C ⟨g, hgO⟩) = φ g := MvPolynomial.eval₂Hom_C _ _ _
  obtain ⟨a, b, ha, hb, hb0, hbi, e1⟩ := exists_div_of_mem_O hU hz hx
  obtain ⟨c, d, hc, hd, hd0, hdi, e2⟩ := exists_div_of_mem_O hU hz hxn
  obtain ⟨a, rfl⟩ := hS a ha
  obtain ⟨b, rfl⟩ := hS b hb
  obtain ⟨c, rfl⟩ := hS c hc
  obtain ⟨d, rfl⟩ := hS d hd
  have hdvd : MvPolynomial.C (⟨g, hgO⟩ : A) ∣ (a * d) ^ (n + 1) := by
    refine ⟨c * b ^ n * a * d ^ n, hψ ?_⟩
    simp only [map_mul, map_pow, hC, ← e2]
    rw [← e1]
    field_simp
    ring
  obtain ⟨Q, hQ⟩ := C_dvd_of_C_dvd_pow hrad hdvd
  have e3 := congrArg ψ hQ
  rw [map_mul, map_mul, hC, ← e1] at e3
  have e4 : x / φ g = ψ Q * (ψ b)⁻¹ * (ψ d)⁻¹ := by
    field_simp
    linear_combination e3
  rw [e4]
  exact mul_mem (mul_mem (hO Q) hbi) hdi

end GlobalTheory.FlagBundle.AffRad
