import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

def KeyFormulaPow : Prop :=
  ∃ N : ℕ → ℕ, (∀ g, 1 ≤ N g) ∧
  ∃ κ : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ,

    (∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
      (M : Matrix (Fin P.g) (Fin P.g) K), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
      (∀ i, IsLieComb (M i) v (v' i)) →
      a ^ (8 * N P.g) * (κ K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) =
        M.det ^ (4 * N P.g) * κ K ⟨P, hg, rig, hr, th, hth, v, hv⟩) ∧

    (∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (f : K →+* K') (x : KeyIn K) (x' : KeyIn K'),
      KeyPB x' x f → (κ K' x' : K') = f (κ K x)) ∧

    (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
      [IsFractionRing R K] (x : KeyIn R) (xK : KeyIn K), KeyPB xK x (algebraMap R K) →
      ∃ u : Rˣ, (κ K xK : K) = algebraMap R K u ∧
        ∀ (k : Type) [Field k] [CharZero k] (r : R →+* k) (xk : KeyIn k), Function.Surjective r → KeyPB xk x r →
          (κ k xk : k) = r u) ∧

    (∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ),
      τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) →
      (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
      u.IsRig x.rig → u.IsFn x.th (thetaChar τ a b) →
      (∀ i, u.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x.v i)) → κ ℂ x = 1) ∧

    ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
      (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)) (nth nη : ℝ),
      u.IsAH Hm χ → u.IsRig x.rig → u.IsFn x.th θ → (∀ i, u.IsDiff (W i) (x.v i)) →
      IsAddFundamentalDomain u.Λ Fd volume →
      nth = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)) / (volume Fd).toReal →
      nη = (volume Fd).toReal / (Real.pi ^ x.P.g * ‖W.det‖ ^ 2) →
      ‖(κ ℂ x : ℂ)‖ * nth ^ (4 * N x.P.g) * nη ^ (2 * N x.P.g) = (2 * Real.pi) ^ (2 * x.P.g * N x.P.g)

namespace KeyPow

def IsArchNorm (x : KeyIn ℂ) (nth nη : ℝ) : Prop :=
  ∃ (u : HolUnif x.P.A x.P.L x.P.g) (Hm W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
    (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)),
    u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ (∀ i, u.IsDiff (W i) (x.v i)) ∧
    IsAddFundamentalDomain u.Λ Fd volume ∧
    nth = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)) / (volume Fd).toReal ∧
    nη = (volume Fd).toReal / (Real.pi ^ x.P.g * ‖W.det‖ ^ 2)

def IsLocalModel {K : Type} [Field K] [NumberField K] (x : KeyIn K) (𝔭 : HeightOneSpectrum (𝓞 K)) (a : K)
    (M : Matrix (Fin x.P.g) (Fin x.P.g) K) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (_ : Algebra R K)
    (_ : IsFractionRing R K) (y : KeyIn R) (th' : x.P.L.Sec)
    (hth' : ∀ s : Sp K, ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th')
    (v' : Fin x.P.g → (epsR K ⟶ x.P.A)) (hv' : IsLieBasis v'),
    (∀ r : R, 𝔭.valuation K (algebraMap R K r) ≤ 1) ∧
    (∀ i, th'.f i = constFn x.P.A.hom _ a * x.th.f i) ∧ (∀ i, IsLieComb (M i) x.v (v' i)) ∧
    KeyPB ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', hth', v', hv'⟩ y (algebraMap R K)

theorem sum_log_norm_eq_finsum {K : Type} [Field K] [NumberField K] {z : K} (hz : z ≠ 0)
    (c : HeightOneSpectrum (𝓞 K) → ℤ) (hc : ∀ 𝔭, 𝔭.valuation K z = WithZero.exp (-c 𝔭)) :
    (Function.support c).Finite ∧
      ∑ σ : K →+* ℂ, Real.log ‖σ z‖ = ∑ᶠ 𝔭, (c 𝔭 : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal) := by
  have hN : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (1 : ℝ) < Ideal.absNorm 𝔭.asIdeal := fun 𝔭 => by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm 𝔭
  have hv : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), FinitePlace.mk 𝔭 z = (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-c 𝔭) := fun 𝔭 => by
    rw [FinitePlace.mk_apply, FinitePlace.norm_embedding', hc,
      WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    push_cast
    rfl
  have hfin : (Function.mulSupport fun 𝔭 : HeightOneSpectrum (𝓞 K) => FinitePlace.mk 𝔭 z).Finite :=
    (FinitePlace.hasFiniteMulSupport hz).preimage (f := FinitePlace.mk) fun _ _ _ _ h => FinitePlace.mk_eq_iff.1 h
  have hs : (Function.support c).Finite := hfin.subset fun 𝔭 h h1 => h (by
    have := (zpow_eq_one_iff_right₀ (zero_lt_one.trans (hN 𝔭)).le (hN 𝔭).ne').1 ((hv 𝔭).symm.trans h1)
    omega)
  refine ⟨hs, ?_⟩
  have h1 : ∏ σ : K →+* ℂ, ‖σ z‖ = (|Algebra.norm ℚ z| : ℚ) := by
    have := congrArg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ z)
    simp only [norm_prod] at this
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => ‖f z‖) (fun φ => ‖φ z‖)
      fun _ => by simp [RingHom.equivRatAlgHom_apply], ← this, eq_ratCast, Rat.cast_abs, ← Real.norm_eq_abs,
      ← Complex.norm_real, Complex.ofReal_ratCast]
  have h2 : ∏ᶠ 𝔭 : HeightOneSpectrum (𝓞 K), FinitePlace.mk 𝔭 z = ((|Algebra.norm ℚ z| : ℚ) : ℝ)⁻¹ := by
    have := FinitePlace.prod_eq_inv_abs_norm hz
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm] at this
    exact this.trans (Rat.cast_inv _)
  rw [← Real.log_prod fun σ _ => by simpa using hz, h1, ← inv_inv ((|Algebra.norm ℚ z| : ℚ) : ℝ), ← h2, Real.log_inv,
    finprod_eq_prod_of_mulSupport_subset _ (s := hs.toFinset) fun 𝔭 h => by
      simp only [Set.Finite.coe_toFinset, Function.mem_support]
      intro h0
      exact h ((hv 𝔭).trans (by rw [h0]; simp)),
    finsum_eq_sum_of_support_subset _ (s := hs.toFinset) fun 𝔭 h => by
      simp only [Set.Finite.coe_toFinset, Function.mem_support]
      intro h0
      exact h (by simp [h0]),
    Real.log_prod fun 𝔭 _ => by rw [hv]; exact zpow_ne_zero _ (zero_lt_one.trans (hN 𝔭)).ne', ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun 𝔭 _ => ?_
  rw [hv, Real.log_zpow]
  push_cast
  ring

end KeyPow

def KeyDegreeSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (oa od : HeightOneSpectrum (𝓞 K) → ℤ)
    (nth nη : (K →+* ℂ) → ℝ),
    (∀ 𝔭, ∃ (a : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), KeyPow.IsLocalModel x 𝔭 a M ∧
      𝔭.valuation K a = WithZero.exp (-oa 𝔭) ∧ 𝔭.valuation K M.det = WithZero.exp (-od 𝔭)) →
    (∀ σ : K →+* ℂ, ∃ x' : KeyIn ℂ, KeyPB x' x σ ∧ KeyPow.IsArchNorm x' (nth σ) (nη σ)) →
    (∀ σ, 0 < nth σ ∧ 0 < nη σ) ∧ (Function.support fun 𝔭 => 8 * oa 𝔭 - 4 * od 𝔭).Finite ∧
    ∑ σ : K →+* ℂ, (4 * Real.log (nth σ) + 2 * Real.log (nη σ)) +
        ∑ᶠ 𝔭, ((8 * oa 𝔭 - 4 * od 𝔭 : ℤ) : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal) =
      2 * x.P.g * Module.finrank ℚ K * Real.log (2 * Real.pi)

theorem keyDegree_of_keyFormulaPow (h : KeyFormulaPow) : KeyDegreeSt := by
  obtain ⟨N, hN, κ, hH, hF, hU, -, hA⟩ := h
  intro K _ _ x oa od nth nη hloc harch
  have hn : 1 ≤ N x.P.g := hN _
  have hn' : (N x.P.g : ℝ) ≠ 0 := by exact_mod_cast (by omega : N x.P.g ≠ 0)
  have hval : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭.valuation K (κ K x : K) =
      WithZero.exp (-(N x.P.g * (8 * oa 𝔭 - 4 * od 𝔭))) := fun 𝔭 => by
    obtain ⟨a, M, ⟨R, _, _, _, _, _, y, th', hth', v', hv', hR, ha, hM, hPB⟩, hoa, hod⟩ := hloc 𝔭
    obtain ⟨u, hu, -⟩ := hU R K y _ hPB
    have e := hH K x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis th' hth' v' hv' a M ha hM
    have hu1 : 𝔭.valuation K (algebraMap R K u) = 1 := by
      refine eq_one_of_one_le_mul_left (hR (u : R)) (hR (u⁻¹ : Rˣ)) ?_
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have e' := congrArg (𝔭.valuation K) e
    rw [hu, map_mul, map_mul, map_pow, map_pow, hu1, hoa, hod, _root_.mul_one, ← WithZero.exp_nsmul,
      ← WithZero.exp_nsmul] at e'
    have h0 : 𝔭.valuation K (κ K x : K) ≠ 0 := by simp
    change _ = _ * 𝔭.valuation K (κ K x : K) at e'
    rw [← WithZero.exp_log h0, ← WithZero.exp_add, WithZero.exp_inj] at e'
    rw [← WithZero.exp_log h0, WithZero.exp_inj]
    simp only [nsmul_eq_mul] at e'
    push_cast at e'
    linarith
  have hσ : ∀ σ : K →+* ℂ, (0 < nth σ ∧ 0 < nη σ) ∧ Real.log ‖σ (κ K x : K)‖ +
      N x.P.g * (4 * Real.log (nth σ) + 2 * Real.log (nη σ)) = N x.P.g * (2 * x.P.g * Real.log (2 * Real.pi)) := fun σ => by
    obtain ⟨x', hPB, u, Hm, W, χ, θ, Fd, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := harch σ
    have e := hA x' u Hm W χ θ Fd _ _ h₁ h₂ h₃ h₄ h₅ h₆ h₇
    have hg : x'.P.g = x.P.g := by obtain ⟨-, -, -, hg, -⟩ := hPB; exact hg
    rw [hF K ℂ σ x x' hPB, hg] at e
    have p₁ : 0 ≤ nth σ := h₆ ▸ div_nonneg (integral_nonneg fun z => by positivity) ENNReal.toReal_nonneg
    have p₂ : 0 ≤ nη σ := h₇ ▸ by positivity
    have hne : ‖σ (κ K x : K)‖ * nth σ ^ (4 * N x.P.g) * nη σ ^ (2 * N x.P.g) ≠ 0 := by
      rw [e]; have := Real.pi_pos; positivity
    have q₀ := left_ne_zero_of_mul (left_ne_zero_of_mul hne)
    have q₁ := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
    have q₂ := right_ne_zero_of_mul hne
    refine ⟨⟨p₁.lt_of_ne' fun h0 => q₁ (by rw [h0]; exact zero_pow (by omega)),
      p₂.lt_of_ne' fun h0 => q₂ (by rw [h0]; exact zero_pow (by omega))⟩, ?_⟩
    have e' := congrArg Real.log e
    rw [Real.log_mul (mul_ne_zero q₀ q₁) q₂, Real.log_mul q₀ q₁, Real.log_pow, Real.log_pow, Real.log_pow] at e'
    push_cast at e'
    linarith
  obtain ⟨hs, hp⟩ := KeyPow.sum_log_norm_eq_finsum (κ K x).ne_zero _ hval
  have hs' : (Function.support fun 𝔭 => 8 * oa 𝔭 - 4 * od 𝔭).Finite :=
    hs.subset fun 𝔭 h => mul_ne_zero (by omega) h
  refine ⟨fun σ => (hσ σ).1, hs', mul_left_cancel₀ hn' ?_⟩
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (K →+* ℂ))) rfl fun σ _ => (hσ σ).2
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
    nsmul_eq_mul, hp] at hsum
  rw [mul_add, mul_finsum]
  simp only [Int.cast_mul (N x.P.g : ℤ), Int.cast_natCast, _root_.mul_assoc] at hsum ⊢
  linarith

namespace KeyPow

theorem exists_scalar_matrix (hT : Out.SecTwistSt) {K : Type} [Field K] (P : Out.PolAV (Sp K)) (th th' : P.L.Sec)
    (hth : ∀ s : Sp K, ∃ z : P.A.left, P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th) {v v' : Fin P.g → (epsR K ⟶ P.A)}
    (hv : IsLieBasis v) (hv' : IsLieBasis v') :
    ∃ (a : K) (M : Matrix (Fin P.g) (Fin P.g) K), (∀ i, th'.f i = constFn P.A.hom _ a * th.f i) ∧
      ∀ i, IsLieComb (M i) v (v' i) := by
  obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section hT P
  obtain ⟨a, ha, -⟩ := hb th
  obtain ⟨a', ha', -⟩ := hb th'
  choose M hM using fun i => (hv.2 _ (hv'.1 i)).exists
  have h0 : a ≠ 0 := by
    rintro rfl
    obtain ⟨z, -, hz⟩ := hth (default : PrimeSpectrum K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    rw [ha i, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  refine ⟨a' * a⁻¹, M, fun i => ?_, hM⟩
  rw [ha' i, ha i, ← _root_.mul_assoc, constFn, constFn, constFn, ← map_mul, ← map_mul, inv_mul_cancel_right₀ h0]

theorem exists_isArchNorm (hU : ThetaUnifAV) (x : KeyIn ℂ) : ∃ nth nη, IsArchNorm x nth nη := by
  obtain ⟨u, Hm, χ, -, hA, hR, hd, -⟩ := hU x.P x.rig x.rig_gen
  choose W hW using fun i => (hd _ (x.basis.1 i)).exists
  obtain ⟨θ, hθ⟩ := exists_isFn x.P.isLB u x.th
  obtain ⟨Fd, hF⟩ := exists_isAddFundamentalDomain u
  exact ⟨_, _, u, Hm, W, χ, θ, Fd, hA, hR, hθ, hW, hF, rfl, rfl⟩

theorem exists_archNorms (hU : ThetaUnifAV) {K : Type} [Field K] (x : KeyIn K) :
    ∃ nth nη : (K →+* ℂ) → ℝ, ∀ σ : K →+* ℂ, ∃ x' : KeyIn ℂ, KeyPB x' x σ ∧ IsArchNorm x' (nth σ) (nη σ) := by
  choose x' hx' using fun σ : K →+* ℂ => exists_keyPB x σ
  choose nth nη h using fun σ => exists_isArchNorm hU (x' σ)
  exact ⟨nth, nη, fun σ => ⟨x' σ, hx' σ, h σ⟩⟩

end KeyPow

end GlobalTheory
