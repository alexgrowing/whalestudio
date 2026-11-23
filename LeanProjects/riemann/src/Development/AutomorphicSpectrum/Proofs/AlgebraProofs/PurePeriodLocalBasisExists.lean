import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsIntegralPosDefPerturbationStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UltrametricDetNormStableStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NegDefBlockOfPosDefStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsOrthogonalLocalBasisStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalBasisGramDeterminantBoundStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramSignatureOrthogonalSplitStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqSesquilinearSkewHermitianStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PeriodGramHermitianSignatureStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicLogIdealMaxElementStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.DSplit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem norm_le_one_of_int {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_int_le (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]) (b : 𝓞 E) : ‖j (b : E)‖ ≤ 1 :=
  norm_le_one_of_int (map_isIntegral_int j b.isIntegral_coe)

theorem norm_prime_lt (ℓ : Nat.Primes) : ‖(((ℓ : ℕ) : ℂ_[ℓ]))‖ < 1 := by
  have h : (((ℓ : ℕ) : ℂ_[ℓ])) = algebraMap ℚ_[ℓ] ℂ_[ℓ] ((ℓ : ℕ) : ℚ_[ℓ]) := by simp
  rw [h, norm_algebraMap', Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast ℓ.2.one_lt)

theorem exists_bound (D : Datum H) (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]) :
    ∃ r : ℝ, 0 < r ∧ Real.log r = -logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) ∧
      ∀ x y, ‖j (sesq D x y)‖ ≤ r := by
  have hinj : Function.Injective (j.comp (algebraMap (𝓞 E) E)) :=
    j.injective.comp (RingOfIntegers.coe_injective)
  obtain ⟨a, ha, ha0, -, hlog⟩ := GlobalTheory.T.padic_logIdeal_max_element E ℓ (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) hinj
    differentIdeal_ne_bot
  have hn : 0 < ‖j (a : E)‖ := by
    rw [norm_pos_iff]
    intro h
    exact ha0 (hinj (by simpa using h))
  refine ⟨‖j (a : E)‖⁻¹, inv_pos.2 hn, ?_, fun x y => ?_⟩
  · rw [Real.log_inv]
    exact congrArg Neg.neg hlog.symm
  · obtain ⟨b, hb⟩ := (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.2.2 a ha x y
    have h1 : ‖j (a : E)‖ * ‖j (sesq D x y)‖ = ‖j (b : E)‖ := by rw [← norm_mul, ← map_mul, hb]
    have h2 := norm_int_le ℓ j b
    rw [← h1] at h2
    rw [← one_div, le_div_iff₀ hn]
    linarith

theorem sesq_sum_left (D : Datum H) {J : Type} (s : Finset J) (f : J → D.La) (y : D.La) :
    sesq D (∑ m ∈ s, f m) y = ∑ m ∈ s, sesq D (f m) y := by
  let φ : D.La →+ E := AddMonoidHom.mk' (fun x => sesq D x y) (fun a b => (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.1 a b y)
  exact map_sum φ f s

theorem sesq_sum_right (D : Datum H) {J : Type} (s : Finset J) (f : J → D.La) (y : D.La) :
    sesq D y (∑ m ∈ s, f m) = ∑ m ∈ s, sesq D y (f m) := by
  let φ : D.La →+ E := AddMonoidHom.mk' (fun x => sesq D y x) (fun a b => (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.1 y a b)
  exact map_sum φ f s

theorem sesq_comb (D : Datum H) {J : Type} [Fintype J] (x : J → D.La) (u v : J → 𝓞 E) :
    sesq D (∑ m, u m • x m) (∑ n, v n • x n) =
      ∑ n, (∑ m, (u m : E) * sesq D (x m) (x n)) * IsCMField.complexConj E (v n : E) := by
  rw [sesq_sum_right]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [(GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.1, sesq_sum_left, mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun m _ => (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.1 _ _ _

theorem gram_comb_map (D : Datum H) (τ : E →+* ℂ) {I J : Type} [Fintype J] (x : J → D.La)
    (X : Matrix I J (𝓞 E)) :
    ((gramE D (fun a => ∑ m, X a m • x m)).map fun a => Complex.I * τ a) =
      (X.map fun a => τ (a : E)) * ((gramE D x).map fun a => Complex.I * τ a) * (X.map fun a => τ (a : E))ᴴ := by
  ext a b
  simp only [Matrix.map_apply, gramE, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, sesq_comb,
    map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, IsCMField.complexEmbedding_complexConj, starRingEnd_apply]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  ring

theorem norm_diff_lt (D : Datum H) (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]) {r : ℝ} (hr : 0 < r)
    (hb : ∀ x y, ‖j (sesq D x y)‖ ≤ r) (u u' v v' : D.La) :
    ‖j (sesq D (u + ((ℓ : ℕ) : 𝓞 E) • v) (u' + ((ℓ : ℕ) : 𝓞 E) • v')) - j (sesq D u u')‖ < r := by
  obtain ⟨-, hl, hr', hsl, hsr, -, -⟩ := GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D
  have hcast : ((((ℓ : ℕ) : 𝓞 E)) : E) = ((ℓ : ℕ) : E) := map_natCast (algebraMap (𝓞 E) E) _
  have e : j (sesq D (u + ((ℓ : ℕ) : 𝓞 E) • v) (u' + ((ℓ : ℕ) : 𝓞 E) • v')) - j (sesq D u u') =
      ((ℓ : ℕ) : ℂ_[ℓ]) * (j (sesq D v u') + j (sesq D u v') + ((ℓ : ℕ) : ℂ_[ℓ]) * j (sesq D v v')) := by
    rw [hl, hr', hr', hsl, hsl, hsr, hsr, hcast, map_natCast (IsCMField.complexConj E)]
    simp only [map_add, map_mul, map_natCast]
    ring
  have hc := norm_prime_lt ℓ
  have hc0 : 0 ≤ ‖(((ℓ : ℕ) : ℂ_[ℓ]))‖ := norm_nonneg _
  have h3 : ‖((ℓ : ℕ) : ℂ_[ℓ]) * j (sesq D v v')‖ ≤ r := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc.le).trans (hb v v')
  have h4 : ‖j (sesq D v u') + j (sesq D u v') + ((ℓ : ℕ) : ℂ_[ℓ]) * j (sesq D v v')‖ ≤ r :=
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hb _ _) (hb _ _))) h3)
  rw [e, norm_mul]
  calc _ ≤ ‖(((ℓ : ℕ) : ℂ_[ℓ]))‖ * r := mul_le_mul_of_nonneg_left h4 hc0
    _ < 1 * r := mul_lt_mul_of_pos_right hc hr
    _ = r := one_mul r

theorem conj_ne (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) :
    (ComplexEmbedding.conjugate τ) (H.rt : E) ≠ H.rt0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hsq := H.sqrt_neg_disc_sq
  have him : H.rt0 ≠ 0 := by
    intro h0
    rw [h0] at hsq
    simp at hsq
    exact H.d_prime.ne_zero hsq
  have h1 : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d : ℝ) := by
    have := congrArg Complex.re hsq
    simpa [pow_two] using this
  have h2 : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0 := by
    have := congrArg Complex.im hsq
    simpa [pow_two] using this
  have h3 : H.rt0.re * H.rt0.im = 0 := by linarith [mul_comm H.rt0.re H.rt0.im]
  have hre : H.rt0.re = 0 := by
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact h4
    · rw [h4] at h1
      nlinarith [mul_self_nonneg H.rt0.re]
  rw [ComplexEmbedding.conjugate_coe_eq, h]
  intro h5
  have h6 := congrArg Complex.im h5
  simp at h6
  exact him (Complex.ext hre (by simpa using (by linarith : H.rt0.im = 0)))

theorem exists_emb (E : Type) [Field E] [NumberField E] (ℓ : Nat.Primes) : Nonempty (E →+* ℂ_[ℓ]) :=
  ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ_[ℓ]).toRingHom⟩

theorem norm_det_close (D : Datum H) (p : ℕ) (ℓ : Nat.Primes) (x x' w : Fin p → D.La)
    (hx' : ∀ a, x' a = x a + ((ℓ : ℕ) : 𝓞 E) • w a) (hx0 : (gramE D x).det ≠ 0)
    (hxn : ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x).det‖ =
      -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) :
    (gramE D x').det ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ =
      -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  have key : ∀ j : E →+* ℂ_[ℓ], 0 < ‖j (gramE D x').det‖ ∧ Real.log ‖j (gramE D x').det‖ =
      -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
    intro j
    obtain ⟨r, hr, hlog, hb⟩ := exists_bound D ℓ j
    have hd0 : 0 < ‖j (gramE D x).det‖ := norm_pos_iff.2 ((map_ne_zero j).2 hx0)
    have hdet : ‖((gramE D x).map j).det‖ = r ^ Fintype.card (Fin p) := by
      have e : ((gramE D x).map j).det = j (gramE D x).det := (RingHom.map_det j _).symm
      rw [e, Fintype.card_fin, ← Real.exp_log hd0, hxn j, ← Real.exp_log (pow_pos hr p), Real.log_pow, hlog]
      congr 1
      ring
    have h := GlobalTheory.T.ultrametric_det_norm_stable ℂ_[ℓ] (Fin p) ((gramE D x).map j) ((gramE D x').map j) r hr
      (fun a b => hb _ _) (fun a b => by
        simp only [Matrix.map_apply, gramE, Matrix.of_apply, hx']
        exact norm_diff_lt D ℓ j hr hb _ _ _ _) hdet
    have e' : ((gramE D x').map j).det = j (gramE D x').det := (RingHom.map_det j _).symm
    rw [e', Fintype.card_fin] at h
    refine ⟨by rw [h]; exact pow_pos hr p, ?_⟩
    rw [h, Real.log_pow, hlog]
    ring
  obtain ⟨j⟩ := exists_emb E ℓ
  refine ⟨fun h0 => ?_, fun j => (key j).2⟩
  have := (key j).1
  rw [h0] at this
  simp at this

theorem neg_compl (D : Datum H) {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P₀ : D.La →+ (Fin g → ℂ)} {p q : ℕ}
    (hP₀ : IsPeriod D ty P₀) (hty : IsTypeFn H p q ty) (hpq : p + q = D.p + D.q)
    (x : Fin p ⊕ Fin q → D.La) (hli : LinearIndependent (𝓞 E) x)
    (horth : ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) (τ : E →+* ℂ) (hτ : τ (H.rt : E) = H.rt0)
    (hpos : ((gramE D (x ∘ Sum.inl)).map fun a => Complex.I * τ a).PosDef) :
    (-((gramE D (x ∘ Sum.inr)).map fun a => Complex.I * τ a)).PosDef := by
  obtain ⟨hH, -, C, hC⟩ := GlobalTheory.T.period_gram_hermitian_signature E H D g ty P₀ p q x τ hP₀ hty hli hpq hτ
  have hblk : ((gramE D x).map fun a => Complex.I * τ a) =
      Matrix.fromBlocks ((gramE D (x ∘ Sum.inl)).map fun a => Complex.I * τ a) 0 0
        ((gramE D (x ∘ Sum.inr)).map fun a => Complex.I * τ a) := by
    ext (a | a) (b | b)
    · simp [gramE]
    · simp [gramE, horth]
    · have h := (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.2.1 (x (.inl b)) (x (.inr a))
      simp [gramE, h, horth]
    · simp [gramE]
  rw [hblk] at hC
  refine GlobalTheory.T.negDef_block_of_posDef p q _ _ C hpos ?_ hC
  ext i k
  have h := congrFun (congrFun hH (.inr i)) (.inr k)
  simpa [gramE] using h

end GlobalTheory.CompanionTheory.Ar.Fl.DSplit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem GlobalTheory.CompanionTheory.Ar.Fl.DSplit.exists_split_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P₀ : D.La →+ (Fin g → ℂ)) (p q : ℕ) (ℓ : Nat.Primes), IsPeriod D ty P₀ → IsTypeFn H p q ty → p + q = D.p + D.q → ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (x : Fin p ⊕ Fin q → D.La), IsLocBasis (𝓞 E) ℓ x ∧ IsPure hP x := by
  intro E _ _ _ H D g ty P₀ p q ℓ hP₀ hty hpq
  obtain ⟨x, hxb, hx0, hxn⟩ := GlobalTheory.T.local_basis_gram_determinant_bound E H D p q ℓ hpq
  have hli := hxb.1
  let Ψ : Set (E →+* ℂ) := {τ | τ (H.rt : E) = H.rt0}
  let M : (E →+* ℂ) → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
    fun τ => (gramE D x).map fun a => Complex.I * τ a
  have hC : ∀ τ : E →+* ℂ, ∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, τ ∈ Ψ → (C * M τ * Cᴴ).PosDef := by
    intro τ
    by_cases h : τ ∈ Ψ
    · obtain ⟨C, hC⟩ := (GlobalTheory.T.period_gram_hermitian_signature E H D g ty P₀ p q x τ hP₀ hty hli hpq h).2.1
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose C hC using hC
  obtain ⟨Y, hY⟩ := GlobalTheory.T.exists_integral_posDef_perturbation E Ψ (Fin p) (Fin p ⊕ Fin q) M C (Matrix.fromCols 1 0) (ℓ : ℕ) ℓ.2.ne_zero
    (fun τ h => DSplit.conj_ne τ h)
    (fun τ h => ⟨(GlobalTheory.T.period_gram_hermitian_signature E H D g ty P₀ p q x τ hP₀ hty hli hpq h).1, hC τ h⟩)
  let X : Matrix (Fin p) (Fin p ⊕ Fin q) (𝓞 E) := Matrix.fromCols 1 0 + (ℓ : ℕ) • Y
  let x' : Fin p → D.La := fun a => ∑ m, X a m • x m
  let w : Fin p → D.La := fun a => ∑ m, Y a m • x m
  have hx' : ∀ a, x' a = (x ∘ Sum.inl) a + (((ℓ : ℕ) : 𝓞 E)) • w a := by
    intro a
    simp only [x', w, X, Matrix.add_apply, Matrix.smul_apply, add_smul, Finset.sum_add_distrib, Finset.smul_sum,
      nsmul_eq_mul, mul_smul, Function.comp]
    congr 1
    simp [Fintype.sum_sum_type, Matrix.one_apply, ite_smul]
  obtain ⟨hd0, hdn⟩ := DSplit.norm_det_close D p ℓ (x ∘ Sum.inl) x' w hx' hx0 hxn
  obtain ⟨x₂, hx₂, hb₂, horth⟩ := GlobalTheory.T.exists_orthogonal_local_basis E H D p q ℓ x' hpq hd0 hdn
  have hpos : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 →
      ((gramE D (x₂ ∘ Sum.inl)).map fun a => Complex.I * τ a).PosDef := by
    intro τ hτ
    rw [hx₂, DSplit.gram_comb_map D τ x X]
    exact hY τ hτ
  obtain ⟨P, hP, hpure⟩ := GlobalTheory.T.gram_signature_orthogonal_split E H D g ty p q x₂ hty hpq hb₂.1 horth fun τ hτ =>
    ⟨hpos τ hτ, DSplit.neg_compl D hP₀ hty hpq x₂ hb₂.1 horth τ hτ (hpos τ hτ)⟩
  exact ⟨P, hP, x₂, hb₂, hpure⟩
