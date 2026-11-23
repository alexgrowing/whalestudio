import Development.WeilBound.CoreStatements.SesquilinearFractions.SesqSesquilinearSkewHermitian
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDeterminantLogDifferentStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDetNeZeroLocalBasisCofiniteStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UltrametricDetNormLeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicIntegralIffDenominatorStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicLogIdealMaxElementStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem card_local_basis_eq_rank (D : Datum H) {I : Type} [Fintype I] (x : I → D.La) (ℓ : ℕ) (h : IsLocBasis (𝓞 E) ℓ x) :
    Fintype.card I = D.p + D.q := by
  haveI := D.fin
  haveI := D.proj
  obtain ⟨hli, n, hn, hspan⟩ := h
  have hn0 : (n : 𝓞 E) ≠ 0 := by
    have : n ≠ 0 := by
      rintro rfl
      exact hn (dvd_zero ℓ)
    exact_mod_cast this
  rw [← D.rank]
  apply le_antisymm
  · exact hli.fintype_card_le_finrank
  · let g : D.La →ₗ[𝓞 E] Submodule.span (𝓞 E) (Set.range x) :=
      LinearMap.codRestrict _ ((n : 𝓞 E) • LinearMap.id) (fun y => by
        simpa [Nat.cast_smul_eq_nsmul] using hspan y)
    have hg : Function.Injective g := by
      intro y z hyz
      have h1 : (n : 𝓞 E) • y = (n : 𝓞 E) • z := congrArg Subtype.val hyz
      exact smul_right_injective _ hn0 h1
    calc Module.finrank (𝓞 E) D.La ≤ Module.finrank (𝓞 E) (Submodule.span (𝓞 E) (Set.range x)) :=
          LinearMap.finrank_le_finrank_of_injective hg
      _ = Fintype.card I := finrank_span_eq_card hli

theorem local_basis_gram_det_log (D : Datum H) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La) (ℓ : Nat.Primes)
    (hx : IsLocBasis (𝓞 E) ℓ x) (horth : ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) :
    (gramE D (x ∘ Sum.inr)).det ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D (x ∘ Sum.inr)).det‖ =
      -(q : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  classical
  have hcard := card_local_basis_eq_rank D x ℓ hx
  obtain ⟨hdet, -⟩ := PositivityTheory.Xgf.gram_det_ne_zero_local_basis_cofinite E H D _ x hcard hx.1
  obtain ⟨-, -, -, -, -, hskew, hdiff⟩ := sesq_sesquilinear_properties D
  have h21 : ∀ a b, sesq D (x (.inr a)) (x (.inl b)) = 0 := by
    intro a b
    rw [hskew (x (.inl b)) (x (.inr a)), horth]
    simp
  have hblock : gramE D x =
      Matrix.fromBlocks (gramE D (x ∘ Sum.inl)) 0 0 (gramE D (x ∘ Sum.inr)) := by
    ext (a | a) (b | b) <;> simp [gramE, horth, h21]
  have hdetprod : (gramE D x).det =
      (gramE D (x ∘ Sum.inl)).det * (gramE D (x ∘ Sum.inr)).det := by
    rw [hblock, Matrix.det_fromBlocks_zero₂₁]
  have h1ne : (gramE D (x ∘ Sum.inl)).det ≠ 0 := fun h0 => hdet (by rw [hdetprod, h0, zero_mul])
  have h2ne : (gramE D (x ∘ Sum.inr)).det ≠ 0 := fun h0 => hdet (by rw [hdetprod, h0, mul_zero])
  refine ⟨h2ne, fun j => ?_⟩
  set emb : 𝓞 E →+* ℂ_[ℓ] := j.comp (algebraMap (𝓞 E) E) with hemb_def
  have hemb : Function.Injective emb := j.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 E) E)
  have hne : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨a, ha, ha0, -, hL⟩ := GlobalTheory.T.padic_logIdeal_max_element E ℓ emb _ hemb hne
  have hemba : emb a = j (a : E) := rfl
  have hja : 0 < ‖j (a : E)‖ := by
    rw [← hemba]
    exact norm_pos_iff.mpr ((map_ne_zero_iff emb hemb).mpr ha0)
  set R : ℝ := ‖j (a : E)‖⁻¹ with hR
  have hR0 : 0 < R := inv_pos.mpr hja
  have hent : ∀ y z : D.La, ‖j (sesq D y z)‖ ≤ R := by
    intro y z
    obtain ⟨b, hb⟩ := hdiff a ha y z
    have hb1 : ‖j (b : E)‖ ≤ 1 :=
      (GlobalTheory.T.padic_integral_iff_denominator E ℓ (b : E)).mpr ⟨1, b, Nat.Prime.not_dvd_one ℓ.prop, by simp⟩ j
    have hm : ‖j (a : E)‖ * ‖j (sesq D y z)‖ ≤ 1 := by
      rw [← norm_mul, ← map_mul, hb]
      exact hb1
    calc ‖j (sesq D y z)‖ = ‖j (a : E)‖⁻¹ * (‖j (a : E)‖ * ‖j (sesq D y z)‖) := by
          field_simp
      _ ≤ ‖j (a : E)‖⁻¹ * 1 := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hja.le)
      _ = R := mul_one _
  have hbound : ∀ {I : Type} [Fintype I] [DecidableEq I] (y : I → D.La),
      ‖j (gramE D y).det‖ ≤ R ^ Fintype.card I := by
    intro I _ _ y
    rw [RingHom.map_det]
    exact GlobalTheory.T.ultrametric_det_norm_le ℂ_[ℓ] I _ R hR0.le (fun a b => by
      simpa [RingHom.mapMatrix_apply, gramE] using hent (y a) (y b))
  have hu := hbound (x ∘ Sum.inl)
  have hv := hbound (x ∘ Sum.inr)
  simp only [Fintype.card_fin] at hu hv
  have hfull := GlobalTheory.T.gram_determinant_log_different E H D _ x ℓ hx j
  rw [← hemb_def, hL, hemba] at hfull
  have hu0 : 0 < ‖j (gramE D (x ∘ Sum.inl)).det‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr h1ne)
  have hv0 : 0 < ‖j (gramE D (x ∘ Sum.inr)).det‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr h2ne)
  have huv : ‖j (gramE D (x ∘ Sum.inl)).det‖ * ‖j (gramE D (x ∘ Sum.inr)).det‖ = R ^ (p + q) := by
    have hlog : Real.log (‖j (gramE D (x ∘ Sum.inl)).det‖ * ‖j (gramE D (x ∘ Sum.inr)).det‖) =
        Real.log (R ^ (p + q)) := by
      rw [← norm_mul, ← map_mul, ← hdetprod, hfull, Real.log_pow, hR, Real.log_inv]
      simp only [Fintype.card_sum, Fintype.card_fin]
      push_cast
      ring
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (mul_pos hu0 hv0)) (Set.mem_Ioi.mpr (pow_pos hR0 _)) hlog
  have hge : R ^ q ≤ ‖j (gramE D (x ∘ Sum.inr)).det‖ := by
    have hp0 : 0 < R ^ p := pow_pos hR0 _
    have : R ^ p * R ^ q ≤ R ^ p * ‖j (gramE D (x ∘ Sum.inr)).det‖ := by
      rw [← pow_add, ← huv]
      exact mul_le_mul_of_nonneg_right hu hv0.le
    exact le_of_mul_le_mul_left this hp0
  rw [hL, hemba, le_antisymm hv hge, Real.log_pow, hR, Real.log_inv]
  ring

end GlobalTheory.CompanionTheory.Ar.Fl

namespace PositivityTheory.Xgf

theorem local_basis_gram_det_log_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → (∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) → (gramE D (x ∘ Sum.inr)).det ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D (x ∘ Sum.inr)).det‖ = -(q : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) :=
  fun _ _ _ _ _ D p q x ℓ hx horth => GlobalTheory.CompanionTheory.Ar.Fl.local_basis_gram_det_log D p q x ℓ hx horth

end PositivityTheory.Xgf
