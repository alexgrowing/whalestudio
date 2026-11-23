import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SplitIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.SplitCM
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.TwCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ResTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDecompositionSubgroupIff

open NumberField IntermediateField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Br UpperTheory.V.Z.Win

namespace UpperTheory.V.Z.Win.A4.SplitIrreducibility

private theorem fix_of_dec {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) {l p c : ℕ} (hc : p + 1 = 4 * l * c)
    {δ : Ω} (hδ : δ ^ 2 = -(p : Ω)) (hl : A.valuation (l : Ω) < 1) (g : Ω ≃ₐ[ℚ] Ω)
    (hg : ∀ x, g x ∈ A ↔ x ∈ A) : g δ = δ := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hg2 : g δ = δ ∨ g δ = -δ := by
    refine sq_eq_sq_iff_eq_or_eq_neg.1 ?_
    rw [← map_pow, hδ, map_neg, map_natCast]
  refine hg2.resolve_right fun hneg => ?_
  have hl0 : l ≠ 0 := by rintro rfl; simp at hc
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  have hcast : (p : Ω) + 1 = 4 * l * c := by exact_mod_cast hc
  obtain ⟨w, hw⟩ : ∃ w : Ω, w = (1 + δ) / 2 := ⟨_, rfl⟩
  have h2 : (2 : Ω) ≠ 0 := two_ne_zero
  have hprod : w * (1 - w) = l * c := by
    rw [hw]
    field_simp
    linear_combination (-1 : Ω) * hδ + hcast
  have hgw : g w = 1 - w := by
    rw [hw, map_div₀, map_add, map_one, hneg, map_ofNat]
    field_simp
    ring
  have hgw' : g (1 - w) = w := by rw [map_sub, map_one, hgw]; ring
  have hlc : (l : Ω) * c ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 hl0) (Nat.cast_ne_zero.2 hc0)
  have hw0 : w ≠ 0 := fun h => hlc (by rw [← hprod, h, zero_mul])
  have hw1 : 1 - w ≠ 0 := fun h => hlc (by rw [← hprod, h, mul_zero])
  have small : ∀ x : Ω, x⁻¹ ∉ A → A.valuation x < 1 := fun x hx => by
    by_contra hge
    refine hx ((A.valuation_le_one_iff _).1 ?_)
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (not_lt.1 hge)
  by_cases hin : w⁻¹ ∈ A
  · have hin' : (1 - w)⁻¹ ∈ A := by
      have := (hg _).2 hin
      rwa [map_inv₀, hgw] at this
    have hli : (l : Ω)⁻¹ ∈ A := by
      have e : (l : Ω)⁻¹ = (c : Ω) * (w⁻¹ * (1 - w)⁻¹) := by
        have hl' : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl0
        have hc' : (c : Ω) ≠ 0 := Nat.cast_ne_zero.2 hc0
        rw [← mul_inv, hprod]
        field_simp
      rw [e]
      exact mul_mem (natCast_mem A c) (mul_mem hin hin')
    have h1 : (1 : _) ≤ A.valuation (l : Ω) := by
      have h3 := (A.valuation_le_one_iff _).2 hli
      rw [map_inv₀] at h3
      exact (inv_le_one₀ (zero_lt_iff.2 (by simpa using hl0))).1 h3
    exact absurd hl (not_lt.2 h1)
  · have hout : (1 - w)⁻¹ ∉ A := fun h => hin (by
      have := (hg _).2 h
      rwa [map_inv₀, hgw'] at this)
    have := Valuation.map_add_lt _ (small w hin) (small _ hout)
    simp at this

private theorem no_sq_pos {t : ℚ} {q : ℕ} (hq : q.Prime) (h : t * t = -(q : ℚ)) : False := by
  have h1 : (0 : ℚ) < q := by exact_mod_cast hq.pos
  nlinarith [mul_self_nonneg t]

private theorem no_sq_mul {t : ℚ} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : t * t = (p : ℚ) * q) : False := by
  have h1 : IsSquare (((p * q : ℕ)) : ℚ) := ⟨t, by push_cast; exact h.symm⟩
  rw [Rat.isSquare_natCast_iff] at h1
  obtain ⟨m, hm⟩ := h1
  have h2 : p ∣ m := by
    have : p ∣ m * m := hm ▸ Dvd.intro _ rfl
    exact (hp.dvd_mul.1 this).elim id id
  obtain ⟨k, rfl⟩ := h2
  have h3 : q = p * (k * k) := by
    have : p * q = p * (p * (k * k)) := by rw [hm]; ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos this
  have h4 : p ∣ q := ⟨_, h3⟩
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 h4)

private theorem no_two {K : Type} [Field K] [Algebra ℚ K] (h2 : Module.finrank ℚ K = 2) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {x y : K} (hx : x * x = -(p : K)) (hy : y * y = -(q : K)) : False := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  haveI : FiniteDimensional ℚ K := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  have hdep : ¬ LinearIndependent ℚ ![(1 : K), x, y] := fun h => by
    have := h.fintype_card_le_finrank
    rw [h2] at this
    simp at this
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg, i, hi⟩ := hdep
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Algebra.smul_def, mul_one] at hg
  obtain ⟨a, b, c, ha, hb, hc⟩ : ∃ a b c : ℚ, a = g 0 ∧ b = g 1 ∧ c = g 2 := ⟨_, _, _, rfl, rfl, rfl⟩
  rw [← ha, ← hb, ← hc] at hg
  let φ := algebraMap ℚ K
  have inj : ∀ s t : ℚ, φ s = φ t → s = t := fun s t h => φ.injective h
  have hcast : ∀ m : ℕ, φ (m : ℚ) = (m : K) := fun m => map_natCast φ m
  have one_var : ∀ {u : K} {m : ℕ} {d e : ℚ}, m.Prime → u * u = -(m : K) → d ≠ 0 → φ e + φ d * u = 0 → False := by
    intro u m d e hm hu hd h
    have hd' : φ d ≠ 0 := fun h0 => hd (inj _ _ (by rw [h0, map_zero]))
    have e1 : u = φ (-e / d) := by
      rw [map_div₀, map_neg]
      field_simp
      linear_combination h
    refine no_sq_pos (t := -e / d) hm (inj _ _ ?_)
    rw [map_mul, ← e1, hu, map_neg, hcast]
  by_cases hb0 : b = 0
  · by_cases hc0 : c = 0
    · have ha0 : a = 0 := inj _ _ (by simpa [hb0, hc0, φ] using hg)
      fin_cases i
      · exact hi (ha ▸ ha0)
      · exact hi (hb ▸ hb0)
      · exact hi (hc ▸ hc0)
    · exact one_var hq hy hc0 (by simpa [hb0, φ] using hg)
  · by_cases hc0 : c = 0
    · exact one_var hp hx hb0 (by simpa [hc0, φ] using hg)
    · have hb' : φ b ≠ 0 := fun h0 => hb0 (inj _ _ (by rw [h0, map_zero]))
      have hc' : φ c ≠ 0 := fun h0 => hc0 (inj _ _ (by rw [h0, map_zero]))
      have h2' : (2 : K) ≠ 0 := two_ne_zero
      have hxy : x * y = φ ((a * a + b * b * p + c * c * q) / (2 * b * c)) := by
        have e2 : φ b * x + φ c * y = -φ a := by linear_combination hg
        have e3 : 2 * (φ b * φ c) * (x * y) = φ a * φ a + φ b * φ b * p + φ c * φ c * q := by
          linear_combination (φ b * x + φ c * y - φ a) * e2 - φ b * φ b * hx - φ c * φ c * hy
        rw [map_div₀]
        simp only [map_add, map_mul, hcast, map_ofNat]
        field_simp
        linear_combination e3
      refine no_sq_mul (t := (a * a + b * b * p + c * c * q) / (2 * b * c)) hp hq hpq (inj _ _ ?_)
      rw [map_mul, ← hxy, map_mul, hcast, hcast]
      linear_combination (x * x) * hy + (-(q : K)) * hx

private theorem good_inf (l : ℕ) (hl : l ≠ 0) : {p : ℕ | p.Prime ∧ 4 * l ∣ p + 1}.Infinite := by
  obtain ⟨k, hk⟩ : ∃ k, 4 * l = k + 1 := ⟨4 * l - 1, by omega⟩
  refine Set.infinite_of_forall_exists_gt fun n => ?_
  obtain ⟨q, hn, hq, hm⟩ := Nat.forall_exists_prime_gt_and_modEq n (q := k + 1) (a := k) (by omega) (by simp)
  refine ⟨q, ⟨hq, ?_⟩, hn⟩
  rw [hk]
  exact (Nat.modEq_zero_iff_dvd).1 ((hm.add_right 1).trans (by simp [Nat.ModEq]))

private theorem mem_of_range {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] (K K' : Type) [Field K] [Field K'] [NumberField K] [NumberField K'] [Algebra K Ω]
    [Algebra K' Ω] [IsScalarTower ℚ K Ω] [IsScalarTower ℚ K' Ω] (h : (res ℚ Ω K).range = (res ℚ Ω K').range) (y : K') :
    ∃ x : K, algebraMap K Ω x = algebraMap K' Ω y := by
  have hy : algebraMap K' Ω y ∈ IntermediateField.fixedField
      (IsScalarTower.toAlgHom ℚ K Ω).fieldRange.fixingSubgroup := by
    rintro ⟨s, hs⟩
    have hs' : s ∈ (res ℚ Ω K).range := by
      rw [IntermediateField.mem_fixingSubgroup_iff] at hs
      refine ⟨{ s.toRingEquiv with commutes' := fun z => hs _ ⟨z, rfl⟩ }, ?_⟩
      ext x
      rfl
    rw [h] at hs'
    obtain ⟨t, rfl⟩ := hs'
    exact t.commutes y
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hy
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, hx⟩

private theorem finrank_any {M : Type} [AddCommGroup M] (m₁ m₂ : Module ℚ M) :
    @Module.finrank ℚ M _ _ m₁ = @Module.finrank ℚ M _ _ m₂ := by
  rw [Subsingleton.elim m₁ m₂]

private theorem fix_gen {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (L : IntermediateField F Ω) {δ : Ω} (h : L = F⟮δ⟯)
    (g : Ω ≃ₐ[F] Ω) (hg : g δ = δ) (x : L) : g (x : Ω) = x := by
  have hext : (g : Ω →ₐ[F] Ω).comp L.val = L.val := by
    refine IntermediateField.algHom_ext_of_eq_adjoin F h ?_
    rintro y rfl
    exact hg
  exact DFunLike.congr_fun hext x

private theorem exK (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {p : ℕ} (hp : p.Prime) (δ : Ω) (hδ : δ ^ 2 = -(p : Ω)) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K) (_ : Algebra K Ω) (_ : IsScalarTower ℚ K Ω),
      Module.finrank ℚ K = 2 ∧ (∃ x : K, algebraMap K Ω x = δ) ∧
      ∀ g : Ω ≃ₐ[ℚ] Ω, g δ = δ → ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x := by
  obtain ⟨Q, hQ⟩ := GlobalTheory.ExSplitCM.exists_qcm (F := ℚ) (-(p : ℚ)) δ (by simp [hδ]) fun φ => by
    simp only [map_neg, map_natCast, neg_lt_zero]
    exact_mod_cast hp.pos
  have hmem : δ ∈ Q.K := hQ ▸ IntermediateField.mem_adjoin_simple_self ℚ δ
  have t : IsScalarTower ℚ ↥Q.K Ω := IsScalarTower.of_algebraMap_eq fun x => by simp
  refine ⟨↥Q.K, inferInstance, inferInstance, inferInstance, inferInstance, t, ?_, ⟨⟨δ, hmem⟩, rfl⟩, ?_⟩
  · exact (finrank_any _ _).trans Q.two
  · exact fun g hg x => fix_gen Q.K hQ g hg x

end UpperTheory.V.Z.Win.A4.SplitIrreducibility

open UpperTheory.V.Z.Win.A4.SplitIrreducibility in
theorem UpperTheory.V.Z.Win.A4.splitIrr :
    SplitIrr := by
  intro Ω _ _ _ l _ n r hr
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hsq : ∀ p : ℕ, ∃ δ : Ω, δ ^ 2 = -(p : Ω) := fun p => IsAlgClosed.exists_pow_nat_eq _ two_pos
  choose δ hδ using hsq
  have hS := good_inf l hl0
  let P : Fin (n ^ 2 + 1) → ℕ := fun i => (hS.natEmbedding _ (i : ℕ)).1
  have hPi : Function.Injective P := fun i j h =>
    Fin.ext (hS.natEmbedding _ |>.injective (Subtype.ext h))
  have hPp : ∀ i, (P i).Prime ∧ 4 * l ∣ P i + 1 := fun i => (hS.natEmbedding _ (i : ℕ)).2
  choose K i1 i2 i3 i4 i5 h2 hx hfix using fun i => exK Ω (hPp i).1 (δ (P i)) (hδ _)
  haveI clo : ∀ i, IsAlgClosure (K i) Ω := fun i => ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  choose χ _ _ hχ _ using fun i => UpperTheory.exists_quadratic_sign_character ℚ (K i) Ω l (h2 i)
  have hsqK : ∀ i (x : K i) j, algebraMap (K i) Ω x = δ (P j) → x * x = -(P j : K i) := fun i x j h => by
    apply (algebraMap (K i) Ω).injective
    rw [map_mul, h, ← sq, hδ, map_neg, map_natCast]
  have hχi : Function.Injective χ := fun i j hij => by
    by_contra hne
    have hrange : (res ℚ Ω (K i)).range = (res ℚ Ω (K j)).range := Subgroup.ext fun s => by
      rw [← (hχ i).1, ← (hχ j).1, hij]
    obtain ⟨x, hx'⟩ := hx i
    obtain ⟨y₀, hy₀⟩ := hx j
    obtain ⟨y, hy⟩ := mem_of_range (K i) (K j) hrange y₀
    exact no_two (h2 i) (hPp i).1 (hPp j).1 (fun h => hne (hPi h)) (hsqK i x i hx') (hsqK i y j (hy.trans hy₀))
  obtain ⟨i, hi⟩ : ∃ i, ¬ RepIso r (tw r (χ i)) := by
    by_contra hall
    have h1 := twCard _ _ n r hr (Finset.univ.image χ) fun d hd => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hd
      by_contra h
      exact hall ⟨i, h⟩
    rw [Finset.card_image_of_injective _ hχi, Finset.card_univ, Fintype.card_fin] at h1
    omega
  have hirr := (resTwo _ _ _ n (res ℚ Ω (K i)) (χ i) (hχ i).1 (hχ i).2 r).1 hr hi
  refine ⟨K i, i1 i, i2 i, i3 i, i4 i, i5 i, h2 i, hirr, fun A hA g hg x => hfix i g ?_ x⟩
  obtain ⟨c, hc⟩ := (hPp i).2
  exact fix_of_dec A hc (hδ _) hA g ((GlobalTheory.QuadSplit.mem_decompositionSubgroup_iff' A g).1 hg)
