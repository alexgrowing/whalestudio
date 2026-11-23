import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ThDist

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

namespace UpperTheory.V.ML.XCP

private def Rel {K' k : Type} [Field K'] [NumberField K'] [Field k] (π : 𝓞 K' →+* k) (a : K') (b : k) : Prop :=
  ∃ n d : 𝓞 K', π n ≠ 0 ∧ π d ≠ 0 ∧ a * algebraMap _ K' d = algebraMap _ K' n ∧ b * π d = π n

section
variable {K' k : Type} [Field K'] [NumberField K'] [Field k] {π : 𝓞 K' →+* k}

private theorem rel_int (x : 𝓞 K') (hx : π x ≠ 0) : Rel π (x : K') (π x) :=
  ⟨x, 1, hx, by simp, by simp, by simp⟩

private theorem rel_one : Rel π 1 1 := ⟨1, 1, by simp, by simp, by simp, by simp⟩

private theorem rel_mul {a a' : K'} {b b' : k} (h : Rel π a b) (h' : Rel π a' b') : Rel π (a * a') (b * b') := by
  obtain ⟨n, d, hn, hd, h1, h2⟩ := h
  obtain ⟨n', d', hn', hd', h1', h2'⟩ := h'
  refine ⟨n * n', d * d', by simp [hn, hn'], by simp [hd, hd'], ?_, ?_⟩
  · rw [map_mul, map_mul, ← h1, ← h1']; ring
  · rw [map_mul, map_mul, ← h2, ← h2']; ring

private theorem rel_inv {a : K'} {b : k} (h : Rel π a b) : Rel π a⁻¹ b⁻¹ := by
  obtain ⟨n, d, hn, hd, h1, h2⟩ := h
  have hn0 : algebraMap _ K' n ≠ 0 := by
    intro h
    have : n = 0 := by simpa using h
    exact hn (by simp [this])
  have ha : a ≠ 0 := by rintro rfl; exact hn0 (by simpa using h1.symm)
  have hb : b ≠ 0 := by rintro rfl; exact hn (by simpa using h2.symm)
  refine ⟨d, n, hd, hn, ?_, ?_⟩
  · rw [← h1]; field_simp
  · rw [← h2]; field_simp

private theorem rel_pow {a : K'} {b : k} (h : Rel π a b) (n : ℕ) : Rel π (a ^ n) (b ^ n) := by
  induction n with
  | zero => simpa using rel_one
  | succ n ih => rw [pow_succ, pow_succ]; exact rel_mul ih h

private theorem rel_zpow {a : K'} {b : k} (h : Rel π a b) (n : ℤ) : Rel π (a ^ n) (b ^ n) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using rel_pow h m
  · simpa using rel_inv (rel_pow h m)

private theorem rel_prod {ι : Type} (s : Finset ι) {a : ι → K'} {b : ι → k} (h : ∀ i, Rel π (a i) (b i)) :
    Rel π (∏ i ∈ s, a i) (∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rel_one
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi]; exact rel_mul (h i) ih

private theorem rel_val (v : HeightOneSpectrum (𝓞 K')) (hv : ∀ x, π x = 0 ↔ x ∈ v.asIdeal) {a a' : K'} {b : k}
    (h : Rel π a b) (h' : Rel π a' b) : v.valuation K' (a - a') < 1 := by
  obtain ⟨n, d, hn, hd, h1, h2⟩ := h
  obtain ⟨n', d', hn', hd', h1', h2'⟩ := h'
  have e : (a - a') * algebraMap _ K' (d * d') = algebraMap _ K' (n * d' - n' * d) := by
    rw [map_mul, map_sub, map_mul, map_mul, ← h1, ← h1']; ring
  have e1 : v.valuation K' (algebraMap _ K' (d * d')) = 1 := by
    rw [HeightOneSpectrum.valuation_eq_one_iff_notMem, ← hv]
    simp [hd, hd']
  have e2 : v.valuation K' (algebraMap _ K' (n * d' - n' * d)) < 1 := by
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem, ← hv, map_sub, map_mul, map_mul, ← h2, ← h2']
    ring
  rwa [← e, map_mul, e1, mul_one] at e2

private theorem hom_ext {N q : ℕ} [NeZero N] [IsCyclotomicExtension {N} ℚ K'] (hq : q.Prime) [CharP k q]
    {ζ : K'} (hζ : IsPrimitiveRoot ζ N) (φ ψ : 𝓞 K' →+* k) (h : φ hζ.toInteger ^ q = ψ hζ.toInteger ^ q) :
    φ = ψ := by
  haveI := Fact.mk hq
  have h1 : φ hζ.toInteger = ψ hζ.toInteger := frobenius_inj k q h
  have h2 : φ.toIntAlgHom = ψ.toIntAlgHom :=
    AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.Rat.adjoin_singleton_eq_top hζ) (by
      rintro _ rfl; exact h1)
  ext x
  exact DFunLike.congr_fun h2 x

end

private theorem compat (M N : ℕ) [NeZero M] [NeZero N] (K K' : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {N} ℚ K'] [Algebra K K']
    (h : M ∣ N) (t : (ZMod N)ˣ) (x : K) :
    sg N K' t (algebraMap K K' x) = algebraMap K K' (sg M K (ZMod.unitsMap h t) x) := by
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {M} ℚ K
  have h1 := IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply N K' K h (sg N K' t)
  rw [sg, MulEquiv.apply_symm_apply] at h1
  rw [← h1, sg, sg, MulEquiv.symm_apply_apply, AlgEquiv.restrictNormal_commutes]

private theorem comb {G G' k : Type} [CommGroup G] [Fintype G] [DecidableEq G] [Fintype G'] [Field k] (p : G' → G) (u : G) (q : ℕ)
    (hq : 0 < q) (f : G → k) (hf : ∀ t, f t ≠ 0) (hfu : ∀ t, f t = f (u * t) ^ q) (a : G → ℤ) (a' : G' → ℤ)
    (ha : ∀ t, ∑ t' ∈ Finset.univ.filter (fun t' => p t' = t), a' t' = a t - a (u⁻¹ * t)) :
    ∏ t', f (p t') ^ a' t' = ∏ t, (f (u * t) ^ (q - 1)) ^ a t := by
  rw [← Finset.prod_fiberwise Finset.univ p]
  have h1 : ∀ t, ∏ t' ∈ Finset.univ.filter (fun t' => p t' = t), f (p t') ^ a' t'
      = f t ^ a t / f t ^ a (u⁻¹ * t) := by
    intro t
    rw [← zpow_sub₀ (hf t), ← ha, Finset.prod_congr rfl (g := fun t' => f t ^ a' t')
      (fun t' ht' => by rw [(Finset.mem_filter.1 ht').2])]
    induction (Finset.univ.filter (fun t' => p t' = t)) using Finset.cons_induction with
    | empty => simp
    | cons i s hi ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ (hf t)]
  rw [Finset.prod_congr rfl (fun t _ => h1 t), Finset.prod_div_distrib,
    ← Equiv.prod_comp (Equiv.mulLeft u) (fun t => f t ^ a (u⁻¹ * t)), ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun t _ => ?_
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
  rw [← div_zpow, hfu t]
  congr 1
  obtain ⟨q, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have := hf (u * t)
  rw [pow_succ, Nat.add_sub_cancel]
  field_simp

private theorem card_gal (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K']
    [IsGalois K K'] (hq : q.Prime) (hc : q.Coprime M) : Fintype.card Gal(K'/K) = q - 1 := by
  have h1 := Module.finrank_mul_finrank ℚ K K'
  rw [IsCyclotomicExtension.Rat.finrank M K, IsCyclotomicExtension.Rat.finrank (q * M) K', Nat.totient_mul hc,
    Nat.totient_prime hq, mul_comm] at h1
  rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
  exact Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.2 (NeZero.pos M)) h1

end UpperTheory.V.ML.XCP

open UpperTheory.V.ML.XCP in
theorem UpperTheory.V.ML.xCongPrin :
    ∀ (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'], q.Prime → ∀ u : (ZMod M)ˣ, (u : ZMod M) = q → ∀ (b : ℕ), b < q → ∀ y : 𝓞 K', (∀ v : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ v.asIdeal → y ∉ v.asIdeal) →
    ∀ v : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ v.asIdeal →
    v.valuation K' ((∏ t : (ZMod (q * M))ˣ, (sg (q * M) K' t)⁻¹ (y : K') ^ th (q * M) b t) -
      algebraMap K K' ((sg M K u)⁻¹ (∏ t : (ZMod M)ˣ, (sg M K t)⁻¹ (Algebra.norm K (y : K')) ^ th M b t))) < 1 := by
  intro M q _ _ K K' _ _ _ _ _ _ _ hq u hu b hb y hy v hv
  classical
  haveI := Fact.mk hq
  haveI : IsGalois ℚ K' := IsCyclotomicExtension.isGalois {q * M} ℚ K'
  haveI : IsGalois K K' := IsGalois.tower_top_of_isGalois ℚ K K'
  haveI := v.isMaximal
  letI : Field (𝓞 K' ⧸ v.asIdeal) := Ideal.Quotient.field _
  obtain ⟨π, hπ⟩ : ∃ π : 𝓞 K' →+* (𝓞 K' ⧸ v.asIdeal), ∀ x, π x = 0 ↔ x ∈ v.asIdeal :=
    ⟨Ideal.Quotient.mk _, fun x => Ideal.Quotient.eq_zero_iff_mem⟩
  haveI : CharP (𝓞 K' ⧸ v.asIdeal) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    rw [← map_natCast π, hπ]; exact hv)
  have hc : q.Coprime M := by
    rw [← ZMod.isUnit_iff_coprime, ← hu]; exact u.isUnit
  have hd : M ∣ q * M := Dvd.intro_left q rfl

  let act : Gal(K'/ℚ) → 𝓞 K' →+* 𝓞 K' := fun σ => (RingOfIntegers.mapRingEquiv σ.toRingEquiv).toRingHom
  have hact : ∀ σ x, ((act σ x : 𝓞 K') : K') = σ (x : K') := fun _ _ => rfl
  have hmul : ∀ σ τ x, act (σ * τ) x = act σ (act τ x) := fun _ _ _ => rfl
  have hne : ∀ σ, π (act σ y) ≠ 0 := by
    intro σ h
    have hq0 : (q : 𝓞 K') ∈ RingHom.ker (π.comp (act σ)) := by
      rw [RingHom.mem_ker, map_natCast]; exact CharP.cast_eq_zero _ q
    refine hy ⟨RingHom.ker (π.comp (act σ)), RingHom.ker_isPrime _, fun h0 => ?_⟩ hq0 h
    rw [h0, Ideal.mem_bot] at hq0
    exact hq.ne_zero (by exact_mod_cast hq0)
  have hζ := IsCyclotomicExtension.zeta_spec (q * M) ℚ K'
  set ζ := IsCyclotomicExtension.zeta (q * M) ℚ K'
  obtain ⟨w, hw, hwζ⟩ : ∃ w : K, w ^ M = 1 ∧ algebraMap K K' w = ζ ^ q := by
    have h0 := IsCyclotomicExtension.zeta_spec M ℚ K
    have h1 := h0.map_of_injective (algebraMap K K').injective
    obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one (ξ := ζ ^ q) (by rw [← pow_mul, hζ.pow_eq_one])
    exact ⟨_ ^ i, by rw [pow_right_comm, h0.pow_eq_one, one_pow], by rw [map_pow, hi]⟩
  have hcoe : ((hζ.toInteger : 𝓞 K') : K') = ζ := rfl
  have hA : ∀ σ τ : Gal(K'/ℚ), σ (algebraMap K K' w) = τ (algebraMap K K' w) → ∀ x, π (act σ x) = π (act τ x) := by
    intro σ τ h x
    have : π.comp (act σ) = π.comp (act τ) := by
      refine hom_ext hq hζ _ _ ?_
      rw [← map_pow, ← map_pow, RingHom.comp_apply, RingHom.comp_apply]
      congr 1
      apply RingOfIntegers.ext
      rw [hact, hact]
      rw [hwζ] at h
      exact h
    exact DFunLike.congr_fun this x
  choose s hs using ZMod.unitsMap_surjective hd
  have hB : ∀ x, π (act (sg (q * M) K' (s u)) x) = π x ^ q := by
    intro x
    have : π.comp (act (sg (q * M) K' (s u))) = (frobenius _ q).comp π := by
      refine hom_ext hq hζ _ _ ?_
      rw [← map_pow, ← map_pow, RingHom.comp_apply, RingHom.comp_apply, frobenius_def, ← map_pow π]
      congr 1
      apply RingOfIntegers.ext
      rw [hact]
      change sg (q * M) K' (s u) (ζ ^ q) = (ζ ^ q) ^ q
      rw [← hwζ, compat M (q * M) K K' hd, hs, sg_apply M K u hw, ← map_pow, hu, ZMod.val_natCast,
        ← pow_eq_pow_mod _ hw]
    exact DFunLike.congr_fun this x
  let f : (ZMod M)ˣ → 𝓞 K' ⧸ v.asIdeal := fun t => π (act (sg (q * M) K' (s t)⁻¹) y)
  have hf : ∀ t' : (ZMod (q * M))ˣ, π (act (sg (q * M) K' t'⁻¹) y) = f (ZMod.unitsMap hd t') := by
    intro t'
    refine hA _ _ ?_ y
    rw [compat M (q * M) K K' hd, compat M (q * M) K K' hd, map_inv (ZMod.unitsMap hd), map_inv (ZMod.unitsMap hd), hs]
  have hfu : ∀ t, f t = f (u * t) ^ q := by
    intro t
    have h1 := hf ((s u)⁻¹ * s (u * t))
    rw [map_mul (ZMod.unitsMap hd), map_inv (ZMod.unitsMap hd), hs, hs, inv_mul_cancel_left, mul_inv, inv_inv, map_mul, hmul, hB] at h1
    exact h1.symm
  have hcomb := comb (ZMod.unitsMap hd) u q hq.pos f (fun t => hne _) hfu (fun t => th M b t)
    (fun t => th (q * M) b t) (fun t => by convert thDist M q b hq hb u hu t)
  refine rel_val v hπ (b := ∏ t' : (ZMod (q * M))ˣ, f (ZMod.unitsMap hd t') ^ th (q * M) b t') ?_ ?_
  · refine rel_prod _ fun t => rel_zpow ?_ _
    rw [← hf, ← map_inv, ← hact]
    exact rel_int _ (hne _)
  · rw [hcomb, map_prod, map_prod]
    refine rel_prod _ fun t => ?_
    rw [map_zpow₀, map_zpow₀]
    refine rel_zpow ?_ _
    have h1 : (sg M K u)⁻¹ ((sg M K t)⁻¹ (Algebra.norm K (y : K')))
        = sg M K (ZMod.unitsMap hd (s (u * t))⁻¹) (Algebra.norm K (y : K')) := by
      rw [map_inv (ZMod.unitsMap hd), hs, mul_inv, map_mul, map_inv, map_inv]; rfl
    rw [h1, ← compat M (q * M) K K' hd, Algebra.norm_eq_prod_automorphisms, map_prod,
      ← card_gal M q K K' hq hc, ← Finset.card_univ, ← Finset.prod_const]
    refine rel_prod _ fun σ => ?_
    have h2 : f (u * t) = π (act (sg (q * M) K' (s (u * t))⁻¹ * σ.restrictScalars ℚ) y) := by
      refine hA _ _ ?_ y
      rw [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]
    rw [h2]
    exact rel_int (act (sg (q * M) K' (s (u * t))⁻¹ * σ.restrictScalars ℚ) y) (hne _)
