import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharValuesInNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharactersPrescribedValuesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteBaseDataAdmissibleStatement
import Development.AutomorphicArithmetic.FrobeniusLocalisation.MuProdtameeqone

open UpperTheory.HF

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

noncomputable section

namespace GlobalTheory.Mem.DatHecke

open Formalism.L2.Host (HChar embPsi)
open GlobalTheory.Mem.Chr (ConjPl CMData)

theorem exists_common_field {ι : Type} [Finite ι] (Q : ι → IntermediateField ℚ ℂ → Prop)
    (mono : ∀ i M M', M ≤ M' → Q i M → Q i M') (h : ∀ i, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ Q i M) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ i, Q i M := by
  choose M hM hQ using h
  exact ⟨⨆ i, M i, inferInstance, fun i => mono i _ _ (le_iSup M i) (hQ i)⟩

theorem exists_gen (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] :
    ∃ α : ℂ, IsAlgebraic ℚ α ∧ ∀ (K : Type) [Field K] [CharZero K] (σ : K →+* ℂ), (∃ x, σ x = α) →
      ∀ z ∈ M, ∃ x, σ x = z := by
  obtain ⟨a, ha⟩ := Field.exists_primitive_element ℚ M
  refine ⟨a, (Algebra.IsAlgebraic.isAlgebraic a).algHom M.val, ?_⟩
  intro K _ _ σ ⟨x, hx⟩ z hz
  have h1 : (⊤ : IntermediateField ℚ M) ≤ (σ.toRatAlgHom.fieldRange).comap M.val := by
    rw [← ha]
    exact IntermediateField.adjoin_simple_le_iff.2 ⟨x, hx⟩
  exact h1 (IntermediateField.mem_top (x := (⟨z, hz⟩ : M)))

section Host

variable {R : Ranks} (H : Host R)

def IsAnti (S : Finset (HeightOneSpectrum (𝓞 H.E))) (e : Tau R → ℚ)
    (θ : ∀ w : {w // w ∈ S}, (𝓞 H.E ⧸ w.1.asIdeal)ˣ →* ℂˣ) (χ : HChar H.E) : Prop :=
  χ.IsUnitary ∧ χ.TrivOn H.F ∧ χ.HasInfQ (embPsi H) (fun τ => -e τ) ∧
    (∀ v : HeightOneSpectrum (𝓞 H.E), (∀ i, ((H.g i : ℕ) : 𝓞 H.E) ∉ v.asIdeal) → χ.UnrAt v) ∧ (∀ v, χ.TameAt v) ∧
    ∀ (w : {w // w ∈ S}) (x : H.Eˣ) (y : 𝓞 H.E) (c : (𝓞 H.E ⧸ w.1.asIdeal)ˣ), (x : H.E) = (y : H.E) →
      (c : 𝓞 H.E ⧸ w.1.asIdeal) = Ideal.Quotient.mk w.1.asIdeal y → χ.locK w.1 x = θ w c

theorem mem_iff_of_conjPl {c : H.E ≃+* H.E} {w w' : HeightOneSpectrum (𝓞 H.E)} (h : ConjPl c w w')
    {x y : 𝓞 H.E} (hxy : c x = y) : x ∈ w.asIdeal ↔ y ∈ w'.asIdeal := by
  have h1 := h (x : H.E)
  rw [hxy] at h1
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := H.E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := H.E)]
  exact (h1 ▸ Iff.rfl)

theorem exists_isAnti (S : Finset (HeightOneSpectrum (𝓞 H.E))) (e : Tau R → ℚ)
    (θ : ∀ w : {w // w ∈ S}, (𝓞 H.E ⧸ w.1.asIdeal)ˣ →* ℂˣ)
    (hS : ∀ w ∈ S, ∃ i, ((H.g i : ℕ) : 𝓞 H.E) ∈ w.asIdeal)
    (hc : ∀ w ∈ S, ∀ w', ConjPl H.conj.toRingEquiv w w' → w' ∉ S)
    (hev : UpperTheory.MUQ (fun τ : Tau R => H.emb (τ : R.GG)) e)
    (hθ : ∀ ζ : (𝓞 H.E)ˣ, (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 H.E) : H.E) ^ m = 1) →
      ∏ w : {w // w ∈ S}, θ w (Units.map (Ideal.Quotient.mk w.1.asIdeal).toMonoidHom ζ) = 1) :
    ∃ χ, IsAnti H S e θ χ := by
  classical
  obtain ⟨z, hz, hmu⟩ := hev
  obtain ⟨c, hcc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hce : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hcc
  obtain ⟨χ, hu, ht, hi, htame, hunr, hloc, -⟩ := GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn H.F H.E c (Tau R) (embPsi H) hcm z S
    (fun v => if h : v ∈ S then θ ⟨v, h⟩ else 1) (by rw [hce]; exact hc)
    (fun ζ hζ => by
      have h1 : ∏ τ : Tau R, embPsi H τ ((ζ : 𝓞 H.E) : H.E) ^ (-z τ) = 1 := hmu.neg _ hζ
      rw [h1, one_mul, ← Units.coe_prod, ← Finset.prod_coe_sort, ← Units.val_one, ← hθ ζ hζ]
      congr 1
      exact Finset.prod_congr rfl fun w _ => by simp only [dif_pos w.2])
  refine ⟨χ, hu, ht, ⟨_, fun τ => ?_, hi⟩, fun v hv => hunr v ?_ ?_, htame, fun w x y b hx hb => ?_⟩
  · show _ = 2 * -e τ
    rw [hz τ]
    push_cast
    ring
  · intro h
    obtain ⟨k, hk⟩ := hS v h
    exact hv k hk
  · intro w hw hcj
    obtain ⟨k, hk⟩ := hS w hw
    exact hv k ((mem_iff_of_conjPl H hcj (by simp)).1 hk)
  · rw [hloc w.1 w.2 x y b hx hb]
    simp only [dif_pos w.2]

theorem exists_value_field (S : Finset (HeightOneSpectrum (𝓞 H.E))) {m : ℕ} (e : Fin m → Tau R → ℚ)
    (hint : ∀ j τ, ∃ z : ℤ, e j τ = z) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
      (∀ j θ, (∃ χ, IsAnti H S (e j) θ χ) → ∃ χ, IsAnti H S (e j) θ χ ∧ ∀ v, χ.UnrAt v → ((χ.val v : ℂˣ) : ℂ) ∈ M) ∧
      ∃ η, Formalism.L2.Host.IsEtaT H η ∧ ∀ v, η.valTw (1 / 2) v ∈ M := by
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hfin : ∀ w : {w // w ∈ S}, Finite ((𝓞 H.E ⧸ w.1.asIdeal)ˣ →* ℂˣ) := fun w => by
    have : Finite (𝓞 H.E ⧸ w.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
    infer_instance
  obtain ⟨M₁, hM₁, h₁⟩ := exists_common_field
    (ι := Fin m × ∀ w : {w // w ∈ S}, (𝓞 H.E ⧸ w.1.asIdeal)ˣ →* ℂˣ)
    (fun p M => (∃ χ, IsAnti H S (e p.1) p.2 χ) →
      ∃ χ, IsAnti H S (e p.1) p.2 χ ∧ ∀ v, χ.UnrAt v → ((χ.val v : ℂˣ) : ℂ) ∈ M)
    (fun p M M' hle h hex => by
      obtain ⟨χ, h1, h2⟩ := h hex
      exact ⟨χ, h1, fun v hv => hle (h2 v hv)⟩)
    (fun p => by
      by_cases hex : ∃ χ, IsAnti H S (e p.1) p.2 χ
      · obtain ⟨χ, hχ⟩ := hex
        obtain ⟨n, hn, hinf⟩ := hχ.2.2.1
        obtain ⟨M, hM, hv⟩ := GlobalTheory.T.algebraicHeckeChar_values_in_numberField H.F H.E c (Tau R) (embPsi H) hcm χ n 0 hinf (fun τ => by
          obtain ⟨z, hz⟩ := hint p.1 τ
          have h3 : (n τ : ℚ) = ((-z + -z : ℤ) : ℚ) := by
            rw [hn τ]
            simp only [hz]
            push_cast
            ring
          exact ⟨-z, by rw [sub_zero]; exact_mod_cast h3⟩)
        refine ⟨M, hM, fun _ => ⟨χ, hχ, fun v hu => ?_⟩⟩
        obtain ⟨y, hy⟩ := hv v hu
        have h4 : (y : ℂ) = ((χ.val v : ℂˣ) : ℂ) := by simpa [HChar.valTw] using hy
        exact h4 ▸ y.2
      · exact ⟨⊥, inferInstance, fun h => absurd h hex⟩)
  obtain ⟨η, hη⟩ := GlobalTheory.Mem.EtaT.etaT_exists R H
  obtain ⟨M₂, hM₂, h₂⟩ := GlobalTheory.T.algebraicHeckeChar_values_in_numberField H.F H.E c (Tau R) (embPsi H) hcm η (fun _ => 1) 1 hη.inf (fun _ => by simp)
  refine ⟨M₁ ⊔ M₂, inferInstance, fun j θ hex => ?_, η, hη, fun v => ?_⟩
  · obtain ⟨χ, h1, h2⟩ := h₁ (j, θ) hex
    exact ⟨χ, h1, fun v hv => (le_sup_left : M₁ ≤ M₁ ⊔ M₂) (h2 v hv)⟩
  · obtain ⟨y, hy⟩ := h₂ v (hη.unr v)
    have h4 : (y : ℂ) = η.valTw (1 / 2) v := by simpa using hy
    exact h4 ▸ (le_sup_right : M₂ ≤ M₁ ⊔ M₂) y.2

end Host

open Classical in

def typePlaces (B : Pre) (X : PreX B) : Finset (HeightOneSpectrum (𝓞 B.host.E)) :=
  letI := B.host.cmStar
  divs (RingOfIntegers.mapRingHom (starRingEnd B.host.E) (X.piG 0)) ∪
    divs (RingOfIntegers.mapRingHom (starRingEnd B.host.E) (X.piG 1))

theorem vGs_eq (B : Base) (X : PreX B.toPre) : (B.primes X).vGs = typePlaces B.toPre X := rfl

section PrimesOk

variable {X : Fields} {Pr : Primes X}

theorem mem_vG (h : Pr.Ok) (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.E)) :
    w ∈ Pr.vG i ↔ X.conjO (Pr.piG i) ∈ w.asIdeal := by
  refine mem_divs (fun h0 => ?_) w
  have h1 := h.piG_norm i
  rw [h0, mul_zero] at h1
  have h2 : (Pr.g i : 𝓞 X.E) ≠ 0 := by exact_mod_cast (h.g_prime i).ne_zero
  exact h2 h1.symm

theorem mem_vGs (w : HeightOneSpectrum (𝓞 X.E)) : w ∈ Pr.vGs ↔ ∃ i, w ∈ Pr.vG i := by
  classical
  unfold Primes.vGs
  rw [Fin.exists_fin_two]
  convert Finset.mem_union

theorem g_mem_of_mem_vG (h : Pr.Ok) {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.asIdeal := by
  rw [← h.piG_norm i]
  exact w.asIdeal.mul_mem_left _ ((mem_vG h i w).1 hw)

theorem not_mem_both {A : Type} [CommRing A] {w : HeightOneSpectrum A} {a b : A} (h : IsCoprime a b) (ha : a ∈ w.asIdeal)
    (hb : b ∈ w.asIdeal) : False := by
  obtain ⟨s, t, hst⟩ := h
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hst]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ ha) (w.asIdeal.mul_mem_left _ hb)

theorem not_mem_vGs (h : Pr.Ok) {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : Pr.piG i ∈ w.asIdeal) :
    w ∉ Pr.vGs := by
  intro hw'
  obtain ⟨k, hk⟩ := (mem_vGs w).1 hw'
  by_cases hik : i = k
  · subst hik
    exact not_mem_both (h.piG_cop i) hw ((mem_vG h i w).1 hk)
  · have hg : Pr.g i ≠ Pr.g k := by
      fin_cases i <;> fin_cases k
      · exact absurd rfl hik
      · exact h.g_ne
      · exact h.g_ne.symm
      · exact absurd rfl hik
    have hc : IsCoprime ((Pr.g i : ℕ) : 𝓞 X.E) ((Pr.g k : ℕ) : 𝓞 X.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes (h.g_prime i) (h.g_prime k)).2 hg)
    refine not_mem_both hc ?_ (g_mem_of_mem_vG h hk)
    rw [← h.piG_norm i]
    exact w.asIdeal.mul_mem_right _ hw

theorem chi_neg_one (h : Pr.Ok) {m : ℕ} {Ch : Chars X Pr m} (hC : Ch.Ok) (j : Fin m) (w : {w // w ∈ Pr.vGs}) :
    Ch.chi j w (-1) = 1 := by
  obtain ⟨i, hi⟩ := (mem_vGs w.1).1 w.2
  obtain ⟨om, -, hom⟩ := hC.chi_om i
  have : NeZero (Pr.g i) := ⟨(h.g_prime i).ne_zero⟩
  have hg : ((Pr.g i : ℕ) : 𝓞 X.E ⧸ w.1.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.1.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact g_mem_of_mem_vG h hi
  rw [hom w hi j (-1) (-1), pow_mul, ← map_pow, neg_one_sq, map_one, one_pow]
  have h1 : ((((-1 : (ZMod (Pr.g i))ˣ) : ZMod (Pr.g i)).val + 1 : ℕ) : ZMod (Pr.g i)) = 0 := by simp
  obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff _ _).1 h1
  have h2 := congrArg (Nat.cast : ℕ → 𝓞 X.E ⧸ w.1.asIdeal) ht
  rw [Nat.cast_mul, hg, zero_mul, Nat.cast_add, Nat.cast_one] at h2
  rw [Units.val_neg, Units.val_one]
  exact (eq_neg_of_add_eq_zero_left h2).symm

end PrimesOk

private theorem span_isMaximal {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    {a b : 𝓞 K} (hab : a * b = (p : 𝓞 K)) (ha : ¬ IsUnit a) (hb : ¬ IsUnit b) :
    b ≠ 0 ∧ (Ideal.span {b}).IsMaximal := by
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hb0 : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hp0)
  have h1 : Ideal.absNorm (Ideal.span {a}) * Ideal.absNorm (Ideal.span {b}) = p ^ 2 := by
    rw [← map_mul, Ideal.span_singleton_mul_span_singleton, hab, Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK]
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro_left _ h1)
  have hN : Ideal.absNorm (Ideal.span {b}) = p := by
    interval_cases k
    · rw [pow_zero, Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top] at hk'
      exact absurd hk' hb
    · rw [hk', pow_one]
    · rw [hk', mul_eq_right₀ (pow_ne_zero _ hp.ne_zero), Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top] at h1
      exact absurd h1 ha
  have hP : (Ideal.span {b}).IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hN]; exact hp)
  exact ⟨hb0, hP.isMaximal (by rwa [Ne, Ideal.span_singleton_eq_bot])⟩

private theorem exists_under (B : Base) (X : PreX B.toPre) (i : Fin 2) (hne : ((B.primes X).vG i).Nonempty) :
    ∃ Q : HeightOneSpectrum (𝓞 B.host.K), ((B.host.g i : ℕ) : 𝓞 B.host.K) ∈ Q.asIdeal ∧
      ∀ w : HeightOneSpectrum (𝓞 B.host.E), w ∈ (B.primes X).vG i ↔ w.under (𝓞 B.host.K) = Q := by
  have hP := (GlobalTheory.BasePrimes.primes_ok B X).1
  obtain ⟨w₀, hw₀⟩ := hne
  have hw₀' := (mem_vG hP i w₀).1 hw₀
  have hn : X.piG i * B.fields.conjO (X.piG i) = ((B.host.g i : ℕ) : 𝓞 B.host.E) := hP.piG_norm i
  have hg0 : ((B.host.g i : ℕ) : 𝓞 B.host.E) ≠ 0 := by exact_mod_cast (B.host.g_prime i).ne_zero
  have ha0 : ((X.piG i : 𝓞 B.host.E) : B.host.E) ≠ 0 :=
    RingOfIntegers.coe_ne_zero_iff.2 (left_ne_zero_of_mul (hn ▸ hg0))
  have hbK : ((B.fields.conjO (X.piG i) : 𝓞 B.host.E) : B.host.E) ∈ B.host.K := by
    have e : ((B.fields.conjO (X.piG i) : 𝓞 B.host.E) : B.host.E)
        = ((X.piG i : 𝓞 B.host.E) : B.host.E)⁻¹ * ((B.host.g i : ℕ) : B.host.E) := by
      rw [B.fields_conjO_coe, ← X.piG_norm i, inv_mul_cancel_left₀ ha0]
    rw [e]
    exact mul_mem (inv_mem (X.piG_K i)) (natCast_mem _ _)
  have lift : ∀ x : 𝓞 B.host.E, (x : B.host.E) ∈ B.host.K →
      ∃ y : 𝓞 B.host.K, algebraMap (𝓞 B.host.K) (𝓞 B.host.E) y = x := fun x hx =>
    ⟨⟨⟨x, hx⟩, (isIntegral_algebraMap_iff (algebraMap B.host.K B.host.E).injective).1 x.isIntegral_coe⟩,
      RingOfIntegers.ext rfl⟩
  obtain ⟨a, ha⟩ := lift _ (X.piG_K i)
  obtain ⟨b, hb⟩ := lift _ hbK
  have hab : a * b = ((B.host.g i : ℕ) : 𝓞 B.host.K) := by
    apply RingOfIntegers.algebraMap.injective B.host.K B.host.E
    rw [map_mul, ha, hb, hn, map_natCast]
  have hnu : ¬ IsUnit (B.fields.conjO (X.piG i)) := fun hu =>
    w₀.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hw₀' hu)
  obtain ⟨hb0, hmax⟩ := span_isMaximal B.host.finrank_K (B.host.g_prime i) hab
    (fun hu => hnu (by rw [← ha]; exact (hu.map _).map _)) (fun hu => hnu (by rw [← hb]; exact hu.map _))
  refine ⟨⟨Ideal.span {b}, hmax.isPrime, by rwa [Ne, Ideal.span_singleton_eq_bot]⟩, ?_, fun w => ?_⟩
  · rw [← hab]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self b)
  · have hm : w ∈ (B.primes X).vG i ↔ b ∈ (w.under (𝓞 B.host.K)).asIdeal := by
      rw [mem_vG hP i w]
      show B.fields.conjO (X.piG i) ∈ w.asIdeal ↔ algebraMap (𝓞 B.host.K) (𝓞 B.host.E) b ∈ w.asIdeal
      rw [hb]
    rw [hm]
    constructor
    · intro h
      exact HeightOneSpectrum.ext
        (hmax.eq_of_le (w.under (𝓞 B.host.K)).isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h)).symm
    · intro h
      rw [h]
      exact Ideal.mem_span_singleton_self b

theorem prod_chi_root (B : Base) (X : PreX B.toPre) {m : ℕ} {Ch : Chars B.fields (B.primes X) m} (hC : Ch.Ok) (j : Fin m)
    (ζ : (𝓞 B.host.E)ˣ) (hζ : ∃ n : ℕ, 0 < n ∧ ((ζ : 𝓞 B.host.E) : B.host.E) ^ n = 1) :
    ∏ w : {w // w ∈ (B.primes X).vGs}, Ch.chi j w (Units.map (Ideal.Quotient.mk w.1.asIdeal).toMonoidHom ζ) = 1 := by
  classical
  have hP := (GlobalTheory.BasePrimes.primes_ok B X).1
  let σ : B.LLˣ →* ℂˣ := Units.map (B.embLL : B.LL →* ℂ)
  let θ : ∀ w : HeightOneSpectrum (𝓞 B.host.E), (𝓞 B.host.E ⧸ w.asIdeal)ˣ →* ℂˣ := fun w =>
    if h : w ∈ (B.primes X).vGs then σ.comp (Ch.chi j ⟨w, h⟩) else 1
  have hi : ∀ i, ∏ w ∈ (B.primes X).vG i, θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) = 1 := by
    intro i
    rcases ((B.primes X).vG i).eq_empty_or_nonempty with h0 | hne
    · rw [h0, Finset.prod_empty]
    obtain ⟨Q, hQ, hmem⟩ := exists_under B X i hne
    obtain ⟨om, -, hom⟩ := hC.chi_om i
    have hS : (B.primes X).vG i = Formalism.L2.Host.aboveF (L := B.host.E) B.host.K Q := by
      ext w
      rw [hmem, Formalism.L2.Host.aboveF, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    have hs := (B.host.splitsC_facts _ (B.host.g_prime i)).1 (hP.g_cong i)
    have key := B.host.prod_tame_eq_one _ (B.host.g_prime i) hs Q hQ ((σ.comp om) ^ (2 * (j.1 + 1))) θ
      (fun w hw a ha b hb => by
        rw [← hS] at hw
        have hw' : w ∈ (B.primes X).vGs := (mem_vGs (Pr := B.primes X) w).2 ⟨i, hw⟩
        have : NeZero (B.host.g i) := ⟨(B.host.g_prime i).ne_zero⟩
        have hg : ((B.host.g i : ℕ) : 𝓞 B.host.E ⧸ w.asIdeal) = 0 := by
          rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
          exact g_mem_of_mem_vG hP hw
        have h1 := hom ⟨w, hw'⟩ hw j (ZMod.unitOfCoprime a ha) b (by
          rw [hb, map_natCast, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
          conv_lhs => rw [← Nat.mod_add_div a (B.host.g i), Nat.cast_add, Nat.cast_mul, hg, zero_mul, add_zero])
        simp only [θ, dif_pos hw', MonoidHom.comp_apply, MonoidHom.pow_apply]
        rw [← map_pow]
        exact congrArg σ h1) ζ hζ
    rw [hS]
    exact key
  have hd : Disjoint ((B.primes X).vG 0) ((B.primes X).vG 1) := Finset.disjoint_left.2 fun w h0 h1 =>
    not_mem_both (Nat.Coprime.cast ((Nat.coprime_primes (hP.g_prime 0) (hP.g_prime 1)).2 hP.g_ne))
      (g_mem_of_mem_vG hP h0) (g_mem_of_mem_vG hP h1)
  have hall : ∏ w ∈ (B.primes X).vGs, θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) = 1 := by
    have e : (B.primes X).vGs = (B.primes X).vG 0 ∪ (B.primes X).vG 1 := by
      ext w
      rw [mem_vGs, Fin.exists_fin_two, Finset.mem_union]
    rw [e, Finset.prod_union hd, hi 0, hi 1, mul_one]
  apply Units.map_injective (f := (B.embLL : B.LL →* ℂ)) B.embLL.injective
  rw [map_prod, map_one, ← hall, ← Finset.prod_coe_sort (B.primes X).vGs]
  exact Finset.prod_congr rfl fun w _ => by simp only [θ, dif_pos w.2]; rfl

theorem exists_units_lift {K ι : Type} [Field K] (σ : K →+* ℂ) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0) :
    ∃ u : ι → Kˣ, ∀ i, (∃ x, σ x = a i) → σ (u i) = a i := by
  have : ∀ i, ∃ u : Kˣ, (∃ x, σ x = a i) → σ u = a i := fun i => by
    by_cases h : ∃ x, σ x = a i
    · obtain ⟨x, hx⟩ := h
      have h0 : x ≠ 0 := by
        rintro rfl
        exact ha i (by rw [← hx, map_zero])
      exact ⟨Units.mk0 x h0, fun _ => hx⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose u hu using this
  exact ⟨u, hu⟩

theorem exists_base_dat_ok : ∀ (B : Pre) (X : PreX B) (S₀ S₁ S₂ : Finset ℂ), (∀ z ∈ S₀, IsAlgebraic ℚ z) → (∀ z ∈ S₁, IsAlgebraic ℚ z) → (∀ z ∈ S₂, IsAlgebraic ℚ z) → ∃ (B' : Base) (h : B'.toPre = B) (Ch : Chars B'.fields (B'.primes (h ▸ X)) B'.R.m), (B'.dat (h ▸ X) Ch).Ok ∧ (∀ z ∈ S₀, ∃ x ∈ B'.Ks, B'.embLL x = z) ∧ (∀ z ∈ S₁, ∃ x ∈ B'.LL0, B'.embLL x = z) ∧ ∀ z ∈ S₂, ∃ x : B'.LL, B'.embLL x = z := by
  classical
  intro B X S₀ S₁ S₂ h₀ h₁ h₂
  obtain ⟨M, hM, hmu, η, hη, hηM⟩ := exists_value_field B.host (typePlaces B X) (fun j τ => (B.hc τ).e j)
    (fun j τ => (B.hc τ).e_int j)
  obtain ⟨α, hα, hgen⟩ := exists_gen M
  obtain ⟨B', rfl, k₀, k₁, k₂⟩ := GlobalTheory.Mem.BaseExt.exists_base B (insert α S₀) S₁ S₂
    (fun z hz => by
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hα
      · exact h₀ z hz) h₁ h₂
  have hin : ∀ z ∈ M, ∃ x, B'.embLL x = z := hgen B'.LL B'.embLL (by
    obtain ⟨x, -, hx⟩ := k₀ α (Finset.mem_insert_self _ _)
    exact ⟨x, hx⟩)
  have hP := (GlobalTheory.BasePrimes.primes_ok B' X).1
  obtain ⟨C, hC, -⟩ := GlobalTheory.T.exists_characters_prescribed_values B' X 1 1
  have hex : ∀ j : Fin B'.R.m, ∃ χ, IsAnti B'.host (typePlaces B'.toPre X) (fun τ => (B'.hc τ).e j)
      (fun w => (Units.map (B'.embLL : B'.LL →* ℂ)).comp (C.chi j w)⁻¹) χ ∧
      ∀ v, χ.UnrAt v → ((χ.val v : ℂˣ) : ℂ) ∈ M := fun j => by
    refine hmu j _ (exists_isAnti _ _ _ _ ?_ ?_ (X.e_even j) ?_)
    · intro w hw
      obtain ⟨i, hi⟩ := (mem_vGs (Pr := B'.primes X) w).1 hw
      exact ⟨i, g_mem_of_mem_vG hP hi⟩
    · intro w hw w' hcj
      obtain ⟨i, hi⟩ := (mem_vGs (Pr := B'.primes X) w).1 hw
      refine not_mem_vGs hP (i := i) ((mem_iff_of_conjPl B'.host hcj ?_).1 ((mem_vG hP i w).1 hi))
      have := B'.fields_conjO_coe (B'.fields.conjO (X.piG i))
      rw [Fields.conjO_invol] at this
      exact this.symm
    · intro ζ hζ
      have := prod_chi_root B' X hC j ζ hζ
      simp only [MonoidHom.comp_apply, MonoidHom.inv_apply]
      rw [← map_prod, Finset.prod_inv_distrib]
      erw [this]
      rw [inv_one, map_one]
  choose mu hmu1 hmu2 using hex
  obtain ⟨u, hu⟩ := exists_units_lift B'.embLL
    (fun p : Fin B'.R.m × HeightOneSpectrum (𝓞 B'.host.E) => (((mu p.1).val p.2 : ℂˣ) : ℂ)) (fun p => Units.ne_zero _)
  obtain ⟨u', hu'⟩ := exists_units_lift B'.embLL (fun v => η.valTw (1 / 2) v) (fun v => by
    refine mul_ne_zero (Units.ne_zero _) ?_
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    left
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot))
  have hemb : B'.fields.embC B'.embLL = embPsi B'.host := funext B'.fields_embC
  let Ch : Chars B'.fields (B'.primes X) B'.R.m := ⟨C.psi0, C.chi, fun j v => u (j, v), u'⟩
  refine ⟨B', rfl, Ch, GlobalTheory.T.definiteBaseData_admissible B' X Ch ⟨hC.1, hC.2, hC.3, hC.4, hC.5⟩ ⟨mu, η, fun j => ?_, fun j v hv => ?_, ?_, fun v => ?_⟩,
    fun z hz => k₀ z (Finset.mem_insert_of_mem hz), k₁, k₂⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hmu1 j
    refine ⟨a1, a2, ?_, a4, a5, fun w x y c hx hc => ?_⟩
    · rw [hemb]; exact a3
    · exact congrArg Units.val (a6 w x y c hx hc)
  · exact hu (j, v) (hin _ (hmu2 j v ((hmu1 j).2.2.2.1 v hv)))
  · refine ⟨hη.unitary, hη.unr, hη.res, ?_⟩
    rw [hemb]; exact hη.inf
  · exact hu' v (hin _ (hηM v))

end GlobalTheory.Mem.DatHecke

end
