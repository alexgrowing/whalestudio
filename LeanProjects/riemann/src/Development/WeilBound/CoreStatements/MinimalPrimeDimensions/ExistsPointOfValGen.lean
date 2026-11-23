import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsPointOfVal
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmallFin

namespace ChowFormHeightComparison₂.RegularPointExistence

theorem exists_point_of_val_gen {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (la : HeightOneSpectrum (𝓞 K)) {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (ν : Valuation Ω Γ)
    (h2 : ∀ a ∈ la.asIdeal, ν (algebraMap K Ω (a : K)) < 1)
    (A : Subalgebra (𝓞 K) Ω) [Algebra.FiniteType (𝓞 K) A] (hA : ∀ a ∈ A, ν a ≤ 1) {t : A} (ht : t ≠ 0) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (O : ValuationSubring L) (φ : A →+* O),
      (∀ a : 𝓞 K, ((φ (algebraMap (𝓞 K) A a) : O) : L) = algebraMap K L (a : K)) ∧
      (∀ s : A, ν (s : Ω) < 1 → ((φ s : O) : L) ∈ O.nonunits) ∧ φ t ≠ 0 := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing (𝓞 K) A
  have hcoe : ∀ a : 𝓞 K, ((algebraMap (𝓞 K) A a : A) : Ω) = algebraMap K Ω (a : K) := fun a => rfl
  have hinj : Function.Injective (algebraMap (𝓞 K) A) := fun a b hab => by
    have : algebraMap K Ω (a : K) = algebraMap K Ω (b : K) := by
      rw [← hcoe, ← hcoe, hab]
    exact RingOfIntegers.ext ((algebraMap K Ω).injective this)
  let P : Ideal A :=
    { carrier := {a | ν (a : Ω) < 1}
      add_mem' := fun {a b} ha hb => ν.map_add_lt ha hb
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        show ν ((c : Ω) * (x : Ω)) < 1
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hA _ c.2)) hx }
  have hP : P ≠ ⊤ := fun h => by
    have : (1 : A) ∈ P := h ▸ Submodule.mem_top
    have h1 : ν ((1 : A) : Ω) < 1 := this
    simp at h1
  obtain ⟨m, hm, hPm⟩ := Ideal.exists_le_maximal P hP
  obtain ⟨π, hπla, hπ⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la.ne_bot
  have hπm : algebraMap (𝓞 K) A π ∈ m := hPm (h2 π hπla)
  have hπ' : algebraMap (𝓞 K) A π ≠ 0 := fun h => hπ (hinj (h.trans (map_zero _).symm))
  obtain ⟨q, hqU, hqm, hht⟩ := exists_mem_height_map_le_one m
    (PrimeSpectrum.basicOpen (algebraMap (𝓞 K) A π * t)).isOpen ⟨⊥, mul_ne_zero hπ' ht, bot_le⟩
  have hqπ : algebraMap (𝓞 K) A π ∉ q.asIdeal := fun h => hqU (Ideal.mul_mem_right _ _ h)
  have hqt : t ∉ q.asIdeal := fun h => hqU (Ideal.mul_mem_left _ _ h)
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have hcomap : (m.map (Ideal.Quotient.mk q.asIdeal)).comap (Ideal.Quotient.mk q.asIdeal) = m := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hqm
  have : (m.map (Ideal.Quotient.mk q.asIdeal)).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hm).resolve_left fun e => by
      rw [e, Ideal.comap_top] at hcomap
      exact hm.ne_top hcomap.symm
  have hlaM : la.asIdeal ≤ m.comap (algebraMap (𝓞 K) A) := fun a ha => hPm (h2 a ha)
  have hmax : (m.comap (algebraMap (𝓞 K) A)) = la.asIdeal :=
    (la.isMaximal.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hlaM).symm
  have hinj' : Function.Injective (algebraMap (𝓞 K) (A ⧸ q.asIdeal)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    have h1 : a ∈ q.asIdeal.comap (algebraMap (𝓞 K) A) :=
      (Ideal.Quotient.eq_zero_iff_mem (I := q.asIdeal) (a := algebraMap (𝓞 K) A a)).mp ha
    have h2' : (q.asIdeal.comap (algebraMap (𝓞 K) A)).IsMaximal :=
      Ideal.IsPrime.isMaximal inferInstance fun h => ha0 (by simpa [h] using h1)
    have h3 := h2'.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (Ideal.comap_mono hqm)
    exact hqπ (by
      have : π ∈ q.asIdeal.comap (algebraMap (𝓞 K) A) := by
        rw [h3]
        exact hπm
      exact this)
  obtain ⟨L, _, _, _, O, φ, hφ, hφi, hφm⟩ := exists_valuationSubring_of_height_le_one (K := K)
    hinj' (m.map (Ideal.Quotient.mk q.asIdeal)) hht π hπ (Ideal.mem_map_of_mem _ hπm)
  have nL : NumberField L := NumberField.of_module_finite K L
  refine ⟨L, _, nL, _, O, φ.comp (Ideal.Quotient.mk _), fun a => hφ a, fun s hs => ?_, fun h => hqt ?_⟩
  · have h1 : Ideal.Quotient.mk q.asIdeal s ∈ m.map (Ideal.Quotient.mk q.asIdeal) := Ideal.mem_map_of_mem _ (hPm hs)
    rw [← hφm, Ideal.mem_comap] at h1
    exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.2 ⟨(φ _).2, h1⟩
  · have : φ (Ideal.Quotient.mk _ t) = 0 := h
    exact Ideal.Quotient.eq_zero_iff_mem.1 ((map_eq_zero_iff φ hφi).1 this)

set_option maxHeartbeats 1000000 in

theorem exists_cdvr_point_gen {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (la : HeightOneSpectrum (𝓞 K)) {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (ν : Valuation Ω Γ)
    (h1 : ∀ a : 𝓞 K, ν (algebraMap K Ω (a : K)) ≤ 1)
    (h2 : ∀ a ∈ la.asIdeal, ν (algebraMap K Ω (a : K)) < 1)
    (Gn W N : Finset Ω) (hG : ∀ g ∈ Gn, ν g ≤ 1)
    (hgen : IntermediateField.adjoin K (Gn : Set Ω) = ⊤) (hN : ∀ x ∈ N, x ≠ 0) :
    ∃ (T : CDVR) (io : K →+* T.Fr) (e : ℕ) (_ : OverLa la T.V io e) (_ : T.FinRes)
      (S : Subalgebra K Ω) (ρ : S →+* T.Fr),
      (∀ a : K, ρ (algebraMap K S a) = io a) ∧ (∀ x ∈ Gn, x ∈ S) ∧ (∀ x ∈ W, x ∈ S) ∧ (∀ x ∈ N, x ∈ S) ∧
      (∀ x : S, (x : Ω) ∈ N → ρ x ≠ 0) ∧ (∀ x : S, (x : Ω) ∈ Gn → 0 ≤ vV T.V (ρ x)) ∧
      (∀ x : S, (x : Ω) ∈ Gn → ν x < 1 → ρ x ≠ 0 → 0 < vV T.V (ρ x)) := by
  classical
  let A : Subalgebra (𝓞 K) Ω := Algebra.adjoin (𝓞 K) (Gn : Set Ω)
  have : Algebra.FiniteType (𝓞 K) A := (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_adjoin_finset Gn)
  have hA : ∀ a ∈ A, ν a ≤ 1 := fun a ha => by
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact hG x hx
    | algebraMap r => exact h1 r
    | add x y _ _ hx hy => exact (ν.map_add x y).trans (max_le hx hy)
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact mul_le_one' hx hy
  have hKA : ∀ a : 𝓞 K, algebraMap K Ω (a : K) ∈ A := fun a => A.algebraMap_mem a
  have hfrac : ∀ x : Ω, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ x * b = a := fun x => by
    have hx : x ∈ IntermediateField.adjoin K (Gn : Set Ω) := hgen ▸ IntermediateField.mem_top
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx => exact ⟨x, Algebra.subset_adjoin hx, 1, A.one_mem, one_ne_zero, mul_one x⟩
    | algebraMap a =>
      obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
      have hq0 : algebraMap K Ω (algebraMap (𝓞 K) K q) ≠ 0 :=
        (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.ne_zero hq))
      refine ⟨_, hKA p, _, hKA q, hq0, ?_⟩
      rw [map_div₀]
      exact div_mul_cancel₀ _ hq0
    | add x y _ _ ihx ihy =>
      obtain ⟨a, ha, b, hb, hb0, e⟩ := ihx
      obtain ⟨a', ha', b', hb', hb0', e'⟩ := ihy
      refine ⟨a * b' + a' * b, A.add_mem (A.mul_mem ha hb') (A.mul_mem ha' hb), b * b', A.mul_mem hb hb',
        mul_ne_zero hb0 hb0', ?_⟩
      rw [← e, ← e']
      ring
    | mul x y _ _ ihx ihy =>
      obtain ⟨a, ha, b, hb, hb0, e⟩ := ihx
      obtain ⟨a', ha', b', hb', hb0', e'⟩ := ihy
      refine ⟨a * a', A.mul_mem ha ha', b * b', A.mul_mem hb hb', mul_ne_zero hb0 hb0', ?_⟩
      rw [← e, ← e']
      ring
    | inv x _ ih =>
      obtain ⟨a, ha, b, hb, hb0, e⟩ := ih
      by_cases hx0 : x = 0
      · exact ⟨0, A.zero_mem, 1, A.one_mem, one_ne_zero, by simp [hx0]⟩
      · refine ⟨b, hb, a, ha, ?_, ?_⟩
        · rw [← e]
          exact mul_ne_zero hx0 hb0
        · rw [← e]
          field_simp
  choose fa hfa fb hfb hb0 hxb using hfrac
  let t : A := (∏ x ∈ W ∪ N, (⟨fb x, hfb x⟩ : A)) * ∏ x ∈ N, (⟨fa x, hfa x⟩ : A)
  have hfa0 : ∀ x ∈ N, (⟨fa x, hfa x⟩ : A) ≠ 0 := fun x hx h => by
    have h0 : fa x = 0 := congrArg Subtype.val h
    rw [← hxb x] at h0
    exact mul_ne_zero (hN x hx) (hb0 x) h0
  have ht : t ≠ 0 := mul_ne_zero
    (Finset.prod_ne_zero_iff.2 fun x _ h => hb0 x (congrArg Subtype.val h))
    (Finset.prod_ne_zero_iff.2 hfa0)
  obtain ⟨L, _, nL, _, O, φ, hφ, hφm, hφt⟩ := exists_point_of_val_gen la ν h2 A hA ht
  have hcoeL : ∀ a : 𝓞 K, ((algebraMap (𝓞 K) (𝓞 L) a : 𝓞 L) : L) = algebraMap K L (a : K) := fun a => rfl
  obtain ⟨π, hπla, hπ⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la.ne_bot
  have hOnon : ∀ a ∈ la.asIdeal, algebraMap K L (a : K) ∈ O.nonunits := fun a ha => by
    rw [← hφ a]
    exact hφm _ (h2 a ha)
  have hx0 : algebraMap (𝓞 K) (𝓞 L) π ≠ 0 := fun h => by
    have h3 : algebraMap K L (π : K) = 0 := by rw [← hcoeL, h]; rfl
    exact hπ (RingOfIntegers.ext ((map_eq_zero _).1 h3))
  obtain ⟨w, hw⟩ := exists_prime_eq O (algebraMap (𝓞 K) (𝓞 L) π) hx0 (hOnon π hπla)
  have memO : ∀ x : L, x ∈ O ↔ w.valuation L x ≤ 1 := fun x => by
    rw [← hw]
    exact GlobalTheory.PlaceCompletion.mem_atPrime_iff w x
  have nonU : ∀ x : L, x ∈ O.nonunits → w.valuation L x < 1 := fun x hx => by
    rcases (ValuationSubring.mem_nonunits_iff_or O).1 hx with h0 | h0
    · simp [h0]
    · rw [memO, map_inv₀, not_le] at h0
      have hne : x ≠ 0 := fun h => by simp [h] at h0
      exact (one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hne))).1 h0
  have hlies : w.asIdeal.LiesOver la.asIdeal := ⟨by
    have hle : la.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) := fun a ha => by
      rw [Ideal.mem_comap, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L)]
      exact nonU _ (hOnon a ha)
    exact la.isMaximal.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle⟩
  have : Finite (𝓞 L ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  have : CharZero (HeightOneSpectrum.adicCompletionIntegers L w) :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective (𝓞 L) (HeightOneSpectrum.adicCompletionIntegers L w))
  obtain ⟨e1, he1, h1e⟩ := GlobalTheory.AdicCompl.exists_e (L := L) w
  let T : CDVR := { V := HeightOneSpectrum.adicCompletionIntegers L w, cpl := GlobalTheory.AdicCompl.isAdicComplete w }
  let k : L →+* T.Fr := GlobalTheory.AdicCompl.kMap w
  have hvk : ∀ x : L, vV T.V (k x) = (e1 : ℤ) * vLa w x := fun x => by
    show vV (HeightOneSpectrum.adicCompletionIntegers L w) (GlobalTheory.AdicCompl.kMap w x) = _
    simp only [vV, vLa]
    rw [h1e, WithZero.log_pow]
    simp
  have he2 : la.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal la.ne_bot
  have ho : OverLa la T.V (k.comp (algebraMap K L)) (la.asIdeal.ramificationIdx' w.asIdeal * e1) := by
    refine ⟨Nat.mul_pos (Nat.pos_of_ne_zero he2) he1, fun a => ?_⟩
    show vV (HeightOneSpectrum.adicCompletionIntegers L w) (GlobalTheory.AdicCompl.kMap w (algebraMap K L a)) = _
    simp only [vV, vLa]
    rw [h1e, ← HeightOneSpectrum.valuation_liesOver L la w a, ← pow_mul, WithZero.log_pow]
    push_cast
    simp
  have hfin : T.FinRes := GlobalTheory.AdicCompl.finite_res w
  let g : A →+* T.Fr := (k.comp O.subtype).comp φ
  have hg : ∀ a : A, g a = k (φ a : O) := fun _ => rfl
  have hfg : IsFractionRing A Ω := IsFractionRing.of_field A Ω fun z =>
    ⟨⟨fa z, hfa z⟩, ⟨fb z, hfb z⟩, by
      show z = fa z / fb z
      rw [← hxb z, mul_div_cancel_right₀ _ (hb0 z)]⟩
  let P₀ : Ideal A := RingHom.ker g
  have hP₀ : P₀.IsPrime := RingHom.ker_isPrime g
  have hM : P₀.primeCompl ≤ nonZeroDivisors A := P₀.primeCompl_le_nonZeroDivisors
  let S₀ : Subalgebra A Ω := Localization.subalgebra.ofField Ω P₀.primeCompl hM
  haveI : IsLocalization P₀.primeCompl S₀ := Localization.subalgebra.isLocalization_ofField Ω P₀.primeCompl hM
  let ρ₀ : S₀ →+* T.Fr := IsLocalization.lift (M := P₀.primeCompl) (g := g) fun y =>
    isUnit_iff_ne_zero.2 fun h => y.2 h
  have hρ₀ : ∀ a : A, ρ₀ (algebraMap A S₀ a) = g a := fun a => IsLocalization.lift_eq _ a
  have memS₀ : ∀ (x : Ω) (a b : A), g b ≠ 0 → x * b = a → x ∈ S₀ := fun x a b hb e => by
    have hb0' : (b : Ω) ≠ 0 := fun h => hb (by
      have : b = 0 := Subtype.ext h
      rw [this, map_zero])
    have hx : x = algebraMap A Ω a * (algebraMap A Ω b)⁻¹ := by
      show x = (a : Ω) * (b : Ω)⁻¹
      rw [← e, mul_inv_cancel_right₀ hb0']
    exact ⟨a, b, fun h => hb h, hx⟩
  have hAS : ∀ a : A, (a : Ω) ∈ S₀ := fun a => memS₀ _ a 1 (by rw [map_one]; exact one_ne_zero) (by simp)
  have hKS : ∀ a : K, algebraMap K Ω a ∈ S₀ := fun a => by
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
    have hq0 : (algebraMap (𝓞 K) K q) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.ne_zero hq)
    refine memS₀ _ (algebraMap (𝓞 K) A p) (algebraMap (𝓞 K) A q) ?_ ?_
    · rw [hg, hφ q]
      exact (map_ne_zero k).2 ((map_ne_zero _).2 hq0)
    · change algebraMap K Ω (algebraMap (𝓞 K) K p / algebraMap (𝓞 K) K q) * algebraMap K Ω (algebraMap (𝓞 K) K q) =
        algebraMap K Ω (algebraMap (𝓞 K) K p)
      rw [← map_mul, div_mul_cancel₀ _ hq0]
  let S : Subalgebra K Ω := { S₀.toSubsemiring with algebraMap_mem' := hKS }
  let ι : S →+* S₀ :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let ρ : S →+* T.Fr := ρ₀.comp ι
  have hρA : ∀ (x : S) (a : A), (x : Ω) = a → ρ x = g a := fun x a e => by
    have h3 : ι x = algebraMap A S₀ a := Subtype.ext e
    show ρ₀ (ι x) = _
    rw [h3, hρ₀]
  have hρM : ∀ (x : S) (a b : A), (x : Ω) * b = a → ρ x * g b = g a := fun x a b e => by
    have h3 : ι x * algebraMap A S₀ b = algebraMap A S₀ a := Subtype.ext e
    have h4 := congrArg ρ₀ h3
    rwa [map_mul, hρ₀, hρ₀] at h4
  have hgt : g t ≠ 0 := by
    rw [hg]
    exact (map_ne_zero k).2 fun h => hφt (Subtype.ext h)
  have hgt' := hgt
  rw [map_mul, map_prod, map_prod] at hgt'
  have hWN : ∀ x ∈ W ∪ N, g ⟨fb x, hfb x⟩ ≠ 0 := fun x hx =>
    Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hgt') x hx
  have hgfa : ∀ x ∈ N, g ⟨fa x, hfa x⟩ ≠ 0 := fun x hx =>
    Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hgt') x hx
  have hvL : ∀ y : L, y ∈ O → 0 ≤ vLa w y := fun y hy => by
    by_cases hy0 : y = 0
    · simp [vLa, hy0]
    · have h3 := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 hy0) one_ne_zero).2 ((memO y).1 hy)
      rw [WithZero.log_one] at h3
      simp only [vLa]
      omega
  have hvL' : ∀ y : L, y ∈ O.nonunits → y ≠ 0 → 0 < vLa w y := fun y hy hy0 => by
    have h3 := (WithZero.log_lt_log ((Valuation.ne_zero_iff _).2 hy0) one_ne_zero).2 (nonU y hy)
    rw [WithZero.log_one] at h3
    simp only [vLa]
    omega
  have hGS : ∀ x ∈ Gn, x ∈ A := fun x hx => Algebra.subset_adjoin hx
  refine ⟨T, k.comp (algebraMap K L), _, ho, hfin, S, ρ, fun a => ?_, fun x hx => hAS ⟨x, hGS x hx⟩,
    fun x hx => memS₀ x ⟨fa x, hfa x⟩ ⟨fb x, hfb x⟩ (hWN x (Finset.mem_union_left _ hx)) (hxb x),
    fun x hx => memS₀ x ⟨fa x, hfa x⟩ ⟨fb x, hfb x⟩ (hWN x (Finset.mem_union_right _ hx)) (hxb x),
    fun x hx h0 => hgfa x hx ?_, fun x hx => ?_, fun x hx hν h0 => ?_⟩
  · obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
    have hq0 : (algebraMap (𝓞 K) K q) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.ne_zero hq)
    have h3 := hρM (algebraMap K S (algebraMap (𝓞 K) K p / algebraMap (𝓞 K) K q)) (algebraMap (𝓞 K) A p)
      (algebraMap (𝓞 K) A q) (by
        change algebraMap K Ω (algebraMap (𝓞 K) K p / algebraMap (𝓞 K) K q) * algebraMap K Ω (algebraMap (𝓞 K) K q) =
          algebraMap K Ω (algebraMap (𝓞 K) K p)
        rw [← map_mul, div_mul_cancel₀ _ hq0])
    rw [hg, hg, hφ q, hφ p] at h3
    have hk0 : k (algebraMap K L (algebraMap (𝓞 K) K q)) ≠ 0 := (map_ne_zero k).2 ((map_ne_zero _).2 hq0)
    show _ = k (algebraMap K L (algebraMap (𝓞 K) K p / algebraMap (𝓞 K) K q))
    rw [map_div₀ (algebraMap K L), map_div₀ k]
    exact eq_div_of_mul_eq hk0 h3
  · have h3 := hρM x ⟨fa x, hfa x⟩ ⟨fb x, hfb x⟩ (hxb x)
    rw [h0, zero_mul] at h3
    exact h3.symm
  · rw [hρA x ⟨x, hGS x hx⟩ rfl, hg, hvk]
    exact mul_nonneg (Int.natCast_nonneg _) (hvL _ (φ _).2)
  · have hρ := hρA x ⟨x, hGS x hx⟩ rfl
    rw [hρ, hg] at h0 ⊢
    rw [hvk]
    have hy0 : ((φ ⟨x, hGS x hx⟩ : O) : L) ≠ 0 := fun h => h0 (by rw [h, map_zero])
    exact mul_pos (by exact_mod_cast he1) (hvL' _ (hφm ⟨x, hGS x hx⟩ hν) hy0)

end ChowFormHeightComparison₂.RegularPointExistence
