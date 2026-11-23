import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPlaceOfNeZeroMaximalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularOfValuationBoundedAtPoints
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem exists_loc {F' : Type} [Field F'] [NumberField F'] (O : ValuationSubring F') (x : 𝓞 F') (hx : x ≠ 0)
    (y : O) (hy : y ∈ maximalIdeal O) (hxy : (y : F') = (x : F')) :
    ∃ c : 𝓞 F' →+* O, ((maximalIdeal O).comap c).IsMaximal ∧
      ∀ o : O, ∃ a s : 𝓞 F', s ∉ (maximalIdeal O).comap c ∧ o * c s = c a := by
  have hmem : ∀ a : 𝓞 F', (algebraMap (𝓞 F') F') a ∈ O := by
    intro a
    have h1 : IsIntegral O (algebraMap (𝓞 F') F' a) := (RingOfIntegers.isIntegral_coe a).tower_top
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
    rw [← hz]
    exact z.2
  let c : 𝓞 F' →+* O := (algebraMap (𝓞 F') F').codRestrict O hmem
  have hc : ∀ a, ((c a : O) : F') = algebraMap (𝓞 F') F' a := fun _ => rfl
  have hprime : ((maximalIdeal O).comap c).IsPrime := Ideal.comap_isPrime _ _
  have hne : (maximalIdeal O).comap c ≠ ⊥ := by
    intro h
    have : x ∈ (maximalIdeal O).comap c := by
      have : c x = y := Subtype.ext hxy.symm
      rw [Ideal.mem_comap, this]
      exact hy
    rw [h] at this
    exact hx this
  refine ⟨c, hprime.isMaximal hne, fun o => ?_⟩
  let P : HeightOneSpectrum (𝓞 F') := ⟨_, hprime, hne⟩
  by_cases e0 : (o : F') = 0
  · exact ⟨0, 1, fun h => hprime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
      rw [show o = 0 from Subtype.ext e0]; simp⟩
  have hS := P.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsLocalization P.asIdeal.primeCompl (P.valuationSubringAtPrime F') :=
    Localization.subalgebra.isLocalization_ofField F' _ hS
  rcases (P.valuationSubringAtPrime F').mem_or_inv_mem (o : F') with h | h
  · obtain ⟨⟨r, s⟩, hh⟩ := IsLocalization.surj P.asIdeal.primeCompl (⟨o, h⟩ : P.valuationSubringAtPrime F')
    have h2 : (o : F') * algebraMap (𝓞 F') F' s = algebraMap (𝓞 F') F' r := congrArg Subtype.val hh
    exact ⟨r, s, s.2, Subtype.ext h2⟩
  · obtain ⟨⟨r, s⟩, hh⟩ := IsLocalization.surj P.asIdeal.primeCompl (⟨(o : F')⁻¹, h⟩ : P.valuationSubringAtPrime F')
    have h2 : (o : F')⁻¹ * algebraMap (𝓞 F') F' s = algebraMap (𝓞 F') F' r := congrArg Subtype.val hh
    have h3 : o * c r = c s := Subtype.ext (by
      change (o : F') * algebraMap (𝓞 F') F' r = algebraMap (𝓞 F') F' s
      rw [← h2, ← mul_assoc, mul_inv_cancel₀ e0, one_mul])
    refine ⟨s, r, fun hr => s.2 ?_, h3⟩
    change c s ∈ maximalIdeal O
    rw [← h3]
    exact Ideal.mul_mem_left _ _ hr

theorem UpperTheory.finiteType_domain_extension_point :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (F' : Type) [Field F'] [NumberField F'] (ε : F →+* F') (O : ValuationSubring F') [IsDiscreteValuationRing O] (b : 𝓞 F →+* O), IsUp v ε O b → ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra O R] [Algebra.FiniteType O R] [CharZero R] (𝔫 : Ideal R), 𝔫 ≠ ⊤ → (∀ a ∈ maximalIdeal O, algebraMap O R a ∈ 𝔫) → ∀ g : R, g ≠ 0 → ∃ (e : TrueGeo.Ext v) (φ : R →+* e.O), (∀ a : 𝓞 F, ((φ (algebraMap O R (b a)) : e.O) : AlgebraicClosure F) = algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a)) ∧ (∀ r ∈ 𝔫, e.w ((φ r : e.O) : AlgebraicClosure F) < 1) ∧ φ g ≠ 0 := by
  intro F _ _ v F' _ _ ε O _ b hup R _ _ _ hft _ 𝔫 hn hmn g hg
  obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hx1 : RingOfIntegers.mapRingHom ε x ≠ 0 := by
    intro h
    have h1 : ε (x : F) = 0 := congrArg (fun t : 𝓞 F' => (t : F')) h
    rw [map_eq_zero] at h1
    exact hx0 (RingOfIntegers.coe_eq_zero_iff.1 h1)
  obtain ⟨c, hP, hloc⟩ := exists_loc O _ hx1 (b x) ((hup.2 x).1 hxv) (hup.1 x)
  letI : Algebra (𝓞 F) R := ((algebraMap O R).comp b).toAlgebra
  obtain ⟨S, hS⟩ := hft.out
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := ℤ) (M := 𝓞 F')
  let d : 𝓞 F' →+* R := (algebraMap O R).comp c
  let R0 : Subalgebra (𝓞 F) R := Algebra.adjoin (𝓞 F) ((S ∪ T.image d : Finset R) : Set R)
  have hft0 : Algebra.FiniteType (𝓞 F) R0 := (Subalgebra.fg_iff_finiteType _).1 ⟨_, rfl⟩
  have hd : ∀ a, d a ∈ R0 := by
    intro a
    have ha : a ∈ Submodule.span ℤ (T : Set (𝓞 F')) := hT ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem t ht => exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht)))
    | zero => rw [map_zero]; exact zero_mem _
    | add s t _ _ hs ht => rw [map_add]; exact add_mem hs ht
    | smul n t _ ht => rw [map_zsmul]; exact zsmul_mem ht n
  let d0 : 𝓞 F' →+* R0 := d.codRestrict R0 hd
  have hn0 : 𝔫.comap R0.val.toRingHom ≠ ⊤ := Ideal.comap_ne_top _ hn
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hn0
  have hPm : (maximalIdeal O).comap c = 𝔪.comap d0 :=
    hP.eq_of_le (Ideal.comap_ne_top _ h𝔪.ne_top) fun a ha => hle (hmn _ ha)
  have hsurj : ∀ r : R, ∃ s : 𝓞 F', s ∉ (maximalIdeal O).comap c ∧ r * d s ∈ R0 := by
    intro r
    have h1 : (1 : 𝓞 F') ∉ (maximalIdeal O).comap c := fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
    have hr : r ∈ Algebra.adjoin O (S : Set R) := hS ▸ Algebra.mem_top
    induction hr using Algebra.adjoin_induction with
    | mem t ht =>
      exact ⟨1, h1, by
        rw [map_one, mul_one]
        exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_left _ ht))⟩
    | algebraMap o =>
      obtain ⟨a, s, hs, h⟩ := hloc o
      refine ⟨s, hs, ?_⟩
      have : algebraMap O R o * d s = d a := by
        change algebraMap O R o * algebraMap O R (c s) = algebraMap O R (c a)
        rw [← map_mul, h]
      rw [this]
      exact hd a
    | add p q _ _ hp hq =>
      obtain ⟨s, hs, h⟩ := hp
      obtain ⟨t, ht, h'⟩ := hq
      refine ⟨s * t, fun hst => (hP.isPrime.mem_or_mem hst).elim hs ht, ?_⟩
      have : (p + q) * d (s * t) = p * d s * d t + q * d t * d s := by rw [map_mul]; ring
      rw [this]
      exact add_mem (mul_mem h (hd t)) (mul_mem h' (hd s))
    | mul p q _ _ hp hq =>
      obtain ⟨s, hs, h⟩ := hp
      obtain ⟨t, ht, h'⟩ := hq
      refine ⟨s * t, fun hst => (hP.isPrime.mem_or_mem hst).elim hs ht, ?_⟩
      have : (p * q) * d (s * t) = p * d s * (q * d t) := by rw [map_mul]; ring
      rw [this]
      exact mul_mem h h'
  have hunit : ∀ s : 𝓞 F', s ∉ (maximalIdeal O).comap c → IsUnit (d s) := fun s hs =>
    (IsLocalRing.notMem_maximalIdeal.1 hs).map (algebraMap O R)
  haveI := h𝔪.isPrime
  let M : Submonoid R0 := 𝔪.primeCompl ⊓ (IsUnit.submonoid R).comap R0.val
  have hM : ∀ s : 𝓞 F', s ∉ (maximalIdeal O).comap c → d0 s ∈ M := fun s hs =>
    ⟨fun h => hs (hPm ▸ h), hunit s hs⟩
  haveI : IsLocalization M R := by
    rw [isLocalization_iff]
    refine ⟨fun y => y.2.2, fun r => ?_, fun {p q} h => ⟨1, by rw [Subtype.ext h]⟩⟩
    obtain ⟨s, hs, h⟩ := hsurj r
    exact ⟨⟨⟨_, h⟩, ⟨d0 s, hM s hs⟩⟩, rfl⟩
  obtain ⟨s, hs, hgs⟩ := hsurj g
  have hg0 : (⟨_, hgs⟩ : R0) ≠ 0 := fun h => mul_ne_zero hg (hunit s hs).ne_zero (congrArg Subtype.val h)
  obtain ⟨v', e, φ, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F R0 𝔪 h𝔪 _ hg0
  have hv : v = v' := by
    refine HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top fun a ha => ?_)
    have h₄ : algebraMap (𝓞 F) R0 a ∈ 𝔪 := hle (hmn _ ((hup.2 a).1 ha))
    rw [← h₂] at h₄
    by_contra hv
    refine (IsLocalRing.mem_maximalIdeal _).1 h₄ (GlobalTheory.TrueGeo.RegCrit.isUnit_of_one_le e _ ?_)
    rw [h₁ a, e.w_alg, ← FinitePlace.norm_embedding]
    exact ((FinitePlace.norm_eq_one_iff_notMem F v' a).2 hv).ge
  subst hv
  have hφ : ∀ y : M, IsUnit (φ y) := fun y => by
    refine IsLocalRing.notMem_maximalIdeal.1 fun h => y.2.1 ?_
    rw [← h₂]
    exact h
  have hl : ∀ y : R0, IsLocalization.lift (S := R) hφ (y : R) = φ y := fun y => IsLocalization.lift_eq hφ y
  refine ⟨e, IsLocalization.lift hφ, fun a => ?_, fun r hr => ?_, fun h => h₃ ?_⟩
  · rw [← h₁ a, ← hl]
    rfl
  · obtain ⟨t, ht, hrt⟩ := hsurj r
    by_contra hw
    have hu := GlobalTheory.TrueGeo.RegCrit.isUnit_of_one_le e _ (not_lt.1 hw)
    have h₄ : (⟨_, hrt⟩ : R0) ∈ 𝔪 := hle (Ideal.mul_mem_right _ _ hr)
    rw [← h₂] at h₄
    refine (IsLocalRing.mem_maximalIdeal _).1 h₄ ?_
    rw [← hl]
    change IsUnit (IsLocalization.lift (S := R) hφ (r * d t))
    rw [map_mul]
    exact hu.mul ((hunit t ht).map _)
  · rw [← hl]
    change IsLocalization.lift (S := R) hφ (g * d s) = 0
    rw [map_mul, h, zero_mul]
