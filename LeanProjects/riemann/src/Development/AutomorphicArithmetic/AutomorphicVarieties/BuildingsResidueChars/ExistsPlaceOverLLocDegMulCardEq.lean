import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open scoped Pointwise

private theorem td_move {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A B : ValuationSubring Ω}
    (g : G F Ω) (hg : ∀ x, g x ∈ A ↔ x ∈ B) {w : HeightOneSpectrum (𝓞 F)} (hw : IsPlaceOver A w) :
    IsPlaceOver B w := by
  intro x
  rw [← hw x, valuation_lt_one_iff', valuation_lt_one_iff']
  have hy : g (algebraMap F Ω x) = algebraMap F Ω x := g.commutes _
  have hyi : g (algebraMap F Ω x)⁻¹ = (algebraMap F Ω x)⁻¹ := by rw [map_inv₀, hy]
  rw [← hg (algebraMap F Ω x), hy, ← hg (algebraMap F Ω x)⁻¹, hyi]

private theorem td_count (l : ℕ) [hl : Fact l.Prime] (F : Type) [Field F] [NumberField F] [IsGalois ℚ F] {V : Type}
    (pl : V → HeightOneSpectrum (𝓞 F)) (hi : Function.Injective pl) (hm : ∀ v, ((l : ℕ) : 𝓞 F) ∈ (pl v).asIdeal)
    (hs : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ v, pl v = w) (v : V) :
    locDeg (pl v) * Nat.card V = Module.finrank ℚ F := by
  classical
  let p : Ideal ℤ := Ideal.span {((l : ℕ) : ℤ)}
  have hpp : p.IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl.out)
  haveI hpmax : p.IsMaximal :=
    hpp.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.out.ne_zero)
  have hlo : ∀ P : Ideal (𝓞 F), P.IsPrime → ((l : ℕ) : 𝓞 F) ∈ P → P.LiesOver p := by
    intro P hP hlP
    constructor
    apply hpmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top)
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 F) ((l : ℕ) : ℤ) ∈ P
    rwa [map_natCast]
  let f : V → p.primesOver (𝓞 F) := fun u =>
    ⟨(pl u).asIdeal, (pl u).isPrime, hlo _ (pl u).isPrime (hm u)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      apply hi
      exact HeightOneSpectrum.ext (congrArg Subtype.val h)
    · rintro ⟨P, hP, hPl⟩
      have hlP : ((l : ℕ) : 𝓞 F) ∈ P := by
        have hm' : ((l : ℕ) : ℤ) ∈ p := Ideal.subset_span (Set.mem_singleton _)
        rw [hPl.over] at hm'
        have hm'' := Ideal.mem_comap.1 hm'
        rwa [map_natCast] at hm''
      have hne : P ≠ ⊥ := by
        intro h
        rw [h, Ideal.mem_bot] at hlP
        exact hl.out.ne_zero (by exact_mod_cast hlP)
      obtain ⟨u, hu⟩ := hs ⟨P, hP, hne⟩ hlP
      exact ⟨u, Subtype.ext (congrArg HeightOneSpectrum.asIdeal hu)⟩
  have key : (p.primesOver (𝓞 F)).ncard = Nat.card V := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_eq_of_bijective f hf).symm
  have hG := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p (𝓞 F) (F ≃ₐ[ℚ] F)
  haveI := hlo _ (pl v).isPrime (hm v)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p (pl v).asIdeal (F ≃ₐ[ℚ] F),
    Ideal.inertiaDegIn_eq_inertiaDeg p (pl v).asIdeal (F ≃ₐ[ℚ] F), key,
    IsGalois.card_aut_eq_finrank] at hG
  rw [← hG, mul_comm]
  rfl

theorem UpperTheory.exists_place_over_l_locDeg_mul_card_eq :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (v : T.ι), ∃ w : HeightOneSpectrum (𝓞 T.F), IsPlaceOver (T.pl v) w ∧ ((l : ℕ) : 𝓞 T.F) ∈ w.asIdeal ∧ locDeg w * Nat.card T.ι = T.d := by
  intro Ω _ _ _ l _ c D T v
  haveI := T.nF
  haveI := T.abF
  haveI hac : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  have hlt : ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 T.F)), IsPlaceOver A w →
      (A.valuation (l : Ω) < 1 ↔ ((l : ℕ) : 𝓞 T.F) ∈ w.asIdeal) := by
    intro A w hA
    rw [← hA]
    simp
  choose P hPS hP using fun u => GlobalTheory.DecLocal.exists_place_below (p := l) (F := T.F) (T.pl u) (T.ovl u)
  have hPl : ∀ u, ((l : ℕ) : 𝓞 T.F) ∈ (P u).asIdeal := fun u => hPS u
  refine ⟨P v, hP v, hPl v, td_count l T.F P ?_ hPl ?_ v⟩
  · intro u u' h
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hP u) (by rw [h]; exact hP u')
    obtain ⟨v0, -, huniq⟩ := T.cover (T.pl u) (T.ovl u)
    have e1 := huniq u ⟨1, fun x => by simp⟩
    have e2 := huniq u' ⟨σ⁻¹, fun x => by
      rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]⟩
    exact e1.trans e2.symm
  · intro w hw
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨u, ⟨g, hg⟩, -⟩ := T.cover A ((hlt A w hA).2 hw)
    exact ⟨u, eq_of_isPlaceOver (hP u) (td_move g hg hA)⟩
