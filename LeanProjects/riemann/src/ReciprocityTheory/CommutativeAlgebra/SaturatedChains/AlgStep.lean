import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain

namespace ReciprocityTheory.CA

open Polynomial

attribute [local instance] Polynomial.algebra Polynomial.isLocalization in

theorem height_le_one_of_comap_C_eq_bot {A : Type*} [CommRing A] [IsDomain A]
    (Q : Ideal A[X]) [Q.IsPrime] (hQ : Q.comap C = ⊥) : Q.height ≤ 1 := by

  have hd : Disjoint ((Submonoid.map (C : A →+* A[X]) (nonZeroDivisors A) : Submonoid A[X]) :
      Set A[X]) (Q : Set A[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsQ
    have h0 : s ∈ Q.comap C := hsQ
    rw [hQ, Ideal.mem_bot] at h0
    exact nonZeroDivisors.ne_zero hs h0
  haveI hQ' : (Q.map (algebraMap A[X] (FractionRing A)[X])).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ Q ‹Q.IsPrime› hd
  have hcomap := IsLocalization.comap_map_of_isPrime_disjoint
    (Submonoid.map (C : A →+* A[X]) (nonZeroDivisors A)) (FractionRing A)[X] ‹Q.IsPrime› hd
  have hh : Q.height = (Q.map (algebraMap A[X] (FractionRing A)[X])).height :=
    (congrArg Ideal.height hcomap.symm).trans
      (IsLocalization.height_comap (Submonoid.map (C : A →+* A[X]) (nonZeroDivisors A)) _)
  have h1 := Ideal.height_le_ringKrullDim_of_ne_top hQ'.ne_top
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    ← hh] at h1
  exact_mod_cast h1

theorem height_le_height_comap_C_add_one {R : Type*} [CommRing R] [IsNoetherianRing R]
    (P : Ideal R[X]) [P.IsPrime] : P.height ≤ (P.comap C).height + 1 := by

  set p := P.comap (C : R →+* R[X]) with hp
  letI : Algebra R[X] (Localization.AtPrime p)[X] := Polynomial.algebra R (Localization.AtPrime p)
  haveI : IsLocalization (Submonoid.map (C : R →+* R[X]) p.primeCompl)
      (Localization.AtPrime p)[X] := Polynomial.isLocalization p.primeCompl (Localization.AtPrime p)
  haveI : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl (Localization.AtPrime p) inferInstance
  have hd : Disjoint ((Submonoid.map (C : R →+* R[X]) p.primeCompl : Submonoid R[X]) :
      Set R[X]) (P : Set R[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsP
    exact hs hsP
  haveI hP' : (P.map (algebraMap R[X] (Localization.AtPrime p)[X])).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ P ‹P.IsPrime› hd
  have hcomap := IsLocalization.comap_map_of_isPrime_disjoint
    (Submonoid.map (C : R →+* R[X]) p.primeCompl) (Localization.AtPrime p)[X] ‹P.IsPrime› hd
  have hh : P.height = (P.map (algebraMap R[X] (Localization.AtPrime p)[X])).height :=
    (congrArg Ideal.height hcomap.symm).trans
      (IsLocalization.height_comap (Submonoid.map (C : R →+* R[X]) p.primeCompl) _)
  have h1 := Ideal.height_le_ringKrullDim_of_ne_top hP'.ne_top
  rw [Polynomial.ringKrullDim_of_isNoetherianRing,
    IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), ← hh] at h1
  exact_mod_cast h1

private theorem height_eq_order_height_lemma {R : Type*} [CommRing R] (p : Ideal R) [hp : p.IsPrime] :
    p.height = Order.height (⟨p, hp⟩ : PrimeSpectrum R) := by
  have hmem : p ∈ p.minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton p
  unfold Ideal.height
  refine le_antisymm ((iInf₂_le p hmem).trans (le_of_eq rfl)) (le_iInf₂ fun J hJ => ?_)
  have hJp : J = p := by
    have h2 := hJ
    rw [Ideal.minimalPrimes_eq_subsingleton_self] at h2
    exact h2
  subst hJp
  exact le_of_eq rfl

theorem height_add_one_le_height_comap_of_surjective {A S : Type*} [CommRing A] [IsDomain A]
    [CommRing S] (φ : A →+* S) (hφ : Function.Surjective φ) (hker : RingHom.ker φ ≠ ⊥)
    (q : Ideal S) [q.IsPrime] : q.height + 1 ≤ (q.comap φ).height := by
  let g : WithBot (PrimeSpectrum S) → PrimeSpectrum A := fun x =>
    Option.elim x ⟨⊥, Ideal.isPrime_bot⟩ (fun p => ⟨p.asIdeal.comap φ, inferInstance⟩)
  have hg : StrictMono g := by
    intro a b hab
    induction b using WithBot.recBotCoe with
    | bot => exact (not_lt_bot hab).elim
    | coe p' =>
      induction a using WithBot.recBotCoe with
      | bot =>
        change (⊥ : Ideal A) < p'.asIdeal.comap φ
        have hk : RingHom.ker φ ≤ p'.asIdeal.comap φ := fun y hy => by
          rw [Ideal.mem_comap, RingHom.mem_ker.mp hy]
          exact p'.asIdeal.zero_mem
        exact bot_lt_iff_ne_bot.mpr fun h => hker (le_bot_iff.mp (hk.trans h.le))
      | coe p =>
        have hpp : p < p' := WithBot.coe_lt_coe.mp hab
        change p.asIdeal.comap φ < p'.asIdeal.comap φ
        refine lt_of_le_of_ne (Ideal.comap_mono (show p.asIdeal ≤ p'.asIdeal from hpp.le)) ?_
        intro h
        have h' : p'.asIdeal ≤ p.asIdeal :=
          (Ideal.comap_le_comap_iff_of_surjective φ hφ _ _).mp h.ge
        exact lt_irrefl _ (lt_of_lt_of_le ((PrimeSpectrum.asIdeal_lt_asIdeal p p').mpr hpp) h')
  have h1 := Order.height_le_height_apply_of_strictMono g hg
    ((⟨q, ‹_›⟩ : PrimeSpectrum S) : WithBot (PrimeSpectrum S))
  rw [Order.height_coe_withBot] at h1
  rw [height_eq_order_height_lemma q, height_eq_order_height_lemma (q.comap φ)]
  exact h1

theorem height_le_height_comap_of_eval₂_surjective {R S : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [CommRing S] [IsDomain S] (f : R →+* S) (hf : Function.Injective f) (x : S)
    (hgen : Function.Surjective (eval₂RingHom f x)) (halg : ∃ g : R[X], g ≠ 0 ∧ eval₂ f x g = 0)
    (q : Ideal S) [q.IsPrime] : q.height ≤ (q.comap f).height := by
  have hker : RingHom.ker (eval₂RingHom f x) ≠ ⊥ := by
    obtain ⟨g, hg0, hg⟩ := halg
    intro h
    apply hg0
    have hmem : g ∈ RingHom.ker (eval₂RingHom f x) := by
      rw [RingHom.mem_ker]
      simpa using hg
    rw [h, Ideal.mem_bot] at hmem
    exact hmem
  have h3 := height_add_one_le_height_comap_of_surjective (eval₂RingHom f x) hgen hker q
  have h2 := height_le_height_comap_C_add_one (q.comap (eval₂RingHom f x))
  have hc : (q.comap (eval₂RingHom f x)).comap (C : R →+* R[X]) = q.comap f := by
    rw [Ideal.comap_comap]
    congr 1
    ext r
    simp
  rw [hc] at h2
  exact (WithTop.add_le_add_iff_right ENat.one_ne_top).mp (h3.trans h2)

end ReciprocityTheory.CA
