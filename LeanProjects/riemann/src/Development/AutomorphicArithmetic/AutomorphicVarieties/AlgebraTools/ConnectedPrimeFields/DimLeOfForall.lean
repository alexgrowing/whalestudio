import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem dim_le_of_forall {R : Type} [CommRing R] (I : Ideal R) (d : WithBot ℕ∞)
    (h : ∀ P : Ideal R, P.IsPrime → I ≤ P → ∃ J : Ideal R, J ≤ P ∧ ringKrullDim (R ⧸ J) ≤ d) :
    ringKrullDim (R ⧸ I) ≤ d := by
  rw [ringKrullDim_quotient]
  unfold Order.krullDim
  apply iSup_le
  intro l
  obtain ⟨J, hJP, hJd⟩ := h l.head.1.asIdeal l.head.1.isPrime l.head.2
  rw [ringKrullDim_quotient] at hJd
  let l' : LTSeries (PrimeSpectrum.zeroLocus (J : Set R)) :=
    { length := l.length
      toFun := fun i => ⟨(l i).1, fun r hr => (l.monotone (Fin.zero_le i)) (hJP hr)⟩
      step := fun i => l.step i }
  exact le_trans (le_iSup (fun p : LTSeries (PrimeSpectrum.zeroLocus (J : Set R)) => (p.length : WithBot ℕ∞)) l') hJd

theorem UpperTheory.V.AlgebraTools.Conn.chain :
    ∀ {R : Type} [CommRing R] [IsNoetherianRing R] (a : Ideal R) (k : WithBot ℕ∞), ConnOn a k →
      ∀ p ∈ a.minimalPrimes, ∀ q ∈ a.minimalPrimes,
        Relation.ReflTransGen (fun x y : Ideal R => x ∈ a.minimalPrimes ∧ y ∈ a.minimalPrimes ∧ ReciprocityTheory.CA.Linked R k x y) p q := by
  intro R _ _ a k hconn p hp q hq
  classical
  let rel : Ideal R → Ideal R → Prop := fun x y =>
    x ∈ a.minimalPrimes ∧ y ∈ a.minimalPrimes ∧ ReciprocityTheory.CA.Linked R k x y
  change Relation.ReflTransGen rel p q
  by_contra hpq
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing R a
  obtain ⟨K, hK⟩ : ∃ K : Finset (Ideal R),
      ∀ x, x ∈ K ↔ x ∈ a.minimalPrimes ∧ Relation.ReflTransGen rel p x :=
    ⟨hfin.toFinset.filter (fun x => Relation.ReflTransGen rel p x), fun x => by
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]⟩
  obtain ⟨L, hL⟩ : ∃ L : Finset (Ideal R),
      ∀ x, x ∈ L ↔ x ∈ a.minimalPrimes ∧ ¬ Relation.ReflTransGen rel p x :=
    ⟨hfin.toFinset.filter (fun x => ¬ Relation.ReflTransGen rel p x), fun x => by
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]⟩
  have hpK : p ∈ K := (hK p).mpr ⟨hp, Relation.ReflTransGen.refl⟩
  have hqL : q ∈ L := (hL q).mpr ⟨hq, hpq⟩
  obtain ⟨g, hg⟩ : ∃ g : Ideal R × Ideal R → WithBot ℕ∞,
      ∀ xy, g xy = ringKrullDim (R ⧸ (xy.1 ⊔ xy.2)) := ⟨_, fun _ => rfl⟩
  have hnl : ∀ x ∈ K, ∀ y ∈ L, g (x, y) < k := by
    intro x hx y hy
    obtain ⟨hxM, hpx⟩ := (hK x).mp hx
    obtain ⟨hyM, hpy⟩ := (hL y).mp hy
    rw [hg]
    by_contra hle
    exact hpy (hpx.tail ⟨hxM, hyM, not_lt.mp hle⟩)
  have hk : ⊥ < k := lt_of_le_of_lt bot_le (hnl p hpK q hqL)
  obtain ⟨J1, hJ1⟩ : ∃ J1 : Ideal R, J1 = K.inf id := ⟨_, rfl⟩
  obtain ⟨J2, hJ2⟩ : ∃ J2 : Ideal R, J2 = L.inf id := ⟨_, rfl⟩
  have haJ1 : a ≤ J1 := hJ1 ▸ Finset.le_inf (fun x hx => ((hK x).mp hx).1.1.2)
  have haI : a ≤ J1 ⊔ J2 := le_sup_of_le_left haJ1
  have hdim : ringKrullDim (R ⧸ (J1 ⊔ J2)) < k := by
    have hd : ringKrullDim (R ⧸ (J1 ⊔ J2)) ≤ (K ×ˢ L).sup g := by
      apply dim_le_of_forall
      intro P hP hIP
      obtain ⟨x, hx, hxP⟩ :=
        (Ideal.IsPrime.inf_le' (s := K) (f := id) hP).mp (hJ1 ▸ le_sup_left.trans hIP)
      obtain ⟨y, hy, hyP⟩ :=
        (Ideal.IsPrime.inf_le' (s := L) (f := id) hP).mp (hJ2 ▸ le_sup_right.trans hIP)
      refine ⟨x ⊔ y, sup_le hxP hyP, ?_⟩
      have hle : g (x, y) ≤ (K ×ˢ L).sup g := Finset.le_sup (Finset.mem_product.mpr ⟨hx, hy⟩)
      rw [hg] at hle
      exact hle
    refine lt_of_le_of_lt hd ((Finset.sup_lt_iff hk).mpr ?_)
    intro xy hxy
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hxy
    exact hnl _ h1 _ h2
  have mz : ∀ (J : Ideal R) (z : PrimeSpectrum R),
      z ∈ PrimeSpectrum.zeroLocus (J : Set R) ↔ J ≤ z.asIdeal := fun J z => by
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  have hJ2p : ¬ J2 ≤ p := by
    intro h
    rw [hJ2] at h
    obtain ⟨y, hy, hyp⟩ := (Ideal.IsPrime.inf_le' (s := L) (f := id) hp.1.1).mp h
    have hyM := ((hL y).mp hy).1
    have hyeq : y = p := le_antisymm hyp (hp.2 hyM.1 hyp)
    exact ((hL y).mp hy).2 (hyeq ▸ Relation.ReflTransGen.refl)
  have hJ1q : ¬ J1 ≤ q := by
    intro h
    rw [hJ1] at h
    obtain ⟨x, hx, hxq⟩ := (Ideal.IsPrime.inf_le' (s := K) (f := id) hq.1.1).mp h
    have hxM := ((hK x).mp hx).1
    have hxeq : x = q := le_antisymm hxq (hq.2 hxM.1 hxq)
    exact hpq (hxeq ▸ ((hK x).mp hx).2)
  obtain ⟨z, hzS, hzu, hzv⟩ := (hconn (J1 ⊔ J2) haI hdim).isPreconnected
    (PrimeSpectrum.zeroLocus (J2 : Set R))ᶜ (PrimeSpectrum.zeroLocus (J1 : Set R))ᶜ
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
    (by
      rintro z ⟨_, hzI⟩
      by_contra hz
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hz
      exact hzI ((mz _ z).mpr (sup_le ((mz J1 z).mp hz.2) ((mz J2 z).mp hz.1))))
    ⟨⟨p, hp.1.1⟩, ⟨(mz a _).mpr hp.1.2, fun h => hJ2p (le_sup_right.trans ((mz _ _).mp h))⟩,
      fun h => hJ2p ((mz J2 _).mp h)⟩
    ⟨⟨q, hq.1.1⟩, ⟨(mz a _).mpr hq.1.2, fun h => hJ1q (le_sup_left.trans ((mz _ _).mp h))⟩,
      fun h => hJ1q ((mz J1 _).mp h)⟩
  obtain ⟨m, hm, hmz⟩ := Ideal.exists_minimalPrimes_le ((mz a z).mp hzS.1)
  by_cases hpm : Relation.ReflTransGen rel p m
  · refine hzv ((mz J1 z).mpr ?_)
    rw [hJ1]
    exact (Finset.inf_le (f := id) ((hK m).mpr ⟨hm, hpm⟩)).trans hmz
  · refine hzu ((mz J2 z).mpr ?_)
    rw [hJ2]
    exact (Finset.inf_le (f := id) ((hL m).mpr ⟨hm, hpm⟩)).trans hmz
