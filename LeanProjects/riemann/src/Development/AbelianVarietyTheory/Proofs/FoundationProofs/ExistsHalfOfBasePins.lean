import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit

noncomputable section

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.FWT Formalism.L2.Pj Formalism.L2.Pj.LPb ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Pointwise

namespace GlobalTheory.CoverHalf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eq_prod_of_squarefree {S : Type} [CommRing S] [IsDedekindDomain S] {I : Ideal S} (hI : Squarefree I)
    (P : Finset (HeightOneSpectrum S)) (hP : ∀ v, v ∈ P ↔ I ≤ v.asIdeal) : I = ∏ v ∈ P, v.asIdeal := by
  classical
  have h0 : I ≠ ⊥ := hI.ne_zero
  have hnd : (normalizedFactors I).Nodup := (squarefree_iff_nodup_normalizedFactors h0).1 hI
  have himg : P.image HeightOneSpectrum.asIdeal = (normalizedFactors I).toFinset := by
    ext J
    rw [Finset.mem_image, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff h0]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.isPrime, (hP v).1 hv⟩
    · rintro ⟨hp, hle⟩
      exact ⟨⟨J, hp, fun h => h0 (eq_bot_iff.2 (h ▸ hle))⟩, (hP _).2 hle, rfl⟩
  have h1 : ∏ v ∈ P, v.asIdeal = ∏ J ∈ P.image HeightOneSpectrum.asIdeal, J :=
    (Finset.prod_image (f := fun J => J) (fun a _ b _ h => HeightOneSpectrum.ext h)).symm
  rw [h1, himg, Finset.prod_eq_multiset_prod, Multiset.map_id', Multiset.toFinset_val, hnd.dedup,
    Ideal.prod_normalizedFactors_eq_self h0]

theorem not_mem_of_coprime {S : Type} [CommRing S] {J : Ideal S} (hJ : J ≠ ⊤) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : (a : S) ∈ J) : (b : S) ∉ J := by
  intro hb
  obtain ⟨u, v, huv⟩ : IsCoprime (a : S) (b : S) := by
    simpa using (Nat.isCoprime_iff_coprime.2 hab).map (Int.castRingHom S)
  exact hJ ((Ideal.eq_top_iff_one _).2 (huv ▸ J.add_mem (J.mul_mem_left _ ha) (J.mul_mem_left _ hb)))

variable {D : D7}

theorem squarefree_span_g (D : D7) :
    Squarefree (Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)}) := by
  have hs : ∀ k, Squarefree (Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)}) := fun k => by
    refine (squarefree_iff_nodup_normalizedFactors ?_).2 (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.g_splits D k).2
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (D.host.g_prime k).ne_zero
  rw [Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton, squarefree_mul_iff]
  refine ⟨IsCoprime.isRelPrime ?_, hs 0, hs 1⟩
  rw [Ideal.isCoprime_span_singleton_iff]
  simpa using (Nat.isCoprime_iff_coprime.2
    ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)).map (Int.castRingHom (𝓞 D.host.E))

theorem g_coprime (D : D7) (k : Fin 2) :
    Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * Ideal.absNorm D.host.ccK) := by
  have hc := D.ntypes.g_cond k
  have h1 : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc, Nat.gcd_one_left]
  refine Nat.Coprime.mul_right (h1.coprime_dvd_right (dvd_mul_right _ _)) ?_
  refine (D.host.ccK_coprime _ ?_).symm
  simp [D.host.g_level k]

theorem not_mem_of_over_g (PP : Pl D.host.E) (h : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) :
    ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal :=
  not_mem_of_coprime PP.isPrime.ne_top (Nat.Coprime.mul_left (g_coprime D 0) (g_coprime D 1)) h

theorem splitOK_of_place (PP : Pl D.host.E) {q : ℕ} (hq : q.Prime) (hc : Nat.card (kP PP) = q)
    (hu : (q : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2) (h2 : (2 : 𝓞 D.host.E) ∉ PP.asIdeal) :
    (q : 𝓞 D.host.E) ∈ PP.asIdeal ∧ SplitOK D q := by
  have := Fact.mk hq
  have : Finite (kP PP) := Nat.finite_of_card_ne_zero (hc ▸ hq.ne_zero)
  let _ : Fintype (kP PP) := Fintype.ofFinite _
  have hc' : Fintype.card (kP PP) = q := by rw [← Nat.card_eq_fintype_card, hc]
  let φ : ZMod q ≃+* kP PP := ZMod.ringEquivOfPrime (kP PP) hq hc'
  have hint : ∀ n : ℤ, (n : 𝓞 D.host.E) ∈ PP.asIdeal ↔ (q : ℤ) ∣ n := fun n => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast, ← ZMod.intCast_zmod_eq_zero_iff_dvd, ← map_intCast φ,
      map_eq_zero_iff φ φ.injective]
  have hqm : (q : 𝓞 D.host.E) ∈ PP.asIdeal := by exact_mod_cast (hint q).2 dvd_rfl
  obtain ⟨e, he⟩ := ZMod.intCast_surjective (φ.symm (Ideal.Quotient.mk _ (w0E D)))
  have hw : w0E D - (e : 𝓞 D.host.E) ∈ PP.asIdeal := by
    rw [← Ideal.Quotient.eq, map_intCast, ← map_intCast φ, he, RingEquiv.apply_symm_apply]
  have hsq := w0E_sq D
  have e4 : (4 : ℤ) * (mE D : ℤ) = (D.host.d : ℤ) + 1 := by exact_mod_cast mE_spec D
  have hdv : (q : ℤ) ∣ e ^ 2 - e + mE D := by
    rw [← hint]
    have : ((e ^ 2 - e + mE D : ℤ) : 𝓞 D.host.E) = (w0E D - (e : 𝓞 D.host.E)) * (1 - w0E D - e) := by
      push_cast
      linear_combination hsq
    rw [this]
    exact Ideal.mul_mem_right _ _ hw
  have hnd : ¬ (q : ℤ) ∣ 1 - 2 * e := by
    intro hdiv
    have hd : (D.host.d : ℤ) = 4 * (e ^ 2 - e + mE D) - (1 - 2 * e) ^ 2 := by linear_combination (-1 : ℤ) * e4
    have hpd : (q : ℤ) ∣ D.host.d := by
      rw [hd]; exact dvd_sub (hdv.mul_left 4) (dvd_pow hdiv two_ne_zero)
    have hpeq : q = D.host.d := (Nat.prime_dvd_prime_iff_eq hq D.host.hyp.2.1).1 (Int.natCast_dvd_natCast.1 hpd)
    have hr : rtE D ∈ PP.asIdeal := by
      have h1 := (hint _).2 hdiv
      have : rtE D = 2 * (w0E D - (e : 𝓞 D.host.E)) - ((1 - 2 * e : ℤ) : 𝓞 D.host.E) := by
        push_cast
        linear_combination (-1 : 𝓞 D.host.E) * two_w0E D
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hw) h1
    apply hu
    have : (q : 𝓞 D.host.E) = -(rtE D ^ 2) := by rw [rtE_sq, hpeq, neg_neg]
    rw [this]
    exact neg_mem (Ideal.pow_mem_pow hr 2)
  refine ⟨hqm, hq, ?_, ?_⟩
  · rintro rfl
    exact h2 (by exact_mod_cast hqm)
  · have hmod : (-(D.host.d : ℤ)) % (q : ℤ) = (1 - 2 * e) ^ 2 % (q : ℤ) := by
      refine (Int.modEq_iff_dvd.2 ?_ : Int.ModEq (q : ℤ) _ _)
      have : (1 - 2 * e) ^ 2 - (-(D.host.d : ℤ)) = 4 * (e ^ 2 - e + mE D) := by linear_combination (-1 : ℤ) * e4
      rw [this]
      exact hdv.mul_left 4
    rw [jacobiSym.mod_left' hmod]
    refine jacobiSym.sq_one' ?_
    exact Int.isCoprime_iff_gcd_eq_one.1
      ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hq)).2 hnd).symm

variable (D) in
open Classical in

def coverHalf (Q : Finset (Pl D.host.E)) : Ideal (𝓞 D.host.E) :=
  ∏ 𝔭 ∈ Q.image (fun PP => PP.under (𝓞 D.host.K)), 𝔭.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

theorem coverHalf_le {Q : Finset (Pl D.host.E)} {PP : Pl D.host.E} (h : PP ∈ Q) : coverHalf D Q ≤ PP.asIdeal := by
  classical
  unfold coverHalf
  refine (Ideal.prod_le_inf.trans (Finset.inf_le (b := PP.under (𝓞 D.host.K)) ?_)).trans Ideal.map_comap_le
  convert Finset.mem_image_of_mem _ h

def IsCoverLevel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (l : Level H) (pd : ℕ)
    (I : Ideal (𝓞 E)) (l₂ : Level H) : Prop :=
  l.Dvd l₂ ∧ l₂.M = l.M * pd ∧ Nat.Coprime pd l.M ∧ l₂.Mb = l.Mb * I ∧
    I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧ l₂.A = 1

theorem isCoverLevel_of_covPin {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} {Tup : Type} {dδ : Tup → DeltaDat Xo c n}
    (h : CovPin Xo c dδ) (t : Tup) : IsCoverLevel l (dδ t).pd (dδ t).I (dδ t).l₂ :=
  ⟨(h t).1.1, (h t).1.2.1, (h t).1.2.2.1, (h t).1.2.2.2.1, (h t).1.2.2.2.2.1, (h t).2.1⟩

theorem exists_coverLevel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (l : Level H)
    (hA : l.A = 1) (pd : ℕ) (I : Ideal (𝓞 E)) (hodd : Odd pd) (hc : Nat.Coprime pd l.M)
    (hK : ∃ G : Set (𝓞 E), I = Ideal.span G ∧ G ⊆ Algebra.adjoin ℤ {H.w0})
    (hp : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(pd : 𝓞 E)})
    (hI : I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) : ∃ l₂ : Level H, IsCoverLevel l pd I l₂ := by
  have hcop : IsCoprime (Ideal.span {(l.M : 𝓞 E)}) (Ideal.span {(pd : 𝓞 E)}) := by
    rw [Ideal.isCoprime_span_singleton_iff]
    simpa using (Nat.isCoprime_iff_coprime.2 hc.symm).map (Int.castRingHom (𝓞 E))
  rw [← l.prod, ← hp] at hcop
  refine ⟨{ M := l.M * pd
            three_le := l.three_le.trans (Nat.le_mul_of_pos_right _ hodd.pos)
            odd := l.odd.mul hodd
            Mb := l.Mb * I
            fromK := ?_
            prod := ?_
            coprime := ?_
            A := 1
            A_pos := Nat.one_pos }, ⟨dvd_mul_right _ _, Ideal.mul_le_left, hA.dvd⟩, rfl, hc, rfl, hI, rfl⟩
  · obtain ⟨G, hG, hGA⟩ := hK
    refine fromK_of_gen ⟨{a | a ∈ l.Mb ∧ a ∈ Algebra.adjoin ℤ {H.w0}} * G, ?_, ?_⟩
    · rw [← Ideal.span_mul_span', ← l.fromK, ← hG]
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx
      exact Subalgebra.mul_mem _ ha.2 (hGA hb)
  · rw [Ideal.map_mul, mul_mul_mul_comm, l.prod, hp, Ideal.span_singleton_mul_span_singleton, Nat.cast_mul]
  · rw [← Ideal.isCoprime_iff_sup_eq, Ideal.map_mul]
    exact IsCoprime.mul_left
      (IsCoprime.mul_right (Ideal.isCoprime_iff_sup_eq.2 l.coprime) hcop.of_mul_left_left.of_mul_right_right)
      (IsCoprime.mul_right hcop.of_mul_left_right.of_mul_right_left.symm (Ideal.isCoprime_iff_sup_eq.2 hI))

theorem coverHalf_spec {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q)
    (h2 : ∀ PP ∈ Q, (2 : 𝓞 D.host.E) ∉ PP.asIdeal)
    (h1 : ∀ PP ∈ Q, ∀ PP' ∈ Q, (∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.E) ∈ PP.asIdeal ∧ (p : 𝓞 D.host.E) ∈ PP'.asIdeal) →
      PP.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = PP'.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) :
    ∃ pd : ℕ, Odd pd ∧ Nat.Coprime pd (D.host.g 0 * D.host.g 1) ∧
      (∃ G : Set (𝓞 D.host.E), coverHalf D Q = Ideal.span G ∧ G ⊆ Algebra.adjoin ℤ {w0E D}) ∧
      coverHalf D Q * (coverHalf D Q).map (bH D) = Ideal.span {(pd : 𝓞 D.host.E)} ∧
      coverHalf D Q ⊔ (coverHalf D Q).map (bH D) = ⊤ := by
  classical
  set S := Q.image (fun PP => PP.under (𝓞 D.host.K)) with hS
  have key : ∀ 𝔭 : HeightOneSpectrum (𝓞 D.host.K), ∃ (q : ℕ) (e : ℤ), 𝔭 ∈ S → SplitOK D q ∧ (∀ i, q ≠ D.host.g i) ∧
      (q : 𝓞 D.host.K) ∈ 𝔭.asIdeal ∧
      (q : ℤ) ∣ e ^ 2 - e + mE D ∧ IsCoprime (1 - 2 * e) (q : ℤ) ∧ 𝔭.asIdeal = JK D q e := by
    intro 𝔭
    by_cases h : 𝔭 ∈ S
    · obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 h
      obtain ⟨⟨q, hq, hc, hu, hg⟩, -⟩ := hQ PP hPP
      obtain ⟨hm, hs⟩ := splitOK_of_place PP hq hc hu (h2 PP hPP)
      have hm' : (q : 𝓞 D.host.K) ∈ (PP.under (𝓞 D.host.K)).asIdeal := by
        show algebraMap (𝓞 D.host.K) (𝓞 D.host.E) q ∈ PP.asIdeal
        rwa [map_natCast]
      obtain ⟨e, he⟩ := pb_eq_JK D hs _ hm'
      exact ⟨q, e, fun _ => ⟨hs, hg, hm', he⟩⟩
    · exact ⟨0, 0, fun h' => absurd h' h⟩
  choose q e hqe using key
  have hinj : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → q a ≠ q b := by
    intro a ha b hb hab h
    have ha' := (hqe a ha).2.2.1
    have hb' := (hqe b hb).2.2.1
    have hp := (hqe a ha).1.1
    rw [← h] at hb'
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨PP', hPP', rfl⟩ := Finset.mem_image.1 hb
    refine hab (HeightOneSpectrum.ext (h1 PP hPP PP' hPP' ⟨_, hp, ?_, ?_⟩))
    · rw [← map_natCast (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))]; exact ha'
    · rw [← map_natCast (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))]; exact hb'
  have hI : coverHalf D Q = ∏ a ∈ S, QE D (q a) (e a) := by
    unfold coverHalf
    refine Finset.prod_congr (by convert rfl) fun a ha => ?_
    rw [(hqe a ha).2.2.2.2.2, map_JK]
  have hIb : (coverHalf D Q).map (bH D) = ∏ a ∈ S, QE D (q a) (1 - e a) := by
    rw [hI, ← Ideal.mapHom_apply, map_prod]
    exact Finset.prod_congr rfl fun a _ => QE_map_bar D _ _
  refine ⟨∏ a ∈ S, q a, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one
      fun a ha => (hqe a ha).1.1.odd_of_ne_two (hqe a ha).1.2.1
  · refine Nat.Coprime.prod_left fun a ha => Nat.Coprime.mul_right ?_ ?_
    · exact (Nat.coprime_primes (hqe a ha).1.1 (D.host.g_prime 0)).2 ((hqe a ha).2.1 0)
    · exact (Nat.coprime_primes (hqe a ha).1.1 (D.host.g_prime 1)).2 ((hqe a ha).2.1 1)
  · rw [hI]
    refine Finset.prod_induction _
      (fun J => ∃ G : Set (𝓞 D.host.E), J = Ideal.span G ∧ G ⊆ Algebra.adjoin ℤ {w0E D}) ?_ ?_ ?_
    · rintro _ _ ⟨G, rfl, hG⟩ ⟨G', rfl, hG'⟩
      refine ⟨G * G', Ideal.span_mul_span' _ _, fun x hx => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx
      exact Subalgebra.mul_mem _ (hG ha) (hG' hb)
    · exact ⟨{1}, by simp, fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact Subalgebra.one_mem _⟩
    · intro a _
      refine ⟨_, rfl, fun y hy => ?_⟩
      rcases hy with rfl | hy
      · exact Subalgebra.natCast_mem _ _
      · rw [Set.mem_singleton_iff.1 hy]
        exact Subalgebra.sub_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) (Subalgebra.intCast_mem _ _)
  · rw [hIb, hI, ← Finset.prod_mul_distrib, Nat.cast_prod, ← Ideal.prod_span_singleton]
    exact Finset.prod_congr rfl fun a ha => QE_mul D _ _ (hqe a ha).2.2.2.1 (hqe a ha).2.2.2.2.1
  · rw [hIb, hI, ← Ideal.isCoprime_iff_sup_eq]
    refine IsCoprime.prod_left fun a ha => IsCoprime.prod_right fun b hb => ?_
    by_cases hab : a = b
    · subst hab
      exact QE_cop_self D _ _ (hqe a ha).2.2.2.2.1
    · exact QE_cop_ne D (hqe a ha).1.1 (hqe b hb).1.1 (hinj a ha b hb hab) _ _

def Oriented {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (l : Level H)
    (pb : Fin 2 → 𝓞 E) : Prop :=
  pb 0 * pb 1 ∈ l.Mb

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_cover_of_places (Q : Par D) (R : RealDat D A Ks) (hH : Q.PinHost) (hl : Q.PinLevel)
    (hP : ∀ PP, PP ∈ R.Pg ↔ Q.l.Mb ≤ PP.asIdeal) (hG : QGuard R) (t : T0) (hQ : IsTwistPlaces D.host.g (R.Q t)) :
    ∃ (pd : ℕ) (l₂ : Level Q.H), IsCoverLevel Q.l pd (coverHalf D (R.Q t)) l₂ ∧
      HalfIs R t Q.l.Mb (coverHalf D (R.Q t)) := by
  have hw : Q.H.w0 = w0E D := by
    have h1 := Q.H.two_weight_eq_one_add_root
    have h3 : Q.H.rt = rtE D := RingOfIntegers.ext hH.2.1
    rw [h3, ← two_w0E D] at h1
    exact mul_left_cancel₀ two_ne_zero h1
  have hb : (Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = bH D :=
    RingHom.ext fun a => RingOfIntegers.ext (Q.H.bar_eq a)
  have h2 : ∀ PP ∈ R.Q t, (2 : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP h => hG.2 t PP hPP (by
    rw [Nat.cast_mul, Nat.cast_mul, mul_assoc]
    obtain ⟨c, hc⟩ := D.host.two_dvd_QS
    refine Ideal.mul_mem_right _ _ ?_
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (by exact_mod_cast h))
  obtain ⟨pd, hodd, hc, hK, hp, hI⟩ := coverHalf_spec hQ h2 (hG.1 t)
  obtain ⟨l₂, hl₂⟩ := exists_coverLevel Q.l hl.2 pd _ hodd (by rw [hl.1]; exact hc) (by rw [hw]; exact hK)
    (by rw [hb]; exact hp) (by rw [hb]; exact hI)
  have hprod := Q.l.prod
  rw [hl.1] at hprod
  refine ⟨pd, l₂, hl₂, eq_prod_of_squarefree ?_ _ hP, fun PP h => coverHalf_le h, fun PP h => ?_⟩
  · exact (hprod ▸ squarefree_span_g D : Squarefree (Q.l.Mb * _)).of_mul_left
  · rcases h with h | h
    · refine not_mem_of_over_g PP ((hP PP).1 h (?_ : _ ∈ Q.l.Mb))
      rw [← Ideal.span_singleton_le_iff_mem, ← hprod]
      exact Ideal.mul_le_left
    · exact hG.2 t PP h

theorem half_eq_span (Q : Par D) (hl : Q.PinLevel) {pb : Fin 2 → 𝓞 D.host.E} (hT : IsTypeDatum D.host.g pb)
    (hO : Oriented Q.l pb) : Q.l.Mb = Ideal.span {pb 0 * pb 1} := by
  set b := (Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) with hbdef
  have hn : ∀ i, pb i * b (pb i) = (D.host.g i : 𝓞 D.host.E) := fun i => by
    apply RingOfIntegers.ext
    have h1 := hT.norm i
    have h2 : ((b (pb i) : 𝓞 D.host.E) : D.host.E) = star (pb i : D.host.E) := Q.H.bar_eq (pb i)
    rw [← h2] at h1
    exact h1
  have hprod := Q.l.prod
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hO)
  have h1 : Ideal.span {pb 0 * pb 1} * (Ideal.span {pb 0 * pb 1}).map b = Ideal.span {(Q.l.M : 𝓞 D.host.E)} := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_mul_span_singleton, map_mul, mul_mul_mul_comm, hn, hn, hl.1,
      Nat.cast_mul]
  rw [hC, Ideal.map_mul, mul_mul_mul_comm, hprod] at h1
  have h0 : Ideal.span {(Q.l.M : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    have := Q.l.three_le
    exact_mod_cast (by omega : Q.l.M ≠ 0)
  have h2 : C * C.map b = 1 := mul_left_cancel₀ h0 (h1.trans (mul_one _).symm)
  have h3 : C = ⊤ := top_le_iff.1 (by rw [← Ideal.one_eq_top, ← h2]; exact Ideal.mul_le_left)
  rw [hC, h3, Ideal.mul_top]

theorem exists_half (Q : Par D) (R : RealDat D A Ks) (pb : Fin 2 → 𝓞 D.host.E) (hH : Q.PinHost) (hl : Q.PinLevel)
    (hO : Oriented Q.l pb) (hP : IsTypePlaces D.host.g pb R.Pg) (hQ : ∀ t, IsTwistPlaces D.host.g (R.Q t))
    (hG : QGuard R) (t : T0) :
    ∃ (pd : ℕ) (l₂ : Level Q.H), IsCoverLevel Q.l pd (coverHalf D (R.Q t)) l₂ ∧
      HalfIs R t Q.l.Mb (coverHalf D (R.Q t)) := by
  refine exists_cover_of_places Q R hH hl (fun PP => ?_) hG t (hQ t)
  have h := half_eq_span Q hl hP.1 hO
  rw [hP.2, mem_primesOf, h, Ideal.span_singleton_le_iff_mem]
  refine and_iff_right fun h0 => ?_
  have hprod := Q.l.prod
  rw [h, h0, Ideal.span_singleton_zero, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at hprod
  have := Q.l.three_le
  exact (by omega : Q.l.M ≠ 0) (by exact_mod_cast hprod)

theorem prod_map_le_iff (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) (PP : Pl D.host.E) :
    ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal ↔ ∃ k, PP.under (𝓞 D.host.K) = pb k := by
  rw [PP.isPrime.prod_le]
  refine exists_congr fun k => ?_
  rw [and_iff_right (Finset.mem_univ k), Ideal.map_le_iff_le_comap]
  constructor
  · intro h
    exact HeightOneSpectrum.ext ((pb k).isMaximal.eq_of_le (PP.under (𝓞 D.host.K)).isPrime.ne_top h).symm
  · intro h
    rw [← h]
    exact le_rfl

theorem exists_half_of_laws (T : Core D) (R : RealDat D A Ks) {μ0 : T0} (hT : LawsM T) (hL : R.toLevCh.Is μ0)
    (hO : T.pb = R.C.P.pb) (hG : QGuard R) (t : T0) :
    ∃ (pd : ℕ) (l₂ : Level T.Q.H), IsCoverLevel T.Q.l pd (coverHalf D (R.Q t)) l₂ ∧
      HalfIs R t T.Q.l.Mb (coverHalf D (R.Q t)) := by
  refine exists_cover_of_places T.Q R hT.pins.1 hT.pins.2.1 (fun PP => ?_) hG t (hL.Q_pl t)
  rw [hL.Pg, hT.half.2, prod_map_le_iff, hO]
  rfl

theorem primes_eq_of_halfIs (T : Core D) (R : RealDat D A Ks) {μ0 : T0} (hT : LawsM T) (hL : R.toLevCh.Is μ0)
    {t : T0} {I : Ideal (𝓞 D.host.E)} (h : HalfIs R t T.Q.l.Mb I) : T.pb = R.C.P.pb := by
  funext k
  have := (R.C.P.pb k).isPrime
  obtain ⟨P, hP, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 D.host.E) (R.C.P.pb k).asIdeal
    (by
      rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))).1 (FaithfulSMul.algebraMap_injective _ _)]
      exact bot_le)
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    apply (R.C.P.pb k).ne_bot
    rw [← hPc, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)]
  let PP : Pl D.host.E := ⟨P, hP, hP0⟩
  have hu : PP.under (𝓞 D.host.K) = R.C.P.pb k := HeightOneSpectrum.ext hPc
  have hmem : PP ∈ R.Pg := (hL.Pg PP).2 ⟨k, hu⟩
  have hle : T.Q.l.Mb ≤ PP.asIdeal := by
    rw [h.1]
    exact Ideal.prod_le_inf.trans (Finset.inf_le hmem)
  rw [hT.half.2, prod_map_le_iff] at hle
  obtain ⟨k', hk'⟩ := hle
  rw [hu] at hk'
  by_cases hkk : k' = k
  · rw [hk', hkk]
  · exfalso
    have hne : D.host.g k' ≠ D.host.g k := by
      have := D.host.g_ne
      fin_cases k <;> fin_cases k' <;> simp_all [eq_comm]
    exact not_mem_of_coprime (T.pb k').isPrime.ne_top
      ((Nat.coprime_primes (D.host.g_prime k') (D.host.g_prime k)).2 hne) (hT.half.1 k') (hk' ▸ R.C.P.pb_over k)

end GlobalTheory.CoverHalf
