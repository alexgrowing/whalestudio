import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.LocDim

namespace ReciprocityTheory.CA

open IsLocalRing

theorem height_add_height_Ici_le {α : Type*} [PartialOrder α] {a b : α} (hab : a ≤ b) :
    Order.height a + Order.height (⟨b, hab⟩ : Set.Ici a) ≤ Order.height b := by
  rcases eq_or_ne (Order.height b) ⊤ with hb | hb
  · rw [hb]; exact le_top
  have hmono : StrictMono (Subtype.val : Set.Ici a → α) := fun _ _ h => h
  have h1 : Order.height a ≠ ⊤ := ne_top_of_le_ne_top hb (Order.height_mono hab)
  have h2 : Order.height (⟨b, hab⟩ : Set.Ici a) ≠ ⊤ :=
    ne_top_of_le_ne_top hb (Order.height_le_height_apply_of_strictMono _ hmono ⟨b, hab⟩)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h1
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h2
  obtain ⟨s, hsl, hsn⟩ := Order.exists_series_of_le_height a (n := n) hn.le
  obtain ⟨t, htl, htm⟩ := Order.exists_series_of_le_height (⟨b, hab⟩ : Set.Ici a) (n := m) hm.le
  rw [← hn, ← hm]
  let t' : LTSeries α := t.map Subtype.val hmono
  have ht'l : t'.last = b := by
    show ((t.last : Set.Ici a) : α) = b
    rw [htl]
  have ht'len : t'.length = m := htm
  have hhead : a ≤ t'.head := t.head.2
  rcases hhead.eq_or_lt with he | hlt
  ·
    have hc : s.last = t'.head := hsl.trans he
    have hlen : (s.smash t' hc).length = n + m := by
      show s.length + t'.length = n + m
      rw [hsn, ht'len]
    have hlast : (s.smash t' hc).last = b := by
      first
      | (rw [RelSeries.last_smash]; exact ht'l)
      | (rw [RelSeries.smash_last]; exact ht'l)
      | simp [ht'l]
    calc ((n : ℕ∞) + (m : ℕ∞)) = ((s.smash t' hc).length : ℕ∞) := by rw [hlen]; norm_cast
      _ ≤ Order.height b := Order.length_le_height hlast.le
  ·
    have hc : s.last < t'.head := by rw [hsl]; exact hlt
    have hlen : (s.append t' hc).length = n + m + 1 := by
      show s.length + t'.length + 1 = n + m + 1
      rw [hsn, ht'len]
    have hlast : (s.append t' hc).last = b := by
      first
      | (rw [RelSeries.last_append]; exact ht'l)
      | (rw [RelSeries.append_last]; exact ht'l)
      | simp [ht'l]
    calc ((n : ℕ∞) + (m : ℕ∞)) ≤ ((n + m + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_succ (n + m)
      _ = ((s.append t' hc).length : ℕ∞) := by rw [hlen]
      _ ≤ Order.height b := Order.length_le_height hlast.le

private theorem height_eq_order_height_lemma {R : Type*} [CommRing R] (I : Ideal R)
    [hI : I.IsPrime] : I.height = Order.height (⟨I, hI⟩ : PrimeSpectrum R) := by
  have hmin : I.minimalPrimes = {I} := Ideal.minimalPrimes_eq_subsingleton_self
  unfold Ideal.height
  apply le_antisymm
  · exact iInf₂_le I (by rw [hmin]; rfl)
  · refine le_iInf₂ fun J hJ => ?_
    have hJI : J = I := by rw [hmin] at hJ; exact hJ
    subst hJI
    exact le_rfl

theorem height_add_height_map_quotient_le {P : Type*} [CommRing P] (p q : Ideal P) [p.IsPrime]
    [q.IsPrime] (hpq : p ≤ q) : p.height + (q.map (Ideal.Quotient.mk p)).height ≤ q.height := by
  haveI hq' : (q.map (Ideal.Quotient.mk p)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hpq)
  rw [height_eq_order_height_lemma p, height_eq_order_height_lemma q,
    height_eq_order_height_lemma (q.map (Ideal.Quotient.mk p))]
  have hpq' : (⟨p, ‹_›⟩ : PrimeSpectrum P) ≤ ⟨q, ‹_›⟩ := hpq

  let f : PrimeSpectrum (P ⧸ p) → Set.Ici (⟨p, ‹_›⟩ : PrimeSpectrum P) := fun x =>
    ⟨⟨Ideal.comap (Ideal.Quotient.mk p) x.asIdeal, inferInstance⟩, fun z hz => by
      show z ∈ Ideal.comap (Ideal.Quotient.mk p) x.asIdeal
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hz]
      exact x.asIdeal.zero_mem⟩
  have hf : StrictMono f := by
    intro x y hxy
    show Ideal.comap (Ideal.Quotient.mk p) x.asIdeal < Ideal.comap (Ideal.Quotient.mk p) y.asIdeal
    refine lt_of_le_of_ne (Ideal.comap_mono (show x.asIdeal ≤ y.asIdeal from hxy.le)) fun e => ?_
    exact hxy.ne (PrimeSpectrum.ext
      (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective e))
  have hfq : f ⟨q.map (Ideal.Quotient.mk p), hq'⟩ = ⟨⟨q, ‹_›⟩, hpq'⟩ := by
    apply Subtype.ext
    apply PrimeSpectrum.ext
    show Ideal.comap (Ideal.Quotient.mk p) (q.map (Ideal.Quotient.mk p)) = q
    ext z
    rw [Ideal.mem_comap]
    first
    | exact Ideal.mem_quotient_iff_mem hpq
    | exact Ideal.mem_quotient_iff_mem_sup.trans (by rw [sup_eq_left.mpr hpq])
  have hle := Order.height_le_height_apply_of_strictMono f hf ⟨q.map (Ideal.Quotient.mk p), hq'⟩
  rw [hfq] at hle
  exact (add_le_add le_rfl hle).trans (height_add_height_Ici_le hpq')

private theorem comap_map_mk_lemma_4 {R : Type*} [CommRing R] (I J : Ideal R) (h : I ≤ J) :
    Ideal.comap (Ideal.Quotient.mk I) (J.map (Ideal.Quotient.mk I)) = J := by
  ext z
  rw [Ideal.mem_comap]
  first
  | exact Ideal.mem_quotient_iff_mem h
  | exact Ideal.mem_quotient_iff_mem_sup.trans (by rw [sup_eq_left.mpr h])

private theorem height_le_height_Iic_lemma_2 {α β : Type*} [PartialOrder α] [Preorder β] (a : α)
    (f : Set.Iic a → β) (hf : StrictMono f) : Order.height a ≤ Order.height (f ⟨a, le_rfl⟩) := by
  have hmono : ∀ s : LTSeries α, Monotone s := fun s => by
    first
    | exact s.monotone
    | exact s.strictMono.monotone
  have H : ∀ s : LTSeries α, s.last ≤ a → (s.length : ℕ∞) ≤ Order.height (f ⟨a, le_rfl⟩) := by
    intro s hs
    let t : LTSeries β :=
      { length := s.length
        toFun := fun i => f ⟨s i, (hmono s (Fin.le_last i)).trans hs⟩
        step := fun i => hf (Subtype.mk_lt_mk.mpr (s.step i)) }
    have ht : t.last ≤ f ⟨a, le_rfl⟩ := by
      show f ⟨s (Fin.last s.length), _⟩ ≤ f ⟨a, le_rfl⟩
      exact hf.monotone (show s (Fin.last s.length) ≤ a from hs)
    exact Order.length_le_height ht
  first
  | exact Order.height_le_iff.mpr fun s hs => H s hs.le
  | exact Order.height_le fun s hs => H s hs.le
  | (unfold Order.height; exact iSup₂_le fun s hs => H s hs)

private theorem krullDim_le_height_lemma_3 {α β : Type*} [Preorder α] [Preorder β] (f : α → β)
    (hf : StrictMono f) (b : β) (hb : ∀ x, f x ≤ b) :
    Order.krullDim α ≤ (Order.height b : WithBot ℕ∞) := by
  unfold Order.krullDim
  refine iSup_le fun s => ?_
  have h := Order.length_le_height (p := s.map f hf) (x := b) (hb s.last)
  exact_mod_cast h

private theorem height_le_krullDim_lemma_6 {α : Type*} [Preorder α] (a : α) :
    (Order.height a : WithBot ℕ∞) ≤ Order.krullDim α := by
  first
  | exact Order.height_le_krullDim a
  | (have H : ∀ s : LTSeries α, ((s.length : ℕ∞) : WithBot ℕ∞) ≤ Order.krullDim α := fun s => by
       have := le_iSup (fun s : LTSeries α => (s.length : WithBot ℕ∞)) s
       exact_mod_cast this
     obtain ⟨k, hk⟩ := WithBot.ne_bot_iff_exists.mp
       (ne_bot_of_le_ne_bot WithBot.coe_ne_bot (H (RelSeries.singleton _ a)))
     rw [← hk]
     refine WithBot.coe_le_coe.mpr (Order.height_le_iff.mpr fun s _ => ?_)
     exact WithBot.coe_le_coe.mp (by rw [hk]; exact H s))

theorem ringKrullDim_localization_quotient_eq_height {P : Type*} [CommRing P] (p q : Ideal P)
    [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    ringKrullDim (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q))) =
      ((q.map (Ideal.Quotient.mk p)).height : WithBot ℕ∞) := by
  haveI hQ : (q.map (Ideal.Quotient.mk p)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hpq)
  have hdisj : Disjoint (q.primeCompl : Set P) (p : Set P) :=
    Set.disjoint_left.mpr fun x hx hxp => hx (hpq hxp)
  haveI hp' : (p.map (algebraMap P (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hdisj
  rw [height_eq_order_height_lemma (q.map (Ideal.Quotient.mk p))]
  show Order.krullDim (PrimeSpectrum (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q)))) = _

  have hpA : ∀ x : PrimeSpectrum (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q))),
      p ≤ Ideal.comap (algebraMap P (Localization.AtPrime q)) (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) x.asIdeal) := by
    intro x z hz
    rw [Ideal.mem_comap, Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hz)]
    exact x.asIdeal.zero_mem
  have hAq : ∀ x : PrimeSpectrum (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q))),
      Ideal.comap (algebraMap P (Localization.AtPrime q)) (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) x.asIdeal) ≤ q := by
    intro x z hz
    by_contra hzq
    rw [Ideal.mem_comap, Ideal.mem_comap] at hz
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hz
      ((IsLocalization.map_units (Localization.AtPrime q) (⟨z, hzq⟩ : q.primeCompl)).map (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q))))))
  apply le_antisymm
  · refine krullDim_le_height_lemma_3 (fun x => (⟨(Ideal.comap (algebraMap P (Localization.AtPrime q))
        (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) x.asIdeal)).map (Ideal.Quotient.mk p),
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
          (by rw [Ideal.mk_ker]; exact hpA x)⟩ : PrimeSpectrum (P ⧸ p))) ?_ _ ?_
    · intro x y hxy
      show (Ideal.comap (algebraMap P (Localization.AtPrime q)) (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) x.asIdeal)).map
          (Ideal.Quotient.mk p) < (Ideal.comap (algebraMap P (Localization.AtPrime q))
          (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) y.asIdeal)).map (Ideal.Quotient.mk p)
      refine lt_of_le_of_ne (Ideal.map_mono (Ideal.comap_mono (Ideal.comap_mono
        (show x.asIdeal ≤ y.asIdeal from hxy.le)))) fun e => hxy.ne ?_
      have e1 := congrArg (Ideal.comap (Ideal.Quotient.mk p)) e
      rw [comap_map_mk_lemma_4 _ _ (hpA x), comap_map_mk_lemma_4 _ _ (hpA y)] at e1
      have e2 := congrArg (Ideal.map (algebraMap P (Localization.AtPrime q))) e1
      rw [IsLocalization.map_comap (M := q.primeCompl) (S := Localization.AtPrime q),
        IsLocalization.map_comap (M := q.primeCompl) (S := Localization.AtPrime q)] at e2
      exact PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective e2)
    · intro x
      show _ ≤ q.map (Ideal.Quotient.mk p)
      exact Ideal.map_mono (hAq x)
  · have hpB : ∀ x : PrimeSpectrum (P ⧸ p), p ≤ Ideal.comap (Ideal.Quotient.mk p) x.asIdeal := by
      intro x z hz
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hz]
      exact x.asIdeal.zero_mem
    have hB : ∀ x : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)), Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal ≤ q := fun x =>
      (Ideal.comap_mono (show x.1.asIdeal ≤ q.map (Ideal.Quotient.mk p) from x.2)).trans
        (comap_map_mk_lemma_4 p q hpq).le
    have hdB : ∀ x : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)), Disjoint (q.primeCompl : Set P)
        (Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal : Set P) := fun x =>
      Set.disjoint_left.mpr fun z hz hzB => hz (hB x hzB)
    have hBprime : ∀ x : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)),
        ((Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal).map (algebraMap P (Localization.AtPrime q))).IsPrime :=
      fun x => IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ _ inferInstance (hdB x)
    have hCprime : ∀ x : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)), (((Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal).map
        (algebraMap P (Localization.AtPrime q))).map (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q))))).IsPrime := by
      intro x
      haveI := hBprime x
      exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact Ideal.map_mono (hpB x.1))
    let h : Set.Iic (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)) → PrimeSpectrum (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q))) := fun x => ⟨_, hCprime x⟩
    have hh : StrictMono h := by
      intro x y hxy
      show ((Ideal.comap (Ideal.Quotient.mk p) x.1.asIdeal).map (algebraMap P (Localization.AtPrime q))).map
          (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q)))) < ((Ideal.comap (Ideal.Quotient.mk p) y.1.asIdeal).map
          (algebraMap P (Localization.AtPrime q))).map (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q))))
      refine lt_of_le_of_ne (Ideal.map_mono (Ideal.map_mono (Ideal.comap_mono
        (show x.1.asIdeal ≤ y.1.asIdeal from hxy.le)))) fun e => hxy.ne ?_
      have e1 := congrArg (Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap P (Localization.AtPrime q))))) e
      rw [comap_map_mk_lemma_4 _ _ (Ideal.map_mono (hpB x.1)),
        comap_map_mk_lemma_4 _ _ (Ideal.map_mono (hpB y.1))] at e1
      have e2 := congrArg (Ideal.under P) e1
      rw [IsLocalization.comap_map_of_isPrime_disjoint (M := q.primeCompl) (S := Localization.AtPrime q)
          inferInstance (hdB x),
        IsLocalization.comap_map_of_isPrime_disjoint (M := q.primeCompl) (S := Localization.AtPrime q)
          inferInstance (hdB y)] at e2
      exact Subtype.ext (PrimeSpectrum.ext
        (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective e2))
    calc ((Order.height (⟨q.map (Ideal.Quotient.mk p), hQ⟩ : PrimeSpectrum (P ⧸ p)) : ℕ∞) :
          WithBot ℕ∞)
        ≤ (Order.height (h ⟨⟨q.map (Ideal.Quotient.mk p), hQ⟩, Set.mem_Iic.mpr le_rfl⟩) :
          WithBot ℕ∞) :=
          WithBot.coe_le_coe.mpr (height_le_height_Iic_lemma_2 _ h hh)
      _ ≤ Order.krullDim (PrimeSpectrum (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q)))) := height_le_krullDim_lemma_6 _

private theorem height_map_atPrime_lemma_5 {R : Type*} [CommRing R] (p q : Ideal R) [p.IsPrime]
    [q.IsPrime] (hpq : p ≤ q) [hp' : (p.map (algebraMap R (Localization.AtPrime q))).IsPrime] :
    (p.map (algebraMap R (Localization.AtPrime q))).height = p.height := by
  have hdisj : ∀ I : Ideal R, I ≤ q → Disjoint (q.primeCompl : Set R) (I : Set R) := fun I hI =>
    Set.disjoint_left.mpr fun x hx hxI => hx (hI hxI)
  rw [height_eq_order_height_lemma (p.map (algebraMap R (Localization.AtPrime q))),
    height_eq_order_height_lemma p]
  apply le_antisymm
  · let f : PrimeSpectrum (Localization.AtPrime q) → PrimeSpectrum R := fun x =>
      ⟨Ideal.comap (algebraMap R (Localization.AtPrime q)) x.asIdeal, inferInstance⟩
    have hf : StrictMono f := by
      intro x y hxy
      show Ideal.comap (algebraMap R (Localization.AtPrime q)) x.asIdeal <
        Ideal.comap (algebraMap R (Localization.AtPrime q)) y.asIdeal
      refine lt_of_le_of_ne (Ideal.comap_mono (show x.asIdeal ≤ y.asIdeal from hxy.le))
        fun e => hxy.ne ?_
      have e2 := congrArg (Ideal.map (algebraMap R (Localization.AtPrime q))) e
      rw [IsLocalization.map_comap (M := q.primeCompl) (S := Localization.AtPrime q),
        IsLocalization.map_comap (M := q.primeCompl) (S := Localization.AtPrime q)] at e2
      exact PrimeSpectrum.ext e2
    have hfp : f ⟨_, hp'⟩ = ⟨p, ‹p.IsPrime›⟩ := PrimeSpectrum.ext (by
      show Ideal.under R (p.map (algebraMap R (Localization.AtPrime q))) = p
      exact IsLocalization.comap_map_of_isPrime_disjoint (M := q.primeCompl)
        (S := Localization.AtPrime q) ‹p.IsPrime› (hdisj p hpq))
    have h := Order.height_le_height_apply_of_strictMono f hf ⟨_, hp'⟩
    rwa [hfp] at h
  · let g : Set.Iic (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum R) → PrimeSpectrum (Localization.AtPrime q) :=
      fun x => ⟨x.1.asIdeal.map (algebraMap R (Localization.AtPrime q)),
        IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ _ inferInstance
          (hdisj _ ((show x.1.asIdeal ≤ p from x.2).trans hpq))⟩
    have hg : StrictMono g := by
      intro x y hxy
      show x.1.asIdeal.map (algebraMap R (Localization.AtPrime q)) <
        y.1.asIdeal.map (algebraMap R (Localization.AtPrime q))
      refine lt_of_le_of_ne (Ideal.map_mono (show x.1.asIdeal ≤ y.1.asIdeal from hxy.le))
        fun e => hxy.ne ?_
      have e2 := congrArg (Ideal.under R) e
      rw [IsLocalization.comap_map_of_isPrime_disjoint (M := q.primeCompl)
          (S := Localization.AtPrime q) inferInstance
          (hdisj _ ((show x.1.asIdeal ≤ p from x.2).trans hpq)),
        IsLocalization.comap_map_of_isPrime_disjoint (M := q.primeCompl)
          (S := Localization.AtPrime q) inferInstance
          (hdisj _ ((show y.1.asIdeal ≤ p from y.2).trans hpq))] at e2
      exact Subtype.ext (PrimeSpectrum.ext e2)
    exact height_le_height_Iic_lemma_2 _ g hg

theorem IsCM.height_eq_height_add_height_map_quotient {P : Type*} [CommRing P] [IsLocalRing P]
    (h : IsCM P) (p q : Ideal P) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    q.height = p.height + (q.map (Ideal.Quotient.mk p)).height := by
  have hL := h.localization_atPrime q
  have hdisj : Disjoint (q.primeCompl : Set P) (p : Set P) :=
    Set.disjoint_left.mpr fun x hx hxp => hx (hpq hxp)
  haveI hp' : (p.map (algebraMap P (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hdisj
  have e := hL.height_add_ringKrullDim_quotient (p.map (algebraMap P (Localization.AtPrime q)))
  have e1 : (p.map (algebraMap P (Localization.AtPrime q))).height = p.height :=
    height_map_atPrime_lemma_5 p q hpq
  have e2 : ringKrullDim (Localization.AtPrime q) = q.height := by
    first
    | exact IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)
    | (haveI hqL : (q.map (algebraMap P (Localization.AtPrime q))).IsPrime :=
         IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ q ‹_›
           (Set.disjoint_left.mpr fun x hx hxq => hx hxq)
       rw [← height_map_atPrime_lemma_5 q q le_rfl,
         height_eq_order_height_lemma (q.map (algebraMap P (Localization.AtPrime q)))]
       apply le_antisymm
       · refine krullDim_le_height_lemma_3 id strictMono_id _ fun x => ?_
         show x.asIdeal ≤ q.map (algebraMap P (Localization.AtPrime q))
         rw [← IsLocalization.map_comap (M := q.primeCompl) (S := Localization.AtPrime q)
           x.asIdeal]
         refine Ideal.map_mono fun z hz => ?_
         by_contra hzq
         exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.mp hz)
           (IsLocalization.map_units (Localization.AtPrime q) (⟨z, hzq⟩ : q.primeCompl)))
       · exact height_le_krullDim_lemma_6 _)
  rw [ringKrullDim_localization_quotient_eq_height p q hpq, e1, e2] at e
  exact_mod_cast e.symm

end ReciprocityTheory.CA
