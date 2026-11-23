import Mathlib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.DimF

variable {A : Type*} [CommRing A]

theorem isPrime_map_mk {q M : Ideal A} [M.IsPrime] (h : q ≤ M) :
    (M.map (Ideal.Quotient.mk q)).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact h)

theorem comap_map_mk {q M : Ideal A} (h : q ≤ M) :
    (M.map (Ideal.Quotient.mk q)).comap (Ideal.Quotient.mk q) = M := by
  exact Ideal.comap_map_mk h

theorem finiteHeight_of_dim_lt_top {B : Type*} [CommRing B] (I : Ideal B) (hI : I ≠ ⊤)
    (h : ringKrullDim B < ⊤) : I.FiniteHeight := by
  refine Ideal.FiniteHeight.mk (Or.inr fun htop => ?_)
  have h1 := Ideal.height_le_ringKrullDim_of_ne_top hI
  rw [htop] at h1
  have h2 := lt_of_le_of_lt h1 h
  simp at h2

theorem height_add_height_map_le [IsNoetherianRing A] [FiniteRingKrullDim A] {q M : Ideal A}
    [q.IsPrime] [M.IsPrime] (h : q ≤ M) :
    q.height + (M.map (Ideal.Quotient.mk q)).height ≤ M.height := by
  have : (M.map (Ideal.Quotient.mk q)).IsPrime := isPrime_map_mk h
  have : (M.map (Ideal.Quotient.mk q)).FiniteHeight :=
    finiteHeight_of_dim_lt_top _ Ideal.IsPrime.ne_top'
      (lt_of_le_of_lt (ringKrullDim_quotient_le q) ringKrullDim_lt_top)
  obtain ⟨lp, hlp, hlenp⟩ := q.exists_ltSeries_length_eq_height
  obtain ⟨lq, hlq, hlenq⟩ := (M.map (Ideal.Quotient.mk q)).exists_ltSeries_length_eq_height
  let l' : LTSeries (PrimeSpectrum A) :=
    lq.map (PrimeSpectrum.comap (Ideal.Quotient.mk q))
      (RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective)
  have hlast : l'.last = ⟨M, ‹_›⟩ := by
    ext1
    simp only [l', LTSeries.last_map, hlq, PrimeSpectrum.comap_asIdeal]
    exact comap_map_mk h
  have hle : lp.last ≤ l'.head := by
    rw [hlp, ← PrimeSpectrum.asIdeal_le_asIdeal]
    simp only [l', LTSeries.head_map, PrimeSpectrum.comap_asIdeal]
    intro x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Ideal.zero_mem _
  rw [← hlenp, ← hlenq, ← Nat.cast_add, (⟨M, ‹_›⟩ : PrimeSpectrum A).height_eq_orderHeight]
  rcases eq_or_lt_of_le hle with e | lt
  · calc ((lp.length + lq.length : ℕ) : ℕ∞) = ((lp.smash l' e).length : ℕ∞) := by simp [l']
      _ ≤ _ := Order.length_le_height (by simp [hlast])
  · calc ((lp.length + lq.length : ℕ) : ℕ∞) ≤ ((lp.append l' lt).length : ℕ∞) := by
          simp [l']
      _ ≤ _ := Order.length_le_height (by simp [hlast])

theorem height_map_le_height_map {I q M : Ideal A} [q.IsPrime] [M.IsPrime] (hIq : I ≤ q)
    (hqM : q ≤ M) (H : ∀ P : Ideal A, P.IsPrime → I ≤ P → P ≤ M → q ≤ P) :
    (M.map (Ideal.Quotient.mk I)).height ≤ (M.map (Ideal.Quotient.mk q)).height := by
  have hMI : (M.map (Ideal.Quotient.mk I)).IsPrime := isPrime_map_mk (hIq.trans hqM)
  have hMq : (M.map (Ideal.Quotient.mk q)).IsPrime := isPrime_map_mk hqM
  rw [(⟨_, hMI⟩ : PrimeSpectrum (A ⧸ I)).height_eq_orderHeight,
    (⟨_, hMq⟩ : PrimeSpectrum (A ⧸ q)).height_eq_orderHeight]
  refine Order.height_le fun p hp => ?_
  have hbelow : ∀ i, (p i).asIdeal.comap (Ideal.Quotient.mk I) ≤ M := fun i => by
    have : p i ≤ p.last := p.monotone (Fin.le_last _)
    rw [hp, ← PrimeSpectrum.asIdeal_le_asIdeal] at this
    calc _ ≤ (M.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) := Ideal.comap_mono this
      _ = M := comap_map_mk (hIq.trans hqM)
  have hmem : ∀ i, q ≤ (p i).asIdeal.comap (Ideal.Quotient.mk I) := fun i => by
    refine H _ (Ideal.comap_isPrime _ _) ?_ (hbelow i)
    intro x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Ideal.zero_mem _
  let f : Fin (p.length + 1) → PrimeSpectrum (A ⧸ q) := fun i =>
    ⟨((p i).asIdeal.comap (Ideal.Quotient.mk I)).map (Ideal.Quotient.mk q), isPrime_map_mk (hmem i)⟩
  have step : ∀ i : Fin p.length, f i.castSucc < f i.succ := by
    intro i
    have h2 : (p i.castSucc).asIdeal.comap (Ideal.Quotient.mk I) <
        (p i.succ).asIdeal.comap (Ideal.Quotient.mk I) := by
      have := RingHom.strictMono_comap_of_surjective (f := Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective (p.step i)
      exact this
    refine lt_of_le_of_ne (Ideal.map_mono h2.le) fun e => h2.ne ?_
    have := congrArg (fun J => J.comap (Ideal.Quotient.mk q)) (congrArg PrimeSpectrum.asIdeal e)
    simpa [f, comap_map_mk (hmem _)] using this
  let p' : LTSeries (PrimeSpectrum (A ⧸ q)) := ⟨p.length, f, step⟩
  have : p'.last ≤ ⟨_, hMq⟩ := by
    rw [← PrimeSpectrum.asIdeal_le_asIdeal]
    exact Ideal.map_mono (hbelow _)
  exact Order.length_le_height this

theorem le_natSub_of_add_le {k n : ℕ} {x : ℕ∞} (h : (k : ℕ∞) + x ≤ n) : x ≤ ((n - k : ℕ) : ℕ∞) := by
  induction x using ENat.recTopCoe with
  | top => simp at h
  | coe m =>
    have h1 : k + m ≤ n := by exact_mod_cast h
    exact_mod_cast (by omega : m ≤ n - k)

theorem dim_quot_add_height [IsNoetherianRing A] [IsJacobsonRing A] [FiniteRingKrullDim A]
    (hA : ∀ M N : Ideal A, M.IsMaximal → N.IsMaximal → M.height = N.height) (q : Ideal A)
    [q.IsPrime] : ringKrullDim (A ⧸ q) + (q.height : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨M₀, hM₀, hqM₀⟩ := Ideal.exists_le_maximal q Ideal.IsPrime.ne_top'
  set N := M₀.height with hN
  have hNtop : N ≠ ⊤ := Ideal.height_ne_top_of_isPrime
  have hqtop : q.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
  set n := N.toNat
  set k := q.height.toNat
  have hn : N = n := (ENat.natCast_toNat hNtop).symm
  have hk : q.height = k := (ENat.natCast_toNat hqtop).symm
  have hmax : ∀ M : Ideal A, M.IsMaximal → M.height = n := fun M hM => hn ▸ hA M M₀ hM hM₀

  have hdimA : ringKrullDim A = n := by
    refine le_antisymm ((ringKrullDim_le_iff_isMaximal_height_le _).mpr fun M hM => ?_) ?_
    · rw [hmax M hM]; rfl
    · have := Ideal.height_le_ringKrullDim_of_ne_top (I := M₀) Ideal.IsPrime.ne_top'
      rwa [hmax M₀ hM₀] at this

  have hup : ringKrullDim (A ⧸ q) ≤ ((n - k : ℕ) : WithBot ℕ∞) := by
    refine (ringKrullDim_le_iff_isMaximal_height_le _).mpr fun Mb hMb => ?_
    set M := Mb.comap (Ideal.Quotient.mk q)
    have hM : M.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have hqM : q ≤ M := fun x hx => by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact Ideal.zero_mem _
    have hMb' : Mb = M.map (Ideal.Quotient.mk q) :=
      (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Mb).symm
    have h1 := height_add_height_map_le (q := q) (M := M) hqM
    rw [← hMb', hmax M hM, hk] at h1
    have h2 := le_natSub_of_add_le h1
    have h3 : ((Mb.height : ℕ∞) : WithBot ℕ∞) ≤ (((n - k : ℕ) : ℕ∞) : WithBot ℕ∞) :=
      WithBot.coe_le_coe.mpr h2
    exact h3.trans_eq (by norm_cast)

  have hlow : ((n - k : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ q) := by
    obtain ⟨s, hs, hcard⟩ := Ideal.exists_finset_card_eq_height_of_isNoetherianRing q
    set I := Ideal.span (s : Set A)
    have hIq : I ≤ q := hs.1.2
    have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing A I
    classical
    set T := hfin.toFinset.erase q
    have hT : ¬ T.inf id ≤ q := by
      rw [Ideal.IsPrime.inf_le' inferInstance]
      rintro ⟨P, hPT, hPq⟩
      have hP : P ∈ I.minimalPrimes := hfin.mem_toFinset.mp (Finset.mem_of_mem_erase hPT)
      have : q ≤ P := hs.2 hP.1 hPq
      exact Finset.ne_of_mem_erase hPT (le_antisymm hPq this)
    obtain ⟨g, hgT, hgq⟩ := SetLike.not_le_iff_exists.mp hT
    have hjac : q.jacobson = q := IsJacobsonRing.out' q (Ideal.IsPrime.isRadical inferInstance)
    rw [← hjac, Ideal.jacobson, Submodule.mem_sInf] at hgq
    push Not at hgq
    obtain ⟨M, ⟨hqM, hM⟩, hgM⟩ := hgq
    have hH : ∀ P : Ideal A, P.IsPrime → I ≤ P → P ≤ M → q ≤ P := by
      intro P hP hIP hPM
      obtain ⟨P', hP', hP'P⟩ := Ideal.exists_minimalPrimes_le hIP
      by_cases e : P' = q
      · exact e ▸ hP'P
      · have hP'T : P' ∈ T := Finset.mem_erase.mpr ⟨e, hfin.mem_toFinset.mpr hP'⟩
        exact absurd (hP'P.trans hPM (Finset.inf_le (f := id) hP'T hgT)) hgM
    have hsM : (s : Set A) ⊆ M := fun x hx => hqM (hIq (Ideal.subset_span hx))
    have hkr := Ideal.height_le_height_add_encard_of_subset (s : Set A) hsM
    rw [Set.encard_coe_eq_coe_finsetCard, hmax M hM, hcard, hk] at hkr
    have hq1 := height_map_le_height_map (I := I) (q := q) (M := M) hIq hqM hH
    have h2 : (n : ℕ∞) ≤ (Ideal.map (Ideal.Quotient.mk q) M).height + k :=
      hkr.trans (add_le_add hq1 le_rfl)
    have h3 : ((n - k : ℕ) : ℕ∞) ≤ (Ideal.map (Ideal.Quotient.mk q) M).height := by
      induction h : (Ideal.map (Ideal.Quotient.mk q) M).height using ENat.recTopCoe with
      | top => exact le_top
      | coe y =>
        rw [h] at h2
        have : n ≤ y + k := by exact_mod_cast h2
        exact_mod_cast (by omega : n - k ≤ y)
    have : (Ideal.map (Ideal.Quotient.mk q) M).IsPrime := isPrime_map_mk hqM
    calc ((n - k : ℕ) : WithBot ℕ∞) ≤ ((Ideal.map (Ideal.Quotient.mk q) M).height : WithBot ℕ∞) := by
          rw [← WithBot.coe_natCast]; exact WithBot.coe_le_coe.mpr h3
      _ ≤ _ := Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  have hkn : k ≤ n := by
    have := height_add_height_map_le (q := q) (M := M₀) hqM₀
    rw [hmax M₀ hM₀, hk] at this
    have h' : (k : ℕ∞) ≤ n := le_trans le_self_add this
    exact_mod_cast h'
  rw [le_antisymm hup hlow, hdimA, hk]
  rw [WithBot.coe_natCast, ← Nat.cast_add, Nat.sub_add_cancel hkn]

end ReciprocityTheory.ChartRestriction.G.Geo.DimF
