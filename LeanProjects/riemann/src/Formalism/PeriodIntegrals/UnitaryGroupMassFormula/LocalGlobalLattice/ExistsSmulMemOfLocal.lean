import Formalism.PeriodIntegrals.LatLocGlob
import Lemmata.GeneralBFactThirdBisAlt.Imports

noncomputable section

namespace PI.LatLocGlob.Proof

open PI.LatLocGlob

section General

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]

theorem mem_loc {p : Ideal R} {N : Submodule R V} {x : V} :
    x ∈ loc p N ↔ ∃ s : R, s ∉ p ∧ s • x ∈ N := Iff.rfl

def locSub (p : Ideal R) (hp : p.IsPrime) (N : Submodule R V) : Submodule R V where
  carrier := loc p N
  add_mem' := by
    intro x y hx hy
    obtain ⟨s, hs, hsx⟩ := mem_loc.1 hx
    obtain ⟨t, ht, hty⟩ := mem_loc.1 hy
    refine mem_loc.2 ⟨s * t, fun h => (hp.mem_or_mem h).elim hs ht, ?_⟩
    rw [smul_add, mul_smul s t y, mul_comm s t, mul_smul t s x]
    exact N.add_mem (N.smul_mem t hsx) (N.smul_mem s hty)
  zero_mem' := mem_loc.2 ⟨1, (Ideal.ne_top_iff_one p).1 hp.ne_top, by simp⟩
  smul_mem' := by
    intro c x hx
    obtain ⟨s, hs, hsx⟩ := mem_loc.1 hx
    refine mem_loc.2 ⟨s, hs, ?_⟩
    rw [smul_comm s c x]
    exact N.smul_mem c hsx

theorem mem_locSub {p : Ideal R} {hp : p.IsPrime} {N : Submodule R V} {x : V} :
    x ∈ locSub p hp N ↔ x ∈ loc p N := Iff.rfl

theorem mem_loc_of_mem {p : Ideal R} (hp : p ≠ ⊤) {N : Submodule R V} {x : V} (hx : x ∈ N) :
    x ∈ loc p N :=
  mem_loc.2 ⟨1, (Ideal.ne_top_iff_one p).1 hp, by simpa using hx⟩

theorem mem_loc_of_smul {p : Ideal R} (hp : p.IsPrime) {N : Submodule R V} {u : R} {y : V}
    (hu : u ∉ p) (h : u • y ∈ loc p N) : y ∈ loc p N := by
  obtain ⟨s, hs, hsy⟩ := mem_loc.1 h
  exact mem_loc.2 ⟨s * u, fun h' => (hp.mem_or_mem h').elim hs hu, by rwa [mul_smul]⟩

theorem mem_of_forall_loc (N : Submodule R V) (x : V)
    (h : ∀ p : Ideal R, p.IsMaximal → x ∈ loc p N) : x ∈ N := by
  let I : Ideal R := N.comap (LinearMap.toSpanSingleton R V x)
  have hI : ∀ r, r ∈ I ↔ r • x ∈ N := fun r => by simp [I]
  by_cases htop : I = ⊤
  · have h1 : (1 : R) ∈ I := by rw [htop]; exact Submodule.mem_top
    simpa using (hI 1).1 h1
  · obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I htop
    obtain ⟨s, hs, hsx⟩ := mem_loc.1 (h p hp)
    exact absurd (hIp ((hI s).2 hsx)) hs

end General

theorem commonMult {R ι : Type} [CommRing R] [IsDomain R] (P : ι → R → Prop)
    (hP : ∀ i c d, P i c → P i (d * c)) (T : Finset ι)
    (hT : ∀ i ∈ T, ∃ c : R, c ≠ 0 ∧ P i c) : ∃ c : R, c ≠ 0 ∧ ∀ i ∈ T, P i c := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert a T ha ih =>
    obtain ⟨c, hc, hPc⟩ := ih (fun i hi => hT i (Finset.mem_insert_of_mem hi))
    obtain ⟨ca, hca, hPa⟩ := hT a (Finset.mem_insert_self a T)
    refine ⟨c * ca, mul_ne_zero hc hca, ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hP _ _ _ hPa
    · rw [mul_comm]; exact hP _ _ _ (hPc i hi)

section Frac

variable {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem exists_smul_mem (N : Submodule R V) {v : V} (hv : v ∈ Submodule.span K (N : Set V)) :
    ∃ c : R, c ≠ 0 ∧ c • v ∈ N := by
  first | exact Bl.general_b_fact_third_bis_other.goal1 .. | (apply Bl.general_b_fact_third_bis_other.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_bis_other.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_bis_other.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_third_bis_other.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_bis_other.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› N v hv | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› N v | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› N | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› ‹_› | exact @Bl.general_b_fact_third_bis_other.goal1 R K V ‹_› | exact @Bl.general_b_fact_third_bis_other.goal1 R K V | exact @Bl.general_b_fact_third_bis_other.goal1 R K | exact @Bl.general_b_fact_third_bis_other.goal1 R

theorem exists_smul_le {N N' : Submodule R V} (hN : N.FG)
    (hN' : Submodule.span K (N' : Set V) = ⊤) : ∃ c : R, c ≠ 0 ∧ ∀ x ∈ N, c • x ∈ N' := by
  obtain ⟨s, rfl⟩ := hN
  obtain ⟨c, hc, hcs⟩ := commonMult (fun (g : V) (c : R) => c • g ∈ N')
    (fun g c d h => by rw [mul_smul]; exact N'.smul_mem d h) s
    (fun g _ => exists_smul_mem (K := K) N' (by rw [hN']; exact Submodule.mem_top))
  refine ⟨c, hc, fun x hx => ?_⟩
  have hle : Submodule.span R (s : Set V) ≤ N'.comap (c • LinearMap.id) := by
    rw [Submodule.span_le]
    intro g hg
    simpa using hcs g hg
  simpa using hle hx

end Frac

section DedekindLFunctions

variable {R V : Type} [CommRing R] [IsDedekindDomain R] [AddCommGroup V] [Module R V]

theorem exists_smul_mem_of_local (W : Ideal R → Set V) (L : Submodule R V)
    (hL : ∀ y, y ∈ L ↔ ∀ q : Ideal R, q.IsMaximal → y ∈ W q)
    (hWsmul : ∀ q : Ideal R, q.IsMaximal → ∀ (r : R) (y : V), y ∈ W q → r • y ∈ W q)
    (hWsat : ∀ q : Ideal R, q.IsMaximal → ∀ (u : R) (y : V), u ∉ q → u • y ∈ W q → y ∈ W q)
    {p : Ideal R} (hp : p.IsMaximal) {x : V} (hx : x ∈ W p) {d : R} (hd : d ≠ 0)
    (hdx : d • x ∈ L) : ∃ s : R, s ∉ p ∧ s • x ∈ L := by
  classical
  by_cases hdp : d ∈ p
  swap
  · exact ⟨d, hdp, hdx⟩
  have hpbot : p ≠ ⊥ := fun h => hd (by rw [h] at hdp; simpa using hdp)
  have hnf : ¬ IsField R := by
    rw [Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top]
    exact ⟨p, bot_lt_iff_ne_bot.2 hpbot, lt_top_iff_ne_top.2 hp.ne_top⟩
  let I : Ideal R := L.comap (LinearMap.toSpanSingleton R V x)
  have hI : ∀ r, r ∈ I ↔ r • x ∈ L := fun r => by simp [I]
  have hI0 : I ≠ ⊥ := by
    intro h
    have h1 := (hI d).2 hdx
    rw [h] at h1
    exact hd (by simpa using h1)
  obtain ⟨Z, hZle, hZne⟩ := PrimeSpectrum.exists_primeSpectrum_prod_le_and_ne_bot_of_domain hnf hI0
  have key : ∀ Y : Multiset (Ideal R), (∀ P ∈ Y, P.IsPrime ∧ P ≠ ⊥) →
      ∀ y ∈ W p, (∀ r ∈ Y.prod, r • y ∈ L) → ∃ s : R, s ∉ p ∧ s • y ∈ L := by
    intro Y
    induction Y using Multiset.induction_on with
    | empty =>
      intro _ y _ hy
      refine ⟨1, (Ideal.ne_top_iff_one p).1 hp.ne_top, hy 1 ?_⟩
      simp
    | cons P Y ih =>
      intro hPY y hyp hy
      have hP := hPY P (Multiset.mem_cons.2 (Or.inl rfl))
      have hPmax : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP.2 hP.1
      have hY' : ∀ Q ∈ Y, Q.IsPrime ∧ Q ≠ ⊥ := fun Q hQ => hPY Q (Multiset.mem_cons.2 (Or.inr hQ))
      rw [Multiset.prod_cons] at hy
      by_cases hPp : P = p
      · apply ih hY' y hyp
        intro r hr
        rw [hL]
        intro q hq
        by_cases hqp : q = p
        · rw [hqp]; exact hWsmul p hp r y hyp
        · obtain ⟨t, htP, htq⟩ : ∃ t ∈ P, t ∉ q := by
            by_contra h
            push Not at h
            exact hqp ((hPmax.eq_of_le hq.ne_top (fun t ht => h t ht)).symm.trans hPp)
          have h1 := (hL _).1 (hy (t * r) (Ideal.mul_mem_mul htP hr)) q hq
          rw [mul_smul] at h1
          exact hWsat q hq t _ htq h1
      · obtain ⟨a, haP, hap⟩ : ∃ a ∈ P, a ∉ p := by
          by_contra h
          push Not at h
          exact hPp (hPmax.eq_of_le hp.ne_top (fun t ht => h t ht))
        obtain ⟨s, hs, hsy⟩ := ih hY' (a • y) (hWsmul p hp a y hyp) (fun r hr => by
          have h1 := hy (a * r) (Ideal.mul_mem_mul haP hr)
          rwa [mul_comm, mul_smul] at h1)
        refine ⟨s * a, fun h => (hp.isPrime.mem_or_mem h).elim hs hap, ?_⟩
        rwa [mul_smul]
  apply key (Z.map PrimeSpectrum.asIdeal) _ x hx
  · intro r hr
    exact (hI r).1 (hZle hr)
  · intro P hP
    obtain ⟨P', _, rfl⟩ := Multiset.mem_map.1 hP
    refine ⟨P'.isPrime, fun h => hZne ?_⟩
    have h0 : (0 : Ideal R) ∈ Z.map PrimeSpectrum.asIdeal := by
      rw [Ideal.zero_eq_bot, ← h]; exact hP
    rw [← Ideal.zero_eq_bot]
    exact Multiset.prod_eq_zero h0

end DedekindLFunctions

section Main

variable {R K V : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem exists_unique_lat (L0 : Submodule R V) (hL0 : IsFullLat K L0) (M : Ideal R → Set V)
    (hM : ∀ p : Ideal R, p.IsMaximal → ∃ N : Submodule R V, IsFullLat K N ∧ M p = loc p N)
    (hfin : Set.Finite {p : Ideal R | p.IsMaximal ∧ M p ≠ loc p L0}) :
    ∃! L : Submodule R V, IsFullLat K L ∧ ∀ p : Ideal R, p.IsMaximal → loc p L = M p := by
  classical
  obtain ⟨hL0fg, hL0sp⟩ := hL0
  choose! N hNfull hMN using hM
  have hMsmul : ∀ q : Ideal R, q.IsMaximal → ∀ (r : R) (y : V), y ∈ M q → r • y ∈ M q := by
    intro q hq r y hy
    rw [hMN q hq] at hy ⊢
    exact mem_locSub.1 ((locSub q hq.isPrime (N q)).smul_mem r (mem_locSub.2 hy))
  have hMsat : ∀ q : Ideal R, q.IsMaximal → ∀ (u : R) (y : V), u ∉ q → u • y ∈ M q → y ∈ M q := by
    intro q hq u y hu h
    rw [hMN q hq] at h ⊢
    exact mem_loc_of_smul hq.isPrime hu h
  let L : Submodule R V := ⨅ q : {q : Ideal R // q.IsMaximal}, locSub q.1 q.2.isPrime (N q.1)
  have hL : ∀ x, x ∈ L ↔ ∀ q : Ideal R, q.IsMaximal → x ∈ M q := by
    intro x
    simp only [L, Submodule.mem_iInf, mem_locSub]
    constructor
    · intro h q hq
      rw [hMN q hq]
      exact h ⟨q, hq⟩
    · intro h q
      rw [← hMN q.1 q.2]
      exact h q.1 q.2
  obtain ⟨c1, hc1, hc1N⟩ := commonMult (fun (q : Ideal R) (c : R) => ∀ y ∈ N q, c • y ∈ L0)
    (fun q c d h y hy => by rw [mul_smul]; exact L0.smul_mem d (h y hy)) hfin.toFinset
    (fun q hq => by
      have hq' : q.IsMaximal ∧ M q ≠ loc q L0 := (Set.Finite.mem_toFinset hfin).1 hq
      obtain ⟨hfg, _⟩ := hNfull q hq'.1
      exact exists_smul_le (K := K) hfg hL0sp)
  obtain ⟨c2, hc2, hc2N⟩ := commonMult (fun (q : Ideal R) (c : R) => ∀ y ∈ L0, c • y ∈ N q)
    (fun q c d h y hy => by rw [mul_smul]; exact (N q).smul_mem d (h y hy)) hfin.toFinset
    (fun q hq => by
      have hq' : q.IsMaximal ∧ M q ≠ loc q L0 := (Set.Finite.mem_toFinset hfin).1 hq
      obtain ⟨_, hsp⟩ := hNfull q hq'.1
      exact exists_smul_le (K := K) hL0fg hsp)
  have hLc1 : ∀ x ∈ L, c1 • x ∈ L0 := by
    intro x hx
    apply mem_of_forall_loc
    intro q hq
    have hxq := (hL x).1 hx q hq
    by_cases hqS : M q = loc q L0
    · rw [hqS] at hxq
      exact mem_locSub.1 ((locSub q hq.isPrime L0).smul_mem c1 (mem_locSub.2 hxq))
    · rw [hMN q hq] at hxq
      obtain ⟨s, hs, hsx⟩ := mem_loc.1 hxq
      refine mem_loc.2 ⟨s, hs, ?_⟩
      rw [smul_comm]
      exact hc1N q ((Set.Finite.mem_toFinset hfin).2 ⟨hq, hqS⟩) _ hsx
  have hLc2 : ∀ y ∈ L0, c2 • y ∈ L := by
    intro y hy
    rw [hL]
    intro q hq
    by_cases hqS : M q = loc q L0
    · rw [hqS]
      exact mem_loc_of_mem hq.ne_top (L0.smul_mem c2 hy)
    · rw [hMN q hq]
      exact mem_loc_of_mem hq.ne_top (hc2N q ((Set.Finite.mem_toFinset hfin).2 ⟨hq, hqS⟩) y hy)
  have hLfg : L.FG := by
    let f : V →ₗ[R] V := c1 • LinearMap.id
    have hK1 : algebraMap R K c1 ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hc1
    have hf : Function.Injective f := fun v w h => by
      have h' : c1 • v = c1 • w := by simpa only [f, LinearMap.smul_apply, LinearMap.id_apply] using h
      have h'' : algebraMap R K c1 • v = algebraMap R K c1 • w := by
        rw [algebraMap_smul, algebraMap_smul]; exact h'
      exact (smul_right_inj hK1).1 h''
    refine Submodule.fg_of_fg_map_injective (f := f) hf ?_
    refine Submodule.FG.of_le hL0fg ?_
    rintro _ ⟨x, hx, rfl⟩
    simpa [f] using hLc1 x hx
  have hLspan : Submodule.span K (L : Set V) = ⊤ := by
    rw [eq_top_iff, ← hL0sp, Submodule.span_le]
    intro y hy
    have hK : algebraMap R K c2 ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hc2
    have h1 : c2 • y ∈ Submodule.span K (L : Set V) := Submodule.subset_span (hLc2 y hy)
    have h2 := Submodule.smul_mem _ (algebraMap R K c2)⁻¹ h1
    rwa [← algebraMap_smul K c2 y, inv_smul_smul₀ hK] at h2
  have hLfull : IsFullLat K L := by
    unfold IsFullLat
    exact ⟨hLfg, hLspan⟩
  have hloc : ∀ p : Ideal R, p.IsMaximal → loc p L = M p := by
    intro p hp
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hsx⟩ := mem_loc.1 hx
      exact hMsat p hp s x hs ((hL _).1 hsx p hp)
    · intro hx
      obtain ⟨d, hd, hdx⟩ := exists_smul_mem (K := K) L (v := x) (by rw [hLspan]; exact Submodule.mem_top)
      obtain ⟨s, hs, hsx⟩ := exists_smul_mem_of_local M L hL hMsmul hMsat hp hx hd hdx
      exact mem_loc.2 ⟨s, hs, hsx⟩
  refine ExistsUnique.intro L ⟨hLfull, hloc⟩ ?_
  rintro L' ⟨_, hloc'⟩
  ext x
  constructor
  · intro hx
    rw [hL]
    intro q hq
    rw [← hloc' q hq]
    exact mem_loc_of_mem hq.ne_top hx
  · intro hx
    apply mem_of_forall_loc L' x
    intro q hq
    rw [hloc' q hq]
    exact (hL x).1 hx q hq

end Main

theorem latLocGlob_core : LatLocGlob := by
  intro R K V _ _ _ _ _ _ _ _ _ _ L0 hL0 M hM hfin
  exact exists_unique_lat L0 hL0 M hM hfin

end PI.LatLocGlob.Proof
