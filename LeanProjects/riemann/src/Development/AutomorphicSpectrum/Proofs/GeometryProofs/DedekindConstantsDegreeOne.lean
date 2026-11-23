import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsChartBundle
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ChartRingLocalizationMembershipStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatChart

open GlobalTheory.CompanionTheory.Ar.ChartTie (unitAt_of_mul smul_mem_lat coord_mem exists_coords frame_mem)

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E] {R : Subring Ω} {T : Set (Cpt ξ)}

theorem exists_pow_mul_mem
    (hprime : ∀ P : Ideal R, P.IsPrime → ∃ q ∈ T, ∀ s : R, s ∉ P ↔ unitAt ξ q (s : Ω))
    (hfrac : ∀ q ∈ T, ∀ a ∈ regAt ξ q, ∃ s ∈ R, unitAt ξ q s ∧ s * a ∈ R)
    {f a : Ω} (hf : f ∈ R) (ha : ∀ q ∈ T, unitAt ξ q f → a ∈ regAt ξ q) : ∃ n : ℕ, f ^ n * a ∈ R := by
  classical
  let J : Ideal R :=
    { carrier := {s | (s : Ω) * a ∈ R}
      add_mem' := fun {s t} hs ht => by
        show ((s + t : R) : Ω) * a ∈ R
        have := add_mem (show (s : Ω) * a ∈ R from hs) (show (t : Ω) * a ∈ R from ht)
        simpa [add_mul] using this
      zero_mem' := by
        show ((0 : R) : Ω) * a ∈ R
        simp
      smul_mem' := fun b s hs => by
        show ((b * s : R) : Ω) * a ∈ R
        have := mul_mem b.2 (show (s : Ω) * a ∈ R from hs)
        simpa [_root_.mul_assoc] using this }
  have hmem : (⟨f, hf⟩ : R) ∈ J.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hJP, hP⟩
    by_contra hfP
    obtain ⟨q, hq, hu⟩ := hprime P hP
    obtain ⟨s, hs, hsu, hsa⟩ := hfrac q hq a (ha q hq ((hu ⟨f, hf⟩).1 hfP))
    have hsJ : (⟨s, hs⟩ : R) ∈ J := hsa
    exact (hu ⟨s, hs⟩).2 hsu (hJP hsJ)
  obtain ⟨n, hn⟩ := hmem
  have hn' : (((⟨f, hf⟩ : R) ^ n : R) : Ω) * a ∈ R := hn
  exact ⟨n, by simpa using hn'⟩

theorem mem_of_forall_regAt
    (hprime : ∀ P : Ideal R, P.IsPrime → ∃ q ∈ T, ∀ s : R, s ∉ P ↔ unitAt ξ q (s : Ω))
    (hfrac : ∀ q ∈ T, ∀ a ∈ regAt ξ q, ∃ s ∈ R, unitAt ξ q s ∧ s * a ∈ R)
    {a : Ω} (ha : ∀ q ∈ T, a ∈ regAt ξ q) : a ∈ R := by
  obtain ⟨n, hn⟩ := exists_pow_mul_mem hprime hfrac (one_mem R) (a := a) fun q hq _ => ha q hq
  simpa using hn

theorem exists_cover
    (hprime : ∀ P : Ideal R, P.IsPrime → ∃ q ∈ T, ∀ s : R, s ∉ P ↔ unitAt ξ q (s : Ω))
    (hbasic : ∀ q ∈ T, ∀ V : X.Opens, q.1 ∈ V →
      ∃ f ∈ R, unitAt ξ q f ∧ ∀ q' ∈ T, unitAt ξ q' f → q'.1 ∈ V)
    (Q : X.Opens → Prop) (hQ : ∀ q ∈ T, ∃ V : X.Opens, q.1 ∈ V ∧ Q V) :
    ∃ (k : ℕ) (f g : Fin k → Ω), (∀ l, f l ∈ R) ∧ (∀ l, g l ∈ R) ∧ ∑ l, g l * f l = 1 ∧
      ∀ l, ∃ V : X.Opens, Q V ∧ ∀ q ∈ T, unitAt ξ q (f l) → q.1 ∈ V := by
  classical
  let S : Set R := {f | ∃ V : X.Opens, Q V ∧ ∀ q ∈ T, unitAt ξ q (f : Ω) → q.1 ∈ V}
  have htop : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨q, hq, hu⟩ := hprime m hm.isPrime
    obtain ⟨V, hqV, hQV⟩ := hQ q hq
    obtain ⟨f, hf, hfu, hfV⟩ := hbasic q hq V hqV
    exact (hu ⟨f, hf⟩).2 hfu (hle (Ideal.subset_span ⟨V, hQV, hfV⟩))
  obtain ⟨s, hsT, hs⟩ := (Ideal.span_eq_top_iff_finite S).1 htop
  let e := s.equivFin
  have h1 : (1 : R) ∈ Ideal.span (Set.range fun l : Fin s.card => ((e.symm l : s) : R)) := by
    have hr : (Set.range fun l : Fin s.card => ((e.symm l : s) : R)) = (s : Set R) := by
      ext y
      constructor
      · rintro ⟨l, rfl⟩
        exact (e.symm l).2
      · intro hy
        exact ⟨e ⟨y, hy⟩, by simp⟩
    rw [hr, hs]
    trivial
  obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.1 h1
  refine ⟨s.card, fun l => (((e.symm l : s) : R) : Ω), fun l => (g l : Ω), fun l => ((e.symm l : s) : R).2,
    fun l => (g l).2, ?_, fun l => hsT (e.symm l).2⟩
  have h2 := congrArg (Subtype.val) hg
  simpa using h2

theorem exists_unitAt (hgen : IsCptGen ξ) (hle : ∀ q ∈ T, R ≤ regAt ξ q)
    {k : ℕ} {f g : Fin k → Ω} (hf : ∀ l, f l ∈ R)
    (hg : ∀ l, g l ∈ R) (hsum : ∑ l, g l * f l = 1) {p : Cpt ξ} (hp : p ∈ T) :
    ∃ l, unitAt ξ p (f l) := by
  obtain ⟨hloc, -, -⟩ := regAt_isLocalRing_isFractionRing_stalk X Ω ξ hgen p
  by_contra hno
  let ff : Fin k → regAt ξ p := fun l => ⟨f l, hle p hp (hf l)⟩
  let gg : Fin k → regAt ξ p := fun l => ⟨g l, hle p hp (hg l)⟩
  have h1 : ∑ l, gg l * ff l = 1 := Subtype.ext (by simpa [ff, gg] using hsum)
  have hmem : (1 : regAt ξ p) ∈ IsLocalRing.maximalIdeal (regAt ξ p) := by
    rw [← h1]
    refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_)
    obtain ⟨t, ht⟩ := hu.exists_right_inv
    have ht' : f l * (t : Ω) = 1 := congrArg Subtype.val ht
    refine hno ⟨l, left_ne_zero_of_mul_eq_one ht', (ff l).2, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right ht']
    exact t.2
  exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top hmem

def FrameOpen (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (V : X.Opens) : Prop :=
  ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
    ∀ q ∈ T, q.1 ∈ V → L.IsFrameAt b q

theorem exists_pow_smul_sec (hgen : IsCptGen ξ) (hle : ∀ q ∈ T, R ≤ regAt ξ q)
    (hprime : ∀ P : Ideal R, P.IsPrime → ∃ q ∈ T, ∀ s : R, s ∉ P ↔ unitAt ξ q (s : Ω))
    (hfrac : ∀ q ∈ T, ∀ a ∈ regAt ξ q, ∃ s ∈ R, unitAt ξ q s ∧ s * a ∈ R)
    (hbasic : ∀ q ∈ T, ∀ V : X.Opens, q.1 ∈ V →
      ∃ f ∈ R, unitAt ξ q f ∧ ∀ q' ∈ T, unitAt ξ q' f → q'.1 ∈ V)
    {L : Lat ξ E} {r : ℕ} (hv : ∀ q ∈ T, ∃ V : X.Opens, q.1 ∈ V ∧ FrameOpen L T r V)
    {f : Ω} (hf : f ∈ R) {e : E} (he : ∀ p ∈ T, unitAt ξ p f → e ∈ L p) :
    ∃ N : ℕ, ∀ p ∈ T, f ^ N • e ∈ L p := by
  obtain ⟨k, g, d, hg, hd, hsum, hl⟩ := exists_cover hprime hbasic (FrameOpen L T r) hv
  have key : ∀ l, ∃ N : ℕ, ∀ p ∈ T, unitAt ξ p (g l) → f ^ N • e ∈ L p := by
    intro l
    obtain ⟨V, ⟨b, hb, hspan, hfr⟩, hV⟩ := hl l
    obtain ⟨a, hae⟩ := exists_coords hspan e
    have h1 : ∀ q, ∃ n : ℕ, (f * g l) ^ n * a q ∈ R := fun q =>
      exists_pow_mul_mem hprime hfrac (mul_mem hf (hg l)) fun p hp hu => by
        have hfp := hle p hp hf
        have hgp := hle p hp (hg l)
        have huf : unitAt ξ p f := unitAt_of_mul hfp hgp hu
        have hug : unitAt ξ p (g l) := unitAt_of_mul hgp hfp (by rwa [mul_comm])
        have hmem := he p hp huf
        rw [(hfr p hp (hV p hp hug)).2, hae] at hmem
        exact coord_mem hb hmem q
    choose n hn using h1
    refine ⟨∑ q, n q, fun p hp hu => ?_⟩
    have hg0 : g l ≠ 0 := hu.1
    have hfrp := hfr p hp (hV p hp hu)
    rw [hae, Finset.smul_sum]
    refine sum_mem fun q _ => ?_
    have hle' : n q ≤ ∑ q, n q := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    have hA : (f * g l) ^ (∑ q, n q) * a q ∈ R := by
      have e1 : (f * g l) ^ (∑ q, n q) * a q =
          (f * g l) ^ (∑ q, n q - n q) * ((f * g l) ^ n q * a q) := by
        rw [← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel hle']
      rw [e1]
      exact mul_mem (pow_mem (mul_mem hf (hg l)) _) (hn q)
    have e2 : f ^ (∑ q, n q) • a q • b q =
        (((g l)⁻¹) ^ (∑ q, n q) * ((f * g l) ^ (∑ q, n q) * a q)) • b q := by
      rw [smul_smul]
      congr 1
      rw [mul_pow, inv_pow]
      field_simp
    rw [e2]
    exact smul_mem_lat L (mul_mem (pow_mem hu.2.2 _) (hle p hp hA)) (frame_mem hfrp q)
  choose N hN using key
  refine ⟨∑ l, N l, fun p hp => ?_⟩
  obtain ⟨l, hl'⟩ := exists_unitAt hgen hle hg hd hsum hp
  have hle' : N l ≤ ∑ l, N l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  have e1 : f ^ (∑ l, N l) • e = f ^ (∑ l, N l - N l) • f ^ N l • e := by
    rw [smul_smul, ← pow_add, Nat.sub_add_cancel hle']
  rw [e1]
  exact smul_mem_lat L (pow_mem (hle p hp hf) _) (hN l p hp hl')

def sec (L : Lat ξ E) (T : Set (Cpt ξ)) : AddSubgroup E where
  carrier := {e | ∀ p ∈ T, e ∈ L p}
  add_mem' ha hb p hp := add_mem (ha p hp) (hb p hp)
  zero_mem' _ _ := zero_mem _
  neg_mem' ha p hp := neg_mem (ha p hp)

theorem mem_sec {L : Lat ξ E} {e : E} : e ∈ sec L T ↔ ∀ p ∈ T, e ∈ L p := Iff.rfl

theorem exists_frames (hgen : IsCptGen ξ) (hle : ∀ q ∈ T, R ≤ regAt ξ q)
    (hprime : ∀ P : Ideal R, P.IsPrime → ∃ q ∈ T, ∀ s : R, s ∉ P ↔ unitAt ξ q (s : Ω))
    (hfrac : ∀ q ∈ T, ∀ a ∈ regAt ξ q, ∃ s ∈ R, unitAt ξ q s ∧ s * a ∈ R)
    (hbasic : ∀ q ∈ T, ∀ V : X.Opens, q.1 ∈ V →
      ∃ f ∈ R, unitAt ξ q f ∧ ∀ q' ∈ T, unitAt ξ q' f → q'.1 ∈ V)
    {L : Lat ξ E} {r : ℕ} (hv : ∀ q ∈ T, ∃ V : X.Opens, q.1 ∈ V ∧ FrameOpen L T r V) :
    ∃ (k : ℕ) (f g : Fin k → Ω), (∀ l, f l ∈ R) ∧ (∀ l, g l ∈ R) ∧ ∑ l, g l * f l = 1 ∧
      ∀ l, ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
        ∀ e : E, (∃ n : ℕ, f l ^ n • e ∈ sec L T) ↔
          ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q := by
  obtain ⟨k, f, g, hf, hg, hsum, hl⟩ := exists_cover hprime hbasic (FrameOpen L T r) hv
  refine ⟨k, f, g, hf, hg, hsum, fun l => ?_⟩
  obtain ⟨V, ⟨b, hb, hspan, hfr⟩, hV⟩ := hl l
  refine ⟨b, hb, hspan, fun e => ⟨?_, ?_⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨a, hae⟩ := exists_coords hspan e
    refine ⟨a, fun q => exists_pow_mul_mem hprime hfrac (hf l) fun p hp hu => ?_, hae⟩
    have h0 : f l ≠ 0 := hu.1
    have h1 : e = ((f l)⁻¹) ^ n • f l ^ n • e := by
      rw [smul_smul, ← mul_pow, inv_mul_cancel₀ h0, one_pow, one_smul]
    have h2 : e ∈ L p := by
      rw [h1]
      exact smul_mem_lat L (pow_mem hu.2.2 _) (mem_sec.1 hn p hp)
    rw [(hfr p hp (hV p hp hu)).2, hae] at h2
    exact coord_mem hb h2 q
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨N, hN⟩ := exists_pow_smul_sec hgen hle hprime hfrac hbasic hv (hf l)
      (e := ∑ q, a q • b q) fun p hp hu => by
        refine sum_mem fun q _ => smul_mem_lat L ?_ (frame_mem (hfr p hp (hV p hp hu)) q)
        obtain ⟨n, hn⟩ := ha q
        have h0 : f l ≠ 0 := hu.1
        have h1 : a q = ((f l)⁻¹) ^ n * (f l ^ n * a q) := by
          rw [← _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ h0, one_pow, _root_.one_mul]
        rw [h1]
        exact mul_mem (pow_mem hu.2.2 _) (hle p hp hn)
    exact ⟨N, mem_sec.2 hN⟩

section Flag

variable {r : ℕ}

theorem flagStep_eq_span_range (b : Fin r → E) : flagStep Ω b r = Submodule.span Ω (Set.range b) := by
  have h : b '' {k : Fin r | (k : ℕ) < r} = Set.range b := by
    ext v
    simp
  rw [flagStep, h]

theorem flagStep_succ (b : Fin r → E) (i : Fin r) :
    flagStep Ω b (i + 1) = Submodule.span Ω (insert (b i) (b '' {k : Fin r | (k : ℕ) < i})) := by
  have h : b '' {k : Fin r | (k : ℕ) < i + 1} = insert (b i) (b '' {k : Fin r | (k : ℕ) < i}) := by
    rw [← Set.image_insert_eq]
    congr 1
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Fin.ext_iff]
    omega
  rw [flagStep, h]

theorem self_mem_flagStep (b : Fin r → E) (i : Fin r) : b i ∈ flagStep Ω b (i + 1) :=
  Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩

theorem flagStep_le_succ (b : Fin r → E) (i : ℕ) : flagStep Ω b i ≤ flagStep Ω b (i + 1) :=
  Submodule.span_mono (Set.image_mono fun _ hk => Nat.lt_succ_of_lt hk)

theorem exists_sub_mem (b : Fin r → E) (i : Fin r) {e : E} (he : e ∈ flagStep Ω b (i + 1)) :
    ∃ c : Ω, e - c • b i ∈ flagStep Ω b i := by
  rw [flagStep_succ, Submodule.mem_span_insert] at he
  obtain ⟨c, z, hz, rfl⟩ := he
  exact ⟨c, by simpa [flagStep] using hz⟩

theorem repr_eq_zero_of_mem (w : Module.Basis (Fin r) Ω E) {i : ℕ} {v : E} (hv : v ∈ flagStep Ω w i)
    (j : Fin r) (hj : i ≤ j) : w.repr v j = 0 := by
  have h : flagStep Ω w i ≤ LinearMap.ker (w.coord j) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have hkj : k ≠ j := fun h => by
      subst h
      exact absurd hk (not_lt.2 hj)
    simp [Module.Basis.coord_apply, Finsupp.single_apply, hkj]
  simpa [Module.Basis.coord_apply] using h hv

theorem sub_repr_mem (w : Module.Basis (Fin r) Ω E) (i : Fin r) {v : E}
    (h : ∀ j, i < j → w.repr v j = 0) : v - w.repr v i • w i ∈ flagStep Ω w i := by
  have hs := w.sum_repr v
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hs
  rw [sub_eq_of_eq_add' hs.symm]
  refine sum_mem fun j hj => ?_
  rcases lt_trichotomy j i with hji | hji | hji
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hji, rfl⟩)
  · exact absurd hji (Finset.ne_of_mem_erase hj)
  · rw [h j hji, zero_smul]
    exact zero_mem _

theorem repr_self_ne_zero (w β : Module.Basis (Fin r) Ω E) (hst : ∀ j, flagStep Ω β j = flagStep Ω w j)
    (i : Fin r) : w.repr (β i) i ≠ 0 := by
  intro h0
  have h1 : w i ∈ flagStep Ω β (i + 1) := by
    rw [hst]
    exact self_mem_flagStep _ i
  obtain ⟨c, hc⟩ := exists_sub_mem β i h1
  rw [hst] at hc
  have h2 := repr_eq_zero_of_mem w hc i le_rfl
  simp [h0] at h2

theorem gr_le_of_frame (w β : Module.Basis (Fin r) Ω E) {L : Lat ξ E} {q : Cpt ξ}
    (hfr : L.IsFrameAt β q) (hst : ∀ j, flagStep Ω β j = flagStep Ω w j) (i : Fin r) {t : Ω}
    (ht : t ∈ L.gr w i q) : ∃ c ∈ regAt ξ q, t = c * w.repr (β i) i := by
  have hle : L.gr w i q ≤ Submodule.span (regAt ξ q) {w.repr (β i) i} := by
    refine Submodule.span_le.2 ?_
    rintro t ⟨e, he, hd⟩
    have he1 : e ∈ flagStep Ω β (i + 1) := by
      rw [hst]
      have := add_mem (flagStep_le_succ _ _ hd) (Submodule.smul_mem _ t (self_mem_flagStep (⇑w) i))
      simpa using this
    obtain ⟨c, hc⟩ := exists_sub_mem β i he1
    have hc1 := repr_eq_zero_of_mem β hc i le_rfl
    have hc2 : β.repr e i = c := by
      simpa [sub_eq_zero] using hc1
    have hcq : c ∈ regAt ξ q := by
      have h3 : ∑ j, β.repr e j • β j ∈ Submodule.span (regAt ξ q) (Set.range β) := by
        rw [β.sum_repr e, ← hfr.2]
        exact he
      rw [← hc2]
      exact coord_mem hfr.1 h3 i
    have h4 := repr_eq_zero_of_mem w hd i le_rfl
    rw [hst] at hc
    have h5 := repr_eq_zero_of_mem w hc i le_rfl
    simp only [map_sub, map_smul, Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_smul, Pi.smul_apply,
      Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, _root_.mul_one, sub_eq_zero] at h4 h5
    refine Submodule.mem_span_singleton.2 ⟨⟨c, hcq⟩, ?_⟩
    show c * w.repr (β i) i = t
    rw [← h5, h4]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hle ht)
  exact ⟨c, c.2, hc.symm⟩

theorem frameOpen_of_flag {L : Lat ξ E} (w : Module.Basis (Fin r) Ω E)
    (hfl : ∀ q ∈ T, ∃ V : X.Opens, q.1 ∈ V ∧ ∃ b : Fin r → E,
      (∀ j, flagStep Ω b j = flagStep Ω w j) ∧ ∀ q' ∈ T, q'.1 ∈ V → L.IsFrameAt b q') :
    ∀ q ∈ T, ∃ V : X.Opens, q.1 ∈ V ∧ FrameOpen L T r V := by
  intro q hq
  obtain ⟨V, hqV, b, hst, hfr⟩ := hfl q hq
  refine ⟨V, hqV, b, (hfr q hq hqV).1, ?_, hfr⟩
  rw [← flagStep_eq_span_range, hst, flagStep_eq_span_range]
  exact w.span_eq

theorem exists_lift (hgen : IsCptGen ξ) (hle : ∀ q ∈ T, R ≤ regAt ξ q)
    (hprime : ∀ P : Ideal R, P.IsPrime → ∃ q ∈ T, ∀ s : R, s ∉ P ↔ unitAt ξ q (s : Ω))
    (hfrac : ∀ q ∈ T, ∀ a ∈ regAt ξ q, ∃ s ∈ R, unitAt ξ q s ∧ s * a ∈ R)
    (hbasic : ∀ q ∈ T, ∀ V : X.Opens, q.1 ∈ V →
      ∃ f ∈ R, unitAt ξ q f ∧ ∀ q' ∈ T, unitAt ξ q' f → q'.1 ∈ V)
    {L : Lat ξ E} (w : Module.Basis (Fin r) Ω E)
    (hfl : ∀ q ∈ T, ∃ V : X.Opens, q.1 ∈ V ∧ ∃ b : Fin r → E,
      (∀ j, flagStep Ω b j = flagStep Ω w j) ∧ ∀ q' ∈ T, q'.1 ∈ V → L.IsFrameAt b q')
    (i : Fin r) {t : Ω} (ht : ∀ q ∈ T, t ∈ L.gr w i q) :
    ∃ v ∈ sec L T, v ∈ flagStep Ω w (i + 1) ∧ w.repr v i = t := by
  have hv := frameOpen_of_flag w hfl
  let I : Ideal R :=
    { carrier := {s | ∃ v ∈ sec L T, v ∈ flagStep Ω w (i + 1) ∧ w.repr v i = (s : Ω) * t}
      add_mem' := by
        rintro a b ⟨v, hv1, hv2, hv3⟩ ⟨v', hv1', hv2', hv3'⟩
        refine ⟨v + v', add_mem hv1 hv1', add_mem hv2 hv2', ?_⟩
        simp [hv3, hv3', add_mul]
      zero_mem' := ⟨0, zero_mem _, zero_mem _, by simp⟩
      smul_mem' := by
        rintro a b ⟨v, hv1, hv2, hv3⟩
        refine ⟨(a : Ω) • v, mem_sec.2 fun p hp => smul_mem_lat L (hle p hp a.2) (hv1 p hp),
          Submodule.smul_mem _ _ hv2, ?_⟩
        simp [hv3, _root_.mul_assoc] }
  have htop : I = ⊤ := by
    by_contra hI
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨q, hq, hu⟩ := hprime m hm.isPrime
    obtain ⟨V, hqV, b, hst, hfr⟩ := hfl q hq
    have hb := (hfr q hq hqV).1
    have hspan : Submodule.span Ω (Set.range b) = ⊤ := by
      rw [← flagStep_eq_span_range, hst, flagStep_eq_span_range]
      exact w.span_eq
    obtain ⟨β, rfl⟩ : ∃ β : Module.Basis (Fin r) Ω E, ⇑β = b :=
      ⟨Module.Basis.mk hb hspan.ge, Module.Basis.coe_mk _ _⟩
    have hu0 := repr_self_ne_zero w β hst i
    obtain ⟨f, hf, hfu, hfV⟩ := hbasic q hq V hqV
    have hsec : ∀ p ∈ T, unitAt ξ p f → (t / w.repr (β i) i) • β i ∈ L p := fun p hp hup => by
      have hfrp := hfr p hp (hfV p hp hup)
      obtain ⟨c, hc, hct⟩ := gr_le_of_frame w β hfrp hst i (ht p hp)
      have h1 : t / w.repr (β i) i = c := by
        rw [hct]
        field_simp
      rw [h1]
      exact smul_mem_lat L hc (frame_mem hfrp i)
    obtain ⟨N, hN⟩ := exists_pow_smul_sec hgen hle hprime hfrac hbasic hv hf hsec
    have hmem : (⟨f, hf⟩ : R) ^ N ∈ I := by
      refine ⟨f ^ N • (t / w.repr (β i) i) • β i, mem_sec.2 hN, ?_, ?_⟩
      · refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
        rw [← hst]
        exact self_mem_flagStep (⇑β) i
      · simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, SubmonoidClass.coe_pow]
        field_simp
    exact (hu ⟨f, hf⟩).2 hfu (hm.isPrime.mem_of_pow_mem N (hIm hmem))
  obtain ⟨v, hv1, hv2, hv3⟩ : (1 : R) ∈ I := htop ▸ Submodule.mem_top
  exact ⟨v, hv1, hv2, by simpa using hv3⟩

end Flag

theorem exists_point_of_prime {W : Set (Cpt ξ)} (Z : Subalgebra ℤ Ω) (R : Subring Ω) (S : Set Ω)
    (hZR : ∀ z ∈ Z, z ∈ R) (hZreg : ∀ q ∈ W, ∀ z ∈ Z, z ∈ regAt ξ q)
    (hSZ : ∀ s ∈ S, s ∈ Z) (hSinv : ∀ s ∈ S, ∃ u ∈ R, u * s = 1)
    (hloc : ∀ t ∈ R, ∃ s ∈ S, s * t ∈ Z)
    (hpt : ∀ I : Ideal Z, I.IsPrime → ∃ q ∈ W, ∀ s : Z, s ∉ I ↔ unitAt ξ q (s : Ω))
    (P : Ideal R) (hP : P.IsPrime) :
    ∃ q ∈ W, (∀ s ∈ S, unitAt ξ q s) ∧ ∀ t : R, t ∉ P ↔ unitAt ξ q (t : Ω) := by
  let ι : Z →+* R :=
    { toFun := fun z => ⟨z, hZR z z.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ => Subtype.ext (by simp) }
  haveI := hP
  obtain ⟨q, hqW, hqu⟩ := hpt (P.comap ι) inferInstance
  have hnot : ∀ s (hs : s ∈ S), (⟨s, hZR s (hSZ s hs)⟩ : R) ∉ P := by
    intro s hs hsP
    obtain ⟨u, hu, hus⟩ := hSinv s hs
    have h1 : (⟨u, hu⟩ : R) * ⟨s, hZR s (hSZ s hs)⟩ = 1 := Subtype.ext hus
    exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ P.mul_mem_left _ hsP))
  have hSu : ∀ s ∈ S, unitAt ξ q s := fun s hs =>
    (hqu ⟨s, hSZ s hs⟩).1 fun h => hnot s hs h
  refine ⟨q, hqW, hSu, fun t => ?_⟩
  obtain ⟨b, hb, hz⟩ := hloc t t.2
  have hbu := hSu b hb
  have htr : (t : Ω) ∈ regAt ξ q := by
    have e : (t : Ω) = b⁻¹ * (b * t) := by
      rw [← _root_.mul_assoc, inv_mul_cancel₀ hbu.1, _root_.one_mul]
    rw [e]
    exact mul_mem hbu.2.2 (hZreg q hqW _ hz)
  have hιz : ι ⟨_, hz⟩ = ⟨b, hZR b (hSZ b hb)⟩ * t := Subtype.ext rfl
  have hzu := hqu ⟨_, hz⟩
  constructor
  · intro htP
    refine unitAt_of_mul htr hbu.2.1 ?_
    rw [mul_comm]
    refine hzu.1 fun h => ?_
    have h' : ι ⟨_, hz⟩ ∈ P := h
    rw [hιz] at h'
    exact (hP.mem_or_mem h').elim (hnot b hb) htP
  · intro hu htP
    have h1 : ι ⟨_, hz⟩ ∈ P := by
      rw [hιz]
      exact P.mul_mem_left _ htP
    refine hzu.2 ?_ h1
    exact ⟨mul_ne_zero hbu.1 hu.1, mul_mem hbu.2.1 hu.2.1, by
      rw [mul_inv]
      exact mul_mem hbu.2.2 hu.2.2⟩

section Concrete

variable {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {A : Type} [CommRing A] [Algebra A Ω] (m : Ideal A) [m.IsPrime]
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O]
  [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω]

def chartPts (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [Algebra O Ω] {κ : Type} (x : κ → Ω)
    (c : κ) : Set (Cpt ξ) :=
  {q | InChart ξ x c q ∧ ∀ o : O, algebraMap O Ω o ∈ regAt ξ q}

theorem unitAt_mul {q : Cpt ξ} {a b : Ω} (ha : unitAt ξ q a) (hb : unitAt ξ q b) : unitAt ξ q (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by
    rw [mul_inv]
    exact mul_mem ha.2.2 hb.2.2⟩

theorem chartRing_le_regAt {κ : Type} {x : κ → Ω} {c : κ} {q : Cpt ξ} (hq : q ∈ chartPts ξ O x c) :
    (chartRing O x c).toSubring ≤ regAt ξ q := fun a ha =>
  Algebra.adjoin_induction (p := fun u _ => u ∈ regAt ξ q)
    (fun u hu => by
      obtain ⟨j, rfl⟩ := hu
      exact hq.1.2 j)
    (fun o => hq.2 o) (fun _ _ _ _ h1 h2 => add_mem h1 h2) (fun _ _ _ _ h1 h2 => mul_mem h1 h2) ha

omit [IsDomain O] [IsDiscreteValuationRing O] in
include m in
theorem exists_inv_of_notMem {s : A} (hs : s ∉ m) :
    ∃ o : O, algebraMap O Ω o * algebraMap A Ω s = 1 := by
  obtain ⟨o, ho⟩ := (IsLocalization.map_units O (⟨s, hs⟩ : m.primeCompl)).exists_left_inv
  refine ⟨o, ?_⟩
  rw [IsScalarTower.algebraMap_apply A O Ω s, ← map_mul]
  have : o * algebraMap A O s = 1 := ho
  rw [this, map_one]

include m

theorem chartRing_int_le (hC : HasConstants ℤ A y) {c : ∀ k, J k} (hc : segreVec y c ≠ 0) {t : Ω}
    (ht : t ∈ chartRing ℤ (segreVec y) c) : t ∈ chartRing O (segreVec y) c :=
  (GlobalTheory.T.chart_ring_localization_membership K J Ω y A hC m O c hc t).2 ⟨1, (Ideal.ne_top_iff_one m).1 Ideal.IsPrime.ne_top', by simpa using ht⟩

theorem chart_prime (hT : CoordTie ℤ ξ (segreVec y)) (hC : HasConstants ℤ A y) {c : ∀ k, J k}
    (hc : segreVec y c ≠ 0) (P : Ideal (chartRing O (segreVec y) c).toSubring) (hP : P.IsPrime) :
    ∃ q ∈ chartPts ξ O (segreVec y) c, ∀ s : (chartRing O (segreVec y) c).toSubring,
      s ∉ P ↔ unitAt ξ q (s : Ω) := by
  obtain ⟨q, hqc, hAu, hiff⟩ := exists_point_of_prime (W := {q : Cpt ξ | InChart ξ (segreVec y) c q})
    (Algebra.adjoin ℤ (Set.range fun j => segreVec y j / segreVec y c))
    (chartRing O (segreVec y) c).toSubring {a | ∃ s : A, s ∉ m ∧ a = algebraMap A Ω s}
    (fun z hz => chartRing_int_le m hC hc hz)
    (fun q hq z hz => ChartTie.mem_regAt_of_mem hT hz hq)
    (by
      rintro _ ⟨s, -, rfl⟩
      exact hC c hc s)
    (by
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨o, ho⟩ := exists_inv_of_notMem m (O := O) (Ω := Ω) hs
      exact ⟨_, Subalgebra.algebraMap_mem _ o, ho⟩)
    (fun t ht => by
      obtain ⟨b, hb, hz⟩ := (GlobalTheory.T.chart_ring_localization_membership K J Ω y A hC m O c hc t).1 ht
      exact ⟨_, ⟨b, hb, rfl⟩, hz⟩)
    (fun I hI => by
      obtain ⟨q, ⟨hqc, hqu⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ _ (segreVec y) hT c hc I hI
      exact ⟨q, hqc, hqu⟩)
    P hP
  have hO : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q := by
    intro o
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj m.primeCompl o
    have h1 : algebraMap O Ω o * algebraMap A Ω s = algebraMap A Ω a := by
      rw [IsScalarTower.algebraMap_apply A O Ω s, IsScalarTower.algebraMap_apply A O Ω a, ← map_mul, h]
    have hu := hAu _ ⟨s, s.2, rfl⟩
    have h2 : algebraMap O Ω o = algebraMap A Ω a * (algebraMap A Ω s)⁻¹ := by
      rw [← h1]
      field_simp [hu.1]
    rw [h2]
    exact mul_mem (ChartTie.mem_regAt_of_mem hT (hC c hc a) hqc) hu.2.2
  exact ⟨q, ⟨hqc, hO⟩, hiff⟩

theorem chart_frac (hT : CoordTie ℤ ξ (segreVec y)) (hC : HasConstants ℤ A y) {c : ∀ k, J k}
    (hc : segreVec y c ≠ 0) {q : Cpt ξ} (hq : q ∈ chartPts ξ O (segreVec y) c) {a : Ω} (ha : a ∈ regAt ξ q) :
    ∃ s ∈ (chartRing O (segreVec y) c).toSubring, unitAt ξ q s ∧
      s * a ∈ (chartRing O (segreVec y) c).toSubring := by
  obtain ⟨s, hs, hsu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ (segreVec y) hT c q hq.1 a).1 ha
  exact ⟨s, chartRing_int_le m hC hc hs, hsu, chartRing_int_le m hC hc hsa⟩

theorem chart_basic (hT : CoordTie ℤ ξ (segreVec y)) (hC : HasConstants ℤ A y) {c : ∀ k, J k}
    (hc : segreVec y c ≠ 0) {q : Cpt ξ} (hq : q ∈ chartPts ξ O (segreVec y) c) (V : X.Opens) (hV : q.1 ∈ V) :
    ∃ f ∈ (chartRing O (segreVec y) c).toSubring, unitAt ξ q f ∧
      ∀ q' ∈ chartPts ξ O (segreVec y) c, unitAt ξ q' f → q'.1 ∈ V := by
  obtain ⟨f, hf, hfu, hfV⟩ := ChartTie.exists_basic hT hc hq.1 V hV
  exact ⟨f, chartRing_int_le m hC hc hf, hfu, fun q' hq' => hfV q' hq'.1⟩

theorem chartPts_subset_overPrime {p : ℕ} (hp : p.Prime) (hpm : (p : A) ∈ m) {κ : Type} {x : κ → Ω} {c : κ} :
    chartPts ξ O x c ⊆ overPrime ξ p := by
  intro q hq p' hp' hne hfib
  refine hfib ?_
  have hcop : IsCoprime (p : ℤ) (p' : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hp').2 hne.symm)
  have hnot : (p' : A) ∉ m := by
    intro hp'm
    obtain ⟨u, v, huv⟩ := hcop
    have h1 : (u : A) * (p : A) + (v : A) * (p' : A) = 1 := by
      have := congrArg (Int.cast : ℤ → A) huv
      push_cast at this
      exact this
    exact (Ideal.ne_top_iff_one m).1 Ideal.IsPrime.ne_top'
      (h1 ▸ add_mem (m.mul_mem_left _ hpm) (m.mul_mem_left _ hp'm))
  obtain ⟨o, ho⟩ := exists_inv_of_notMem m (O := O) (Ω := Ω) hnot
  rw [map_natCast] at ho
  have h0 : (p' : Ω) ≠ 0 := right_ne_zero_of_mul_eq_one ho
  refine ⟨h0, natCast_mem _ _, ?_⟩
  rw [← eq_inv_of_mul_eq_one_left ho]
  exact hq.2 o

end Concrete

theorem exists_chartBundle_of_isFlagVBOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ d : ℕ, IsArithVar (mCoordIdeal y) (d + 1) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) → HasConstants ℤ A y → ∀ (p : ℕ), p.Prime → ∀ (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (E : Type) [AddCommGroup E] [Module Ω E] (r : ℕ) (w : Module.Basis (Fin r) Ω E) (L : Lat ξ E), L.IsFlagVBOn (overPrime ξ p) w → ∃ B : ChartBundle O (segreVec y) r E, (∀ c, segreVec y c ≠ 0 → ∀ v, v ∈ B.lat c ↔ ∀ q : Cpt ξ, InChart ξ (segreVec y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → v ∈ L q) ∧ ∀ (x : Fin r → K → ℤ) (e : Fin r → Ω) (he : ∀ i, e i ≠ 0), (∀ i, (L.gr w i).IsDegOn (overPrime ξ p) y (x i) (e i)) → IsFlagFrame y B (w.unitsSMul fun i => Units.mk0 (e i) (he i)) x := by
  intro X Ω _ ξ K _ _ J _ y hT' d _ A _ _ _ _ hinj hC p hp m _ hpm O _ _ _ _ _ _ _ E _ _ r w L hfl
  have hT : CoordTie ℤ ξ (segreVec y) := hT'
  have hsub : ∀ c, chartPts ξ O (segreVec y) c ⊆ overPrime ξ p := fun c =>
    chartPts_subset_overPrime m hp hpm
  have hflc : ∀ c, ∀ q ∈ chartPts ξ O (segreVec y) c, ∃ V : X.Opens, q.1 ∈ V ∧ ∃ b : Fin r → E,
      (∀ j, flagStep Ω b j = flagStep Ω w j) ∧
        ∀ q' ∈ chartPts ξ O (segreVec y) c, q'.1 ∈ V → L.IsFrameAt b q' := by
    intro c q hq
    obtain ⟨U, hU, b, hst, hfr⟩ := hfl q (hsub c hq)
    exact ⟨U, hU, b, hst, fun q' hq' => hfr q' (hsub c hq')⟩
  have hle : ∀ c, ∀ q ∈ chartPts ξ O (segreVec y) c, (chartRing O (segreVec y) c).toSubring ≤ regAt ξ q :=
    fun c q hq => chartRing_le_regAt hq
  have hprime : ∀ c, segreVec y c ≠ 0 → ∀ P : Ideal (chartRing O (segreVec y) c).toSubring, P.IsPrime →
      ∃ q ∈ chartPts ξ O (segreVec y) c, ∀ s : (chartRing O (segreVec y) c).toSubring,
        s ∉ P ↔ unitAt ξ q (s : Ω) := fun c hc => chart_prime m hT hC hc
  have hfrac : ∀ c, segreVec y c ≠ 0 → ∀ q ∈ chartPts ξ O (segreVec y) c, ∀ a ∈ regAt ξ q,
      ∃ s ∈ (chartRing O (segreVec y) c).toSubring, unitAt ξ q s ∧
        s * a ∈ (chartRing O (segreVec y) c).toSubring :=
    fun c hc q hq a ha => chart_frac m hT hC hc hq ha
  have hbasic : ∀ c, segreVec y c ≠ 0 → ∀ q ∈ chartPts ξ O (segreVec y) c, ∀ V : X.Opens, q.1 ∈ V →
      ∃ f ∈ (chartRing O (segreVec y) c).toSubring, unitAt ξ q f ∧
        ∀ q' ∈ chartPts ξ O (segreVec y) c, unitAt ξ q' f → q'.1 ∈ V :=
    fun c hc q hq V hV => chart_basic m hT hC hc hq V hV
  obtain ⟨B, hB⟩ : ∃ B : ChartBundle O (segreVec y) r E,
      ∀ c, B.lat c = sec L (chartPts ξ O (segreVec y) c) := by
    refine ⟨{ lat := fun c => sec L (chartPts ξ O (segreVec y) c), stable := ?_, frame := ?_,
              overlap := ?_ }, fun _ => rfl⟩
    · intro c a ha e hec
      exact mem_sec.2 fun p hp => smul_mem_lat L (hle c p hp ha) (mem_sec.1 hec p hp)
    · intro c hc
      exact exists_frames hT.gen (hle c) (hprime c hc) (hfrac c hc) (hbasic c hc)
        (frameOpen_of_flag w (hflc c))
    · intro i j hi hj e hei
      have hf : segreVec y i / segreVec y j ∈ (chartRing O (segreVec y) j).toSubring :=
        Algebra.subset_adjoin ⟨i, rfl⟩
      obtain ⟨N, hN⟩ := exists_pow_smul_sec hT.gen (hle j) (hprime j hj) (hfrac j hj) (hbasic j hj)
        (frameOpen_of_flag w (hflc j)) hf (e := e) fun p hp hu => by
          refine mem_sec.1 hei p ⟨⟨hi, fun c' => ?_⟩, hp.2⟩
          have h1 : segreVec y c' / segreVec y i =
              (segreVec y c' / segreVec y j) * (segreVec y i / segreVec y j)⁻¹ := by
            field_simp
          rw [h1]
          exact mul_mem (hp.1.2 c') hu.2.2
      exact ⟨N, mem_sec.2 hN⟩
  refine ⟨B, fun c _ v => ?_, fun x e he hgr => ⟨fun c hc i => ?_⟩⟩
  · rw [hB, mem_sec]
    exact ⟨fun h q h1 h2 => h q ⟨h1, h2⟩, fun h q hq => h q hq.1 hq.2⟩
  · have hg0 : ∏ k, y ⟨k, c k⟩ ^ x i k ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ fun h0 => hc ?_
      exact Finset.prod_eq_zero (Finset.mem_univ k) h0
    have hgenr : ∀ q ∈ chartPts ξ O (segreVec y) c, L.gr w i q =
        Submodule.span (regAt ξ q) {(∏ k, y ⟨k, c k⟩ ^ x i k) • e i} := fun q hq =>
      (hgr i).2 q (hsub c hq) c hq.1
    have hrep : ∀ (v : E) (j : Fin r), (w.unitsSMul fun i => Units.mk0 (e i) (he i)).repr v j =
        (e j)⁻¹ * w.repr v j := by
      intro v j
      rw [Module.Basis.repr_unitsSMul]
      simp [Units.smul_def]
    have hei := he i
    ext s
    constructor
    · rintro ⟨v, hv, hz, rfl⟩
      rw [hB] at hv
      have hz' : ∀ j, i < j → w.repr v j = 0 := fun j hj => by
        have h := hz j hj
        rw [hrep] at h
        exact (mul_eq_zero.1 h).resolve_left (inv_ne_zero (he j))
      show ∃ a ∈ chartRing O (segreVec y) c, _ = a * ∏ k, y ⟨k, c k⟩ ^ x i k
      refine ⟨(e i)⁻¹ * w.repr v i / ∏ k, y ⟨k, c k⟩ ^ x i k, ?_, ?_⟩
      · refine mem_of_forall_regAt (hprime c hc) (hfrac c hc) fun q hq => ?_
        have hmem : w.repr v i ∈ L.gr w i q :=
          Submodule.subset_span ⟨v, hv q hq, sub_repr_mem w i hz'⟩
        rw [hgenr q hq] at hmem
        obtain ⟨ρ, hρ⟩ := Submodule.mem_span_singleton.1 hmem
        have hρ' : (ρ : Ω) * ((∏ k, y ⟨k, c k⟩ ^ x i k) * e i) = w.repr v i := hρ
        rw [← hρ']
        have h1 : (e i)⁻¹ * ((ρ : Ω) * ((∏ k, y ⟨k, c k⟩ ^ x i k) * e i)) /
            ∏ k, y ⟨k, c k⟩ ^ x i k = ρ := by
          field_simp
        rw [h1]
        exact ρ.2
      · rw [hrep]
        field_simp
    · rintro ⟨a, ha, rfl⟩
      have ht : ∀ q ∈ chartPts ξ O (segreVec y) c,
          a * (∏ k, y ⟨k, c k⟩ ^ x i k) * e i ∈ L.gr w i q := fun q hq => by
        rw [hgenr q hq]
        refine Submodule.mem_span_singleton.2 ⟨⟨a, hle c q hq ha⟩, ?_⟩
        show a * ((∏ k, y ⟨k, c k⟩ ^ x i k) * e i) = _
        rw [_root_.mul_assoc]
      obtain ⟨v, hv, hv2, hv3⟩ := exists_lift hT.gen (hle c) (hprime c hc) (hfrac c hc) (hbasic c hc) w
        (hflc c) i ht
      refine ⟨v, by rw [hB]; exact hv, fun j hj => ?_, ?_⟩
      · rw [hrep, repr_eq_zero_of_mem w hv2 j hj, MulZeroClass.mul_zero]
      · rw [hrep, hv3]
        field_simp

end GlobalTheory.CompanionTheory.Ar.Num.LatChart
