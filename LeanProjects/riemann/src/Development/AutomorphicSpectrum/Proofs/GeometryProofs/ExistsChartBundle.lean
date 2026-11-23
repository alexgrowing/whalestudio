import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

namespace ChartTie

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω}
  {c : κ} {E : Type} [AddCommGroup E] [Module Ω E]

theorem mem_regAt_iff {a : Ω} {p : Cpt ξ} : a ∈ regAt ξ p ↔ ∃ t, genMap ξ p t = a := RingHom.mem_range

theorem mem_regAt_of_mem (hT : CoordTie ℤ ξ x) {a : Ω} (ha : a ∈ chartRing ℤ x c) {p : Cpt ξ}
    (hp : InChart ξ x c p) : a ∈ regAt ξ p :=
  (hT.ring c hp.1 a).1 ha p hp

theorem unitAt_of_mul {p : Cpt ξ} {f g : Ω} (hf : f ∈ regAt ξ p) (hg : g ∈ regAt ξ p)
    (h : unitAt ξ p (f * g)) : unitAt ξ p f := by
  obtain ⟨h0, -, hi⟩ := h
  have hf0 := left_ne_zero_of_mul h0
  have hg0 := right_ne_zero_of_mul h0
  refine ⟨hf0, hf, ?_⟩
  have e : f⁻¹ = g * (f * g)⁻¹ := by field_simp
  rw [e]
  exact mul_mem hg hi

theorem exists_pow_mul_mem (hT : CoordTie ℤ ξ x) (hc : x c ≠ 0) {f a : Ω} (hf : f ∈ chartRing ℤ x c)
    (ha : ∀ p : Cpt ξ, InChart ξ x c p → unitAt ξ p f → a ∈ regAt ξ p) :
    ∃ n : ℕ, f ^ n * a ∈ chartRing ℤ x c := by
  classical
  let A := Algebra.adjoin ℤ (Set.range fun j => x j / x c)
  let J : Ideal A :=
    { carrier := {s | (s : Ω) * a ∈ A}
      add_mem' := fun {s t} hs ht => by
        show ((s + t : A) : Ω) * a ∈ A
        have hs' : (s : Ω) * a ∈ A := hs
        have ht' : (t : Ω) * a ∈ A := ht
        have := add_mem hs' ht'
        simpa [add_mul] using this
      zero_mem' := by
        show ((0 : A) : Ω) * a ∈ A
        simp
      smul_mem' := fun b s hs => by
        show ((b * s : A) : Ω) * a ∈ A
        have hs' : (s : Ω) * a ∈ A := hs
        have := mul_mem b.2 hs'
        simpa [_root_.mul_assoc] using this }
  have hmem : (⟨f, hf⟩ : A) ∈ J.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hJP, hP⟩
    by_contra hfP
    obtain ⟨p, ⟨hpc, hpu⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ κ x hT c hc P hP
    have hu := (hpu ⟨f, hf⟩).1 hfP
    obtain ⟨s, hs, hsu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x hT c p hpc a).1 (ha p hpc hu)
    have hsJ : (⟨s, hs⟩ : A) ∈ J := hsa
    exact (hpu ⟨s, hs⟩).2 hsu (hJP hsJ)
  obtain ⟨n, hn⟩ := hmem
  have hn' : (((⟨f, hf⟩ : A) ^ n : A) : Ω) * a ∈ A := hn
  have hn'' : f ^ n * a ∈ A := by simpa using hn'
  exact ⟨n, hn''⟩

theorem exists_basic (hT : CoordTie ℤ ξ x) (hc : x c ≠ 0) {p : Cpt ξ} (hp : InChart ξ x c p) (V : X.Opens)
    (hV : p.1 ∈ V) : ∃ f ∈ chartRing ℤ x c, unitAt ξ p f ∧
      ∀ q : Cpt ξ, InChart ξ x c q → unitAt ξ q f → q.1 ∈ V := by
  obtain ⟨U, hU, hmem⟩ := hT.affine c hc
  have hpU : p.1 ∈ U := (hmem p.1).2 ⟨p.2, hp⟩
  obtain ⟨s, hsV, hps⟩ := hU.exists_basicOpen_le (V := V) ⟨p.1, hV⟩ hpU
  have hη : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
  obtain ⟨a, ha⟩ : ∃ a, a = (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη s) := ⟨_, rfl⟩
  have hUq : ∀ q : Cpt ξ, InChart ξ x c q → q.1 ∈ U := fun q hq => (hmem q.1).2 ⟨q.2, hq⟩
  have hval : ∀ (q : Cpt ξ) (hq : q.1 ∈ U), genMap ξ q (X.presheaf.germ U q.1 hq s) = a := fun q hq => by
    rw [ha]
    exact genMap_germ_eq_stalk_closed ξ q U hq hη s
  refine ⟨a, (hT.ring c hc a).2 fun q hq => mem_regAt_iff.2 ⟨_, hval q (hUq q hq)⟩, ?_, ?_⟩
  · have hu : IsUnit (X.presheaf.germ U p.1 hpU s) := (X.mem_basicOpen s p.1 hpU).1 hps
    obtain ⟨t, ht⟩ := hu.exists_right_inv
    have h1 : a * genMap ξ p t = 1 := by
      rw [← hval p hpU, ← map_mul, ht, map_one]
    have ha0 : a ≠ 0 := left_ne_zero_of_mul_eq_one h1
    refine ⟨ha0, mem_regAt_iff.2 ⟨_, hval p hpU⟩, mem_regAt_iff.2 ⟨t, ?_⟩⟩
    exact eq_inv_of_mul_eq_one_right h1
  · intro q hq hu
    obtain ⟨h0, -, hi⟩ := hu
    obtain ⟨t, ht⟩ := mem_regAt_iff.1 hi
    have hqU := hUq q hq
    have h1 : X.presheaf.germ U q.1 hqU s * t = 1 := hT.gen.inj q (by
      rw [map_mul, hval q hqU, ht, map_one, mul_inv_cancel₀ h0])
    exact hsV ((X.mem_basicOpen s q.1 hqU).2 (isUnit_iff_exists_inv.2 ⟨t, h1⟩))

theorem exists_cover (hT : CoordTie ℤ ξ x) (hc : x c ≠ 0) (Q : X.Opens → Prop)
    (hQ : ∀ p : Cpt ξ, InChart ξ x c p → ∃ V : X.Opens, p.1 ∈ V ∧ Q V) :
    ∃ (k : ℕ) (f g : Fin k → Ω), (∀ l, f l ∈ chartRing ℤ x c) ∧ (∀ l, g l ∈ chartRing ℤ x c) ∧
      ∑ l, g l * f l = 1 ∧
      ∀ l, ∃ V : X.Opens, Q V ∧ ∀ q : Cpt ξ, InChart ξ x c q → unitAt ξ q (f l) → q.1 ∈ V := by
  classical
  let A := Algebra.adjoin ℤ (Set.range fun j => x j / x c)
  let T : Set A := {f | ∃ V : X.Opens, Q V ∧
    ∀ q : Cpt ξ, InChart ξ x c q → unitAt ξ q (f : Ω) → q.1 ∈ V}
  have htop : Ideal.span T = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨p, ⟨hpc, hpu⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ κ x hT c hc m hm.isPrime
    obtain ⟨V, hpV, hQV⟩ := hQ p hpc
    obtain ⟨f, hf, hfu, hfV⟩ := exists_basic hT hc hpc V hpV
    exact (hpu ⟨f, hf⟩).2 hfu (hle (Ideal.subset_span ⟨V, hQV, hfV⟩))
  obtain ⟨s, hsT, hs⟩ := (Ideal.span_eq_top_iff_finite T).1 htop
  let e := s.equivFin
  have h1 : (1 : A) ∈ Ideal.span (Set.range fun l : Fin s.card => ((e.symm l : s) : A)) := by
    have hr : (Set.range fun l : Fin s.card => ((e.symm l : s) : A)) = (s : Set A) := by
      ext y
      constructor
      · rintro ⟨l, rfl⟩
        exact (e.symm l).2
      · intro hy
        exact ⟨e ⟨y, hy⟩, by simp⟩
    rw [hr, hs]
    trivial
  obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.1 h1
  refine ⟨s.card, fun l => (((e.symm l : s) : A) : Ω), fun l => (g l : Ω), fun l => ((e.symm l : s) : A).2,
    fun l => (g l).2, ?_, fun l => hsT (e.symm l).2⟩
  have h2 := congrArg (Subtype.val) hg
  simpa using h2

theorem exists_unitAt (hT : CoordTie ℤ ξ x) {k : ℕ} {f g : Fin k → Ω} (hf : ∀ l, f l ∈ chartRing ℤ x c)
    (hg : ∀ l, g l ∈ chartRing ℤ x c) (hsum : ∑ l, g l * f l = 1) {p : Cpt ξ} (hp : InChart ξ x c p) :
    ∃ l, unitAt ξ p (f l) := by
  obtain ⟨hloc, -, -⟩ := regAt_isLocalRing_isFractionRing_stalk X Ω ξ hT.gen p
  by_contra hno
  let ff : Fin k → regAt ξ p := fun l => ⟨f l, mem_regAt_of_mem hT (hf l) hp⟩
  let gg : Fin k → regAt ξ p := fun l => ⟨g l, mem_regAt_of_mem hT (hg l) hp⟩
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

theorem smul_mem_lat (L : Lat ξ E) {p : Cpt ξ} {a : Ω} (ha : a ∈ regAt ξ p) {e : E} (he : e ∈ L p) :
    a • e ∈ L p :=
  (L p).smul_mem ⟨a, ha⟩ he

theorem coord_mem {p : Cpt ξ} {r : ℕ} {b : Fin r → E} (hb : LinearIndependent Ω b) {a : Fin r → Ω}
    (h : ∑ q, a q • b q ∈ Submodule.span (regAt ξ p) (Set.range b)) (q : Fin r) : a q ∈ regAt ξ p := by
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h
  have hd' : ∑ i, (d i : Ω) • b i = ∑ i, a i • b i := hd
  have h0 := Fintype.linearIndependent_iff.1 hb (fun i => (d i : Ω) - a i)
    (by simp [sub_smul, Finset.sum_sub_distrib, hd']) q
  rw [← sub_eq_zero.1 h0]
  exact (d q).2

theorem exists_coords {r : ℕ} {b : Fin r → E} (hs : Submodule.span Ω (Set.range b) = ⊤) (e : E) :
    ∃ a : Fin r → Ω, e = ∑ q, a q • b q := by
  have he : e ∈ Submodule.span Ω (Set.range b) := hs ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 he
  exact ⟨a, ha.symm⟩

def FrameOpen (L : Lat ξ E) (r : ℕ) (V : X.Opens) : Prop :=
  ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
    ∀ q : Cpt ξ, q.1 ∈ V → L.IsFrameAt b q

theorem frameOpen_cover {L : Lat ξ E} {r : ℕ} (hv : L.IsVB r ⊤) (p : Cpt ξ) :
    ∃ V : X.Opens, p.1 ∈ V ∧ FrameOpen L r V := by
  obtain ⟨U, hp, b, hs, hq⟩ := hv p (Set.mem_univ _)
  exact ⟨U, hp, b, (hq p trivial hp).1, hs, fun q h => hq q trivial h⟩

theorem frame_mem {L : Lat ξ E} {r : ℕ} {b : Fin r → E} {p : Cpt ξ} (h : L.IsFrameAt b p) (q : Fin r) :
    b q ∈ L p := by
  rw [h.2]
  exact Submodule.subset_span ⟨q, rfl⟩

theorem exists_pow_smul_sec (hT : CoordTie ℤ ξ x) (hc : x c ≠ 0) {L : Lat ξ E} {r : ℕ} (hv : L.IsVB r ⊤)
    {f : Ω} (hf : f ∈ chartRing ℤ x c) {e : E}
    (he : ∀ p : Cpt ξ, InChart ξ x c p → unitAt ξ p f → e ∈ L p) :
    ∃ N : ℕ, ∀ p : Cpt ξ, InChart ξ x c p → f ^ N • e ∈ L p := by
  obtain ⟨k, g, d, hg, hd, hsum, hl⟩ := exists_cover hT hc (FrameOpen L r) fun p _ => frameOpen_cover hv p
  have key : ∀ l, ∃ N : ℕ, ∀ p : Cpt ξ, InChart ξ x c p → unitAt ξ p (g l) → f ^ N • e ∈ L p := by
    intro l
    obtain ⟨V, ⟨b, hb, hspan, hfr⟩, hV⟩ := hl l
    obtain ⟨a, hae⟩ := exists_coords hspan e
    have h1 : ∀ q, ∃ n : ℕ, (f * g l) ^ n * a q ∈ chartRing ℤ x c := fun q =>
      exists_pow_mul_mem hT hc (mul_mem hf (hg l)) fun p hp hu => by
        have hfp := mem_regAt_of_mem hT hf hp
        have hgp := mem_regAt_of_mem hT (hg l) hp
        have huf : unitAt ξ p f := unitAt_of_mul hfp hgp hu
        have hug : unitAt ξ p (g l) := unitAt_of_mul hgp hfp (by rwa [mul_comm])
        have hmem := he p hp huf
        rw [(hfr p (hV p hp hug)).2, hae] at hmem
        exact coord_mem hb hmem q
    choose n hn using h1
    refine ⟨∑ q, n q, fun p hp hu => ?_⟩
    have hg0 : g l ≠ 0 := hu.1
    have hfrp := hfr p (hV p hp hu)
    rw [hae, Finset.smul_sum]
    refine sum_mem fun q _ => ?_
    have hle : n q ≤ ∑ q, n q := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    have hA : (f * g l) ^ (∑ q, n q) * a q ∈ chartRing ℤ x c := by
      have e1 : (f * g l) ^ (∑ q, n q) * a q =
          (f * g l) ^ (∑ q, n q - n q) * ((f * g l) ^ n q * a q) := by
        rw [← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
      rw [e1]
      exact mul_mem (pow_mem (mul_mem hf (hg l)) _) (hn q)
    have e2 : f ^ (∑ q, n q) • a q • b q =
        (((g l)⁻¹) ^ (∑ q, n q) * ((f * g l) ^ (∑ q, n q) * a q)) • b q := by
      rw [smul_smul]
      congr 1
      rw [mul_pow, inv_pow]
      field_simp
    rw [e2]
    exact smul_mem_lat L (mul_mem (pow_mem hu.2.2 _) (mem_regAt_of_mem hT hA hp)) (frame_mem hfrp q)
  choose N hN using key
  refine ⟨∑ l, N l, fun p hp => ?_⟩
  obtain ⟨l, hl'⟩ := exists_unitAt hT hg hd hsum hp
  have hle : N l ≤ ∑ l, N l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  have e1 : f ^ (∑ l, N l) • e = f ^ (∑ l, N l - N l) • f ^ N l • e := by
    rw [smul_smul, ← pow_add, Nat.sub_add_cancel hle]
  rw [e1]
  exact smul_mem_lat L (pow_mem (mem_regAt_of_mem hT hf hp) _) (hN l p hp hl')

def sec (L : Lat ξ E) (x : κ → Ω) (c : κ) : AddSubgroup E where
  carrier := {e | ∀ p : Cpt ξ, InChart ξ x c p → e ∈ L p}
  add_mem' ha hb p hp := add_mem (ha p hp) (hb p hp)
  zero_mem' _ _ := zero_mem _
  neg_mem' ha p hp := neg_mem (ha p hp)

theorem mem_sec {L : Lat ξ E} {e : E} : e ∈ sec L x c ↔ ∀ p : Cpt ξ, InChart ξ x c p → e ∈ L p := Iff.rfl

end ChartTie

open ChartTie in

theorem exists_chartBundle_of_isVB : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (r : ℕ),
    CoordTie ℤ ξ x → L.IsVB r ⊤ → ∃ W : ChartBundle ℤ x r E, L.IsChartOf x W.lat := by
  intro X Ω _ ξ E _ _ κ x L r hT hv
  refine ⟨{ lat := sec L x, stable := ?_, frame := ?_, overlap := ?_ }, fun c _ e => mem_sec⟩
  · intro i a ha e he
    exact mem_sec.2 fun p hp => smul_mem_lat L (mem_regAt_of_mem hT ha hp) (mem_sec.1 he p hp)
  · intro c hc
    obtain ⟨k, f, g, hf, hg, hsum, hl⟩ := exists_cover hT hc (FrameOpen L r) fun p _ => frameOpen_cover hv p
    refine ⟨k, f, g, hf, hg, hsum, fun l => ?_⟩
    obtain ⟨V, ⟨b, hb, hspan, hfr⟩, hV⟩ := hl l
    refine ⟨b, hb, hspan, fun e => ⟨?_, ?_⟩⟩
    · rintro ⟨n, hn⟩
      obtain ⟨a, hae⟩ := exists_coords hspan e
      refine ⟨a, fun q => exists_pow_mul_mem hT hc (hf l) fun p hp hu => ?_, hae⟩
      have h0 : f l ≠ 0 := hu.1
      have h1 : e = ((f l)⁻¹) ^ n • f l ^ n • e := by
        rw [smul_smul, ← mul_pow, inv_mul_cancel₀ h0, one_pow, one_smul]
      have h2 : e ∈ L p := by
        rw [h1]
        exact smul_mem_lat L (pow_mem hu.2.2 _) (mem_sec.1 hn p hp)
      rw [(hfr p (hV p hp hu)).2, hae] at h2
      exact coord_mem hb h2 q
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨N, hN⟩ := exists_pow_smul_sec hT hc hv (hf l) (e := ∑ q, a q • b q) fun p hp hu => by
        refine sum_mem fun q _ => smul_mem_lat L ?_ (frame_mem (hfr p (hV p hp hu)) q)
        obtain ⟨n, hn⟩ := ha q
        have h0 : f l ≠ 0 := hu.1
        have h1 : a q = ((f l)⁻¹) ^ n * (f l ^ n * a q) := by
          rw [← _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ h0, one_pow, _root_.one_mul]
        rw [h1]
        exact mul_mem (pow_mem hu.2.2 _) (mem_regAt_of_mem hT hn hp)
      exact ⟨N, mem_sec.2 hN⟩
  · intro i j hi hj e he
    have hf : x i / x j ∈ chartRing ℤ x j := Algebra.subset_adjoin ⟨i, rfl⟩
    obtain ⟨N, hN⟩ := exists_pow_smul_sec hT hj hv hf (e := e) fun p hp hu => by
      refine mem_sec.1 he p ⟨hi, fun c' => ?_⟩
      have h1 : x c' / x i = (x c' / x j) * (x i / x j)⁻¹ := by
        field_simp
      rw [h1]
      exact mul_mem (hp.2 c') hu.2.2
    exact ⟨N, mem_sec.2 hN⟩

end GlobalTheory.CompanionTheory.Ar
