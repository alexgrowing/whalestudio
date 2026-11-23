import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalization
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermGenPtInjectiveRangeRegAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TieFrame

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

noncomputable def secVal (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (h : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom

theorem genMap_germ (U : X.Opens) (h : genPt ξ ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U) (t : Γ(X, U)) :
    genMap ξ q (X.presheaf.germ U q.1 hq t) = secVal ξ U h t := by
  have e : X.presheaf.germ U q.1 hq ≫ X.presheaf.stalkSpecializes q.2 = X.presheaf.germ U (genPt ξ) h :=
    TopCat.Presheaf.germ_stalkSpecializes X.presheaf hq q.2
  have e2 : X.presheaf.germ U q.1 hq ≫ (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) =
      X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ Scheme.stalkClosedPointTo ξ) e)
  exact congrArg (fun f => f.hom t) e2

theorem isUnit_iff_unitAt {q : Cpt ξ} (hi : Function.Injective (genMap ξ q)) (s : X.presheaf.stalk q.1) :
    IsUnit s ↔ unitAt ξ q (genMap ξ q s) := by
  constructor
  · intro hs
    have hu := hs.map (genMap ξ q)
    refine ⟨hu.ne_zero, ⟨s, rfl⟩, ?_⟩
    obtain ⟨u, rfl⟩ := hs
    refine ⟨(u⁻¹ : (X.presheaf.stalk q.1)ˣ).1, ?_⟩
    have : genMap ξ q u.1 * genMap ξ q (u⁻¹ : (X.presheaf.stalk q.1)ˣ).1 = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact eq_inv_of_mul_eq_one_right this
  · rintro ⟨h0, -, ⟨s', hs'⟩⟩
    have : s * s' = 1 := hi (by rw [map_mul, hs', map_one, mul_inv_cancel₀ h0])
    exact IsUnit.of_mul_eq_one _ this

theorem mem_basicOpen_iff (hg : IsCptGen ξ) (U : X.Opens) (h : genPt ξ ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U)
    (t : Γ(X, U)) : q.1 ∈ X.basicOpen t ↔ unitAt ξ q (secVal ξ U h t) := by
  rw [Scheme.mem_basicOpen X t q.1 hq, isUnit_iff_unitAt (hg.inj q), genMap_germ U h q hq]

theorem exists_unitAt_of_sum (hg : IsCptGen ξ) (p : Cpt ξ) {k : ℕ} (f c : Fin k → Ω)
    (hf : ∀ l, f l ∈ regAt ξ p) (hc : ∀ l, c l ∈ regAt ξ p) (h1 : ∑ l, c l * f l = 1) :
    ∃ l, unitAt ξ p (f l) := by
  choose f' hf' using hf
  choose c' hc' using hc
  have hs : ∑ l, c' l * f' l = 1 := (hg.inj p) (by simp [map_sum, hf', hc', h1])
  by_contra hno
  have hmem : ∀ l, c' l * f' l ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p.1) := fun l => by
    refine Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu => hno ⟨l, ?_⟩)
    have := (isUnit_iff_unitAt (hg.inj p) (f' l)).1 hu
    rwa [hf'] at this
  have := Ideal.sum_mem _ fun l (_ : l ∈ Finset.univ) => hmem l
  rw [hs] at this
  exact (Ideal.ne_top_iff_one _).1 (Ideal.IsPrime.ne_top inferInstance) this

theorem unitAt_or_of_add (hg : IsCptGen ξ) (p : Cpt ξ) {s t : Ω} (hs : s ∈ regAt ξ p) (ht : t ∈ regAt ξ p)
    (h : unitAt ξ p (s + t)) : unitAt ξ p s ∨ unitAt ξ p t := by
  obtain ⟨s', rfl⟩ := hs
  obtain ⟨t', rfl⟩ := ht
  rw [← map_add, ← isUnit_iff_unitAt (hg.inj p)] at h
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
  · exact Or.inl ((isUnit_iff_unitAt (hg.inj p) _).1 h)
  · exact Or.inr ((isUnit_iff_unitAt (hg.inj p) _).1 h)

theorem unitAt_mul {p : Cpt ξ} {s t : Ω} (hs : unitAt ξ p s) (ht : unitAt ξ p t) : unitAt ξ p (s * t) :=
  ⟨mul_ne_zero hs.1 ht.1, mul_mem hs.2.1 ht.2.1, by rw [mul_inv]; exact mul_mem hs.2.2 ht.2.2⟩

theorem unitAt_pow {p : Cpt ξ} {s : Ω} (hs : unitAt ξ p s) (n : ℕ) : unitAt ξ p (s ^ n) :=
  ⟨pow_ne_zero _ hs.1, pow_mem hs.2.1 _, by rw [← inv_pow]; exact pow_mem hs.2.2 _⟩

theorem unitAt_of_mul {p : Cpt ξ} {s t : Ω} (hs : s ∈ regAt ξ p) (ht : t ∈ regAt ξ p) (h : unitAt ξ p (s * t)) :
    unitAt ξ p t := by
  refine ⟨right_ne_zero_of_mul h.1, ht, ?_⟩
  have : t⁻¹ = s * (s * t)⁻¹ := by
    have h0 := left_ne_zero_of_mul h.1
    have h1 := right_ne_zero_of_mul h.1
    field_simp
  rw [this]
  exact mul_mem hs h.2.2

theorem unitAt_one (p : Cpt ξ) : unitAt ξ p 1 := ⟨one_ne_zero, one_mem _, by simp [one_mem]⟩

theorem not_unitAt_zero (p : Cpt ξ) : ¬ unitAt ξ p 0 := fun h => h.1 rfl

theorem regAt_genPt (hg : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ (⟨genPt ξ, specializes_rfl⟩ : Cpt ξ) := by
  obtain ⟨s, rfl⟩ := hg.bij.2 a
  refine ⟨s, ?_⟩
  unfold genMap
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  erw [Category.id_comp]
  rfl

section Chart

variable {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}

theorem exists_chart (hT : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) :
    ∃ (U : X.Opens) (h : genPt ξ ∈ U), IsAffineOpen U ∧ (∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q) ∧
      (∀ q : X, q ∈ U → genPt ξ ⤳ q) ∧
      Function.Injective (secVal ξ U h) ∧
      ∀ a : Ω, a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) ↔ a ∈ (secVal ξ U h).range := by
  obtain ⟨U, hU, hmem⟩ := hT.affine c hc
  have h : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, hc, fun c' => regAt_genPt hT.gen _⟩
  have hsp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => by
    obtain ⟨h2, _⟩ := (hmem q).1 hq
    exact h2
  have hUq : ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q := fun q =>
    ⟨fun hq => by obtain ⟨_, h2⟩ := (hmem q.1).1 hq; exact h2, fun hq => (hmem q.1).2 ⟨q.2, hq⟩⟩
  obtain ⟨hinj, hran⟩ := regAt_sections X Ω ξ hT.gen U h hsp
  refine ⟨U, h, hU, hUq, hsp, hinj, fun a => ?_⟩
  rw [hT.ring c hc a]
  refine Iff.trans ?_ (hran a).symm
  exact forall_congr' fun q => (by rw [hUq q])

theorem exists_point (hT : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) (P : Ideal (chartRing o x c)) (hP : P.IsPrime) :
    ∃ p : Cpt ξ, InChart ξ x c p ∧ ∀ s : chartRing o x c, s ∈ P ↔ ¬ unitAt ξ p s := by
  obtain ⟨U, h, hU, hUq, hsp, -, hran⟩ := exists_chart hT hc
  let φ : Γ(X, U) →+* chartRing o x c :=
    (secVal ξ U h).codRestrict (chartRing o x c) fun t => (hran _).2 ⟨t, rfl⟩
  let y : PrimeSpectrum Γ(X, U) := ⟨P.comap φ, inferInstance⟩
  have hyU : hU.fromSpec y ∈ U := by
    have : hU.fromSpec y ∈ Set.range hU.fromSpec := ⟨y, rfl⟩
    rwa [hU.range_fromSpec] at this
  let q : Cpt ξ := ⟨_, hsp _ hyU⟩
  refine ⟨q, (hUq q).1 hyU, fun s => ?_⟩
  obtain ⟨t, ht⟩ := (hran s).1 s.2
  have hst : s = φ t := Subtype.ext ht.symm
  have key : q.1 ∈ X.basicOpen t ↔ t ∉ P.comap φ := by
    show y ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen t ↔ _
    rw [hU.fromSpec_preimage_basicOpen]
    rfl
  have h2 := mem_basicOpen_iff hT.gen U h q hyU t
  have h3 : (s : Ω) = secVal ξ U h t := ht.symm
  rw [h3, ← h2, key, hst, Ideal.mem_comap, not_not]

theorem exists_basic (hT : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) (V : X.Opens) {q : Cpt ξ}
    (hq : InChart ξ x c q) (hV : q.1 ∈ V) :
    ∃ g ∈ chartRing o x c, unitAt ξ q g ∧ ∀ p : Cpt ξ, InChart ξ x c p → unitAt ξ p g → p.1 ∈ V := by
  obtain ⟨U, h, hU, hUq, hsp, -, hran⟩ := exists_chart hT hc
  obtain ⟨f, hle, hmem⟩ := hU.exists_basicOpen_le (⟨q.1, hV⟩ : V) ((hUq q).2 hq)
  refine ⟨secVal ξ U h f, (hran _).2 ⟨f, rfl⟩, (mem_basicOpen_iff hT.gen U h q ((hUq q).2 hq) f).1 hmem,
    fun p hp hu => hle ((mem_basicOpen_iff hT.gen U h p ((hUq p).2 hp) f).2 hu)⟩

theorem ideal_eq_top (hT : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) (I : Ideal (chartRing o x c))
    (h : ∀ p : Cpt ξ, InChart ξ x c p → ∃ s ∈ I, unitAt ξ p s) : I = ⊤ := by
  by_contra hI
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨p, hp, hs⟩ := exists_point hT hc M hM.isPrime
  obtain ⟨s, hsI, hu⟩ := h p hp
  exact (hs s).1 (hle hsI) hu

theorem chart_le_regAt (hT : CoordTie o ξ x) {c : κ} {p : Cpt ξ} (hp : InChart ξ x c p) {a : Ω}
    (ha : a ∈ chartRing o x c) : a ∈ regAt ξ p :=
  (hT.ring c hp.1 a).1 ha p hp

theorem exists_den (hT : CoordTie o ξ x) {c : κ} {p : Cpt ξ} (hp : InChart ξ x c p) {a : Ω}
    (ha : a ∈ regAt ξ p) : ∃ s ∈ chartRing o x c, unitAt ξ p s ∧ s * a ∈ chartRing o x c :=
  (regAt_iff_exists_chart_fraction X Ω ξ o κ x hT c p hp a).1 ha

theorem exists_pow_mul_mem (hT : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) {f a : Ω} (hf : f ∈ chartRing o x c)
    (h : ∀ p : Cpt ξ, InChart ξ x c p → unitAt ξ p f → a ∈ regAt ξ p) :
    ∃ n : ℕ, f ^ n * a ∈ chartRing o x c := by
  let I : Ideal (chartRing o x c) :=
    { carrier := {s | (s : Ω) * a ∈ chartRing o x c}
      add_mem' := fun {u v} hu hv => by
        show ((u + v : chartRing o x c) : Ω) * a ∈ chartRing o x c
        have : ((u + v : chartRing o x c) : Ω) * a = (u : Ω) * a + (v : Ω) * a := by
          push_cast; ring
        rw [this]
        exact add_mem hu hv
      zero_mem' := by
        show ((0 : chartRing o x c) : Ω) * a ∈ chartRing o x c
        simp
      smul_mem' := fun t u hu => by
        show ((t • u : chartRing o x c) : Ω) * a ∈ chartRing o x c
        have : ((t • u : chartRing o x c) : Ω) * a = (t : Ω) * ((u : Ω) * a) := by
          simp [_root_.mul_assoc]
        rw [this]
        exact mul_mem t.2 hu }
  have hrad : (⟨f, hf⟩ : chartRing o x c) ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hle, hP⟩
    by_contra hfP
    obtain ⟨p, hp, hs⟩ := exists_point hT hc P hP
    have hu : unitAt ξ p f := by
      by_contra hn
      exact hfP ((hs ⟨f, hf⟩).2 hn)
    obtain ⟨s, hsA, hsu, hsa⟩ := exists_den hT hp (h p hp hu)
    exact (hs ⟨s, hsA⟩).1 (hle hsa) hsu
  obtain ⟨n, hn⟩ := hrad
  exact ⟨n, hn⟩

variable {E : Type} [AddCommGroup E] [Module Ω E]

theorem mem_of_smul_mem {p : Cpt ξ} (N : Submodule (regAt ξ p) E) {s : Ω} (hs : unitAt ξ p s) {e : E}
    (h : s • e ∈ N) : e ∈ N := by
  have := N.smul_mem ⟨s⁻¹, hs.2.2⟩ h
  rwa [Subring.smul_def, smul_smul, inv_mul_cancel₀ hs.1, one_smul] at this

theorem smul_mem_reg {p : Cpt ξ} (N : Submodule (regAt ξ p) E) {a : Ω} (ha : a ∈ regAt ξ p) {e : E}
    (h : e ∈ N) : a • e ∈ N :=
  N.smul_mem ⟨a, ha⟩ h

theorem exists_den_span (hT : CoordTie o ξ x) {c : κ} {p : Cpt ξ} (hp : InChart ξ x c p) (M : AddSubgroup E)
    (hM : ∀ a ∈ chartRing o x c, ∀ e ∈ M, a • e ∈ M) {e : E}
    (he : e ∈ Submodule.span (regAt ξ p) (M : Set E)) :
    ∃ s ∈ chartRing o x c, unitAt ξ p s ∧ s • e ∈ M := by
  induction he using Submodule.span_induction with
  | mem v hv => exact ⟨1, one_mem _, unitAt_one p, by simpa using hv⟩
  | zero => exact ⟨1, one_mem _, unitAt_one p, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨s, hs, hsu, hsM⟩ := hu
    obtain ⟨t, ht, htu, htM⟩ := hv
    refine ⟨s * t, mul_mem hs ht, unitAt_mul hsu htu, ?_⟩
    have h1 : (s * t) • (u + v) = t • s • u + s • t • v := by
      rw [smul_add, smul_smul, smul_smul, mul_comm t s]
    rw [h1]
    exact add_mem (hM t ht _ hsM) (hM s hs _ htM)
  | smul r u _ hu =>
    obtain ⟨s, hs, hsu, hsM⟩ := hu
    obtain ⟨t, ht, htu, htr⟩ := exists_den hT hp r.2
    refine ⟨t * s, mul_mem ht hs, unitAt_mul htu hsu, ?_⟩
    have h1 : (t * s) • r • u = (t * (r : Ω)) • s • u := by
      rw [Subring.smul_def, smul_smul, smul_smul]
      congr 1
      ring
    rw [h1]
    exact hM _ htr _ hsM

theorem coords_mem {p : Cpt ξ} {r : ℕ} {b : Fin r → E} (hli : LinearIndependent Ω b) {a : Fin r → Ω}
    (h : ∑ i, a i • b i ∈ Submodule.span (regAt ξ p) (Set.range b)) (i : Fin r) : a i ∈ regAt ξ p := by
  obtain ⟨a', ha'⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h
  have h0 : ∑ i, ((a' i : Ω) - a i) • b i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← ha']
    simp [Subring.smul_def]
  have h1 := Fintype.linearIndependent_iff.1 hli _ h0 i
  rw [← sub_eq_zero.1 h1]
  exact (a' i).2

theorem exists_frame_basic (hT : CoordTie o ξ x) {L : Lat ξ E} {r : ℕ} (hVB : L.IsVB r ⊤) {c : κ}
    {p₀ : Cpt ξ} (hp₀ : InChart ξ x c p₀) :
    ∃ g ∈ chartRing o x c, ∃ b : Fin r → E, unitAt ξ p₀ g ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ p : Cpt ξ, InChart ξ x c p → unitAt ξ p g → L.IsFrameAt b p := by
  obtain ⟨V, hV, b, hb, hfr⟩ := hVB p₀ (Set.mem_univ _)
  obtain ⟨g, hg, hu, hgV⟩ := exists_basic hT hp₀.1 V hp₀ hV
  exact ⟨g, hg, b, hu, hb, fun p hp hup => hfr p (Set.mem_univ _) (hgV p hp hup)⟩

theorem exists_pow_smul_mem (hT : CoordTie o ξ x) {L : Lat ξ E} {r : ℕ} (hVB : L.IsVB r ⊤) {c : κ}
    (hc : x c ≠ 0) {h : Ω} (hh : h ∈ chartRing o x c) {v : E}
    (hM : ∀ p : Cpt ξ, InChart ξ x c p → unitAt ξ p h → v ∈ L p) :
    ∃ n : ℕ, ∀ p : Cpt ξ, InChart ξ x c p → h ^ n • v ∈ L p := by
  let N : Ideal (chartRing o x c) :=
    { carrier := {s | ∃ n : ℕ, ∀ p : Cpt ξ, InChart ξ x c p → unitAt ξ p s → h ^ n • v ∈ L p}
      add_mem' := by
        rintro u w ⟨n, hn⟩ ⟨m, hm⟩
        refine ⟨n + m, fun p hp hu => ?_⟩
        have hu' : unitAt ξ p ((u : Ω) + w) := hu
        rcases unitAt_or_of_add hT.gen p (chart_le_regAt hT hp u.2)
          (chart_le_regAt hT hp w.2) hu' with h1 | h1
        · rw [add_comm, pow_add, mul_smul]
          exact smul_mem_reg (L p) (pow_mem (chart_le_regAt hT hp hh) _) (hn p hp h1)
        · rw [pow_add, mul_smul]
          exact smul_mem_reg (L p) (pow_mem (chart_le_regAt hT hp hh) _) (hm p hp h1)
      zero_mem' := ⟨0, fun p _ hu => absurd hu (not_unitAt_zero p)⟩
      smul_mem' := by
        rintro t u ⟨n, hn⟩
        refine ⟨n, fun p hp hu => hn p hp ?_⟩
        have hu' : unitAt ξ p ((t : Ω) * u) := hu
        exact unitAt_of_mul (chart_le_regAt hT hp t.2) (chart_le_regAt hT hp u.2) hu' }
  have hN : N = ⊤ := ideal_eq_top hT hc N fun p₀ hp₀ => by
    obtain ⟨g, hg, b, hu, hspan, hfr⟩ := exists_frame_basic hT hVB hp₀
    refine ⟨⟨g, hg⟩, ?_, hu⟩
    have hmem : v ∈ Submodule.span Ω (Set.range b) := by rw [hspan]; trivial
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 hmem
    have hreg : ∀ i, ∃ n : ℕ, (h * g) ^ n * a i ∈ chartRing o x c := fun i =>
      exists_pow_mul_mem hT hc (mul_mem hh hg) fun p hp hup => by
        have uh : unitAt ξ p h := unitAt_of_mul (chart_le_regAt hT hp hg)
          (chart_le_regAt hT hp hh) (by rwa [mul_comm] at hup)
        have ug : unitAt ξ p g := unitAt_of_mul (chart_le_regAt hT hp hh)
          (chart_le_regAt hT hp hg) hup
        refine coords_mem (hfr p hp ug).1 ?_ i
        rw [ha, ← (hfr p hp ug).2]
        exact hM p hp uh
    choose n hn using hreg
    have hm : ∀ i, (h * g) ^ (∑ i, n i) * a i ∈ chartRing o x c := fun i => by
      have hle : n i ≤ ∑ i, n i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have : (h * g) ^ (∑ i, n i) * a i = (h * g) ^ (∑ i, n i - n i) * ((h * g) ^ n i * a i) := by
        rw [← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
      rw [this]
      exact mul_mem (pow_mem (mul_mem hh hg) _) (hn i)
    refine ⟨∑ i, n i, fun p hp hup => ?_⟩
    have hup' : unitAt ξ p g := hup
    refine mem_of_smul_mem (L p) (unitAt_pow hup' (∑ i, n i)) ?_
    have h1 : g ^ (∑ i, n i) • h ^ (∑ i, n i) • v = ∑ i, ((h * g) ^ (∑ i, n i) * a i) • b i := by
      rw [← ha, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, smul_smul, mul_pow, mul_comm (g ^ _)]
    rw [h1]
    refine sum_mem fun i _ => smul_mem_reg (L p) (chart_le_regAt hT hp (hm i)) ?_
    rw [(hfr p hp hup').2]
    exact Submodule.subset_span ⟨i, rfl⟩
  have h1 : (1 : chartRing o x c) ∈ N := by rw [hN]; trivial
  obtain ⟨n, hn⟩ := h1
  exact ⟨n, fun p hp => hn p hp (unitAt_one p)⟩

theorem exists_uniform (hT : CoordTie o ξ x) {L : Lat ξ E} {r : ℕ} (hVB : L.IsVB r ⊤) {c : κ} (hc : x c ≠ 0)
    {q : Cpt ξ} (hq : InChart ξ x c q) {e : E} (he : e ∈ L q) :
    ∃ s ∈ chartRing o x c, unitAt ξ q s ∧ ∀ p : Cpt ξ, InChart ξ x c p → s • e ∈ L p := by
  obtain ⟨h, hh, b₀, huq, -, hfr₀⟩ := exists_frame_basic hT hVB hq
  let M : AddSubgroup E :=
    { carrier := {v | ∀ p : Cpt ξ, InChart ξ x c p → unitAt ξ p h → v ∈ L p}
      add_mem' := fun ha hb p hp hu => add_mem (ha p hp hu) (hb p hp hu)
      zero_mem' := fun p _ _ => zero_mem _
      neg_mem' := fun ha p hp hu => neg_mem (ha p hp hu) }
  have hMs : ∀ a ∈ chartRing o x c, ∀ v ∈ M, a • v ∈ M := fun a ha v hv p hp hu =>
    smul_mem_reg (L p) (chart_le_regAt hT hp ha) (hv p hp hu)
  have he' : e ∈ Submodule.span (regAt ξ q) (M : Set E) := by
    rw [(hfr₀ q hq huq).2] at he
    refine Submodule.span_mono ?_ he
    rintro _ ⟨i, rfl⟩ p hp hu
    rw [(hfr₀ p hp hu).2]
    exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨s₀, hs₀, hu₀, hM⟩ := exists_den_span hT hq M hMs he'
  obtain ⟨n, hn⟩ := exists_pow_smul_mem hT hVB hc hh hM
  refine ⟨h ^ n * s₀, mul_mem (pow_mem hh n) hs₀, unitAt_mul (unitAt_pow huq n) hu₀, fun p hp => ?_⟩
  rw [mul_smul]
  exact hn p hp

end Chart

end GlobalTheory.CompanionTheory.Ar.TieFrame

namespace GlobalTheory.CompanionTheory.Ar

theorem isFrameOver_iff_forall_isFrameAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (E : Type) [AddCommGroup E] [Module Ω E] (r : ℕ) (W : ChartBundle ℤ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) r E) (L : Lat ξ E), CoordTie ℤ ξ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) → L.IsVB r ⊤ → L.IsChartOf (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) W.lat → ∀ (c : (k : K) → J k) (f : Ω) (b : Fin r → E), GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y c ≠ 0 → f ∈ chartRing ℤ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) c → f ≠ 0 → (GroundTheory.Heights₂.Heights.LowerBoundFree.IsFrameOver y W c f b ↔ ∀ p : Cpt ξ, InChart ξ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) c p → unitAt ξ p f → L.IsFrameAt b p) := by
  intro X Ω _ ξ K _ J _ y E _ _ r W L hT hVB hch c f b hc hf hf0
  constructor
  · rintro ⟨-, -, -, hli, hb⟩ p hp hu
    refine ⟨hli, le_antisymm (fun e he => ?_) (Submodule.span_le.2 ?_)⟩
    · obtain ⟨s, -, hsu, hse⟩ := TieFrame.exists_uniform hT hVB hc hp he
      obtain ⟨a, ha, hsum⟩ := (hb (s • e)).1 ⟨0, by simpa using (hch c hc _).2 hse⟩
      refine TieFrame.mem_of_smul_mem _ hsu ?_
      rw [hsum]
      refine sum_mem fun q _ => TieFrame.smul_mem_reg _ ?_ (Submodule.subset_span ⟨q, rfl⟩)
      obtain ⟨n, hn⟩ := ha q
      have h1 : a q = (f⁻¹) ^ n * (f ^ n * a q) := by
        rw [← _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ hu.1, one_pow, _root_.one_mul]
      rw [h1]
      exact mul_mem (pow_mem hu.2.2 n) (TieFrame.chart_le_regAt hT hp hn)
    · rintro _ ⟨q, rfl⟩
      obtain ⟨n, hn⟩ := (hb (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by
        rw [pow_zero, _root_.one_mul]
        by_cases h : q' = q
        · subst h; simp only [Pi.single_eq_same]; exact one_mem _
        · rw [Pi.single_eq_of_ne h]; exact zero_mem _⟩, by simp [Pi.single_apply]⟩
      exact TieFrame.mem_of_smul_mem _ (TieFrame.unitAt_pow hu n) ((hch c hc _).1 hn p hp)
  · intro hfr
    let p₀ : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
    have hreg : ∀ a : Ω, a ∈ regAt ξ p₀ := TieFrame.regAt_genPt hT.gen
    have hp₀ : InChart ξ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) c p₀ :=
      ⟨hc, fun c' => hreg _⟩
    have hu₀ : unitAt ξ p₀ f := ⟨hf0, hreg _, hreg _⟩
    have h₀ := hfr p₀ hp₀ hu₀
    refine ⟨hc, hf, hf0, h₀.1, fun e => ⟨?_, ?_⟩⟩
    · rintro ⟨n, hn⟩
      have heL : ∀ p : Cpt ξ, InChart ξ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) c p →
          unitAt ξ p f → e ∈ L p := fun p hp hu =>
        TieFrame.mem_of_smul_mem (L p) (TieFrame.unitAt_pow hu n) ((hch c hc _).1 hn p hp)
      have he0 : e ∈ Submodule.span (regAt ξ p₀) (Set.range b) := by
        rw [← h₀.2]
        exact heL p₀ hp₀ hu₀
      obtain ⟨a', ha'⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he0
      have hsum : ∑ i, (a' i : Ω) • b i = e := by simpa [Subring.smul_def] using ha'
      refine ⟨fun q => (a' q : Ω), fun q => TieFrame.exists_pow_mul_mem hT hc hf fun p hp hu => ?_, hsum.symm⟩
      refine TieFrame.coords_mem (hfr p hp hu).1 (a := fun q => (a' q : Ω)) ?_ q
      rw [hsum, ← (hfr p hp hu).2]
      exact heL p hp hu
    · rintro ⟨a, ha, rfl⟩
      have hM : ∀ p : Cpt ξ, InChart ξ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) c p →
          unitAt ξ p f → ∑ q, a q • b q ∈ L p := fun p hp hu => by
        rw [(hfr p hp hu).2]
        refine sum_mem fun q _ => TieFrame.smul_mem_reg _ ?_ (Submodule.subset_span ⟨q, rfl⟩)
        obtain ⟨n, hn⟩ := ha q
        have h1 : a q = (f⁻¹) ^ n * (f ^ n * a q) := by
          rw [← _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ hu.1, one_pow, _root_.one_mul]
        rw [h1]
        exact mul_mem (pow_mem hu.2.2 n) (TieFrame.chart_le_regAt hT hp hn)
      obtain ⟨n, hn⟩ := TieFrame.exists_pow_smul_mem hT hVB hc hf hM
      exact ⟨n, (hch c hc _).2 hn⟩

end GlobalTheory.CompanionTheory.Ar
