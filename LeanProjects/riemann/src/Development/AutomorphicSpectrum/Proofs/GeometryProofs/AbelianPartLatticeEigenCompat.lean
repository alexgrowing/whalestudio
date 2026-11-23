import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValues
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.FinFrame

section Sat

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]

def sat (𝔭 : Ideal A) [h𝔭 : 𝔭.IsPrime] (N : Submodule A M) : Submodule A M where
  carrier := {x | ∃ t ∉ 𝔭, t • x ∈ N}
  add_mem' := by
    rintro a b ⟨t, ht, ha⟩ ⟨t', ht', hb⟩
    refine ⟨t * t', h𝔭.mul_notMem ht ht', ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem _ ha
    · rw [mul_smul]; exact N.smul_mem _ hb
  zero_mem' := ⟨1, (Ideal.ne_top_iff_one _).1 h𝔭.ne_top, by simp⟩
  smul_mem' := by
    rintro c x ⟨t, ht, hx⟩
    exact ⟨t, ht, by rw [smul_comm]; exact N.smul_mem _ hx⟩

theorem mem_sat {𝔭 : Ideal A} [𝔭.IsPrime] {N : Submodule A M} {x : M} :
    x ∈ sat 𝔭 N ↔ ∃ t ∉ 𝔭, t • x ∈ N := Iff.rfl

theorem span_sat_iff (𝔭 : Ideal A) [h𝔭 : 𝔭.IsPrime] {N G : Submodule A M} (h1 : N ≤ G) (h2 : G ≤ sat 𝔭 N) (x : M) :
    x ∈ Submodule.span A {x | ∃ s ∉ 𝔭, s • x ∈ G} ↔ ∃ t ∉ 𝔭, t • x ∈ N := by
  constructor
  · intro hx
    have : Submodule.span A {x | ∃ s ∉ 𝔭, s • x ∈ G} ≤ sat 𝔭 N := by
      refine Submodule.span_le.2 ?_
      rintro y ⟨s, hs, hy⟩
      obtain ⟨t, ht, h⟩ := h2 hy
      exact ⟨t * s, h𝔭.mul_notMem ht hs, by rwa [mul_smul]⟩
    exact this hx
  · rintro ⟨t, ht, h⟩
    exact Submodule.subset_span ⟨t, ht, h1 h⟩

end Sat

section Frames

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem exists_germs {p : Cpt ξ} {Vl : Lat ξ E} {m : ℕ} {u u' : Fin m → E} (hu : Vl.IsFrameAt u p)
    (hu' : Vl.IsFrameAt u' p) (k : Fin m) :
    ∃ c : Fin m → X.presheaf.stalk p.1, u' k = ∑ j, genMap ξ p (c j) • u j := by
  have h : u' k ∈ Vl p := by
    rw [hu'.2]
    exact Submodule.subset_span ⟨k, rfl⟩
  rw [hu.2] at h
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h
  have hg : ∀ j, ∃ σ, genMap ξ p σ = (c j : Ω) := fun j => (c j).2
  choose σ hσ using hg
  refine ⟨σ, ?_⟩
  rw [← hc]
  exact Finset.sum_congr rfl fun j _ => by rw [hσ]; rfl

theorem frame_compare (hξ : IsCptGen ξ) {F : Type} [Field F] (w : Sp F ⟶ X) (h : genPt ξ ⤳ centre w)
    (Vl : Lat ξ E) {m : ℕ} {s b : Fin m → E}
    (hs : Vl.IsFrameAt s ⟨centre w, h⟩) (hb : Vl.IsFrameAt b ⟨centre w, h⟩) :
    ∃ (T' : Matrix (Fin m) (Fin m) Ω) (T : Matrix (Fin m) (Fin m) F),
      (∀ k, b k = ∑ k', T' k' k • s k') ∧ (∀ i j, ValAt ξ w (T' i j) (T i j)) ∧ T.det ≠ 0 := by
  classical
  choose A hA using exists_germs hs hb
  choose B hB using exists_germs hb hs
  set g := genMap ξ ⟨centre w, h⟩ with hg
  set ψ := (Scheme.stalkClosedPointTo w).hom with hψ
  let Ts : Matrix (Fin m) (Fin m) (X.presheaf.stalk (centre w)) := Matrix.of fun i j => A j i
  let Ds : Matrix (Fin m) (Fin m) (X.presheaf.stalk (centre w)) := Matrix.of fun i j => B j i
  have e : ∀ k, ∑ j, g ((Ts * Ds) j k) • s j = s k := fun k => by
    conv_rhs => rw [hB k]
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hA l, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, mul_comm]
    rfl
  have e1 : Ts * Ds = 1 := by
    ext j k
    have hz := Fintype.linearIndependent_iff.1 hs.1 (fun j => g ((Ts * Ds) j k) - if j = k then 1 else 0) (by
      simp [sub_smul, Finset.sum_sub_distrib, e k]) j
    refine hξ.inj ⟨centre w, h⟩ (sub_eq_zero.1 hz |>.trans ?_)
    rw [Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨Ts.map g, Ts.map ψ, fun k => ?_, fun i j => ⟨h, Ts i j, rfl, rfl⟩, ?_⟩
  · rw [hA k]; rfl
  · have e2 : (Ts.map ψ) * (Ds.map ψ) = 1 := by
      refine (Matrix.map_mul (f := ψ) (L := Ts) (M := Ds)).symm.trans ?_
      rw [e1]
      exact Matrix.map_one _ (map_zero ψ) (map_one ψ)
    intro h0
    have := congrArg Matrix.det e2
    rw [Matrix.det_mul, h0] at this
    simp at this

end Frames

section Point

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {L : Type} [Field L] [NumberField L]

theorem exists_bot_point (z : Sp (𝓞 L) ⟶ X) :
    ∃ o₀ : PrimeSpectrum (𝓞 L), o₀.asIdeal = ⊥ ∧ z o₀ = centre (spMap (algebraMap (𝓞 L) L) ≫ z) := by
  refine ⟨(spMap (algebraMap (𝓞 L) L)) (IsLocalRing.closedPoint L), ?_, ?_⟩
  · have : ((spMap (algebraMap (𝓞 L) L)) (IsLocalRing.closedPoint L)).asIdeal =
        (IsLocalRing.maximalIdeal L).comap (algebraMap (𝓞 L) L) := rfl
    rw [this, IsLocalRing.maximalIdeal_eq_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective _ _)
  · simp [centre]
    rfl

theorem centre_specializes (z : Sp (𝓞 L) ⟶ X) (𝔭 : PrimeSpectrum (𝓞 L)) :
    centre (spMap (algebraMap (𝓞 L) L) ≫ z) ⤳ z 𝔭 := by
  obtain ⟨o₀, h0, h1⟩ := exists_bot_point z
  rw [← h1]
  refine Specializes.map ((PrimeSpectrum.le_iff_specializes _ _).1 ?_) z.continuous
  show o₀.asIdeal ≤ 𝔭.asIdeal
  rw [h0]
  exact bot_le

theorem reg_value (z : Sp (𝓞 L) ⟶ X) (hξ : IsCptGen ξ) (𝔭 : PrimeSpectrum (𝓞 L)) (h : genPt ξ ⤳ z 𝔭) {a : Ω}
    (ha : a ∈ regAt ξ ⟨z 𝔭, h⟩) :
    ∃ (r : L) (t n : 𝓞 L), ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) a r ∧ t ∉ 𝔭.asIdeal ∧
      algebraMap (𝓞 L) L t * r = algebraMap (𝓞 L) L n := by
  classical
  let A := Localization.AtPrime 𝔭.asIdeal
  have hunit : ∀ d : 𝔭.asIdeal.primeCompl, IsUnit (algebraMap (𝓞 L) L d) := fun d =>
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2
      fun e => d.2 (e ▸ 𝔭.asIdeal.zero_mem))
  let jL : A →+* L := IsLocalization.lift (M := 𝔭.asIdeal.primeCompl) hunit
  have hjL : ∀ x, jL (algebraMap (𝓞 L) A x) = algebraMap (𝓞 L) L x := fun x => IsLocalization.lift_eq hunit x
  set zA : Sp A ⟶ X := spMap (algebraMap (𝓞 L) A) ≫ z with hzA
  have hzL : spMap (algebraMap (𝓞 L) L) ≫ z = spMap jL ≫ zA := by
    have e : algebraMap (𝓞 L) L = jL.comp (algebraMap (𝓞 L) A) := RingHom.ext fun x => (hjL x).symm
    rw [hzA, ← Category.assoc, e]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hc : z 𝔭 = centre zA := by
    have e : (spMap (algebraMap (𝓞 L) A)) (IsLocalRing.closedPoint A) = 𝔭 := by
      apply PrimeSpectrum.ext
      show (IsLocalRing.maximalIdeal A).comap (algebraMap (𝓞 L) A) = 𝔭.asIdeal
      exact Localization.AtPrime.comap_maximalIdeal
    show z 𝔭 = z ((spMap (algebraMap (𝓞 L) A)) (IsLocalRing.closedPoint A))
    rw [e]
  have key : ∀ (q : X) (hq : q = centre zA) (h' : genPt ξ ⤳ q), a ∈ regAt ξ ⟨q, h'⟩ →
      ∃ r, ValAt ξ zA a r := by
    intro q hq h' ha'
    subst hq
    obtain ⟨s, hs⟩ := ha'
    exact ⟨_, h', s, hs, rfl⟩
  obtain ⟨r, hr⟩ := key _ hc h ha
  obtain ⟨n, d, rfl⟩ := IsLocalization.exists_mk'_eq 𝔭.asIdeal.primeCompl r
  refine ⟨jL (IsLocalization.mk' A n d), d, n, ?_, d.2, ?_⟩
  · rw [hzL]
    exact LieTangent.valAt_base hξ jL hr
  · rw [← hjL, ← hjL, ← map_mul, mul_comm]
    exact congrArg jL (IsLocalization.mk'_spec A n d)

theorem prime_cases (𝔭 : PrimeSpectrum (𝓞 L)) : 𝔭.asIdeal = ⊥ ∨ ∃ v : FinitePlace L, primeOf v = 𝔭 := by
  by_cases h : 𝔭.asIdeal = ⊥
  · exact Or.inl h
  · refine Or.inr ⟨FinitePlace.mk ⟨𝔭.asIdeal, 𝔭.isPrime, h⟩, ?_⟩
    apply PrimeSpectrum.ext
    show (FinitePlace.maximalIdeal (FinitePlace.mk ⟨𝔭.asIdeal, 𝔭.isPrime, h⟩)).asIdeal = _
    rw [FinitePlace.maximalIdeal_mk]

theorem bad_finite {m : ℕ} (T : Matrix (Fin m) (Fin m) L) (hT : T.det ≠ 0) :
    {v : FinitePlace L | ¬ ((∀ i j, v (T i j) ≤ 1) ∧ v T.det = 1)}.Finite := by
  classical
  have h1 : (Function.mulSupport fun v : FinitePlace L => v T.det).Finite := FinitePlace.mulSupport_finite hT
  have h2 : ∀ i j, {v : FinitePlace L | ¬ v (T i j) ≤ 1}.Finite := fun i j => by
    by_cases h0 : T i j = 0
    · simp [h0]
    · refine Set.Finite.subset (FinitePlace.mulSupport_finite h0) fun v hv e => hv ?_
      exact (show v (T i j) = 1 from e).le
  refine (h1.union (Set.finite_iUnion fun i => Set.finite_iUnion fun j => h2 i j)).subset fun v hv => ?_
  by_cases hd : v T.det = 1
  · refine Or.inr ?_
    have : ¬ ∀ i j, v (T i j) ≤ 1 := fun h => hv ⟨h, hd⟩
    push_neg at this
    obtain ⟨i, j, hij⟩ := this
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, not_le.2 hij⟩⟩
  · exact Or.inl hd

end Point

section Span

variable {L : Type} [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V] [Module (𝓞 L) V]
  [IsScalarTower (𝓞 L) L V]

theorem exists_smul_mem_iff {I₀ : Type} (g : I₀ → V) (x : V) :
    (∃ t : 𝓞 L, t ≠ 0 ∧ t • x ∈ Submodule.span (𝓞 L) (Set.range g)) ↔ x ∈ Submodule.span L (Set.range g) := by
  constructor
  · rintro ⟨t, ht, hx⟩
    have h1 : Submodule.span (𝓞 L) (Set.range g) ≤ (Submodule.span L (Set.range g)).restrictScalars (𝓞 L) :=
      Submodule.span_le.2 fun y hy => Submodule.subset_span hy
    have h2 : algebraMap (𝓞 L) L t • x ∈ Submodule.span L (Set.range g) := by
      rw [algebraMap_smul]
      exact h1 hx
    have h3 : algebraMap (𝓞 L) L t ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 ht
    exact (Submodule.smul_mem_iff _ h3).1 h2
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, one_ne_zero, by simpa using Submodule.subset_span hy⟩
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨t, ht, ha⟩ := ha
      obtain ⟨t', ht', hb⟩ := hb
      refine ⟨t * t', mul_ne_zero ht ht', ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ ha
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hb
    | smul c a _ ha =>
      obtain ⟨t, ht, ha⟩ := ha
      obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) c
      have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
      have hd1 : algebraMap (𝓞 L) L d ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 hd0
      refine ⟨d * t, mul_ne_zero hd0 ht, ?_⟩
      have e : (d * t) • (algebraMap (𝓞 L) L n / algebraMap (𝓞 L) L d) • a = n • t • a := by
        calc (d * t) • (algebraMap (𝓞 L) L n / algebraMap (𝓞 L) L d) • a
            = algebraMap (𝓞 L) L (d * t) • (algebraMap (𝓞 L) L n / algebraMap (𝓞 L) L d) • a :=
              (algebraMap_smul L _ _).symm
          _ = (algebraMap (𝓞 L) L n * algebraMap (𝓞 L) L t) • a := by
              rw [smul_smul, map_mul]
              congr 1
              field_simp
          _ = n • t • a := by
              rw [mul_smul, algebraMap_smul, algebraMap_smul]
      rw [e]
      exact Submodule.smul_mem _ _ ha

end Span

section Core

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]
  {Li : Type} [AddCommGroup Li] [Module Ω Li]

section Val

variable {F : Type} [Field F] {w : Sp F ⟶ X} {V : Type} [AddCommGroup V] [Module F V]
  {M : LieModel G ξ Li} {ML : LieModel G w V}

theorem val_smul {a : Ω} {r : F} {e : Li} {x : V} (ha : ValAt ξ w a r) (he : M.ValAt w e (ML.pt x)) :
    M.ValAt w (a • e) (ML.pt (r • x)) := by
  obtain ⟨h, σ, rfl, rfl⟩ := ha
  rw [ML.pt_smul]
  exact he.smul h σ

theorem val_add {e e' : Li} {x x' : V} (he : M.ValAt w e (ML.pt x)) (he' : M.ValAt w e' (ML.pt x')) :
    M.ValAt w (e + e') (ML.pt (x + x')) := by
  rw [ML.add]
  exact he.add he'

theorem val_sum (h : genPt ξ ⤳ centre w) {n : ℕ} {a : Fin n → Ω} {r : Fin n → F} {e : Fin n → Li} {x : Fin n → V}
    (ha : ∀ k, ValAt ξ w (a k) (r k)) (he : ∀ k, M.ValAt w (e k) (ML.pt (x k))) :
    M.ValAt w (∑ k, a k • e k) (ML.pt (∑ k, r k • x k)) := by
  classical
  have : ∀ s : Finset (Fin n), M.ValAt w (∑ k ∈ s, a k • e k) (ML.pt (∑ k ∈ s, r k • x k)) := fun s => by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      rw [ML.pt_zero]
      exact M.valAt_zero h
    | insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk]
      exact val_add (val_smul (ha k) (he k)) ih
  exact this _

end Val

variable {L : Type} [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V] [Module (𝓞 L) V]
  [IsScalarTower (𝓞 L) L V]

theorem local_iff (hξ : IsCptGen ξ) (all : ∀ q : X, genPt ξ ⤳ q) (z : Sp (𝓞 L) ⟶ X) (M : LieModel G ξ Li)
    (ML : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) V) (Vl : Lat ξ Li) (𝔭 : PrimeSpectrum (𝓞 L)) {m : ℕ}
    {b : Fin m → Li} {g : Fin m → V} (hb : Vl.IsFrameAt b ⟨z 𝔭, all _⟩)
    (hg : ∀ k, M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) (b k) (ML.pt (g k))) (x : V) :
    x ∈ Submodule.span (𝓞 L) {x | ∃ s ∉ 𝔭.asIdeal, s • x ∈ Submodule.span (𝓞 L)
      {x' | ∃ e ∈ Vl ⟨z 𝔭, all _⟩, M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')}} ↔
    ∃ t ∉ 𝔭.asIdeal, t • x ∈ Submodule.span (𝓞 L) (Set.range g) := by
  refine span_sat_iff 𝔭.asIdeal (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_) x
  · rintro _ ⟨k, rfl⟩
    refine Submodule.subset_span ⟨b k, ?_, hg k⟩
    rw [hb.2]
    exact Submodule.subset_span ⟨k, rfl⟩
  · rintro x' ⟨e, he, hv⟩
    rw [hb.2] at he
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
    have hr := fun i => reg_value z hξ 𝔭 (all _) (c i).2
    choose r t n hr ht hn using hr
    have hv' : M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) (∑ i, (c i : Ω) • b i) (ML.pt (∑ i, r i • g i)) :=
      val_sum (all _) hr hg
    have hx : x' = ∑ i, r i • g i := ML.inj (LieModel.ValAt.unique hξ hv hv')
    rw [hx]
    refine sum_mem fun i _ => ?_
    refine ⟨t i, ht i, ?_⟩
    have e1 : t i • r i • g i = n i • g i := by
      rw [← algebraMap_smul L (t i), smul_smul, hn i, algebraMap_smul]
    rw [e1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem core (hξ : IsCptGen ξ) (all : ∀ q : X, genPt ξ ⤳ q) (z : Sp (𝓞 L) ⟶ X) (M : LieModel G ξ Li)
    (ML : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) V) (Vl : Lat ξ Li) {m : ℕ} (U : Submodule Ω Li)
    (s : Fin m → Li) (sL : Fin m → V) (hvb : Vl.IsVB m U)
    (hs : Vl.IsFrameAt s ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), all _⟩)
    (hval : ∀ k, M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) (s k) (ML.pt (sL k))) :
    ∃ (T : FinitePlace L → Matrix (Fin m) (Fin m) L) (T' : FinitePlace L → Matrix (Fin m) (Fin m) Ω)
      (b' : FinitePlace L → Fin m → Li),
      (∀ v, Vl.IsFrameAt (b' v) ⟨z (primeOf v), all _⟩) ∧ (∀ v k, b' v k = ∑ k', T' v k' k • s k') ∧
      (∀ v i j, ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (T' v i j) (T v i j)) ∧ (∀ v, (T v).det ≠ 0) ∧
      {v : FinitePlace L | ¬ ((∀ i j, v (T v i j) ≤ 1) ∧ v (T v).det = 1)}.Finite ∧
      ∀ x, x ∈ (⨅ 𝔭 : PrimeSpectrum (𝓞 L), Submodule.span (𝓞 L) {x | ∃ s ∉ 𝔭.asIdeal, s • x ∈ Submodule.span (𝓞 L)
          {x' | ∃ e ∈ Vl ⟨z 𝔭, all _⟩, M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')}}) ↔
        x ∈ Submodule.span L (Set.range sL) ∧ ∀ v : FinitePlace L, ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧
          t • x ∈ Submodule.span (𝓞 L) (Set.range fun k => ∑ j, T v j k • sL j) := by
  classical
  have hp : ∀ 𝔭 : PrimeSpectrum (𝓞 L), ∃ (W : X.Opens) (b : Fin m → Li), z 𝔭 ∈ W ∧
      ∀ q : Cpt ξ, q.1 ∈ W → Vl.IsFrameAt b q := fun 𝔭 => by
    obtain ⟨W, hW, b, -, hb⟩ := hvb ⟨z 𝔭, all _⟩ trivial
    exact ⟨W, b, hW, fun q hq => hb q trivial hq⟩
  choose W b hW hb using hp
  have hcen : ∀ 𝔭, centre (spMap (algebraMap (𝓞 L) L) ≫ z) ∈ W 𝔭 := fun 𝔭 =>
    (centre_specializes z 𝔭).mem_open (W 𝔭).isOpen (hW 𝔭)
  have hcmp := fun 𝔭 => frame_compare hξ (spMap (algebraMap (𝓞 L) L) ≫ z) (all _) Vl hs (hb 𝔭 _ (hcen 𝔭))
  choose T' T hT hTv hdet using hcmp
  obtain ⟨t, ht⟩ := (isCompact_univ (X := PrimeSpectrum (𝓞 L))).elim_finite_subcover
    (fun 𝔭 : PrimeSpectrum (𝓞 L) => z ⁻¹' ((W 𝔭 : X.Opens) : Set X))
    (fun 𝔭 => (W 𝔭).isOpen.preimage z.continuous)
    (fun 𝔭 _ => Set.mem_iUnion.2 ⟨𝔭, hW 𝔭⟩)
  have hcov : ∀ v : FinitePlace L, ∃ 𝔭 ∈ t, z (primeOf v) ∈ W 𝔭 := fun v => by
    have := ht (Set.mem_univ (primeOf v))
    simp only [Set.mem_iUnion] at this
    obtain ⟨𝔭, h𝔭, h⟩ := this
    exact ⟨𝔭, h𝔭, h⟩
  choose i hi hiv using hcov
  have hfr : ∀ v, Vl.IsFrameAt (b (i v)) ⟨z (primeOf v), all _⟩ := fun v => hb _ _ (hiv v)
  have hrel : ∀ v k, M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) (b (i v) k)
      (ML.pt (∑ j, T (i v) j k • sL j)) := fun v k => by
    rw [hT (i v) k]
    exact val_sum (all _) (fun j => hTv (i v) j k) hval
  refine ⟨fun v => T (i v), fun v => T' (i v), fun v => b (i v), hfr, fun v k => hT _ k, fun v a c => hTv _ a c,
    fun v => hdet _, ?_, fun x => ?_⟩
  · refine (Set.Finite.biUnion t.finite_toSet fun 𝔭 _ => bad_finite (T 𝔭) (hdet 𝔭)).subset fun v hv => ?_
    exact Set.mem_biUnion (hi v) hv
  · obtain ⟨o₀, h0, h1⟩ := exists_bot_point z
    have hs' : Vl.IsFrameAt s ⟨z o₀, all _⟩ := by
      have e : (⟨z o₀, all _⟩ : Cpt ξ) = ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), all _⟩ := Subtype.ext h1
      rw [e]
      exact hs
    have hbot := local_iff hξ all z M ML Vl o₀ hs' hval x
    have hloc := fun v => local_iff hξ all z M ML Vl (primeOf v) (hfr v) (hrel v) x
    rw [Submodule.mem_iInf]
    constructor
    · intro h
      refine ⟨?_, fun v => ?_⟩
      · obtain ⟨c, hc, hx⟩ := hbot.1 (h o₀)
        refine (exists_smul_mem_iff sL x).1 ⟨c, fun e => hc ?_, hx⟩
        rw [h0, e]
        exact Ideal.zero_mem _
      · obtain ⟨c, hc, hx⟩ := (hloc v).1 (h (primeOf v))
        exact ⟨c, hc, hx⟩
    · rintro ⟨hx, hv⟩ 𝔭
      rcases prime_cases 𝔭 with h𝔭 | ⟨v, rfl⟩
      · obtain rfl : 𝔭 = o₀ := PrimeSpectrum.ext (h𝔭.trans h0.symm)
        obtain ⟨c, hc, hcx⟩ := (exists_smul_mem_iff sL x).2 hx
        refine hbot.2 ⟨c, fun e => hc ?_, hcx⟩
        rw [h0] at e
        exact e
      · obtain ⟨c, hc, hcx⟩ := hv v
        exact (hloc v).2 ⟨c, hc, hcx⟩

end Core

theorem fin_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (Vl : Lat 𝔐.ξ 𝔐.Li) (m : ℕ) (U : Submodule Ω 𝔐.Li) (s : Fin m → 𝔐.Li) (sL : Fin m → V), Vl.IsVB m U → Vl.IsFrameAt s ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩ → IsValues 𝔐 z P MV s sL → LinearIndependent L sL → ∃ (T : FinitePlace L → Matrix (Fin m) (Fin m) L) (T' : FinitePlace L → Matrix (Fin m) (Fin m) Ω) (b' : FinitePlace L → Fin m → 𝔐.Li), (∀ v, Vl.IsFrameAt (b' v) ⟨z (primeOf v), 𝔐.all _⟩) ∧ (∀ v k, b' v k = ∑ k', T' v k' k • s k') ∧ (∀ v i j, ValAt 𝔐.ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (T' v i j) (T v i j)) ∧ (∀ v, (T v).det ≠ 0) ∧ {v : FinitePlace L | ¬ ((∀ i j, v (T v i j) ≤ 1) ∧ v (T v).det = 1)}.Finite ∧ ∀ x, x ∈ 𝔐.FibLat Vl z P MV ↔ x ∈ Submodule.span L (Set.range sL) ∧ ∀ v : FinitePlace L, ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧ t • x ∈ Submodule.span (𝓞 L) (Set.range fun k => ∑ j, T v j k • sL j) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 L _ _ z P V _ _ _ _ MV Vl m U s sL hvb hs hval _
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  obtain ⟨ML, hML⟩ := (LieMove.main L 𝔐.X (spMap (algebraMap (𝓞 L) L) ≫ z) 𝔐.t.G P.tK.G P.m.φ V P.m.cart).2 MV
  have hval' : ∀ k, 𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) (s k) (ML.pt (sL k)) := fun k => by
    obtain ⟨v, hv, h⟩ := hval k
    have e : v = ML.pt (sL k) := Over.OverMorphism.ext (h.symm.trans (hML _))
    rwa [← e]
  obtain ⟨T, T', b', h1, h2, h3, h4, h5, h6⟩ := core hξ 𝔐.all z 𝔐.M ML Vl U s sL hvb hs hval'
  refine ⟨T, T', b', h1, h2, h3, h4, h5, fun x => ?_⟩
  rw [← h6 x]
  have hset : ∀ 𝔭 : PrimeSpectrum (𝓞 L), {x' : V | ∃ e ∈ Vl ⟨z 𝔭, 𝔐.all _⟩,
      ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ 𝔐.t.G,
      𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ (MV.pt x').left ≫ P.m.φ = v.left} =
      {x' | ∃ e ∈ Vl ⟨z 𝔭, 𝔐.all _⟩, 𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt x')} := fun 𝔭 => by
    ext x'
    constructor
    · rintro ⟨e, he, v, hv, h⟩
      have e' : v = ML.pt x' := Over.OverMorphism.ext (h.symm.trans (hML _))
      exact ⟨e, he, e' ▸ hv⟩
    · rintro ⟨e, he, hv⟩
      exact ⟨e, he, _, hv, hML _⟩
  simp only [HodgeCpt.FibLat, hset]

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.FinFrame
