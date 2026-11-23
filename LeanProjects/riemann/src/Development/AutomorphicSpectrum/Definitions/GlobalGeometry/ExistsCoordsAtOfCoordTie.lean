import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CoordModel

open AlgebraicGeometry CategoryTheory

variable (A : Type) [CommRing A] (Ω : Type) [Field Ω] [Algebra A Ω]

def gen : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A Ω))

def pr (p : Spec (CommRingCat.of A)) : PrimeSpectrum A := p

def toSt (p : Spec (CommRingCat.of A)) : A →+* (Spec (CommRingCat.of A)).presheaf.stalk p :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Spec (CommRingCat.of A)).presheaf.germ ⊤ p trivial).hom

theorem isLoc (p : Spec (CommRingCat.of A)) :
    letI := (toSt A p).toAlgebra
    IsLocalization.AtPrime ((Spec (CommRingCat.of A)).presheaf.stalk p) (pr A p).asIdeal :=
  StructureSheaf.IsLocalization.to_stalk A (pr A p)

set_option backward.isDefEq.respectTransparency false in
theorem genMap_toSt (p : Cpt (gen A Ω)) (a : A) :
    genMap (gen A Ω) p (toSt A p.1 a) = algebraMap A Ω a := by
  have h1 := (Spec (CommRingCat.of A)).presheaf.germ_stalkSpecializes (U := ⊤) (y := p.1) trivial p.2
  have h2 := Scheme.germ_stalkClosedPointTo_Spec (R := CommRingCat.of A) (S := CommRingCat.of Ω)
    (CommRingCat.ofHom (algebraMap A Ω))
  have h3 : ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Spec (CommRingCat.of A)).presheaf.germ ⊤ p.1 trivial) ≫
      ((Spec (CommRingCat.of A)).presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo (gen A Ω)) =
      CommRingCat.ofHom (algebraMap A Ω) := by
    rw [Category.assoc, ← Category.assoc ((Spec (CommRingCat.of A)).presheaf.germ ⊤ p.1 trivial), h1]
    erw [h2]
    simp
  exact congrArg (fun f => f.hom a) h3

theorem mem_regAt (p : Cpt (gen A Ω)) (a : Ω) :
    a ∈ regAt (gen A Ω) p ↔ ∃ r s : A, s ∉ (pr A p.1).asIdeal ∧ a * algebraMap A Ω s = algebraMap A Ω r := by
  letI := (toSt A p.1).toAlgebra
  haveI := isLoc A p.1
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj ((pr A p.1).asIdeal).primeCompl t
    refine ⟨r, s, s.2, ?_⟩
    rw [← genMap_toSt A Ω p, ← genMap_toSt A Ω p, ← map_mul]
    exact congrArg _ h
  · rintro ⟨r, s, hs, h⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units ((Spec (CommRingCat.of A)).presheaf.stalk p.1)
      (⟨s, hs⟩ : ((pr A p.1).asIdeal).primeCompl)
    refine ⟨toSt A p.1 r * ↑u⁻¹, ?_⟩
    have e : genMap (gen A Ω) p u = algebraMap A Ω s := by
      rw [hu]; exact genMap_toSt A Ω p s
    have e2 : genMap (gen A Ω) p u * genMap (gen A Ω) p ↑u⁻¹ = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [map_mul, genMap_toSt, ← h, ← e, mul_assoc, e2, mul_one]

variable [IsDomain A] [IsFractionRing A Ω]

theorem genPt_asIdeal : (pr A (genPt (gen A Ω))).asIdeal = ⊥ := by
  ext a
  change algebraMap A Ω a ∈ IsLocalRing.maximalIdeal Ω ↔ _
  simp

theorem spec_all (q : Spec (CommRingCat.of A)) : genPt (gen A Ω) ⤳ q := by
  refine (PrimeSpectrum.le_iff_specializes (R := A) _ _).1 ?_
  change (pr A (genPt (gen A Ω))).asIdeal ≤ (pr A q).asIdeal
  rw [genPt_asIdeal]; exact bot_le

theorem genMap_inj (p : Cpt (gen A Ω)) : Function.Injective (genMap (gen A Ω) p) := by
  letI := (toSt A p.1).toAlgebra
  haveI := isLoc A p.1
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj ((pr A p.1).asIdeal).primeCompl t
  have h' := congrArg (genMap (gen A Ω) p) h
  rw [map_mul, ht, zero_mul] at h'
  have : algebraMap A Ω r = 0 := by rw [← genMap_toSt A Ω p]; exact h'.symm
  have hr : r = 0 := by simpa using this
  subst hr
  simp only [map_zero] at h
  exact (IsLocalization.map_units _ s).mul_left_eq_zero.1 h

theorem isCptGen : IsCptGen (gen A Ω) := by
  refine ⟨?_, genMap_inj A Ω⟩
  have e : genMap (gen A Ω) ⟨genPt (gen A Ω), specializes_rfl⟩ = (Scheme.stalkClosedPointTo (gen A Ω)).hom := by
    unfold genMap
    erw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
    rfl
  have hb : Function.Bijective (genMap (gen A Ω) ⟨genPt (gen A Ω), specializes_rfl⟩) := by
    refine ⟨genMap_inj A Ω _, fun a => ?_⟩
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := A) a
    refine (mem_regAt A Ω ⟨genPt (gen A Ω), specializes_rfl⟩ _).2 ⟨r, s, ?_, ?_⟩
    · change s ∉ (pr A (genPt (gen A Ω))).asIdeal
      rw [genPt_asIdeal]; simpa using nonZeroDivisors.ne_zero hs
    · have : algebraMap A Ω s ≠ 0 := by simpa using nonZeroDivisors.ne_zero hs
      field_simp
  rw [e] at hb
  exact hb

omit [IsDomain A] [IsFractionRing A Ω] in
theorem inv_mem {κ : Type} {x : κ → A} (hx : Ideal.span (Set.range x) = ⊤) (c : κ) (S : Subring Ω)
    (hA : ∀ a, algebraMap A Ω a ∈ S) (hS : ∀ j, algebraMap A Ω (x j) / algebraMap A Ω (x c) ∈ S) :
    (algebraMap A Ω (x c))⁻¹ ∈ S := by
  have key : ∀ a ∈ Ideal.span (Set.range x), algebraMap A Ω a / algebraMap A Ω (x c) ∈ S := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a h => obtain ⟨j, rfl⟩ := h; exact hS j
    | zero => simpa using S.zero_mem
    | add a b _ _ ha hb => rw [map_add, add_div]; exact S.add_mem ha hb
    | smul r a _ ha => rw [smul_eq_mul, map_mul, mul_div_assoc]; exact S.mul_mem (hA r) ha
  simpa using key 1 (hx ▸ Submodule.mem_top)

omit [IsDomain A] [IsFractionRing A Ω] in
theorem algebraMap_mem_regAt (p : Cpt (gen A Ω)) (a : A) : algebraMap A Ω a ∈ regAt (gen A Ω) p :=
  ⟨_, genMap_toSt A Ω p a⟩

theorem inChart_iff {κ : Type} {x : κ → A} (hx : Ideal.span (Set.range x) = ⊤) (c : κ) (p : Cpt (gen A Ω)) :
    InChart (gen A Ω) (fun j => algebraMap A Ω (x j)) c p ↔ x c ∉ (pr A p.1).asIdeal := by
  constructor
  · rintro ⟨h0, h⟩ hc
    obtain ⟨r, s, hs, e⟩ := (mem_regAt A Ω p _).1 (inv_mem A Ω hx c _ (algebraMap_mem_regAt A Ω p) h)
    have : s = x c * r := by
      apply IsFractionRing.injective A Ω
      rw [map_mul, ← e]; field_simp
    exact hs (this ▸ Ideal.mul_mem_right _ _ hc)
  · intro hc
    have h0 : algebraMap A Ω (x c) ≠ 0 := by
      intro h
      have : x c = 0 := by simpa using h
      exact hc (this ▸ Ideal.zero_mem _)
    exact ⟨h0, fun j => (mem_regAt A Ω p _).2 ⟨x j, x c, hc, by field_simp⟩⟩

theorem coordTie (o : Type) [CommRing o] [Algebra o A] [Algebra o Ω] [IsScalarTower o A Ω]
    {κ : Type} {x : κ → A} (hx : Ideal.span (Set.range x) = ⊤)
    (hA : ∀ c, x c ≠ 0 → ∀ a : A, algebraMap A Ω a ∈
      Algebra.adjoin o (Set.range fun j => algebraMap A Ω (x j) / algebraMap A Ω (x c))) :
    CoordTie o (gen A Ω) (fun j => algebraMap A Ω (x j)) where
  gen := isCptGen A Ω
  cover p := by
    by_contra h
    push Not at h
    refine (pr A p.1).isPrime.ne_top (top_le_iff.1 (hx ▸ Ideal.span_le.2 ?_))
    rintro _ ⟨c, rfl⟩
    by_contra hc
    exact h c ((inChart_iff A Ω hx c p).2 hc)
  affine c _ := by
    refine ⟨_, IsAffineOpen.Spec_basicOpen (R := CommRingCat.of A) (x c), fun q => ?_⟩
    exact ⟨fun hq => ⟨spec_all A Ω q, (inChart_iff A Ω hx c _).2 hq⟩,
      fun ⟨h, hq⟩ => (inChart_iff A Ω hx c ⟨q, h⟩).1 hq⟩
  ring c hc a := by
    have hc' : x c ≠ 0 := fun h => hc (by simp [h])
    constructor
    · intro ha p hp
      induction ha using Algebra.adjoin_induction with
      | mem a h => obtain ⟨j, rfl⟩ := h; exact hp.2 j
      | algebraMap r => rw [IsScalarTower.algebraMap_apply o A Ω]; exact algebraMap_mem_regAt A Ω p _
      | add a b _ _ ha hb => exact Subring.add_mem _ ha hb
      | mul a b _ _ ha hb => exact Subring.mul_mem _ ha hb
    · intro h
      let I : Ideal A :=
        { carrier := {s | ∃ r, a * algebraMap A Ω s = algebraMap A Ω r}
          add_mem' := by
            rintro s t ⟨r, hr⟩ ⟨r', hr'⟩
            exact ⟨r + r', by rw [map_add, map_add, mul_add, hr, hr']⟩
          zero_mem' := ⟨0, by simp⟩
          smul_mem' := by
            rintro t s ⟨r, hr⟩
            exact ⟨t * r, by rw [smul_eq_mul, map_mul, map_mul, ← hr]; ring⟩ }
      have hrad : x c ∈ I.radical := by
        rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
        rintro J ⟨hIJ, hJ⟩
        by_contra hxc
        let q : Spec (CommRingCat.of A) := (⟨J, hJ⟩ : PrimeSpectrum A)
        obtain ⟨r, s, hs, e⟩ := (mem_regAt A Ω ⟨q, spec_all A Ω q⟩ a).1
          (h _ ((inChart_iff A Ω hx c _).2 hxc))
        exact hs (hIJ ⟨r, e⟩)
      obtain ⟨n, r, e⟩ := hrad
      have hi := inv_mem A Ω hx c (Algebra.adjoin o
        (Set.range fun j => algebraMap A Ω (x j) / algebraMap A Ω (x c))).toSubring (hA c hc')
        (fun j => Algebra.subset_adjoin ⟨j, rfl⟩)
      have : a = algebraMap A Ω r * (algebraMap A Ω (x c))⁻¹ ^ n := by
        rw [← e, map_pow, mul_assoc, ← mul_pow, mul_inv_cancel₀ hc, one_pow, mul_one]
      rw [this]
      exact Subalgebra.mul_mem _ (hA c hc' r) (Subalgebra.pow_mem _ hi n)

theorem coordTie_two_three : CoordTie ℤ (gen ℤ ℚ) (fun j => algebraMap ℤ ℚ (![2, 3] j)) := by
  refine coordTie ℤ ℚ ℤ ?_ fun c _ a => Subalgebra.algebraMap_mem _ a
  rw [Ideal.eq_top_iff_one]
  have h := Ideal.sub_mem (Ideal.span (Set.range (![2, 3] : Fin 2 → ℤ)))
    (Ideal.subset_span ⟨1, rfl⟩) (Ideal.subset_span ⟨0, rfl⟩)
  simpa using h

theorem not_coordTie_rat : ¬ CoordTie ℤ (gen ℚ ℚ) (fun _ : Unit => (1 : ℚ)) := by
  intro h
  have h2 := (h.ring () one_ne_zero (1 / 2)).2 fun p _ => algebraMap_mem_regAt ℚ ℚ p (1 / 2)
  have hle : Algebra.adjoin ℤ (Set.range fun _ : Unit => (1 : ℚ) / 1) ≤ ⊥ := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨_, rfl⟩
    simpa using Subalgebra.one_mem _
  obtain ⟨n, hn⟩ := Algebra.mem_bot.1 (hle h2)
  have : (2 * n : ℤ) = 1 := by
    have h' : (n : ℚ) = 1 / 2 := by simpa using hn
    have : ((2 * n : ℤ) : ℚ) = 1 := by push_cast; rw [h']; norm_num
    exact_mod_cast this
  omega

theorem inFibre_iff (p : ℕ) (q : Cpt (gen A Ω)) : InFibre (gen A Ω) p q ↔ (p : A) ∈ (pr A q.1).asIdeal := by
  have hp : (p : Ω) = algebraMap A Ω p := by simp
  unfold InFibre unitAt
  rw [hp, ← not_iff_not, not_not]
  constructor
  · rintro ⟨h0, -, h⟩ hc
    obtain ⟨r, s, hs, e⟩ := (mem_regAt A Ω q _).1 h
    have : s = p * r := by
      apply IsFractionRing.injective A Ω
      rw [map_mul, ← e]; field_simp
    exact hs (this ▸ Ideal.mul_mem_right _ _ hc)
  · intro hc
    have h0 : algebraMap A Ω p ≠ 0 := by
      intro h
      have : (p : A) = 0 := IsFractionRing.injective A Ω (by rw [h, map_zero])
      exact hc (this ▸ Ideal.zero_mem _)
    exact ⟨h0, algebraMap_mem_regAt A Ω q _, (mem_regAt A Ω q _).2 ⟨1, p, hc, by rw [map_one]; field_simp⟩⟩

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R] [IsLocalRing R]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of R) ⟶ X}

theorem valAt_unique (hξ : IsCptGen ξ) {a : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨hz, s, rfl, rfl⟩ := h
  obtain ⟨_, s', e, rfl⟩ := h'
  rw [hξ.inj ⟨centre z, hz⟩ e]

theorem valAt_mul {a b : Ω} {r s : R} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  obtain ⟨_, t', rfl, rfl⟩ := h'
  exact ⟨hz, t * t', map_mul _ _ _, map_mul _ _ _⟩

theorem valAt_inv {a : Ω} {r : Rˣ} (h : ValAt ξ z a r) : a ≠ 0 ∧ ValAt ξ z a⁻¹ ↑r⁻¹ := by
  obtain ⟨hz, t, rfl, e⟩ := h
  have ht : IsUnit t := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit t (by have := r.isUnit; rw [← e] at this; exact this)
  obtain ⟨u, rfl⟩ := ht
  refine ⟨(u.isUnit.map (genMap ξ ⟨centre z, hz⟩)).ne_zero, hz, ↑u⁻¹, map_units_inv _ u, ?_⟩
  refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
  rw [← e]
  exact (map_mul _ _ _).symm.trans ((congrArg _ u.mul_inv).trans (map_one _))

theorem exists_coordsAt {K : Type} {ι : K → Type} (y : (Σ k, ι k) → Ω) (hz : genPt ξ ⤳ centre z)
    (h : ∀ k, ∃ c, InChart ξ (fun i => y ⟨k, i⟩) c ⟨centre z, hz⟩) (hξ : IsCptGen ξ) :
    ∃ w, CoordsAt ξ y z w := by
  choose c hc using h
  have hv : ∀ j : Σ k, ι k, ∃ r, ValAt ξ z (y j / y ⟨j.1, c j.1⟩) r := by
    rintro ⟨k, i⟩
    obtain ⟨s, hs⟩ := (hc k).2 i
    exact ⟨_, hz, s, hs, rfl⟩
  choose w hw using hv
  refine ⟨w, fun k => ⟨c k, ?_⟩, fun k d hd => ?_⟩
  · have h1 : ValAt ξ z 1 1 := ⟨hz, 1, map_one _, map_one _⟩
    have h2 := hw ⟨k, c k⟩
    rw [div_self (hc k).1] at h2
    rw [valAt_unique hξ h2 h1]; exact isUnit_one
  · obtain ⟨u, hu⟩ := hd
    have h1 := hw ⟨k, d⟩
    rw [← hu] at h1
    obtain ⟨h0, h2⟩ := valAt_inv h1
    have hd0 : y ⟨k, d⟩ ≠ 0 := fun e => h0 (by simp [e])
    refine ⟨hd0, fun i => ⟨w ⟨k, i⟩ * ↑u⁻¹, ?_, by rw [← hu]; simp⟩⟩
    have h3 := valAt_mul (hw ⟨k, i⟩) h2
    have hc0 : y ⟨k, c k⟩ ≠ 0 := (hc k).1
    convert h3 using 1
    field_simp

theorem coordsAt_unique {K : Type} {ι : K → Type} {y : (Σ k, ι k) → Ω} (hξ : IsCptGen ξ) {w w' : (Σ k, ι k) → R}
    (h : CoordsAt ξ y z w) (h' : CoordsAt ξ y z w') (k : K) : ∃ u : Rˣ, ∀ i, w' ⟨k, i⟩ = u * w ⟨k, i⟩ := by
  obtain ⟨c, hc⟩ := h.1 k
  obtain ⟨d, hd⟩ := h'.1 k
  obtain ⟨hc0, hv⟩ := h.2 k c hc
  obtain ⟨hd0, hv'⟩ := h'.2 k d hd
  obtain ⟨r, hr, -⟩ := hv d
  obtain ⟨r', hr', e'⟩ := hv' c
  have h1 : ValAt ξ z 1 1 := ⟨hr.1, 1, map_one _, map_one _⟩
  have h2 := valAt_mul hr hr'
  rw [show y ⟨k, d⟩ / y ⟨k, c⟩ * (y ⟨k, c⟩ / y ⟨k, d⟩) = 1 by field_simp] at h2
  have hu : IsUnit (w' ⟨k, c⟩) := by
    rw [e']
    exact (IsUnit.of_mul_eq_one_right r (valAt_unique hξ h2 h1)).mul hd
  obtain ⟨-, hv''⟩ := h'.2 k c hu
  refine ⟨hu.unit * hc.unit⁻¹, fun i => ?_⟩
  obtain ⟨s, hs, es⟩ := hv i
  obtain ⟨s', hs', es'⟩ := hv'' i
  rw [es, es', valAt_unique hξ hs' hs, Units.val_mul, IsUnit.unit_spec, mul_assoc, mul_left_comm _ s,
    IsUnit.val_inv_mul, mul_one, mul_comm]

theorem not_coordTie_zero (o : Type) [CommRing o] [Algebra o Ω] {κ : Type} : ¬ CoordTie o ξ (0 : κ → Ω) := by
  intro h
  obtain ⟨c, hc⟩ := h.cover ⟨genPt ξ, specializes_rfl⟩
  exact hc.1 rfl

theorem exists_coordsAt_of_coordTie {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (h : CoordTie o ξ x) (hz : genPt ξ ⤳ centre z) :
    ∃ w, CoordsAt ξ (K := Unit) (ι := fun _ => κ) (fun j => x j.2) z w :=
  exists_coordsAt _ hz (fun _ => h.cover _) h.gen

end General

end GlobalTheory.CompanionTheory.Ar.CoordModel
