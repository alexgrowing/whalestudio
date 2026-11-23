import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalAut
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalRoots
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.LevelLift

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem ga_restrict {Ω : Type*} [Monoid Ω] {m M : ℕ} [NeZero m] [NeZero M] (hm : m ∣ M)
    (f : Ω → Ω) (a : (ZMod M)ˣ) (h : ∀ ζ : Ω, ζ ^ M = 1 → f ζ = ζ ^ (a : ZMod M).val)
    (ζ : Ω) (hζ : ζ ^ m = 1) :
    f ζ = ζ ^ ((ZMod.unitsMap hm a : (ZMod m)ˣ) : ZMod m).val := by
  have hM : ζ ^ M = 1 := by
    obtain ⟨c, rfl⟩ := hm
    rw [pow_mul, hζ, one_pow]
  rw [h ζ hM, ZMod.unitsMap_val, ← ZMod.natCast_val, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ]

private theorem ga_red {F : Type*} [Field F] [CharZero F] (g : Gal(AlgebraicClosure F/F)) (n : ℕ)
    (w : (ZMod (l ^ n))ˣ)
    (h : ∀ ζ : AlgebraicClosure F, ζ ^ l ^ n = 1 → g ζ = ζ ^ (w : ZMod (l ^ n)).val) :
    redPow l n (eps l F g) = w := by
  have hen : ∀ i, HasEnoughRootsOfUnity (AlgebraicClosure F) (l ^ i) := fun i => by
    have : NeZero (l ^ i) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have : NeZero ((l ^ i : ℕ) : AlgebraicClosure F) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩
    infer_instance
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure F) (l ^ n)
  have h1 : g ζ = ζ ^ (PadicInt.toZModPow n ((eps l F g : ℤ_[l]ˣ) : ℤ_[l])).val :=
    cyclotomicCharacter.spec l
      (MulSemiringAction.toRingAut Gal(AlgebraicClosure F/F) (AlgebraicClosure F) g) ζ
      hζ.pow_eq_one
  rw [h ζ hζ.pow_eq_one] at h1
  have hfin : IsOfFinOrder ζ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨l ^ n, Nat.pos_of_neZero _, hζ.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf, ← ZMod.natCast_eq_natCast_iff,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h1
  exact Units.ext h1.symm

private theorem ga_embed {K : Type*} [Field K] [NumberField K] (E : IntermediateField ℚ K) :
    ∃ φ : K →+* AlgebraicClosure E, ∀ x : E, φ (x : K) = algebraMap E (AlgebraicClosure E) x := by
  have : Algebra.IsAlgebraic E K := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  let φ : K →ₐ[E] AlgebraicClosure E := IsAlgClosed.lift
  exact ⟨φ.toRingHom, fun x => φ.commutes x⟩

variable {N : ℕ} [NeZero N] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]

theorem galImage_le_levelGroup (E : IntermediateField ℚ K) :
    galImage l E ≤ levelGroup l N (fieldSubgroup N K E) := by
  rintro _ ⟨g, rfl⟩
  obtain ⟨φ, hφ⟩ := ga_embed E
  obtain ⟨a, ha⟩ := exists_class_of_aut (N := N) g.toRingEquiv
  have : NeZero (l ^ N.factorization l) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine mem_levelGroup.2 ⟨a, ?_, ?_⟩
  · refine ⟨(IsCyclotomicExtension.Rat.galEquivZMod N K).symm a, ?_,
      MulEquiv.apply_symm_apply _ _⟩
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
    apply φ.injective
    rw [← aut_comp_embedding φ g.toRingEquiv.toRingHom a ha x]
    have := hφ ⟨x, hx⟩
    change φ x = _ at this
    rw [this]
    exact g.commutes _
  · exact (ga_red g _ _ (ga_restrict (Nat.ordProj_dvd N l) g a ha)).symm

theorem levelGroup_le_galImage (E : IntermediateField ℚ K) :
    levelGroup l N (fieldSubgroup N K E) ≤ galImage l E := by
  intro u hu
  obtain ⟨h, ⟨σ, hσ, rfl⟩, hu⟩ := mem_levelGroup.1 hu
  obtain ⟨φ, hφ⟩ := ga_embed E
  refine mem_of_isClosed isClosed_galImage fun b => ?_
  obtain ⟨a, ha1, ha2⟩ := exists_lift_level _ u hu b
  have : NeZero (l ^ b) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : NeZero (N * l ^ b) := ⟨mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure E) := Algebra.IsAlgebraic.trans ℚ E _
  obtain ⟨g, hg⟩ := exists_aut_pow_roots (AlgebraicClosure E) a
  have hN := ga_restrict (Nat.dvd_mul_right N (l ^ b)) g a hg
  have hb := ga_restrict (Nat.dvd_mul_left (l ^ b) N) g a hg
  rw [ha1] at hN
  rw [ha2] at hb
  have hfix : ∀ x : E, g.toRingEquiv (algebraMap E (AlgebraicClosure E) x) =
      algebraMap E (AlgebraicClosure E) x := fun x => by
    have h1 := aut_comp_embedding φ g.toRingEquiv.toRingHom _ hN (x : K)
    have h2 : (IsCyclotomicExtension.Rat.galEquivZMod N K).symm
        ((IsCyclotomicExtension.Rat.galEquivZMod N K).toMonoidHom σ) = σ :=
      MulEquiv.symm_apply_apply _ _
    rw [h2, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x x.2, hφ] at h1
    exact h1
  let g' : Gal(AlgebraicClosure E/E) := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hfix
  exact ⟨eps l E g', ⟨g', rfl⟩, ga_red g' b _ hb⟩

theorem galImage_eq_levelGroup (E : IntermediateField ℚ K) :
    galImage l E = levelGroup l N (fieldSubgroup N K E) :=
  le_antisymm (galImage_le_levelGroup E) (levelGroup_le_galImage E)

end KStar.TotallyRealRoots
