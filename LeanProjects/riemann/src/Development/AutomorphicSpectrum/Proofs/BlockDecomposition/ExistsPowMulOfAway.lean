import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TrivOfSectionOfLocallyTriv

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.TrivLoc

theorem eq_zero_of_pow_mul {R : Type} [CommRing R] (s : Set R) (hs : Ideal.span s = ⊤) (b : R)
    (h : ∀ a ∈ s, ∃ n : ℕ, a ^ n * b = 0) : b = 0 := by
  let K : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R b)
  have hK : K.radical = ⊤ := by
    rw [eq_top_iff, ← hs, Ideal.span_le]
    intro a ha
    obtain ⟨n, hn⟩ := h a ha
    exact ⟨n, by simpa [K, LinearMap.mem_ker] using hn⟩
  have h1 : (1 : R) ∈ K := by
    rw [Ideal.radical_eq_top.1 hK]; trivial
  simpa [K, LinearMap.mem_ker] using h1

theorem exists_pow_mul_of_away {R : Type} [CommRing R] (a x : R)
    (h : algebraMap R (Localization.Away a) x = 0) : ∃ n : ℕ, a ^ n * x = 0 := by
  obtain ⟨⟨_, n, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers a) (Localization.Away a) x).1 h
  exact ⟨n, hm⟩

theorem isUnit_away {R : Type} [CommRing R] (a : R) : IsUnit (algebraMap R (Localization.Away a) a) :=
  IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a

theorem exists_ideal_of_local {R : Type} [CommRing R] (Q : ∀ (R' : Type) [CommRing R'], (R →+* R') → Prop)
    (stab : ∀ (R' R'' : Type) [CommRing R'] [CommRing R''] (g : R →+* R') (h : R' →+* R''), Q R' g → Q R'' (h.comp g))
    (loc : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (s : Set R'), Ideal.span s = ⊤ →
      (∀ a ∈ s, Q (Localization.Away a) ((algebraMap R' _).comp g)) → Q R' g)
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤) (I : R → Ideal R)
    (hI : ∀ f ∈ s, ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g f) → (Q R' g ↔ I f ≤ RingHom.ker g)) :
    ∃ J : Ideal R, ∀ (R' : Type) [CommRing R'] (g : R →+* R'), Q R' g ↔ J ≤ RingHom.ker g := by
  classical
  let B : R → Type := fun f => Localization.Away (Ideal.Quotient.mk (I f) f)
  let b : ∀ f, R →+* B f := fun f => (algebraMap (R ⧸ I f) (B f)).comp (Ideal.Quotient.mk (I f))
  have bu : ∀ f, IsUnit (b f f) := fun f => isUnit_away _
  have bI : ∀ f, I f ≤ RingHom.ker (b f) := fun f x hx => by
    simp [b, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem.2 hx]
  have bQ : ∀ f ∈ s, Q (B f) (b f) := fun f hf => (hI f hf _ _ (bu f)).2 (bI f)

  have fac : ∀ f ∈ s, ∀ (R' : Type) [CommRing R'] (g : R →+* R'), Q R' g → IsUnit (g f) →
      ∃ h : B f →+* R', h.comp (b f) = g := fun f hf R' _ g hq hu => by
    have hle := (hI f hf R' g hu).1 hq
    let g₁ : R ⧸ I f →+* R' := Ideal.Quotient.lift (I f) g fun x hx => hle hx
    have hu' : IsUnit (g₁ (Ideal.Quotient.mk (I f) f)) := by
      rw [show g₁ (Ideal.Quotient.mk (I f) f) = g f from Ideal.Quotient.lift_mk _ _ _]; exact hu
    refine ⟨IsLocalization.Away.lift (S := B f) (Ideal.Quotient.mk (I f) f) hu', ?_⟩
    ext x
    change IsLocalization.Away.lift (S := B f) (Ideal.Quotient.mk (I f) f) hu' (algebraMap (R ⧸ I f) (B f) (Ideal.Quotient.mk (I f) x)) = g x
    rw [IsLocalization.Away.lift_eq]
    exact Ideal.Quotient.lift_mk _ _ _

  refine ⟨⨅ f ∈ s, RingHom.ker (b f), fun R' _ g => ⟨fun hq a ha => ?_, fun hJ => ?_⟩⟩
  · have ha' : ∀ f ∈ s, b f a = 0 := fun f hf => by
      have := (Submodule.mem_iInf _).1 ha f
      exact (Submodule.mem_iInf _).1 this hf
    refine eq_zero_of_pow_mul (g '' (s : Set R)) ?_ (g a) ?_
    · rw [← Ideal.map_span, hs, Ideal.map_top]
    · rintro _ ⟨f, hf, rfl⟩
      let L := Localization.Away (g f)
      obtain ⟨h, hh⟩ := fac f hf L ((algebraMap R' L).comp g) (stab _ _ _ _ hq)
        (isUnit_away _)
      apply exists_pow_mul_of_away
      have := congrArg (fun q => q a) hh
      simpa [ha' f hf] using this.symm
  · set J : Ideal R := ⨅ f ∈ s, RingHom.ker (b f) with hJdef
    suffices H : Q (R ⧸ J) (Ideal.Quotient.mk J) by
      have := stab _ _ _ (Ideal.Quotient.lift J g fun x hx => hJ hx) H
      have e : (Ideal.Quotient.lift J g fun x hx => hJ hx).comp (Ideal.Quotient.mk J) = g := by
        exact RingHom.ext fun x => Ideal.Quotient.lift_mk J g fun x hx => hJ hx
      rwa [e] at this
    refine loc _ _ (Ideal.Quotient.mk J '' (s : Set R)) (by rw [← Ideal.map_span, hs]; exact Ideal.map_top _) ?_
    rintro _ ⟨f, hf, rfl⟩
    refine (hI f hf _ ((algebraMap (R ⧸ J) (Localization.Away (Ideal.Quotient.mk J f))).comp (Ideal.Quotient.mk J))
      (isUnit_away (Ideal.Quotient.mk J f))).2 fun x hx => ?_
    have key : ∀ f' ∈ s, ∃ n : ℕ, b f' f ^ n * b f' x = 0 := fun f' hf' => by
      let L := Localization.Away (b f' f)
      have h1 := (hI f hf L ((algebraMap (B f') L).comp (b f')) (isUnit_away _)).1
        (stab _ _ _ _ (bQ f' hf'))
      exact exists_pow_mul_of_away _ _ (h1 hx)
    choose! n hn using key
    have hmem : Ideal.Quotient.mk J f ^ (s.sup n) * Ideal.Quotient.mk J x = 0 := by
      rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      refine (Submodule.mem_iInf _).2 fun f' => (Submodule.mem_iInf _).2 fun hf' => ?_
      have hle : n f' ≤ s.sup n := Finset.le_sup hf'
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      rw [RingHom.mem_ker, map_mul, map_pow, hd, pow_add, mul_comm (b f' f ^ n f'), _root_.mul_assoc, hn f' hf', mul_zero]
    have hu : IsUnit (algebraMap (R ⧸ J) (Localization.Away (Ideal.Quotient.mk J f)) (Ideal.Quotient.mk J f ^ (s.sup n))) := by
      rw [map_pow]; exact (isUnit_away _).pow _
    have := congrArg (algebraMap (R ⧸ J) (Localization.Away (Ideal.Quotient.mk J f))) hmem
    rw [map_mul, map_zero] at this
    exact (hu.mul_right_eq_zero).1 this

end GlobalTheory.CompanionTheory.TrivLoc

namespace GlobalTheory.CompanionTheory.TrivLoc

variable {S : Scheme.{0}} {A Y : Over S}

def IsTrivAt (N : LB (A ⊗ Y).left) {T : Over S} (y : T ⟶ Y) : Prop :=
  Triv (ev N (fst A T) (snd A T ≫ y))

theorem IsTrivAt.comp {N : LB (A ⊗ Y).left} {T T' : Over S} {y : T ⟶ Y} (h : IsTrivAt N y) (u : T' ⟶ T) :
    IsTrivAt N (u ≫ y) := by
  have e : lift (fst A T') (snd A T' ≫ u ≫ y) = lift (fst A T') (snd A T' ≫ u) ≫ lift (fst A T) (snd A T ≫ y) := by
    ext <;> simp
  unfold IsTrivAt ev at *
  rw [e, Over.comp_left]
  exact GlobalTheory.Biadditive.triv_pull_comp h _

def Locus (N : LB (A ⊗ Y).left) {T : Scheme.{0}} (t : T ⟶ Y.left) : Prop :=
  IsTrivAt N (Over.homMk t rfl : Over.mk (t ≫ Y.hom) ⟶ Y)

theorem locus_left_iff {N : LB (A ⊗ Y).left} {T : Over S} (y : T ⟶ Y) : Locus N y.left ↔ IsTrivAt N y := by
  have w : y.left ≫ Y.hom = T.hom := Over.w y
  let u : T ⟶ Over.mk (y.left ≫ Y.hom) := Over.homMk (𝟙 _) (by simp [w])
  let v : Over.mk (y.left ≫ Y.hom) ⟶ T := Over.homMk (𝟙 _) (by simp [w])
  constructor
  · intro h
    have := IsTrivAt.comp h u
    have e : u ≫ (Over.homMk y.left rfl : Over.mk (y.left ≫ Y.hom) ⟶ Y) = y := by
      ext; simp [u]
    rwa [e] at this
  · intro h
    have := IsTrivAt.comp h v
    have e : v ≫ y = (Over.homMk y.left rfl : Over.mk (y.left ≫ Y.hom) ⟶ Y) := by
      ext; simp [v]
    unfold Locus
    rwa [e] at this

theorem Locus.comp {N : LB (A ⊗ Y).left} {T T' : Scheme.{0}} {t : T ⟶ Y.left} (h : Locus N t) (u : T' ⟶ T) :
    Locus N (u ≫ t) := by
  let v : Over.mk ((u ≫ t) ≫ Y.hom) ⟶ Over.mk (t ≫ Y.hom) := Over.homMk u (by simp)
  have := IsTrivAt.comp h v
  have e : v ≫ (Over.homMk t rfl : Over.mk (t ≫ Y.hom) ⟶ Y) = (Over.homMk (u ≫ t) rfl : Over.mk ((u ≫ t) ≫ Y.hom) ⟶ Y) := by
    ext; simp [v]
  unfold Locus
  rwa [e] at this

end GlobalTheory.CompanionTheory.TrivLoc
