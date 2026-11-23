import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Formalism.SharpRestriction.LevelLetterCocycles.TWSet
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF Vc Wc)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Artin

variable {Ω : Type} [Field Ω] [Algebra D.host.E Ω] {A : Type} [CommGroup A]

structure Recip (D : D7) (Ω : Type) [Field Ω] [Algebra D.host.E Ω] where
  κ : AE D →+* AdeleRing (𝓞 D.host.E) D.host.E
  art : Ideles D.host.E →* Gab D.host.E Ω

structure Recip.Good (a : Recip D Ω) : Prop where
  cont : Continuous a.κ
  rat : ∀ x : D.host.E, a.κ (incA D x) = algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) x
  loc : ∀ (P : Pl D.host.E) (e : AE D), Formalism.L2.JoinChr.IsPlIdem D e P → ∀ k : D.host.Eˣ,
    a.κ (Formalism.L2.JoinChr.locE D e (k : D.host.E)) =
      ((Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k) : Ideles D.host.E) :
        AdeleRing (𝓞 D.host.E) D.host.E)
  artin : IsGlobalArtin a.art

theorem exists_recip_good (h : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (Ω : Type) [Field Ω] [Algebra D.host.E Ω]
    [IsAlgClosure D.host.E Ω] : ∃ a : Recip D Ω, a.Good := by
  obtain ⟨art, ha⟩ := h D.host.E Ω
  obtain ⟨κ, h1, h2, h3⟩ := GlobalTheory.CharTransport.exists_hom D
  exact ⟨⟨κ, art⟩, h1, h2, h3, ha⟩

def Recip.sym (a : Recip D Ω) : (AE D)ˣ →* Gab D.host.E Ω := a.art.comp (Units.map a.κ.toMonoidHom)

open Classical in

def descend (φ : G D.host.E Ω →* A) : Gab D.host.E Ω →* A :=
  if h : (commutator (G D.host.E Ω)).topologicalClosure ≤ φ.ker then QuotientGroup.lift _ φ h else 1

theorem descend_toAb {φ : G D.host.E Ω →* A} (h : IsOpen (φ.ker : Set (G D.host.E Ω))) (σ : G D.host.E Ω) :
    descend φ (toAb D.host.E Ω σ) = φ σ := by
  rw [descend, dif_pos (Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker φ)
    (Subgroup.isClosed_of_isOpen _ h))]
  rfl

def Recip.pull (a : Recip D Ω) (φ : G D.host.E Ω →* A) : (AE D)ˣ →* A := (descend φ).comp a.sym

theorem Recip.pull_eq (a : Recip D Ω) {φ : G D.host.E Ω →* A} (h : IsOpen (φ.ker : Set (G D.host.E Ω))) {x : (AE D)ˣ}
    {σ : G D.host.E Ω} (hx : a.sym x = toAb D.host.E Ω σ) : a.pull φ x = φ σ := by
  rw [Recip.pull, MonoidHom.comp_apply, hx, descend_toAb h]

theorem Recip.exists_sym (a : Recip D Ω) (x : (AE D)ˣ) : ∃ σ, a.sym x = toAb D.host.E Ω σ :=
  (QuotientGroup.mk'_surjective _ (a.sym x)).imp fun _ h => h.symm

@[simp] theorem Recip.pull_one (a : Recip D Ω) : a.pull (1 : G D.host.E Ω →* A) = 1 := by
  ext x
  obtain ⟨σ, h⟩ := a.exists_sym x
  rw [a.pull_eq (by simp) h]
  rfl

theorem Recip.pull_comp (a : Recip D Ω) {A' : Type} [CommGroup A'] {φ : G D.host.E Ω →* A}
    (h : IsOpen (φ.ker : Set (G D.host.E Ω))) (f : A →* A') : a.pull (f.comp φ) = f.comp (a.pull φ) := by
  ext x
  obtain ⟨σ, hx⟩ := a.exists_sym x
  rw [MonoidHom.comp_apply, a.pull_eq h hx,
    a.pull_eq (Subgroup.isOpen_mono (H₁ := φ.ker) (fun g hg => by simp [MonoidHom.mem_ker.1 hg]) h) hx]
  rfl

end Artin

def unitPart : ℂˣ →* Circle where
  toFun z := ⟨(z : ℂ) / ‖(z : ℂ)‖, by simp [Submonoid.unitSphere, z.ne_zero]⟩
  map_one' := Circle.ext (by simp)
  map_mul' z w := Circle.ext (by
    change ((z * w : ℂˣ) : ℂ) / ‖((z * w : ℂˣ) : ℂ)‖ = (z : ℂ) / ‖(z : ℂ)‖ * ((w : ℂ) / ‖(w : ℂ)‖)
    rw [Units.val_mul, norm_mul, Complex.ofReal_mul, div_mul_div_comm])

theorem unitPart_of_pow {z : ℂˣ} {n : ℕ} (hn : n ≠ 0) (h : z ^ n = 1) : ((unitPart z : Circle) : ℂ) = z := by
  have h1 : ‖(z : ℂ)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]) hn
  change (z : ℂ) / ‖(z : ℂ)‖ = z
  rw [h1, Complex.ofReal_one, div_one]

def resOf {A : Type} [CommGroup A] (χ : (AE D)ˣ →* A) : ResChars D A := fun P => Classical.epsilon (IsResAt χ P)

theorem isResAt_resOf {A : Type} [CommGroup A] {χ : (AE D)ˣ →* A} {P : Pl D.host.E} (h : ∃ c, IsResAt χ P c) :
    IsResAt χ P (resOf χ P) := Classical.epsilon_spec h

structure IsChoice (ch : Set (Pl D.host.E)) : Prop where
  pair : ∀ P P', IsConjPl D.host P P' → P ≠ P' → (P ∈ ch ↔ P' ∉ ch)
  one : ∀ P ∈ ch, ∀ P' ∈ ch, (∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.E) ∈ P.asIdeal ∧ (p : 𝓞 D.host.E) ∈ P'.asIdeal) →
    P.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = P'.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

open Classical in

def half (ch : Set (Pl D.host.E)) (Q : Finset (Pl D.host.E)) : Finset (Pl D.host.E) := Q.filter (· ∈ ch)

theorem mem_half {ch : Set (Pl D.host.E)} {Q : Finset (Pl D.host.E)} {P : Pl D.host.E} : P ∈ half ch Q ↔ P ∈ Q ∧ P ∈ ch := by
  classical
  exact Finset.mem_filter

@[simp] theorem half_empty (ch : Set (Pl D.host.E)) : half ch ∅ = ∅ := Finset.eq_empty_of_forall_notMem fun _ h => Finset.notMem_empty _ (mem_half.1 h).1

section Tw

variable {Ω : Type} [Field Ω] [Algebra D.host.E Ω] (a : Recip D Ω) {R : Type} [CommRing R] (f : R →+* ℂ)

def charOf (ψ : G D.host.E Ω →* Rˣ) : (AE D)ˣ →* Circle := unitPart.comp ((Units.map f.toMonoidHom).comp (a.pull ψ))

theorem charOf_eq {ψ : G D.host.E Ω →* Rˣ} (h : IsOpen (ψ.ker : Set (G D.host.E Ω))) {x : (AE D)ˣ} {σ : G D.host.E Ω}
    (hx : a.sym x = toAb D.host.E Ω σ) {n : ℕ} (hn : n ≠ 0) (hψ : ψ σ ^ n = 1) :
    ((charOf a f ψ x : Circle) : ℂ) = f (ψ σ : Rˣ) := by
  rw [charOf, MonoidHom.comp_apply, MonoidHom.comp_apply, a.pull_eq h hx, unitPart_of_pow hn (by rw [← map_pow, hψ, map_one])]
  rfl

@[simp] theorem charOf_one : charOf a f 1 = 1 := by
  rw [charOf, Recip.pull_one, MonoidHom.comp_one, MonoidHom.comp_one]

def twistOf (ch : Set (Pl D.host.E)) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E Ω →* Rˣ) : Twist D Circle :=
  ⟨half ch Q, charOf a f ψ, resOf (charOf a f ψ)⟩

end Tw

section Univ

variable {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

instance (i : X.Tw) (M : ℕ) : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩

variable (X) in
open Classical in

def admissibleConjugatePairPlaces (i : X.Tw) (Q : Finset (Pl D.host.E)) (M : ℕ) : Finset (Pl D.host.E) :=
  Q.filter fun P => ∃ P' ∈ Q, IsConjPl D.host P P' ∧ Formalism.MainNotions.NAdm.AdmQ X i {P, P'} M

open Classical in
theorem mem_admissibleConjugatePairPlaces_iff {i : X.Tw} {Q : Finset (Pl D.host.E)} {M : ℕ} {P : Pl D.host.E} : P ∈ admissibleConjugatePairPlaces X i Q M ↔
    P ∈ Q ∧ ∃ P' ∈ Q, IsConjPl D.host P P' ∧ Formalism.MainNotions.NAdm.AdmQ X i {P, P'} M := Finset.mem_filter

theorem admissibleConjugatePairPlaces_subset (i : X.Tw) (Q : Finset (Pl D.host.E)) (M : ℕ) : admissibleConjugatePairPlaces X i Q M ⊆ Q := fun _ h => (mem_admissibleConjugatePairPlaces_iff.1 h).1

@[simp] theorem admissibleConjugatePairPlaces_empty (i : X.Tw) (M : ℕ) : admissibleConjugatePairPlaces X i ∅ M = ∅ := Finset.subset_empty.1 (admissibleConjugatePairPlaces_subset i ∅ M)

theorem conj_mem_admissibleConjugatePairPlaces {i : X.Tw} {Q : Finset (Pl D.host.E)} {M : ℕ} {P P' : Pl D.host.E} (h : P ∈ admissibleConjugatePairPlaces X i Q M)
    (hc : IsConjPl D.host P P') : P' ∈ admissibleConjugatePairPlaces X i Q M := by
  classical
  obtain ⟨h1, P'', h2, h3, h4⟩ := mem_admissibleConjugatePairPlaces_iff.1 h
  obtain rfl := GlobalTheory.GalChar.isConjPl_unique hc h3
  exact mem_admissibleConjugatePairPlaces_iff.2 ⟨h2, P, h1, GlobalTheory.GalChar.isConjPl_symm hc, by rwa [Finset.pair_comm]⟩

theorem ne_of_split {P P' : Pl D.host.E} (h : IsSplitPl D.host P) (hc : IsConjPl D.host P P') : P ≠ P' := by
  rintro rfl
  obtain ⟨x, hx, h2⟩ := h
  exact h2 (RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) x) rfl ((hc x _ rfl).1 hx)

theorem isSplit_of_mem_admissibleConjugatePairPlaces {i : X.Tw} {Q : Finset (Pl D.host.E)} {M : ℕ} {P : Pl D.host.E} (h : P ∈ admissibleConjugatePairPlaces X i Q M) :
    IsSplitPl D.host P := by
  obtain ⟨-, P', -, -, h4⟩ := mem_admissibleConjugatePairPlaces_iff.1 h
  exact (h4.1 P (by simp)).1

variable (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (Q : Finset (Pl D.host.E)) (M : ℕ)

open Classical in

def coord (P : Pl D.host.E) : G D.host.E N.Om →* Multiplicative (ZMod (X.l i ^ M)) :=
  if h : P ∈ Q then
    (AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : ↥Q => ZMod (X.l i ^ M)) ⟨P, h⟩)).comp (Y.delU i Q M)
  else 1

theorem coord_apply {P : Pl D.host.E} (h : P ∈ Q) (σ : G D.host.E N.Om) :
    Multiplicative.toAdd (coord Y i Q M P σ) = Multiplicative.toAdd (Y.delU i Q M σ) ⟨P, h⟩ := by
  rw [coord, dif_pos h]
  rfl

def univOf (a : Recip D N.Om) : UnivTwist D (ZMod (X.l i ^ M)) :=
  ⟨fun P => a.pull (coord Y i Q M P), fun P => resOf (a.pull (coord Y i Q M P)) P⟩

open Classical in

def weight (P : ↥Q) (v : Pl D.host.E) : ZMod (X.l i ^ M) :=
  if v = P.1 then 1
  else if h : v ∈ Q ∧ IsConjPl D.host P.1 v then (((Y.delU_conj i Q M P.1 P.2 v h.1 h.2).choose : ℤ) : ZMod (X.l i ^ M)) else 0

variable (ch : Set (Pl D.host.E))

def spread : (↥(half ch (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) →+ DelQM D.host (X.l i) Q M where
  toFun x v := ∑ P, weight Y i (admissibleConjugatePairPlaces X i Q M) M ⟨P.1, (mem_half.1 P.2).1⟩ v.1 * x P
  map_zero' := by funext v; simp
  map_add' x y := by funext v; simp [mul_add, Finset.sum_add_distrib]

theorem spread_apply (x : ↥(half ch (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) (v : ↥Q) : spread Y i Q M ch x v =
    ∑ P, weight Y i (admissibleConjugatePairPlaces X i Q M) M ⟨P.1, (mem_half.1 P.2).1⟩ v.1 * x P := rfl

theorem spread_of_not_mem (x : ↥(half ch (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) (v : ↥Q) (hv : v.1 ∉ admissibleConjugatePairPlaces X i Q M) :
    spread Y i Q M ch x v = 0 := by
  refine Finset.sum_eq_zero fun P _ => ?_
  rw [weight, if_neg fun e : v.1 = P.1 => hv (e ▸ (mem_half.1 P.2).1), dif_neg fun h => hv h.1, zero_mul]

variable {ch}

theorem spread_of_mem (hch : IsChoice ch) (x : ↥(half ch (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) (v : ↥Q)
    (hv : v.1 ∈ half ch (admissibleConjugatePairPlaces X i Q M)) : spread Y i Q M ch x v = x ⟨v.1, hv⟩ := by
  rw [spread_apply, Finset.sum_eq_single ⟨v.1, hv⟩, weight, if_pos rfl, one_mul]
  · intro P _ hP
    have hne : v.1 ≠ P.1 := fun e => hP (Subtype.ext e.symm)
    rw [weight, if_neg hne, dif_neg fun h => (hch.pair _ _ h.2 hne.symm).1 (mem_half.1 P.2).2 (mem_half.1 hv).2, zero_mul]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem spread_coord (hch : IsChoice ch) (σ : G D.host.E N.Om) (v : ↥Q) :
    spread Y i Q M ch (fun P => Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M P.1 σ)) v =
      Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M v.1 σ) := by
  by_cases hv : v.1 ∈ admissibleConjugatePairPlaces X i Q M
  · by_cases hc : v.1 ∈ ch
    · exact spread_of_mem Y i Q M hch _ v (mem_half.2 ⟨hv, hc⟩)
    · obtain ⟨-, P, -, hP, -⟩ := mem_admissibleConjugatePairPlaces_iff.1 hv
      have hne : v.1 ≠ P := ne_of_split (isSplit_of_mem_admissibleConjugatePairPlaces hv) hP
      have hPc : P ∈ ch := by
        by_contra h
        exact hc ((hch.pair _ _ hP hne).2 h)
      have hPa := conj_mem_admissibleConjugatePairPlaces hv hP
      have hP' := GlobalTheory.GalChar.isConjPl_symm hP
      rw [spread_apply, Finset.sum_eq_single ⟨P, mem_half.2 ⟨hPa, hPc⟩⟩, weight, if_neg hne, dif_pos ⟨hv, hP'⟩,
        coord_apply _ _ _ _ hv, coord_apply _ _ _ _ hPa]
      · exact ((Y.delU_conj i _ M P hPa v.1 hv hP').choose_spec σ).symm
      · intro P' _ h'
        rw [weight, if_neg fun e : v.1 = P'.1 => hc (e ▸ (mem_half.1 P'.2).2), dif_neg fun h => h' (Subtype.ext
          (GlobalTheory.GalChar.isConjPl_unique (GlobalTheory.GalChar.isConjPl_symm h.2) hP)), zero_mul]
      · exact fun h => absurd (Finset.mem_univ _) h
  · rw [spread_of_not_mem Y i Q M ch _ v hv, coord, dif_neg hv]
    rfl

end Univ

example : ((unitPart (-1) : Circle) : ℂ) = -1 := unitPart_of_pow two_ne_zero (by simp)

end GlobalTheory.SeriesTie

end
