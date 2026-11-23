import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolume
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMassStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumTransversalEqTsumOrbitQuotientGeneral

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordAmp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : HermSp M V} {r k : ℕ} {P : LocNG.FPair H r} {S : Frames M.L r k}

open scoped Pointwise ENNReal Classical in
private lemma tsum_transversal_eq_tsum_orbits_lemma {T X G R : Type*} [Group G] [MulAction G X]
    [AddCommMonoid R] [TopologicalSpace R] (St : Subgroup G)
    (rel : T → T → Prop) (A B : Set T) (hB : _root_.Formalism.MainNotions.S.LocNG.IsTransv rel A B) (ℓ : T → X) (term : X → Prop)
    (p : T → Prop) (Q : X → Prop)
    (hterm : ∀ t ∈ A, term (ℓ t)) (hsurj : ∀ Λ, term Λ → ∃ t ∈ A, ℓ t = Λ)
    (hrel : ∀ t t', rel t t' ↔ ∃ g ∈ St, ℓ t' = g • ℓ t)
    (hinv : ∀ Λ, term Λ → ∀ g ∈ St, term (g • Λ))
    (hpQ : ∀ t ∈ A, (p t ↔ Q (ℓ t))) (hQ : ∀ Λ, term Λ → ∀ g ∈ St, Q Λ → Q (g • Λ))
    (f : X → R) (hf : ∀ Λ, term Λ → ∀ g ∈ St, f (g • Λ) = f Λ)
    (val : T → R) (hval : ∀ t ∈ A, val t = f (ℓ t)) :
    ∑' t : {t // t ∈ B ∧ p t}, val t.1
      = ∑' o : MulAction.orbitRel.Quotient St X,
          if term (Quotient.out o) ∧ Q (Quotient.out o) then f (Quotient.out o) else 0 := by
  obtain ⟨hBA, hcover, huniq⟩ := hB
  have key : ∀ Λ : X, ∃ g ∈ St,
      Quotient.out (Quotient.mk (MulAction.orbitRel St X) Λ) = g • Λ := fun Λ => by
    obtain ⟨⟨g, hg⟩, hgx⟩ := Quotient.mk_out (s := MulAction.orbitRel St X) Λ
    exact ⟨g, hg, hgx.symm⟩
  let toFun : {t // t ∈ B ∧ p t} →
      ↥{o : MulAction.orbitRel.Quotient St X | term (Quotient.out o) ∧ Q (Quotient.out o)} :=
    fun t => ⟨Quotient.mk _ (ℓ t.1), by
      obtain ⟨g, hg, he⟩ := key (ℓ t.1)
      have h1 := hterm _ (hBA t.2.1)
      show term (Quotient.out (Quotient.mk (MulAction.orbitRel St X) (ℓ t.1)))
        ∧ Q (Quotient.out (Quotient.mk (MulAction.orbitRel St X) (ℓ t.1)))
      rw [he]
      exact ⟨hinv _ h1 g hg, hQ _ h1 g hg ((hpQ _ (hBA t.2.1)).1 t.2.2)⟩⟩
  have hbij : Function.Bijective toFun := by
    constructor
    · rintro ⟨t, ht⟩ ⟨t', ht'⟩ heq
      have h2 : Quotient.mk (MulAction.orbitRel St X) (ℓ t) = Quotient.mk _ (ℓ t') :=
        congrArg Subtype.val heq
      obtain ⟨⟨g, hg⟩, hgx⟩ := Quotient.exact h2
      have : rel t' t := (hrel t' t).2 ⟨g, hg, hgx.symm⟩
      exact Subtype.ext (huniq _ ht'.1 _ ht.1 this).symm
    · rintro ⟨o, ho⟩
      obtain ⟨t0, ht0A, ht0⟩ := hsurj _ ho.1
      obtain ⟨y, hyB, hy⟩ := hcover t0 ht0A
      obtain ⟨g, hg, hgy⟩ := (hrel y t0).1 hy
      have hyA := hBA hyB
      have hQy : Q (ℓ y) := by
        have := hQ (ℓ t0) (hterm _ ht0A) g⁻¹ (inv_mem hg) (by rw [ht0]; exact ho.2)
        rwa [hgy, inv_smul_smul] at this
      refine ⟨⟨y, hyB, (hpQ y hyA).2 hQy⟩, Subtype.ext ?_⟩
      show Quotient.mk _ (ℓ y) = o
      rw [← Quotient.out_eq o, ← ht0, hgy]
      exact Quotient.sound ⟨⟨g⁻¹, inv_mem hg⟩, inv_smul_smul g _⟩
  let e := Equiv.ofBijective toFun hbij
  have hR : (∑' o : MulAction.orbitRel.Quotient St X,
      if term (Quotient.out o) ∧ Q (Quotient.out o) then f (Quotient.out o) else 0)
      = ∑' o : ↥{o : MulAction.orbitRel.Quotient St X |
          term (Quotient.out o) ∧ Q (Quotient.out o)}, f (Quotient.out o.1) := by
    refine Eq.trans ?_ (tsum_subtype _ (fun o => f (Quotient.out o))).symm
    refine tsum_congr fun o => ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [hR, ← e.tsum_eq]
  refine tsum_congr fun t => ?_
  show val t.1 = f (Quotient.out (Quotient.mk _ (ℓ t.1)))
  obtain ⟨g, hg, he⟩ := key (ℓ t.1)
  rw [he, hf _ (hterm _ (hBA t.2.1)) g hg, hval _ (hBA t.2.1)]

open scoped Pointwise ENNReal Classical in
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k} in

theorem _root_.GlobalTheory.HL.CoordAmp.sums_eq (hM : M.OK) (c : _root_.GlobalTheory.HL.Coord P S)
    (R : _root_.Formalism.MainNotions.S.LocNG.Reps P) (d : _root_.Formalism.MainNotions.S.LocNG.Datum P)
    (p : _root_.Formalism.MainNotions.S.Loc.Term V M r → Prop) (Q : Submodule M.L.O S.V → Prop)
    (hpQ : ∀ t, _root_.Formalism.MainNotions.S.LocNG.IsTermOver P d t → (p t ↔ Q (c.lat t.abelian₂)))
    (hQ : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ h ∈ S.St, Q Λ → Q (h • Λ)) :
    _root_.Formalism.MainNotions.S.LocNG.amp R d p = S.amp (c.dat d) Q ∧
      (∑' t : {t // t ∈ R.RT d ∧ p t}, ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t.1))
        = S.mass (c.dat d) Q := by
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨-, -, hbij, hlatg, -, hmu⟩ := _root_.GlobalTheory.HL.CoordMass.transport M hM H r k P S c
  obtain ⟨-, -, -, hSt, -⟩ := _root_.GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  obtain ⟨hcorr, hex, -⟩ := _root_.GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c
  have hB := R.hRT d
  have hrel : ∀ t t', _root_.Formalism.MainNotions.S.LocNG.TRel P t t' ↔ ∃ g ∈ S.St,
      c.lat t'.abelian₂ = g • c.lat t.abelian₂ := by
    intro t t'
    unfold _root_.Formalism.MainNotions.S.LocNG.TRel
    constructor
    · rintro ⟨s, hs, he⟩
      exact ⟨c.grp s, (hSt s).1 hs, by rw [he, hlatg]⟩
    · rintro ⟨g, hg, he⟩
      refine ⟨c.grp.symm g, (hSt _).2 (by simpa using hg), hbij.1 ?_⟩
      rw [hlatg, MulEquiv.apply_symm_apply, he]
  have hterm_inv : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ g ∈ S.St, S.IsTerm (c.dat d) (g • Λ) :=
    fun Λ h g hg => (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S _ Λ h g hg).1
  have hom_inv : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ g ∈ S.St,
        S.om (c.dat d) (g • Λ) = S.om (c.dat d) Λ :=
    fun Λ h g hg => (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S _ Λ h g hg).2.1
  have hmu_inv : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ g ∈ S.St,
        S.mu (g • Λ) = S.mu Λ :=
    fun Λ h g hg => ((_root_.GlobalTheory.HL.volSt M.L r k S).1 Λ
      (_root_.GlobalTheory.HL.TermBasic.term_basic M.L r k S _ Λ h).1.1).2.2 g hg
  constructor
  · unfold _root_.Formalism.MainNotions.S.LocNG.amp _root_.GlobalTheory.HL.Frames.amp
    exact tsum_transversal_eq_tsum_orbits_lemma S.St (_root_.Formalism.MainNotions.S.LocNG.TRel P) _ _ hB
      (fun t => c.lat t.abelian₂) (S.IsTerm (c.dat d)) p Q
      (fun t ht => (hcorr d t ht).1) (fun Λ h => hex d Λ h) hrel hterm_inv hpQ hQ
      (fun Λ => (S.mu Λ : ℂ) * S.om (c.dat d) Λ)
      (fun Λ h g hg => by simp only [hmu_inv Λ h g hg, hom_inv Λ h g hg])
      (fun t => (_root_.Formalism.MainNotions.S.LocNG.mu P t : ℂ) * _root_.Formalism.MainNotions.S.LocNG.om P t)
      (fun t ht => by simp only [hmu t, (hcorr d t ht).2.1])
  · unfold _root_.GlobalTheory.HL.Frames.mass
    exact tsum_transversal_eq_tsum_orbits_lemma S.St (_root_.Formalism.MainNotions.S.LocNG.TRel P) _ _ hB
      (fun t => c.lat t.abelian₂) (S.IsTerm (c.dat d)) p Q
      (fun t ht => (hcorr d t ht).1) (fun Λ h => hex d Λ h) hrel hterm_inv hpQ hQ
      (fun Λ => ENNReal.ofReal (S.mu Λ))
      (fun Λ h g hg => by simp only [hmu_inv Λ h g hg])
      (fun t => ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t))
      (fun t _ => by simp only [hmu t])

open scoped Pointwise ENNReal Classical in
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k} in

theorem _root_.GlobalTheory.HL.CoordAmp.amp_mass_eq : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : _root_.Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : _root_.Formalism.MainNotions.S.Loc.HermSp M V) (r k : ℕ)
    (P : _root_.Formalism.MainNotions.S.LocNG.FPair H r), ∀ (S : _root_.GlobalTheory.HL.Frames M.L r k) (c : _root_.GlobalTheory.HL.Coord P S),
    ∀ (R : _root_.Formalism.MainNotions.S.LocNG.Reps P) (d : _root_.Formalism.MainNotions.S.LocNG.Datum P),
    _root_.Formalism.MainNotions.S.LocNG.amp R d (_root_.Formalism.MainNotions.S.LocNG.BBne (H := H)) = S.amp (c.dat d)
        (fun Λ => ¬ S.BBzero (c.dat d) Λ) ∧
      _root_.Formalism.MainNotions.S.LocNG.amp R d (fun t => ¬ _root_.Formalism.MainNotions.S.LocNG.BBne (H := H) t) = S.amp (c.dat d)
        (S.BBzero (c.dat d)) ∧
      _root_.Formalism.MainNotions.S.LocNG.amp R d (fun _ => True) = S.amp (c.dat d) (fun _ => True) ∧
      (∑' t : R.RT d, ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t.1))
        = S.mass (c.dat d) (fun _ => True) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c R d
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨hcorr, -, -⟩ := _root_.GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c
  have hBB : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ h ∈ S.St,
        (S.BBzero (c.dat d) (h • Λ)
          ↔ S.BBzero (c.dat d) Λ) :=
    fun Λ hΛ h hh => (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S _ Λ hΛ h hh).2.2.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d _ _
      (fun t ht => (hcorr d t ht).2.2)
      (fun Λ hΛ h hh hq => by rwa [hBB Λ hΛ h hh])).1
  · exact (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d _ _
      (fun t ht => by rw [(hcorr d t ht).2.2, not_not])
      (fun Λ hΛ h hh hq => (hBB Λ hΛ h hh).2 hq)).1
  · exact (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d (fun _ => True) (fun _ => True)
      (fun _ _ => Iff.rfl) (fun _ _ _ _ _ => trivial)).1
  · rw [← (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d (fun _ => True) (fun _ => True)
      (fun _ _ => Iff.rfl) (fun _ _ _ _ _ => trivial)).2]
    exact ((Equiv.subtypeEquivRight (fun t => by simp)).tsum_eq
      (fun t => ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t.1))).symm

end GlobalTheory.HL.CoordAmp
