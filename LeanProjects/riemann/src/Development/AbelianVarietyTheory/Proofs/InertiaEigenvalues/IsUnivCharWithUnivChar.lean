import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisExportOfMatrixDetBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.TwistDet

namespace GlobalTheory.UnivChar

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

section Chosen

def IsUnivChar (Y : NExp D.R D.host D.what₂ D.LL0 N X) : Prop :=
  ∀ i Q M, Y.delU i Q M = GalChar.delU D.host X.cc (X.l i) Q M

def withUnivChar (Y : NExp D.R D.host D.what₂ D.LL0 N X) : NExp D.R D.host D.what₂ D.LL0 N X :=
  { Y with
    delU := fun i Q M => GalChar.delU D.host X.cc (X.l i) Q M
    delU_unr := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).1
    delU_l := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.1
    delU_anti := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.1
    delU_open := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.1
    delU_res := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.2.1
    delU_conj := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.2.2.1 }

end Chosen

section Family

variable (X) in

abbrev Fam (i : X.Tw) (M : ℕ) : Type := PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))

def admitted (H : Subgroup (GE N)) (S : Finset (PlE D.host)) (P : PlE D.host) : Prop :=
  P ∉ S ∧ IsSplitPl D.host P ∧ DecV N P ≤ H

def IsCharOfFam (Y : NExp D.R D.host D.what₂ D.LL0 N X) (H : X.Tw → ℕ → Subgroup (GE N))
    (S : X.Tw → ℕ → Finset (PlE D.host)) (d : ∀ i M, Fam X i M) : Prop :=
  ∀ i M Q, ConjCl (D := D) Q → ∀ (P : PlE D.host) (hP : P ∈ Q),
    (∃ v, Over P v ∧ admitted (H i M) (S i M) v ∧ ∃ s : ℤˣ, ∀ σ, Multiplicative.toAdd (Y.delU i Q M σ) ⟨P, hP⟩ =
      ((s : ℤ) : ZMod (X.l i ^ M)) * Multiplicative.toAdd (d i M v σ)) ∨
    ((∀ v, Over P v → ¬ admitted (H i M) (S i M) v) ∧ ∀ σ, Multiplicative.toAdd (Y.delU i Q M σ) ⟨P, hP⟩ = 0)

variable {i : X.Tw} {M : ℕ} (H : Subgroup (GE N)) (S : Finset (PlE D.host)) (d : Fam X i M)

open Classical in

def setChar (T : Set (PlE D.host)) : GE N →* Multiplicative (ZMod (X.l i ^ M)) :=
  if h : ∃ v, v ∈ T ∧ admitted H S v then d h.choose else 1

open Classical in

def famCoord (Q : Finset (PlE D.host)) (P : PlE D.host) : GE N →* Multiplicative (ZMod (X.l i ^ M)) :=
  if GalChar.pair D.host P ⊆ ↑Q then setChar H S d (GalChar.pair D.host P) else 1

def famDel (Q : Finset (PlE D.host)) : GE N →* Multiplicative (DelQM D.host (X.l i) Q M) :=
  delAll X i M fun P : ↥Q => famCoord H S d Q P.1

theorem famDel_apply (Q : Finset (PlE D.host)) (σ : GE N) (P : ↥Q) :
    Multiplicative.toAdd (famDel H S d Q σ) P = Multiplicative.toAdd (famCoord H S d Q P.1 σ) := rfl

theorem famDel_eq_one_iff (Q : Finset (PlE D.host)) (σ : GE N) :
    famDel H S d Q σ = 1 ↔ ∀ P ∈ Q, famCoord H S d Q P σ = 1 :=
  ⟨fun h P hP => Multiplicative.toAdd.injective (congrFun (congrArg Multiplicative.toAdd h) ⟨P, hP⟩),
    fun h => Multiplicative.toAdd.injective (funext fun P => congrArg Multiplicative.toAdd (h P.1 P.2))⟩

theorem famCoord_of_closed {Q : Finset (PlE D.host)} (hQ : ConjCl (D := D) Q) {P : PlE D.host} (hP : P ∈ Q) :
    famCoord H S d Q P = setChar H S d (GalChar.pair D.host P) := by
  refine if_pos ?_
  rintro v (rfl | hv)
  · exact hP
  · exact hQ P hP v hv

theorem famCoord_conj (Q : Finset (PlE D.host)) {P P' : PlE D.host} (h : IsConjPl D.host P P') :
    famCoord H S d Q P' = famCoord H S d Q P := by
  unfold famCoord
  rw [GalChar.pair_eq h]

theorem setChar_pair (P : PlE D.host) :
    (∃ v, Over P v ∧ admitted H S v ∧ setChar H S d (GalChar.pair D.host P) = d v) ∨
    ((∀ v, Over P v → ¬ admitted H S v) ∧ setChar H S d (GalChar.pair D.host P) = 1) := by
  by_cases h : ∃ v, v ∈ GalChar.pair D.host P ∧ admitted H S v
  · exact Or.inl ⟨h.choose, h.choose_spec.1, h.choose_spec.2, dif_pos h⟩
  · exact Or.inr ⟨fun v hv ha => h ⟨v, hv, ha⟩, dif_neg h⟩

variable {H S d}

theorem famCoord_laws (h : AdmFam X i M H S d) (Q : Finset (PlE D.host)) (P : PlE D.host) :
    IsOpen ((famCoord H S d Q P).ker : Set (GE N)) ∧ AntiHom X.cc (famCoord H S d Q P) ∧
    TrivAbove (famCoord H S d Q P) (X.l i) ∧
    (∀ v, v ∉ Q → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A,
      famCoord H S d Q P σ = 1) := by
  have triv : ∀ c : GE N →* Multiplicative (ZMod (X.l i ^ M)), c = 1 →
      IsOpen (c.ker : Set (GE N)) ∧ AntiHom X.cc c ∧ TrivAbove c (X.l i) ∧
      (∀ v, v ∉ Q → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, c σ = 1) := by
    rintro _ rfl
    exact ⟨by rw [MonoidHom.ker_one]; exact isOpen_univ, fun _ _ _ => inv_one.symm, fun _ _ _ _ _ _ => rfl,
      fun _ _ _ _ _ _ => rfl⟩
  by_cases hs : GalChar.pair D.host P ⊆ ↑Q
  · have e : famCoord H S d Q P = setChar H S d (GalChar.pair D.host P) := if_pos hs
    rcases setChar_pair H S d P with ⟨v, hv, ha, e'⟩ | ⟨-, e'⟩
    · obtain ⟨h1, h2, h3, h4, -⟩ := h.2.2.2 v ha.1 ha.2.1 ha.2.2
      rw [e, e']
      exact ⟨h1, h2, h3, fun w hw => h4 w fun ho => hw (hs (over_trans hv ho))⟩
    · exact triv _ (e.trans e')
  · exact triv _ (if_neg hs)

end Family

section Record

variable {H : X.Tw → ℕ → Subgroup (GE N)} {S : X.Tw → ℕ → Finset (PlE D.host)} {d : ∀ i M, Fam X i M}

def withFam (Y : NExp D.R D.host D.what₂ D.LL0 N X) (h : ∀ i M, AdmFam X i M (H i M) (S i M) (d i M)) :
    NExp D.R D.host D.what₂ D.LL0 N X :=
  { Y with
    delU := fun i Q M => famDel (H i M) (S i M) (d i M) Q
    delU_unr := fun i Q M v hv A hA σ hσ =>
      (famDel_eq_one_iff _ _ _ Q σ).2 fun P _ => (famCoord_laws (h i M) Q P).2.2.2 v hv A hA σ hσ
    delU_l := fun i Q M v hv A hA σ hσ =>
      (famDel_eq_one_iff _ _ _ Q σ).2 fun P _ => (famCoord_laws (h i M) Q P).2.2.1 v hv A hA σ hσ
    delU_anti := fun i Q M g g' hg => Multiplicative.toAdd.injective (funext fun P =>
      congrArg Multiplicative.toAdd ((famCoord_laws (h i M) Q P.1).2.1 g g' hg))
    delU_open := fun i Q M => by
      have e : ((famDel (H i M) (S i M) (d i M) Q).ker : Set (GE N)) =
          ⋂ P ∈ Q, ((famCoord (H i M) (S i M) (d i M) Q P).ker : Set (GE N)) := by
        ext σ
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, famDel_eq_one_iff]
      rw [e]
      exact isOpen_biInter_finset fun P _ => (famCoord_laws (h i M) Q P).1
    delU_res := fun i M Q' Q hs h1 h2 σ P hP => by
      rw [famDel_apply, famDel_apply, famCoord_of_closed _ _ _ h1 hP, famCoord_of_closed _ _ _ h2 (hs hP)]
    delU_conj := fun i Q M P hP P' hP' hc => ⟨1, fun σ => by
      rw [famDel_apply, famDel_apply]
      simp only [famCoord_conj _ _ _ Q hc, Units.val_one, Int.cast_one, one_mul]⟩ }

end Record

theorem delUTie_of_isUnivChar (Y : NExp D.R D.host D.what₂ D.LL0 N X) : K1 X → IsUnivChar Y → DelUTie Y :=
  fun hK hY => GalChar.delUTie_of_exists Y hY hK

def withTrivial (Y : NExp D.R D.host D.what₂ D.LL0 N X) : NExp D.R D.host D.what₂ D.LL0 N X :=
  { Y with
    delU := fun _ _ _ => 1
    delU_unr := fun _ _ _ _ _ _ _ _ _ => rfl
    delU_l := fun _ _ _ _ _ _ _ _ _ => rfl
    delU_anti := fun _ _ _ _ _ _ => inv_one.symm
    delU_open := fun _ _ _ => by rw [MonoidHom.ker_one]; exact isOpen_univ
    delU_res := fun _ _ _ _ _ _ _ _ _ _ => rfl
    delU_conj := fun _ _ _ _ _ _ _ _ => ⟨1, fun _ => (mul_zero _).symm⟩ }

end GlobalTheory.UnivChar

end
