import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalToGlobal.UnitaryNorms.CharHost
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.HeckeGal

namespace GlobalTheory.GalChar

theorem isTorsionFree_field (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] : Module.IsTorsionFree E Ω := inferInstance

attribute [local instance 10000] isTorsionFree_field

section Avatar

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
  {O : Type} [CommRing O] [IsDomain O]

def toQ (κ : FractionRing O →+* Qbar l) : O →+* Qbar l := κ.comp (algebraMap O (FractionRing O))

def inQ (κ : FractionRing O →+* Qbar l) (r : G E Ω →* Oˣ) : G E Ω →* (Qbar l)ˣ :=
  (Units.map (toQ κ).toMonoidHom).comp r

def IsGal [TopologicalSpace O] (art : Ideles E →* Gab E Ω) (κ : FractionRing O →+* Qbar l) (ι : Qbar l ≃+* ℂ)
    (χ : HChar E) (n : (E →+* ℂ) → ℤ) (r : G E Ω →* Oˣ) : Prop :=
  IsAlgPos χ n ∧ Continuous (fun g => ((r g : Oˣ) : O)) ∧ IsLAdicOf art ι χ n (inQ κ r)

def sideIso (ι : Qbar l ≃+* ℂ) (b : Bool) : Qbar l ≃+* ℂ :=
  if b then ι else ι.trans (starRingAut : ℂ ≃+* ℂ)

def block (μ η : HChar E) (r : ℕ) : HChar E := μ * (η⁻¹ * Model.absPow E (-(r : ℝ) / 2))

end Avatar

section Universal

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) {Ω : Type} [Field Ω] [Algebra H.E Ω]

def delAt {e : Fin R.m → R.Psi → ℚ} (C : GlobalTheory.Mem.Chr.HFrame H e) (l : ℕ) : HChar H.E :=
  if l = H.pde then C.del' else C.del

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  let φ : H.E →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  have h := fun y => H.conjE_apply φ y
  exact (h _).trans ((congrArg (starRingEnd ℂ) (h x)).trans (Complex.conj_conj _))

def pair (P : PlE H) : Set (PlE H) := {v | v = P ∨ IsConjPl H P v}

variable {H}

theorem isConjPl_symm {P P' : PlE H} (h : IsConjPl H P P') : IsConjPl H P' P := fun x y e =>
  (h y x (by rw [e, conj_conj])).symm

theorem isConjPl_unique {P P' P'' : PlE H} (h : IsConjPl H P P') (h' : IsConjPl H P P'') : P' = P'' :=
  (GlobalTheory.Mem.Chr.existsUnique_conjPl H.conj.toRingEquiv P).unique
    ((GlobalTheory.Mem.Chr.conjPl_main.2.1 R H P P').1 h) ((GlobalTheory.Mem.Chr.conjPl_main.2.1 R H P P'').1 h')

theorem pair_eq {P P' : PlE H} (h : IsConjPl H P P') : pair H P' = pair H P := by
  ext v
  constructor
  · rintro (rfl | hv)
    · exact Or.inr h
    · exact Or.inl (isConjPl_unique hv (isConjPl_symm h))
  · rintro (rfl | hv)
    · exact Or.inr (isConjPl_symm h)
    · exact Or.inl (isConjPl_unique hv h)

variable (H) (cc : Ω ≃+* Ω) (l : ℕ)

def IsDel (M : ℕ) (T : Set (PlE H)) (d : G H.E Ω →* Multiplicative (ZMod (l ^ M))) : Prop :=
  IsOpen (d.ker : Set (G H.E Ω)) ∧ AntiHom cc d ∧
    (∀ v ∈ placesOver H.E l, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Dec (F := H.E) A, d σ = 1) ∧
    (∀ v, v ∉ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, d σ = 1) ∧
    (∀ v, v ∈ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ c, ∃ σ ∈ Ine (F := H.E) A, d σ = c)

open Classical in

def delOf (M : ℕ) (T : Set (PlE H)) : G H.E Ω →* Multiplicative (ZMod (l ^ M)) :=
  if h : ∃ d, IsDel H cc l M T d then h.choose else 1

theorem isDel_delOf {M : ℕ} {T : Set (PlE H)} (h : ∃ d, IsDel H cc l M T d) : IsDel H cc l M T (delOf H cc l M T) := by
  rw [delOf, dif_pos h]
  exact h.choose_spec

theorem delOf_laws (M : ℕ) (T : Set (PlE H)) :
    IsOpen ((delOf H cc l M T).ker : Set (G H.E Ω)) ∧ AntiHom cc (delOf H cc l M T) ∧
    (∀ v ∈ placesOver H.E l, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Dec (F := H.E) A,
      delOf H cc l M T σ = 1) ∧
    (∀ v, v ∉ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, delOf H cc l M T σ = 1) := by
  by_cases h : ∃ d, IsDel H cc l M T d
  · obtain ⟨h1, h2, h3, h4, -⟩ := isDel_delOf H cc l h
    exact ⟨h1, h2, h3, h4⟩
  · rw [delOf, dif_neg h]
    refine ⟨by simp, fun _ _ _ => by simp, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

open Classical in

def delCoord (Q : Finset (PlE H)) (M : ℕ) (P : PlE H) : G H.E Ω →* Multiplicative (ZMod (l ^ M)) :=
  if pair H P ⊆ ↑Q then delOf H cc l M (pair H P) else 1

def delU (Q : Finset (PlE H)) (M : ℕ) : G H.E Ω →* Multiplicative (DelQM H l Q M) where
  toFun σ := Multiplicative.ofAdd fun P => Multiplicative.toAdd (delCoord H cc l Q M P.1 σ)
  map_one' := by simp only [map_one, toAdd_one]; rfl
  map_mul' g h := by simp only [map_mul, toAdd_mul]; rfl

theorem delU_apply (Q : Finset (PlE H)) (M : ℕ) (σ : G H.E Ω) (P : ↥Q) :
    Multiplicative.toAdd (delU H cc l Q M σ) P = Multiplicative.toAdd (delCoord H cc l Q M P.1 σ) := rfl

theorem delU_eq_one_iff (Q : Finset (PlE H)) (M : ℕ) (σ : G H.E Ω) :
    delU H cc l Q M σ = 1 ↔ ∀ P ∈ Q, delCoord H cc l Q M P σ = 1 :=
  ⟨fun h P hP => Multiplicative.toAdd.injective (congrFun (congrArg Multiplicative.toAdd h) ⟨P, hP⟩),
    fun h => Multiplicative.toAdd.injective (funext fun P => congrArg Multiplicative.toAdd (h P.1 P.2))⟩

theorem delCoord_laws (Q : Finset (PlE H)) (M : ℕ) (P : PlE H) :
    IsOpen ((delCoord H cc l Q M P).ker : Set (G H.E Ω)) ∧ AntiHom cc (delCoord H cc l Q M P) ∧
    (∀ v ∈ placesOver H.E l, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Dec (F := H.E) A,
      delCoord H cc l Q M P σ = 1) ∧
    (∀ v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A,
      delCoord H cc l Q M P σ = 1) := by
  unfold delCoord
  split_ifs with h
  · obtain ⟨h1, h2, h3, h4⟩ := delOf_laws H cc l M (pair H P)
    exact ⟨h1, h2, h3, fun v hv => h4 v fun hm => hv (h hm)⟩
  · refine ⟨by simp, fun _ _ _ => by simp, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

theorem delCoord_of_closed {Q : Finset (PlE H)} (hQ : ∀ P ∈ Q, ∀ P', IsConjPl H P P' → P' ∈ Q) (M : ℕ) {P : PlE H}
    (hP : P ∈ Q) : delCoord H cc l Q M P = delOf H cc l M (pair H P) := by
  refine if_pos ?_
  rintro v (rfl | hv)
  · exact hP
  · exact hQ P hP v hv

def UniversalAnticyclotomicCharLaws : Prop :=
  (∀ Q M v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, delU H cc l Q M σ = 1) ∧
  (∀ Q M v, v ∈ placesOver H.E l → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
    ∀ σ ∈ Dec (F := H.E) A, delU H cc l Q M σ = 1) ∧
  (∀ Q M, AntiHom cc (delU H cc l Q M)) ∧
  (∀ (Q : Finset (PlE H)) (M : ℕ), IsOpen ((delU H cc l Q M).ker : Set (G H.E Ω))) ∧
  (∀ (M : ℕ) (Q' Q : Finset (PlE H)) (h : Q' ⊆ Q),
    (∀ P ∈ Q', ∀ P', IsConjPl H P P' → P' ∈ Q') → (∀ P ∈ Q, ∀ P', IsConjPl H P P' → P' ∈ Q) →
    ∀ (σ : G H.E Ω) (P : PlE H) (hP : P ∈ Q'),
      Multiplicative.toAdd (delU H cc l Q' M σ) ⟨P, hP⟩ = Multiplicative.toAdd (delU H cc l Q M σ) ⟨P, h hP⟩) ∧
  (∀ (Q : Finset (PlE H)) (M : ℕ) (P : PlE H) (hP : P ∈ Q) (P' : PlE H) (hP' : P' ∈ Q),
    IsConjPl H P P' → ∃ s : ℤˣ, ∀ σ : G H.E Ω,
      Multiplicative.toAdd (delU H cc l Q M σ) ⟨P', hP'⟩ =
        ((s : ℤ) : ZMod (l ^ M)) * Multiplicative.toAdd (delU H cc l Q M σ) ⟨P, hP⟩) ∧
  (∀ (Q : Finset (PlE H)) (M : ℕ), (∀ P ∈ Q, ∀ P', IsConjPl H P P' → P' ∈ Q) → ∀ (P : PlE H) (hP : P ∈ Q) (σ : G H.E Ω),
    Multiplicative.toAdd (delU H cc l Q M σ) ⟨P, hP⟩ = Multiplicative.toAdd (delOf H cc l M (pair H P) σ)) ∧
  ∀ (M : ℕ) (P : PlE H), (∃ d, IsDel H cc l M (pair H P) d) → IsDel H cc l M (pair H P) (delOf H cc l M (pair H P))

theorem universal_anticyclotomic_character_laws : UniversalAnticyclotomicCharLaws H cc l := by
  refine ⟨fun Q M v hv A hA σ hσ => ?_, fun Q M v hv A hA σ hσ => ?_, fun Q M g g' h => ?_, fun Q M => ?_,
    fun M Q' Q h h1 h2 σ P hP => ?_, fun Q M P hP P' hP' h => ⟨1, fun σ => ?_⟩, fun Q M hQ P hP σ => ?_,
    fun M P h => isDel_delOf H cc l h⟩
  · exact (delU_eq_one_iff H cc l Q M σ).2 fun P _ => (delCoord_laws H cc l Q M P).2.2.2 v hv A hA σ hσ
  · exact (delU_eq_one_iff H cc l Q M σ).2 fun P _ => (delCoord_laws H cc l Q M P).2.2.1 v hv A hA σ hσ
  · exact Multiplicative.toAdd.injective (funext fun P =>
      congrArg Multiplicative.toAdd ((delCoord_laws H cc l Q M P.1).2.1 g g' h))
  · have e : ((delU H cc l Q M).ker : Set (G H.E Ω)) = ⋂ P ∈ Q, ((delCoord H cc l Q M P).ker : Set (G H.E Ω)) := by
      ext σ
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, delU_eq_one_iff]
    rw [e]
    exact isOpen_biInter_finset fun P _ => (delCoord_laws H cc l Q M P).1
  · rw [delU_apply, delU_apply, delCoord_of_closed H cc l h1 M hP, delCoord_of_closed H cc l h2 M (h hP)]
  · rw [delU_apply, delU_apply]
    have e : delCoord H cc l Q M P' = delCoord H cc l Q M P := by
      unfold delCoord
      rw [pair_eq h]
    simp only [e, Units.val_one, Int.cast_one, one_mul]
  · rw [delU_apply, delCoord_of_closed H cc l hQ M hP]

end Universal

theorem delUTie_of_exists {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
    (Y : NExp D.R D.host D.what₂ D.LL0 N X) (hY : ∀ i Q M, Y.delU i Q M = delU D.host X.cc (X.l i) Q M)
    (h : GlobalTheory.TwSys.K1 X) : GlobalTheory.TwSys.DelUTie Y := by
  intro i M _ hM
  obtain ⟨H', S, d, h1, h2, h3, h4⟩ := h i M hM
  refine ⟨H', S, fun P => delOf D.host X.cc (X.l i) M (pair D.host P), ⟨h1, h2, h3, fun P a b c => ?_⟩,
    fun Q hQ P hP σ => ?_⟩
  · exact isDel_delOf D.host X.cc (X.l i) ⟨d P, h4 P a b c⟩
  · rw [hY]
    exact (universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.2.2.2.1 Q M hQ P hP σ

end GlobalTheory.GalChar

end
