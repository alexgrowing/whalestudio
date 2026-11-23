import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSequenceEtaleTateTwistStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Deg2

abbrev T (q : ℕ) : Shv ℤ := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)

def kap (q : ℕ) [NeZero q] : T q ⟶ Gm := (GlobalTheory.T.kummer_sequence_etale_tateTwist q).choose

theorem kap_spec (q : ℕ) [NeZero q] : Mono (kap q) ∧ kap q ≫ ((q : ℤ) • 𝟙 Gm) = 0 ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map (kap q) (show Sec (T q) U from twGen 1 ζ) = unitSec u) ∧ (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map (kap q) a = b) ∧ ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b :=
  (GlobalTheory.T.kummer_sequence_etale_tateTwist q).choose_spec

def Cq (q : ℕ) [NeZero q] : Shv ℤ := cokernel (kap q)

def piq (q : ℕ) [NeZero q] : Gm ⟶ Cq q := cokernel.π (kap q)

def powq (q : ℕ) [NeZero q] : Cq q ⟶ Gm := cokernel.desc (kap q) ((q : ℤ) • 𝟙 Gm) (kap_spec q).2.1

def kumS (q : ℕ) [NeZero q] : ShortComplex (Shv ℤ) := ShortComplex.mk (kap q) (piq q) (cokernel.condition (kap q))

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [spMap, spMap, spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

section MV
variable (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A)

theorem mvS_zero : biprod.lift ((chains R).map (spMap (Localization.awayMap (algebraMap A A') f)))
      (-(chains R).map (spMap (algebraMap A' (Localization.Away (algebraMap A A' f))))) ≫
    biprod.desc ((chains R).map (spMap (algebraMap A (Localization.Away f))))
      ((chains R).map (spMap (algebraMap A A'))) = 0 := by
  have h : (Localization.awayMap (algebraMap A A') f).comp (algebraMap A (Localization.Away f)) =
      (algebraMap A' (Localization.Away (algebraMap A A' f))).comp (algebraMap A A') :=
    IsLocalization.map_comp _
  have e1 := (chains R).map_comp (spMap (Localization.awayMap (algebraMap A A') f)) (spMap (algebraMap A (Localization.Away f)))
  have e2 := (chains R).map_comp (spMap (algebraMap A' (Localization.Away (algebraMap A A' f)))) (spMap (algebraMap A A'))
  rw [spMap_comp] at e1 e2
  rw [biprod.lift_desc, Preadditive.neg_comp, ← e1, ← e2, h]
  simp

def mvS : ShortComplex (Cx R) := ShortComplex.mk _ _ (mvS_zero R A A' f)

end MV

section Shrink
variable (R : Type) [CommRing R] (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f s : B)

abbrev LS : Type := Localization.Away (algebraMap B A' s)

theorem rho_unit : IsUnit (((algebraMap (LS B A' s) (Localization.Away (algebraMap B (LS B A' s) f))).comp
    (algebraMap A' (LS B A' s))) (algebraMap B A' f)) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap B (LS B A' s) f)) (algebraMap B (LS B A' s) f)
  rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  exact h

def rho : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B (LS B A' s) f) :=
  IsLocalization.Away.lift (algebraMap B A' f)
    (g := (algebraMap (LS B A' s) (Localization.Away (algebraMap B (LS B A' s) f))).comp (algebraMap A' (LS B A' s)))
    (rho_unit B A' f s)

theorem rho_comp : (rho B A' f s).comp (algebraMap A' (Localization.Away (algebraMap B A' f))) =
    (algebraMap (LS B A' s) (Localization.Away (algebraMap B (LS B A' s) f))).comp (algebraMap A' (LS B A' s)) := by
  unfold rho
  exact IsLocalization.Away.lift_comp (algebraMap B A' f) (rho_unit B A' f s)

theorem rho_away : (rho B A' f s).comp (Localization.awayMap (algebraMap B A') f) =
    Localization.awayMap (algebraMap B (LS B A' s)) f := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  have h1 : (Localization.awayMap (algebraMap B A') f).comp (algebraMap B (Localization.Away f)) =
      (algebraMap A' (Localization.Away (algebraMap B A' f))).comp (algebraMap B A') := IsLocalization.map_comp _
  have h2 : (Localization.awayMap (algebraMap B (LS B A' s)) f).comp (algebraMap B (Localization.Away f)) =
      (algebraMap (LS B A' s) (Localization.Away (algebraMap B (LS B A' s) f))).comp (algebraMap B (LS B A' s)) :=
    IsLocalization.map_comp _
  rw [RingHom.comp_assoc, h1, h2, ← RingHom.comp_assoc, rho_comp, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]

def mvMor : mvS R B (LS B A' s) f ⟶ mvS R B A' f where
  τ₁ := (chains R).map (spMap (rho B A' f s))
  τ₂ := biprod.map (𝟙 _) ((chains R).map (spMap (algebraMap A' (LS B A' s))))
  τ₃ := 𝟙 _
  comm₁₂ := by
    have e1 := (chains R).map_comp (spMap (rho B A' f s)) (spMap (Localization.awayMap (algebraMap B A') f))
    have e2 := (chains R).map_comp (spMap (rho B A' f s)) (spMap (algebraMap A' (Localization.Away (algebraMap B A' f))))
    have e3 := (chains R).map_comp (spMap (algebraMap (LS B A' s) (Localization.Away (algebraMap B (LS B A' s) f)))) (spMap (algebraMap A' (LS B A' s)))
    rw [spMap_comp, rho_away] at e1
    rw [spMap_comp, rho_comp] at e2
    rw [spMap_comp] at e3
    apply biprod.hom_ext
    · simp [mvS, e1]
    · simp only [mvS, Category.assoc, biprod.lift_snd, biprod.map_snd, Preadditive.neg_comp, Preadditive.comp_neg, biprod.lift_snd_assoc]
      rw [← e2, e3]
  comm₂₃ := by
    have e1 := (chains R).map_comp (spMap (algebraMap A' (LS B A' s))) (spMap (algebraMap B A'))
    rw [spMap_comp, ← IsScalarTower.algebraMap_eq] at e1
    apply biprod.hom_ext'
    · simp [mvS]
    · simp [mvS, e1]

end Shrink

end UpperTheory.Deg2
