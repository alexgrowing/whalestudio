import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
  GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step.Maps

section Pull

variable {X : Scheme.{0}} {P : X.Modules}

lemma le_pullback_of_factors {Y T : Subobject P} (φ : P ⟶ P) (h : T.Factors (Y.arrow ≫ φ)) :
    Y ≤ (Subobject.pullback φ).obj T := by
  rw [Subobject.pullback_obj]
  exact Subobject.le_mk_of_comm
    (pullback.lift (T.factorThru (Y.arrow ≫ φ) h) Y.arrow (Subobject.factorThru_arrow _ _ _))
    (pullback.lift_snd _ _ _)

lemma factors_of_le_pullback {Y T : Subobject P} (φ : P ⟶ P)
    (h : Y ≤ (Subobject.pullback φ).obj T) : T.Factors (Y.arrow ≫ φ) := by
  rw [Subobject.pullback_obj] at h
  have e : Y.arrow ≫ φ = (Y.ofLE _ h ≫ (Subobject.underlyingIso (pullback.snd T.arrow φ)).hom ≫
      pullback.fst T.arrow φ) ≫ T.arrow := by
    rw [← Subobject.ofLE_arrow h, ← Subobject.underlyingIso_hom_comp_eq_mk]
    simp only [Category.assoc, pullback.condition]
  rw [e]
  exact Subobject.factors_comp_arrow _

lemma restrictTop_whole (r : Γ(X, ⊤)) : restrictTop (X := X) ⊤ r = r := by
  unfold GroundTheory.Arith.SchemeCoh.restrictTop
  simp

end Pull

section Mul

attribute [local instance] algebraOfOver

variable {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
  [X.Over (Spec (.of A))]

lemma exists_smulHom_eq (P : X.Modules) {a : A} (ha : a ∈ I ^ 1) :
    ∃ m : P ⟶ idealPow I P 1, m ≫ idealPowι I P 1 = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
  rw [← span_idealGen (I ^ 1)] at ha
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp ha
  have ht : (∑ i, GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) (c i)) ≫
      biproduct.ι (fun _ : Fin (idealGenNum (I ^ 1)) => P) i) ≫ idealSumMap P (I ^ 1) =
      GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
    unfold idealSumMap
    rw [Preadditive.sum_comp]
    simp only [Category.assoc, biproduct.ι_desc, smulHom_comp_smulHom]
    rw [← smulHom_sum, ← hc, map_sum]
    simp only [smul_eq_mul, map_mul]
  refine ⟨kernel.lift _ (GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a)) ?_, ?_⟩
  · rw [← ht, Category.assoc, cokernel.condition, comp_zero]
  · exact kernel.lift_ι _ _ _

lemma factors_powSub (P : X.Modules) (n : ℕ) {a : A} (ha : a ∈ I ^ 1) :
    (powSub I P (n + 1)).Factors ((powSub I P n).arrow ≫ GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a)) := by
  show (Subobject.mk (idealPowι I P (n + 1))).Factors _
  rw [Subobject.mk_factors_iff]
  refine ⟨(Subobject.underlyingIso (idealPowι I P n)).hom ≫ idealPowMul I P (n := n) a ha, ?_⟩
  show ((Subobject.underlyingIso (idealPowι I P n)).hom ≫ idealPowMul I P (n := n) a ha) ≫
    idealPowι I P (n + 1) = _
  rw [Category.assoc, idealPowMul_ι, ← Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]
  rfl

theorem mapsDown_toFunctions {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules} (_ : P.IsQuasicoherent)
    (S : ℕ → Subobject P) (hS : ClosedSys I P S) (a : A) (ha : a ∈ I) :
    MapsDown S (toFunctions (X := X) (A := A) ⊤ a) := by
  have ha1 : a ∈ I ^ 1 := by rwa [pow_one]
  have hr : toFunctions (X := X) (A := A) ⊤ a = algebraMap A Γ(X, ⊤) a := by
    simp only [GroundTheory.Arith.SchemeCoh.toFunctions, RingHom.comp_apply]
    exact restrictTop_whole _
  rw [hr]
  intro e
  cases e with
  | zero =>
    show (S 0).Factors ((⊤ : Subobject P).arrow ≫ GroundTheory.Arith.SchemeCoh.smulHom P _)
    apply Subobject.factors_of_le _ (hS.pow_le 0)
    obtain ⟨m, hm⟩ := exists_smulHom_eq I P ha1
    show (Subobject.mk (idealPowι I P 1)).Factors _
    rw [Subobject.mk_factors_iff]
    refine ⟨(⊤ : Subobject P).arrow ≫ m, ?_⟩
    show ((⊤ : Subobject P).arrow ≫ m) ≫ idealPowι I P 1 = _
    rw [Category.assoc, hm]
  | succ e =>
    show (S (e + 1)).Factors ((S e).arrow ≫ GroundTheory.Arith.SchemeCoh.smulHom P _)
    apply factors_of_le_pullback
    rw [hS.succ e]
    apply sup_le
    · apply le_pullback_of_factors
      rw [← GroundTheory.Arith.SchemeCoh.smulHom_comp]
      exact Subobject.factors_comp_arrow _
    · apply le_pullback_of_factors
      apply Subobject.factors_of_le _ (hS.pow_le (e + 1))
      exact factors_powSub I P (e + 1) ha1

end Mul

end GlobalTheory.CompanionTheory.GE.Step.Maps
