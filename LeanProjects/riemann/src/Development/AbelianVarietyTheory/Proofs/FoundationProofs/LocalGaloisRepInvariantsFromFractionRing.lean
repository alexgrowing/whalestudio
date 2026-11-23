import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerRankVanishing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.LengthValuationTwists

namespace GlobalTheory.BKDimNoInv

section Bridge

open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

theorem rep_apply {m : ℕ} (r : ↥Gw →* GL (Fin m) O) (g : ↥(GK Bw.Kw)) (x : Fin m → ↥Bw.LL.1) :
    Bw.rep r g x = (((r (Bw.e.symm g) : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map Bw.toLL).mulVec x :=
  rfl

theorem toLL_injective : Function.Injective Bw.toLL :=
  Subtype.val_injective.comp Bw.eO.injective

theorem toLL_continuous : Continuous Bw.toLL :=
  continuous_subtype_val.comp Bw.eO_cont

theorem rep_continuous {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O))
    (x : Fin m → ↥Bw.LL.1) : Continuous fun g => Bw.rep r g x := by
  haveI : IsTopologicalRing ↥Bw.LL.1 := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1.2.2.2.1
  simp only [rep_apply]
  exact ((hr.comp Bw.e_symm_cont).matrix_map (toLL_continuous Bw)).matrix_mulVec continuous_const

theorem localGaloisRep_invariants_from_fractionRing [IsDomain O] {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (h : ∀ x : Fin m → FractionRing O, (∀ g : ↥Gw,
      (((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map (algebraMap O (FractionRing O))).mulVec x = x) →
        x = 0) : H0V (Bw.rep r) = ⊥ := by
  obtain ⟨_, -, hfr⟩ := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1.1
  let φ : FractionRing O →+* ↥Bw.LL.1 := IsFractionRing.lift (g := Bw.toLL) (toLL_injective Bw)
  have hφ : ∀ a, φ (algebraMap O _ a) = Bw.toLL a := fun a => IsFractionRing.lift_algebraMap _ a
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨n, d, -, rfl⟩ := IsFractionRing.div_surjective (A := ↥(OL Bw.LL)) y
    refine ⟨algebraMap O _ (Bw.eO.symm n) / algebraMap O _ (Bw.eO.symm d), ?_⟩
    rw [map_div₀, hφ, hφ]
    simp [LocBridge.toLL]
  rw [eq_bot_iff]
  intro x hx
  choose x₀ hx₀ using fun a => hsurj (x a)
  have h0 : x₀ = 0 := by
    refine h x₀ fun g => ?_
    have h1 : Bw.rep r (Bw.e g) x = x := by
      have := (Submodule.mem_iInf _).1 hx (Bw.e g)
      rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    rw [rep_apply, MulEquiv.symm_apply_apply] at h1
    funext a
    apply φ.injective
    rw [hx₀, ← congrFun h1 a]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hφ, hx₀]
  rw [Submodule.mem_bot]
  funext a
  rw [← hx₀, h0]
  exact map_zero φ

noncomputable def grepOf {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O)) :
    GRep ↥(GK Bw.Kw) ℚ_[l] ↥Bw.LL.1 ↥(OL Bw.LL) :=
  haveI : IsTopologicalRing ↥Bw.LL.1 := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1.2.2.2.1
  { V := Fin m → ↥Bw.LL.1
    acg := inferInstance
    modLL := inferInstance
    modQp := inferInstance
    towQp := inferInstance
    modO := inferInstance
    towO := inferInstance
    fd := inferInstance
    top := inferInstance
    mtop := inferInstance
    cadd := inferInstance
    csmul := inferInstance
    ρ := Bw.rep r
    cont := rep_continuous Bw r hr }

set_option maxHeartbeats 1000000 in

theorem finrank_h1f_no_invariants [IsDomain O] (P : LocPrime l) {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O))
    (hBK : Formalism.MainNotions.LocalSituation.bkADim (P.PD Bw.Kw)) (hdR : Bw.IsdRW P r)
    (h : ∀ x : Fin m → FractionRing O, (∀ g : ↥Gw,
      (((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map (algebraMap O (FractionRing O))).mulVec x = x) →
        x = 0) :
    (Module.finrank ↥Bw.LL.1 (FiniteCohomology (P.PD Bw.Kw) (Bw.rep r)) : ℤ) =
      (Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r)) : ℤ) -
        Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r) ⊓
          FilV (P.PD Bw.Kw) (LL := ↥Bw.LL.1) (V := Fin m → ↥Bw.LL.1) 0) := by
  have hG := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1
  let A := grepOf Bw r hr
  have hA : IsDR (P.PD Bw.Kw) A.ρ := by
    change Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r)) =
      Module.finrank ℚ_[l] ↥Bw.Kw.1 * Module.finrank ↥Bw.LL.1 (Fin m → ↥Bw.LL.1)
    rw [Module.finrank_fin_fun]
    exact hdR
  have key := hBK _ _ hG A hA
  have h0 : Module.finrank ↥Bw.LL.1 ↥(H0V A.ρ) = 0 := by
    have : H0V A.ρ = ⊥ := localGaloisRep_invariants_from_fractionRing Bw r h
    rw [this, finrank_bot]
  rw [h0, Nat.cast_zero, zero_add] at key
  exact key

end Bridge

end GlobalTheory.BKDimNoInv
