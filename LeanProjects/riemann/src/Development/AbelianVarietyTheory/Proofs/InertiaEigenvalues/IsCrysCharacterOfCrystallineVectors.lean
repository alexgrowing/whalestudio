import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBoundsCrystallineDeRhamConcreteRings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFrobeniusBijOnLettersDirectSum
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.LetterCrys

theorem isCrys_of_letters : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → ∀ d : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ, (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)), ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ) ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ + 1)) → IsCrys (P.PD K) (charRep μ) := by
  intro l _ P AI hT K LL hA μ hμ d hw
  haveI := LL.2
  haveI := K.2
  obtain ⟨hgood, -⟩ := GlobalTheory.LocalIntegers.good_integers l LL
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := ↥LL.1
      ρ := charRep μ
      cont := fun x => (hμ.mul continuous_const :
        Continuous fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1) * x) }
  obtain ⟨⟨hfin, hle⟩, -, -⟩ :=
    GlobalTheory.Per.FontaineTied.fontCore_all_of_tied l P AI hT K ↥LL.1 ↥(OL LL) hgood A
  haveI : Module.Finite ↥LL.1 ↥(Dcris (P.PD K) (charRep μ)) := hfin
  unfold IsCrys
  refine le_antisymm hle ?_
  have hcard : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 :=
    Formalism.MainNotions.N.JsetEmb.card_emb_good hA.2.2
  have e : K0 K = K.1 := inf_eq_left.2 hA.1
  have hfr : finrank ℚ_[l] ↥(K0 K) = finrank ℚ_[l] ↥K.1 :=
    (IntermediateField.equivOfEq e).toLinearEquiv.finrank_eq
  have hsurj : Function.Surjective (algebraMap ↥(K0 K) ↥K.1) := fun x =>
    ⟨⟨x, x.2, hA.1 x.2⟩, rfl⟩
  let f : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) := fun τ =>
    τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)
  have hf : Function.Injective f := fun τ τ' h => AlgHom.ext fun x => by
    obtain ⟨y, rfl⟩ := hsurj x
    exact AlgHom.congr_fun h y
  choose w hwmem hw1 hw2 using hw
  have hne : ∀ τ, w τ ≠ 0 := fun τ h0 => hw2 τ (by rw [h0, map_zero]; exact Submodule.zero_mem _)
  have hind : iSupIndep fun τ => DcrisL (P.PD K) (charRep μ) (f τ) :=
    (GlobalTheory.NL.PhiD.iSupIndep_letter (P.PD K) (charRep μ)).comp hf
  have hli : LinearIndependent ↥LL.1 w := iSupIndep.linearIndependent _ hind hwmem hne
  let w' : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ↥(Dcris (P.PD K) (charRep μ)) := fun τ => ⟨w τ, (hwmem τ).1⟩
  have hli' : LinearIndependent ↥LL.1 w' :=
    LinearIndependent.of_comp (Dcris (P.PD K) (charRep μ)).subtype hli
  have hpos : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) ≠ 0 := by
    rw [hcard]; exact Module.finrank_pos.ne'
  haveI : Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Nat.finite_of_card_ne_zero hpos
  haveI := Fintype.ofFinite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
  have h2 := hli'.fintype_card_le_finrank
  rw [← Nat.card_eq_fintype_card, hcard] at h2
  rw [Module.finrank_self, mul_one, hfr]
  exact h2

end GlobalTheory.LetterCrys
