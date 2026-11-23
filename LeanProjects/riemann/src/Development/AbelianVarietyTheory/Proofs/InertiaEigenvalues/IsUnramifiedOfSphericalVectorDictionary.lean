import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitaryFinitePointsToGLFiniteAdelesIsUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryAutFormEqZeroOfFinitePoints
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.UnramDict

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => maximalRealSubfield L

theorem kappa_tmul (F : FinIso L n) (x : L) (a : AFplus L) :
    F.κ.toRingHom (x ⊗ₜ[L⁺] a) = algebraMap L _ x * GlobalTheory.AdeleBaseChange.adMap L⁺ L a := by
  rw [Model.kappa_eq F (Model.finIso L n)]
  exact (Model.kappa_tmul L x a).trans (mul_comm _ _)

theorem mem_ALint (F : FinIso L n) (z : AL L) (hz : ∀ u, F.κ z u ∈ u.adicCompletionIntegers L) : z ∈ ALint L := by
  have h := GlobalTheory.AdeleBaseChange.mem_int_of_map (ι := F.κ.toRingHom) (kappa_tmul F) (y := z) hz
  refine (Subring.closure_le.2 ?_ : _ ≤ ALint L) h
  rintro x (⟨⟨e, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
  · exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
  · exact Subring.subset_closure (Or.inr ⟨y, hy, rfl⟩)

theorem compAt_eq_zero (F : FinIso L n) (v : HeightOneSpectrum (𝓞 L⁺)) (z : AL L)
    (hz : ∀ u : HeightOneSpectrum (𝓞 L), u.under (𝓞 L⁺) = v → F.κ z u = 0) : compAt L v z = 0 :=
  (GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (ι := F.κ.toRingHom) (kappa_tmul F) v z).2 hz

omit [IsCMField L] in

theorem entry_mem {w : HeightOneSpectrum (𝓞 L)} {g : GL (Fin n) (w.adicCompletion L)} (hg : g ∈ GlobalTheory.LFun.KGL w n)
    (i j : Fin n) : g.val i j ∈ w.adicCompletionIntegers L := by
  obtain ⟨Q, rfl⟩ := hg
  exact (Q.val i j).2

theorem cLoc_entry_mem {w : HeightOneSpectrum (𝓞 L)} {x : UA L n} (hx : x ∈ locU n w) (hK : cLoc w x ∈ GlobalTheory.LFun.KGL w n)
    (u : HeightOneSpectrum (𝓞 L)) (i j : Fin n) : (cLoc u x).val i j ∈ u.adicCompletionIntegers L := by
  by_cases hu : u.under (𝓞 L⁺) = w.under (𝓞 L⁺)
  · rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj L)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one L) w u).1 hu with rfl | h
    · exact entry_mem hK i j
    · obtain rfl : u = conjSrc (GlobalTheory.SplitPts.conjE L) w := by
        rw [eq_conjSrc h, GlobalTheory.SplitPts.conjSrc_conjSrc_cm]
      have h1 := Units.inv_eq_of_mul_eq_one_left (GlobalTheory.SplitPts.comp_eq x w)
      have h2 := entry_mem (inv_mem hK) j i
      rw [h1] at h2
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h2 ⊢
      rw [← (conjLoc_spec (GlobalTheory.SplitPts.conjE L) w).2.2]
      exact h2
  · have h := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) hu)
    rw [h, Units.val_one, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem trivOutside (F : FinIso L n) {w : HeightOneSpectrum (𝓞 L)} {y : GAf L n} (hy : F.j y ∈ locU n w) :
    TrivOutside {w.under (𝓞 L⁺)} y := by
  intro v hv
  refine Matrix.ext fun i j => ?_
  have h0 := compAt_eq_zero F v (y.1.val i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) fun u hu => by
    have h := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hy).2 u)
      (fun e => hv (hu.symm.trans e)))
    have h1 := F.loc y u i j
    rw [h] at h1
    rw [map_sub]
    change F.κ _ u - F.κ _ u = 0
    rw [← h1]
    simp only [Units.val_one, Matrix.one_apply]
    split_ifs <;> simp
  rw [map_sub, sub_eq_zero] at h0
  rw [Matrix.map_apply, h0]
  simp only [Matrix.one_apply]
  split_ifs <;> simp

theorem isUnramU_of_sphAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → IsUnramU U w := by
  intro L _ _ _ n F π U hD v w hw hs
  obtain rfl : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hw
  obtain ⟨f, hfS, hf0, hfix⟩ := hs
  obtain ⟨g0, hg0⟩ : ∃ g0, f g0 ≠ 0 := Function.ne_iff.1 hf0
  obtain ⟨lam, hlam⟩ : ∃ lam : Module.Dual ℂ π.W, lam (f g0) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hg0 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  have hmem : (fun x => lam (f x)) ∈ U.map (LinearMap.funLeft ℂ ℂ F.j) := by
    rw [hD.2]
    exact Submodule.subset_span ⟨f, hfS, lam, rfl⟩
  obtain ⟨φ, hφU, hφ⟩ := hmem
  have hφ' : ∀ g, φ (F.j g) = lam (f g) := fun g => congrFun hφ g
  refine ⟨φ, hφU, fun h => hlam ?_, fun x hx hK => ?_⟩
  · rw [← hφ', h]; rfl
  obtain ⟨y, rfl⟩ := F.onto x (Subgroup.mem_inf.1 hx).1
  have hyU : y ∈ Umax L n := fun i j => mem_ALint F _ fun u => by
    rw [← F.loc]
    exact cLoc_entry_mem hx hK u i j
  have hy := hfix y hyU (trivOutside F hx)
  rw [← sub_eq_zero]
  refine GlobalTheory.DefiniteDense.eq_zero_of_finU L n _ (hD.1.aut _ (U.sub_mem (hD.1.stable _ _ hφU) hφU)) fun z hz => ?_
  obtain ⟨g, rfl⟩ := F.onto z hz
  change φ (F.j g * F.j y) - φ (F.j g) = 0
  rw [← map_mul, hφ', hφ', sub_eq_zero]
  exact congrArg lam (congrFun hy g)

end GlobalTheory.UnramDict

end
