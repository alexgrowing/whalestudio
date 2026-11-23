import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLeOneIffOfContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SatakeEigenvalueInvNormalisedEqEsymmStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAdicCompletionEquivUniformiserStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitHeckeOperatorInverseConjugatePlaceCosetSumStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HeckeEigConj
open GlobalTheory.HeckeEigConj

theorem tN_eig : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ J : Subgroup (GAf L n),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) →
    ∀ (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L))) (α : Fin n → ℂˣ),
    GlobalTheory.SmGL.HasSatake σ.ρ α →
    ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L), Continuous i →
    (∀ x : L, i ((GlobalTheory.HeckeFrob.conjSplit s).i x) = algebraMap L ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) x) →
    ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (T : σ.V →ₗ[ℂ] (GAf L n → W)),
    GlobalTheory.HeckeFrob.IsLocMap (GlobalTheory.HeckeFrob.conjSplit s) σ i T →
    ∀ e ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KO ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) (Fin n)),
    ∀ k, 1 ≤ k → k ≤ n →
      ((normV (GlobalTheory.HeckeFrob.conjSplit s).w : ℕ) : ℂ) ^ (k * (k - 1) / 2) • NG.tN J s ϖ k (T e) =
        (GlobalTheory.HeckeFrob.twEig (GlobalTheory.HeckeFrob.conjSplit s).w α).esymm k • T e := by
  intro L _ _ _ n s ϖ hϖ J hJ σ α hα i hi hiL W _ _ T hT e he k hk1 hkn
  classical
  have hK : ∀ a, i a ∈ Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w ↔
      a ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun a =>
    GlobalTheory.IsoInteg.valued_le_one_iff_of_continuous (maximalRealSubfield L) L s.v _ i hi a
  have heK : e ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n) := by
    rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL L (GlobalTheory.HeckeFrob.conjSplit s).w n]; exact he
  have hφK : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ →
      Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n κ) ∈
        GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n := fun κ hκ ht => by
    rw [GlobalTheory.HeckeEigConj.map_loc_conjSplit L n s i κ]
    exact (GlobalTheory.LFun.ConjPlace.mem_iff_invT i hK _).1 ((GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s ht).2 hκ)
  obtain ⟨α0, -, hT0⟩ := GlobalTheory.HeckeScalarSph.exists_tSet_eq (n := n) s ϖ k hϖ
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.HeckeScalarSph.exists_repsU (n := n) s.v α0
  have hR1' : ∀ γ ∈ R, γ ∈ tSet L n s ϖ k := fun γ hγ => (hT0 γ).2 (hR1 γ hγ)
  have hR2' : ∀ x ∈ tSet L n s ϖ k, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n := fun x hx => hR2 x ((hT0 x).1 hx)
  have hD : ∀ x ∈ tSet L n s ϖ k, TrivOutside {s.v} x := fun x hx => hx.1
  have hrt : ∀ x, TrivOutside {s.v} x → NG.rt L n x (T e) =
      T (σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n x)) e) :=
    fun x hx => (hT x hx e).symm
  have hfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ (T e) = T e := fun κ hκ ht => by
    rw [hrt κ ht, GlobalTheory.LGrp.mem_fixed.1 heK _ (hφK κ hκ ht)]
  have hsum := heckeD_eq_sum_of_agree J hJ hD hR1' hR2' hfix
  have hloc := GlobalTheory.T.splitHeckeOperator_inverse_conjugatePlace_cosetSum L n s ϖ hϖ k hkn i hi σ.ρ R hR1' hR2' e heK
  have key : NG.heckeD J (tSet L n s ϖ k) (T e) = T (GlobalTheory.LFun.heckeVec σ.ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n)
      (fun g => Formalism.UG.Tj ℂ n (Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w) (i ϖ) k g⁻¹) e) := by
    rw [hsum, hloc, map_sum]
    exact Finset.sum_congr rfl fun γ hγ => hrt γ (hD γ (hR1' γ hγ))
  obtain ⟨hq1, hq2⟩ := norms_eq s
  by_cases he0 : e = 0
  · subst he0
    simp only [map_zero, smul_zero]
    funext g
    simp [NG.tN, NG.heckeD]
  have hSat := (GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake L (GlobalTheory.HeckeFrob.conjSplit s).w n σ.V σ.ρ α hα).2 e heK he0
  have hU : Formalism.UG.IsUnifV L (GlobalTheory.HeckeFrob.conjSplit s).w (i ϖ) :=
    GlobalTheory.T.continuous_adicCompletion_equiv_uniformiser (maximalRealSubfield L) L s.v _ i hi ϖ hϖ
  have hinv := (GlobalTheory.ChainOnto.SatInv.satVec_iff_inv L (GlobalTheory.HeckeFrob.conjSplit s).w n σ.V σ.ρ e _ he0 heK
    (by simp)).1 hSat (i ϖ) hU k hkn
  rw [NG.tN, key, hinv, map_smul, smul_smul, smul_smul, hq1, hq2]
  congr 1
  rw [mul_assoc]
  exact GlobalTheory.T.satakeEigenvalue_inv_normalised_eq_esymm (normV (GlobalTheory.HeckeFrob.conjSplit s).w) n k
    (Nat.pos_of_ne_zero (hq1 ▸ GlobalTheory.LFun.qV_ne_zero (GlobalTheory.HeckeFrob.conjSplit s).w)) hkn α

end GlobalTheory.HeckeEigConj

end
