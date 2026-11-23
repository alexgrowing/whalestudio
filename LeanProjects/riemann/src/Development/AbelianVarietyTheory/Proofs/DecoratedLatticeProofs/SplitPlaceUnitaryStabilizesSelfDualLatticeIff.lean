import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmulOfMemFlagSubOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FinPl.FrameLat

theorem moves_iff_smul_eq : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : GlobalTheory.FinPl.SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p S n) (L : GlobalTheory.FinPl.Lat S) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S L → β.IsLat L Λ → ∀ (κ : GA D S) (g : GL n k), (mt S κ).map p.pr = β.b * g.val * β.b' → (GlobalTheory.FinPl.Moves S κ L L (· = p.v) ↔ g • Λ = Λ) := by
  intro D k _ _ _ _ p S n _ _ β L Λ hL hΛ κ g hg
  have hsec : ∀ u : Fin S.rank → k, mt S κ *ᵥ (fun i => p.sec (u i)) =
      fun i => p.sec (((β.b * g.val * β.b') *ᵥ u) i) := by
    intro u
    funext i
    rw [← hg]
    simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, e_mul_sec]
  have key : ∀ x : n → k, mt S κ *ᵥ (fun i => p.sec ((β.b *ᵥ x) i)) =
      fun i => p.sec ((β.b *ᵥ (g.val *ᵥ x)) i) := by
    intro x
    rw [hsec, Matrix.mulVec_mulVec, Matrix.mul_assoc, β.b'b, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  constructor
  · intro hm
    have hiff : ∀ x, x ∈ Λ ↔ g • x ∈ Λ := by
      intro x
      rw [hΛ, hΛ]
      change _ ∈ latV S L _ ↔ (fun i => p.sec ((β.b *ᵥ (g.val *ᵥ x)) i)) ∈ latV S L _
      rw [hm _ (fun i => sec_mem_idAt p _), key]
    ext x
    rw [GlobalTheory.LatPair.mem_smul_iff, hiff, smul_inv_smul]
  · intro hgΛ
    have hinv : ∀ x, g • x ∈ Λ ↔ x ∈ Λ := by
      intro x
      conv_lhs => rw [← hgΛ]
      rw [GlobalTheory.LatPair.mem_smul_iff, inv_smul_smul]
    have hE : ∀ u : Fin S.rank → k, (fun i => p.sec (u i)) ∈ latV S L (· = p.v) ↔
        (fun i => p.sec (((β.b * g.val * β.b') *ᵥ u) i)) ∈ latV S L (· = p.v) := by
      intro u
      have hu : u = β.b *ᵥ (β.b' *ᵥ u) := by rw [Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
      have hAu : (β.b * g.val * β.b') *ᵥ u = β.b *ᵥ (g.val *ᵥ (β.b' *ᵥ u)) := by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      have h := hinv (β.b' *ᵥ u)
      rw [hΛ, hΛ] at h
      change (fun i => p.sec ((β.b *ᵥ (g.val *ᵥ (β.b' *ᵥ u))) i)) ∈ latV S L _ ↔
        (fun i => p.sec ((β.b *ᵥ (β.b' *ᵥ u)) i)) ∈ latV S L _ at h
      rw [← hu, ← hAu] at h
      exact h.symm
    have hAA : ∀ x : Fin S.rank → k, (β.b * g.val * β.b') *ᵥ ((β.b * (g⁻¹).val * β.b') *ᵥ x) = x := by
      intro x
      rw [Matrix.mulVec_mulVec]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc β.b' β.b, β.b'b, Matrix.one_mul, ← Matrix.mul_assoc g.val, Units.mul_inv,
        Matrix.one_mul, β.bb', Matrix.one_mulVec]
    have hunit : ∀ x z : Fin S.rank → k,
        ∑ i, ∑ j, ((β.b * g.val * β.b') *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) *
          (((mt S κ).map (fun a => p.pr (cA D a))) *ᵥ z) j =
        ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * z j := by
      intro x z
      have h := pairing_inv (p := p) κ x z
      rwa [hg] at h
    have hC : ∀ z : Fin S.rank → k, (fun i => cA D (p.sec (z i))) ∈ latV S L (· = p.v) ↔
        (fun i => cA D (p.sec ((((mt S κ).map (fun a => p.pr (cA D a))) *ᵥ z) i))) ∈ latV S L (· = p.v) := by
      intro z
      rw [csec_mem_iff hL, csec_mem_iff hL]
      constructor
      · intro h x hx
        have hx' : (fun i => p.sec (((β.b * (g⁻¹).val * β.b') *ᵥ x) i)) ∈ latV S L (· = p.v) := by
          rw [hE, hAA]; exact hx
        have h2 := hunit ((β.b * (g⁻¹).val * β.b') *ᵥ x) z
        rw [hAA] at h2
        rw [h2]; exact h _ hx'
      · intro h x hx
        rw [← hunit x z]; exact h _ ((hE x).1 hx)
    intro y hy
    have hyd : y = (fun i => p.sec (p.pr (y i))) + (fun i => cA D (p.sec (p.pr (cA D (y i))))) := by
      funext i
      simp only [Pi.add_apply, p.sec_pr]
      rw [map_mul, cA_cA, ← add_mul]
      exact ((idem_iff p _).1 (hy i)).symm
    obtain ⟨u, z, rfl⟩ : ∃ u z : Fin S.rank → k, y = (fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))) :=
      ⟨_, _, hyd⟩
    rw [Matrix.mulVec_add, hsec u, mt_csec κ z, decomp hL, decomp hL, hE u, hC z]

end GlobalTheory.FinPl.FrameLat

end
