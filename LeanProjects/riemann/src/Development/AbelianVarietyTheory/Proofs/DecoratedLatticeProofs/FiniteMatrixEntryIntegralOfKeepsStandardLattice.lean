import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianStepLevelOfChartFormsLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledLatticeVectorMemDualBaseLatticeCompletion
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

namespace GlobalTheory.FinPl.MovesEntries

theorem map_mulVec_single {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (y : Fin n → A) (r s : Fin n) (h1 : f (y s) = 1)
    (h0 : ∀ b, b ≠ s → y b = 0) : f ((M *ᵥ y) r) = f (M r s) := by
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [Finset.sum_eq_single s]
  · rw [h1, mul_one]
  · intro b _ hb
    rw [h0 b hb, map_zero, mul_zero]
  · intro hs
    exact (hs (Finset.mem_univ _)).elim

theorem toEAf_pair (D : D7) (α : Af D.host.F) (e : D.host.E) :
    toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] e) = e ⊗ₜ[D.host.F] α := by
  rfl

theorem infPart_pair (D : D7) (α : Af D.host.F) (e : D.host.E) :
    infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] e) = 0 := by
  have : infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] e)
      = (0 : Ainf D.host.F) ⊗ₜ[D.host.F] e := rfl
  rw [this, TensorProduct.zero_tmul]

theorem coord_int (D : D7) (S : HSp D) (L : GlobalTheory.FinPl.Lat S)
    (hL : ∀ z, z ∈ L ↔ z ∈ GlobalTheory.AdForm.intVec D S.rank) (v : HeightOneSpectrum (𝓞 D.host.F))
    (y : Fin S.rank → AE D) (hy : y ∈ GlobalTheory.FinPl.latV S L (fun _ => True)) (i : Fin S.rank) :
    Formalism.UG.prV (E := D.host.E) v (toEAf D (y i)) ∈ Formalism.BasicNotions.intV D.host.E v := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, a, ha, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at ha
    subst ha
    have hxi : IsIntegral ℤ (x i) := (hL x).1 hx i
    have h1 : Formalism.UG.prV (E := D.host.E) v
        (toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)))
        = ((x i) ⊗ₜ[D.host.F] (1 : v.adicCompletion D.host.F))
          * ((1 : D.host.E) ⊗ₜ[D.host.F] (evalV D.host.F v α : v.adicCompletion D.host.F)) := by
      rw [toEAf_pair, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, one_mul]
      rfl
    show Formalism.UG.prV (E := D.host.E) v
        (toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i))) ∈ _
    rw [h1]
    refine Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨x i, ⟨⟨x i, hxi⟩, rfl⟩⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨evalV D.host.F v α, hα v⟩, rfl⟩))
  | zero =>
    rw [Pi.zero_apply, (toEAf D).map_zero, (Formalism.UG.prV (E := D.host.E) v).map_zero]
    exact Subring.zero_mem _
  | add a b _ _ ha hb =>
    rw [Pi.add_apply, (toEAf D).map_add, (Formalism.UG.prV (E := D.host.E) v).map_add]
    exact Subring.add_mem _ ha hb
  | neg a _ ha =>
    rw [Pi.neg_apply, (toEAf D).map_neg, (Formalism.UG.prV (E := D.host.E) v).map_neg]
    exact Subring.neg_mem _ ha

theorem finM_entry_int : ∀ (D : D7) (S : HSp D) {n : ℕ} (hn : S.rank = n) (L : GlobalTheory.FinPl.Lat S), (∀ z, z ∈ L ↔ z ∈ GlobalTheory.AdForm.intVec D S.rank) → ∀ κ : GA D S, GlobalTheory.FinPl.Moves S κ L L (fun _ => True) → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (r s : Fin n), Formalism.UG.prV (E := D.host.E) v (GlobalTheory.AdForm.finM S hn κ r s) ∈ Formalism.BasicNotions.intV D.host.E v := by
  intro D S n hn L hL κ hκ v r s
  subst hn
  let x : Fin S.rank → D.host.E := Pi.single s 1
  have hx : x ∈ L := by
    rw [hL]
    intro k
    by_cases hk : k = s
    · subst hk
      simp only [x, Pi.single_eq_same]
      exact isIntegral_one
    · simp only [x, Pi.single_eq_of_ne hk]
      exact isIntegral_zero
  let y : Fin S.rank → AE D := fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 * x i)
  have hy : y ∈ GlobalTheory.FinPl.latV S L (fun _ => True) := by
    refine AddSubgroup.subset_closure ⟨1, ?_, fun w hw => (hw trivial).elim, 1, rfl, x, hx, rfl⟩
    intro w
    rw [map_one]
    exact one_mem _
  have hid : ∀ i, y i ∈ GlobalTheory.FinPl.idAt D (fun _ => True) := by
    intro i
    refine Submodule.mem_inf.2 ⟨infPart_pair D _ _, ?_⟩
    rw [Submodule.mem_iInf]
    intro w
    exact (w.2 trivial).elim
  have h := coord_int D S L hL v _ ((hκ y hid).1 hy) r
  have h2 : toEAf D ((Formalism.L2.Theta.mt S κ *ᵥ y) r) = toEAf D (Formalism.L2.Theta.mt S κ r s) := by
    refine map_mulVec_single (toEAf D) _ y r s ?_ ?_
    · simp only [y, x, toEAf_pair, Pi.single_eq_same, one_mul]
      rfl
    · intro b hb
      simp only [y, x, Pi.single_eq_of_ne hb, mul_zero, TensorProduct.tmul_zero]
  rw [h2] at h
  exact h

end GlobalTheory.FinPl.MovesEntries
