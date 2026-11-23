import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOHZeroRight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMapsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.ContrComb.LatT

variable {D : D7}

theorem latV_entry_mem {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) (i : Fin S.rank) : y i ∈ idAt D P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, -, hβ, c, -, x, -, rfl⟩ := hz
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt hβ _
  | zero => exact zero_mem _
  | add z z' _ _ hz hz' => exact add_mem hz hz'
  | neg z _ hz => exact neg_mem hz

theorem jA_latV {V₀ A L : HSp D} (o : OrthDec V₀ A L) {P : Pl D → Prop} {LA : Lat A} {M : Lat V₀}
    (hLA : IsSelfDualC A LA) (hM : IsSelfDualC V₀ M) (hloc : ∀ v, P v → ∃ LL, OrthAt o M LA LL v)
    {y : Fin A.rank → AE D} (hy : y ∈ latV A LA P) : o.jA *ᵥ y ∈ latV V₀ M P := by
  have hG := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P
  have hy' := ((hG.2 A).2.2.2 LA y hLA.1).1 hy
  refine ((hG.2 V₀).2.2.2 M _ hM.1).2 ⟨fun i => ?_, fun v hv e he => ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (hy'.1 j)
  · obtain ⟨LL, hLL⟩ := hloc v hv
    have hz := hy'.2 v hv e he
    rw [← Matrix.mulVec_smul]
    refine (hLL _).2 ⟨?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, o.pA_jA, Matrix.one_mulVec]; exact hz
    · rw [Matrix.mulVec_mulVec, o.pB_jA, Matrix.zero_mulVec]; exact zero_mem _

theorem smul_latV_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {w : Fin S.rank → AE D} (hw : w ∈ latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • w ∈ latA S L P := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz

theorem jA_latA {V₀ A L : HSp D} (o : OrthDec V₀ A L) {P : Pl D → Prop} {LA : Lat A} {M : Lat V₀}
    (hLA : IsSelfDualC A LA) (hM : IsSelfDualC V₀ M) (hloc : ∀ v, P v → ∃ LL, OrthAt o M LA LL v)
    {z : Fin A.rank → AE D} (hz : z ∈ latA A LA P) : o.jA *ᵥ z ∈ latA V₀ M P := by
  induction hz using AddSubgroup.closure_induction with
  | mem g hg =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hg
    have hsplit : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i) : Fin A.rank → AE D) =
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hsplit, Matrix.mulVec_smul]
    exact smul_latV_mem_latA ha
      (jA_latV o hLA hM hloc (AddSubgroup.subset_closure ⟨α, hαi, hα, 1, rfl, x, hx, rfl⟩))
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem latO_extR : ∀ (D : D7) (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (P : Pl D → Prop) (LA : Lat A) (LS : Lat S)
    (M : Lat V₀), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC V₀ M → (∀ v, P v → ∃ LL, OrthAt o M LA LL v) →
    ∀ u ∈ latO S A (LS : Set _) (LA : Set _) P, (o.resT S).symm (u, 0) ∈ latO S V₀ (LS : Set _) (M : Set _) P := by
  intro D V₀ A L S o P LA LS M hLA hLS hM hloc u hu
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
  have hu' := (GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D S A LS LA hLS hLA P u).1 hu
  refine (GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D S V₀ LS M hLS hM P _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [Matrix.mul_apply]
    exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hu'.1 k j)
  · show (o.jA * u) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec]
    exact jA_latA o hLA hM hloc (hu'.2 y hy)

end GlobalTheory.ContrComb.LatT
end
