import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LatLocIdealSmul

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in
theorem smul_tmul_fun {v : HeightOneSpectrum (𝓞 F)} (z b : Fv F v) (x : Fin n → E) :
    (z • fun i => b ⊗ₜ[F] x i) = fun i => (z * b) ⊗ₜ[F] x i := by
  funext i
  simp only [Pi.smul_apply, TensorProduct.smul_tmul', smul_eq_mul]

omit [NumberField E] in
theorem tmul_algebraMap_mul {v : HeightOneSpectrum (𝓞 F)} (a : Fv F v) (c : F) (e : E) :
    a ⊗ₜ[F] (algebraMap F E c * e) = (algebraMap F (Fv F v) c * a) ⊗ₜ[F] e := by
  rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def]

noncomputable def smulSet (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v) :
    AddSubgroup (Fin n → Fv F v ⊗[F] E) :=
  (GlobalTheory.AdelicU.latLoc F L v).toAddSubgroup.map (DistribMulAction.toAddMonoidHom _ z)

omit [NumberField E] in
theorem mem_smulSet {L : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)} {z : Fv F v}
    {y : Fin n → Fv F v ⊗[F] E} : y ∈ smulSet L v z ↔ ∃ x ∈ GlobalTheory.AdelicU.latLoc F L v, y = z • x := by
  simp only [smulSet, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, DistribMulAction.toAddMonoidHom_apply]
  exact ⟨fun ⟨x, hx, e⟩ => ⟨x, hx, e.symm⟩, fun ⟨x, hx, e⟩ => ⟨x, hx, e.symm⟩⟩

theorem mem_latLoc_idealMap_smul_iff (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 F)) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)
    (hle : ∀ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) ≤ Valued.v z)
    (hex : ∃ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) = Valued.v z) :
    ∀ y : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E,
      y ∈ GlobalTheory.AdelicU.latLoc F (I.map (algebraMap (𝓞 F) (𝓞 E)) • L) v ↔
        ∃ x ∈ GlobalTheory.AdelicU.latLoc F L v, y = z • x := by
  intro y
  rw [← mem_smulSet]
  constructor
  · intro hy

    have key : ∀ a ∈ v.adicCompletionIntegers F, ∀ d ∈ I, ∀ x₀ ∈ L,
        (fun i => a ⊗ₜ[F] (algebraMap F E (d : F) * x₀ i)) ∈ smulSet L v z := by
      intro a ha d hd x₀ hx₀
      simp_rw [tmul_algebraMap_mul]
      by_cases hz : z = 0
      · have h0 : algebraMap F (Fv F v) (d : F) = 0 := by
          have := hle d hd
          rw [hz, map_zero] at this
          exact (Valuation.zero_iff _).1 (le_antisymm this zero_le')
        rw [h0, zero_mul]
        simp only [TensorProduct.zero_tmul]
        exact zero_mem _
      · refine mem_smulSet.2 ⟨fun i => (algebraMap F (Fv F v) (d : F) * a / z) ⊗ₜ[F] x₀ i,
          GlobalTheory.AdelicU.tmul_mem_latLoc ?_ hx₀, ?_⟩
        · rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha ⊢
          have hzv : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz
          rw [map_div₀, map_mul, div_le_one₀ (zero_lt_iff.2 hzv)]
          calc Valued.v (algebraMap F (Fv F v) (d : F)) * Valued.v a
              ≤ Valued.v z * 1 := mul_le_mul' (hle d hd) ha
            _ = Valued.v z := mul_one _
        · rw [smul_tmul_fun, mul_div_cancel₀ _ hz]
    refine GlobalTheory.AdelicU.latLoc_induction (p := fun y => y ∈ smulSet L v z) ?_ (zero_mem _)
      (fun _ _ h h' => add_mem h h') (fun _ h => neg_mem h) hy
    intro a ha x' hx'
    refine Submodule.smul_induction_on hx' ?_ ?_
    · intro r hr x₀ hx₀
      induction hr using Submodule.span_induction generalizing x₀ with
      | mem r hr =>
        obtain ⟨d, hd, rfl⟩ := hr
        exact key a ha d hd x₀ hx₀
      | zero =>
        simp only [zero_smul, Pi.zero_apply, TensorProduct.tmul_zero]
        exact zero_mem _
      | add r s _ _ hr hs =>
        have e : (fun i => a ⊗ₜ[F] ((r + s) • x₀) i) =
            (fun i => a ⊗ₜ[F] (r • x₀) i) + fun i => a ⊗ₜ[F] (s • x₀) i := by
          funext i; simp [add_smul, TensorProduct.tmul_add]
        rw [e]; exact add_mem (hr x₀ hx₀) (hs x₀ hx₀)
      | smul o r _ hr =>
        have e : (o • r) • x₀ = r • (o • x₀) := by rw [smul_eq_mul, mul_smul, smul_comm]
        rw [e]; exact hr _ (L.smul_mem o hx₀)
    · intro x y hx hy
      have e : (fun i => a ⊗ₜ[F] (x + y) i) = (fun i => a ⊗ₜ[F] x i) + fun i => a ⊗ₜ[F] y i := by
        funext i; simp [TensorProduct.tmul_add]
      rw [e]; exact add_mem hx hy
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_smulSet.1 hy
    obtain ⟨d₀, hd₀, hv⟩ := hex
    refine GlobalTheory.AdelicU.latLoc_induction
      (p := fun x => z • x ∈ GlobalTheory.AdelicU.latLoc F (I.map (algebraMap (𝓞 F) (𝓞 E)) • L) v) ?_
      (by rw [smul_zero]; exact zero_mem _) (fun _ _ h h' => by rw [smul_add]; exact add_mem h h')
      (fun _ h => by rw [smul_neg]; exact neg_mem h) hx
    intro a ha x₀ hx₀
    by_cases hz : z = 0
    · rw [hz, zero_smul]; exact zero_mem _
    have hzv : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz
    have hd0 : algebraMap F (Fv F v) (d₀ : F) ≠ 0 := by
      intro h; rw [h, map_zero] at hv; exact hzv hv.symm
    have hmem : (algebraMap (𝓞 F) (𝓞 E) d₀ • x₀) ∈ I.map (algebraMap (𝓞 F) (𝓞 E)) • L :=
      Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hd₀) hx₀
    have hc : z * a / algebraMap F (Fv F v) (d₀ : F) ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha ⊢
      rw [map_div₀, map_mul, hv, mul_div_cancel_left₀ _ hzv]
      exact ha
    have := GlobalTheory.AdelicU.tmul_mem_latLoc (L := I.map (algebraMap (𝓞 F) (𝓞 E)) • L) hc hmem
    convert this using 1
    rw [smul_tmul_fun]
    funext i
    change _ = (z * a / algebraMap F (Fv F v) (d₀ : F)) ⊗ₜ[F] (algebraMap F E (d₀ : F) * x₀ i)
    rw [tmul_algebraMap_mul, mul_div_cancel₀ _ hd0]

end GlobalTheory.LatLocIdealSmul
