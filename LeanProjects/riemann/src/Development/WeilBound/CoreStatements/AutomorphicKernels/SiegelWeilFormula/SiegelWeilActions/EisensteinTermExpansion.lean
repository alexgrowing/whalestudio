import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SectionSumIntegralExpand
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.NonLagrangianCosetsBijection

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C5

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} (R : RD d) (L : LD d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

theorem eisenstein_term_expansion (h : Hyp L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    {e : (Σ _ : Cs L.sd, Crat L) ≃ {q : Cs d // ¬ LagrangianCondition L (rep q)}}
    (he : ∀ x, ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ rep (e x).1 = p * (w₁ * (cM x.2.1 * L.j (rep x.1)))) (g : d.G) :
    E2 L (phz d f s₁ z) g = ∑' x : (Σ _ : Cs L.sd, Crat L), phz d f s₁ z (w₁ * (cM x.2.1 * (L.j (rep x.1) * g))) ∧
      ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, ‖phz d f s₁ z (rep q.1 * g)‖ₑ =
        ∑' x : (Σ _ : Cs L.sd, Crat L), ‖phz d f s₁ z (w₁ * (cM x.2.1 * (L.j (rep x.1) * g)))‖ₑ := by
  have key : ∀ x : (Σ _ : Cs L.sd, Crat L), phz d f s₁ z (rep (e x).1 * g) =
      phz d f s₁ z (w₁ * (cM x.2.1 * (L.j (rep x.1) * g))) := fun x => by
    obtain ⟨p, hp, hr, hx⟩ := he x
    rw [hx, mul_assoc, C4.phz_rat hf z hp hr, mul_assoc, mul_assoc]
  constructor
  · rw [E2, ← e.tsum_eq]
    exact tsum_congr key
  · rw [← e.tsum_eq]
    exact tsum_congr fun x => by rw [key]

end PositivityTheory.SiegelWeilFormula.Act.C5

end
