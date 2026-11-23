import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK.EulerUnr

theorem integral_map_prod_snd_of_prob {α β α' β' : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace α']
    [MeasurableSpace β'] {i : α' → α} {j : β' → β} (hi : MeasurableEmbedding i) (hj : MeasurableEmbedding j)
    (μ : Measure α') (ν : Measure β') [IsProbabilityMeasure μ] [SFinite ν] (g : α × β → ℝ) (r : β' → ℝ)
    (hg : ∀ a b, g (i a, j b) = r b) :
    ∫ q, g q ∂((μ.map i).prod (ν.map j)) = ∫ b, r b ∂ν := by
  rw [Measure.map_prod_map _ _ hi.measurable hj.measurable, (hi.prodMap hj).integral_map]
  have h : ∀ p : α' × β', g (Prod.map i j p) = r p.2 := fun p => hg p.1 p.2
  simp only [h]
  rw [integral_fun_snd]
  simp

theorem integral_KAt_idelesAt_snd : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} {X : Spc F E n} (K : Subgroup (UA σ X.J)), IsClosed (K : Set (UA σ X.J)) → ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))), IsNormK K (evFin F v) μK → ∀ (μE : Measure (idelesAt E (evFin F v))), IsNormE E v μE → ∀ (g : UA σ X.J × (AE F E)ˣ → ℝ) (r : idelesAt E (evFin F v) → ℝ), (∀ k ∈ KAt K (evFin F v), ∀ (l : (AE F E)ˣ) (hl : l ∈ idelesAt E (evFin F v)), g (k, l) = r ⟨l, hl⟩) → ∫ q, g q ∂((μK.map Subtype.val).prod (μE.map Subtype.val)) = ∫ l, r l ∂μE := by
  intro F E _ _ _ _ _ σ n X K hKc v μK hμK μE hμE g r hg
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI : IsProbabilityMeasure μK := ⟨hμK.2⟩
  haveI := hμE.1
  have hK1 : IsClosed (KAt K (evFin F v) : Set (UA σ X.J)) := hKc.inter (isClosed_UAtSub X _)
  exact integral_map_prod_snd_of_prob (MeasurableEmbedding.subtype_coe hK1.measurableSet)
    (MeasurableEmbedding.subtype_coe (isClosed_idelesAt (E := E) (evFin F v)).measurableSet) μK μE g r
    (fun a b => hg _ a.2 _ b.2)

end GlobalTheory.ThK.EulerUnr
