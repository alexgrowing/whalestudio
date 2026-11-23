import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.TailSplit

theorem tprod_split {ι : Type} (a : ι → ℝ) (ha : Summable fun v => |a v - 1|) (S T S' : Finset ι)
    (h : ∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) (hd : Disjoint S T) :
    ∏' v : {v : ι // v ∉ S}, a v.1 = (∏ v ∈ T, a v) * ∏' v : {v : ι // v ∉ S'}, a v.1 := by
  classical
  have e1 : ∏' v : {v : ι // v ∉ S}, a v.1 = ∏' v, Set.mulIndicator {v | v ∉ S} a v :=
    tprod_subtype {v | v ∉ S} a
  have e2 : ∏' v : {v : ι // v ∉ S'}, a v.1 = ∏' v, Set.mulIndicator {v | v ∉ S'} a v :=
    tprod_subtype {v | v ∉ S'} a
  have m2 : Multipliable fun v => Set.mulIndicator {v | v ∉ S'} a v := by
    have : Summable fun v => ‖Set.mulIndicator {v | v ∉ S'} a v - 1‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => ?_) ha
      by_cases hv : v ∈ S'
      · simp [Set.mulIndicator, hv]
      · simp [Set.mulIndicator, hv]
    simpa using multipliable_one_add_of_summable this
  have m1 : HasProd (fun v => Set.mulIndicator (T : Set ι) a v) (∏ v ∈ T, a v) := by
    have : HasProd (fun v => Set.mulIndicator (T : Set ι) a v)
        (∏ v ∈ T, Set.mulIndicator (T : Set ι) a v) :=
      hasProd_prod_of_ne_finset_one fun v hv => by simp [Set.mulIndicator, hv]
    rwa [Finset.prod_congr rfl (fun v hv => Set.mulIndicator_of_mem (by simpa using hv) a)] at this
  rw [e1, e2, ← (m1.mul m2.hasProd).tprod_eq]
  refine tprod_congr fun v => ?_
  by_cases hS : v ∈ S
  · have hT : v ∉ T := Finset.disjoint_left.1 hd hS
    simp [Set.mulIndicator, h, hS, hT]
  · by_cases hT : v ∈ T <;> simp [Set.mulIndicator, h, hS, hT]

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (S T S' : Finset (HeightOneSpectrum (𝓞 F))), Conv b mi mv → (∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) → Disjoint S T → tailProd b mv S = (∏ v ∈ T, mv v (latV b v)) * tailProd b mv S' := by
  intro F E _ _ _ _ _ d b n M mi mv S T S' hc h hd
  obtain ⟨-, hfin, hsum⟩ := hc
  have hne : ∀ v, mv v (latV b v) ≠ ∞ := by
    intro v
    have hk : IsCompact (intV b v) :=
      ((GlobalTheory.GaugeEx.IntBasis.main F E (AlgHom.id F E) d b).1 v).1
    have hk2 : IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
      have : (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) =
          Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => intV b v := by
        ext Y
        rw [mem_latV_iff]
        simp [Set.mem_pi]
      rw [this]
      exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hk
    have := hfin v
    exact hk2.measure_lt_top.ne
  unfold tailProd
  rw [tprod_split (fun v => (mv v (latV b v)).toReal) hsum S T S' h hd,
    ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg),
    ENNReal.ofReal_prod_of_nonneg fun _ _ => ENNReal.toReal_nonneg]
  congr 1
  exact Finset.prod_congr rfl fun v _ => ENNReal.ofReal_toReal (hne v)

end GlobalTheory.GaugeEx.TailSplit
