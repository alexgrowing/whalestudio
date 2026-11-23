import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleDescentModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem GlobalTheory.ThK.EvOnto.main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    B.IsGood σ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') → M.IsGood B.ψ → M₁.IsGood B.ψ →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁, IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ →
      ∀ Ψ₁ ∈ schA F (Fin n × Fin d₁), ∃ Ψ ∈ schA F (Fin n × Fin d), e₀ Ψ = Ψ₁ := by
  intro hK F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hB hXW hM hM₁ hH e₀ he₀ Ψ₁ hΨ₁
  classical
  obtain ⟨r, s, r', s', hX, hW⟩ := hXW
  obtain ⟨ei, ev, hei, hv, hl⟩ := he₀.loc
  have hR := GlobalTheory.ThK.EvUniq.infRel_of_isEv F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH hM₁ e₀ he₀
    ei ev hei hv hl
  have hsurj := GlobalTheory.ThK.EvTwoNe.infRel_surjective hK.base B hB hX hW hM hH hM₁ ei hei hR

  have hloc : ∀ (v : Pl F) (φ₁ : (Fin n × Fin d₁ → Fv F v) → ℂ), φ₁ ∈ SB (Fin n × Fin d₁ → Fv F v) →
      ∃ φ, φ ∈ SB (Fin n × Fin d → Fv F v) ∧ ev v φ = φ₁ ∧ (φ₁ = M₁.vac v → φ = M.vac v) := by
    intro v φ₁ h
    by_cases hc : φ₁ = M₁.vac v
    · exact ⟨M.vac v, (hM.vac v).1, hc ▸ (hv v).1, fun _ => rfl⟩
    · have hm : φ₁ ∈ (SB (Fin n × Fin d → Fv F v)).map (ev v) := by rw [(hv v).2]; exact h
      obtain ⟨φ, hφ, hφe⟩ := hm
      exact ⟨φ, hφ, hφe, fun h' => absurd h' hc⟩
  choose pre hpreSB hpreEv hpreVac using hloc
  obtain ⟨T, m, f, φ, hφSB, hφstd, rfl⟩ := GlobalTheory.SchADecomp.exists_sum_pure F _ Ψ₁ hΨ₁
  choose f' hf' using fun i => hsurj (f i)
  let φ' : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun i v => pre v (φ i v) (hφSB i v)
  have hcof : ∀ i, ∀ᶠ v in cofinite, φ i v = M₁.vac v := fun i => by
    have hT : ∀ᶠ v in cofinite, v ∉ T := Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by simpa using hv)
    filter_upwards [hM₁.std, hT] with v h1 h2
    rw [hφstd i v h2, h1]
  have hcof' : ∀ i, ∀ᶠ v in cofinite, φ' i v = M.vac v := fun i =>
    (hcof i).mono fun v h => hpreVac v _ _ h
  have hSB' : ∀ i v, φ' i v ∈ SB (Fin n × Fin d → Fv F v) := fun i v => hpreSB v _ _
  refine ⟨∑ i, pure (f' i) (φ' i), Submodule.sum_mem _ fun i _ => ?_, ?_⟩
  · refine GlobalTheory.TensUniq.pure_mem_schA (f' i) (φ' i) (hSB' i) ?_
    filter_upwards [hcof' i, hM.std] with v h1 h2
    rw [h1, h2]
  · rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hl (f' i) (φ' i) (hSB' i) (hcof' i), hf' i]
    congr 1
    funext v
    exact hpreEv v _ _
