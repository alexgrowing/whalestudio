import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

variable {D : D7} {p : ℕ}

theorem mx_zero_subsingleton : Subsingleton (Mx D 0 p) :=
  ⟨fun _ _ => funext fun i => i.elim0⟩

theorem one_mem_schwartzA_zero (θ : InfFam D) : (fun _ => 1 : Mx D 0 p → ℂ) ∈ schwartzA θ 0 p := by
  refine Submodule.subset_span ?_
  let f : SchwartzMap (D.what₂.Tau → Fin 0 → Fin p → ℂ) ℂ :=
    { toFun := fun _ => 1
      smooth' := contDiff_const
      decay' := by
        intro k n
        refine ⟨1, fun x => ?_⟩
        have hx : x = 0 := Subsingleton.elim _ _
        subst hx
        rcases k with _ | k
        · rcases n with _ | n
          · simp
          · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
        · simp }
  refine ⟨f, fun _ => 1, ⟨IsLocallyConstant.const 1, ?_⟩, ?_⟩
  · exact (Set.subsingleton_of_subsingleton).isCompact
  · funext x
    exact (mul_one (1 : ℂ)).symm

theorem pr_zero (b₀ : HermE D 0) (x y : Mx D 0 p) : pr b₀ x y = 0 := by
  ext i j
  simp [pr, HMul.hMul]

theorem isTh_one {μ : Measure (Mx D 0 p)} (h1 : μ Set.univ = 1) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (b₀ : HermE D 0) : IsTh ψ 1 θ b₀ μ (fun _ _ => 1) := by
  have : IsProbabilityMeasure μ := ⟨h1⟩
  refine ⟨fun _ => one_mem_schwartzA_zero θ, continuous_const, ?_, ?_, ?_, ?_⟩
  · intro C _
    exact ⟨_, one_mem_schwartzA_zero θ, fun _ _ _ => le_rfl⟩
  · intro g a _ h y
    simp [npow]
  · intro g b _ h y
    simp [pr_zero, halfTr]
  · intro g _ h x
    simp [pr_zero]

theorem zeroTotal : ZeroTotal := by
  intro D p μ 𝓕 h ψ hψ b₀ θ hθ u hu hB hall
  have hs : Subsingleton (Mx D 0 p) := mx_zero_subsingleton
  obtain ⟨-, -, hF⟩ := h
  have hne : 𝓕.Nonempty := by
    rcases Set.eq_empty_or_nonempty 𝓕 with he | hn
    · simp [he] at hF
    · exact hn
  have huniv : 𝓕 = Set.univ := by
    obtain ⟨y, hy⟩ := hne
    exact Set.eq_univ_of_forall fun z => (Subsingleton.elim z y) ▸ hy
  have h1 : μ Set.univ = 1 := huniv ▸ hF
  have : IsProbabilityMeasure μ := ⟨h1⟩
  have h0 := hall _ (isTh_one h1 ψ θ b₀)
  have hc : (fun y => u y * conj (1 : ℂ)) = fun _ => u 0 := by
    funext y
    simp [Subsingleton.elim y 0]
  have h2 : u 0 = 0 := by
    have h3 : ∫ y, u y * conj (1 : ℂ) ∂μ = 0 := h0
    rw [hc] at h3
    simpa using h3
  funext y
  rw [Subsingleton.elim y 0, h2]
  rfl

end GlobalTheory.CompanionTheory.ThTot

end
