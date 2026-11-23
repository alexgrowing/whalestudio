import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThProdA

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

open PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.ThTot

namespace PositivityTheory.Rg.Rsw.L.LThProd

variable {D : D7}

theorem rowB_eq {m p : ℕ} (y : Mx D (m + 1) p) : rowB (r := m) (s := 1) y = y.submatrix (fun _ => Fin.last m) id := by
  funext a j
  show y (Fin.natAdd m a) j = y (Fin.last m) j
  rw [natAdd_one]

theorem succ (hW : L.WMaj) {p : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {θ : InfFam D}
    (hθ : IsInfFam θ) : ∀ (k : ℕ) (b₀ : HermE D (k + 1)), IsDiagInv b₀ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ →
    ResEta D χ (k + 1) → ∀ (μ : Measure (Mx D (k + 1) p)) (𝓕 : Set (Mx D (k + 1) p)), IsCovolOne (ratMx D (k + 1) p) μ 𝓕 →
    ∀ η : Fin (k + 1) → Mx D 1 p → ℂ, (∀ i, η i ∈ schwartzA θ 1 p) →
    ∃ Ω, IsTh ψ χ θ b₀ μ Ω ∧ ∀ y, Ω 1 y = ∏ i, η i (y.submatrix (fun _ => i) id)
  | 0, b₀, hb, χ, hχ, hr, μ, 𝓕, hμ, η, hη => by
    obtain ⟨Ω, hT, h1⟩ := oneTh hW μ 𝓕 hμ hψ b₀ hb.2 hχ hr hθ (η 0) (hη 0)
    refine ⟨Ω, hT, fun y => ?_⟩
    rw [Fin.prod_univ_one, h1]
    congr 1
    funext a j
    rw [Fin.fin_one_eq_zero a]
    rfl
  | k + 1, b₀, hb, χ, hχ, hr, μ, 𝓕, hμ, η, hη => by
    obtain ⟨ε, hε, hεr⟩ := GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta D 1
    obtain ⟨μr, 𝓕r, hμr⟩ := GlobalTheory.MixModel.exists_isCovolOne D (k + 1) p
    obtain ⟨μs, 𝓕s, hμs⟩ := GlobalTheory.MixModel.exists_isCovolOne D 1 p
    obtain ⟨Ωr, hTr, hr1⟩ := succ hW hψ hθ k (topH b₀) (topH_diag hb) (χ * ε⁻¹) (hecke_mul_inv hχ hε)
      (resEta_mul_inv hr (by simpa using hεr)) μr 𝓕r hμr (fun i => η (Fin.castSucc i)) fun i => hη _
    obtain ⟨Ωs, hTs, hs1⟩ := oneTh hW μs 𝓕s hμs hψ (botH b₀) (botH_det hb) hε (by simpa using hεr) hθ
      (η (Fin.last (k + 1))) (hη _)
    have hP := GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor GlobalTheory.CompanionTheory.ThTot.SchwT.schwTensor D (k + 1) 1 p μr 𝓕r μs 𝓕s
      hμr hμs ψ hψ (χ * ε⁻¹) ε θ hθ (topH b₀) (botH b₀) b₀ (diagonal_hermitian_is_block hb) Ωr Ωs hTr hTs
    rw [inv_mul_cancel_right,
      ← GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas D (k + 1) 1 p μr 𝓕r μs 𝓕s μ 𝓕 hμr hμs hμ] at hP
    refine ⟨_, hP, fun y => ?_⟩
    show Ωr 1 (rowT y) * Ωs 1 (rowB y) = _
    rw [hr1, hs1, rowB_eq]
    conv_rhs => rw [Fin.prod_univ_castSucc]
    rfl

end PositivityTheory.Rg.Rsw.L.LThProd

namespace PositivityTheory.Rg.Rsw.L

theorem thProd (hW : WMaj) : ThProd := by
  intro D ρ p m ψ hψ b₀ hb χ hχ hr hρ θ hθ η hη
  obtain ⟨k, rfl⟩ : ∃ k, ρ = k + 1 := ⟨ρ - 1, by omega⟩
  exact LThProd.succ hW hψ hθ k b₀ hb χ hχ hr m.μ m.𝓕 m.hμ η hη

end PositivityTheory.Rg.Rsw.L

end
