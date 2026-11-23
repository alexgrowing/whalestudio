import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix ContDiff
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKLeftInv

theorem polMatch_mem_schA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') {R : RealMaps F a a'} {Rf : FinMaps F a a'} {Φ Φ'} (hm : PolMatch B G X R Rf Φ Φ') :
    Φ ∈ schA F (Fin a × Fin (a + a')) ∧ Φ' ∈ schA F (Fin a' × Fin (a + a')) := by
  obtain ⟨T, -, m, m', f, φ, f', φ', hf, hf', rfl, rfl, -⟩ := hm
  refine ⟨Submodule.sum_mem _ fun i _ => ?_, Submodule.sum_mem _ fun j _ => ?_⟩
  · refine GlobalTheory.TensUniq.pure_mem_schA (f i) (φ i) (hf i).2.1 ?_
    filter_upwards [hT.geo.hM.std, (T.finite_toSet.compl_mem_cofinite : (↑T : Set (Pl F))ᶜ ∈ cofinite)] with v hv hvT
    rw [(hf i).2.2 v hvT, hv]
  · refine GlobalTheory.TensUniq.pure_mem_schA (f' j) (φ' j) (hf' j).2.1 ?_
    filter_upwards [hT.geo.hM'.std, (T.finite_toSet.compl_mem_cofinite : (↑T : Set (Pl F))ᶜ ∈ cofinite)] with v hv hvT
    rw [(hf' j).2.2 v hvT, hv]

theorem integral_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (hΦ : ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, theta om Φ (γ * g) (γ' * h) = theta om Φ g h)
    (γ : UA σ W.J) (hγ : γ ∈ ratU σ W.J) (h : UA σ W.J) : M.I om Φ (γ * h) = M.I om Φ h := by
  unfold Model.I
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  have := hΦ 1 (one_mem _) γ hγ g h
  simpa only [one_mul] using this

end GlobalTheory.ThKLeftInv

open GlobalTheory.ThKLeftInv in

theorem GlobalTheory.ThKLeftInv.left_invariant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 → 1 ≤ G.p →
    ∀ c : ℂ, ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' →
    ∀ c₀ : E, c₀ ≠ 0 → ∀ φ' : GAd σ (c₀ • G.W.J.map σ) → ℂ,
      (∀ (g : UA σ G.W.J) (g' : GAd σ (c₀ • G.W.J.map σ)), g.1 = g'.1 → φ' g' = G.M.I om Φ g - c * G.M'.I om' Φ' g) →
      ∀ γ ∈ ratPts σ (c₀ • G.W.J.map σ), ∀ g, φ' (γ * g) = φ' g := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hm _ _ c Φ Φ' _ hpm c₀ hc₀ φ' hφ' γ hγ g
  have hT := hm.triple
  have hS := polMatch_mem_schA hT hpm
  have hTB := GlobalTheory.T.theta_basic_properties hKP.base
  have k1 := (hTB F E σ B _ _ _ _ G.M _ _ om _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hT)).1 Φ hS.1
  have k2 := (hTB F E σ B _ _ _ _ G.M' _ _ om' _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hT)).1 Φ' hS.2
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hT.base.cm
  have eq := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := G.W.J) hσ hc₀
  have mem : ∀ x : GAd σ (c₀ • G.W.J.map σ), x.1 ∈ UG (cA σ) (incM F G.W.J) := fun x => by
    have h2 : x.1 ∈ HR (AF F) σ (c₀ • G.W.J.map σ) := x.2
    exact (SetLike.ext_iff.mp eq x.1).mpr h2
  let g₀ : UA σ G.W.J := ⟨g.1, mem g⟩
  let γ₀ : UA σ G.W.J := ⟨γ.1, mem γ⟩
  have hγ₀ : γ₀ ∈ ratU σ G.W.J := by
    have h1 : γ.1 ∈ HFin (AF F) σ (c₀ • G.W.J.map σ) := hγ
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.mp h1
    exact Subgroup.mem_subgroupOf.mpr ⟨u, hu⟩
  rw [hφ' (γ₀ * g₀) (γ * g) rfl, hφ' g₀ g rfl, integral_rat G.M om Φ k1.2.1 γ₀ hγ₀ g₀,
    integral_rat G.M' om' Φ' k2.2.1 γ₀ hγ₀ g₀]
