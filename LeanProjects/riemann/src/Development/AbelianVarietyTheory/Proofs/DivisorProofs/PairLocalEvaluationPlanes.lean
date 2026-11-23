import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinIntEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerActionLocallyConstant
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ConeBump.LocConst

private theorem isLocallyConstant_prod {α β γ δ : Type} [TopologicalSpace α] [TopologicalSpace β] {p : α → γ}
    (hp : IsLocallyConstant p) (f : γ → β → δ) (hf : ∀ a, IsLocallyConstant (f (p a))) :
    IsLocallyConstant fun q : α × β => f (p q.1) q.2 := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro q₀
  filter_upwards [continuous_fst.continuousAt.eventually (hp.eventually_eq q₀.1),
    continuous_snd.continuousAt.eventually ((hf q₀.1).eventually_eq q₀.2)] with q h1 h2
  rw [h1, h2]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem continuous_locCo_smul {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (v : Pl F)
    (u : Matrix (Fin n) (Fin d) (AE F E)) : Continuous fun l : AE F E => GlobalTheory.LatVac.locCo M.co v (l • u) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  let L : AE F E →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    M.co.e.toLinearMap ∘ₗ
      { toFun := fun l => l • u, map_add' := fun a b => add_smul a b u, map_smul' := fun a b => smul_assoc a b u }
  have hL : Continuous L := IsModuleTopology.continuous_of_linearMap L
  have he : Continuous (evFin F v) := (RestrictedProduct.continuous_eval v).comp continuous_snd
  exact (continuous_pi fun k => he.comp ((continuous_apply k).comp hL.fst)).prodMk
    (continuous_pi fun k => he.comp ((continuous_apply k).comp hL.snd))

private theorem isLocallyConstant_locOp_om (hA : ActsEx) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E}
    {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s')
    (K : Subgroup (UA σ X.J)) (v : Pl F) {φ : (Fin n × Fin d → Fv F v) → ℂ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) :
    IsLocallyConstant fun k : KAt K (evFin F v) => locOp v (om (k.1, 1)) φ := by
  have h1W : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := (UAtSub σ W (evFin F v)).one_mem
  obtain ⟨U, hU, hUact⟩ := (hA F E σ B n d X W M χX χW om r s r' s' hP v).2.2 φ hφ
  rw [IsLocallyConstant.iff_eventually_eq]
  intro k₀
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have hc : Continuous fun k : KAt K (evFin F v) => ((k₀⁻¹ * k : KAt K (evFin F v)).1, (1 : UA σ W.J)) :=
    (continuous_subtype_val.comp (continuous_const.mul continuous_id)).prodMk continuous_const
  have h0 : ((k₀⁻¹ * k₀ : KAt K (evFin F v)).1, (1 : UA σ W.J)) = 1 := by
    rw [inv_mul_cancel]; rfl
  have hev : ∀ᶠ k in 𝓝 k₀, ((k₀⁻¹ * k : KAt K (evFin F v)).1, (1 : UA σ W.J)) ∈ U :=
    hc.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU)
  filter_upwards [hev] with k hk
  have hfix : Acts (evFin F v) (om ((k₀⁻¹ * k).1, 1)) φ φ := hUact _ hk (mem_KAt.1 (k₀⁻¹ * k).2).2 h1W
  have ha := acts_locOp_om hA hP (mem_KAt.1 k₀.2).2 h1W hφ
  have ek : (k.1, (1 : UA σ W.J)) = (k₀.1, 1) * ((k₀⁻¹ * k).1, 1) := by
    rw [Prod.mk_mul_mk, mul_one, ← Subgroup.coe_mul, mul_inv_cancel_left]
  refine locOp_eq hφ (locOp_mem _ _ _) fun ρ hρ => ?_
  rw [ek, map_mul, Module.End.mul_apply, hfix ρ hρ, ha ρ hρ]

end GlobalTheory.ConeBump.LocConst

open scoped GlobalTheory.VacAny in
theorem _root_.GlobalTheory.T.pair_local_evaluation_planes : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (m m' : ℕ) (H : Plane E n m) (H' : Plane E d m') (v : Pl F)
    (ev : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ) (K : Subgroup (UA σ X.J)),
    ∀ φ ∈ SB (Fin n × Fin d → Fv F v), IsLocallyConstant (fun p : KAt K (evFin F v) × idelesAt E (evFin F v) =>
      GlobalTheory.ConeBump.integ B M om v ev (shiftA H H') φ p.1.1 p.2.1) := by
  intro hKP F E _ _ _ _ _ σ B n d n₁ d₁ X W M χX χW om r s r' s' hP m m' H H' v ev K φ hφ
  have hc : Continuous B.ψ := hP.base.std.1
  refine GlobalTheory.ConeBump.LocConst.isLocallyConstant_prod
    (GlobalTheory.ConeBump.LocConst.isLocallyConstant_locOp_om (GlobalTheory.T.theta_action_exists hKP.base) hP K v hφ)
    (fun ψ (l : idelesAt E (evFin F v)) => ev (locOp v (M.co.rho B.ψ (partFin v (shiftA H H' l.1))) ψ)) fun k => ?_
  have hψ := locOp_mem v (om (k.1, 1)) φ
  generalize locOp v (om (k.1, 1)) φ = ψ at hψ
  have hχl : IsLocallyConstant (GlobalTheory.LatVac.psiAt B.ψ v) :=
    GlobalTheory.SchrSB.isLocallyConstant_addChar _ (GlobalTheory.SchrSB.continuous_psiAt B.ψ hc v)
  have hχ0 : ∀ᶠ y in 𝓝 (0 : Fv F v), GlobalTheory.LatVac.psiAt B.ψ v y = 1 := by simpa using hχl.eventually_eq 0
  have hS := GlobalTheory.SchrLocConst.schr_isLocallyConstant _ hχ0 ψ hψ
  have hL := GlobalTheory.ConeBump.LocConst.continuous_locCo_smul M v (Matrix.vecMulVec (incV F H.x) (incV F H'.y))
  have hcl : Continuous fun l : idelesAt E (evFin F v) => l.1.1 :=
    Units.continuous_val.comp continuous_subtype_val
  have h := (hS.comp_continuous (hL.comp hcl)).comp ev
  convert h using 1
  funext l
  rw [(locOp_rho M.co hc v _ hψ).2]
  rfl
