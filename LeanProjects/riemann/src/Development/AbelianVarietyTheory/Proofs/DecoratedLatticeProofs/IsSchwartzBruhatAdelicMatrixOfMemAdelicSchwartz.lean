import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeBoundsAlongRealParametrisatiStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.SchwartzPure

open GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies

variable {D : D7} {m n : ℕ}

theorem eventually_invariant {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {Φ : M → ℂ}
    (h1 : IsLocallyConstant Φ) (h2 : HasCompactSupport Φ) : ∀ᶠ u in 𝓝 (0 : M), ∀ x, Φ (x + u) = Φ x := by
  have h : ∀ᶠ u in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + u) = Φ x ∧ Φ (x - u) = Φ x := by
    apply h2.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have a1 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 + z.1 by fun_prop)).eventually_eq (0, x)
    have a2 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 - z.1 by fun_prop)).eventually_eq (0, x)
    have a3 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 by fun_prop)).eventually_eq (0, x)
    filter_upwards [a1, a2, a3] with z b1 b2 b3
    simp only [Function.comp, add_zero, sub_zero] at b1 b2 b3
    exact ⟨b1.trans b3.symm, b2.trans b3.symm⟩
  filter_upwards [h] with u hu x
  by_cases hx : x ∈ tsupport Φ
  · exact (hu x hx).1
  · by_cases hx' : x + u ∈ tsupport Φ
    · have := (hu _ hx').2
      rw [add_sub_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

def periods {M : Type} [AddCommGroup M] (Φ : M → ℂ) : AddSubgroup M where
  carrier := {u | ∀ x, Φ (x + u) = Φ x}
  zero_mem' := fun x => by rw [add_zero]
  add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
  neg_mem' := fun {a} ha x => by
    have := ha (x + -a)
    rw [neg_add_cancel_right] at this
    exact this.symm

theorem isOpen_periods {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {Φ : M → ℂ}
    (h1 : IsLocallyConstant Φ) (h2 : HasCompactSupport Φ) : IsOpen (periods Φ : Set M) :=
  AddSubgroup.isOpen_of_mem_nhds _ (eventually_invariant h1 h2)

theorem zero : IsSchwartzBruhat (0 : Mx D m n → ℂ) where
  level := ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  supp := ⟨∅, isCompact_empty, fun _ h => absurd rfl h⟩
  schwartz := fun _ _ _ _ _ => ⟨0, fun _ => rfl⟩

theorem add {φ ψ : Mx D m n → ℂ} (hφ : IsSchwartzBruhat φ) (hψ : IsSchwartzBruhat ψ) : IsSchwartzBruhat (φ + ψ) where
  level := by
    obtain ⟨U, hU, h⟩ := hφ.level
    obtain ⟨U', hU', h'⟩ := hψ.level
    refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 x => ?_⟩
    simp only [Pi.add_apply, h u hu.1 h0, h' u hu.2 h0]
  supp := by
    obtain ⟨K, hK, h⟩ := hφ.supp
    obtain ⟨K', hK', h'⟩ := hψ.supp
    refine ⟨K ∪ K', hK.union hK', fun x hx => ?_⟩
    by_cases h1 : φ x = 0
    · exact Or.inr (h' x fun h2 => hx (by simp [h1, h2]))
    · exact Or.inl (h x h1)
  schwartz := fun k L hL hi x => by
    obtain ⟨g, hg⟩ := hφ.schwartz k L hL hi x
    obtain ⟨g', hg'⟩ := hψ.schwartz k L hL hi x
    exact ⟨g + g', fun t => by simp [hg, hg']⟩

theorem smul (c : ℂ) {φ : Mx D m n → ℂ} (hφ : IsSchwartzBruhat φ) : IsSchwartzBruhat (c • φ) where
  level := by
    obtain ⟨U, hU, h⟩ := hφ.level
    exact ⟨U, hU, fun u hu h0 x => by simp only [Pi.smul_apply, h u hu h0]⟩
  supp := by
    obtain ⟨K, hK, h⟩ := hφ.supp
    exact ⟨K, hK, fun x hx => h x fun h1 => hx (by simp [h1])⟩
  schwartz := fun k L hL hi x => by
    obtain ⟨g, hg⟩ := hφ.schwartz k L hL hi x
    exact ⟨c • g, fun t => by simp [hg]⟩

theorem compAt_add (θ : InfFam D) (τ : D.what₂.Tau) (x y : Mx D m n) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.add_apply]
  rw [(infPart D).map_add, (θ τ).map_add]

def realVec {k : ℕ} (θ : InfFam D) (L : (Fin k → ℝ) →+ Mx D m n) : (Fin k → ℝ) →+ (D.what₂.Tau → Fin m → Fin n → ℂ) where
  toFun t := fun τ i j => compAt θ τ (L t) i j
  map_zero' := by ext τ i j; simp [compAt]
  map_add' a b := by ext τ i j; simp [compAt_add]

theorem norm_compAt_le (θ : InfFam D) (x : Mx D m n) (τ : D.what₂.Tau) (i : Fin m) (j : Fin n) :
    ‖compAt θ τ x i j‖ ≤ GlobalTheory.Unf.realSize θ x := by
  unfold GlobalTheory.Unf.realSize
  calc ‖compAt θ τ x i j‖ ≤ ∑ j', ‖compAt θ τ x i j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖compAt θ τ x i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖compAt θ τ x i' j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖compAt θ τ x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', ‖compAt θ τ' x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ)

theorem realSize_nonneg (θ : InfFam D) (x : Mx D m n) : 0 ≤ GlobalTheory.Unf.realSize θ x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_vec_le (θ : InfFam D) (x : Mx D m n) :
    ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ)‖ ≤ GlobalTheory.Unf.realSize θ x :=
  (pi_norm_le_iff_of_nonneg (realSize_nonneg θ x)).2 fun τ =>
    (pi_norm_le_iff_of_nonneg (realSize_nonneg θ x)).2 fun i =>
      (pi_norm_le_iff_of_nonneg (realSize_nonneg θ x)).2 fun j => norm_compAt_le θ x τ i j

theorem realSize_le (θ : InfFam D) (x : Mx D m n) :
    GlobalTheory.Unf.realSize θ x ≤ (Fintype.card D.what₂.Tau * (m * n) : ℝ) *
      ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ)‖ := by
  set v : D.what₂.Tau → Fin m → Fin n → ℂ := fun τ i j => compAt θ τ x i j with hv
  unfold GlobalTheory.Unf.realSize
  calc ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖ ≤ ∑ τ : D.what₂.Tau, ∑ i : Fin m, ∑ j : Fin n, ‖v‖ :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          (norm_le_pi_norm (v τ i) j).trans ((norm_le_pi_norm (v τ) i).trans (norm_le_pi_norm v τ))
    _ = _ := by simp [Finset.sum_const]; ring

theorem realSize_zero (θ : InfFam D) : GlobalTheory.Unf.realSize θ (0 : Mx D m n) = 0 := by
  simp [GlobalTheory.Unf.realSize, compAt]

def finVec : Mx D m n →+ (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) where
  toFun x := fun i j => finPart D (x i j)
  map_zero' := by ext i j; exact (finPart D).map_zero
  map_add' a b := by ext i j; exact (finPart D).map_add _ _

theorem continuous_finVec : Continuous (finVec (D := D) (m := m) (n := n)) :=
  continuous_pi fun i => continuous_pi fun j =>
    (GlobalTheory.Member.continuous_finPart D).comp ((continuous_apply j).comp (continuous_apply i))

theorem pure (θ : InfFam D) (hθ : IsInfFam θ) (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
    (g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) :
    IsSchwartzBruhat fun x : Mx D m n => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j)) where
  level := by
    haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    haveI : IsTopologicalAddGroup (Af D.host.F ⊗[D.host.F] D.host.E) :=
      IsModuleTopology.topologicalAddGroup (Af D.host.F) _
    set P := (finVec : Mx D m n →+ (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) with hP
    refine ⟨(periods g).comap P, (isOpen_periods hg.1 hg.2).preimage continuous_finVec, fun u hu h0 x => ?_⟩
    have e1 : ∀ τ, compAt θ τ (x + u) = compAt θ τ x := fun τ => by
      rw [compAt_add]
      ext i j
      have h := congrFun (congrFun h0 i) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at h
      simp only [Matrix.add_apply, compAt, Matrix.map_apply, h, (θ τ).map_zero, add_zero]
    have e2 : (fun i j => finPart D ((x + u) i j)) = (fun i j => finPart D (x i j)) + P u :=
      P.map_add x u
    simp only [e1, e2]
    rw [show g ((fun i j => finPart D (x i j)) + P u) = g (fun i j => finPart D (x i j)) from hu _]
  supp := ⟨tsupport g, hg.2.isCompact, fun x hx => subset_tsupport g (right_ne_zero_of_mul hx)⟩
  schwartz := fun k L hL hi x => by
    obtain ⟨⟨C₁, hC₁⟩, hlow⟩ := GlobalTheory.T.adelicMatrixRealSize_bounds_along_real_parametrisation D θ hθ m n k L hL
    obtain ⟨C₂, hC₂⟩ := hlow hi
    have hAb : ∀ t, ‖realVec θ L t‖ ≤ C₁ * ‖t‖ := fun t => (norm_vec_le θ (L t)).trans (hC₁ t)
    have hAc : Continuous (realVec θ L) := AddMonoidHomClass.continuous_of_bound (realVec θ L) C₁ hAb
    set Al := (realVec θ L).toRealLinearMap hAc with hAl
    have hAlt : ∀ t, Al t = realVec θ L t := fun t => rfl
    have hker : (Al : (Fin k → ℝ) →ₗ[ℝ] (D.what₂.Tau → Fin m → Fin n → ℂ)).ker = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro t ht
      have h0 : realVec θ L t = 0 := by rw [← hAlt]; exact ht
      have h1 := hC₂ 0 t
      rw [zero_add, realSize_zero, add_zero] at h1
      have h2 := realSize_le θ (L t)
      have h3 : (fun τ i j => compAt θ τ (L t) i j : D.what₂.Tau → Fin m → Fin n → ℂ) = 0 := h0
      rw [h3, norm_zero, mul_zero] at h2
      have h4 : GlobalTheory.Unf.realSize θ (L t) = 0 := le_antisymm h2 (realSize_nonneg θ _)
      rw [h4, mul_zero] at h1
      exact norm_le_zero_iff.mp h1
    obtain ⟨K, -, hK⟩ := (Al : (Fin k → ℝ) →ₗ[ℝ] (D.what₂.Tau → Fin m → Fin n → ℂ)).exists_antilipschitzWith hker
    set a : D.what₂.Tau → Fin m → Fin n → ℂ := fun τ i j => compAt θ τ x i j with ha
    have hgr : Function.HasTemperateGrowth (fun t => a + Al t) :=
      (Function.HasTemperateGrowth.const a).add Al.hasTemperateGrowth
    have hanti : AntilipschitzWith K (fun t => a + Al t) :=
      AntilipschitzWith.of_le_mul_dist fun s t => by rw [dist_add_left]; exact hK.le_mul_dist s t
    refine ⟨g (fun i j => finPart D (x i j)) • SchwartzMap.compCLMOfAntilipschitz ℂ hgr hanti f, fun t => ?_⟩
    have e1 : (fun τ i j => compAt θ τ (x + L t) i j : D.what₂.Tau → Fin m → Fin n → ℂ) = a + Al t := by
      ext τ i j
      rw [hAlt, compAt_add]
      rfl
    have e2 : (fun i j => finPart D ((x + L t) i j)) = (fun i j => finPart D (x i j)) := by
      ext i j
      have h := congrFun (congrFun (hL.2 t) i) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at h
      rw [Matrix.add_apply, (finPart D).map_add, h, add_zero]
    simp only [e1, e2, SchwartzMap.smul_apply, SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply, smul_eq_mul]
    ring

theorem isSchwartzBruhat_of_mem_schwartzA : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ),
    ∀ φ ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n, GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ := by
  intro D θ hθ m n φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact pure θ hθ f g hg
  | zero => exact zero
  | add _ _ _ _ h1 h2 => exact add h1 h2
  | smul c _ _ h => exact smul c h

end GlobalTheory.SchwartzPure
