import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspLie

theorem hasDerivAt_constTermOn {G : Type} [Group G] [TopologicalSpace G] {Γ N : Subgroup G} [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ] [LocallyCompactSpace N]
    (hc : Cocompact Γ N) {φ ψ : G → ℂ} (hφ : LeftInv Γ φ) (hφc : Continuous φ) (hψ : LeftInv Γ ψ) (hψc : Continuous ψ)
    {u : ℝ → G} (hu : Continuous u) (hd : ∀ g t, HasDerivAt (fun s => φ (g * u s)) (ψ (g * u t)) t) (x : G) :
    HasDerivAt (fun s => constTermOn Γ N φ (x * u s)) (constTermOn Γ N ψ (x * u 0)) 0 := by
  have := hc.isProbabilityMeasure
  obtain ⟨K, hK, hs⟩ := id hc
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall (0 : ℝ) 1)).exists_bound_of_continuousOn
    (f := fun p : N × ℝ => ψ (p.1 * (x * u p.2))) (by fun_prop)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := probMeasure Γ N) (bound := fun _ => C)
    (F := fun s q => φ ((q.out : N) * (x * u s))) (F' := fun s q => ψ ((q.out : N) * (x * u s)))
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) (.of_forall fun s => (hc.integrable hφ hφc _).1) (hc.integrable hφ hφc _)
    (hc.integrable hψ hψc _).1 (.of_forall fun q s hs' => ?_) (integrable_const C) (.of_forall fun q s _ => ?_)).2
  · obtain ⟨γ, hγ, hk⟩ := hs q.out
    exact (congrArg norm (leftInv_integrand hψ (x * u s) γ hγ q.out)).ge.trans
      (hC (_, s) ⟨hk, Metric.ball_subset_closedBall hs'⟩)
  · simpa only [mul_assoc] using hd ((q.out : N) * x) s

variable {D : D7} {θ : InfF D} {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} {φ : GA D V → ℂ}

theorem gelf_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (hφ : φ ∈ SmFun θ V) (τ' : D.what₂.Tau) (k : ℕ) :
    gelf θ V τ' k (Rder θ V τ X φ) = Rder θ V τ X (gelf θ V τ' k φ) := by
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  obtain ⟨c, hc, hg⟩ := GlobalTheory.SmoothForms.exists_gelf R τ'
  let ψ : GlobalTheory.SmoothForms.SmF θ V := ⟨φ, (GlobalTheory.SmoothForms.smooth_iff R φ).1 hφ⟩
  let X' : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X, hX⟩
  have e : ∀ f : GlobalTheory.SmoothForms.SmF θ V, Rder θ V τ X f.1 =
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ X') f).1 := fun f => GlobalTheory.SmoothForms.Rder_eq R τ X' f.1
  have hcomm : Commute (GlobalTheory.SmoothForms.envRep R τ' (c k))
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ X')) := by
    rw [← GlobalTheory.SmoothForms.envRep_ι]
    by_cases h : τ' = τ
    · subst h
      have hm : c k ∈ Subalgebra.center ℂ _ := hc ▸ Algebra.subset_adjoin ⟨k, rfl⟩
      exact Commute.map (Subalgebra.mem_center_iff.1 hm _).symm _
    · exact GlobalTheory.SmoothForms.envRep_comm R h _ _
  change gelf θ V τ' k (Rder θ V τ X ψ.1) = Rder θ V τ X (gelf θ V τ' k ψ.1)
  rw [e ψ, hg, hg, e]
  exact congrArg (fun S : Module.End ℂ (GlobalTheory.SmoothForms.SmF θ V) => (S ψ).1) hcomm.eq

theorem fg_comap {W : Submodule ℂ (GA D V → ℂ)} (hW : FiniteDimensional ℂ W) :
    (W.comap (SmFun θ V).subtype).FG :=
  Module.Finite.iff_fg.1 (FiniteDimensional.of_injective ((SmFun θ V).subtype.restrict (q := W) fun _ hx => hx)
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : W => z.1) h)))

theorem derEnd_coe (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (f : SmFun θ V) : (derEnd hθ τ X f).1 = Rder θ V τ X f.1 :=
  GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hX f.1

theorem isAutFunSm_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (h : IsAutFunSm θ V φ) :
    IsAutFunSm θ V (Rder θ V τ X φ) := by
  refine { left := fun γ hγ => GlobalTheory.Mem.Lift.Rder_left (h.left γ hγ) τ X, level := ?_, cont := ?_,
           smooth := Rder_mem h.smooth hX, zfin := ?_, growth := ?_ }
  · obtain ⟨U, hU, e⟩ := h.level
    refine ⟨U, hU, fun k hk hf g => ?_⟩
    have := congrFun (GlobalTheory.Mem.FinTranslate.Rder_rTr (θ := θ) hf τ X φ) g
    rw [show rTr V k φ = φ from funext (e k hk hf)] at this
    exact this.symm
  · exact GlobalTheory.Size.continuous_rWord hθ h.smooth h.cont (GlobalTheory.Grow.unifModGrowth_of_isAutFunSm hθ h) (l := [(τ, X)])
      fun p hp => by rw [List.mem_singleton.1 hp]; exact hX
  · obtain ⟨W, hW, m, s⟩ := h.zfin
    refine ⟨((W.comap (SmFun θ V).subtype).map (derEnd hθ τ X)).map (SmFun θ V).subtype,
      Module.Finite.iff_fg.2 (((fg_comap hW).map _).map _),
      ⟨_, ⟨⟨φ, h.smooth⟩, m, rfl⟩, derEnd_coe hθ hX _⟩, ?_⟩
    rintro τ' k _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨_, ⟨⟨_, (linOnSm_gelf τ' k).mem _ f.2⟩, s τ' k _ hf, rfl⟩, ?_⟩
    rw [Submodule.subtype_apply, Submodule.subtype_apply, derEnd_coe hθ hX, derEnd_coe hθ hX, gelf_Rder hθ hX f.2]
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using
      hN (l ++ [(τ, X)]) (GlobalTheory.Mem.Lift.append_mem_lie hl hX) x

theorem isKFinite_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) {K : Subgroup (GA D V)} (hK : K ≤ GinfC V)
    (hs : φ ∈ SmFun θ V) (h : GlobalTheory.Doubling.IsKFinite K φ) : GlobalTheory.Doubling.IsKFinite K (Rder θ V τ X φ) := by
  obtain ⟨W, hW, m⟩ := GlobalTheory.Doubling.isKFinite_iff.1 h
  refine GlobalTheory.Doubling.isKFinite_iff.2
    ⟨(Submodule.map₂ (derEnd hθ τ) ⊤ (W.comap (SmFun θ V).subtype)).map (SmFun θ V).subtype,
      Module.Finite.iff_fg.2 ((Submodule.FG.map₂ _ Module.Finite.fg_top (fg_comap hW)).map _), fun k hk => ?_⟩
  have hr : ∀ k ∈ K, IsRealPt θ k := fun k hk => ⟨hK hk, FockCompare.RealAction.infMat_mem_UH hθ V k⟩
  have hi := hr _ (inv_mem hk)
  refine ⟨_, Submodule.apply_mem_map₂ _ (Submodule.mem_top (x := adAt θ k⁻¹ τ X))
    (n := ⟨rTr V k φ, rTr_mem hθ (hr k hk) hs⟩) (m k hk), ?_⟩
  rw [Submodule.subtype_apply, derEnd_coe hθ (adAt_mem hi hX)]
  funext g
  have := congrFun (Rder_rTr hθ hi hX (rTr V k φ)) (g * k)
  rw [show rTr V k⁻¹ (rTr V k φ) = φ from funext fun y => by simp [rTr]] at this
  rw [this, rTr, mul_inv_cancel_right]

theorem isCuspFun_Rder (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) :
    IsCuspFun V (Rder θ V τ X φ) := by
  have h' := isAutFunSm_Rder hθ hX h
  refine (isCuspFun_iff h'.left).2 fun W hW => funext fun x => ?_
  have h0 : constTermOn (GQ V) (NA (.single hW)) φ = 0 := (isCuspFun_iff h.left).1 hc W hW
  have := hasDerivAt_constTermOn (cocompact_single hW) h.left h.cont h'.left h'.cont (GlobalTheory.Mem.Lift.continuous_oneP hθ hX)
    (GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder h.smooth hX)) x
  rw [h0, GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at this
  exact this.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))

theorem rder_mem_autForms_cuspForms : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (K : Subgroup (GA D V)), K ≤ GinfC V → ∀ τ, ∀ X ∈ lieAt V τ, (∀ φ ∈ autForms θ V K, Rder θ V τ X φ ∈ autForms θ V K) ∧ ∀ φ ∈ cuspForms θ V K, Rder θ V τ X φ ∈ cuspForms θ V K := by
  intro D θ hθ V K hK τ X hX
  refine ⟨fun φ h => ⟨isAutFunSm_Rder hθ hX h.1, isKFinite_Rder hθ hX hK h.1.smooth h.2⟩, fun φ h => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_cuspForms.1 h
  exact mem_cuspForms.2 ⟨⟨isAutFunSm_Rder hθ hX h1, isCuspFun_Rder hθ hX h1 h2⟩, isKFinite_Rder hθ hX hK h1.smooth h3⟩

end GlobalTheory.CuspLie

end
