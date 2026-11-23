import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Ker (ipO)
open GlobalTheory.OrientedHeis GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.ThetaSquare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}

theorem cocompact (V W : HSp D) : Cocompact V W := by
  obtain ⟨-, -, -, -, -, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have h := hK.image (QuotientAddGroup.continuous_mk (N := (ratL W V : AddSubgroup (WO V W))))
  refine ⟨(Set.eq_univ_of_forall fun q => ?_ : _ = Set.univ) ▸ h⟩
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨γ, hγ, hk⟩ := hc w
  exact ⟨_, hk, QuotientAddGroup.eq.2 (by simpa using hγ)⟩

theorem symplOH_zero_right (w : WO V W) : symplOH V W w 0 = 0 := by
  have := symplOH_add_right w 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem symplOH_zero_left (w : WO V W) : symplOH V W 0 w = 0 := by
  have := symplOH_add_left 0 0 w
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem symplOH_neg_self (u : WO V W) : symplOH V W (-u) u = 0 := by
  have := symplOH_add_left (-u) u u
  rwa [neg_add_cancel, symplOH_zero_left, symplOH_self, add_zero, eq_comm] at this

theorem squareIntegrable (hψ : IsStdChar D ψ (-1)) : SquareIntegrable ψ V W :=
  fun _ h => ⟨theta_norm_periodic hψ h, theta_bounded hψ h, fun _ _ hμ h𝓕 => GlobalTheory.Size.memLp_theta hψ hμ h𝓕 h⟩

theorem heisUnitary (hψ : IsStdChar D ψ (-1)) : HeisUnitary ψ V W := by
  refine ⟨heisO_heisO, fun u f => ?_, fun u f h => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ h u,
    fun _ _ hμ h𝓕 u _ _ h h' => GlobalTheory.Size.ipO_heisO hψ hμ h𝓕 h h' u, ?_⟩
  · rw [heisO_heisO, symplOH_neg_self, ψ.map_zero_eq_one, one_smul, neg_add_cancel, heisO_zero]
  · rintro _ ⟨γ, rfl⟩ f h
    have e := h.quasi γ 0
    rw [symplOH_zero_right, neg_zero, ψ.map_zero_eq_one, one_mul, add_zero] at e
    change ψ (symplOH V W 0 (ratW W V γ)) * f (0 + ratW W V γ) = f 0
    rw [symplOH_zero_left, ψ.map_zero_eq_one, one_mul, zero_add, e]

theorem norm_heisO (hψ : IsStdChar D ψ (-1)) (u : WO V W) (f : WO V W → ℂ) (x : WO V W) :
    ‖heisO ψ V W u f x‖ = ‖f (x + u)‖ := by
  rw [heisO, norm_mul, hψ.1.2.1, one_mul]

theorem ipO_dLine (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {L : ℝ →+ WO V W} (hL : IsRealDir W V L)
    {μ : Measure (WO V W)} {𝓕 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ)
    {f f' : WO V W → ℂ} (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') :
    ipO μ 𝓕 (dLine ψ V W L f) f' = -ipO μ 𝓕 f (dLine ψ V W L f') := by
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (GlobalTheory.Size.measure_dom hμ h𝓕).2
  have hd := theta_dLine hθ hψ hL h
  have hd' := theta_dLine hθ hψ hL h'
  have hI := fun {g g'} => GlobalTheory.Size.integrableOn_mul_conj (f := g) (f' := g') hψ hμ h𝓕
  have hT := fun {g} (hg : IsThetaFunO ψ V W g) t => theta_heisO_real hθ hψ (hL.2 t) hg
  obtain ⟨a, ha⟩ := theta_bounded hψ h
  obtain ⟨b, hb⟩ := theta_bounded hψ h'
  obtain ⟨c, hc⟩ := theta_bounded hψ hd
  obtain ⟨d, hd0⟩ := theta_bounded hψ hd'
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (𝕜 := ℝ) (x₀ := (0 : ℝ))
    (s := Set.univ) (bound := fun _ => c * b + a * d)
    (F := fun t x => heisO ψ V W (L t) f x * conj (heisO ψ V W (L t) f' x))
    (F' := fun t x => heisO ψ V W (L t) (dLine ψ V W L f) x * conj (heisO ψ V W (L t) f' x) +
      heisO ψ V W (L t) f x * conj (heisO ψ V W (L t) (dLine ψ V W L f') x))
    Filter.univ_mem
    (.of_forall fun t => (hI (hT h t) (hT h' t)).aestronglyMeasurable)
    (hI (hT h 0) (hT h' 0))
    ((hI (hT hd 0) (hT h' 0)).add (hI (hT h 0) (hT hd' 0))).aestronglyMeasurable
    (.of_forall fun x t _ => by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
        rw [norm_mul, Complex.norm_conj, norm_heisO hψ, norm_heisO hψ]
      · exact mul_le_mul (hc _) (hb _) (norm_nonneg _) ((norm_nonneg _).trans (hc 0))
      · exact mul_le_mul (ha _) (hd0 _) (norm_nonneg _) ((norm_nonneg _).trans (ha 0)))
    (integrable_const _)
    (.of_forall fun x t _ =>
      (hasDerivAt_heisO hθ hψ hL h x t).mul (hasDerivAt_heisO hθ hψ hL h' x t).star)).2
  have e : (fun t => ∫ x in 𝓕, heisO ψ V W (L t) f x * conj (heisO ψ V W (L t) f' x) ∂μ) = fun _ => ipO μ 𝓕 f f' :=
    funext fun t => GlobalTheory.Size.ipO_heisO hψ hμ h𝓕 h h' (L t)
  rw [e] at key
  have k := key.unique (hasDerivAt_const _ _)
  simp only [map_zero, heisO_zero] at k
  rw [integral_add (hI hd h') (hI h hd')] at k
  exact eq_neg_of_add_eq_zero_left k

theorem derSkew (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) : DerSkew ψ θ V W := by
  intro τ z
  have hL := isRealDir_lineAt (S := V) (T := W) hθ τ z
  refine ⟨fun f h x => ?_, fun f h => theta_dRho hθ hψ τ z h, fun μ 𝓕 hμ h𝓕 f f' h h' => ipO_dLine hψ hθ hL hμ h𝓕 h h'⟩
  exact (hasDerivAt_heisO hθ hψ hL h x 0).differentiableAt.hasDerivAt

theorem commScalar_eq (τ τ' : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ) :
    commScalar V W τ τ' z w = -(2 * Real.pi * Complex.I) * (GlobalTheory.FockIndep.omDir V W τ z τ' w : ℝ) := by
  unfold commScalar GlobalTheory.FockIndep.omDir
  split_ifs
  · rfl
  · simp

theorem symplO_eq (x y : WO V W) : symplO V W x y = symplOH V W x y + symplOH V W x y := by
  rw [symplOH, ← add_mul, ← map_add, add_halves, map_one, one_mul]

theorem derComm (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) : DerComm ψ θ V W := by
  intro τ τ' z w
  rw [commScalar_eq]
  refine ⟨fun s t => ?_, fun f h => sub_eq_of_eq_add (GlobalTheory.FockIndep.dRho_comm hψ hθ τ z τ' w h)⟩
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e := (smooth_iff_sm_and_real_lines D θ σ h W V).2.1
  rw [symplO_eq, AddChar.map_add_eq_mul, e _ (isRealDir_lineAt hθ τ z) s, e _ (isRealDir_lineAt hθ τ' w) t,
    psi_symplOH h hψ, h.pi_iota, LinearMap.map_smul₂, map_smul, GlobalTheory.FockIndep.piW_lineAt hθ,
    GlobalTheory.FockIndep.piW_lineAt hθ, GlobalTheory.FockIndep.omO_single, ← Complex.exp_add]
  congr 1
  simp only [smul_eq_mul]
  push_cast
  ring

theorem finRealComm (hθ : IsInfFam θ) : FinRealComm ψ θ V W := by
  refine fun u hu => ⟨fun v hv f => ?_, fun τ z f _ => (GlobalTheory.FinTranslate.dRho_heisO hθ hu τ z f).symm⟩
  rw [heisO_heisO, heisO_heisO, (symplOH_fin_real hu hv).1, (symplOH_fin_real hu hv).2, add_comm]

theorem theta_square_integrable (D : D7) : ThetaSquareIntegrable D :=
  fun V W => ⟨cocompact V W, fun _ hψ => ⟨squareIntegrable hψ, heisUnitary hψ,
    fun _ hθ => ⟨derSkew hψ hθ, derComm hψ hθ, finRealComm hθ⟩⟩⟩

end GlobalTheory.ThetaSquare

end
