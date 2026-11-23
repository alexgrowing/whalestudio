import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmAdeleIdempotentOfPlacePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixComponentAtPlaceMemCompletedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceStable

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem symplO_of_place {p : Place D} {x y : WO S T} (hx : wAt p x = x) (hy : wAt p y = 0) : symplO S T x y = 0 := by
  rw [← hx, wAt_eq_smul, GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.2.1 p, ← wAt_eq_smul, hy,
    GlobalTheory.SplitScalar.symplO_zero_right]

theorem wAt_wAt (p : Place D) (w : WO S T) : wAt p (wAt p w) = wAt p w := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 p]

theorem wAt_wAt_ne {p q : Place D} (h : q ≠ p) (w : WO S T) : wAt q (wAt p w) = 0 := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 q p h, zero_smul]

theorem heisO_swap {u w : WO S T} (h : symplO S T u w = 0) (f : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T w f) = heisO ψ S T w (heisO ψ S T u f) := by
  rw [GlobalTheory.SplitScalar.heisO_comm, h, AddChar.map_zero_eq_one, one_smul]

theorem isLatVac_map {Λ : AddSubgroup (WO S T)} {A : (WO S T → ℂ) → WO S T → ℂ} {f : WO S T → ℂ}
    (h : ∀ u ∈ Λ, heisO ψ S T u (A f) = A (heisO ψ S T u f)) (hf : IsLatVac (heisO ψ S T) Λ f) :
    IsLatVac (heisO ψ S T) Λ (A f) :=
  ⟨fun u hu => by rw [h _ (Λ.nsmul_mem hu 2), hf.1 u hu], fun e he u hu hh => by rw [h u hu, hf.2 e he u hu hh]⟩

theorem latO_empty {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {P : FinPl D → Prop}
    (hP : ∀ v, ¬ P v) {u : WO S T} (hu : u ∈ latO S T LS LT P) : u = 0 := by
  have h : latO S T LS LT P ≤ ⊥ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro x ⟨α, -, h0, a, -, s, -, t, -, rfl⟩
    have hα : α = 0 := RestrictedProduct.ext _ _ fun v => h0 v (hP v)
    subst hα
    refine AddSubgroup.mem_bot.2 (Matrix.ext fun i j => ?_)
    exact TensorProduct.zero_tmul _ _
  exact AddSubgroup.mem_bot.1 (h hu)

theorem wAt_lineAt (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    wAt (.inr τ) (lineAt θ τ z t : WO S T) = lineAt θ τ z t := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, h1, h2⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  obtain ⟨-, -, -, -, h3, -, h4⟩ := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
  refine funext fun i => funext fun j => ?_
  show idem D (.inr τ) * lineAt θ τ z t i j = lineAt θ τ z t i j
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [← sub_eq_zero, ← RingHom.map_sub]
    refine GlobalTheory.FockCompare.ThetaCont.infPart_eq_zero hσ _ fun τ' => ?_
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, RingHom.map_mul]
    by_cases h : τ' = τ
    · subst h
      rw [(h4 θ hθ τ').1, one_mul, sub_self]
    · have h5 : θ τ' (infPart D (lineAt θ τ z t i j)) = 0 := by
        have := h2 t τ'
        rw [if_neg h] at this
        exact congrFun (congrFun this i) j
      rw [h5, mul_zero, sub_self]
  · have h5 : finPart D (lineAt θ τ z t i j) = 0 := congrFun (congrFun (h1 t) i) j
    rw [RingHom.map_mul, h5, mul_zero]

theorem dRho_heisO (hθ : IsInfFam θ) {τ : D.what₂.Tau} {w : WO S T} (hw : wAt (.inr τ) w = 0)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (heisO ψ S T w g) =
      heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g) := by
  funext x
  unfold Formalism.IndefR.Datum.dRho
  rw [heisO, ← deriv_const_mul_field]
  congr 1
  funext t
  rw [heisO_swap (symplO_of_place (wAt_lineAt hθ τ z t) hw)]
  rfl

theorem isFockVacAt_heisO (hθ : IsInfFam θ) {τ : D.what₂.Tau} {w : WO S T} (hw : wAt (.inr τ) w = 0)
    {J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ} {f : WO S T → ℂ}
    (hf : IsFockVacAt (heisO ψ S T) θ τ J f) : IsFockVacAt (heisO ψ S T) θ τ J (heisO ψ S T w f) := by
  intro z
  have h := congrArg (GlobalTheory.SplitScalar.heisL ψ S T w) (hf z)
  rw [annih, map_add, map_smul, map_zero] at h
  rw [annih, dRho_heisO hθ hw, dRho_heisO hθ hw]
  exact h

theorem heis_stable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ (q : Place D) (w : WO S T), wAt q w = 0 → VacAt ψ θ S T sS sT ΛS ΛT q f → VacAt ψ θ S T sS sT ΛS ΛT q (heisO ψ S T w f)) ∧ ∀ (p : Place D), IsLocal ψ θ S T sS sT ΛS ΛT p f → (∀ w : WO S T, IsLocal ψ θ S T sS sT ΛS ΛT p (heisO ψ S T (wAt p w) f)) ∧ (∀ (c : ℂ) g, IsLocal ψ θ S T sS sT ΛS ΛT p g → IsLocal ψ θ S T sS sT ΛS ΛT p (c • f + g)) ∧ ∀ τ : D.what₂.Tau, p = .inr τ → ∀ z, IsLocal ψ θ S T sS sT ΛS ΛT p (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
  intro D ψ θ S T sS sT ΛS ΛT hψ hθ f hf
  refine ⟨fun q w hw hv => ?_, fun p hp => ⟨fun w => ⟨GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _, ?_, fun τ hτ => ?_⟩,
    fun c g hg => ⟨GlobalTheory.WeilVacMove.isTheta_add (GlobalTheory.WeilVacMove.isTheta_smul c hf) hg.1, ?_, fun τ hτ z => ?_⟩,
    fun τ hτ z => ⟨GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ z hf, ?_, fun τ' hτ' z' => ?_⟩⟩⟩
  · cases q with
    | inl v =>
      refine isLatVac_map (fun u hu => heisO_swap (symplO_of_place ?_ hw) f) hv
      have h := (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu (.inl v)).2.1
      exact (sub_eq_zero.1 (latO_empty (fun v' h' => h'.2 (by rw [h'.1])) h)).symm
    | inr τ => exact isFockVacAt_heisO hθ hw hv
  · refine isLatVac_map (fun u hu => (heisO_swap (symplO_of_place (wAt_wAt p w) ?_) f).symm) hp.2.1
    exact (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu p).2.2 fun _ h => h
  · exact isFockVacAt_heisO hθ (wAt_wAt_ne hτ w) (hp.2.2 τ hτ)
  · have key : ∀ u, heisO ψ S T u f = f → heisO ψ S T u g = g → heisO ψ S T u (c • f + g) = c • f + g := fun u h1 h2 => by
      rw [← GlobalTheory.SplitScalar.heisL_apply, map_add, map_smul, GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply, h1, h2]
    exact ⟨fun u hu => key _ (hp.2.1.1 u hu) (hg.2.1.1 u hu),
      fun e he u hu hh => key _ (hp.2.1.2 e he u hu hh) (hg.2.1.2 e he u hu hh)⟩
  · have h1 := hp.2.2 τ hτ z
    have h2 := hg.2.2 τ hτ z
    have hc := GlobalTheory.WeilVacMove.isTheta_smul c hf
    rw [annih] at h1 h2 ⊢
    rw [GlobalTheory.FockIndep.dRho_add hψ hθ _ _ hc hg.1, GlobalTheory.FockIndep.dRho_add hψ hθ _ _ hc hg.1,
      GlobalTheory.FockIndep.dRho_smul hψ hθ _ _ c hf, GlobalTheory.FockIndep.dRho_smul hψ hθ _ _ c hf, smul_add, smul_comm,
      add_add_add_comm, ← smul_add, h1, h2, smul_zero, add_zero]
  · refine isLatVac_map (fun u hu => (dRho_heisO hθ ?_ z f).symm) hp.2.1
    exact (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu (.inr τ)).2.2 fun _ _ => Sum.inl_ne_inr
  · have hne : τ' ≠ τ := fun h => hτ' (by rw [h, hτ])
    have hc : ∀ y, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' y (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) =
        Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' y f) := fun y => by
      rw [GlobalTheory.FockIndep.dRho_comm hψ hθ τ' y τ z hf, GlobalTheory.FockIndep.omDir, if_neg hne, Complex.ofReal_zero, mul_zero,
        zero_smul, zero_add]
    have ht := fun y => GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ' y hf
    have h1 := hp.2.2 τ' hτ' z'
    have h0 := GlobalTheory.FockIndep.dRho_smul hψ hθ τ z 0 hf
    rw [zero_smul, zero_smul] at h0
    rw [annih] at h1 ⊢
    rw [hc, hc, ← GlobalTheory.FockIndep.dRho_smul hψ hθ τ z _ (ht _),
      ← GlobalTheory.FockIndep.dRho_add hψ hθ τ z (ht _) (GlobalTheory.WeilVacMove.isTheta_smul _ (ht _)), h1, h0]

end GlobalTheory.PlaceStable

end
