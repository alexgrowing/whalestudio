import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapValuesCompactSobolevBound
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TprodEqZeroOfKFinOff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepPer.KFinPer

open Formalism.MainNotions.S
open scoped Classical

variable {D : D7}

theorem isMultMap_bound (hP : GlobalTheory.Published.CuspRapidDecay) (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M)
    (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ Y ∈ l, Y ∈ lieAt V τ) ∧
      ∀ w : M.sm τ, ∀ g, ‖T (Function.update v τ w) g‖ ≤
        C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hσ : IsURepOn (UJset (M.ε τ)) (M.σ τ) := (M.ds τ).2.2.1
  have hPu := M.fr_unit τ
  have hG := M.fr_gram τ
  choose ℓ hℓ hℓT using fun g : GA D V => hT.cont τ v g
  have hsm : ∀ u : M.H τ, SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) u → u ∈ M.sm τ := fun u hu =>
    Submodule.subset_span ((GlobalTheory.SmoothCyclic.smoothVec_transport hPu hG u).2 hu)
  obtain ⟨L, C, hL, hC⟩ := GlobalTheory.SobUnif.unif_model hσ ℓ
    (fun g => GlobalTheory.SmoothCyclic.sobCont_transport hPu hG (hℓ g))
    (fun u hu => by
      obtain ⟨B, hB⟩ := GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hT.aut (Function.update v τ ⟨u, hsm u hu⟩))
        (hT.cusp (Function.update v τ ⟨u, hsm u hu⟩))
      exact ⟨B, fun g => by rw [hℓT g ⟨u, hsm u hu⟩]; exact hB g⟩)
  refine ⟨L.map fun l => l.map fun X => (M.fr τ)⁻¹ * X * M.fr τ, C, ?_, fun w g => ?_⟩
  · intro l hl Y hY
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.1 hl
    obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hY
    exact GlobalTheory.SmoothCyclic.conj_lie (Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hPu)) hG
      (hL l0 hl0 X hX)
  · have hw := (GlobalTheory.SmoothCyclic.smoothVec_transport hPu hG (w : M.H τ)).1
      (GlobalTheory.HolRead.MultDer.smoothVec_of_mem M τ w.2)
    have h1 := hC g (w : M.H τ) hw
    rw [hℓT g w] at h1
    refine h1.trans_eq ?_
    congr 1
    rw [GlobalTheory.SmoothGlob.sobNorm, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun l _ => ?_)
    exact congrArg norm (GlobalTheory.SobUnif.foldr_conj_eq (M.σ τ) hPu l (w : M.H τ)).symm

theorem mult_bound (hP : GlobalTheory.Published.CuspRapidDecay) (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) {T : MMap M}
    (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ Y ∈ l, Y ∈ lieAt V τ) ∧
      ∀ w : M.sm τ, ∀ g, ‖T (Function.update v τ w) g‖ ≤
        C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact isMultMap_bound hP θ hθ M J χ T hT τ v
  | zero => exact ⟨[], 0, by simp, fun w g => by simp⟩
  | add T₁ T₂ _ _ h₁ h₂ =>
    obtain ⟨L₁, C₁, hL₁, hb₁⟩ := h₁
    obtain ⟨L₂, C₂, hL₂, hb₂⟩ := h₂
    refine ⟨L₁ ++ L₂, max C₁ 0 + max C₂ 0, fun l hl => ?_, fun w g => ?_⟩
    · rcases List.mem_append.1 hl with h | h
      exacts [hL₁ l h, hL₂ l h]
    · set s₁ := (L₁.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum
      set s₂ := (L₂.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum
      have hs₁ : 0 ≤ s₁ := List.sum_nonneg fun x hx => by
        obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      have hs₂ : 0 ≤ s₂ := List.sum_nonneg fun x hx => by
        obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      rw [List.map_append, List.sum_append, MultilinearMap.add_apply, Pi.add_apply]
      calc _ ≤ ‖T₁ (Function.update v τ w) g‖ + ‖T₂ (Function.update v τ w) g‖ := norm_add_le _ _
        _ ≤ C₁ * s₁ + C₂ * s₂ := add_le_add (hb₁ w g) (hb₂ w g)
        _ ≤ max C₁ 0 * s₁ + max C₂ 0 * s₂ :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hs₁)
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hs₂)
        _ ≤ (max C₁ 0 + max C₂ 0) * (s₁ + s₂) := by
          have := le_max_right C₁ 0; have := le_max_right C₂ 0; nlinarith
  | smul c T _ h =>
    obtain ⟨L, C, hL, hb⟩ := h
    refine ⟨L, ‖c‖ * C, hL, fun w g => ?_⟩
    rw [MultilinearMap.smul_apply, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb w g) (norm_nonneg _)

theorem per_eq_zero_of_kF : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ y ∈ MultT θ M J χ, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (e : X → GA D V) (u : X → ℂ), Measurable e → Integrable u ν → (∀ a ∈ KF M, ∫ x, y a (e x) * u x ∂ν = 0) → ∀ a, ∫ x, y a (e x) * u x ∂ν = 0 := by
  intro hP hHC D θ hθ V S M J χ y hy X _ ν e u he hu h0 a
  have : BorelSpace (GA D V) := ⟨rfl⟩
  set T' : MMap M := PiTensorProduct.lift.symm y with hT'
  have hT'm : T' ∈ Mult θ M J χ := (mem_multT θ M J χ y).1 hy
  have hTt : ∀ w : M.Vec, y (PiTensorProduct.tprod ℂ w) = T' w := by
    intro w
    have : y = PiTensorProduct.lift T' := by rw [hT']; exact (PiTensorProduct.lift.apply_symm_apply y).symm
    rw [this, PiTensorProduct.lift.tprod]
  have hval : ∀ b, Continuous (y b) ∧ ∃ B : ℝ, ∀ g, ‖y b g‖ ≤ B := by
    intro b
    obtain ⟨h1, h2, -⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP D V S M θ hθ J χ y hy b
    exact ⟨h1.cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ h1 h2⟩
  have hint : ∀ b, Integrable (fun x => y b (e x) * u x) ν := by
    intro b
    obtain ⟨hc, B, hB⟩ := hval b
    have hm : AEStronglyMeasurable (fun x => y b (e x)) ν :=
      (hc.measurable.comp he).aestronglyMeasurable
    first
      | exact hu.bdd_mul hm ⟨B, fun x => hB (e x)⟩
      | exact hu.bdd_mul hm (Filter.Eventually.of_forall fun x => hB (e x))
  let Λ : SmT M →ₗ[ℂ] ℂ :=
    { toFun := fun b => ∫ x, y b (e x) * u x ∂ν
      map_add' := fun b c => by
        simp only [map_add, Pi.add_apply, add_mul]
        exact integral_add (hint b) (hint c)
      map_smul' := fun c b => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ }
  have hsep : GlobalTheory.Core.Mi.SepCont M Λ := by
    intro τ v
    obtain ⟨L, Cu, hL, hb⟩ := mult_bound hP θ hθ M J χ hT'm τ v
    let ℓ₀ : M.sm τ →ₗ[ℂ] ℂ := (Λ.compMultilinearMap (PiTensorProduct.tprod ℂ)).toLinearMap v τ
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
    have hℓw : ∀ w : M.sm τ, ℓ w = Λ (PiTensorProduct.tprod ℂ (Function.update v τ w)) := by
      intro w
      have := congrArg (fun m => m w) hℓ
      simpa [ℓ₀, MultilinearMap.toLinearMap_apply] using this
    refine ⟨ℓ, ⟨L, Cu * ∫ x, ‖u x‖ ∂ν, hL, fun w hw => ?_⟩, hℓw⟩
    have hw' : w ∈ M.sm τ := Submodule.subset_span hw
    rw [hℓw ⟨w, hw'⟩]
    change ‖∫ x, y (PiTensorProduct.tprod ℂ (Function.update v τ ⟨w, hw'⟩)) (e x) * u x ∂ν‖ ≤ _
    rw [hTt]
    set s := (L.map fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum
    have hpt : ∀ x, ‖T' (Function.update v τ ⟨w, hw'⟩) (e x) * u x‖ ≤ Cu * s * ‖u x‖ := by
      intro x
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb ⟨w, hw'⟩ (e x)) (norm_nonneg _)
    calc _ ≤ ∫ x, Cu * s * ‖u x‖ ∂ν :=
          norm_integral_le_of_norm_le (hu.norm.const_mul _) (Filter.Eventually.of_forall hpt)
      _ = Cu * s * ∫ x, ‖u x‖ ∂ν := integral_const_mul _ _
      _ = _ := by ring
  have hΛ : Λ = 0 := GlobalTheory.Core.Mi.eq_zero_of_sepCont hHC D V S M Λ hsep fun v hv =>
    h0 _ (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv τ), rfl⟩)
  exact congrArg (fun L : SmT M →ₗ[ℂ] ℂ => L a) hΛ

end GlobalTheory.SepPer.KFinPer
