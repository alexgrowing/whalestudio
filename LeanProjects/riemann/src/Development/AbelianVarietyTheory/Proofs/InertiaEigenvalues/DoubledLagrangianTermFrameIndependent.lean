import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntegrandPeriodic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift

variable {D : D7}

theorem ratMul_ratMul {m : ℕ} {a c : ℕ} (c₁ : Matrix (Fin a) (Fin m) D.host.E) (c₂ : Matrix (Fin m) (Fin m) D.host.E)
    (u : Mx D m c) : ratMul c₁ (ratMul c₂ u) = ratMul (c₁ * c₂) u := by
  unfold ratMul
  rw [Matrix.map_mul, Matrix.mul_assoc]

theorem covolOne_integral_ratMul {m n : ℕ} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (hμ : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) μ 𝓕) (c c' : Matrix (Fin m) (Fin m) D.host.E) (h1 : c' * c = 1)
    (h2 : c * c' = 1) (φ : Mx D m n → ℂ) (hφ : ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∀ a, φ (γ + a) = φ a) :
    ∫ a in 𝓕, φ (ratMul c a) ∂μ = ∫ a in 𝓕, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  have hl : ∀ a : Mx D m n, ratMul c' (ratMul c a) = a := fun a => by
    rw [ratMul_ratMul, h1, ratMul_one]
  have hr : ∀ a : Mx D m n, ratMul c (ratMul c' a) = a := fun a => by
    rw [ratMul_ratMul, h2, ratMul_one]
  have mem : ∀ (d : Matrix (Fin m) (Fin m) D.host.E) (g : GlobalTheory.MixModel.ratMx D m n),
      ratMul d (g : Mx D m n) ∈ GlobalTheory.MixModel.ratMx D m n := fun d g =>
    GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem d) g.2
  let A : Mx D m n ≃+ Mx D m n :=
    { toFun := fun a => ratMul c a
      invFun := fun a => ratMul c' a
      left_inv := hl
      right_inv := hr
      map_add' := fun a b => Matrix.mul_add _ _ _ }
  let L : Mx D m n ≃ₜ+ Mx D m n :=
    { A with
      continuous_toFun := continuous_const.matrix_mul continuous_id
      continuous_invFun := continuous_const.matrix_mul continuous_id }
  let e : Mx D m n ≃ᵐ Mx D m n := L.toHomeomorph.toMeasurableEquiv
  haveI := hμ.1
  have hH : (μ.map e).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  have hmp : MeasurePreserving e μ (μ.map e) := e.measurable.measurePreserving μ
  let r : GlobalTheory.MixModel.ratMx D m n ≃ GlobalTheory.MixModel.ratMx D m n :=
    { toFun := fun g => ⟨ratMul c' (g : Mx D m n), mem c' g⟩
      invFun := fun g => ⟨ratMul c (g : Mx D m n), mem c g⟩
      left_inv := fun g => Subtype.ext (hr _)
      right_inv := fun g => Subtype.ext (hl _) }
  have hcov : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) (μ.map e) (e '' 𝓕) := by
    refine ⟨hH, ?_, ?_⟩
    · refine hμ.2.1.image_of_equiv e.toEquiv (hmp.symm e).quasiMeasurePreserving r fun g a => ?_
      show ratMul c (ratMul c' (g : Mx D m n) + a) = (g : Mx D m n) + ratMul c a
      unfold ratMul
      rw [Matrix.mul_add]
      congr 1
      exact hr _
    · rw [e.map_apply, e.preimage_image]; exact hμ.2.2
  have h := GlobalTheory.MixModel.covolOne_integral_eq hμ hcov φ hφ
  rw [setIntegral_map_equiv, e.preimage_image] at h
  exact h

theorem exists_frame_change {W : HSp D} {Y : Lag W}
    {C C' : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hC : IsLagFrame W Y C) (hC' : IsLagFrame W Y C') :
    ∃ c c' : Matrix (Fin W.rank) (Fin W.rank) D.host.E,
      C'.1 = C.1 * c ∧ C'.2 = C.2 * c ∧ c * c' = 1 ∧ c' * c = 1 := by
  have mem : ∀ {C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E},
      IsLagFrame W Y C → ∀ j, ((fun a => C.1 a j), (fun a => C.2 a j)) ∈ Y.1 :=
    fun h j => h ▸ Submodule.subset_span ⟨j, rfl⟩
  let v : ∀ C, IsLagFrame W Y C → Fin W.rank → Y.1 := fun C h j => ⟨_, mem h j⟩
  have sp : ∀ C (h : IsLagFrame W Y C), ⊤ ≤ Submodule.span D.host.E (Set.range (v C h)) := by
    intro C h
    refine le_of_eq (Submodule.map_injective_of_injective Y.1.injective_subtype ?_).symm
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact h
  have li : ∀ C (h : IsLagFrame W Y C), LinearIndependent D.host.E (v C h) := fun C h =>
    linearIndependent_of_top_le_span_of_card_eq_finrank (sp C h) (by rw [Fintype.card_fin, Y.2.1])
  let b := Module.Basis.mk (li C hC) (sp C hC)
  let b' := Module.Basis.mk (li C' hC') (sp C' hC')
  have hb : ∀ j, (b j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) = ((fun a => C.1 a j), (fun a => C.2 a j)) :=
    fun j => by simp [b, v]
  have hb' : ∀ j, (b' j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) = ((fun a => C'.1 a j), (fun a => C'.2 a j)) :=
    fun j => by simp [b', v]
  have key : ∀ j, (b' j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) =
      ∑ i, b.toMatrix b' i j • (b i : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) := fun j => by
    have := congrArg Subtype.val (b.sum_repr (b' j))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    simp only [Module.Basis.toMatrix_apply]
    exact this.symm
  refine ⟨b.toMatrix b', b'.toMatrix b, ?_, ?_, Module.Basis.toMatrix_mul_toMatrix_flip b b', Module.Basis.toMatrix_mul_toMatrix_flip b' b⟩
  · refine Matrix.ext fun a j => ?_
    have := congrArg (fun y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E) => y.1 a) (key j)
    simp only [hb, hb', Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · refine Matrix.ext fun a j => ?_
    have := congrArg (fun y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E) => y.2 a) (key j)
    simp only [hb, hb', Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem lagTerm_frame_indep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → IsStdChar D ψ (-1) → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ (Y : Lag W) C C', IsLagFrame W Y C → IsLagFrame W Y C' → lagTerm μ 𝓕 C f₁ f₂ = lagTerm μ 𝓕 C' f₁ f₂ := by
  intro D ψ V W μ 𝓕 hμ hψ f₁ f₂ h₁ h₂ Y C C' hC hC'
  obtain ⟨c, c', e1, e2, hcc, hc'c⟩ := exists_frame_change hC hC'
  have hψ' : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  unfold lagTerm
  rw [e1, e2]
  simp only [← ratMul_ratMul]
  refine (covolOne_integral_ratMul (m := W.rank) (n := V.rank) hμ c c' hc'c hcc
    (fun u => f₁ (ratMul C.1 u) * star (f₂ (ratMul C.2 u))) ?_).symm
  rintro _ ⟨γ, rfl⟩ a
  exact GlobalTheory.RawLift.Model.integrand_periodic hψ' hC h₁ h₂ γ a

end GlobalTheory.RawLift

end
