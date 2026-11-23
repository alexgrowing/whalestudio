import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KerReal

open GlobalTheory.FockCompare

variable {D : D7}

theorem infPart_eq_zero {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ) (a : AE D)
    (ha : ∀ τ, θ τ (infPart D a) = 0) : infPart D a = 0 := by

  let e0 : AF D.host.F := ((1 : Ainf D.host.F), (0 : Af D.host.F))
  let e : AE D := e0 ⊗ₜ[D.host.F] (1 : D.host.E)
  have hi : infPart D e = 1 := by
    simp only [infPart, e, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq]
    rfl
  have hf : finPart D e = 0 := by
    simp only [finPart, e, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq]
    exact TensorProduct.zero_tmul _ _
  have he : e * a = 0 :=
    h.ext _ (by rw [map_mul, hf, zero_mul]) fun τ => by rw [map_mul, hi, one_mul]; exact ha τ
  calc infPart D a = infPart D (e * a) := by rw [map_mul, hi, one_mul]
    _ = 0 := by rw [he, map_zero]

variable {S T : HSp D}

def realOf (C : Ctx S T) (σ : (D.what₂.Tau → ℂ) →+ AE D) : WR C.X S.rank →+ WO S T where
  toFun v := Matrix.of fun a k => σ fun τ => conj (v (C.m.e τ) k a)
  map_zero' := by
    funext a k
    have : (fun τ : D.what₂.Tau => conj ((0 : WR C.X S.rank) (C.m.e τ) k a)) = 0 := by
      funext τ; simp
    show σ _ = 0
    rw [this, σ.map_zero]
  map_add' x y := by
    funext a k
    have : (fun τ : D.what₂.Tau => conj ((x + y) (C.m.e τ) k a)) =
        (fun τ => conj (x (C.m.e τ) k a)) + fun τ => conj (y (C.m.e τ) k a) := by
      funext τ; simp
    show σ _ = σ _ + σ _
    rw [this, σ.map_add]

theorem realPt_apply (C : Ctx S T) (w : WO S T) (s : C.X.Ψ) (k : Fin S.rank) (a : Fin T.rank) :
    C.realPt w s k a = conj (C.θ (C.m.e.symm s) (infPart D (w a k))) := rfl

theorem realPt_sub (C : Ctx S T) (w w' : WO S T) : C.realPt (w - w') = C.realPt w - C.realPt w' := by
  funext s k a
  simp only [realPt_apply, Matrix.sub_apply, map_sub, Pi.sub_apply]

theorem realPt_add (C : Ctx S T) (w w' : WO S T) : C.realPt (w + w') = C.realPt w + C.realPt w' := by
  funext s k a
  simp only [realPt_apply, Matrix.add_apply, map_add, Pi.add_apply]

theorem map_actO {B : Type} [CommRing B] (f : AE D →+* B) (h : GA D S) (g : GA D T) (w : WO S T) :
    (actO S T h g w).map f = (mt T g).map f * w.map f * (mt S h⁻¹).map f := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul]

private theorem isLineAt_apply_unique {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ) {m n : ℕ}
    {τ : D.what₂.Tau} {z : Matrix (Fin m) (Fin n) ℂ} {L L' : ℝ →+ Mx D m n}
    (hL : IsLineAt θ τ z L) (hL' : IsLineAt θ τ z L') (t : ℝ) : L t = L' t := by
  unfold IsLineAt at hL hL'
  refine Matrix.ext fun a k => sub_eq_zero.mp (h.ext _ ?_ fun τ' => ?_)
  · have h1 := congrFun (congrFun (hL.2.1 t) a) k
    have h2 := congrFun (congrFun (hL'.2.1 t) a) k
    simp only [Matrix.map_apply, Matrix.zero_apply] at h1 h2
    rw [map_sub, h1, h2, sub_zero]
  · have h1 := congrFun (congrFun (hL.2.2 t τ') a) k
    have h2 := congrFun (congrFun (hL'.2.2 t τ') a) k
    simp only [compAt, Matrix.map_apply] at h1 h2
    rw [map_sub, map_sub, h1, h2, sub_self]

theorem real_points : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∃ R : WR C.X S.rank →+ WO S T, Continuous R ∧ Continuous C.realPt ∧ (∀ w w', C.realPt (w + w') = C.realPt w + C.realPt w') ∧ (∀ v, IsRealPt (R v) ∧ C.realPt (R v) = v) ∧ (∀ w, IsRealPt w → R (C.realPt w) = w) ∧ (∀ w, IsFinPt (w - R (C.realPt w))) ∧ (∀ u, IsFinPt u → C.realPt u = 0) ∧ (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ), lineAt C.θ τ z t = R (t • (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank))) ∧ ∀ (h : GA D S) (g : GA D T) (w : WO S T), (IsRealPt w → IsRealPt (actO S T h g w)) ∧ (IsFinPt w → IsFinPt (actO S T h g w)) ∧ ∀ τ, compAt C.θ τ (actO S T h g w) = compAt C.θ τ (mt T g) * compAt C.θ τ w * compAt C.θ τ (mt S h⁻¹) := by
  intro D S T C
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart C.inf

  have hRfin : ∀ v a k, finPart D (realOf C σ v a k) = 0 := fun v a k =>
    hσ.fin fun τ => conj (v (C.m.e τ) k a)
  have hRcomp : ∀ v a k τ, C.θ τ (infPart D (realOf C σ v a k)) = conj (v (C.m.e τ) k a) :=
    fun v a k τ => hσ.comp (fun τ => conj (v (C.m.e τ) k a)) τ
  have hRreal : ∀ v, IsRealPt (realOf C σ v) := by
    intro v
    show (realOf C σ v).map (finPart D) = 0
    refine Matrix.ext fun a k => ?_
    rw [Matrix.map_apply, hRfin]
    rfl
  have hReal : ∀ v, C.realPt (realOf C σ v) = v := by
    intro v
    funext s k a
    rw [realPt_apply, hRcomp]
    simp
  have hRcont : Continuous (realOf C σ) := by
    refine continuous_pi fun a => continuous_pi fun k => ?_
    exact hσ.cont.comp (continuous_pi fun τ => Complex.continuous_conj.comp
      ((continuous_apply a).comp ((continuous_apply k).comp (continuous_apply (C.m.e τ)))))
  refine ⟨realOf C σ, hRcont, ?_, fun w w' => realPt_add C w w', fun v => ⟨hRreal v, hReal v⟩, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine continuous_pi fun s => continuous_pi fun k => continuous_pi fun a => ?_
    simp only [realPt_apply]
    exact Complex.continuous_conj.comp ((GlobalTheory.FockCompare.continuous_comp C.inf _).comp
      ((continuous_apply k).comp (continuous_apply a)))
  ·
    intro w hw
    have hw' : w.map (finPart D) = 0 := hw
    refine Matrix.ext fun a k => sub_eq_zero.mp (hσ.ext _ ?_ fun τ => ?_)
    · have h1 : finPart D (w a k) = 0 := by simpa using congrFun (congrFun hw' a) k
      rw [map_sub, hRfin, h1, sub_zero]
    · rw [map_sub, map_sub, hRcomp, realPt_apply]
      simp
  ·
    intro w
    show (w - realOf C σ (C.realPt w)).map (infPart D) = 0
    refine Matrix.ext fun a k => ?_
    rw [Matrix.map_apply, Matrix.zero_apply, Matrix.sub_apply]
    refine infPart_eq_zero hσ _ fun τ => ?_
    rw [map_sub, map_sub, hRcomp, realPt_apply]
    simp
  ·
    intro u hu
    have hu' : u.map (infPart D) = 0 := hu
    funext s k a
    have h1 : infPart D (u a k) = 0 := by simpa using congrFun (congrFun hu' a) k
    simp [realPt_apply, h1]
  ·
    intro τ z t
    have hL : IsLineAt C.θ τ z ((realOf C σ).comp
        ((smulAddHom ℝ (WR C.X S.rank)).flip (Pi.single (C.m.e τ) fun k a => conj (z a k)))) := by
      unfold IsLineAt
      refine ⟨hRcont.comp (continuous_id.smul continuous_const), fun t => hRreal _, fun t τ' => ?_⟩
      refine Matrix.ext fun a k => ?_
      simp only [compAt, Matrix.map_apply, AddMonoidHom.coe_comp, Function.comp_apply,
        AddMonoidHom.flip_apply, smulAddHom_apply]
      rw [hRcomp]
      by_cases hτ : τ' = τ
      · subst hτ
        simp [Complex.real_smul]
      · simp [hτ]
    have hE : IsLineAt C.θ τ z (lineAt C.θ τ z) := by
      unfold lineAt
      exact Classical.epsilon_spec ⟨_, hL⟩
    exact isLineAt_apply_unique hσ hE hL t
  ·
    intro h g w
    refine ⟨fun hw => ?_, fun hw => ?_, fun τ => map_actO ((C.θ τ).comp (infPart D)) h g w⟩
    · have hw' : w.map (finPart D) = 0 := hw
      show (actO S T h g w).map (finPart D) = 0
      rw [map_actO, hw', Matrix.mul_zero, Matrix.zero_mul]
    · have hw' : w.map (infPart D) = 0 := hw
      show (actO S T h g w).map (infPart D) = 0
      rw [map_actO, hw', Matrix.mul_zero, Matrix.zero_mul]

end GlobalTheory.KerReal

end
