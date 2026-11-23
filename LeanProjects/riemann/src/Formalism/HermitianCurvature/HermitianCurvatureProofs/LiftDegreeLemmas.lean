import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormPos
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfChoices
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

section nice

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def NV {S : Type} (Bs : B.RealPlaceData k ρ Wp Wq) (ε : ℝ) (x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ e, JC.NiceCoef Bs ε (x e)

variable {S : Type} {Bs : B.RealPlaceData k ρ Wp Wq} {ε : ℝ}

theorem nv_zero : NV (S := S) Bs ε 0 := fun _ => JCx2.mn_nice_zero

theorem nv_add {x y : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (hx : NV Bs ε x) (hy : NV Bs ε y) : NV Bs ε (x + y) :=
  fun e => JCx2.mn_nice_add (hx e) (hy e)

theorem nv_smul (c : ℂ) {x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (hx : NV Bs ε x) : NV Bs ε (c • x) :=
  fun e => JCx2.mn_nice_smul c (hx e)

theorem nice_mono {F : B.Mat k ρ → (Wq →L[ℂ] Wp)} {ε ε' : ℝ} (h : JC.NiceCoef Bs ε F) (h' : ε' ≤ ε) :
    JC.NiceCoef Bs ε' F :=
  ⟨h.1, h.2.1, fun g hg hne => h'.trans (h.2.2 g hg hne)⟩

theorem nv_mono {x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} {ε ε' : ℝ} (h : NV Bs ε x) (h' : ε' ≤ ε) : NV Bs ε' x :=
  fun e => nice_mono (h e) h'

theorem nice_of_cpt {F : B.Mat k ρ → (Wq →L[ℂ] Wp)} (h : KB.CptCoef Bs F) : ∃ ε, 0 < ε ∧ JC.NiceCoef Bs ε F := by
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hG⟩⟩ := h
  refine ⟨ε, hε, hs, fun A m => JFxG.cptInCC_G hs (PBE.isCompact_gN_le k ρ R) (fun g hg hgC => ?_) A m, hG⟩
  by_contra h0
  exact hgC (hR g hg h0)

end nice

section forms

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem nv_common {α S : Type} {k ρ : ℕ} {Bs : B.RealPlaceData k ρ Wp Wq} (Y : Finset α)
    (u : α → Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) (h : ∀ a ∈ Y, ∃ ε, 0 < ε ∧ NV Bs ε (u a)) :
    ∃ ε, 0 < ε ∧ ∀ a ∈ Y, NV Bs ε (u a) := by
  obtain ⟨ε, hε, hall⟩ := common_eps (ι := Y) (fun a ε => NV Bs ε (u a)) (fun a ε ε' h h0 h' => nv_mono h h')
    (fun a => h a a.2)
  exact ⟨ε, hε, fun a ha => hall ⟨a, ha⟩⟩

theorem slv_nv (p : KB.Pl P Wp Wq) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef p.T.base F) (j : ℕ)
    (hj : j ≤ P.r) (w : List C.Letter) (a : C.LPt) (ha : D.IsLocPt a j) :
    ∃ ε, 0 < ε ∧ NV (p.T.bs j) ε (KB.slv p.T F j hj w a ha.2) := by
  have h := fun e => nice_of_cpt (Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w a ha hF e)
  obtain ⟨ε, hε, hall⟩ := common_eps (fun e ε => JC.NiceCoef (p.T.bs j) ε (KB.slv p.T F j hj w a ha.2 e))
    (fun e ε ε' h h0 h' => nice_mono h h') h
  exact ⟨ε, hε, hall⟩

theorem form_eq' (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) :
    p.form j hj w = D.formLev p.T (M.sgn P p.l0) ⟨j, by omega⟩ w := rfl

theorem form_sl (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) {ε : ℝ}
    (x₁ x₂ y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (h₁ : NV (p.T.bs j) ε x₁) (h₂ : NV (p.T.bs j) ε x₂) (hy : NV (p.T.bs j) ε y) :
    p.form j hj w (x₁ + c • x₂) y = p.form j hj w x₁ y + c * p.form j hj w x₂ y :=
  PBG.form_sesq_left P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w x₁ x₂ y c (PBG.decV_of_nice h₁) (PBG.decV_of_nice h₂)
    (PBG.decV_of_nice hy)

theorem form_sr (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) {ε : ℝ}
    (x y₁ y₂ : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : NV (p.T.bs j) ε x) (h₁ : NV (p.T.bs j) ε y₁) (h₂ : NV (p.T.bs j) ε y₂) :
    p.form j hj w x (y₁ + c • y₂) = p.form j hj w x y₁ + conj c * p.form j hj w x y₂ :=
  PBG.form_sesq_right P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w x y₁ y₂ c (PBG.decV_of_nice hx) (PBG.decV_of_nice h₁)
    (PBG.decV_of_nice h₂)

end forms

end

end Formalism.FourierDecayAlt.P.PBL
