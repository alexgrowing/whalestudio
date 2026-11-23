import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IntAtExtExtAll
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective

noncomputable section

namespace GlobalTheory.RunIn

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj

variable {D : D7}

def sOf (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) {j : ℕ} (w : WeightFamilies.Wt D j) : 𝓞 B.KO :=
  nnW B hinj EX w * (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : 𝓞 B.KO)

theorem sW_eq_sOf (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) {j : ℕ}
    (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) : (scalOfP B hinj EX p ka wL wF T).sW = sOf B hinj EX wL := rfl

def ThInt {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (hinj : Function.Injective D.what₂.OtoLL)
    (EX : ErrX D) (w : WeightFamilies.Wt D j) : Prop :=
  X.WWc (sOf B hinj EX w) w ≤ B.Mlat j w

structure SecNorm (B : WeightFamilies.Prov D) where
  N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ
  h0 : ∀ j ka σ F, 0 ≤ N j ka σ F
  h1 : ∀ j ka σ F, N j ka σ F = 0 ↔ F = 0
  h2 : ∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F
  h3 : ∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G
  h4 : ∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F

def SecNorm.sup (B : WeightFamilies.Prov D) : SecNorm B :=
  ⟨B.supN, B.supN_nonneg, B.supN_eq_zero, B.supN_smul, B.supN_add, fun _ _ _ _ => le_rfl⟩

abbrev SecNorm.base {B : WeightFamilies.Prov D} (n : SecNorm B) : WeightFamilies.Prov D := withNorm B n.N n.h0 n.h1 n.h2 n.h3 n.h4

def recPlusN {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) :
    PJ D n.base T.G.P j :=
  PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (recPlus h j hj)

end GlobalTheory.RunIn
