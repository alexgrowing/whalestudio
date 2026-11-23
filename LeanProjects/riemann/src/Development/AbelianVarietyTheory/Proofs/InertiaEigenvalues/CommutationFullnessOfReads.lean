import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ExistsIsHeckeSetting
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ZeroDegreeOfPinFor

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CommFullAll

section Act
variable {D : D7} (S : RatDat D.ntw)

def hLr (j : ℕ) (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (hs : HeckeStabR S j hL) (k : ℕ) (P : PlE D.host) :
    Module.End S.Ks (FmK S j) :=
  ((hL k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) fun x hx => hs k P x hx

theorem hkFR_act (i : D.ntw.Tw) (j : ℕ) (b : Bool) (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : HeckeStabR S j hL) (k : ℕ) (P : PlE D.host) (hst : RhoStab S j) (hχ : ChiInLL0 S j)
    (hc : ∀ g x, hL k P ((S.A j).ρ g x) = (S.A j).ρ g (hL k P x)) (g : G0g D.nd) (z : Fm S i j b) :
    hkFR S i j b hL hs k P (actG S i j b hst hχ g z) = actG S i j b hst hχ g (hkFR S i j b hL hs k P z) := by
  have hcomm : hLr S j hL hs k P * rhoKG S j hst (S.eG.symm g) = rhoKG S j hst (S.eG.symm g) * hLr S j hL hs k P := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact hc (S.eG.symm g) (show ↥(S.A j).WK from x).1
  have h2 := LinearMap.congr_fun (congrArg (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j)) hcomm) z
  rw [map_mul, map_mul] at h2
  change Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (hLr S j hL hs k P) ((readLL0 S i b (chiL S j hχ (S.eG.symm g)))⁻¹ •
      Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (rhoKG S j hst (S.eG.symm g)) z) =
    (readLL0 S i b (chiL S j hχ (S.eG.symm g)))⁻¹ •
      Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (rhoKG S j hst (S.eG.symm g))
        (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (hLr S j hL hs k P) z)
  rw [map_smul]
  congr 1
end Act

section Real
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.IndefR.Cx Formalism.L2.Pj
variable {D : D7} (X : RealSide D) {S : RatDat D.ntw} (YS : NExpRealS X.R X.cG S) (H : NExpRealH X.R X.cG S YS)

end Real

section Iso

variable {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  [Field Ks'] [NumberField Ks'] [Algebra Ks' LL]
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  [AddCommGroup WL'] [Module LL WL'] [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 LL) WL']
  [IsScalarTower (𝓞 LL) LL WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
  {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']
  {A : Arith.FormsL LL Ks WL W G} {A' : Arith.FormsL LL Ks' WL' W' G'}

theorem iso_smul (Y : NX.FormsIso A A') (c : Ks) (w : WL) : Y.e (c • w) = Y.eK c • Y.e w := by
  rw [← algebraMap_smul LL c w, map_smul, ← Y.eK_LL, algebraMap_smul]

theorem iso_symm_smul (Y : NX.FormsIso A A') (c : Ks') (y : WL') : Y.e.symm (c • y) = Y.eK.symm c • Y.e.symm y := by
  apply Y.e.injective
  rw [iso_smul]
  simp

theorem iso_span (Y : NX.FormsIso A A') (h : Submodule.span Ks' (A'.MK : Set WL') = A'.WK) :
    Submodule.span Ks (A.MK : Set WL) = A.WK := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun x hx => by obtain ⟨h, -⟩ := hx; exact h
  · intro x hx
    have h1 : Y.e x ∈ Submodule.span Ks' (A'.MK : Set WL') := h ▸ (Y.wk x).1 hx
    have h2 : ∀ y ∈ Submodule.span Ks' (A'.MK : Set WL'),
        Y.e.symm y ∈ Submodule.span Ks (A.MK : Set WL) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ((Y.mkK _).2 (by simpa using hy))
      | zero => simp
      | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [iso_symm_smul]; exact Submodule.smul_mem _ _ ha
    simpa using h2 _ h1

end Iso

section Base
variable {D : D7} (S : RatDat D.ntw) (i : D.ntw.Tw) (j : ℕ) (b : Bool)

def mkF (y : S.WL j) (h : y ∈ (S.A j).WK) : FmK S j := ⟨y, h⟩

def rdF (c : S.Ks) : FractionRing (D.ntw.O i) := ιK S i b c

def rdK (a : KB S i b) : FractionRing (D.ntw.O i) := a

def oneT (x : FmK S j) : Fm S i j b := ((1 : KB S i b) ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j)

theorem oneT_zero : oneT S i j b 0 = 0 := TensorProduct.tmul_zero _ _

theorem oneT_add (x y : FmK S j) : oneT S i j b (x + y) = oneT S i j b x + oneT S i j b y :=
  TensorProduct.tmul_add _ _ _

theorem oneT_smul (c : S.Ks) (x : FmK S j) :
    oneT S i j b (c • x) = (rdF S i b c) • oneT S i j b x := by
  change (1 : KB S i b) ⊗ₜ[S.Ks] (c • x) = (ιK S i b c : KB S i b) • ((1 : KB S i b) ⊗ₜ[S.Ks] x)
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  congr 1

theorem Bsup_span (hS : Submodule.span S.Ks ((S.A j).MK : Set (S.WL j)) = (S.A j).WK) :
    Submodule.span (FractionRing (D.ntw.O i)) (Bsup S i j b : Set (Fm S i j b)) = ⊤ := by
  let B := Submodule.span (FractionRing (D.ntw.O i)) (Bsup S i j b : Set (Fm S i j b))
  have aux : ∀ y ∈ Submodule.span S.Ks ((S.A j).MK : Set (S.WL j)), ∃ h : y ∈ (S.A j).WK,
      oneT S i j b (mkF S j y h) ∈ B := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, h'⟩ := id hy
      exact ⟨h, Submodule.subset_span (Submodule.subset_span ⟨mkF S j y h, hy, rfl⟩)⟩
    | zero =>
      refine ⟨(S.A j).WK.zero_mem, ?_⟩
      have : oneT S i j b (mkF S j 0 (S.A j).WK.zero_mem) = 0 := oneT_zero S i j b
      rw [this]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      obtain ⟨h1, h2⟩ := hx
      obtain ⟨h3, h4⟩ := hy
      refine ⟨(S.A j).WK.add_mem h1 h3, ?_⟩
      have : oneT S i j b (mkF S j (x + y) ((S.A j).WK.add_mem h1 h3)) =
          oneT S i j b (mkF S j x h1) + oneT S i j b (mkF S j y h3) :=
        oneT_add S i j b (mkF S j x h1) (mkF S j y h3)
      rw [this]
      exact Submodule.add_mem _ h2 h4
    | smul c x _ hx =>
      obtain ⟨h1, h2⟩ := hx
      refine ⟨(S.A j).WK.smul_mem c h1, ?_⟩
      have : oneT S i j b (mkF S j (c • x) ((S.A j).WK.smul_mem c h1)) =
          (rdF S i b c) • oneT S i j b (mkF S j x h1) :=
        oneT_smul S i j b c (mkF S j x h1)
      rw [this]
      exact Submodule.smul_mem _ _ h2
  have hall : ∀ (a : KB S i b) (x : FmK S j),
      ((a ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j) : Fm S i j b) ∈ B := by
    intro a x
    have hx : (show ↥(S.A j).WK from x).1 ∈ Submodule.span S.Ks ((S.A j).MK : Set (S.WL j)) := by
      rw [hS]; exact (show ↥(S.A j).WK from x).2
    obtain ⟨h, h'⟩ := aux _ hx
    have e : ((a ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j) : Fm S i j b) =
        (rdK S i b a) • oneT S i j b x := by
      change a ⊗ₜ[S.Ks] x = a • ((1 : KB S i b) ⊗ₜ[S.Ks] x)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e]
    exact Submodule.smul_mem _ _ h'
  refine eq_top_iff.2 fun t _ => ?_
  change t ∈ B
  induction (show KB S i b ⊗[S.Ks] FmK S j from t) using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a x => exact hall a x
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end Base

end GlobalTheory.CommFullAll
