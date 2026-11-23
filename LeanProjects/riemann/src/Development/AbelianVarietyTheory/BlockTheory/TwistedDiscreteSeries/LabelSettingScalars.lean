import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalRingCardinality.DataParams
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

abbrev EigSys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

open Classical in

def badPl (t : T) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  (R.Pg ∪ R.Q t).image fun PP => PP.under (𝓞 D.host.F)

def rowPart (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : EigSys D) : Submodule ℂ (MMap (R.MY 0)) :=
  partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) Sb c ⊓ R.EEat R.triv

def IsLValue (t : T) (B : GlobalTheory.LFun.Fam D.host.E) (j : ℕ) (l : ℝ) : Prop :=
  GlobalTheory.LFun.Converges (GlobalTheory.LFun.above D.host.E (badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F))))
               (GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (R.toLevCh.mu t j))⁻¹) ((1 + (D.R.t : ℂ)) / 2) ∧
    0 < l ∧ GlobalTheory.LFun.LSD D (badPl R t) B (R.toLevCh.mu t j) ((1 + (D.R.t : ℂ)) / 2) = (l : ℂ)

def IsIP (t : T) (k : ℕ) (u u' : MMap (R.MY k)) (a : ℂ) : Prop :=
  IsMultIP (R.MY k) (R.νY t k) (R.fdY t k) u u' a

def IsUp (t : T) (k : ℕ) (u : MMap (R.MY k)) (x : MMap (R.MY (k + 1))) : Prop :=
  PiTensorProduct.lift x ∈ R.CC t (k + 1) ∧ ∀ y : R.CC t (k + 1), ∃ a : ℂ,
    IsIP R t (k + 1) x (PiTensorProduct.lift.symm y.1) a ∧ IsIP R t k u (PiTensorProduct.lift.symm (R.ioY t k y).1) a

def topStep (t : T) (y : (R.HX t).H) : MMap (R.MY (D.R.m - 1)) :=
  PiTensorProduct.lift.symm (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1

def IsUpTop (t : T) (u : MMap (R.MY (D.R.m - 1))) (x : (R.HX t).H) : Prop :=
  ∀ y : (R.HX t).H, IsIP R t (D.R.m - 1) u (topStep R t y) ⟪x, y⟫_ℂ

def reached (t : T) (c : EigSys D) (k : ℕ) : Set (MMap (R.MY k)) :=
  Nat.rec (motive := fun k => Set (MMap (R.MY k))) (rowPart R (badPl R t) c : Set (MMap (R.MY 0)))
    (fun k P => {x | ∃ u ∈ P, IsUp R t k u x}) k

theorem reached_zero (t : T) (c : EigSys D) : reached R t c 0 = (rowPart R (badPl R t) c : Set (MMap (R.MY 0))) := rfl

theorem reached_succ (t : T) (c : EigSys D) (k : ℕ) :
    reached R t c (k + 1) = {x | ∃ u ∈ reached R t c k, IsUp R t k u x} := rfl

def StepScalar (t : T) (c : EigSys D) (k : ℕ) (Λ : ℝ) : Prop :=
  (∀ u ∈ reached R t c k, ∃ x, IsUp R t k u x) ∧
  ∀ u₁ ∈ reached R t c k, ∀ u₂ ∈ reached R t c k, ∀ x₁ x₂, IsUp R t k u₁ x₁ → IsUp R t k u₂ x₂ →
    ∃ a : ℂ, IsIP R t k u₁ u₂ a ∧ IsIP R t (k + 1) x₁ x₂ ((Λ : ℂ) * a)

def TopScalar (t : T) (c : EigSys D) (Λ : ℝ) : Prop :=
  (∀ u ∈ reached R t c (D.R.m - 1), ∃ x, IsUpTop R t u x) ∧
  ∀ u₁ ∈ reached R t c (D.R.m - 1), ∀ u₂ ∈ reached R t c (D.R.m - 1), ∀ x₁ x₂, IsUpTop R t u₁ x₁ → IsUpTop R t u₂ x₂ →
    ∃ a : ℂ, IsIP R t (D.R.m - 1) u₁ u₂ a ∧ ⟪x₁, x₂⟫_ℂ = (Λ : ℂ) * a

def ScalarsWith (κ : ℕ → ℝ) : Prop :=
  ∀ (t : T) (c : EigSys D), rowPart R (badPl R t) c ≠ ⊥ →
    (∃ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B) ∧
    ∀ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B →
      (∀ k, k + 1 < D.R.m → ∃ l, IsLValue R t B (k + 1) l ∧ StepScalar R t c k (κ (k + 1) * l)) ∧
      ∃ l, IsLValue R t B D.R.m l ∧ TopScalar R t c (κ D.R.m * l)

def Scalars : Prop := ∃ κ : ℕ → ℝ, (∀ j, 1 ≤ j → j ≤ D.R.m → 0 < κ j) ∧ ScalarsWith R κ

def IsLabelOf {g : ℕ} [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) {κ : Type} [CommRing κ] (e : ZMod g ≃+* κ)
    (x : (ZMod g)ˣ) (χ : κˣ →* ℂˣ) : Prop :=
  ∀ z : (ZMod g)ˣ, GlobalTheory.GLq.thetaOf L 1 (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) x) (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) z) =
    ((χ (Units.map (e : ZMod g →+* κ).toMonoidHom z) : ℂˣ) : ℂ)

def GoodTypes : Prop :=
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  ∃ (eR : G ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg)
    (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1)
    (L : ∀ k : Fin 2, GlobalTheory.GLq.LabelDatum (D.host.g k)),
    (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff (eR g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧
    (∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)) ∧
    (∀ k, (L k).teich = D.ntypes.teichC k ∧ ∀ f, D.ntypes.eSer k f = GlobalTheory.GLq.eSerC (L k) D.R.r f) ∧
    ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (j : Fin D.R.m),
      IsLabelOf (L kv.1) (iso kv) (D.nd.chiT kv.1 kv.2 j) (R.chi ((j : ℕ) + 1) (plg kv).1) ∨
      IsLabelOf (L kv.1) (iso kv) (D.nd.chiT kv.1 kv.2 j) (R.chi ((j : ℕ) + 1) (plg kv).1)⁻¹

structure HidaSetting : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  chain : R.IsChain
  thP : R.IsThP
  scal : R.IsScal F
  params : ∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)
  good : GoodTypes R

def OneStepAt : Prop := HidaSetting R F → Scalars R

def OneStep : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), OneStepAt R F

theorem rowPart_mono {Sb Sb' : Finset (HeightOneSpectrum (𝓞 D.host.F))} (h : Sb ⊆ Sb') (c : EigSys D) :
    rowPart R Sb c ≤ rowPart R Sb' c := by
  refine inf_le_inf_right _ fun u hu => ?_
  rw [partDual, mem_partFull] at hu ⊢
  refine ⟨hu.1, fun P d Rp hR => hu.2 P d Rp ?_⟩
  obtain ⟨e, f, ϖ, α, h1, h2⟩ := hR
  exact ⟨e, f, ϖ, α, fun v hv => h1 v (h hv), h2⟩

theorem GoodTypes.record {R : RealDat D A Ks} (h : GoodTypes R) : R.grp_record := by
  obtain ⟨eR, plg, iso, -, h1, h2, h3, -⟩ := h
  exact ⟨eR, plg, iso, h1, h2, h3⟩

theorem IsLValue.unique {R : RealDat D A Ks} {t : T} {B : GlobalTheory.LFun.Fam D.host.E} {j : ℕ} {l l' : ℝ}
    (h : IsLValue R t B j l) (h' : IsLValue R t B j l') : l = l' := by
  exact_mod_cast h.2.2.symm.trans h'.2.2

theorem IsUpTop.unique {R : RealDat D A Ks} {t : T} {u : MMap (R.MY (D.R.m - 1))} {x x' : (R.HX t).H}
    (v : (R.MY (D.R.m - 1)).Vec) (hv : ∏ τ, ⟪(v τ : (R.MY (D.R.m - 1)).H τ), (v τ : (R.MY (D.R.m - 1)).H τ)⟫_ℂ ≠ 0)
    (h : IsUpTop R t u x) (h' : IsUpTop R t u x') : x = x' :=
  ext_inner_right ℂ fun y => hasPeterssonInner_unique _ _ _ _ _ v hv (h y) (h' y)

end GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars

end
