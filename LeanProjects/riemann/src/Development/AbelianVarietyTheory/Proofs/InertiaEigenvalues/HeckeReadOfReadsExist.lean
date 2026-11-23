import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ZeroDegreeOfPinFor
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperLeftBlockEqOneIffOfMemBlockTri
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinPartMulIncAMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOffOutsideS0

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open Formalism.IndefR.Lev (levG flag1L)
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw}

section Delta

def IsDeltaInv (ρ : Setup D.ntw) (u : ∀ i : D.ntw.Tw, Bool → PlE D.host → (D.ntw.O i)ˣ) : Prop :=
  ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (P : PlE D.host), HkIdx i k P →
    ∀ (α : GA D (Wc D j)) (z : (AE D)ˣ), IsHeckeAt (Wc D j) P k α → IsDetAt (idemAt P) (Wc D j) α z →
      ρ.eO i b (u i b P) ^ k = (((ρ.B i j b).de.chi z : Circle) : ℂ)⁻¹

end Delta

section Pin

variable (Rl cG S) (YS : NX.NExpRealS Rl cG S)

set_option synthInstance.maxHeartbeats 400000 in

def PinDFor (ρ : Setup D.ntw)
    (hk : ∀ i j b, ℕ → PlE D.host → Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) : Prop :=
  ∀ (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → NX.HeckeStabR S j (hL j)),
    GlobalTheory.ExportPin.Reads Rl cG S YS hL → ∃ u : ∀ i : D.ntw.Tw, Bool → PlE D.host → (D.ntw.O i)ˣ,
      (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (x : D.nexp.Fm i j b), P ∉ D.ntw.S0 i →
        Formalism.BasicNotions.IsSplitPl D.host P → k ≤ D.R.r →
        YS.eF i j b h1 h2 (hk i j b k P x) =
          (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k •
            NX.hkFR S i j b (hL j) (hs j h1 h2) k P (YS.eF i j b h1 h2 x)) ∧
      IsDeltaInv ρ u

set_option synthInstance.maxHeartbeats 400000 in

def HeckePinD (ρ : Setup D.ntw) : Prop :=
  ∀ (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → NX.HeckeStabR S j (hL j)),
    GlobalTheory.ExportPin.Reads Rl cG S YS hL → ∃ u : ∀ i : D.ntw.Tw, Bool → PlE D.host → (D.ntw.O i)ˣ,
      (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (x : D.nexp.Fm i j b), P ∉ D.ntw.S0 i →
        Formalism.BasicNotions.IsSplitPl D.host P → k ≤ D.R.r →
        YS.eF i j b h1 h2 (D.nexp.hkF i j b k P x) =
          (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k •
            NX.hkFR S i j b (hL j) (hs j h1 h2) k P (YS.eF i j b h1 h2 x)) ∧
      ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (P : PlE D.host), HkIdx i k P →
        ∀ (α : GA D (Wc D j)) (z : (AE D)ˣ), IsHeckeAt (Wc D j) P k α → IsDetAt (idemAt P) (Wc D j) α z →
          ρ.eO i b (u i b P) ^ k = (((ρ.B i j b).de.chi z : Circle) : ℂ)⁻¹

def ReadsExist : Prop :=
  ∃ (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (_ : ∀ j, 1 ≤ j → j ≤ D.R.m → NX.HeckeStabR S j (hL j)), GlobalTheory.ExportPin.Reads Rl cG S YS hL

end Pin

section Read

variable (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

theorem evK_smul (c : NX.KB S i b) (x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    evK YS v₀ hρ i j b (c • x) = ρ.e i b c • evK YS v₀ hρ i j b x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | tmul a f =>
    rw [TensorProduct.smul_tmul', evK_tmul, evK_tmul, smul_smul]
    exact congrArg (· • _) (map_mul (ρ.e i b) c a)

theorem evK_hkFR (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL ((j : ℕ) + 1)))
    (hs : NX.HeckeStabR S ((j : ℕ) + 1) hL) (k : ℕ) (P : PlE D.host) (R : Finset (GA D (Wc D j))) (c : ℂ)
    (h : ∀ w, evW YS v₀ j (hL k P w) = c • fun x => ∑ γ ∈ R, evW YS v₀ j w (x * γ))
    (t : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    evK YS v₀ hρ i j b (NX.hkFR S i _ b hL hs k P t) = c • fun x => ∑ γ ∈ R, evK YS v₀ hρ i j b t (x * γ) := by
  induction t using TensorProduct.induction_on with
  | zero =>
    have e0 : NX.hkFR S i _ b hL hs k P (0 : NX.Fm S i ((j : ℕ) + 1) b) = 0 := LinearMap.map_zero _
    rw [show (0 : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) = (0 : NX.Fm S i ((j : ℕ) + 1) b) from rfl, e0]
    have z0 : evK YS v₀ hρ i j b (0 : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) = 0 := map_zero _
    erw [z0]
    funext x
    simp
  | add x y hx hy =>
    have e0 : NX.hkFR S i _ b hL hs k P ((x + y : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) : NX.Fm S i ((j : ℕ) + 1) b) =
        NX.hkFR S i _ b hL hs k P x + NX.hkFR S i _ b hL hs k P y := LinearMap.map_add _ _ _
    rw [e0]
    erw [map_add (evK YS v₀ hρ i j b)]
    rw [hx, hy, map_add, ← smul_add]
    congr 1
    funext x
    simp [Finset.sum_add_distrib]
  | tmul a f =>
    change evK YS v₀ hρ i j b (a ⊗ₜ[S.Ks] _) = _
    rw [evK_tmul, evK_tmul]
    change ρ.e i b a • evW YS v₀ j (hL k P f.1) = _
    rw [h]
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    ring

end Read

section Main

variable (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem heckeAt_of_scaled {ρ : Setup D.ntw} (hpin : RealPin Rl cG ρ) (hIs : Rl.toRealDat.toLevCh.Is A3.A.μ0)
    (hA : Rl.AllPlaces) (hρ : ρ.Good) {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)}
    (hr : GlobalTheory.ExportPin.Reads Rl cG S YS hL) {u} (hδ : IsDeltaInv ρ u) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ)
    (hs : NX.HeckeStabR S ((j : ℕ) + 1) (hL ((j : ℕ) + 1))) {k : ℕ} {P : PlE D.host} (hk : HkIdx i k P)
    {f g : D.nexp.Fm i ((j : ℕ) + 1) b}
    (e1 : YS.eF i _ b (Nat.le_add_left _ _) j.2 g = (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k •
      NX.hkFR S i _ b (hL _) hs k P (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)) :
    HeckeAt (realRd YS v₀ hρ i j b ν) k P f g := by
  rintro α R z ⟨hα, hR, hz⟩
  funext x
  rw [Setup.hecke_apply]
  have hδ' := hδ i j b k P hk α z hα hz
  obtain ⟨hk1, hkr, hsp, hP⟩ := hk
  have ho := GlobalTheory.ExportPin.Model.covered_of_allPlaces Rl hIs hA i P hP hsp
  have hR' : Bridge.IsDC (levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv)) α R :=
    GlobalTheory.PrincipalLevel.levK_eq_levG hpin i j b ▸ hR
  have hw : ∀ w, evW YS v₀ j (hL ((j : ℕ) + 1) k P w) =
      ((((Rl.C.mu0 j).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (Formalism.L2.DIV.kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) •
        fun x => ∑ γ ∈ R, evW YS v₀ j w (x * γ) := by
    intro w
    have := hr j k P hsp ho hkr α R hα hR' w
    exact congrArg (fun T => T (v₀ j _)) this
  have hmu : (((ρ.B i j b).mu0 z : Circle) : ℂ) = (((Rl.C.mu0 j).val P : ℂˣ) : ℂ) ^ k := by
    rw [hpin.mu0 i j b]
    refine GlobalTheory.HeckeDetChar.chi_detAt (hIs.mu0 j) (Q := Rl.Pg) ?_ ?_ ?_ hα hz
    · have := (hρ.base i j b).unram
      rwa [hpin.Pg i j b, hpin.mu0 i j b] at this
    · obtain ⟨Q, h1, -, h3⟩ := (hρ.base i j b).places.split
      exact hpin.Pg i j b ▸ h3.mono h1
    · have hA' : Rl.Sb = Rl.Pg := hA
      rw [← hA']; exact ho
  have hrk : (Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  change ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 g) x = _
  rw [e1]
  erw [evK_smul YS v₀ hρ i j b ((algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k)]
  erw [evK_hkFR YS v₀ hρ i j b (hL ((j : ℕ) + 1)) hs k P R _ hw]
  have he : ρ.e i b ((algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k) = ρ.eO i b (u i b P) ^ k := by
    rw [map_pow]; rfl
  have hm : (((ρ.B i j b).mu z : Circle) : ℂ) =
      (((ρ.B i j b).mu0 z : Circle) : ℂ) * (((ρ.B i j b).de.chi z : Circle) : ℂ) := by
    rw [Base.mu, MonoidHom.mul_apply, Circle.coe_mul]
  have hr1 : ∀ y, realRd YS v₀ hρ i j b ν f y =
      ν⁻¹ * evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f) y := fun _ => rfl
  have hq : normV P = Nat.card (Formalism.L2.DIV.kP P) := rfl
  simp only [hr1, Pi.smul_apply, smul_eq_mul, he, hδ', hm, hmu, hrk, hq]
  rw [← Finset.mul_sum]
  ring

end Main

end GlobalTheory.SeriesTie
