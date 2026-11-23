import Formalism.LocalToGlobal.Columns.InvariantSubspaceCoordsX
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Formalism.LocalToGlobal.GroupLattices.JointServices.LevelOperatorFixesImage
import Formalism.LocalToGlobal.Columns.RecPerFF

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.L2.Col Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.G.ServJoint
open scoped ComplexOrder

section Row

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (h : (mtildeKGSD W Ch sel mu).Ok) (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (P : LevFam X.E X.K R.r Pr.vGs)

def evRow0 : (Fin (V0C W Ch sel mu h Xg P).d → X.K) →ₗ[X.K] (mtildeKGSD W Ch sel mu).EqFun :=
  ((mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec).symm.toLinearMap ∘ₗ (V0C W Ch sel mu h Xg P).E.mulVecLin

theorem evRow0_mem (x : Fin (V0C W Ch sel mu h Xg P).d → X.K) : evRow0 W Ch sel mu h Xg P x ∈ V0X W Ch sel mu Xg P := by
  have hx : (V0C W Ch sel mu h Xg P).E.mulVecLin x ∈
      (V0X W Ch sel mu Xg P).map ((mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec).toLinearMap := by
    rw [invariantSubspace_coords_X]
    exact ⟨x, rfl⟩
  obtain ⟨φ, hφ, e⟩ := hx
  have : evRow0 W Ch sel mu h Xg P x = φ := by
    show ((mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec).symm ((V0C W Ch sel mu h Xg P).E.mulVecLin x) = φ
    rw [← e]
    exact LinearEquiv.symm_apply_apply _ φ
  rw [this]
  exact hφ

def evRow : (Fin (V0C W Ch sel mu h Xg P).d → X.K) →ₗ[X.K] V0X W Ch sel mu Xg P :=
  LinearMap.codRestrict _ (evRow0 W Ch sel mu h Xg P) (evRow0_mem W Ch sel mu h Xg P)

theorem evRow_coord (x : Fin (V0C W Ch sel mu h Xg P).d → X.K) :
    (mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec (evRow W Ch sel mu h Xg P x).1 =
      (V0C W Ch sel mu h Xg P).E.mulVec x := ((mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec).apply_symm_apply _

theorem evRow_injective : Function.Injective (evRow W Ch sel mu h Xg P) := by
  intro x y e
  have e1 : (V0C W Ch sel mu h Xg P).E.mulVec x = (V0C W Ch sel mu h Xg P).E.mulVec y := by
    rw [← evRow_coord, ← evRow_coord, e]
  exact (image_idempotent_spec X.K _ _).1 e1

theorem evRow_surjective : Function.Surjective (evRow W Ch sel mu h Xg P) := by
  intro φ
  have hx : (mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec φ.1 ∈
      LinearMap.range (V0C W Ch sel mu h Xg P).E.mulVecLin := by
    rw [← invariantSubspace_coords_X]
    exact ⟨φ.1, φ.2, rfl⟩
  obtain ⟨x, e⟩ := hx
  refine ⟨x, Subtype.ext ?_⟩
  apply ((mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec).injective
  rw [evRow_coord]
  exact e

def evRowE : (Fin (V0C W Ch sel mu h Xg P).d → X.K) ≃ₗ[X.K] V0X W Ch sel mu Xg P :=
  LinearEquiv.ofBijective (evRow W Ch sel mu h Xg P) ⟨evRow_injective W Ch sel mu h Xg P, evRow_surjective W Ch sel mu h Xg P⟩

theorem evRow_res (x : Fin (V0C W Ch sel mu h Xg P).d → X.K) :
    (mtildeKGSD W Ch sel mu).res h (evRow W Ch sel mu h Xg P x).1 =
      (MtildeKCSD W Ch sel mu h).basis.equivFun.symm ((V0C W Ch sel mu h Xg P).E.mulVec x) := by
  exact ((mtildeKGSD W Ch sel mu).res h).apply_symm_apply _

theorem evRow_res_lvl (hX : X.Ok) {v0 : InfinitePlace X.K} (h0 : IsConjAt v0)
    (hpos : ((MtildeKCSD W Ch sel mu h).H.map v0.embedding).PosDef) (hXg : ∀ χ ∈ Xg, IsAbsIrrChar χ)
    (x : Fin (V0C W Ch sel mu h Xg P).d → X.K) :
    (mtildeKGSD W Ch sel mu).res h (evRow W Ch sel mu h Xg P x).1 =
      (MtildeKCSD W Ch sel mu h).basis.equivFun.symm
        (((MtildeKCSD W Ch sel mu h).lvlE (g0Act W Ch sel mu h) P.grp P.chr).mulVec
          (((MtildeKCSD W Ch sel mu h).lvlPr (g0Act W Ch sel mu h) P.grp P.chr *
            (MtildeKCSD W Ch sel mu h).V0E (g0Act W Ch sel mu h) Xg P.grp P.chr).mulVec x)) := by
  rw [lvlE_lvlPr_V0E (MtildeKCSD W Ch sel mu h) (g0Act W Ch sel mu h) Xg P.grp P.chr h0 hpos (unipotentActionForms_good W Ch sel mu hX h) hXg x]
  exact evRow_res W Ch sel mu h Xg P x

end Row

section Fam

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
  (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
  (trIv : Fin R.m → (LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)
  (P : LevFam X.E X.K R.r Pr.vGs)

def evC (Zs : DefSub (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.amb3) (t : (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.base3.Tup) :
    (Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).nV t) → X.K) →ₗ[X.K] V0X W Ch sel t.1 Xg P :=
  evRow W Ch sel t.1 (mtildeKOk W Ch sel t.1 hX) Xg P

theorem evC_bijective (Zs : DefSub (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.amb3)
    (t : (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.base3.Tup) :
    Function.Bijective (evC W Ch sel hX v0 TU Xg S0 xiVal trIv P Zs t) := ⟨evRow_injective W Ch sel t.1 (mtildeKOk W Ch sel t.1 hX) Xg P,
    evRow_surjective W Ch sel t.1 (mtildeKOk W Ch sel t.1 hX) Xg P⟩

theorem evC_res_lvl {s : ℕ} (hOk : (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.Ok s)
    (Zs : DefSub (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.amb3)
    (t : (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.base3.Tup)
    (F : Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).nV t) → X.K) :
    (mtildeKGSD W Ch sel t.1).res (mtildeKOk W Ch sel t.1 hX) (evC W Ch sel hX v0 TU Xg S0 xiVal trIv P Zs t F).1 =
      ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.basis.equivFun.symm
        ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.cutE ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r
            (lvlIdem ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).P
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).ψ)).mulVec
          ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.lvlPr ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).P
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).ψ *
            ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).vE
              ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr)).mulVec F)) :=
  evRow_res_lvl W Ch sel t.1 _ Xg P hX hOk.conj ((hOk.what₂ t).hpos _) hOk.irr F

variable (σ₀ : X.K →+* ℂ) (hM : (rowGSD W (rowTyG Ch P).inv).Ok)
  (rd : ∀ t : (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.base3.Tup,
    (Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.lvlDim ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r
      P.grp P.chr) → X.K) → Fin ((rowGSD W (rowTyG Ch P).inv).hDim hM) → ℂ)
  (T0 : (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.base3.Tup → Prop)

def EvReadAll : Prop :=
  ∀ (t : (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.base3.Tup) (_ : T0 t) (hQ : QE sel (t.1 : Chr X.F X.E X.K) = ∅)
    (y : Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.lvlDim ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r
      P.grp P.chr) → X.K),
    ∃ (F' : (mtildeKGSD W Ch sel t.1).EqFun) (hm : F'.1 ∈ (mtildeGSD W Ch sel t.1 P).EqFun),
      (mtildeKGSD W Ch sel t.1).res (mtildeKOk W Ch sel t.1 hX) F' =
        ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.basis.equivFun.symm
          ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.cutE ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r
            (lvlIdem P.grp P.chr)).mulVec y) ∧
      rd t y = zOfRow W Ch sel t.1 hQ P σ₀ hM ⟨F'.1, hm⟩

def EvRead : Prop :=
  ∀ (Zs : DefSub (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.amb3)
    (t : (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.base3.Tup) (_ : T0 t) (hQ : QE sel (t.1 : Chr X.F X.E X.K) = ∅)
    (F : Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).nV t) → X.K),
    ∃ hm : (evC W Ch sel hX v0 TU Xg S0 xiVal trIv P Zs t F).1.1 ∈ (mtildeGSD W Ch sel t.1 P).EqFun,
      rd t ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.lvlPr ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r
            P.grp P.chr *
          ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).vE
            ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr)).mulVec F) =
        zOfRow W Ch sel t.1 hQ P σ₀ hM ⟨_, hm⟩

end Fam

end Formalism.L2.DIV
