import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMtTie
import Formalism.LocalToGlobal.Columns.InvariantSubspaceCoordsX
import Formalism.LocalToGlobal.Divisibility.RowSideTie

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
open scoped ComplexOrder

namespace GlobalTheory.Mem.ColTie

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok)

abbrev csdK : CSD X.K := MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)

abbrev actK : Representation X.K (G0 X.E Pr.vGs R.r) (csdK W Ch sel mu hX).Forms :=
  g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX)

abbrev dimP : ℕ := (csdK W Ch sel mu hX).lvlDim (actK W Ch sel mu hX) P.grp P.chr

abbrev resK : (mtildeKGSD W Ch sel mu).EqFun ≃ₗ[X.K] (csdK W Ch sel mu hX).Forms :=
  (mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX)

abbrev formK (x : Fin (dimP W Ch sel mu P hX) → X.K) : (csdK W Ch sel mu hX).Forms :=
  LiftForms.lvlForm (csdK W Ch sel mu hX) (actK W Ch sel mu hX) P.grp P.chr x

theorem resK_symm_act (a : G0 X.E Pr.vGs R.r) (f : (csdK W Ch sel mu hX).Forms) :
    (resK W Ch sel mu hX).symm (actK W Ch sel mu hX a f) = g0HatRepEqFunX W Ch sel mu a ((resK W Ch sel mu hX).symm f) :=
  LinearEquiv.symm_apply_apply _ _

theorem resK_act (a : G0 X.E Pr.vGs R.r) (φ : (mtildeKGSD W Ch sel mu).EqFun) :
    actK W Ch sel mu hX a (resK W Ch sel mu hX φ) = resK W Ch sel mu hX (g0HatRepEqFunX W Ch sel mu a φ) := by
  show resK W Ch sel mu hX (g0HatRepEqFunX W Ch sel mu a ((resK W Ch sel mu hX).symm (resK W Ch sel mu hX φ))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem formK_mem (x : Fin (dimP W Ch sel mu P hX) → X.K) :
    formK W Ch sel mu P hX x ∈ lvlForms (csdK W Ch sel mu hX) (actK W Ch sel mu hX) P.grp P.chr := by
  rw [← LiftForms.range_lvlForm]
  exact ⟨x, rfl⟩

theorem zOf_mem (x : Fin (dimP W Ch sel mu P hX) → X.K) :
    ((resK W Ch sel mu hX).symm (formK W Ch sel mu P hX x)).1 ∈ (mtildeGSD W Ch sel mu P).EqFun := by
  refine (mem_MtildeV_iff W Ch sel mu P _).2 ⟨Subtype.prop _, fun a => ?_⟩
  refine (resK_symm_act W Ch sel mu hX a.1 _).symm.trans ?_
  rw [formK_mem W Ch sel mu P hX x a, map_smul]

def zOf : (Fin (dimP W Ch sel mu P hX) → X.K) →ₗ[X.K] MtildeV W Ch sel mu P where
  toFun x := ⟨_, zOf_mem W Ch sel mu P hX x⟩
  map_add' x y := Subtype.ext (by simp only [map_add]; rfl)
  map_smul' c x := Subtype.ext (by simp only [map_smul]; rfl)

theorem zOf_val (x : Fin (dimP W Ch sel mu P hX) → X.K) :
    (zOf W Ch sel mu P hX x).1 = ((resK W Ch sel mu hX).symm (formK W Ch sel mu P hX x)).1 := rfl

theorem zOf_injective : Function.Injective (zOf W Ch sel mu P hX) := by
  intro x y h
  apply LiftForms.lvlForm_injective (csdK W Ch sel mu hX) (actK W Ch sel mu hX) P.grp P.chr
  apply (resK W Ch sel mu hX).symm.injective
  have h1 : (zOf W Ch sel mu P hX x).1 = (zOf W Ch sel mu P hX y).1 := congrArg Subtype.val h
  exact Subtype.ext h1

theorem zOf_surjective : Function.Surjective (zOf W Ch sel mu P hX) := by
  intro φ
  obtain ⟨hφ, hact⟩ := (mem_MtildeV_iff W Ch sel mu P φ.1).1 φ.2
  have hf : resK W Ch sel mu hX ⟨φ.1, hφ⟩ ∈ lvlForms (csdK W Ch sel mu hX) (actK W Ch sel mu hX) P.grp P.chr := by
    intro a
    rw [resK_act, hact a, map_smul]
  rw [← LiftForms.range_lvlForm] at hf
  obtain ⟨x, hx⟩ := hf
  refine ⟨x, Subtype.ext ?_⟩
  rw [zOf_val]
  show ((resK W Ch sel mu hX).symm (LiftForms.lvlForm _ _ P.grp P.chr x)).1 = φ.1
  rw [hx, LinearEquiv.symm_apply_apply]

def zEquiv : (Fin (dimP W Ch sel mu P hX) → X.K) ≃ₗ[X.K] MtildeV W Ch sel mu P :=
  LinearEquiv.ofBijective (zOf W Ch sel mu P hX) ⟨zOf_injective W Ch sel mu P hX, zOf_surjective W Ch sel mu P hX⟩

end Gen

end GlobalTheory.Mem.ColTie
