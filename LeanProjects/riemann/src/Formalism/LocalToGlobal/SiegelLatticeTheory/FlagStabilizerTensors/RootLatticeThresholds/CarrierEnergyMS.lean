import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ConstPinOfStd

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S IsDedekindDomain

namespace Formalism.L2.SG.Pf.Carrier.EnergyMS

open Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.Carrier.EnergyConst Formalism.L2.SG.Pf.Carrier.EnergyConst2 Formalism.L2.SG.TypedSets Function

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def dN (v : PlX X) : ℝ := ((Ideal.absNorm (v.maxPowDividing (differentIdeal ℤ (𝓞 X.B.I.F))) : ℕ) : ℝ)

open Classical in

def nT (v : PlX X) : ℝ :=
  if TypAt X v then ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) else 1

end Defs

def MSOrd : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ → IsStdChar ψ →
    ∀ v : PlX X, ¬ TypAt X v → localVolumeUnit X ψ v = dN X v ^ e1 D * ZZX X u u' ψ v

def MSTyp : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ → IsStdChar ψ →
    ∀ v : PlX X, TypAt X v → 0 < ZZX X u u' ψ v →
      localVolumeUnit X ψ v = dN X v ^ e1 D * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) *
        ZZX X u u' ψ v

def DiffProd : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
    HasFiniteMulSupport (dN X) ∧ ∏ᶠ v, dN X v = |((NumberField.discr X.B.I.F : ℤ) : ℝ)|

def DiscRd : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), |((NumberField.discr X.B.I.F : ℤ) : ℝ)| = D.host.rdE ^ D.R.f

def TypNorm : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
    ∏ p : TypX X, ((Ideal.absNorm p.1.asIdeal : ℕ) : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ D.R.f

theorem lemmaMSStd_of (hO : MSOrd) (hT : MSTyp) (hD : DiffProd) (hR : DiscRd) (hN : TypNorm)
    {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : LemmaMSStd X u u' ψ := by
  classical
  intro hψ hstd hC
  set k := (D.R.rS + 1) * (2 * D.R.rS + 3) with hk
  have hZpos : ∀ v, 0 < ZZX X u u' ψ v := fun v => (hC.1 v).2.2.1
  have hU00m : Multipliable (fun v : OrdX X => localVolumeUnit X ψ v.1) := hC.2.2.2.1
  have hZm : Multipliable (ZZX X u u' ψ) := hC.2.2.2.2.2.1
  have hloc : ∀ v, localVolumeUnit X ψ v = (dN X v ^ e1 D * nT X v) * ZZX X u u' ψ v := by
    intro v
    by_cases hv : TypAt X v
    · rw [hT D X u u' ψ hψ hstd v hv (hZpos v)]
      simp only [nT, if_pos hv]
    · rw [hO D X u u' ψ hψ hstd v hv]
      simp only [nT, if_neg hv, mul_one]
  obtain ⟨hDf, hDp⟩ := hD D X

  set s : Set (PlX X) := ↑(Formalism.L2.SG.TypedSets.typSet X.B.I.F (D.host.g 0) (D.host.g 1)) with hs
  have hnTs : Function.mulSupport (nT X) ⊆ s := by
    intro v hv
    by_contra h
    exact hv (by unfold nT; exact if_neg (show ¬ TypAt X v from h))
  have hnTf : HasFiniteMulSupport (nT X) := (Finset.finite_toSet _).subset hnTs
  have hAf : HasFiniteMulSupport (fun v => dN X v ^ e1 D * nT X v) := (hDf.pow _).mul hnTf

  have h1 : (∏' v : OrdX X, localVolumeUnit X ψ v.1) * ∏ p : TypX X, localVolumeUnit X ψ p.1 = ∏' v, localVolumeUnit X ψ v := by
    have hsm : Multipliable ((localVolumeUnit X ψ) ∘ ((↑) : s → PlX X)) := Multipliable.of_finite
    have hscm : Multipliable ((localVolumeUnit X ψ) ∘ ((↑) : ↑sᶜ → PlX X)) := hU00m
    rw [← Multipliable.tprod_mul_tprod_compl hsm hscm, mul_comm]
    congr 1
    rw [tprod_fintype]
    rfl

  have h2 : ∏' v, localVolumeUnit X ψ v = (∏ᶠ v, (dN X v ^ e1 D * nT X v)) * ∏' v, ZZX X u u' ψ v := by
    rw [tprod_congr hloc, Multipliable.tprod_mul (multipliable_of_hasFiniteMulSupport hAf) hZm,
      tprod_eq_finprod hAf]

  have h3 : (∏ᶠ v, (dN X v ^ e1 D * nT X v)) =
      D.host.rdE ^ (D.R.f * e1 D) * ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * k) := by
    have hDpow : HasFiniteMulSupport (fun v => dN X v ^ e1 D) := hDf.pow _
    rw [finprod_mul_distrib hDpow hnTf, ← finprod_pow hDf, hDp, hR D X, ← pow_mul]
    congr 1
    rw [finprod_eq_prod_of_mulSupport_subset (nT X) hnTs, pow_mul, ← hN D X, ← Finset.prod_pow]
    rw [← Finset.prod_coe_sort]
    refine Finset.prod_congr rfl fun p _ => ?_
    unfold nT
    exact if_pos (show TypAt X p.1 from p.2)
  unfold LemmaMS
  show (∏' v : OrdX X, localVolumeUnit X ψ v.1) * ∏ p : TypX X, localVolumeUnit X ψ p.1 = _ * (∏' v : PlX X, ZZX X u u' ψ v)
  rw [h1, h2, h3]

end Formalism.L2.SG.Pf.Carrier.EnergyMS
