import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyMS

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S IsDedekindDomain Function

namespace Formalism.L2.SG.Pf.Carrier.EnergyMS

open Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StepGSplit : Prop := ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), GSplitX X

def TypCount : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (i : Fin 2),
    (Finset.univ.filter (fun p : TypX X => gAt X p.1 = D.host.g i)).card = D.R.f

theorem typNorm_of (hG : StepGSplit) (hC : TypCount) : TypNorm := by
  intro D X
  have hgA : ∀ p : TypX X, ((Ideal.absNorm p.1.asIdeal : ℕ) : ℝ) = ((gAt X p.1 : ℕ) : ℝ) := fun p => by
    rw [(hG D X p).1]
  simp only [hgA]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun p : TypX X => gAt X p.1 = D.host.g 0)]
  have h0 : ∀ p ∈ Finset.univ.filter (fun p : TypX X => gAt X p.1 = D.host.g 0),
      ((gAt X p.1 : ℕ) : ℝ) = ((D.host.g 0 : ℕ) : ℝ) := fun p hp => by
    rw [(Finset.mem_filter.1 hp).2]
  have h1 : ∀ p ∈ Finset.univ.filter (fun p : TypX X => ¬ gAt X p.1 = D.host.g 0),
      ((gAt X p.1 : ℕ) : ℝ) = ((D.host.g 1 : ℕ) : ℝ) := fun p hp => by
    have h := (Finset.mem_filter.1 hp).2
    unfold gAt at h ⊢
    split_ifs at h ⊢ with hg
    · exact absurd rfl h
    · rfl
  rw [Finset.prod_congr rfl h0, Finset.prod_congr rfl h1, Finset.prod_const, Finset.prod_const]
  have hc1 : Finset.univ.filter (fun p : TypX X => ¬ gAt X p.1 = D.host.g 0) =
      Finset.univ.filter (fun p : TypX X => gAt X p.1 = D.host.g 1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold gAt
    have hne := D.host.g_ne
    split_ifs <;> simp [hne, Ne.symm hne]
  rw [hc1, hC D X 0, hC D X 1, Formalism.MainNotions.S.Lat.gS, Nat.cast_mul, mul_pow]

theorem dN_eq {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : PlX X) :
    dN X v = ((Nat.castRingHom ℝ : ℕ →* ℝ).comp (Ideal.absNorm : Ideal (𝓞 X.B.I.F) →*₀ ℕ).toMonoidHom)
      (v.maxPowDividing (differentIdeal ℤ (𝓞 X.B.I.F))) := rfl

theorem diffProd_holds : DiffProd := by
  intro D X
  have hne : differentIdeal ℤ (𝓞 X.B.I.F) ≠ ⊥ := by
    intro h
    have h2 := NumberField.absNorm_differentIdeal (K := X.B.I.F) (𝓞 X.B.I.F)
    rw [h, Ideal.absNorm_bot] at h2
    exact NumberField.discr_ne_zero X.B.I.F (Int.natAbs_eq_zero.mp h2.symm)
  have hfin := Ideal.finite_mulSupport hne
  have hdN : dN X = fun v => ((Nat.castRingHom ℝ : ℕ →* ℝ).comp
      (Ideal.absNorm : Ideal (𝓞 X.B.I.F) →*₀ ℕ).toMonoidHom) (v.maxPowDividing (differentIdeal ℤ (𝓞 X.B.I.F))) :=
    funext (fun v => dN_eq X v)
  refine ⟨?_, ?_⟩
  · rw [hdN]
    exact hfin.subset (Function.mulSupport_comp_subset (map_one _) _)
  · rw [hdN, ← MonoidHom.map_finprod _ hfin, Ideal.finprod_heightOneSpectrum_factorization hne]
    show ((Ideal.absNorm (differentIdeal ℤ (𝓞 X.B.I.F)) : ℕ) : ℝ) = _
    rw [NumberField.absNorm_differentIdeal (K := X.B.I.F) (𝓞 X.B.I.F), Nat.cast_natAbs, Int.cast_abs]

def DiscEF : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
    |((NumberField.discr X.B.I.E : ℤ) : ℝ)| = |((NumberField.discr X.B.I.F : ℤ) : ℝ)| ^ 2

def DegE : Prop := ∀ (D : D7), Module.finrank ℚ D.host.E = 2 * D.R.f

theorem discRd_of (hE : DiscEF) (hd : DegE) : DiscRd := by
  intro D X
  have hdisc : NumberField.discr X.B.I.E = NumberField.discr D.host.E :=
    NumberField.discr_eq_discr_of_algEquiv (K := X.B.I.E) X.ιE.toRatAlgEquiv
  have h1 := hE D X
  rw [hdisc] at h1
  have h2 := hd D
  have ha : 0 ≤ |((NumberField.discr X.B.I.F : ℤ) : ℝ)| := abs_nonneg _
  have hpos : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
  have hf : (D.R.f : ℝ) ≠ 0 := by
    have : D.R.f ≠ 0 := by omega
    exact_mod_cast this
  unfold Formalism.BasicNotions.Host.rdE
  rw [h1, h2, ← Real.rpow_natCast (|((NumberField.discr X.B.I.F : ℤ) : ℝ)|) 2, ← Real.rpow_mul ha,
    ← Real.rpow_natCast _ D.R.f, ← Real.rpow_mul ha]
  have hex : ((2 : ℕ) : ℝ) * (1 / ((2 * D.R.f : ℕ) : ℝ)) * (D.R.f : ℝ) = 1 := by
    push_cast
    field_simp
  rw [hex, Real.rpow_one]

theorem lemmaMSStd_of_leaves (hO : MSOrd) (hT : MSTyp) (hG : StepGSplit) (hC : TypCount) (hE : DiscEF) (hd : DegE)
    {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : Formalism.L2.SG.Pf.Carrier.EnergyConst2.LemmaMSStd X u u' ψ := by
  exact lemmaMSStd_of hO hT diffProd_holds (discRd_of hE hd) (typNorm_of hG hC) X u u' ψ

end Formalism.L2.SG.Pf.Carrier.EnergyMS
