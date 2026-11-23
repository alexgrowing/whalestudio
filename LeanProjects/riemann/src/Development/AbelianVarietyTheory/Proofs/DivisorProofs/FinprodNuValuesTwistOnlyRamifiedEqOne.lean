import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveHeckeLFunctionInvOfTrivialOnMaxReal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties

open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistPairs

open Formalism.L2.Host Formalism.L2.Host.CT GlobalTheory.CMVal.InvConj

theorem conjPl_eq_plMap {D : D7} [IsCMField D.host.E] (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Formalism.DivisionValues.conjPl P = plMap conjE P := by
  apply HeightOneSpectrum.ext
  rw [asIdeal_plMap]
  show P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) = _
  congr 1
  refine RingEquiv.ext fun x => RingOfIntegers.ext ?_
  rfl

theorem conjE_symm {E : Type} [Field E] [NumberField E] [IsCMField E] : (conjE (E := E)).symm = conjE :=
  RingEquiv.ext fun x => by rw [conjE_symm_apply, conjE_apply]

theorem finprod_val_nu_eq_one : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T},
    Lc.Is μ₀ → ∀ (i j : Fin D.R.m) (t : T), ∏ᶠ (w : HeightOneSpectrum (𝓞 D.host.E))
      (_ : ¬ (Lc.xiH t).UnrAt w ∧ (nuH G μ₀ i j).UnrAt w), (((nuH G μ₀ i j).val w : ℂˣ) : ℂ) = 1 := by
  intro D T Lc sc G μ₀ hL i j t
  classical
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  set ν := nuH G μ₀ i j with hν
  have hT : TrivOnF ν := (GlobalTheory.FunObj.SqNum.Model.isValChar_nu hL G i j (s := 0) (Nat.zero_le _)).1.2.1
  set c : HeightOneSpectrum (𝓞 D.host.E) → HeightOneSpectrum (𝓞 D.host.E) := fun P => Formalism.DivisionValues.conjPl P with hcdef
  have hc : ∀ P, c P = plMap conjE P := fun P => conjPl_eq_plMap P
  have hcc : ∀ P, c (c P) = P := fun P => by
    rw [hc, hc]
    have h := plMap_symm_plMap (conjE (E := D.host.E)) P
    rwa [conjE_symm] at h
  have hcinj : Function.Injective c := fun x y h => by rw [← hcc x, h, hcc y]
  have hunr : ∀ P, ν.UnrAt P ↔ ν.UnrAt (c P) := fun P => by
    rw [hc, ← unrAt_inv_iff ν hT P]
    simp only [HChar.UnrAt, HChar.loc_inv, inv_eq_one]
  have hval : ∀ P, ν.UnrAt P → ((ν.val P : ℂˣ) : ℂ) * ((ν.val (c P) : ℂˣ) : ℂ) = 1 := fun P hP => by
    have h1 := val_inv_eq ν hT P (by rw [← hc]; exact (hunr P).1 hP)
    rw [HChar.val_inv] at h1
    rw [hc, ← h1, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  set Q' := (Lc.Q t).filter fun P => ν.UnrAt P with hQ'
  have hset : {w | ¬ (Lc.xiH t).UnrAt w ∧ ν.UnrAt w} = (↑(Q' ∪ Q'.image c) : Set (HeightOneSpectrum (𝓞 D.host.E))) := by
    ext w
    simp only [Set.mem_setOf_eq, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image, Finset.mem_coe, hQ',
      Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      rcases (hL.Q_ram t w).1 h1 with h | ⟨P, hP, hcP⟩
      · exact Or.inl ⟨h, h2⟩
      · have e : w = c P := GlobalTheory.GoodPrimes.isConjPl_iff.1 hcP
        exact Or.inr ⟨P, ⟨hP, (hunr P).2 (e ▸ h2)⟩, e.symm⟩
    · rintro (⟨h, h2⟩ | ⟨P, ⟨hP, h2⟩, rfl⟩)
      · exact ⟨(hL.Q_ram t w).2 (Or.inl h), h2⟩
      · exact ⟨(hL.Q_ram t (c P)).2 (Or.inr ⟨P, hP, GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl⟩), (hunr P).1 h2⟩
  have hdisj : Disjoint Q' (Q'.image c) := by
    rw [Finset.disjoint_left]
    intro P hP hP'
    obtain ⟨P', hP'Q, e⟩ := Finset.mem_image.1 hP'
    exact ((hL.Q_pl t) P' (Finset.mem_filter.1 hP'Q).1).2 P (Finset.mem_filter.1 hP).1 (GlobalTheory.GoodPrimes.isConjPl_iff.2 e.symm)
  show ∏ᶠ w ∈ {w | ¬ (Lc.xiH t).UnrAt w ∧ ν.UnrAt w}, ((ν.val w : ℂˣ) : ℂ) = 1
  rw [hset, finprod_mem_coe_finset, Finset.prod_union hdisj, Finset.prod_image fun x _ y _ h => hcinj h,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun P hP => hval P (Finset.mem_filter.1 hP).2

end GlobalTheory.TwistPairs
