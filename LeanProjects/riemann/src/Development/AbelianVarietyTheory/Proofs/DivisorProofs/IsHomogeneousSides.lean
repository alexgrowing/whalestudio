import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArTopTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialNumeratorLinearExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveClIsHomogeneous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompEpsMul

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.EigWhole

open GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Mean4 GlobalTheory.Published GlobalTheory.FlagAr

theorem update_ind_one (T : Finset ℕ) (h : 1 ∉ T) : Function.update (ArIn.ind T) 1 false = ArIn.ind T := by
  funext q
  by_cases hq : q = 1
  · subst hq; simp [ArIn.ind, h]
  · rw [Function.update_of_ne hq]

theorem one_not_mem_setB {D : D7} (O : Setup D) (B : ℝ) : 1 ∉ Pad.setB O.κ B := by
  intro h
  rcases Finset.mem_union.1 h with h | h
  · exact Nat.not_prime_one (Finset.mem_filter.1 h).2
  · exact Nat.not_prime_one (Nat.prime_of_mem_primeFactors h)

theorem fam_support {D : D7} (O : Setup D) (T : Finset ℕ) (R : ℝ) (i : Var O) :
    ∀ a ∈ (fam O T R i).support, {q | a.1 q = true}.Finite ∧ a.2.1 = some R := by
  intro a ha
  have key : a.1 = ArIn.ind T ∧ a.2.1 = some R := by
    rcases i with x | l
    · simp only [fam, rootSym] at ha
      split_ifs at ha
      · have := Finsupp.support_single_subset ha
        simp only [Finset.mem_singleton] at this
        subst this; exact ⟨rfl, rfl⟩
      · have := Finsupp.support_single_subset ha
        simp only [Finset.mem_singleton] at this
        subst this; exact ⟨rfl, rfl⟩
    · rcases l with k | k
      · have := Finsupp.support_single_subset ha
        simp only [Finset.mem_singleton] at this
        subst this; exact ⟨rfl, rfl⟩
      · have := Finsupp.support_single_subset ha
        simp only [Finset.mem_singleton] at this
        subst this; exact ⟨rfl, rfl⟩
  refine ⟨?_, key.2⟩
  rw [key.1]
  simpa [ArIn.ind] using T.finite_toSet

end GlobalTheory.EigWhole

namespace GlobalTheory.EigWhole

open GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Mean4 GlobalTheory.Published GlobalTheory.FlagAr

variable {D : D7} (O : Setup D)

theorem mixEv_sieg (T : Finset ℕ) (hT : 1 ∉ T) (R : ℝ) (c : O.s.Comp) :
    (arIn O.s O.Φ O.met.hm).mixEv T R 1 c
        (X (Sum.inr (false, 2)) * DV.tagDR D.what₂.Tau O.N (curveCl D.what₂.Tau O.N O.j)) =
      rename (fam O T R) (C (1 / 2 : ℝ) * (∑ l, X (Sum.inr l) ^ 2) * rename Sum.inl (curveCl D.what₂.Tau O.N O.j)) := by
  have e1 : ((arIn O.s O.Φ O.met.hm).mixEv T R 1 c).comp (DV.tagDR D.what₂.Tau O.N) =
      rename fun x => (arIn O.s O.Φ O.met.hm).root (ArIn.ind T) R x c := by
    ext x : 1
    simp [ArIn.mixEv, DV.tagDR, update_ind_one T hT]
  have e2 := congrArg (fun f => f (curveCl D.what₂.Tau O.N O.j)) e1
  simp only [AlgHom.comp_apply] at e2
  rw [map_mul, e2, map_mul, map_mul, rename_rename]
  congr 1
  simp only [ArIn.mixEv, aeval_X, update_ind_one T hT, map_sum, map_pow, rename_X, map_mul, algHom_C]
  norm_num
  rfl

end GlobalTheory.EigWhole

namespace GlobalTheory.EigWhole

open GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Mean4 GlobalTheory.Published GlobalTheory.FlagAr

variable {D : D7} (O : Setup D)

theorem rename_testF_gen {σ : Type} (f : DV.Rt D.what₂.Tau O.N → σ) :
    rename f (testF O.Y) = (∑ x, X (f x) ^ 2) * rename f (curveCl D.what₂.Tau O.N O.j) := by
  have e : rename f (testF O.Y) =
      rename f (∑ τ, pSum τ 2 * curveCl D.what₂.Tau O.N O.j : Pol D.what₂.Tau O.N) := rfl
  rw [e, map_sum, Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_mul, show (pSum τ 2 : Pol D.what₂.Tau O.N) = ∑ i, X (τ, i) ^ 2 from rfl, map_sum, Finset.sum_mul]
  simp only [map_pow, rename_X]
  rw [Finset.sum_mul]

end GlobalTheory.EigWhole

namespace GlobalTheory.EigWhole

open GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Mean4 GlobalTheory.Published GlobalTheory.FlagAr

variable {D : D7} (O : Setup D)

theorem isHomogeneous_sides :
    ((∑ x, X (Sum.inl x) ^ 2) * rename (Sum.inl : DV.Rt D.what₂.Tau O.N → Var O) (curveCl D.what₂.Tau O.N O.j)).IsHomogeneous
        (dimFl D.what₂.Tau O.N + 1) ∧
    (C (1 / 2 : ℝ) * (∑ l, X (Sum.inr l) ^ 2) *
        rename (Sum.inl : DV.Rt D.what₂.Tau O.N → Var O) (curveCl D.what₂.Tau O.N O.j)).IsHomogeneous
        (dimFl D.what₂.Tau O.N + 1) := by
  classical
  have hι : 0 < Fintype.card D.what₂.Tau := Fintype.card_pos_iff.2 ⟨D.eTau.symm (Classical.arbitrary _)⟩
  obtain ⟨m, hm, hG⟩ := WholeShift.curveCl_isHomogeneous hι O.j O.indef.1 O.indef.2
  have hG' := hG.rename_isHomogeneous (f := (Sum.inl : DV.Rt D.what₂.Tau O.N → Var O))
  have hsq : ∀ v : Var O, (X v ^ 2 : MvPolynomial (Var O) ℝ).IsHomogeneous 2 := fun v => by
    simpa using (isHomogeneous_X ℝ v).pow 2
  refine ⟨?_, ?_⟩
  · have := (IsHomogeneous.sum Finset.univ (fun x : DV.Rt D.what₂.Tau O.N => (X (Sum.inl x) ^ 2 : MvPolynomial (Var O) ℝ)) 2 fun x _ => hsq (Sum.inl x)).mul hG'
    rwa [add_comm, hm] at this
  · have := ((isHomogeneous_C (Var O) (1 / 2 : ℝ)).mul (IsHomogeneous.sum Finset.univ (fun l : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N) => (X (Sum.inr l) ^ 2 : MvPolynomial (Var O) ℝ)) 2 fun l _ => hsq (Sum.inr l))).mul hG'
    rwa [zero_add, add_comm, hm] at this

theorem comp_eq (hM : RamModel) (hC : ArCalc) (hD : ArDegree) (hO : O.Core) (B : ℝ) (hB : 2 ≤ B) (R : ℝ)
    (hR : 2 ≤ R) (c : O.s.Comp) (hA : AwayAgree O (Pad.setB O.κ B) R c) :
    numL ((arIn O.s O.Φ O.met.hm).num c) (dimFl D.what₂.Tau O.N + 1)
        (rename (fun y => (arIn O.s O.Φ O.met.hm).root (ArIn.ind (Pad.setB O.κ B)) R y c) (testF O.Y)) =
      numL ((arIn O.s O.Φ O.met.hm).num c) (dimFl D.what₂.Tau O.N + 1)
        ((arIn O.s O.Φ O.met.hm).mixEv (Pad.setB O.κ B) R 1 c
          (X (Sum.inr (false, 2)) * DV.tagDR D.what₂.Tau O.N (curveCl D.what₂.Tau O.N O.j))) := by
  obtain ⟨x, P, hW⟩ := hO
  have hm := hW.hm_eq
  obtain ⟨-, h2⟩ := GlobalTheory.ArTopTrue.arTop_true hC hD GlobalTheory.ShFam.Pad.HTBound.htBound D O.A O.N O.j O.S O.κ O.s x O.Φ c R hR
  obtain ⟨M, L, m, Ψ, hI, hΨ, hnum⟩ := h2 (Var O) (fam O (Pad.setB O.κ B) R) (fam_support O _ R)
  have hdim := O.dim_eq c
  have hnum' : ∀ μ : Multiset (Var O), Multiset.card μ = dimFl D.what₂.Tau O.N + 1 →
      (arIn O.s O.Φ O.met.hm).num c (μ.map (fam O (Pad.setB O.κ B) R)) =
        Ψ ((μ.map X).prod) / ((((m : ℕ) : ℝ)) ^ ((O.Φ.C c).Y.dim + 1) * (Module.finrank ℚ D.what₂.LL : ℝ)) := by
    intro μ hμ
    rw [hm]
    exact hnum μ (by rw [hdim]; exact hμ)
  have key := GlobalTheory.NumLRename.numL_rename_of_agree _ _ _ Ψ _ hnum'
  have hz := hM D O ⟨x, P, hW⟩ B hB R hR c hA M L m Ψ (by rw [hm]; exact hI) hΨ
  have hL : rename (fun y => (arIn O.s O.Φ O.met.hm).root (ArIn.ind (Pad.setB O.κ B)) R y c) (testF O.Y) =
      rename (fam O (Pad.setB O.κ B) R)
        ((∑ x, X (Sum.inl x) ^ 2) * rename Sum.inl (curveCl D.what₂.Tau O.N O.j)) := by
    rw [rename_testF_gen, map_mul, map_sum, rename_rename]
    simp only [map_pow, rename_X]
    rfl
  obtain ⟨hPL, hPR⟩ := isHomogeneous_sides O
  rw [hL, mixEv_sieg O _ (one_not_mem_setB O B)]
  refine (key _ hPL).trans (Eq.trans ?_ (key _ hPR).symm)
  congr 1
  have e : diffPol O = C (1 / 2 : ℝ) * (∑ l, X (Sum.inr l) ^ 2) * rename Sum.inl (curveCl D.what₂.Tau O.N O.j) -
      (∑ x, X (Sum.inl x) ^ 2) * rename Sum.inl (curveCl D.what₂.Tau O.N O.j) := by
    rw [diffPol]; ring
  rw [e, map_sub, sub_eq_zero] at hz
  exact hz.symm

end GlobalTheory.EigWhole

namespace GlobalTheory.EigWhole

open GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Mean4 GlobalTheory.Published GlobalTheory.FlagAr

theorem latAt_of_ramModel : RamModel → Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB →
    PrismaticDieudonnePerfd → OnObj fun _ O _ _ _ _ => LatAt O.Y := by
  intro hM h2 hH _ _ _ D O hO _ A T H hRd B hB R hR
  rw [Setup.setB_eq O B]
  have eR : sieg O.Y (Pad.setB O.κ B) R = (arIn O.s O.Φ O.met.hm).arMix (Pad.setB O.κ B) R 1
      (X (Sum.inr (false, 2)) * DV.tagDR D.what₂.Tau O.N (curveCl D.what₂.Tau O.N O.j)) := rfl
  have eR' : (arIn O.s O.Φ O.met.hm).arMix (Pad.setB O.κ B) R 1
      (X (Sum.inr (false, 2)) * DV.tagDR D.what₂.Tau O.N (curveCl D.what₂.Tau O.N O.j)) =
      ∑ c, numL ((arIn O.s O.Φ O.met.hm).num c) (dimFl D.what₂.Tau O.N + 1)
        ((arIn O.s O.Φ O.met.hm).mixEv (Pad.setB O.κ B) R 1 c
          (X (Sum.inr (false, 2)) * DV.tagDR D.what₂.Tau O.N (curveCl D.what₂.Tau O.N O.j))) := by
    rw [ArIn.arMix, LinearMap.sum_apply]; rfl
  have eL : O.Y.arDeg (Pad.setB O.κ B) R (testF O.Y) =
      ∑ c, numL ((arIn O.s O.Φ O.met.hm).num c) (dimFl D.what₂.Tau O.N + 1)
        (rename (fun y => (arIn O.s O.Φ O.met.hm).root (ArIn.ind (Pad.setB O.κ B)) R y c) (testF O.Y)) := by
    have e0 : O.Y.arDeg (Pad.setB O.κ B) R (testF O.Y) =
        (arIn O.s O.Φ O.met.hm).arDeg (Pad.setB O.κ B) R (testF O.Y : Pol D.what₂.Tau O.N) := rfl
    have hsum : ∀ F : Pol D.what₂.Tau O.N, (arIn O.s O.Φ O.met.hm).arDeg (Pad.setB O.κ B) R F =
        ∑ c, numL ((arIn O.s O.Φ O.met.hm).num c) (dimFl D.what₂.Tau O.N + 1)
          (rename (fun y => (arIn O.s O.Φ O.met.hm).root (ArIn.ind (Pad.setB O.κ B)) R y c) F) := fun F => by
      rw [ArIn.arDeg, LinearMap.sum_apply]; rfl
    exact e0.trans (hsum _)
  rw [eR, eR', eL]
  exact Finset.sum_congr rfl fun c _ =>
    comp_eq O hM h2.p4 hH.deg hO B hB R hR c (GlobalTheory.T.eigen_away_agree D O hO _ R c)

end GlobalTheory.EigWhole

end
