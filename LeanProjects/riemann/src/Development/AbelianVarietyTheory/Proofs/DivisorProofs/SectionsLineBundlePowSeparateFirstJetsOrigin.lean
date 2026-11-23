import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetFiltrationSectionCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsChangeSectionBasis
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsUniqueSecIsFnAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.MBLow.JetSep

theorem sep : ∀ (K : Type) [Field K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (N : ℕ), 4 ≤ N → ∀ (i₀ : x.P.L.ι),
    ⊤ ≤ (𝟙 (Sp K) ≫ eSec x.P.A) ⁻¹ᵁ x.P.L.U i₀ → ∀ (j₀ : Fin g) (a : K) (c : Fin g → K),
    (∀ s : LB.Sec (LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))),
      a * (valR (epsLift (x.v (j₀.cast hg.symm))) ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀)
          (s.f fun _ => i₀)).fst +
        ∑ j, c j * (valR (epsLift (x.v (j.cast hg.symm))) ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀)
          (s.f fun _ => i₀)).snd = 0) →
    a = 0 ∧ c = 0 := by
  intro K _ x g hg N hN i₀ hi₀ j₀ a c H
  subst hg
  have := x.P.isAb.comm
  have k₀ : ⊤ ≤ eSec x.P.A ⁻¹ᵁ x.P.L.U i₀ := by simpa using hi₀
  let U' : x.P.A.left.Opens := (lbPow x.P.L N).U fun _ => i₀
  have hU' : ⊤ ≤ eSec x.P.A ⁻¹ᵁ U' :=
    (GlobalTheory.ThetaFn.le_wchart_unique x.P.L (K := PUnit) (eSec x.P.A) (𝟙 _) (fun _ => i₀)).2 (by simpa using k₀)
  let pb : (lbPow x.P.L N).Sec → LB.Sec (LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))) := fun s =>
    GlobalTheory.ThetaFn.pullPow x.P.L (K := PUnit) (K' := Fin 1) (snd (baseOver (Sp K)) x.P.A).left
      (Category.comp_id _) (N : ℤ) s
  have hval : ∀ (s : (lbPow x.P.L N).Sec) (w : epsR K ⟶ x.P.A), IsTangent w →
      valR (epsLift w) ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀) ((pb s).f fun _ => i₀) =
        valR w.left U' (s.f fun _ => i₀) := by
    intro s w hw
    have h1 : ⊤ ≤ epsLift w ⁻¹ᵁ ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀) := by
      refine (GlobalTheory.ThetaFn.le_wchart_unique x.P.L (K := Fin 1) (epsLift w) _ (fun _ => i₀)).2 ?_
      rw [JetUniq.epsLift_snd]
      exact JetUniq.tan_le hw k₀
    refine (GlobalTheory.HolHom.valR_appLE _ _ _ _ _ _ h1).trans ?_
    rw [JetUniq.epsLift_snd]
    rfl
  have Hs : ∀ s : (lbPow x.P.L N).Sec, a * valR (eSec x.P.A) U' (s.f fun _ => i₀) +
      (valR (tanComb c x.v).left U' (s.f fun _ => i₀)).snd = 0 := by
    intro s
    have e := H (pb s)
    simp only [Fin.cast_eq_self] at e
    rw [hval s _ (x.basis.1 j₀), JetUniq.fst_valR (x.basis.1 j₀) hU'] at e
    rw [JetUniq.snd_valR x.basis.1 (isLieComb_tanComb c x.v) hU']
    refine Eq.trans ?_ e
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hval s _ (x.basis.1 j)]
  obtain ⟨M, sec, hsec⟩ := GlobalTheory.ZH.CrdMove.immBy_lbPow GlobalTheory.allSixLaws.1.ample K x.P N hN
  have key : ∀ d : Fin x.P.g → K, d ≠ 0 → ∃ s₀ s₁ : (lbPow x.P.L N).Sec,
      valR (eSec x.P.A) U' (s₀.f fun _ => i₀) ≠ 0 ∧ valR (eSec x.P.A) U' (s₁.f fun _ => i₀) = 0 ∧
      (valR (tanComb d x.v).left U' (s₁.f fun _ => i₀)).snd ≠ 0 := by
    intro d hd
    have hy := isTangent_tanComb K x.P.A _ x.v d x.basis.1
    obtain ⟨s₀, s₁, h0, h1, h2⟩ := Orders.exists_sep sec hsec hy (Orders.tanComb_ne_one x.basis hd) (fun _ => i₀) hU'
    refine ⟨s₀, s₁, ?_, ?_, ?_⟩
    · rwa [Orders.valR_eq _ _ hU']
    · rwa [Orders.valR_eq _ _ hU']
    · rwa [Orders.valR_eq _ _ (Orders.top_le_tangent hy hU')]
  have hc : c = 0 := by
    by_contra hc
    obtain ⟨-, s₁, -, h1, h2⟩ := key c hc
    have e := Hs s₁
    rw [h1, mul_zero, zero_add] at e
    exact h2 e
  refine ⟨?_, hc⟩
  have hd : (Pi.single j₀ 1 : Fin x.P.g → K) ≠ 0 := fun h => by simpa using congrFun h j₀
  obtain ⟨s₀, -, h0, -, -⟩ := key _ hd
  have e := Hs s₀
  subst hc
  rw [JetUniq.snd_valR x.basis.1 (isLieComb_tanComb 0 x.v) hU'] at e
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] at e
  exact (mul_eq_zero.1 e).resolve_right h0

end GlobalTheory.MBLow.JetSep

end
