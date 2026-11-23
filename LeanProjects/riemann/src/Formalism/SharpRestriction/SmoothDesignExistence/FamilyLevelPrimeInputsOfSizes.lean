import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLl
import Formalism.LocalRingCardinality.Lemmas
import Formalism.SharpRestriction.Divisibility.ClosedSizeLink.AdmissibleFamilyOfThreshold
import Formalism.SharpRestriction.SmoothDesignExistence.LatticeIndexTer
import Formalism.SharpRestriction.SmoothDesignExistence.WithSmOfWithCh
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLw

noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions Formalism.BasicNotions.DV

section Family

variable {eps : ℝ} (Fm : FamP eps)

structure BrT : Prop where

  t5Tw : DIV.Ev Fm fun x hx i => J.LevelPrimeColumnOtherTuples (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw

  tg : DIV.Ev Fm fun x _ i => WeightDegreeSizes.LevelPrimeNotTypePrime (Fm.D x i)

variable {Fm}

theorem admissible_dgamma_tuples (hT : TuSize Fm) (hDl : J.DlSize Fm) (hS : DGamSmooth Fm) :
    DIV.Ev Fm fun x _ i => WeightDegreeSizes.LevelPrimeCoprimeStabiliser (Fm.D x i) :=
  ((DIV.Ev.of_ge (settingF Fm hT hDl)).and (DIV.Ev.of_ge hS)).imp fun x _ i ⟨hs, hp⟩ u hd =>
    absurd (hp u _ ((Fm.D x i).mem u).A.T_prime hd) (not_le.mpr (hs u).1)

theorem servedModel_of_params {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (X : G.Inst D L) (K : G.Consts)
    (h3 : 3 ≤ L.sc.x ^ (L.sc.ez / 5)) : WeightDegreeSizes.ServedHasModel X K := by
  intro u w hw hVV
  have hc : G.Cand D L K (D.what₂.places.resChar w) := by
    by_contra hn
    apply hVV
    unfold G.VV
    rw [if_neg (fun h => hn h.1)]
  exact gIdx_of_cand P K h3 u _ hc hw

theorem servedF (he : 0 < eps) : DIV.Ev Fm fun x _ i => WeightDegreeSizes.ServedHasModel (Fm.Gx x i) Fm.GK :=
  ⟨(3 : ℝ) ^ (5 / Fm.ez), fun x h3 h1 i => servedModel_of_params (Fm.params x h1 i) _ _ (by
    have hez : 0 < Fm.ez := by rw [← Fm.L_ez x i]; exact (Fm.L x i).sc.ez_pos
    rw [Fm.L_x x i h1, Fm.L_ez x i]
    calc (3 : ℝ) = ((3 : ℝ) ^ (5 / Fm.ez)) ^ (Fm.ez / 5) := by
          rw [← Real.rpow_mul (by norm_num), show 5 / Fm.ez * (Fm.ez / 5) = 1 by field_simp, Real.rpow_one]
      _ ≤ x ^ (Fm.ez / 5) := Real.rpow_le_rpow (by positivity) h3 (by positivity))⟩

theorem familyLevelPrimeInputs_of_sizes {crystallineComparison : ℝ} (he : 0 < eps) (hT : TuSize Fm) (hDl : J.DlSize Fm) (hS : DGamSmooth Fm) (h10 : LevelPrimeItems Fm crystallineComparison) (B : BrT Fm) :
    WeightDegreeSizes.FamilyLevelPrimeInputs Fm := by
  have p := DIV.Ev.of_ge (level_prime_items_large_scale Fm hT hDl h10)
  exact (p.and (B.t5Tw.and (B.tg.and ((admissible_dgamma_tuples hT hDl hS).and (servedF he))))).imp fun x hx i ⟨p, t5, tg, dg, sv⟩ =>
    ⟨J.levelColumn_of_sharpBound (fun u => (p u).2.2.2) t5,
      J.sizeData_at_level_primes_of_defs (Fm.params x hx i) (Fm.ex x hx i).fdef (Fm.ex x hx i).err.edef tg, dg, sv⟩

theorem integrality_last_map {crystallineComparison : ℝ} (hT : TuSize Fm) (hDl : J.DlSize Fm) (h10 : LevelPrimeItems Fm crystallineComparison) :
    DIV.Ev Fm fun x _ i => WeightDegreeSizes.MemberChainIntegral (Fm.D x i) :=
  (DIV.Ev.of_ge (level_prime_items_large_scale Fm hT hDl h10)).imp fun _ _ _ p u => (p u).2.2.1

theorem kernels_rational_over_field {crystallineComparison : ℝ} (hT : TuSize Fm) (hDl : J.DlSize Fm) (h10 : LevelPrimeItems Fm crystallineComparison) (hLL : LLKerE Fm) :
    DIV.Ev Fm fun x _ i => LocalQuadraticParts.KernelRationality (Fm.D x i) := by
  obtain ⟨x0, hk⟩ := kRatE_of hLL
  have k : DIV.Ev Fm fun x _ i => StandardLatticesGL3.kRat (Fm.D x i) := ⟨x0, fun x hx h1 i => hk x hx h1 i⟩
  exact ((DIV.Ev.of_ge (level_prime_items_large_scale Fm hT hDl h10)).and k).imp fun _ _ _ ⟨p, k⟩ => J.kernels_rational_over_coefficients _ k (fun u => (p u).2.2.1)

theorem stmtPairF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), WeightDegreeSizes.PairingFromIntegrality (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw :=
  fun x hx i => J.pairing_integrality_both_sides _ _

theorem vanishing_above_threshold : DIV.Ev Fm fun x _ i => LocalQuadraticParts.ZeroGainAbove (Fm.L x i) := by
  unfold DIV.Ev
  refine ⟨0, fun x _ hx i => J.gains_losses_eq_defined (Fm.Gx x i) Fm.GK _ _ (Fm.fills x hx i) (Fm.ex x hx i).err.edef⟩

theorem admissible_complement_two (hc : Fm.cX.err.Large) (h : WeightDegreeSizes.FamilySecondComplementInputs Fm) :
    ∃ C, DIV.Ev Fm fun x _ i => LocalQuadraticParts.adm11 (Fm.D x i) (Fm.L x i) C := by
  obtain ⟨C, x0, h⟩ := WeightDegreeSizes.secondComplement_family_of_large Fm hc h
  exact ⟨C, x0, fun x hx h1 i => h x hx h1 i⟩

end Family

end Formalism.MainNotions.Pk

end
