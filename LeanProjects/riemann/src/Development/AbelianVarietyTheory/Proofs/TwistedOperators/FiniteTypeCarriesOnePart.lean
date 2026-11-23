import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabelThetaLiftSpaceIffDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePolynomialsOfCarriedEigensystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertValuesIffInertLabelsCarriedEigensystems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPartnerCombinationGoodInertLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodSplitPlaceOfFamilyPrimeBaseTupleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeEigenvaluesEqOfDualEnlargingLabelsSplitStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.CarriesOne

open GlobalTheory.Hk3

theorem heckePolyOf_coeff_inj : ∀ (n q : ℕ), q ≠ 0 → ∀ a b : ℕ → ℂ, Formalism.L2.Col.heckePolyOf n q a = Formalism.L2.Col.heckePolyOf n q b → ∀ k ≤ n, a k = b k := by
  intro n q hq a b h k hk
  have hc := congrArg (fun f => Polynomial.coeff f k) h
  simp only [Formalism.L2.Col.heckePolyOf, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow] at hc
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos (Finset.mem_range.2 (Nat.lt_succ_of_le hk)),
    if_pos (Finset.mem_range.2 (Nat.lt_succ_of_le hk))] at hc
  have h0 : ((-1 : ℂ) ^ k * (q : ℂ) ^ (k * (k - 1) / 2)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hq))
  exact mul_left_cancel₀ h0 hc

theorem parts_eq_of_rowLabels : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ SF, GlobalTheory.Hk3.IsSF R SF → ∀ (c c' : Pl D.host.E → List ℤ → ℂ), (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.IsLab (Yc D 0) P d → c P (dualLab d) = c' P (dualLab d)) → GlobalTheory.Hk3.EEc R SF c = GlobalTheory.Hk3.EEc R SF c' ∧ ∀ i, GlobalTheory.Hk3.Wcc R SF i c = GlobalTheory.Hk3.Wcc R SF i c' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF c c' key
  obtain ⟨hQ, hgood, hoff, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev
  refine ⟨?_, fun i => ?_⟩
  · obtain ⟨n, hβ⟩ := hC.lev.βY 0 (by have := D.R.two_le_m; omega)
    have hlev := fun (P : Pl D.host.E) (hP : Good R A.μ0 P) =>
      GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D 0) (R.βY 0) (R.ΛY 0) ((D.host.g 0 * D.host.g 1) ^ n) (R.dat0 R.triv) hβ P
        (by
          intro h
          push_cast at h
          exact (hgood A.μ0 P hP).1 (P.isPrime.mem_of_pow_mem _ (by exact_mod_cast h)))
        (by
          intro PP hPP
          refine hP PP (hPP.imp id ?_)
          intro h
          exact absurd h (Finset.notMem_empty _))
    unfold GlobalTheory.Hk3.EEc partDual
    congr 1
    ext U
    rw [LabDet.mem_partFull, LabDet.mem_partFull]
    refine and_congr_right fun _ => forall_congr' fun P => forall_congr' fun d => forall_congr' fun B => imp_congr_right fun hB => ?_
    have hP : Good R A.μ0 P := by
      obtain ⟨_, _, _, _, ho, _⟩ := hB
      exact (hoff SF hSF P).1 ho
    rw [key P d hP ⟨B, (((hlev P hP).2.1 SF d B).1 hB).2⟩]
  · obtain ⟨n, hβ⟩ := hC.lev.βW i
    have hlev := fun (P : Pl D.host.E) (hP : Good R A.μ0 P) =>
      GlobalTheory.T.level_operators_at_prime_off_level_datum (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ P
        (by rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top)
        (by
          intro PP hPP
          refine hP PP (hPP.imp id ?_)
          intro h
          exact absurd h (Finset.notMem_empty _))
    have keyW : ∀ P, Good R A.μ0 P → ∀ d, IsLab (Wc D i) P d → c P d = c' P d := by
      intro P hP d hd
      have h := key P (dualLab d) hP ((GlobalTheory.LabEq.isLab_W_iff R F (s := 0) hC i P d hP).1.1 hd)
      rwa [GlobalTheory.CarriedHecke.dualLab_dualLab] at h
    have hpf : partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c =
        partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c' := by
      ext U
      rw [LabDet.mem_partFull, LabDet.mem_partFull]
      refine and_congr_right fun _ => forall_congr' fun P => forall_congr' fun d => forall_congr' fun B => imp_congr_right fun hB => ?_
      have hP : Good R A.μ0 P := by
        obtain ⟨_, _, _, _, ho, _⟩ := hB
        exact (hoff SF hSF P).1 ho
      rw [keyW P hP d ⟨B, (((hlev P hP).2.1 SF d B).1 hB).2⟩]
    unfold Wcc
    rw [hpf]

theorem parts_eq_of_carries : GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → UpInj R.toRealDat → (∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c') := by

  intro hHowe hCusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hW e hInert hUp p c c' hc hc'
  obtain ⟨hC, hSF, hE, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW e
  have hS := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCusp R.toRealDat
  have hL := GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hCusp D
  have hTwo := GlobalTheory.VmTwo.twoSided_goodInert hHowe R F hL hW e hS
  have hinj : ∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0 :=
    fun _ w _ h => hUp A3.A.μ0 (h.trans (map_zero _).symm)
  have hpol := GlobalTheory.CarriedHecke.hecke_polys_of_carries R F hL hok hW e hS hinj
  have hr : (Yc D 0).rank = D.R.r := by
    show (D.sp.Y (min 0 D.R.m)).rank = D.R.r
    rw [Nat.zero_min, D.sp.Y_rank 0 (Nat.zero_le _)]
    simp [Ranks.rankY, Ranks.r]
  have hs : ∀ P, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → Formalism.DivisionValues.conjPl P ≠ P → ∀ k ≤ (Yc D 0).rank,
      c P (dualLab (splitLab (Yc D 0).rank k)) = c' P (dualLab (splitLab (Yc D 0).rank k)) := by
    intro P hP hcP k hk
    obtain ⟨P0, h0, rfl, hq⟩ := GlobalTheory.T.goodSplitPlace_of_family_prime_base_tuple R F hW e P hP hcP
    have h1 := (hpol p c hc P0 h0).1
    have h2 := (hpol p c' hc' P0 h0).1
    rw [hr] at hk ⊢
    exact heckePolyOf_coeff_inj D.R.r _ hq _ _ (h1.symm.trans h2) k hk
  have hE0 : GlobalTheory.Hk3.EEc R.toRealDat R.SF c ≠ ⊥ := hE c ▸ hc.1
  have hE0' : GlobalTheory.Hk3.EEc R.toRealDat R.SF c' ≠ ⊥ := hE c' ▸ hc'.1
  have ksplit := GlobalTheory.T.heckeEigenvalues_eq_of_dual_enlarging_labels_split R.toRealDat F.lv2 hC R.SF hSF c c' hE0 hE0' hs
  let i0 : Fin D.R.m := ⟨0, by have := D.R.two_le_m; omega⟩
  have kin := (GlobalTheory.InertValLab.inert_vals_iff_labels R F hL hok hW e hS hTwo hInert hinj i0 p p c c' hc hc').1 (fun _ => rfl)
  have key : ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → GlobalTheory.Hk3.IsLab (Yc D 0) P d → c P (dualLab d) = c' P (dualLab d) := by
    intro P d hP hd
    by_cases hcP : Formalism.DivisionValues.conjPl P = P
    · apply kin P _ hP hcP
      rw [(GlobalTheory.LabEq.isLab_W_iff R.toRealDat F.lv2 (s := 0) hC i0 P _ hP).1, GlobalTheory.CarriedHecke.dualLab_dualLab]
      exact hd
    · exact ksplit P hP hcP d hd
  obtain ⟨h1, h2⟩ := parts_eq_of_rowLabels R.toRealDat F.lv2 hC R.SF hSF c c' key
  exact ⟨by rw [hE, hE, h1], fun i => by rw [hWc, hWc, h2 i]⟩

end GlobalTheory.CarriesOne

end
