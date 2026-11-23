import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta

theorem isSBHalf_levDatum : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → IsIdemSum e Z → IsSBHalf (cA D e) (latO S T ΛS ΛT fun _ => True) (levDatum S T βS βT LT Q m e) := by
  intro D S T ΛS ΛT βS βT LT Q m Z e hS hT hfS hfT he
  classical

  have hlin : ∀ (k : ℕ) (u : WO S T), frMapAdj S T βS βT (k • u) = k • frMapAdj S T βS βT u := by
    intro k u
    induction k with
    | zero =>
      have h0 := GlobalTheory.PlaceVec.frMapAdj_add S T βS βT 0 0
      simpa using h0
    | succ n ih =>
      rw [succ_nsmul, GlobalTheory.PlaceVec.frMapAdj_add, ih, succ_nsmul]
  have hadd : ∀ (x u : WO S T) (k : ℕ) i j,
      frMapAdj S T βS βT (x + k • u) i j = frMapAdj S T βS βT x i j + k * frMapAdj S T βS βT u i j := by
    intro x u k i j
    rw [GlobalTheory.PlaceVec.frMapAdj_add, hlin, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]

  have hB : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      (fun _ => True), ∀ i j, (M : EAf D) * frMapAdj S T βS βT u i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    obtain ⟨M, hM, hMl⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.1.fg hT.1.fg
    obtain ⟨k, hk, hup⟩ := GlobalTheory.PlaceVec.frMapAdj_up S T βS βT
    refine ⟨k * M, Nat.mul_pos hk hM, fun u hu i j => ?_⟩
    have hint : IsIntM ((M • u).map (toEAf D)) := by
      intro a b
      rw [Matrix.map_apply, Matrix.smul_apply, map_nsmul, nsmul_eq_mul]
      exact hMl u hu a b
    have h := hup (M • u) hint i j
    rw [hlin, Matrix.smul_apply, Matrix.smul_apply, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc] at h
    simpa [Nat.cast_mul] using h

  have hC : ∃ K : ℕ, 0 < K ∧ ∀ t, IsHalf (cA D e) t → IsIntM (frMapAdj S T βS βT t) →
      K • t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    obtain ⟨k, hk, hdown⟩ := GlobalTheory.PlaceVec.frMapAdj_down S T βS βT
    obtain ⟨K, hK, hKl⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS.1 hT.1
    refine ⟨K * k, Nat.mul_pos hK hk, fun t ht hti => ?_⟩
    have hinf : t.map (infPart D) = 0 :=
      GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum he)) ht
    have hinf' : (k • t).map (infPart D) = 0 := by
      ext a b
      have h1 := congrFun (congrFun hinf a) b
      rw [Matrix.map_apply, Matrix.zero_apply] at h1
      rw [Matrix.map_apply, Matrix.smul_apply, map_nsmul, h1, smul_zero, Matrix.zero_apply]
    have hint' : ∀ a b, toEAf D ((k • t) a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro a b
      have h2 := hdown t hti a b
      rwa [Matrix.smul_apply, Matrix.map_apply, ← map_nsmul] at h2
    rw [← smul_smul]
    exact hKl (k • t) hinf' hint'

  have hω : ∀ y y' : (∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP)),
      (∀ PP ∈ LT.Pg ∪ Q, y PP = y' PP) →
        omegaG LT m y * omegaQ Q T.rank m (-1) y = omegaG LT m y' * omegaQ Q T.rank m (-1) y' := by
    intro y y' h
    rw [GlobalTheory.PlaceDatum.omegaG_congr LT m y y' (fun PP hP => h PP (Finset.mem_union_left _ hP)),
      GlobalTheory.PlaceDatum.omegaQ_congr Q T.rank m (-1) y y' (fun PP hP => h PP (Finset.mem_union_right _ hP))]
  have key := GlobalTheory.PlaceDatum.isSBHalf_of_red (cA D e)
    (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (frMapAdj S T βS βT) hadd hB hC (LT.Pg ∪ Q) (fun y => omegaG LT m y * omegaQ Q T.rank m (-1) y) hω
  unfold levDatum
  exact key

end GlobalTheory.FinZeta

end
