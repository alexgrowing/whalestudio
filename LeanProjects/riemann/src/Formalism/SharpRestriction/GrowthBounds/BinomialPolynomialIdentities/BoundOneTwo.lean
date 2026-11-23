import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LiePolarizationDerEqZeroOfDisjoint
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ComponentsInFiltrationContractionSingle
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.IntegralJointTypeSumOfParts

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints Formalism.MainNotions.LemmaBAlt

theorem word_support_dominated (F : Type) [Field F] {N n : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ}
    (i : Fin (N + 1)) (P : PPath n N LL B) (I : ℤ → Finset (Fin n)) (hidx : Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsIndex (pEnd P.mu) I)
    (k1 : Type) [CommRing k1] (φ : F →+* k1) (g0 g0inv : Matrix (Fin n) (Fin n) k1) (hg : g0 * g0inv = 1)
    (m : Fin N × Fin n →₀ ℕ)
    (hm : m ∈ (matrixSubst LL {j : Fin N | j.val < i.val} φ g0inv g0 (Psi F P.mu I)).support) :
    DomLE (wtS LL {j : Fin N | j.val < i.val} m) (P.mu i) := by
  classical
  have hidx' : Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsIndex (ext P.mu N) I := by rw [ext_last]; exact hidx
  have hpath := restPathTo n N LL B P
  have h1 := restWord k1 n N i.val (isV LL) (Bn B) (ext P.mu) I g0inv g0 (mul_eq_one_comm.1 hg) hpath hidx'
    (Nat.lt_succ_iff.1 i.2) (m.mapDomain (iv N n)) ?_
  · rw [monomialWeight_eq_letterWeight, ext_val] at h1
    exact (dominanceOrder_iff _ _).2 h1
  · rw [← Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.map_psi φ hpath hidx', ← restPsi F n N LL B P I hidx,
      ← restAct F k1 N n i.val LL φ g0inv g0, MvPolynomial.mem_support_iff,
      MvPolynomial.coeff_rename_mapDomain _ (iv_inj N n)]
    exact MvPolynomial.mem_support_iff.1 hm

theorem adm_twelve (D : Formalism.BasicNotions.D7) : NestedTypeBound D := by
  classical
  intro F _ _ N n LL B P I i
  set I' : ℤ → Finset (Fin n) := fun c => if c ∈ colRange P.mu then I c else ∅ with hI'
  have hPsi : Psi F P.mu I = Psi F P.mu I' := by
    unfold Psi
    exact Finset.prod_congr rfl fun c hc => by simp only [hI', if_pos hc]
  rw [hPsi]
  by_cases hidx : Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsIndex (pEnd P.mu) I'
  · refine (restTypes D F N LL n _ _ (prin_lower (P.mu i)) _).2 ?_
    intro mu hmu hdom
    exact ⟨hdom, restFwd F (Fin N) LL n _ (fun mu => DomLE mu (P.mu i)) _
      (fun k1 _ φ g0 g0inv hg m hm => word_support_dominated F i P I' hidx k1 φ g0 g0inv hg m hm) mu hmu⟩
  · have h0 : Psi F P.mu I' = 0 := by
      unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsIndex at hidx
      push Not at hidx
      obtain ⟨c, hc⟩ := hidx
      by_cases hcr : c ∈ colRange P.mu
      · unfold Psi
        apply Finset.prod_eq_zero hcr
        exact column_kernel_support_degree F P c N (Nat.lt_succ_self N) (I' c) hc
      · exfalso
        apply hc
        have h1 := colH_off P.mu hcr (Fin.last N)
        have h2 : Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (pEnd P.mu) c = colH (P.mu (Fin.last N)) c := rfl
        simp only [hI', if_neg hcr, Finset.card_empty]
        rw [h2, h1]
        split_ifs <;> omega
    rw [h0]
    exact Submodule.zero_mem _

end Formalism.MainNotions.G.ColumnFamilies
