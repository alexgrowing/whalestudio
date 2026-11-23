import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.PairingAdjointness
import Formalism.LocalToGlobal.GlobalTheory.GL6.SecondBranchInclLengthOfLengths

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

variable (D : D7)

def owEquiv (w : D.what₂.places.Pl) : Ow D w ≃+* bwA_Ow D w :=
  Subring.equivMapOfInjective (intW D.what₂.places w) D.what₂.embLL D.what₂.embLL.injective

instance owPair (w : D.what₂.places.Pl) :
    RingHomInvPair ((owEquiv D w : Ow D w ≃+* bwA_Ow D w) : Ow D w →+* bwA_Ow D w)
      ((owEquiv D w).symm : bwA_Ow D w →+* Ow D w) :=
  RingHomInvPair.of_ringEquiv (owEquiv D w)

instance owPair' (w : D.what₂.places.Pl) :
    RingHomInvPair ((owEquiv D w).symm : bwA_Ow D w →+* Ow D w)
      ((owEquiv D w : Ow D w ≃+* bwA_Ow D w) : Ow D w →+* bwA_Ow D w) where
  comp_eq := by ext x; simp
  comp_eq₂ := by ext x; simp

variable (u : D.what₂.Word)

theorem lenLen2_of_coord (A : AtTTied u) (Lv : LvTied u A 0 (Nat.zero_le _)) (w : D.what₂.places.Pl) (hw : OverT D u w)
    (v : (D.mem u).A.vT)
    (hLc0 : ∀ c, clsCrd D u 0 (Nat.zero_le _) c ≤ Ld D u 0 (Nat.zero_le _) c)
    (B B' : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E)
    (hB : ∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c))
    (hB' : ∀ c, IsLocBasis (D.mem u).A.T (Lk A 0 (Nat.zero_le _) v c : Set _) (B' c))
    (hunit : ∀ c, (((((B c)⁻¹ * B' c : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det * (((D.mem u).A.T : ℂ))⁻¹ ∈ bwA_Ow D w ∧
      ((D.mem u).A.T : ℂ) * ((((((B c)⁻¹ * B' c : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det)⁻¹ ∈ bwA_Ow D w)
    (Φ : Vl D u 0 →ₛₗ[((owEquiv D w : Ow D w ≃+* bwA_Ow D w) : Ow D w →+* bwA_Ow D w)]
      ((D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ))
    (hΦ : Function.Injective Φ)
    (hA : ((D.fm u).Bw 0 w v).map Φ = Submodule.pi Set.univ fun c =>
      ((intSubm D w ((D.fm u).lam 0)).map
            ((Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c))).toLinearMap.restrictScalars (bwA_Ow D w))).map
          (scO (bwA_Ow D w) _ ((bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) ((D.fm u).tauOf w v)).det ^
            ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift)))
    (hS : (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)).map Φ = Submodule.pi Set.univ fun _ =>
      (intSubm D w ((D.fm u).lam 0)).map
            (scO (bwA_Ow D w) _ (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v))))
    (hd : D.duS u = Fintype.card ((D.mem u).C.cls 0) *
      ∏ τ, Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ))) :
    ∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)) = n ∧
      (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
        ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
          (D.R.k : ℚ)) := by
  classical
  have hkpos : (0 : ℚ) < (D.R.k : ℚ) := by
    have h := D.R.m_add_three_le_k
    exact_mod_cast (show 0 < D.R.k by omega)
  choose n hn hnq using fun c => cls_len_D D u A w hw v Lv c (hLc0 c) (B c) (B' c) (hB c) (hB' c) (hunit c)
  refine ⟨∑ c, n c, ?_, ?_⟩
  · unfold Formalism.MainNotions.product_first_zeroth_parts.len
    rw [len_quot_semilinear (σ' := ((owEquiv D w).symm : bwA_Ow D w →+* Ow D w)) Φ hΦ, hA, hS, len_pi_sum,
      Nat.cast_sum]
    exact Finset.sum_congr rfl fun c _ => hn c
  · have e : ∀ c, (n c : ℚ) = (D.what₂.places.ramIdx w : ℚ) *
        ((∏ τ, Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ)) : ℕ) : ℚ) *
        ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
          (D.R.k : ℚ) := fun c => by
      rw [eq_div_iff hkpos.ne', mul_comm]; exact hnq c
    rw [Nat.cast_sum, Finset.sum_congr rfl fun c _ => e c, Finset.sum_const, Finset.card_univ, hd, nsmul_eq_mul]
    push_cast
    ring

end Formalism.L2.GlobalTheoryTheory.LemB
