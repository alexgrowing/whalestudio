import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.HinjX

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
  (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] [CharZero Kc]

theorem nuT_antitone (hS : XShape) (j : ℕ) (b : BX X) : Antitone (nuT X j b) := by
  obtain ⟨-, -, hanti, -⟩ := hS p X j b
  unfold nuT
  split_ifs
  · exact BidetPairing.kap_antitone (hanti _) _
  · exact hanti _

theorem shape_szT (hS : XShape) (j : ℕ) (b : BX X) : shapeDeg (szT X j b) = nuT X j b := by
  obtain ⟨-, -, hanti, hle, -⟩ := hS p X j b
  by_cases ho : IsOddPos b.2
  · have h1 : szT X j b = fun k => NJ X (j + 1) - colH (muX X j (NJ X (j + 1)) b) k.val := by
      funext k; exact if_pos ho
    rw [h1, show nuT X j b = _ from if_pos ho]
    exact shape_odd_holds _ _ (hanti _) _ (hle _)
  · have h1 : szT X j b = fun k => colH (muX X j (NJ X (j + 1)) b) k.val := by
      funext k; exact if_neg ho
    rw [h1, show nuT X j b = _ from if_neg ho]
    exact shape_even_holds _ _ (hanti _) _ (hle _)

theorem xPair (hS : XShape) (hBrS : XBrS) (hInj : XInj) (hMid : XMid) (hU : XUnit)
    (Oc : Subring Kc) (hval : ∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc)
    (hO : ∀ o : X.G.O, algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf o) ∈ Oc)
    (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Frm X j La La') (i0 : X.Pl → ℕ) (h3 : ∀ v, i0 v ≤ X.G.P.r)
    (f : MvPowerSeries (X.ZA j) Kc) (gg : ℝ)
    (hf : ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ), geX p Oc (coeff n (applyD (X.PI j I i0) f)) gg)
    (G : (X.Pj j).Xsp) (hG : G ∈ (X.Pj j).HtupW La.2)
    (I : ∀ (b : BX X) (k : Fin (cX X j b)), Fin (szT X j b k) → Fin (NJ X (j + 1))) :
    ∃ a ∈ MG p Oc hval gg,
      fockR ((((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) *
            ((∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j La.2)) *
              (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) La'.2))⁻¹)) *
            (∏ b : BX X, (mF X (j + 1) b (φ.g' b.1) * DgX X X.G.Kf j i0 b.1).det ^ (-(eJ X (j + 1) b.1 b.2)))⁻¹) •
          delF X Kc j G (linSub (bc Kc φ) f))
        (map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b)
          (rowAct X.G.Kf (mF X (j + 1) b (φ.g' b.1) * DgX X X.G.Kf j i0 b.1).transpose
            (bideterminant X.G.Kf (szT X j b) (szT_le X j b) (I b))))) = a * ∏ b, cN Kc (nuT X j b) := by
  classical
  by_cases hI : ∀ b k, Function.Injective (I b k)
  · obtain ⟨Ist, ε, hε, hmid⟩ := hMid p X Kc j La La' φ i0 I hI
    set TI := map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b)
      (rowAct X.G.Kf (mF X (j + 1) b (φ.g' b.1) * DgX X X.G.Kf j i0 b.1).transpose
        (bideterminant X.G.Kf (szT X j b) (szT_le X j b) (I b)))) with hTI
    set cc : Kc := ∏ b, cN Kc (nuT X j b) with hcc
    have hcc0 : cc ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => cN_ne Kc _
    set S1 : X.G.Kf := ((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) *
            ((∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j La.2)) *
              (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) La'.2))⁻¹)) with hS1
    set s1 : X.G.Kf := (∏ b : BX X, (mF X (j + 1) b (φ.g' b.1) * DgX X X.G.Kf j i0 b.1).det ^ (-(eJ X (j + 1) b.1 b.2)))⁻¹ with hs1
    have hp0 : (p : Kc) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    have hu := hU p X Kc Oc hO hp0 j La.2 La'.2 φ.g φ.g' φ.hg φ.hg' i0 h3
    rw [← hS1, ← hs1] at hu
    set U0 := numericalIdentityScalar X Kc j (fun v => φ.g v) (fun v => φ.g' v) i0 with hU0
    have hεO : ε ∈ Oc := by
      rcases hε with h | h
      · rw [h]; exact Oc.one_mem
      · rw [h]; exact Oc.neg_mem Oc.one_mem
    have key := phi_mem X Kc hS hBrS hInj j La.2 φ.g φ.hg (MG p Oc hval gg) (fun o a ha => geX_mul (hO o) ha)
      (PhiX X Kc j (fockL TI) (cc⁻¹ * algebraMap X.G.Kf Kc (S1 * s1)) (linSub (bc Kc φ) f))
      (C (ε * (algebraMap X.G.Kf Kc (S1 * sX X j (fun v => φ.g v) * s1) * U0)) * applyD (X.PI j Ist i0) f)
      (fun m => by
        rw [coeff_C_mul]
        exact geX_mul (Oc.mul_mem hεO hu) (hf Ist m))
      (fun x => by
        rw [PhiX_apply, map_smul, LinearMap.smul_apply, ← algebraMap_smul Kc (sX X j fun v => φ.g v), map_smul, smul_eq_mul]
        show _ * (_ * fockR _ TI) = _
        rw [hmid f x]
        simp only [map_mul, eval_C]
        field_simp) G hG
    refine ⟨_, key, ?_⟩
    rw [PhiX_apply, ← algebraMap_smul Kc (S1 * s1), fockR_smul_left]
    show _ = _ * _ * fockR _ TI * cc
    field_simp
  · push Not at hI
    obtain ⟨b0, k0, hk⟩ := hI
    refine ⟨0, AddSubgroup.zero_mem _, ?_⟩
    have hb : bideterminant X.G.Kf (szT X j b0) (szT_le X j b0) (I b0) = 0 := by
      unfold bideterminant
      exact Finset.prod_eq_zero (Finset.mem_univ k0) (minor_zero_holds _ _ _ _ _ _ hk)
    have hz : (∏ b, rename (emX X (j + 1) b)
        (rowAct X.G.Kf (mF X (j + 1) b (φ.g' b.1) * DgX X X.G.Kf j i0 b.1).transpose
          (bideterminant X.G.Kf (szT X j b) (szT_le X j b) (I b)))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ b0) (by rw [hb, map_zero, map_zero])
    rw [hz, map_zero, fockR_comm, fockR_zero_left, zero_mul]

end Formalism.L2.PairingIndexBounds.Ent
