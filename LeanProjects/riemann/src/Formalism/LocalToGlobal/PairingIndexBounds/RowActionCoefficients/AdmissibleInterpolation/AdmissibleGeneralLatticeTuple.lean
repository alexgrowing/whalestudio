import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.NuTAntitone

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
  (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] [CharZero Kc]

theorem admissible_general_lattice_tuple (hS : XShape) (hBrS : XBrS) (hBrT : XBrT) (hInj : XInj) (hSp : XSpanN) (hMid : XMid) (hU : XUnit) (hE : XEdge)
    (Oc : Subring Kc) (hval : ∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc)
    (hO : ∀ o : X.G.O, algebraMap X.G.Kf Kc (algebraMap X.G.O X.G.Kf o) ∈ Oc)
    (j : ℕ) (La : X.Lt j) (c' : X.Lv.comp (j + 1)) (L' L'' : (X.Pj (j + 1)).Tup) (i0 : X.Pl → ℕ)
    (h1 : (X.Pj j).IsLatTup La.2) (h2 : (X.Pj (j + 1)).IsLatTup L') (h3 : ∀ v, i0 v ≤ X.G.P.r)
    (h4 : ∀ v' : Fin (X.Pj (j + 1)).nV, (i0 (X.vB (j + 1) v') = 0 ∧ L'' v' = L' v') ∨
      (1 ≤ i0 (X.vB (j + 1) v') ∧ IsEdge p ((X.Pj (j + 1)).n' v') (i0 (X.vB (j + 1) v')) ⟨L'' v', L' v'⟩)) :
    ∃ φ : Frm X j La (c', L''), ∀ (f : MvPowerSeries (X.ZA j) Kc) (gg : ℝ),
      (∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ), geX p Oc (coeff n (applyD (X.PI j I i0) f)) gg) →
      ∀ G ∈ (X.Pj j).HtupW La.2,
        ((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) •
          (((∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j La.2)) *
            (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) L''))⁻¹) •
              delF X Kc j G (linSub (bc Kc φ) f))) ∈
        AddSubgroup.closure {y' | ∃ a : Kc, geX p Oc a gg ∧ ∃ z ∈ (X.Pj (j + 1)).HtupW L',
          y' = a • map (algebraMap X.G.Kf Kc) z} := by
  classical
  have cz : CharZero X.G.Kf := (algebraMap X.G.Kf Kc).charZero
  obtain ⟨g', h', hg', hh', hmF⟩ := hE p X j L' L'' i0 h2 h4
  obtain ⟨φ0⟩ := exists_frm X j La (c', L') h1 h2
  let φ : Frm X j La (c', L'') := ⟨φ0.g, g', φ0.hg, hg'⟩
  refine ⟨φ, fun f gg hf G hG => ?_⟩
  set ft := linSub (bc Kc φ) f with hft
  set S1 : X.G.Kf := ((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) *
    ((∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v j La.2)) *
      (∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * len X v (j + 1) L''))⁻¹)) with hS1
  set s' : X.G.Kf := sX X (j + 1) (fun v => h' v) with hs'
  have hs'0 : s' ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => zpow_ne_zero _ (mF_det_ne X (j + 1) b (h' b.1))
  have hs'e : s' = ∏ b : BX X, (mF X (j + 1) b (g' b.1) * DgX X X.G.Kf j i0 b.1).det ^ (-(eJ X (j + 1) b.1 b.2)) :=
    Finset.prod_congr rfl fun b _ => by rw [hmF b]
  have hy1 := tgt_bidet (O := X.G.O) (Kc := Kc) (emX X (j + 1)) (hInj p X (j + 1)).1 (nuT X j) (nuT_antitone X hS j)
    (fun b => mF X (j + 1) b (h' b.1)) (fun b => mF X (j + 1) b ((h' b.1)⁻¹ : GL _ _)) (fun b => mF_inv_mul X (j + 1) b (h' b.1))
    (MG p Oc hval gg) (fun o a ha => geX_mul (hO o) ha) dual_bases_holds fock_product_holds reorder_holds (cX X j) (szT X j)
    (szT_le X j) (shape_szT X hS j) ((S1 * s'⁻¹) • delF X Kc j G ft)
    (by
      rw [← algebraMap_smul Kc (S1 * s'⁻¹)]
      exact Submodule.smul_mem _ _ (xSpan X Kc hS hBrS hInj hSp j La.2 φ0.g φ0.hg ft G hG))
    (fun I => by
      have := xPair X Kc hS hBrS hInj hMid hU Oc hval hO j La (c', L'') φ i0 h3 f gg hf G hG I
      rw [← hS1, ← hs'e] at this
      simp only [hmF]
      exact this)
  have htr : ∀ z ∈ AddSubgroup.closure {z | ∃ a ∈ MG p Oc hval gg,
      ∃ F : BX X → MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) X.G.Kf,
        (∀ b, F b ∈ deltaL X.G.O X.G.Kf (NJ X (j + 1)) (nuT X j b) (mF X (j + 1) b (h' b.1))) ∧
          z = a • map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b) (F b))},
      s' • z ∈ AddSubgroup.closure {y' | ∃ a : Kc, geX p Oc a gg ∧ ∃ z ∈ (X.Pj (j + 1)).HtupW L',
        y' = a • map (algebraMap X.G.Kf Kc) z} := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, F, hF, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨a, ha, s' • ∏ b, rename (emX X (j + 1) b) (F b), ?_, ?_⟩
      · refine hBrT p X (hinjX X) (j + 1) L' (fun v => h' v) (fun v => (Matrix.isUnit_iff_isUnit_det _).1 (h' v).isUnit) hh' F ?_
        intro b
        rw [(hS p X j b).2.1]
        exact hF b
      · rw [smul_comm, smul_eq_C_mul (a := s'), map_mul, map_C, ← smul_eq_C_mul, algebraMap_smul]
    | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
    | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx
  have := htr _ hy1
  rw [smul_smul, mul_comm s', mul_assoc, inv_mul_cancel₀ hs'0, mul_one, hS1, mul_smul] at this
  exact this

end Formalism.L2.PairingIndexBounds.Ent
