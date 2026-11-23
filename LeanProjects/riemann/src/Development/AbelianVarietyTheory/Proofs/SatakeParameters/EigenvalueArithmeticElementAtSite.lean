import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ToMatrixCoMulSymm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KapGEqCharInf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LenSmulTup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitDetFrameMatrixOfCharts
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.TwV.Xc.kapG_at_site : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → FillAt (hT := hT) (H := H) (X := X) std j hj → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) ∈ TaylorLogMetric.Qbar ∧ kapG (sysS H X std) ℂ_[D.what₂.places.resChar w] j c γ = TaylorLogMetric.lamC S.lam (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)))) * ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * (len (sysS H X std) v j (((sysS H X std).Lv.lev j c).smul γ La) - len (sysS H X std) v j La))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hSpl hPos j hj c La γ g κ hr hLat hMove hFill
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  obtain ⟨hgU, -, hfr, r, hr1, hr2⟩ := hMove

  obtain ⟨-, hE⟩ := eMat_unitary_det D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) (fun x => rfl) _ _ hr
    (gramN D j hj.le) (J.A.crd j hj.le) (J.pins.crd_orth j hj.le)
  obtain ⟨hEu, hEdet⟩ := hE g hgU
  have ha : g.1.det * D.host.conj g.1.det = 1 := by
    have h1 := congrArg Matrix.det hEu
    rw [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one, hEdet] at h1
    rw [← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj D]
    exact h1

  have hdet : ∀ v, (gamAt (sysS H X std) j c γ v : Matrix (Fin (((sysS H X std).Pj j).m + 1)) (Fin (((sysS H X std).Pj j).m + 1)) ((sysS H X std).G.P.Qq v)).det = J.rho std v g.1.det := by
    intro v
    have h1 := congrArg Matrix.det (hfr hr v)
    have hm : ((eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g).map (J.rho std v)).det = J.rho std v g.1.det := by
      rw [← hEdet]; exact (RingHom.map_det (J.rho std v) _).symm
    rw [Matrix.det_mul, Matrix.det_mul, hm] at h1
    have hu : IsUnit ((J.fd std).frM j (c, La) v).det := isUnit_det_frameMatrix_ofCharts _ _ _ j (c, La) v
    rw [mul_comm (J.rho std v _)] at h1
    exact hu.mul_left_cancel h1
  have ha0 : g.1.det ≠ 0 := fun h0 => by rw [h0, zero_mul] at ha; exact zero_ne_one ha
  have hT0 : ∀ τ, TaylorLogMetric.embT D τ g.1.det ≠ 0 := fun τ => (map_ne_zero _).2 ha0
  have hkap := kapG_eq_char_inf D (D.what₂.places.resChar w) (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) S.lam (J.rho std) hPos j c γ
    g.1.det ha hdet

  obtain ⟨e, he, hmu⟩ := S.law.mu_rat j hj
  have hdetR : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g) = ratId D.host.F D.host.E (Matrix.GeneralLinearGroup.det g) := by
    ext
    simp [GlobalTheory.TwU.ratA, ratId, Formalism.UG.bc, RingHom.map_det]
  have hmuT : S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) = ∏ τ, TaylorLogMetric.embT D τ g.1.det ^ e τ := by
    rw [hdetR, hmu _ (by simpa using ha)]
    simp
  have hq1 : (∏ τ, TaylorLogMetric.embT D τ g.1.det ^ e τ) ∈ TaylorLogMetric.Qbar :=
    prod_mem fun τ _ => zpow_mem (embT_mem_qbar D τ _) _
  have hz : D.what₂.embLL r ∈ algebraicClosure ℚ ℂ := by
    rw [mem_algebraicClosure_iff']
    exact (Algebra.IsIntegral.isIntegral r).map D.what₂.embLL.toRatAlgHom
  have hχ : S.E.toCEmb.iK (algebraMap (sysS H X std).G.O (sysS H X std).G.Kf ((((sysS H X std).Lv.lev j c).χ γ : (sysS H X std).G.Oˣ) : (sysS H X std).G.O)) =
      TaylorLogMetric.lamC S.lam (D.what₂.embLL r) := by
    rw [hr2, S.hK r hz]
    exact (lamC_qbar S.lam ⟨_, hz⟩).symm

  set A : ℤ := (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)) with hA
  set B : ℤ := (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ) with hB
  have hfill := hFill e he
  have hq2 : (∏ τ, TaylorLogMetric.embT D τ g.1.det) ^ (-A - B) ∈ TaylorLogMetric.Qbar :=
    zpow_mem (prod_mem fun τ _ => embT_mem_qbar D τ _) _
  have hkey : (∏ v : (sysS H X std).Pl, ∏ s : Fin ((sysS H X std).G.P.n' v), TaylorLogMetric.embT D (hT.gat_pos u w hg ⟨v, s⟩) g.1.det ^ (sysS H X std).w v (j + 1) s) =
      (∏ τ, TaylorLogMetric.embT D τ g.1.det ^ e τ) * (∏ τ, TaylorLogMetric.embT D τ g.1.det) ^ (-A - B) := by
    simp_rw [hfill]
    rw [← Fintype.prod_sigma (fun x => TaylorLogMetric.embT D (hT.gat_pos u w hg x) g.1.det ^ (e (hT.gat_pos u w hg x) - A - B))]
    rw [Fintype.prod_equiv (hT.gat_pos u w hg) _ (fun τ => TaylorLogMetric.embT D τ g.1.det ^ (e τ - A - B)) (fun _ => rfl)]
    rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← zpow_add₀ (hT0 τ)]
    ring_nf
  have hlen : ∀ v, (sysS H X std).vm v (j + 1) * (len (sysS H X std) v j (((sysS H X std).Lv.lev j c).smul γ La) - len (sysS H X std) v j La) =
      -((sysS H X std).vm v (j + 1) * ordP ((sysS H X std).G.P.W v) (D.what₂.places.resChar w) (J.rho std v g.1.det)) := by
    intro v
    rw [len_smul_tup _ (sysS H X std) j c γ La hLat v, hdet v]
    ring
  refine ⟨hmuT ▸ hq1, ?_⟩
  rw [hkap, hχ, hkey, hmuT, ← hr1, Finset.sum_congr rfl fun v _ => hlen v, Finset.sum_neg_distrib,
    show -A - B = -(A + B) by ring, mul_assoc (D.what₂.embLL r), Formalism.L2.Ker.lamC_mul S.lam hz (mul_mem hq1 (by rw [show -(A + B) = -A - B by ring]; exact hq2))]

end
