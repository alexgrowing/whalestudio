import Formalism.LocalToGlobal.GlobalTheory.BlockActions.IsUnitBZMap

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix NumberField
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in

theorem normClsAt_of_tors (hT : ChiTors) : NormClsAt := by
  intro D u Ch chOf Tf hL hBe h s x Pc hPc Qc hQc o ho o' ho' c
  classical
  have hbase := base_eq Tf hL h x Pc hPc Qc hQc c
  obtain ⟨k, hk, hχ⟩ := hT D u Ch chOf Tf c
  obtain ⟨a, ha, has⟩ := desc_scalar D.what₂.embLL (Qc c) (brTenL D u (PL Tf c (Pc ((D.fm u).til c)))) _ k hk hχ hbase
  have hAsu : ∀ τ, IsUnit ((AL Tf c τ).map s).det := fun τ => isUnit_AL_map Tf c s τ
  have hR : MvPolynomial.map s (Pc ((D.fm u).til c)) ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m) :=
    map_mem_CSpan_of_rat _ _ (pc_rat Tf x Pc hPc _) s
  have hY := blkRow_mem_CSpan _ (fun τ => (AL Tf c τ).map s) hAsu _ hR
  have hQs : MvPolynomial.map s (Qc c) = (s a * ∏ τ, ((AL Tf c τ).map s).det ^ shiftOf (lamT u D.R.m) τ) •
      Formalism.L2.Ker.brTen D u (blkRow (fun τ => (AL Tf c τ).map s) (MvPolynomial.map s (Pc ((D.fm u).til c)))) := by
    rw [ha, MvPolynomial.smul_eq_C_mul, map_mul, map_C, map_brTenL, map_PL, map_smul, ← MvPolynomial.smul_eq_C_mul,
      smul_smul]
  have hoN : ∀ τ, (o.1 τ)ᴴ * gramC (gramN D D.R.m le_rfl) (embS D s) τ * o.1 τ = 1 := fun τ =>
    Formalism.L2.Col.frame_pos o ho τ (gramN_posDef_at Tf (embS D s τ)).posSemidef
  have hoP : ∀ τ, (o'.1 τ)ᴴ * gramC (gramP D) (embS D s) τ * o'.1 τ = 1 := fun τ =>
    Formalism.L2.Col.frame_pos o' ho' τ (gramP_posDef_at Tf (embS D s τ)).posSemidef
  have hon : ∀ τ, ((AL Tf c τ).map s * dOT u (o'.1 τ))ᴴ * gramC (gramN D D.R.m le_rfl) (embS D s) τ *
      ((AL Tf c τ).map s * dOT u (o'.1 τ)) = 1 := by
    intro τ
    rw [AL_map, Matrix.map_mul]
    exact frame_on_at Tf c (embS D s τ) (o'.1 τ) (hoP τ)
  have hind := term_frame_indep ((D.fm u).lam D.R.m) (gramC (gramN D D.R.m le_rfl) (embS D s)) (shiftOf (lamT u D.R.m)) o.1
    (fun τ => (AL Tf c τ).map s * dOT u (o'.1 τ)) hoN hon (MvPolynomial.map s (Pc ((D.fm u).til c)))
  have hchain := chain_at Tf hBe o'.1 o'.2 _ hY
  have hcomp : blkRow (fun τ => dOT u (o'.1 τ)) (blkRow (fun τ => (AL Tf c τ).map s) (MvPolynomial.map s (Pc ((D.fm u).til c)))) =
      subP (fun τ => (AL Tf c τ).map s * dOT u (o'.1 τ)) (MvPolynomial.map s (Pc ((D.fm u).til c))) := blkRow_comp _ _ _
  rw [hcomp] at hchain
  rw [hQs, map_smul, nfAll_smul_reB, normal_form_agree, hind]
  have hdet : ∏ τ, ‖((AL Tf c τ).map s * dOT u (o'.1 τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ) =
      (∏ τ, ‖((AL Tf c τ).map s).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)) *
        ∏ τ, ‖(dOT u (o'.1 τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_mul, norm_mul, mul_zpow]
  have hκ : ‖s a * ∏ τ, ((AL Tf c τ).map s).det ^ shiftOf (lamT u D.R.m) τ‖ ^ 2 =
      ‖s a‖ ^ 2 * ∏ τ, ‖((AL Tf c τ).map s).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ) := by
    rw [norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [norm_zpow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm (shiftOf (lamT u D.R.m) τ)]
    norm_num
  rw [hdet, hκ]
  have hsa : ‖s a‖ ^ 2 ≤ 1 := by
    have h1 := has s
    have h0 := norm_nonneg (s a)
    nlinarith
  set nW := (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o'.1 (Formalism.L2.Ker.brTen D u (blkRow (fun τ => (AL Tf c τ).map s)
    (MvPolynomial.map s (Pc ((D.fm u).til c)))))) (subP o'.1 (Formalism.L2.Ker.brTen D u (blkRow (fun τ => (AL Tf c τ).map s)
    (MvPolynomial.map s (Pc ((D.fm u).til c))))))).re with hnW
  set K2 := ∏ τ, ‖(o'.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)
  set KA := ∏ τ, ‖((AL Tf c τ).map s).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)
  have hKA : 0 ≤ KA := Finset.prod_nonneg fun τ _ => zpow_nonneg (norm_nonneg _) _
  have hK2 : 0 ≤ K2 := Finset.prod_nonneg fun τ _ => zpow_nonneg (norm_nonneg _) _
  have hnW : 0 ≤ nW := Formalism.L2.Ker.ta_nfAll_nonneg _ _
  calc K2 * (‖s a‖ ^ 2 * KA * nW) = ‖s a‖ ^ 2 * (KA * (K2 * nW)) := by ring
    _ ≤ 1 * (KA * (ptB D u * ((∏ τ, ‖(dOT u (o'.1 τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)) *
          (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) (subP (fun τ => (AL Tf c τ).map s * dOT u (o'.1 τ)) (MvPolynomial.map s (Pc ((D.fm u).til c))))
            (subP (fun τ => (AL Tf c τ).map s * dOT u (o'.1 τ)) (MvPolynomial.map s (Pc ((D.fm u).til c))))).re))) :=
        mul_le_mul hsa (mul_le_mul_of_nonneg_left hchain hKA) (mul_nonneg hKA (mul_nonneg hK2 hnW)) zero_le_one
    _ = _ := by ring

theorem norm_bound_of_torsion_character (h1 : ClassMapInjective) (h2 : StabiliserMapBijective) (hT : ChiTors) : NormBoundAtInfinity :=
  norm_bound_of_classes h1 h2 (normClsAt_of_tors hT)

end Formalism.L2.GlobalTheoryTheory.Br
