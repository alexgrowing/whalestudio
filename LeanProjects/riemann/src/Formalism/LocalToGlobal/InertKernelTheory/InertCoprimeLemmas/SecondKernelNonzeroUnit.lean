import Formalism.LocalToGlobal.InertKernelTheory.K2OfAgreements
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.K2

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem p_ne_zero_Kf (Y : Pend X) : (p : X.G.Kf) ≠ 0 := by
  intro h
  have h1 : algebraMap (K0 p) Y.Kc (p : K0 p) = 0 := by
    rw [map_natCast, ← map_natCast (algebraMap X.G.Kf Y.Kc), h, map_zero]
  rw [map_eq_zero_iff _ (algebraMap (K0 p) Y.Kc).injective] at h1
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h1

theorem eS_ne_zero (Y : Pend X) (j : ℕ) (La : X.Lt j) : Y.eS j La ≠ 0 := by
  unfold Pend.eS
  exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (p_ne_zero_Kf Y)

theorem eT_ne_zero (Y : Pend X) (j : ℕ) (La' : X.Lt (j + 1)) : Y.eT j La' ≠ 0 := by
  unfold Pend.eT
  exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (p_ne_zero_Kf Y)

theorem kernel_of_smul : KerOfSmul := by
  intro p _ X Y j La La' f h G
  have hne : Y.eS j La * (Y.eT j La')⁻¹ ≠ 0 :=
    mul_ne_zero (eS_ne_zero Y j La) (inv_ne_zero (eT_ne_zero Y j La'))
  unfold Pend.ker Pend.kerF
  rw [h, map_smul, smul_smul, mul_inv_cancel₀ hne, one_smul]

theorem ker_zero (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : Y.ker j La La' 0 = 0 := by
  simp only [Pend.ker, Pend.kerF, map_zero, LinearMap.zero_apply, smul_zero]

theorem ker_add (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (G1 G2 : (X.Pj j).Xsp) :
    Y.ker j La La' (G1 + G2) = Y.ker j La La' G1 + Y.ker j La La' G2 := by
  simp only [Pend.ker, Pend.kerF, map_add, LinearMap.add_apply, smul_add]

theorem ker_smul (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (a : X.G.Kf) (G : (X.Pj j).Xsp) :
    Y.ker j La La' (a • G) = a • Y.ker j La La' G := by
  simp only [Pend.ker, Pend.kerF, map_smul, LinearMap.smul_apply]
  rw [smul_smul, smul_smul, mul_comm]

theorem map_smul_Kf (Y : Pend X) {σ : Type} (a : X.G.Kf) (P : MvPolynomial σ X.G.Kf) :
    MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (a • P) = a • MvPolynomial.map (algebraMap X.G.Kf Y.Kc) P := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, algebraMap_smul]

theorem tieChain_of_K {Y : Pend X} (R : RecSide X Y) (hC : TieChainK R) (hR : TieRat R) : TieChain R :=
  fun j hj x => hC j hj x (R.KL j x) (hR j hj x)

theorem body_of_span (Y : Pend X) (j : ℕ) (cK : Y.Kc) (S : Set (X.Fm j))
    (hS : ∀ F ∈ S, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ La ∈ Y.Rep j, (((X.stab j La : Y.Kc))⁻¹ * cK) • Y.ker j La (c', L') (F La.1 La.2))
    (F : X.Fm j) (hF : F ∈ Submodule.span X.G.Kf S) :
    ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ La ∈ Y.Rep j, (((X.stab j La : Y.Kc))⁻¹ * cK) • Y.ker j La (c', L') (F La.1 La.2) := by
  induction hF using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    intro c' L' _
    simp only [map_zero, Pi.zero_apply, ker_zero, smul_zero, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
    intro c' L' hL
    simp only [map_add, Pi.add_apply, ker_add, smul_add, Finset.sum_add_distrib, hx c' L' hL, hy c' L' hL]
  | smul a x _ hx =>
    intro c' L' hL
    simp only [map_smul, Pi.smul_apply, ker_smul]
    rw [map_smul_Kf Y, hx c' L' hL, Finset.smul_sum]
    refine Finset.sum_congr rfl fun La _ => ?_
    rw [smul_comm]

theorem second_kernel_nonzero_unit : K2OfAgreements := by
  intro D p _ X Y R hC hR hS hRd hCl hSer hDel hSp
  have body : K2NonzeroUnit X Y := by
    intro j hj
    obtain ⟨cK, h1, h2, h3, hD⟩ := hDel j hj
    refine ⟨cK, h1, h2, h3, ?_⟩
    intro F hF
    refine body_of_span Y j cK (R.cmp j '' R.Sh j) ?_ F (hSp j hj hF)
    rintro _ ⟨x, hx, rfl⟩ c' L' hL
    rw [hC j hj x, hRd j hj _ c' L' hL, hR j hj x, hS j hj x hx, map_sum]
    rw [← Equiv.sum_comp (R.e j), ← Finset.sum_coe_sort (Y.Rep j)]
    refine Finset.sum_congr rfl fun La _ => ?_
    rw [map_smulₛₗ, map_inv₀, map_natCast, hCl j hj La, hD La x hx c' L' hL,
      kernel_of_smul p X Y j La.1 (c', L') _ (hSer j hj La.1 La.2 c' L' hL), mul_smul]
  refine ⟨body, fun j hj => ?_⟩
  obtain ⟨cK, h1, h2, _, h⟩ := body j hj
  exact ⟨cK, h1, h2, h⟩

theorem admissible_third_of_forms : Adm3bOf := by
  intro D p _ X Y R hC hSp hUp j hj F hF
  have hspan := hSp j hj hF
  clear hF
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    rw [hC j hj y]
    exact hUp j hj _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

section Rec

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}

theorem sharpQ_qOf {t : KerEntTied ex} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {i : ℕ}
    {x : ((Tw.fm u μ).lat i).V} (h : ∃ Q, SharpQ t Tw u μ i x Q) : SharpQ t Tw u μ i x (qOf t Tw u μ i x) := by
  unfold qOf
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem recSum_recOf {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) (t : KerEntTied ex) (Tw : TwForms D)
    (u : D.what₂.Word) (μ : D.what₂.Tup) (ι : ℂ →+* Y.Kc) (σ : D.what₂.LL →+* X.G.Kf)
    (cmp : ∀ j, ((Tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (e : ∀ j, ↥(Y.Rep j) ≃ (D.chTw u μ).cls j)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (hm : X.mm ≤ D.R.m) :
    RecSum (recOf X Y t Tw u μ ι σ cmp Rd e Sr) := by
  intro j hj x hx
  have hQ := sharpQ_qOf hx
  funext c' y'
  show (D.chTw u μ).K j ((Tw.fm u μ).emb j x) c' y' =
    (∑ c : (D.chTw u μ).cls j, (((Nat.card ((D.chTw u μ).stab j c) : ℕ) : ℂ))⁻¹ • entRec t Tw u μ j c x) c' y'
  rw [compatible_lift_exists D L hT Gi Gl Kc0 Dx cX ex t u μ j (lt_of_lt_of_le hj hm) _ _ hQ.1 hQ.2 c' y']
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, entRec]

theorem tieRat_recOf {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) (t : KerEntTied ex) (Tw : TwForms D)
    (u : D.what₂.Word) (μ : D.what₂.Tup) (ι : ℂ →+* Y.Kc) (σ : D.what₂.LL →+* X.G.Kf)
    (cmp : ∀ j, ((Tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (e : ∀ j, ↥(Y.Rep j) ≃ (D.chTw u μ).cls j)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (hK : ∀ j < X.mm, (Tw.fm u μ).KRat j) :
    TieRat (recOf X Y t Tw u μ ι σ cmp Rd e Sr) := by
  intro j hj x
  change ((Tw.fm u μ).lat j).V at x
  obtain ⟨y, hy⟩ := hK j hj x
  show (Tw.fm u μ).emb (j + 1) (klRec Tw u μ j x) = (D.chTw u μ).K j ((Tw.fm u μ).emb j x)
  rw [klRec, Formalism.L2.G.Cmp.ratMap_eq _ _ _ _ x y (by exact hy)]
  exact hy

theorem second_kernel_of_data : K2OfParams := by
  intro D L hT Gi Gl Kc0 Dx cX ex t Tw u μ p _ X Y ι σ cmp Rd e Sr hm hK hC hRd hCl hSer hDel hSp
  have hR := tieRat_recOf X Y t Tw u μ ι σ cmp Rd e Sr hK
  exact second_kernel_nonzero_unit D p X Y _ (tieChain_of_K _ hC hR) hR
    (recSum_recOf X Y t Tw u μ ι σ cmp Rd e Sr hm) hRd hCl hSer hDel hSp

theorem admissible_third_of_data : Adm3bOfRec := by
  intro D L hT Gi Gl Kc0 Dx cX ex t Tw u μ p _ X Y ι σ cmp Rd e Sr hK hC hSp hUp
  exact admissible_third_of_forms D p X Y _ (tieChain_of_K _ hC (tieRat_recOf X Y t Tw u μ ι σ cmp Rd e Sr hK)) hSp hUp

end Rec

end Formalism.L2.KerInert.K2
