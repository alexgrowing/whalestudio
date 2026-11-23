import Mathlib
import GroundTheory.PAdicHodge.WAFracFinal
import GroundTheory.PAdicHodge.ExistsFactorAnn
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WAFrac

open Laurent Filter Topology UniformSpace
open _root_.WittVector WittTilt WAEval TeichLift PhiGamma ACris WABridge WAPeriodT

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔽" => frob ℂ_[p] p

theorem list_prod_dvd_of_pairwise {α A : Type*} [CommRing A] (f : α → A) {w : A} :
    ∀ l : List α, (∀ x ∈ l, f x ∣ w) → l.Pairwise (fun x y => IsCoprime (f x) (f y)) →
      (l.map f).prod ∣ w
  | [], _, _ => by simp
  | x :: l, hd, hp' => by
    rw [List.pairwise_cons] at hp'
    rw [List.map_cons, List.prod_cons]
    have hc : IsCoprime (f x) (l.map f).prod := by
      clear hd
      induction l with
      | nil => simp [isCoprime_one_right]
      | cons y l ih =>
        rw [List.map_cons, List.prod_cons]
        exact (hp'.1 y List.mem_cons_self).mul_right
          (ih ⟨fun z hz => hp'.1 z (List.mem_cons_of_mem _ hz), (List.pairwise_cons.1 hp'.2).2⟩)
    exact hc.mul_dvd (hd x List.mem_cons_self)
      (list_prod_dvd_of_pairwise f l (fun y hy => hd y (List.mem_cons_of_mem _ hy)) hp'.2)

abbrev radBig : Set.Ioo (0 : ℝ) 1 := radTwo p

def radSmall : Set.Ioc (0 : ℝ) (radBig (p := p)) :=
  ⟨(p : ℝ)⁻¹, inv_pos.2 (Nat.cast_pos.2 hp.out.pos), inv_p_lt_radTwo.le⟩

theorem coe_radSmall : ((radSmall (p := p) : Set.Ioc (0 : ℝ) _) : ℝ) = (p : ℝ)⁻¹ := rfl

def radMid : Set.Ioo (0 : ℝ) 1 :=
  ⟨((p : ℝ)⁻¹ + rhoMid p) / 2, by have := WAEval.inv_p_pos (p := p); have := (rhoMid p).2.1; positivity,
    by have := (rhoMid p).2.2; have := inv_p_lt_rhoMid (p := p); linarith⟩

theorem inv_p_lt_radMid : (p : ℝ)⁻¹ < radMid (p := p) := by
  show (p : ℝ)⁻¹ < ((p : ℝ)⁻¹ + rhoMid p) / 2; have := inv_p_lt_rhoMid (p := p); linarith

theorem radMid_lt_rhoMid : (radMid (p := p) : ℝ) < rhoMid p := by
  show ((p : ℝ)⁻¹ + rhoMid p) / 2 < rhoMid p; have := inv_p_lt_rhoMid (p := p); linarith

abbrev radRho : Set.Ioo (0 : ℝ) 1 := (𝔽).rootRadius (radMid (p := p))

theorem coe_inRad_radRho : ((inRad p (radRho (p := p)) : Set.Ioc (0 : ℝ) _) : ℝ) = radMid (p := p) :=
  congrArg Subtype.val ((𝔽).powRadius_rootRadius (radMid (p := p)))

theorem inv_p_le_inRad : (p : ℝ)⁻¹ ≤ ((inRad p (radRho (p := p)) : Set.Ioc (0 : ℝ) _) : ℝ) := by
  rw [coe_inRad_radRho]; exact inv_p_lt_radMid.le

theorem radSmall_lt_inRad :
    ((radSmall (p := p) : Set.Ioc (0 : ℝ) _) : ℝ) < ((inRad p (radRho (p := p)) : Set.Ioc (0 : ℝ) _) : ℝ) := by
  rw [coe_inRad_radRho, coe_radSmall]; exact inv_p_lt_radMid

theorem radRho_lt_radBig : ((radRho (p := p) : Set.Ioo (0 : ℝ) 1) : ℝ) < (radBig (p := p) : ℝ) := by
  show (((𝔽).rootRadius (radMid (p := p)) : Set.Ioo (0 : ℝ) 1) : ℝ) < (((𝔽).rootRadius (rhoMid p) :
    Set.Ioo (0 : ℝ) 1) : ℝ)
  rw [rootRadius_coe, rootRadius_coe]
  exact Real.rpow_lt_rpow (radMid (p := p)).2.1.le radMid_lt_rhoMid
    (inv_pos.2 (Nat.cast_pos.2 hp.out.pos))

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

def ptStab (ξ : (𝓣).int) : Subgroup Gal(PadicAlgCl p/K) where
  carrier := {σ | ∃ u : (𝓣).int, IsUnit u ∧ ((galIso σ).ψ ξ : WC p) = u * ξ}
  one_mem' := ⟨1, isUnit_one, by rw [galIso_one]; simp⟩
  mul_mem' := by
    rintro σ τ ⟨u, hu, hσ⟩ ⟨v, hv, hτ⟩
    refine ⟨⟨(galIso σ).ψ v, galIso_mem_int σ v.2⟩ * u, ?_, ?_⟩
    · refine IsUnit.mul ?_ hu
      obtain ⟨w, hw⟩ := hv.exists_right_inv
      refine isUnit_iff_exists_inv.2 ⟨⟨(galIso σ).ψ w, galIso_mem_int σ w.2⟩, Subtype.ext ?_⟩
      have := congrArg (fun x : (𝓣).int => (galIso σ).ψ (x : WC p)) hw
      simp only [Subring.coe_mul, map_mul, Subring.coe_one, map_one] at this
      simpa using this
    · show (galIso (σ * τ)).ψ (ξ : WC p) = _
      rw [galIso_mul, TeichLift.TeichIso.comp_ψ, hτ, map_mul, hσ]
      simp only [Subring.coe_mul]; ring
  inv_mem' := by
    rintro σ ⟨u, hu, hσ⟩
    have h1 := congrArg (galIso σ⁻¹).ψ hσ
    rw [← TeichLift.TeichIso.comp_ψ, ← galIso_mul, inv_mul_cancel, galIso_one, map_mul] at h1
    simp only [TeichLift.TeichIso.refl_ψ] at h1
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    refine ⟨⟨(galIso σ⁻¹).ψ w, galIso_mem_int σ⁻¹ w.2⟩, ?_, ?_⟩
    · refine isUnit_iff_exists_inv.2 ⟨⟨(galIso σ⁻¹).ψ u, galIso_mem_int σ⁻¹ u.2⟩, Subtype.ext ?_⟩
      have := congrArg (fun x : (𝓣).int => (galIso σ⁻¹).ψ (x : WC p)) (show w * u = 1 by rw [mul_comm]; exact hw)
      simp only [Subring.coe_mul, map_mul, Subring.coe_one, map_one] at this
      simpa using this
    · have hwu : ((galIso σ⁻¹).ψ w : WC p) * (galIso σ⁻¹).ψ u = 1 := by
        rw [← map_mul]
        have := congrArg (fun x : (𝓣).int => (x : WC p)) (show w * u = 1 by rw [mul_comm]; exact hw)
        simp only [Subring.coe_mul, Subring.coe_one] at this
        rw [this, map_one]
      show ((galIso σ⁻¹).ψ ξ : WC p) = (galIso σ⁻¹).ψ w * ξ
      calc ((galIso σ⁻¹).ψ ξ : WC p) = (galIso σ⁻¹).ψ w * ((galIso σ⁻¹).ψ u * (galIso σ⁻¹).ψ ξ) := by
            rw [← mul_assoc, hwu, one_mul]
        _ = (galIso σ⁻¹).ψ w * ξ := by rw [← h1]

section Main

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

theorem hσSmall : (p : ℝ)⁻¹ ≤ ((radSmall (p := p) : Set.Ioc (0 : ℝ) _) : ℝ) := le_of_eq rfl

def denSet (a b : BCrisPlus ℂ_[p] p) : Set (BCrisPlus ℂ_[p] p) := {β | ∃ γ, β * a = γ * b}

def IsDenPt (a b : BCrisPlus ℂ_[p] p) (P : (𝓣).Pt) : Prop :=
  ∀ β ∈ denSet a b, (𝓣).ξAnn (ρ0 := radBig (p := p)) (σ0 := radSmall) P.1 ∣ bcrisToAnn hσSmall β

variable {a b : BCrisPlus ℂ_[p] p}
  (hrel : ∀ σ : Gal(PadicAlgCl p/K), σ • a * b - a * σ • b =
    algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) (kummerC hε hζ σ : ℚ_[p]) * periodTPlus hε * σ • b * b)

include hrel in
theorem smul_mem_denSet (hb : b ≠ 0) (σ : Gal(PadicAlgCl p/K)) {β : BCrisPlus ℂ_[p] p}
    (hβ : β ∈ denSet a b) : σ • β ∈ denSet a b := by
  have := isDomain_bCrisPlus (p := p)
  obtain ⟨γ, hγ⟩ := hβ
  have hσb : σ • b ≠ 0 := fun h => hb (MulAction.injective σ (show σ • b = σ • (0 : BCrisPlus ℂ_[p] p) by
    rw [h, smul_zero]))
  exact ⟨_, galois_mem_den (MulSemiringAction.toRingHom _ _ σ) hσb (hrel σ) hγ⟩

include hrel in
theorem isDenPt_galPt (hb : b ≠ 0) {P : (𝓣).Pt} (hP : IsDenPt a b P) (σ : Gal(PadicAlgCl p/K)) :
    IsDenPt a b (galPt σ P) := by
  intro β hβ
  have h1 := hP _ (smul_mem_denSet hε hζ hrel hb σ⁻¹ hβ)
  have h2 := map_dvd (galIso σ).annMap h1
  rw [annMap_ξAnn, annMap_bcrisToAnn] at h2
  have e : galPlus σ (σ⁻¹ • β) = β := smul_inv_smul σ β
  rwa [e] at h2

theorem ptRadBig (P : (𝓣).Pt) (hr : (p : ℝ)⁻¹ < (𝓣).ptRad P.1 ∧ (𝓣).ptRad P.1 < radTwo p) :
    (𝓣).ptRad P.1 ∈ Set.Icc ((radSmall (p := p) : Set.Ioc (0 : ℝ) _) : ℝ) (radBig (p := p)) :=
  ⟨hr.1.le, hr.2.le⟩

set_option maxHeartbeats 3200000 in
include hrel in

theorem finiteIndex_ptStab (hb : b ≠ 0) {P : (𝓣).Pt} (hP : IsDenPt a b P)
    (hr : (p : ℝ)⁻¹ < (𝓣).ptRad P.1 ∧ (𝓣).ptRad P.1 < radTwo p) :
    (ptStab (K := K) P.1).FiniteIndex := by
  have := isDomain_bCrisPlus (p := p)
  set w := bcrisToAnn (ρ0 := radBig (p := p)) hσSmall b with hwdef
  have hw : ∀ r, 0 < (𝓣).annNorm _ _ r w := annNorm_bcrisToAnn_pos hσSmall hb
  set rr : AnnRad (radBig (p := p)) radSmall := ⟨(𝓣).ptRad P.1, ptRadBig P hr⟩
  have hab : ((annIn (radBig (p := p)) radSmall : AnnRad _ _) : ℝ) < rr := hr.1
  have hcd : (rr : ℝ) < (annOut (radBig (p := p)) radSmall : AnnRad _ _) := hr.2

  have hbI : b ∈ denSet a b := ⟨a, mul_comm b a⟩
  have key : ∀ (n : ℕ) (g : Fin n → Gal(PadicAlgCl p/K)),
      (∀ i j, i ≠ j → (g j)⁻¹ * g i ∉ ptStab (K := K) P.1) →
      ((List.finRange n).map fun i => galPt (g i) P).length ≤ ((List.finRange n).map fun i => galPt (g i) P).length
        ∧ (((List.finRange n).map fun i => galPt (g i) P).length : ℝ) ≤
        (Real.log ((𝓣).annNorm _ _ (annOut _ _) w) - Real.log ((𝓣).annNorm _ _ rr w)) /
          (Real.log (annOut (radBig (p := p)) radSmall : AnnRad _ _) - Real.log rr) -
        (Real.log ((𝓣).annNorm _ _ rr w) - Real.log ((𝓣).annNorm _ _ (annIn _ _) w)) /
          (Real.log rr - Real.log (annIn (radBig (p := p)) radSmall : AnnRad _ _)) := by
    intro n g hg
    refine ⟨le_rfl, (𝓣).length_le_of_prod_dvd w hw _ rr rr _ hab le_rfl hcd _ ?_ ?_⟩
    · intro Q hQ
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hQ
      rw [ptRad_galPt]; exact ⟨le_rfl, le_rfl⟩
    · rw [List.map_map]
      refine list_prod_dvd_of_pairwise _ _ (fun i _ => isDenPt_galPt hε hζ hrel hb hP (g i) b hbI) ?_
      refine (List.nodup_finRange n).pairwise_of_forall_ne fun i _ j _ hij => ?_
      set Qi := galPt (g i) P
      set Qj := galPt (g j) P
      have hri : (𝓣).ptRad Qi.1 ∈ Set.Icc ((radSmall (p := p) : Set.Ioc (0 : ℝ) _) : ℝ) (radBig (p := p)) := by
        rw [ptRad_galPt]; exact ptRadBig P hr
      have hne : (𝓣).annEval Qi.2 hri ((𝓣).ξAnn (ρ0 := radBig (p := p)) (σ0 := radSmall) Qj.1) ≠ 0 := by
        refine annEval_ξAnn_ne_zero hri (by rw [ptRad_galPt, ptRad_galPt]) ?_
        rintro ⟨u, hu, hQ⟩
        refine hg j i (Ne.symm hij) ⟨⟨(galIso (g i)⁻¹).ψ u, galIso_mem_int _ u.2⟩, ?_, ?_⟩
        · obtain ⟨w', hw'⟩ := hu.exists_right_inv
          refine isUnit_iff_exists_inv.2 ⟨⟨(galIso (g i)⁻¹).ψ w', galIso_mem_int _ w'.2⟩, Subtype.ext ?_⟩
          have := congrArg (fun x : (𝓣).int => (galIso (g i)⁻¹).ψ (x : WC p)) hw'
          simp only [Subring.coe_mul, map_mul, Subring.coe_one, map_one] at this
          simpa using this
        · have h1 := congrArg (fun x : (𝓣).int => (galIso (g i)⁻¹).ψ (x : WC p)) hQ
          simp only [Subring.coe_mul, map_mul] at h1
          show (galIso ((g i)⁻¹ * g j)).ψ (P.1 : WC p) = _
          rw [galIso_mul, TeichLift.TeichIso.comp_ψ]
          have e1 : (galIso (g i)⁻¹).ψ ((galIso (g i)).ψ (P.1 : WC p)) = P.1 := by
            rw [← TeichLift.TeichIso.comp_ψ, ← galIso_mul, inv_mul_cancel, galIso_one]; rfl
          change (galIso (g i)⁻¹).ψ ((galIso (g j)).ψ (P.1 : WC p)) =
            (galIso (g i)⁻¹).ψ (u : WC p) * (galIso (g i)⁻¹).ψ ((galIso (g i)).ψ (P.1 : WC p)) at h1
          rw [h1, e1]
      obtain ⟨α, β, hαβ⟩ := (𝓣).exists_bezout_ann Qi.2 hri hne
      exact ⟨α, β, hαβ⟩

  have hfin : Finite (Gal(PadicAlgCl p/K) ⧸ ptStab (K := K) P.1) := by
    by_contra hinf
    have : Infinite (Gal(PadicAlgCl p/K) ⧸ ptStab (K := K) P.1) := not_finite_iff_infinite.1 hinf
    set e := Infinite.natEmbedding (Gal(PadicAlgCl p/K) ⧸ ptStab (K := K) P.1)
    set Bd := (Real.log ((𝓣).annNorm _ _ (annOut _ _) w) - Real.log ((𝓣).annNorm _ _ rr w)) /
          (Real.log (annOut (radBig (p := p)) radSmall : AnnRad _ _) - Real.log rr) -
        (Real.log ((𝓣).annNorm _ _ rr w) - Real.log ((𝓣).annNorm _ _ (annIn _ _) w)) /
          (Real.log rr - Real.log (annIn (radBig (p := p)) radSmall : AnnRad _ _))
    set n := ⌈Bd⌉₊ + 1
    set g : Fin n → Gal(PadicAlgCl p/K) := fun i => Quotient.out (e i)
    have hg : ∀ i j, i ≠ j → (g j)⁻¹ * g i ∉ ptStab (K := K) P.1 := by
      intro i j hij hmem
      have h1 : (QuotientGroup.mk (g j) : Gal(PadicAlgCl p/K) ⧸ ptStab (K := K) P.1) = QuotientGroup.mk (g i) :=
        QuotientGroup.eq.2 hmem
      have h2 : e j = e i := by
        have hj : (QuotientGroup.mk (g j) : Gal(PadicAlgCl p/K) ⧸ ptStab (K := K) P.1) = e j :=
          Quotient.out_eq (e j)
        have hi : (QuotientGroup.mk (g i) : Gal(PadicAlgCl p/K) ⧸ ptStab (K := K) P.1) = e i :=
          Quotient.out_eq (e i)
        rw [← hj, ← hi, h1]
      exact hij (Fin.ext (e.injective h2).symm)
    have hk := (key n g hg).2
    rw [List.length_map, List.length_finRange] at hk
    have : (n : ℝ) > Bd := by
      have := Nat.le_ceil Bd
      push_cast [n]; linarith
    linarith
  exact Subgroup.finiteIndex_of_finite_quotient

set_option maxHeartbeats 3200000 in
include hrel in

theorem dvd_tTilde_of_isDenPt [FiniteDimensional ℚ_[p] K] (hb : b ≠ 0) {P : (𝓣).Pt}
    (hP : IsDenPt a b P) (hr : (p : ℝ)⁻¹ < (𝓣).ptRad P.1 ∧ (𝓣).ptRad P.1 < radTwo p) :
    (𝓣).ξAnn (ρ0 := radBig (p := p)) (σ0 := radSmall) P.1 ∣
      (𝓣).toAnn (radBig (p := p)) radSmall (tTildeExt p ε (radBig (p := p))) := by
  have := finiteIndex_ptStab hε hζ hrel hb hP hr
  have h0 := ptEval_tTilde_eq_zero_of_fixed hε hζ (ptStab (K := K) P.1) P.2 hr.1.le hr.2.le
    (fun σ hσ => hσ) (radBig (p := p)) hr.2 (tTildeExt p ε _) (ofRad_tTildeExt hε hζ _)
  rw [← (𝓣).annEval_toAnn P.2 (ptRadBig P hr)] at h0
  obtain ⟨y, hy⟩ := ((𝓣).annEval_eq_zero_iff P.2 (ptRadBig P hr) _).1 h0
  exact ⟨y, hy⟩

abbrev AnnS := (𝓣).Ann (radRho (p := p)) (inRad p (radRho (p := p)))

def resS : (𝓣).Ann (radBig (p := p)) radSmall →+* AnnS (p := p) :=
  (𝓣).annRes radRho_lt_radBig.le radSmall_lt_inRad.le

omit hε hζ in

def denIdealS (a b : BCrisPlus ℂ_[p] p) : Ideal (AnnS (p := p)) :=
  Ideal.span ((fun β => resS (bcrisToAnn hσSmall β)) '' denSet a b)

include hε hζ in
theorem resS_tTilde :
    resS ((𝓣).toAnn (radBig (p := p)) radSmall (tTildeExt p ε (radBig (p := p)))) =
      (𝓣).toAnn (radRho (p := p)) (inRad p (radRho (p := p))) (tTildeExt p ε (radRho (p := p))) := by
  rw [resS, (𝓣).annRes_toAnn, res_tTildeExt hε hζ]

theorem ptRad_bounds {P : (𝓣).Pt}
    (h : ((inRad p (radRho (p := p)) : Set.Ioc (0 : ℝ) _) : ℝ) ≤ (𝓣).ptRad P.1 ∧
      (𝓣).ptRad P.1 ≤ (radRho (p := p) : ℝ)) :
    (p : ℝ)⁻¹ < (𝓣).ptRad P.1 ∧ (𝓣).ptRad P.1 < radTwo p :=
  ⟨(show (p : ℝ)⁻¹ < _ from (coe_radSmall (p := p)) ▸ radSmall_lt_inRad).trans_le h.1,
    h.2.trans_lt radRho_lt_radBig⟩

set_option maxHeartbeats 3200000 in
include hrel in

theorem exists_pow_mem_span [FiniteDimensional ℚ_[p] K] (hb : b ≠ 0) :
    ∀ l : List (𝓣).Pt, (∀ P ∈ l, ((inRad p (radRho (p := p)) : Set.Ioc (0 : ℝ) _) : ℝ) ≤ (𝓣).ptRad P.1 ∧
      (𝓣).ptRad P.1 ≤ (radRho (p := p) : ℝ)) →
      ∃ (m : ℕ) (c : AnnS (p := p)),
        (𝓣).toAnn (radRho (p := p)) (inRad p (radRho (p := p))) (tTildeExt p ε (radRho (p := p))) ^ m -
          c * (l.map fun P => (𝓣).ξAnn P.1).prod ∈ denIdealS a b
  | [], _ => ⟨0, 1, by simp⟩
  | P :: l, hl => by
    obtain ⟨m, c, hmc⟩ := exists_pow_mem_span hb l fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ)
    have hrP := ptRad_bounds (hl P List.mem_cons_self)
    set t' := (𝓣).toAnn (radRho (p := p)) (inRad p (radRho (p := p))) (tTildeExt p ε (radRho (p := p)))
    rw [List.map_cons, List.prod_cons]
    by_cases hS : IsDenPt a b P
    · obtain ⟨d, hd⟩ := dvd_tTilde_of_isDenPt hε hζ hrel hb hS hrP
      have hd' := congrArg resS hd
      rw [resS_tTilde hε hζ, map_mul, resS, annRes_ξAnn] at hd'
      refine ⟨m + 1, resS d * c, ?_⟩
      have e : t' ^ (m + 1) - resS d * c * ((𝓣).ξAnn P.1 * (l.map fun P => (𝓣).ξAnn P.1).prod) =
          t' * (t' ^ m - c * (l.map fun P => (𝓣).ξAnn P.1).prod) := by
        have hd'' : t' = (𝓣).ξAnn P.1 * resS d := hd'
        rw [hd'']; ring
      rw [e]
      exact Ideal.mul_mem_left _ _ hmc
    · simp only [IsDenPt, not_forall] at hS
      obtain ⟨β, hβ, hnd⟩ := hS
      have hne : (𝓣).annEval P.2 (ptRadBig P hrP) (bcrisToAnn hσSmall β) ≠ 0 := fun h0 =>
        hnd (by obtain ⟨y, hy⟩ := ((𝓣).annEval_eq_zero_iff P.2 (ptRadBig P hrP) _).1 h0; exact ⟨y, hy⟩)
      obtain ⟨α, α', hαα'⟩ := (𝓣).exists_bezout_ann P.2 (ptRadBig P hrP) hne
      have h1 := congrArg resS hαα'
      rw [map_add, map_mul, map_mul, map_one, resS, annRes_ξAnn] at h1
      refine ⟨m, resS α * c, ?_⟩
      have e : t' ^ m - resS α * c * ((𝓣).ξAnn P.1 * (l.map fun P => (𝓣).ξAnn P.1).prod) =
          (t' ^ m - c * (l.map fun P => (𝓣).ξAnn P.1).prod) +
            (c * (l.map fun P => (𝓣).ξAnn P.1).prod * resS α') * resS (bcrisToAnn hσSmall β) := by
        rw [resS]; linear_combination (-(c * (l.map fun P => (𝓣).ξAnn P.1).prod)) * h1
      rw [e]
      exact add_mem hmc (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨β, hβ, rfl⟩))

set_option maxHeartbeats 3200000 in
include hrel in

theorem false_of_frac [FiniteDimensional ℚ_[p] K] (hb : b ≠ 0)
    (hφ : phiPlus ℂ_[p] p a * b = (p : BCrisPlus ℂ_[p] p) * a * phiPlus ℂ_[p] p b) : False := by
  have := isDomain_bCrisPlus (p := p)
  set w := bcrisToAnn (ρ0 := radBig (p := p)) hσSmall b with hwdef
  have hw : ∀ r, 0 < (𝓣).annNorm _ _ r w := annNorm_bcrisToAnn_pos hσSmall hb
  obtain ⟨l, u, hl, hu, hfac⟩ := (𝓣).exists_factor_ann w hw (ρ1 := radRho (p := p))
    (σ1 := inRad p (radRho (p := p))) radRho_lt_radBig radSmall_lt_inRad
  obtain ⟨m, c, hmc⟩ := exists_pow_mem_span hε hζ hrel hb l hl
  set J := denIdealS (p := p) a b
  have hbI : b ∈ denSet a b := ⟨a, mul_comm b a⟩
  have hwJ : resS w ∈ J := Ideal.subset_span ⟨b, hbI, rfl⟩
  have hprod : (l.map fun P => (𝓣).ξAnn P.1).prod ∈ J := by
    have e : (l.map fun P => (𝓣).ξAnn P.1).prod = resS w * ((hu.unit⁻¹ : (AnnS (p := p))ˣ) : AnnS (p := p)) := by
      rw [resS, hfac, mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [e]; exact Ideal.mul_mem_right _ _ hwJ
  set t' := (𝓣).toAnn (radRho (p := p)) (inRad p (radRho (p := p))) (tTildeExt p ε (radRho (p := p)))
  have htJ : t' ^ m ∈ J := by
    have := add_mem hmc (Ideal.mul_mem_left J c hprod)
    rwa [sub_add_cancel] at this
  have hY : ∃ Y, Y * resS (bcrisToAnn hσSmall b) = t' ^ m * resS (bcrisToAnn hσSmall a) := by
    refine Submodule.span_induction (p := fun x _ => ∃ Y, Y * resS (bcrisToAnn hσSmall b) =
      x * resS (bcrisToAnn hσSmall a)) ?_ ?_ ?_ ?_ htJ
    · rintro x ⟨β, ⟨γ, hγ⟩, rfl⟩
      exact ⟨resS (bcrisToAnn hσSmall γ), by rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hγ]⟩
    · exact ⟨0, by rw [zero_mul, zero_mul]⟩
    · rintro x y - - ⟨Y₁, h₁⟩ ⟨Y₂, h₂⟩
      exact ⟨Y₁ + Y₂, by rw [add_mul, h₁, h₂, add_mul]⟩
    · rintro c' x - ⟨Y, h⟩
      exact ⟨c' * Y, by rw [mul_assoc, h, smul_eq_mul, mul_assoc]⟩
  obtain ⟨Y, hY⟩ := hY
  rw [resS, annRes_bcrisToAnn, annRes_bcrisToAnn] at hY
  exact false_of_mul_eq_tTilde_pow hε hζ (radRho (p := p)) inv_p_le_inRad radRho_lt_radBig.le hb hφ hrel hY

end Main

end WAFrac

end GroundTheory.PAdicHodge
