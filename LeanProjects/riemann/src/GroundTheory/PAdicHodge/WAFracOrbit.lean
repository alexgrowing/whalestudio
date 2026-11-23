import Mathlib
import GroundTheory.PAdicHodge.WAPeriodT
import GroundTheory.PAdicHodge.WABridgeGerm
import GroundTheory.PAdicHodge.CauchySeqOfIncrements
import GroundTheory.PAdicHodge.ExtRobbaTrivialV
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem map_tail (Ψ : Γ →+* Γ) (g : L → L) (hred : ∀ x, T.red (Ψ x) = g (T.red x))
    (hπ : Ψ T.π = T.π) (hteich : ∀ c, Ψ (T.teich c) = T.teich (g c)) (x : Γ) :
    Ψ (T.tail x) = T.tail (Ψ x) := by
  have h1 := congrArg Ψ (T.eq_teich_add_π_mul_tail x)
  rw [map_add, map_mul, hteich, hπ] at h1
  have h2 := T.eq_teich_add_π_mul_tail (Ψ x)
  rw [hred] at h2
  have hz : (Ψ (T.tail x) - T.tail (Ψ x)) * T.π = 0 := by linear_combination h2 - h1
  exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 T.π_mem_nonZeroDivisors) _ hz)

theorem map_normPt (Ψ : Γ →+* Γ) (g : L → L) (hred : ∀ x, T.red (Ψ x) = g (T.red x))
    (hπ : Ψ T.π = T.π) (hteich : ∀ c, Ψ (T.teich c) = T.teich (g c)) (ΨB : T.B →+* T.B)
    (hB : ∀ x, ΨB (algebraMap Γ T.B x) = algebraMap Γ T.B (Ψ x)) {ξ η : T.int}
    (hξ : T.IsPrimOne ξ) (hη : T.IsPrimOne η) (hξη : (η : Γ) = Ψ ξ) :
    ΨB (T.normPt hξ) = T.normPt hη := by
  have hinv : ΨB (IsLocalization.Away.invSelf T.π) = IsLocalization.Away.invSelf T.π := by
    have e1 := IsLocalization.Away.mul_invSelf (S := T.B) T.π
    have e2 := congrArg ΨB e1
    rw [map_mul, hB, hπ, map_one] at e2
    calc ΨB (IsLocalization.Away.invSelf T.π)
        = ΨB (IsLocalization.Away.invSelf T.π) *
            (algebraMap Γ T.B T.π * IsLocalization.Away.invSelf T.π) := by rw [e1, mul_one]
      _ = IsLocalization.Away.invSelf T.π := by rw [← mul_assoc, mul_comm (ΨB _), e2, one_mul]
  have htail : Ψ (T.ξtail ξ : Γ) = (T.ξtail η : Γ) := by
    show Ψ (T.tail ξ) = T.tail η
    rw [T.map_tail Ψ g hred hπ hteich, hξη]
  have hv : Ψ (T.vInv hξ : Γ) = (T.vInv hη : Γ) := by
    have e1 := congrArg Ψ (T.ξtail_mul_vInv hξ)
    rw [map_mul, map_one, htail] at e1
    have e2 := T.ξtail_mul_vInv hη
    calc Ψ (T.vInv hξ : Γ) = Ψ (T.vInv hξ : Γ) * ((T.ξtail η : Γ) * (T.vInv hη : Γ)) := by
          rw [e2, mul_one]
      _ = (T.vInv hη : Γ) := by rw [← mul_assoc, mul_comm (Ψ _), e1, one_mul]
  have hc : T.coeff (η : Γ) 0 = g (T.coeff (ξ : Γ) 0) := by
    rw [coeff_zero, coeff_zero, hξη, hred]
  rw [normPt, normPt, map_add, map_one, map_mul, hB, hinv, normU, normU, map_mul, hteich, hv, hc]

theorem normPt_eq_mul_of_assoc {ξ η : T.int} (hξ : T.IsPrimOne ξ) (hη : T.IsPrimOne η) {u : T.int}
    (hu : IsUnit u) (h : (η : Γ) = u * ξ) :
    T.normPt hξ = T.normPt hη *
      algebraMap Γ T.B ((T.ξtail η : Γ) * ((hu.unit⁻¹ : T.intˣ) : T.int) * (T.vInv hξ : Γ)) := by
  have hu1 : (u : Γ) * (((hu.unit⁻¹ : T.intˣ) : T.int) : Γ) = 1 := by
    have h' : ((u * ((hu.unit⁻¹ : T.intˣ) : T.int) : T.int) : Γ) = ((1 : T.int) : Γ) := by
      rw [hu.mul_val_inv]
    rwa [Subring.coe_mul, Subring.coe_one] at h'
  have hvη := T.ξtail_mul_vInv hη
  rw [normPt_eq, normPt_eq, h]
  simp only [map_mul]
  have e1 := congrArg (algebraMap Γ T.B) hu1
  have e2 := congrArg (algebraMap Γ T.B) hvη
  rw [map_mul, map_one] at e1 e2
  linear_combination (algebraMap Γ T.B (ξ : Γ) * algebraMap Γ T.B (T.vInv hξ : Γ) *
    IsLocalization.Away.invSelf T.π) * (-(algebraMap Γ T.B ((T.ξtail η : Γ)) *
      algebraMap Γ T.B (T.vInv hη : Γ)) * e1 - e2)

end TeichLift

namespace WAFrac

open _root_.WittVector WittTilt PhiGamma TeichLift UniformSpace WAEval WAPeriodT WABridge Filter
  Topology

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p

theorem frob_φ_teich (c : Cb p) : (frob ℂ_[p] p).φ ((𝓣).teich c) = (𝓣).teich (c ^ p) := by
  rw [(frob ℂ_[p] p).φ_teich, frob_a, pow_one]

theorem frob_red (x : WC p) : (𝓣).red ((frob ℂ_[p] p).φ x) = (𝓣).red x ^ p := by
  rw [(frob ℂ_[p] p).red_φ, frob_a, pow_one]

theorem frob_φ_π : (frob ℂ_[p] p).φ (𝓣).π = (𝓣).π := by
  rw [(frob ℂ_[p] p).φ_π, frob_u, mul_one]

theorem isPrimOne_frob {ξ : (𝓣).int} (hξ : (𝓣).IsPrimOne ξ) :
    (𝓣).IsPrimOne ⟨(frob ℂ_[p] p).φ ξ, (frob ℂ_[p] p).map_int _ ξ.2⟩ where
  coeff_zero_ne := by
    show (𝓣).coeff ((frob ℂ_[p] p).φ ξ) 0 ≠ 0
    rw [coeff_frob]; exact pow_ne_zero _ hξ.coeff_zero_ne
  norm_coeff_zero_lt := by
    show ‖(𝓣).coeff ((frob ℂ_[p] p).φ ξ) 0‖ < 1
    rw [coeff_frob, norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hξ.norm_coeff_zero_lt hp.out.ne_zero
  norm_coeff_one := by
    show ‖(𝓣).coeff ((frob ℂ_[p] p).φ ξ) 1‖ = 1
    rw [coeff_frob, norm_pow, hξ.norm_coeff_one, one_pow]

def frobPt (P : (𝓣).Pt) : (𝓣).Pt :=
  ⟨⟨(frob ℂ_[p] p).φ P.1, (frob ℂ_[p] p).map_int _ P.1.2⟩, isPrimOne_frob P.2⟩

theorem coe_frobPt (P : (𝓣).Pt) : ((frobPt P).1 : WC p) = (frob ℂ_[p] p).φ P.1 := rfl

theorem ptRad_frobPt (P : (𝓣).Pt) : (𝓣).ptRad (frobPt P).1 = (𝓣).ptRad P.1 ^ p := by
  show ‖(𝓣).coeff ((frob ℂ_[p] p).φ P.1) 0‖ = ‖(𝓣).coeff (P.1 : WC p) 0‖ ^ p
  rw [coeff_frob, norm_pow]

theorem frob_toB_normPt (P : (𝓣).Pt) :
    (frob ℂ_[p] p).toB ((𝓣).normPt P.2) = (𝓣).normPt (frobPt P).2 :=
  (𝓣).map_normPt ((frob ℂ_[p] p).φ : WC p →+* WC p) (fun c => c ^ p) frob_red frob_φ_π frob_φ_teich
    ((frob ℂ_[p] p).toB : (𝓣).B →+* (𝓣).B) (fun x => (frob ℂ_[p] p).toB_algebraMap x) P.2 (frobPt P).2
    rfl

theorem extFrob_normPtExt (P : (𝓣).Pt) (ρ : Set.Ioo (0 : ℝ) 1) :
    (frob ℂ_[p] p).extFrob ρ ((𝓣).normPtExt P.2 ρ) =
      (𝓣).normPtExt (frobPt P).2 ((frob ℂ_[p] p).powRadius ρ) := by
  rw [normPtExt, (frob ℂ_[p] p).extFrob_coe, normPtExt]
  congr 1
  exact Subtype.ext (frob_toB_normPt P)

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem isPrimOne_gal (σ : Gal(PadicAlgCl p/K)) {ξ : (𝓣).int} (hξ : (𝓣).IsPrimOne ξ) :
    (𝓣).IsPrimOne ⟨(galIso σ).ψ ξ, galIso_mem_int σ ξ.2⟩ where
  coeff_zero_ne := by
    show (𝓣).coeff ((galIso σ).ψ ξ) 0 ≠ 0
    rw [(galIso σ).coeff_map]
    exact fun h => hξ.coeff_zero_ne ((galIso σ).g.injective (h.trans (map_zero _).symm))
  norm_coeff_zero_lt := by
    show ‖(𝓣).coeff ((galIso σ).ψ ξ) 0‖ < 1
    rw [(galIso σ).coeff_map, (galIso σ).norm_g]; exact hξ.norm_coeff_zero_lt
  norm_coeff_one := by
    show ‖(𝓣).coeff ((galIso σ).ψ ξ) 1‖ = 1
    rw [(galIso σ).coeff_map, (galIso σ).norm_g]; exact hξ.norm_coeff_one

def galPt (σ : Gal(PadicAlgCl p/K)) (P : (𝓣).Pt) : (𝓣).Pt :=
  ⟨⟨(galIso σ).ψ P.1, galIso_mem_int σ P.1.2⟩, isPrimOne_gal σ P.2⟩

theorem gal_toB_normPt (σ : Gal(PadicAlgCl p/K)) (P : (𝓣).Pt) :
    (galIso σ).toB ((𝓣).normPt P.2) = (𝓣).normPt (galPt σ P).2 :=
  (𝓣).map_normPt ((galIso σ).ψ : WC p →+* WC p) (galIso σ).g (fun x => (galIso σ).red_ψ x)
    (galIso σ).ψ_π (fun c => (galIso σ).ψ_teich c) ((galIso σ).toB : (𝓣).B →+* (𝓣).B)
    (fun x => (galIso σ).toB_algebraMap x) P.2 (galPt σ P).2 rfl

theorem extMap_normPtExt (σ : Gal(PadicAlgCl p/K)) (P : (𝓣).Pt) (ρ : Set.Ioo (0 : ℝ) 1) :
    (galIso σ).extMap ρ ((𝓣).normPtExt P.2 ρ) = (𝓣).normPtExt (galPt σ P).2 ρ := by
  rw [normPtExt, (galIso σ).extMap_coe, normPtExt]
  congr 1
  exact Subtype.ext (gal_toB_normPt σ P)

end WAFrac

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

open Filter Topology

theorem InfProd.map_prod {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (F1 : T.InfProd ρ0) (F2 : T.InfProd ρ1)
    (M : T.RobbaExt ρ0 →+* T.RobbaExt ρ1) (hM : Continuous M) (h : ∀ n, M (F1.g n) = F2.g n) :
    M F1.prod = F2.prod := by
  have h1 : Tendsto (fun n => M (F1.part n)) atTop (𝓝 (M F1.prod)) :=
    (hM.tendsto _).comp F1.tendsto_part
  have e : (fun n => M (F1.part n)) = F2.part := funext fun n => by
    simp only [InfProd.part]
    rw [_root_.map_prod]
    exact Finset.prod_congr rfl fun i _ => h i
  rw [e] at h1
  exact tendsto_nhds_unique h1 F2.tendsto_part

theorem InfProd.prod_dvd_of_g {ρ0 : Set.Ioo (0 : ℝ) 1} (F1 F2 : T.InfProd ρ0)
    (h : ∀ n, ∃ w w' : T.RobbaExt ρ0, F1.g n = F2.g n * w ∧ w * w' = 1) : F1.prod ∣ F2.prod := by
  choose w w' hw hww' using h
  refine F1.dvd_of_forall fun n => ?_
  have e : F1.part n * ∏ i ∈ Finset.range n, w' i = F2.part n := by
    simp only [InfProd.part]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hw i, mul_assoc, hww' i, mul_one]
  exact (Dvd.intro _ e).trans (F2.part_dvd_prod n)

theorem InfProd.prod_eq_g_zero_mul {ρ0 : Set.Ioo (0 : ℝ) 1} (F : T.InfProd ρ0) :
    F.prod = F.g 0 * (F.shift 1).prod := by
  rw [F.prod_eq_part_mul_shift 1, InfProd.part_succ, InfProd.part_zero, one_mul]

end TeichLift

namespace WAFrac

open _root_.WittVector WittTilt PhiGamma TeichLift UniformSpace WAEval WAPeriodT WABridge Filter
  Topology

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p

section Prod

def ptInf (Q : ℕ → (𝓣).Pt) (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hs : Tendsto s atTop (𝓝 0))
    (hQ : ∀ n, (𝓣).ptRad (Q n).1 ≤ s n) (ρ0 : Set.Ioo (0 : ℝ) 1) : (𝓣).InfProd ρ0 :=
  InfProd.ofLists (𝓣) ρ0 (fun n => [Q n]) s hs0 hs (fun n P hP => by
    rw [List.mem_singleton] at hP; rw [hP]; exact hQ n)

theorem ptInf_g (Q : ℕ → (𝓣).Pt) (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hs : Tendsto s atTop (𝓝 0))
    (hQ : ∀ n, (𝓣).ptRad (Q n).1 ≤ s n) (ρ0 : Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    (ptInf Q s hs0 hs hQ ρ0).g n = (𝓣).normPtExt (Q n).2 ρ0 := by
  show (𝓣).normProd ρ0 [Q n] = _
  rw [normProd_cons, normProd_nil, mul_one]

end Prod

def ptSeq (P0 : (𝓣).Pt) (n : ℕ) : (𝓣).Pt := frobPt^[n] P0

theorem ptSeq_zero (P0 : (𝓣).Pt) : ptSeq P0 0 = P0 := rfl

theorem ptSeq_succ (P0 : (𝓣).Pt) (n : ℕ) : ptSeq P0 (n + 1) = frobPt (ptSeq P0 n) :=
  Function.iterate_succ_apply' _ _ _

theorem ptSeq_succ' (P0 : (𝓣).Pt) (n : ℕ) : ptSeq P0 (n + 1) = ptSeq (frobPt P0) n :=
  Function.iterate_succ_apply _ _ _

theorem ptRad_ptSeq (P0 : (𝓣).Pt) (n : ℕ) :
    (𝓣).ptRad (ptSeq P0 n).1 = (𝓣).ptRad P0.1 ^ p ^ n := by
  induction n with
  | zero => rw [ptSeq_zero, pow_zero, pow_one]
  | succ n ih => rw [ptSeq_succ, ptRad_frobPt, ih, ← pow_mul, pow_succ]

def radSeq (P0 : (𝓣).Pt) (n : ℕ) : ℝ := (𝓣).ptRad P0.1 ^ p ^ n

theorem radSeq_nonneg (P0 : (𝓣).Pt) (n : ℕ) : 0 ≤ radSeq P0 n :=
  pow_nonneg ((𝓣).ptRad_pos' P0.2).le _

theorem tendsto_radSeq (P0 : (𝓣).Pt) : Tendsto (radSeq P0) atTop (𝓝 0) := by
  have h0 := ((𝓣).ptRad_pos' P0.2).le
  have h1 := (𝓣).ptRad_lt_one' P0.2
  refine squeeze_zero (radSeq_nonneg P0) (fun n => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1)
  exact pow_le_pow_of_le_one h0 h1.le (Nat.lt_pow_self hp.out.one_lt).le

def fInf (P0 : (𝓣).Pt) (ρ0 : Set.Ioo (0 : ℝ) 1) : (𝓣).InfProd ρ0 :=
  ptInf (ptSeq P0) (radSeq P0) (radSeq_nonneg P0) (tendsto_radSeq P0)
    (fun n => (ptRad_ptSeq P0 n).le) ρ0

theorem fInf_g (P0 : (𝓣).Pt) (ρ0 : Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    (fInf P0 ρ0).g n = (𝓣).normPtExt (ptSeq P0 n).2 ρ0 :=
  ptInf_g _ _ _ _ _ ρ0 n

theorem res_normPtExt (P : (𝓣).Pt) {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) :
    (𝓣).res h ((𝓣).normPtExt P.2 ρ0) = (𝓣).normPtExt P.2 ρ1 := by
  rw [normPtExt, res_coe, normPtExt]; rfl

theorem extFrob_fProd (P0 : (𝓣).Pt) (ρ0 : Set.Ioo (0 : ℝ) 1) :
    (frob ℂ_[p] p).extFrob ρ0 (fInf P0 ρ0).prod =
      (fInf (frobPt P0) ((frob ℂ_[p] p).powRadius ρ0)).prod := by
  refine InfProd.map_prod _ _ _ ((frob ℂ_[p] p).continuous_extFrob ρ0) fun n => ?_
  rw [fInf_g, fInf_g, extFrob_normPtExt, ← ptSeq_succ, ptSeq_succ']

theorem res_fProd (P0 : (𝓣).Pt) (ρ0 : Set.Ioo (0 : ℝ) 1) :
    (𝓣).res ((frob ℂ_[p] p).powRadius_le_self ρ0) (fInf P0 ρ0).prod =
      (𝓣).normPtExt P0.2 ((frob ℂ_[p] p).powRadius ρ0) *
        (fInf (frobPt P0) ((frob ℂ_[p] p).powRadius ρ0)).prod := by
  set ρ1 := (frob ℂ_[p] p).powRadius ρ0
  have h1 : (𝓣).res ((frob ℂ_[p] p).powRadius_le_self ρ0) (fInf P0 ρ0).prod = (fInf P0 ρ1).prod :=
    InfProd.map_prod _ _ _ ((𝓣).continuous_res _) fun n => by
      rw [fInf_g, fInf_g, res_normPtExt]
  have h2 : ((fInf P0 ρ1).shift 1).prod = (fInf (frobPt P0) ρ1).prod :=
    InfProd.map_prod _ _ (RingHom.id _) continuous_id fun n => by
      show (fInf P0 ρ1).g (1 + n) = _
      rw [fInf_g, fInf_g, add_comm, ptSeq_succ']
  rw [h1, (fInf P0 ρ1).prod_eq_g_zero_mul, h2, fInf_g, ptSeq_zero]

theorem normPtExt_eq_mul_of_assoc {P Q : (𝓣).Pt} {u : (𝓣).int} (hu : IsUnit u)
    (h : (Q.1 : WC p) = u * P.1) (ρ0 : Set.Ioo (0 : ℝ) 1) :
    ∃ w w' : (𝓣).RobbaExt ρ0, (𝓣).normPtExt P.2 ρ0 = (𝓣).normPtExt Q.2 ρ0 * w ∧ w * w' = 1 := by
  set v : (𝓣).int := ((hu.unit⁻¹ : (𝓣).intˣ) : (𝓣).int)
  have hv : (u : WC p) * (v : WC p) = 1 := by
    have h' : ((u * v : (𝓣).int) : WC p) = ((1 : (𝓣).int) : WC p) := by rw [hu.mul_val_inv]
    rwa [Subring.coe_mul, Subring.coe_one] at h'
  set a : WC p := ((𝓣).ξtail Q.1 : WC p) * (v : WC p) * ((𝓣).vInv P.2 : WC p)
  set b : WC p := ((𝓣).vInv Q.2 : WC p) * (u : WC p) * ((𝓣).ξtail P.1 : WC p)
  have ha : a ∈ (𝓣).int := (𝓣).int.mul_mem ((𝓣).int.mul_mem ((𝓣).ξtail Q.1).2 v.2) ((𝓣).vInv P.2).2
  have hb : b ∈ (𝓣).int := (𝓣).int.mul_mem ((𝓣).int.mul_mem ((𝓣).vInv Q.2).2 u.2) ((𝓣).ξtail P.1).2
  have hab : a * b = 1 := by
    have e1 := (𝓣).ξtail_mul_vInv Q.2
    have e2 := (𝓣).ξtail_mul_vInv P.2
    simp only [a, b]
    linear_combination ((𝓣).ξtail Q.1 : WC p) * ((𝓣).vInv Q.2 : WC p) * (v : WC p) * (u : WC p) * e2 +
      ((𝓣).ξtail Q.1 : WC p) * ((𝓣).vInv Q.2 : WC p) * hv + e1
  refine ⟨(((⟨algebraMap _ (𝓣).B a, (𝓣).algebraMap_int_mem_Econ ha ρ0⟩ : (𝓣).Econ ρ0)) : (𝓣).RobbaExt ρ0),
    (((⟨algebraMap _ (𝓣).B b, (𝓣).algebraMap_int_mem_Econ hb ρ0⟩ : (𝓣).Econ ρ0)) : (𝓣).RobbaExt ρ0),
    ?_, ?_⟩
  · rw [normPtExt, normPtExt, ← Completion.coe_mul]
    congr 1
    exact Subtype.ext ((𝓣).normPt_eq_mul_of_assoc P.2 Q.2 hu h)
  · rw [← Completion.coe_mul, ← Completion.coe_one]
    congr 1
    exact Subtype.ext (by simp only [Subring.coe_mul, Subring.coe_one]; rw [← map_mul, hab, map_one])

section Galois

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem ptRad_galPt (σ : Gal(PadicAlgCl p/K)) (P : (𝓣).Pt) :
    (𝓣).ptRad (galPt σ P).1 = (𝓣).ptRad P.1 := by
  show ‖(𝓣).coeff ((galIso σ).ψ P.1) 0‖ = ‖(𝓣).coeff (P.1 : WC p) 0‖
  rw [(galIso σ).coeff_map, (galIso σ).norm_g]

def fInfGal (σ : Gal(PadicAlgCl p/K)) (P0 : (𝓣).Pt) (ρ0 : Set.Ioo (0 : ℝ) 1) : (𝓣).InfProd ρ0 :=
  ptInf (fun n => galPt σ (ptSeq P0 n)) (radSeq P0) (radSeq_nonneg P0) (tendsto_radSeq P0)
    (fun n => by rw [ptRad_galPt]; exact (ptRad_ptSeq P0 n).le) ρ0

theorem extMap_fProd (σ : Gal(PadicAlgCl p/K)) (P0 : (𝓣).Pt) (ρ0 : Set.Ioo (0 : ℝ) 1) :
    (galIso σ).extMap ρ0 (fInf P0 ρ0).prod = (fInfGal σ P0 ρ0).prod :=
  InfProd.map_prod _ _ _ ((galIso σ).continuous_extMap) fun n => by
    rw [fInf_g]
    show _ = (ptInf _ _ _ _ _ ρ0).g n
    rw [ptInf_g, extMap_normPtExt]

theorem exists_assoc_ptSeq (σ : Gal(PadicAlgCl p/K)) (P0 : (𝓣).Pt)
    (h : ∃ u : (𝓣).int, IsUnit u ∧ ((galIso σ).ψ P0.1 : WC p) = u * P0.1) (n : ℕ) :
    ∃ u : (𝓣).int, IsUnit u ∧ ((galPt σ (ptSeq P0 n)).1 : WC p) = u * (ptSeq P0 n).1 := by
  induction n with
  | zero => exact h
  | succ n ih =>
    obtain ⟨u, hu, hue⟩ := ih
    obtain ⟨v, huv⟩ := hu.exists_right_inv
    have huv' : (u : WC p) * (v : WC p) = 1 := by
      have h' : ((u * v : (𝓣).int) : WC p) = ((1 : (𝓣).int) : WC p) := by rw [huv]
      rwa [Subring.coe_mul, Subring.coe_one] at h'
    refine ⟨⟨(frob ℂ_[p] p).φ u, (frob ℂ_[p] p).map_int _ u.2⟩,
      IsUnit.of_mul_eq_one ⟨(frob ℂ_[p] p).φ v, (frob ℂ_[p] p).map_int _ v.2⟩ ?_, ?_⟩
    · apply Subtype.ext
      show (frob ℂ_[p] p).φ (u : WC p) * (frob ℂ_[p] p).φ (v : WC p) = 1
      rw [← map_mul, huv', map_one]
    · have hue' : (galIso σ).ψ ((ptSeq P0 n).1 : WC p) = u * (ptSeq P0 n).1 := hue
      rw [ptSeq_succ]
      show (galIso σ).ψ ((frob ℂ_[p] p).φ (ptSeq P0 n).1) =
        (frob ℂ_[p] p).φ u * (frob ℂ_[p] p).φ (ptSeq P0 n).1
      rw [galIso_frob, hue', map_mul]

theorem exists_fProd_gal (σ : Gal(PadicAlgCl p/K)) (P0 : (𝓣).Pt) (ρ0 : Set.Ioo (0 : ℝ) 1)
    (h : ∃ u : (𝓣).int, IsUnit u ∧ ((galIso σ).ψ P0.1 : WC p) = u * P0.1) :
    ∃ v v' : (𝓣).RobbaExt ρ0,
      (galIso σ).extMap ρ0 (fInf P0 ρ0).prod = (fInf P0 ρ0).prod * v ∧ v * v' = 1 := by
  rw [extMap_fProd]
  have h1 : (fInf P0 ρ0).prod ∣ (fInfGal σ P0 ρ0).prod := InfProd.prod_dvd_of_g _ _ fun n => by
    obtain ⟨u, hu, hue⟩ := exists_assoc_ptSeq σ P0 h n
    rw [fInf_g]
    show ∃ w w', _ = (ptInf _ _ _ _ _ ρ0).g n * w ∧ w * w' = 1
    rw [ptInf_g]
    exact normPtExt_eq_mul_of_assoc hu hue ρ0
  have h2 : (fInfGal σ P0 ρ0).prod ∣ (fInf P0 ρ0).prod := InfProd.prod_dvd_of_g _ _ fun n => by
    obtain ⟨u, hu, hue⟩ := exists_assoc_ptSeq σ P0 h n
    obtain ⟨v, huv⟩ := hu.exists_right_inv
    have hv : IsUnit v := IsUnit.of_mul_eq_one u (by rw [mul_comm]; exact huv)
    have huv' : (u : WC p) * (v : WC p) = 1 := by
      have h' : ((u * v : (𝓣).int) : WC p) = ((1 : (𝓣).int) : WC p) := by rw [huv]
      rwa [Subring.coe_mul, Subring.coe_one] at h'
    have hve : ((ptSeq P0 n).1 : WC p) = v * (galPt σ (ptSeq P0 n)).1 := by
      rw [hue, ← mul_assoc, mul_comm (v : WC p), huv', one_mul]
    show ∃ w w', (ptInf _ _ _ _ _ ρ0).g n = _ * w ∧ w * w' = 1
    rw [ptInf_g, fInf_g]
    exact normPtExt_eq_mul_of_assoc hv hve ρ0
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨a, b, ha, ?_⟩
  apply mul_left_cancel₀ (fInf P0 ρ0).prod_ne_zero
  rw [← mul_assoc, ← ha, ← hb, mul_one]

end Galois

theorem normPt_mem_Edag (P : (𝓣).Pt) : (𝓣).normPt P.2 ∈ (𝓣).Edag :=
  (𝓣).Econ_le_Edag (rhoMid p) ((𝓣).normPt_mem_Econ P.2 _)

def normPtE (P : (𝓣).Pt) : (𝓣).Edag := ⟨_, normPt_mem_Edag P⟩

theorem ofRad_normPtExt (P : (𝓣).Pt) (ρ : Set.Ioo (0 : ℝ) 1) :
    (𝓣).ofRad ρ ((𝓣).normPtExt P.2 ρ) = (𝓣).edagToTilde (normPtE P) := by
  rw [show normPtE P = ⟨(𝓣).normPt P.2, (𝓣).Econ_le_Edag ρ ((𝓣).normPt_mem_Econ P.2 ρ)⟩ from rfl,
    (𝓣).edagToTilde_apply]
  rfl

theorem normPt_ne_zero (P : (𝓣).Pt) : (𝓣).normPt P.2 ≠ 0 := by
  intro h
  have := (𝓣).one_le_norm_normPtExt (ρ0 := rhoMid p) P (topRad _)
  rw [normPtExt, show (⟨(𝓣).normPt P.2, (𝓣).normPt_mem_Econ P.2 (rhoMid p)⟩ : (𝓣).Econ (rhoMid p)) = 0
    from Subtype.ext h, Completion.coe_zero, extNorm_zero] at this
  linarith

def fTilde (P0 : (𝓣).Pt) : (𝓣).RobbaTilde := (𝓣).ofRad (rhoMid p) (fInf P0 (rhoMid p)).prod

theorem fTilde_ne_zero (P0 : (𝓣).Pt) : fTilde P0 ≠ 0 := fun h =>
  (fInf P0 (rhoMid p)).prod_ne_zero ((𝓣).ofRad_injective _ (h.trans (map_zero _).symm))

theorem fTilde_eq (P0 : (𝓣).Pt) :
    fTilde P0 = (𝓣).edagToTilde (normPtE P0) * (frob ℂ_[p] p).tildeFrob (fTilde P0) := by
  unfold fTilde
  rw [(frob ℂ_[p] p).tildeFrob_ofRad, extFrob_fProd,
    ← (𝓣).ofRad_res ((frob ℂ_[p] p).powRadius_le_self (rhoMid p)), res_fProd, map_mul,
    ofRad_normPtExt]

theorem πTilde_eq : (𝓣).πTilde = (p : (𝓣).RobbaTilde) := by
  have e : (⟨algebraMap (WC p) (𝓣).B (𝓣).π, (𝓣).Econ_le_Edag ⟨1 / 2, by norm_num, by norm_num⟩
      ((𝓣).algebraMap_π_mem_Econ _)⟩ : (𝓣).Edag) = (p : (𝓣).Edag) := by
    apply Subtype.ext
    show algebraMap (WC p) (𝓣).B ((p : ℕ) : WC p) = (((p : ℕ) : (𝓣).Edag) : (𝓣).B)
    rw [map_natCast]
    rfl
  show (𝓣).edagToTilde _ = _
  rw [e, map_natCast]

theorem ξExt_extFrobSymm (Q : (𝓣).Pt) (τ : Set.Ioo (0 : ℝ) 1) :
    (frob ℂ_[p] p).extFrobSymm τ ((𝓣).ξExt (frobPt Q).1 τ) =
      (𝓣).ξExt Q.1 ((frob ℂ_[p] p).rootRadius τ) := by
  rw [ξExt, (frob ℂ_[p] p).extFrobSymm_coe, ξExt]
  congr 1
  apply Subtype.ext
  rw [(frob ℂ_[p] p).coe_econFrobSymm]
  show (frob ℂ_[p] p).toB.symm (algebraMap _ _ ((frob ℂ_[p] p).φ Q.1)) = algebraMap _ _ (Q.1 : WC p)
  rw [RingEquiv.symm_apply_eq, (frob ℂ_[p] p).toB_algebraMap]

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

set_option maxHeartbeats 4000000 in
include hε hζ in

theorem exists_eigen_vanishing {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (H : Subgroup Gal(PadicAlgCl p/K)) {ξ' : (𝓣).int} (hξ' : (𝓣).IsPrimOne ξ')
    (hfix : ∀ σ ∈ H, ∃ u : (𝓣).int, IsUnit u ∧ ((galIso σ).ψ ξ' : WC p) = u * ξ') :
    ∃ (k : ℕ) (z : (𝓣).RobbaTilde), z ≠ 0 ∧
      (frob ℂ_[p] p).tildeFrob z = (p : (𝓣).RobbaTilde) ^ (k + 1) * z ∧
      (∀ σ ∈ H, ∃ q : ℚ_[p], q ≠ 0 ∧ (galIso σ).tildeMap z = padicToTilde p q * z) ∧
      (∀ ρ : Set.Ioo (0 : ℝ) 1, ∃ w : (𝓣).RobbaExt ρ, (𝓣).ofRad ρ w = z) ∧
      ∀ (ρ : Set.Ioo (0 : ℝ) 1) (hρ : (𝓣).ptRad ξ' < ρ) (w : (𝓣).RobbaExt ρ), (𝓣).ofRad ρ w = z →
        (𝓣).ptEval hξ' hρ.le w = 0 := by
  classical
  set P0 : (𝓣).Pt := ⟨ξ', hξ'⟩ with hP0
  have ha : 0 < (frob ℂ_[p] p).a := by rw [frob_a]; exact one_pos
  obtain ⟨y, hy, hy0, m, N, hyeq⟩ :=
    (frob ℂ_[p] p).exists_toB_eq_mul ha (normPt_mem_Edag P0) (normPt_ne_zero P0)
  set yE : (𝓣).Edag := ⟨y, hy⟩ with hyEdef
  set Y := (𝓣).edagToTilde yE with hYdef
  have hY0 : Y ≠ 0 := fun h =>
    hy0 (congrArg Subtype.val ((𝓣).edagToTilde_injective (h.trans (map_zero _).symm)))
  have hYu : IsUnit Y := ((𝓣).isUnit_iff Y).2 ⟨hY0, yE, rfl⟩
  have hp0 : (p : (𝓣).RobbaTilde) ≠ 0 := πTilde_eq (p := p) ▸ (𝓣).πTilde_ne_zero
  set c := (𝓣).edagToTilde (normPtE P0) with hcdef
  have hYeq : (p : (𝓣).RobbaTilde) ^ m * (frob ℂ_[p] p).tildeFrob Y =
      (p : (𝓣).RobbaTilde) ^ N * c * Y := by
    have e : TeichFrob.πEdag (𝓣) ^ m * (frob ℂ_[p] p).edagEquiv yE =
        TeichFrob.πEdag (𝓣) ^ N * normPtE P0 * yE :=
      Subtype.ext (by simpa [TeichFrob.πEdag, (frob ℂ_[p] p).edagEquiv_apply, normPtE] using hyeq)
    have := congrArg (𝓣).edagToTilde e
    simp only [map_mul, map_pow, TeichFrob.edagToTilde_πEdag] at this
    rw [← πTilde_eq, hYdef, (frob ℂ_[p] p).tildeFrob_edagToTilde]
    exact this
  set f := fTilde P0 with hfdef
  have hf : f = c * (frob ℂ_[p] p).tildeFrob f := fTilde_eq P0
  have hf0 : f ≠ 0 := fTilde_ne_zero P0
  set t := tTilde p ε with htdef
  have ht : (frob ℂ_[p] p).tildeFrob t = p * t := tildeFrob_tTilde hε hζ
  have ht0 : t ≠ 0 := tTilde_ne_zero hε hζ
  set z := t ^ (m + 1) * f * Y with hzdef
  have hz0 : z ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ ht0) hf0) hY0
  have hzφ : (frob ℂ_[p] p).tildeFrob z = (p : (𝓣).RobbaTilde) ^ (N + 1) * z := by
    apply mul_left_cancel₀ (pow_ne_zero m hp0)
    calc (p : (𝓣).RobbaTilde) ^ m * (frob ℂ_[p] p).tildeFrob z
        = (p * t) ^ (m + 1) * (frob ℂ_[p] p).tildeFrob f *
            ((p : (𝓣).RobbaTilde) ^ m * (frob ℂ_[p] p).tildeFrob Y) := by
          rw [hzdef, map_mul, map_mul, map_pow, ht]; ring
      _ = (p * t) ^ (m + 1) * (frob ℂ_[p] p).tildeFrob f * ((p : (𝓣).RobbaTilde) ^ N * c * Y) := by
          rw [hYeq]
      _ = (p : (𝓣).RobbaTilde) ^ m * ((p : (𝓣).RobbaTilde) ^ (N + 1) *
            (t ^ (m + 1) * (c * (frob ℂ_[p] p).tildeFrob f) * Y)) := by ring
      _ = (p : (𝓣).RobbaTilde) ^ m * ((p : (𝓣).RobbaTilde) ^ (N + 1) * z) := by rw [← hf]
  have hzsymm : (p : (𝓣).RobbaTilde) ^ (N + 1) * (frob ℂ_[p] p).tildeFrobSymm z = z := by
    have e := congrArg (frob ℂ_[p] p).tildeFrobSymm hzφ
    rw [(frob ℂ_[p] p).tildeFrobSymm_tildeFrob, map_mul, map_pow, map_natCast] at e
    exact e.symm
  refine ⟨N, z, hz0, hzφ, ?_, ?_, ?_⟩
  ·
    intro σ hσ
    obtain ⟨v, v', hv, hvv'⟩ := exists_fProd_gal σ P0 (rhoMid p) (hfix σ hσ)
    have hGf : (galIso σ).tildeMap f = f * (𝓣).ofRad (rhoMid p) v := by
      rw [hfdef, fTilde, TeichIso.tildeMap_ofRad, hv, map_mul]
    obtain ⟨χ, hχ⟩ : ∃ χ, χ = padicToTilde p ((cycloChar K σ : ℤ_[p]) : ℚ_[p]) := ⟨_, rfl⟩
    have hGt : (galIso σ).tildeMap t = χ * t := by
      rw [htdef, hχ]; exact galIso_tildeMap_tTilde hε hζ σ
    obtain ⟨Yi, hYi⟩ := hYu.exists_right_inv
    obtain ⟨lam, hlam⟩ : ∃ lam, lam = χ ^ (m + 1) * (𝓣).ofRad (rhoMid p) v * (galIso σ).tildeMap Y * Yi :=
      ⟨_, rfl⟩
    have hGz : (galIso σ).tildeMap z = lam * z := by
      rw [hzdef, map_mul, map_mul, map_pow, hGt, hGf, hlam]
      linear_combination (-(χ ^ (m + 1) * (𝓣).ofRad (rhoMid p) v * (galIso σ).tildeMap Y * t ^ (m + 1) *
        f)) * hYi
    have hlamφ : (frob ℂ_[p] p).tildeFrob lam = lam := by
      have e1 : (frob ℂ_[p] p).tildeFrob ((galIso σ).tildeMap z) =
          (galIso σ).tildeMap ((frob ℂ_[p] p).tildeFrob z) := (galIso_tildeMap_tildeFrob σ z).symm
      have e2 : (frob ℂ_[p] p).tildeFrob ((galIso σ).tildeMap z) =
          (frob ℂ_[p] p).tildeFrob lam * ((p : (𝓣).RobbaTilde) ^ (N + 1) * z) := by
        rw [hGz, map_mul, hzφ]
      have e3 : (galIso σ).tildeMap ((frob ℂ_[p] p).tildeFrob z) =
          (p : (𝓣).RobbaTilde) ^ (N + 1) * (lam * z) := by
        rw [hzφ, map_mul, map_pow, map_natCast, hGz]
      have hne : (p : (𝓣).RobbaTilde) ^ (N + 1) * z ≠ 0 := mul_ne_zero (pow_ne_zero _ hp0) hz0
      exact mul_right_cancel₀ hne (by rw [← e2, e1, e3]; ring)
    obtain ⟨q, hq⟩ := (tildeFrob_eq_self_iff lam).1 hlamφ
    refine ⟨q, ?_, by rw [hGz, hq]⟩
    rintro rfl
    have hinj : Function.Injective (galIso σ).tildeMap := fun a b hab => by
      have := congrArg (galIso σ⁻¹).tildeMap hab
      rwa [← galIso_tildeMap_mul, ← galIso_tildeMap_mul, inv_mul_cancel, galIso_tildeMap_one,
        galIso_tildeMap_one] at this
    apply hz0
    apply hinj
    rw [hGz, hq, map_zero, zero_mul, map_zero]
  ·
    intro ρ
    have hall := mem_allRad_of_tildeFrob_eq (m := 1) (fun _ _ => (p : (𝓣).RobbaTilde) ^ (N + 1))
      (fun _ _ => pow_mem (natCast_mem _ p) _) (fun _ => z) (fun _ => by simp [hzφ]) 0
    exact mem_allRad.1 hall ρ
  ·
    set ρ0 := rhoMid p
    set ρs : Set.Ioo (0 : ℝ) 1 := ⟨min ((𝓣).edagRad yE) ρ0, lt_min ((𝓣).edagRad yE).2.1 ρ0.2.1,
      min_lt_of_left_lt ((𝓣).edagRad yE).2.2⟩ with hρsdef
    have hρs0 : (ρs : ℝ) ≤ ρ0 := min_le_right _ _
    have hys : y ∈ (𝓣).Econ ρs := (𝓣).Econ_anti (min_le_left _ _) ((𝓣).edagRad_spec yE)
    set ws : (𝓣).RobbaExt ρs := tTildeExt p ε ρs ^ (m + 1) * (𝓣).res hρs0 (fInf P0 ρ0).prod *
      (((⟨y, hys⟩ : (𝓣).Econ ρs)) : (𝓣).RobbaExt ρs) with hwsdef
    have hws : (𝓣).ofRad ρs ws = z := by
      rw [hwsdef, map_mul, map_mul, map_pow, ofRad_tTildeExt hε hζ, (𝓣).ofRad_res, hzdef]
      congr 1
      show (𝓣).econToTilde ρs ⟨y, hys⟩ = Y
      rw [hYdef, ← (𝓣).edagToTilde_apply hys]
    obtain ⟨n, hn⟩ : ∃ n, radSeq P0 n < ρs :=
      ((tendsto_radSeq P0).eventually (gt_mem_nhds ρs.2.1)).exists
    have hdiv : (𝓣).ξExt (ptSeq P0 n).1 ρs ∣ ws := by
      have h1 : (fInf P0 ρ0).part (n + 1) ∣ (fInf P0 ρ0).prod := (fInf P0 ρ0).part_dvd_prod _
      have h2 := map_dvd ((𝓣).res hρs0) h1
      have h3 : (𝓣).normPtExt (ptSeq P0 n).2 ρs ∣ (𝓣).res hρs0 ((fInf P0 ρ0).part (n + 1)) := by
        simp only [InfProd.part]
        rw [_root_.map_prod]
        refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.self_mem_range_succ n))
        rw [fInf_g, res_normPtExt]
      have h4 := ((𝓣).dvd_ξExt_iff_normPtExt (ptSeq P0 n).2 _).2 (h3.trans h2)
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h4 _) _
    have key : ∀ (k : ℕ) (ρ : Set.Ioo (0 : ℝ) 1) (w : (𝓣).RobbaExt ρ),
        (𝓣).ptRad (ptSeq P0 k).1 < ρ → (𝓣).ofRad ρ w = z → (𝓣).ξExt (ptSeq P0 k).1 ρ ∣ w →
        ∃ (ρ' : Set.Ioo (0 : ℝ) 1) (w' : (𝓣).RobbaExt ρ'),
          (𝓣).ptRad ξ' < ρ' ∧ (𝓣).ofRad ρ' w' = z ∧ (𝓣).ξExt ξ' ρ' ∣ w' := by
      intro k
      induction k with
      | zero => intro ρ w h1 h2 h3; exact ⟨ρ, w, h1, h2, h3⟩
      | succ k ih =>
        intro ρ w h1 h2 h3
        rw [ptSeq_succ] at h1 h3
        set Q := ptSeq P0 k
        refine ih ((frob ℂ_[p] p).rootRadius ρ)
          ((p : (𝓣).RobbaExt _) ^ (N + 1) * (frob ℂ_[p] p).extFrobSymm ρ w) ?_ ?_ ?_
        · rw [rootRadius_coe]
          rw [ptRad_frobPt] at h1
          have hq0 := ((𝓣).ptRad_pos' Q.2).le
          calc (𝓣).ptRad Q.1 = ((𝓣).ptRad Q.1 ^ p) ^ ((p : ℝ)⁻¹) :=
                (Real.pow_rpow_inv_natCast hq0 hp.out.ne_zero).symm
            _ < (ρ : ℝ) ^ ((p : ℝ)⁻¹) :=
                Real.rpow_lt_rpow (pow_nonneg hq0 _) h1 (inv_pos.2 (Nat.cast_pos.2 hp.out.pos))
        · rw [map_mul, map_pow, map_natCast, ← (frob ℂ_[p] p).tildeFrobSymm_ofRad, h2, hzsymm]
        · obtain ⟨v, hv⟩ := h3
          refine Dvd.intro ((p : (𝓣).RobbaExt _) ^ (N + 1) * (frob ℂ_[p] p).extFrobSymm ρ v) ?_
          rw [hv, map_mul, ξExt_extFrobSymm Q ρ]
          ring
    obtain ⟨ρ', w', hρ', hw', hdw'⟩ := key n ρs ws (by rw [ptRad_ptSeq]; exact hn) hws hdiv
    intro ρ hρ w hw
    have hev' : (𝓣).ptEval hξ' hρ'.le w' = 0 := by
      obtain ⟨v, rfl⟩ := hdw'
      rw [map_mul, (𝓣).ptEval_ξExt, zero_mul]
    set μ : Set.Ioo (0 : ℝ) 1 := ⟨min ρ ρ', lt_min ρ.2.1 ρ'.2.1, min_lt_of_left_lt ρ.2.2⟩
    have hμ : (𝓣).ptRad ξ' ≤ μ := le_min hρ.le hρ'.le
    have hμρ : (μ : ℝ) ≤ ρ := min_le_left _ _
    have hμρ' : (μ : ℝ) ≤ ρ' := min_le_right _ _
    have heq : (𝓣).res hμρ w = (𝓣).res hμρ' w' :=
      (𝓣).ofRad_injective μ (by rw [(𝓣).ofRad_res, (𝓣).ofRad_res, hw, hw'])
    rw [← (𝓣).ptEval_res hξ' hμρ hμ w, heq, (𝓣).ptEval_res hξ' hμρ' hμ w', hev']

end WAFrac

end GroundTheory.PAdicHodge
