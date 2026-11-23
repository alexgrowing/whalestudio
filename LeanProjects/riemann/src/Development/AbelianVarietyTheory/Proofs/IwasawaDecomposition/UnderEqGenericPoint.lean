import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ChartGlue GlobalTheory.ArInt

namespace GlobalTheory.TwistTop

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k}

structure Refines (N L : HermLB p) (π : N.B.ι → L.B.ι) (s : (k →+* ℂ) → ℝ) : Prop where
  le : ∀ c, N.B.U c ≤ L.B.U (π c)
  g : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) c c', r z ∈ N.B.U c → r z ∈ N.B.U c' →
    gm r z (N.B.U c ⊓ N.B.U c') (N.B.g c c') = gm r z (L.B.U (π c) ⊓ L.B.U (π c')) (L.B.g (π c) (π c'))
  φ : ∀ σ c, ∀ y ∈ ptsIn p σ (N.B.U c), (N.φ σ).φ c y = (L.φ σ).φ (π c) y + s σ

structure Const (T : HermLB p) (s : (k →+* ℂ) → ℝ) : Prop where
  g : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) c c', r z ∈ T.B.U c → r z ∈ T.B.U c' →
    gm r z (T.B.U c ⊓ T.B.U c') (T.B.g c c') = 1
  φ : ∀ σ c, ∀ y ∈ ptsIn p σ (T.B.U c), (T.φ σ).φ c y = s σ

variable {N L T T' : HermLB p} {π : N.B.ι → L.B.ι} {s s' : (k →+* ℂ) → ℝ}

theorem Refines.pull (h : Refines N L π s) {q : Y ⟶ Sp k} (f : Y ⟶ X) (hf : f ≫ p = q) :
    Refines (N.pull f hf) (L.pull f hf) (fun c a => π (c a)) s where
  le c y hy := mem_iInter.2 fun a => h.le _ (mem_iInter.1 hy a)
  g Z r z c c' hc hc' := (gm_pull_g _ f r z c c' hc hc').trans
    ((h.g Z (r ≫ f) z _ _ (mem_iInter.1 hc PUnit.unit) (mem_iInter.1 hc' PUnit.unit)).trans
      (gm_pull_g _ f r z (fun a => π (c a)) (fun a => π (c' a))
        (mem_iInter.2 fun a => h.le _ (mem_iInter.1 hc a))
        (mem_iInter.2 fun a => h.le _ (mem_iInter.1 hc' a))).symm)
  φ σ c y hy := ((N.φ σ).pull_φ f hf c y).trans ((h.φ σ _ _
    (mem_of_mem_linComb (m := fun _ => Points.PtsOver.map f hf _ y) (fun _ => rfl) hy PUnit.unit)).trans
      (congrArg (· + _) ((L.φ σ).pull_φ f hf (fun a => π (c a)) y).symm))

theorem gm_pow (L : HermLB p) (m : ℕ) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (c c' : (L.pow m).B.ι)
    (hc : r z ∈ (L.pow m).B.U c) (hc' : r z ∈ (L.pow m).B.U c') :
    gm r z ((L.pow m).B.U c ⊓ (L.pow m).B.U c') ((L.pow m).B.g c c') =
      gm r z _ (L.B.g (c PUnit.unit) (c' PUnit.unit)) ^ m :=
  (gm_linComb L.B (K := PUnit) (fun _ => 𝟙 X) (fun _ => (m : ℤ)) r z c c' hc hc').trans (by
    rw [Fintype.prod_unique, zpow_natCast, Category.comp_id])

theorem Refines.pow (h : Refines N L π 0) (m : ℕ) :
    Refines (N.pow m) (L.pow m) (fun c a => π (c a)) 0 where
  le c y hy := mem_iInter.2 fun a => h.le _ (mem_iInter.1 hy a)
  g Z r z c c' hc hc' := (gm_pow N m r z c c' hc hc').trans
    ((congrArg (· ^ m) (h.g Z r z _ _ (mem_iInter.1 hc PUnit.unit) (mem_iInter.1 hc' PUnit.unit))).trans
      (gm_pow L m r z (fun a => π (c a)) (fun a => π (c' a))
        (mem_iInter.2 fun a => h.le _ (mem_iInter.1 hc a))
        (mem_iInter.2 fun a => h.le _ (mem_iInter.1 hc' a))).symm)
  φ σ c y hy := ((N.φ σ).zpow_φ m c y).trans ((congrArg _ ((h.φ σ _ _ (mem_pow_iff.1 hy)).trans (add_zero _))).trans
      (((L.φ σ).zpow_φ m (fun a => π (c a)) y).symm.trans (add_zero _).symm))

theorem Refines.shift (h : Refines N L π fun σ => 2 * s σ) (hs : ∀ σ, s ((starRingEnd ℂ).comp σ) = s σ) :
    Refines N (L.shift s hs) π 0 :=
  ⟨h.le, h.g, fun σ c y hy => (h.φ σ c y hy).trans (add_zero _).symm⟩

theorem Refines.lbIso (h : Refines N L π s) : LBIso N.B L.B :=
  iso_of_chart L.isLB ⟨π, h.le, h.g X (𝟙 X)⟩

theorem Refines.chernPart (h : Refines N L π s) (σ : k →+* ℂ) (D : ℕ) (ε : ℤˣ) :
    (N.φ σ).chernPart D ε = (L.φ σ).chernPart D ε := by
  refine iSup_congr fun c => congrArg (Measure.map _) (withDensity_congr_ae ?_)
  filter_upwards [ae_restrict_mem c.e.open_target.measurableSet] with v hv
  have hy := c.e.map_target hv
  have hi := mem_pick N.isLB (c.e.symm v)
  simp only [Function.comp_apply]
  rw [c.chernDens_eq (N.cInf σ) hy hi, c.chernDens_eq (L.cInf σ) hy (ptsIn_mono (h.le _) hi), AlgChart.hess,
    AlgChart.hess, ← ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_add_const
      (fun w => ((L.φ σ).φ (π (pick N.isLB (c.e.symm v))) (c.e.symm w) : ℂ)) (s σ)]
  congr 5
  refine ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_
  filter_upwards [(isOpen_over c.e (isOpen_ptsIn _)).mem_nhds (mem_over c.e hy hi)] with w hw
  rw [h.φ σ _ _ hw.2, Complex.ofReal_add]

theorem Refines.chernInt (h : Refines N L π s) (σ : k →+* ℂ) (D : ℕ) (S : Set (CxPts p σ)) (f : CxPts p σ → ℝ) :
    (N.φ σ).chernInt D S f = (L.φ σ).chernInt D S f := by
  simp only [Weight.chernInt, h.chernPart]

section Rat

variable [IsIntegral X] {r : L.B.ι → X.functionFieldˣ}

theorem Refines.isRatSec (h : Refines N L π s) (hr : IsRatSec L.B r) : IsRatSec N.B fun c => r (π c) :=
  fun c c' hc => by
  have h' : genericPoint X ∈ L.B.U (π c) ⊓ L.B.U (π c') := ⟨h.le _ hc.1, h.le _ hc.2⟩
  have e := congrArg Units.val (h.g X (𝟙 X) _ c c' hc.1 hc.2)
  rw [gm_val _ _ _ hc, gm_val _ _ _ h'] at e
  exact (hr _ _ h').trans (congrArg (· * _) e.symm)

theorem Refines.div (h : Refines N L π s) (hr : IsRatSec L.B r) : N.div (h.isRatSec hr) = L.div hr :=
  CartierDiv.ext_of_isEqn fun z =>
    have ⟨i, hi⟩ := exists_chart N.isLB z
    ⟨r (π i), (presents_divOfRatSec _ (h.isRatSec hr)).isEqn i z hi,
      (presents_divOfRatSec _ hr).isEqn _ z (h.le _ hi)⟩

theorem Refines.logNorm (h : Refines N L π 0) (hr : IsRatSec L.B r) {σ : k →+* ℂ} {y : CxPts p σ}
    (hy : y ∈ offSupp p σ (L.div hr)) : logNorm (N.φ σ) (fun c => r (π c)) y = logNorm (L.φ σ) r y := by
  have hi := mem_pick N.isLB y
  rw [logNorm_eq (L.φ σ) hr hy (ptsIn_mono (h.le _) hi), Cartier.logNorm, h.φ σ _ y hi, Pi.zero_apply, add_zero]

theorem under_eq_genericPoint (hX : IsArithVar p 0) {σ : k →+* ℂ} (y : CxPts p σ) : under y = genericPoint X := by
  by_contra hne
  have hd : Order.krullDim (IrreducibleCloseds X) ≤ 1 := hX.dim_eq.le
  have hcl : IsClosed {under y} := by
    rcases Order.krullDim_le_one_iff.1 hd ⟨closure {under y}, isIrreducible_singleton.closure, isClosed_closure⟩
      with h | h
    · rw [← closure_subset_iff_isClosed]
      intro w hw
      have := @h ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
        (closure_minimal (singleton_subset_iff.2 hw) isClosed_closure)
      exact ((specializes_iff_mem_closure.2 (this (subset_closure rfl))).antisymm
        (specializes_iff_mem_closure.2 hw)).eq
    · exact absurd (IsGenericPoint.eq (eq_univ_of_univ_subset (@h
        ⟨univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ (subset_univ _))) (genericPoint_spec X)) hne
  have := hX.finite_residueField hcl
  have := (Scheme.descResidueField (Scheme.stalkClosedPointTo y.1)).hom.charZero
  exact not_finite (X.residueField (under y))

end Rat

theorem Refines.isArithHeight {D : ℕ} (hX : IsArithVar p D) (h : Refines N L π 0) {f : X → ℝ}
    (H : N.IsArithHeight f) : L.IsArithHeight f where
  vertical Z i _ _ κ _ _ _ d hd := (H.vertical Z i κ d hd).trans (congrArg (fun n : ℤ => (n : ℝ) * _)
    (topSelf_congr κ (N.restr i).isLB (L.restr i).isLB (h.pull i rfl).lbIso d))
  point Z i _ _ _ hc hd r hr := by
    have h' := h.pull i rfl
    rw [H.point Z i hc hd _ (h'.isRatSec hr), HermLB.curveDeg, HermLB.curveDeg, h'.div hr]
    refine congrArg _ (finsum_congr fun σ => finsum_congr fun y => h'.logNorm hr (mem_offSupp.2 ?_))
    rw [under_eq_genericPoint (hX.of_isClosedImmersion i hc hd) y]
    exact CartierDiv.genericPoint_notMem_supp _
  recursion Z i _ _ _ hc e he hd m r hr := by
    have h' := h.pull i rfl
    have h'' := h'.pow m
    obtain ⟨h₁, h₂⟩ := H.recursion Z i hc e he hd m _ (h''.isRatSec hr)
    unfold HermLB.ArchIntegrable Weight.ChernIntegrableOn at h₁
    unfold HermLB.archInt at h₂
    rw [h''.div hr] at h₁ h₂
    simp only [h'.chernPart] at h₁
    refine ⟨fun σ => Weight.ChernIntegrableOn.congr (h₁ σ) (isOpen_offSupp _).measurableSet
      fun y hy => h''.logNorm hr hy, h₂.trans (congrArg _ (finsum_congr fun σ => ?_))⟩
    rw [h'.chernInt]
    exact Weight.chernInt_congr (isOpen_offSupp _).measurableSet fun y hy => h''.logNorm hr hy

theorem Refines.congr (h : Refines N L π s) (e : ∀ σ, s σ = s' σ) : Refines N L π s' := funext e ▸ h

theorem Const.congr (h : Const T s) (e : ∀ σ, s σ = s' σ) : Const T s' := funext e ▸ h

theorem const_triv : Const (HermLB.triv p) 0 :=
  ⟨fun _ _ _ _ _ _ _ => map_one _, fun _ _ _ _ => rfl⟩

theorem Const.pow (h : Const T s) (m : ℕ) : Const (T.pow m) fun σ => m * s σ where
  g Z r z c c' hc hc' := (gm_pow T m r z c c' hc hc').trans (by
    rw [h.g Z r z _ _ (mem_iInter.1 hc PUnit.unit) (mem_iInter.1 hc' PUnit.unit), one_pow])
  φ σ c y hy := ((T.φ σ).zpow_φ m c y).trans (by rw [h.φ σ _ _ (mem_pow_iff.1 hy), Int.cast_natCast])

theorem const_pow_zero (L : HermLB p) : Const (L.pow 0) 0 where
  g Z r z c c' hc hc' := (gm_pow L 0 r z c c' hc hc').trans (pow_zero _)
  φ σ c y _ := ((L.φ σ).zpow_φ (0 : ℕ) c y).trans (by simp)

theorem refines_pow_one (L : HermLB p) : Refines (L.pow 1) L (fun c => c PUnit.unit) 0 where
  le _ _ hy := mem_iInter.1 hy PUnit.unit
  g Z r z c c' hc hc' := (gm_pow L 1 r z c c' hc hc').trans (pow_one _)
  φ σ c y _ := ((L.φ σ).zpow_φ (1 : ℕ) c y).trans (by simp)

theorem Const.dual (h : Const T s) : Const T.dual (-s) where
  g Z r z c c' hc hc' := (map_inv _ _).trans (inv_eq_one.2 (h.g Z r z c c' hc hc'))
  φ σ c y hy := congrArg (- ·) (h.φ σ c y hy)

theorem Const.tens (h : Const T s) (h' : Const T' s') : Const (T.tens T') (s + s') where
  g Z r z c c' hc hc' := (gm_tens _ _ r z c c' hc hc').trans (by
    rw [h.g Z r z _ _ hc.1 hc'.1, h'.g Z r z _ _ hc.2 hc'.2, one_mul])
  φ σ c y hy := congrArg₂ (· + ·) (h.φ σ _ y (mem_ptsIn_inf.1 hy).1) (h'.φ σ _ y (mem_ptsIn_inf.1 hy).2)

theorem Refines.tens_const (h : Refines N L π s) (h' : Const T s') :
    Refines (N.tens T) L (fun c => π c.1) (s + s') where
  le _ := inf_le_left.trans (h.le _)
  g Z r z c c' hc hc' := (gm_tens _ _ r z c c' hc hc').trans (by
    rw [h.g Z r z _ _ hc.1 hc'.1, h'.g Z r z _ _ hc.2 hc'.2, mul_one])
  φ σ c y hy := (congrArg₂ (· + ·) (h.φ σ _ y (mem_ptsIn_inf.1 hy).1)
    (h'.φ σ _ y (mem_ptsIn_inf.1 hy).2)).trans (add_assoc _ _ _)

theorem Const.tens_refines (h' : Const T s') (h : Refines N L π s) :
    Refines (T.tens N) L (fun c => π c.2) (s' + s) where
  le _ := inf_le_right.trans (h.le _)
  g Z r z c c' hc hc' := (gm_tens _ _ r z c c' hc hc').trans (by
    rw [h.g Z r z _ _ hc.2 hc'.2, h'.g Z r z _ _ hc.1 hc'.1, one_mul])
  φ σ c y hy := (congrArg₂ (· + ·) (h'.φ σ _ y (mem_ptsIn_inf.1 hy).1)
    (h.φ σ _ y (mem_ptsIn_inf.1 hy).2)).trans (add_left_comm _ _ _)

theorem Const.zp (h : Const T s) (n : ℤ) : Const (zp T n) fun σ => n * s σ := by
  refine ((h.pow n.toNat).tens (h.pow (-n).toNat).dual).congr fun σ => ?_
  have e : ((n.toNat : ℤ) : ℝ) - (((-n).toNat : ℤ) : ℝ) = n := by exact_mod_cast n.toNat_sub_toNat_neg
  simp only [Int.cast_natCast] at e
  simp only [Pi.add_apply, Pi.neg_apply]
  linear_combination (s σ) * e

theorem exists_refines_zp_one (L : HermLB p) : ∃ π, Refines (zp L 1) L π 0 := by
  have h := (refines_pow_one L).tens_const (const_pow_zero L).dual
  rw [neg_zero, add_zero] at h
  exact ⟨_, h⟩

theorem refines_foldr {κ : Type} (M : κ → HermLB p) (c : κ → (k →+* ℂ) → ℝ) (i₀ : κ)
    (h₀ : ∃ π, Refines (M i₀) L π (c i₀)) (h : ∀ i, i ≠ i₀ → Const (M i) (c i)) (l : List κ) (hl : l.Nodup) :
    (i₀ ∉ l → Const (l.foldr (fun i N => (M i).tens N) (HermLB.triv p)) (l.map c).sum) ∧
    (i₀ ∈ l → ∃ π, Refines (l.foldr (fun i N => (M i).tens N) (HermLB.triv p)) L π (l.map c).sum) := by
  induction l with
  | nil => exact ⟨fun _ => const_triv, fun h => absurd h List.not_mem_nil⟩
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.nodup_cons.1 hl
    obtain ⟨h₁, h₂⟩ := ih hl
    refine ⟨fun hm => (h i fun e => hm (e ▸ List.mem_cons_self)).tens (h₁ fun e => hm (List.mem_cons_of_mem _ e)),
      fun hm => ?_⟩
    by_cases e : i = i₀
    · subst e
      obtain ⟨π, hπ⟩ := h₀
      exact ⟨_, hπ.tens_const (h₁ hi)⟩
    · obtain ⟨π, hπ⟩ := h₂ ((List.mem_cons.1 hm).resolve_left (Ne.symm e))
      exact ⟨_, (h i e).tens_refines hπ⟩

theorem refines_comb {κ : Type} [Fintype κ] (M : κ → HermLB p) (n : κ → ℤ) (i₀ : κ) (h₀ : M i₀ = L) (hn : n i₀ = 1)
    (h : ∀ i, i ≠ i₀ → Const (M i) s) : ∃ π, Refines (comb M n) L π fun σ => (∑ i, n i - 1 : ℤ) * s σ := by
  classical
  obtain ⟨π, hπ⟩ := (refines_foldr (L := L) (fun i => zp (M i) (n i)) (fun i σ => if i = i₀ then 0 else n i * s σ) i₀
    (by rw [h₀, hn]; exact (exists_refines_zp_one L).imp fun _ h => h.congr fun σ => (if_pos rfl).symm)
    (fun i hi => by simpa only [if_neg hi] using (h i hi).zp (n i)) _ (Finset.nodup_toList Finset.univ)).2
    (Finset.mem_toList.2 (Finset.mem_univ _))
  refine ⟨π, hπ.congr fun σ => Eq.symm ?_⟩
  rw [Finset.sum_map_toList, Finset.sum_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), if_pos rfl, hn, zero_add, add_sub_cancel_left, Int.cast_sum,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun i hi => (if_neg (Finset.ne_of_mem_erase hi)).symm

open Polynomial in

theorem step_of_linear {R : Type*} [CommRing R] [Algebra ℝ R] (Φ : R →ₗ[ℝ] ℝ) (x y z : R) (D : ℕ) (G : ℤ → ℝ) (c : ℝ)
    (hG : ∀ a b : ℤ, Φ (((a : ℝ) • x + ((b : ℝ) • y + z)) ^ (D + 1)) = G (a + b))
    (hc : ∀ b : ℤ, Φ (x * ((b : ℝ) • y + z) ^ D) = c) : G 1 = G 0 + (D + 1) * c := by
  let P (b : ℤ) : ℝ[X] := ∑ j ∈ Finset.range (D + 1 + 1),
    monomial j (((D + 1).choose j : ℝ) * Φ (x ^ j * ((b : ℝ) • y + z) ^ (D + 1 - j)))
  have hinf : (Set.range (Int.cast : ℤ → ℝ)).Infinite := Set.infinite_range_of_injective Int.cast_injective
  have h₁ (a b : ℤ) : (P b).eval (a : ℝ) = G (a + b) := by
    rw [← hG, add_pow, map_sum, eval_finset_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval_monomial, _root_.smul_pow, mul_comm _ ((D + 1).choose j : R), ← nsmul_eq_mul (α := R), map_nsmul, smul_mul_assoc,
      map_smul, nsmul_eq_mul, smul_eq_mul]
    ring
  have h₂ (b : ℤ) : (P b).coeff 1 = (D + 1) * c := by
    rw [finset_sum_coeff, Finset.sum_eq_single 1 (fun j _ hj => by rw [coeff_monomial, if_neg hj]) (by simp),
      coeff_monomial_same, pow_one, Nat.add_sub_cancel, hc, Nat.choose_one_right, Nat.cast_succ]
  have h₃ (b : ℤ) : P b = taylor (b : ℝ) (P 0) := eq_of_infinite_eval_eq _ _ (hinf.mono (by
    rintro _ ⟨a, rfl⟩
    rw [Set.mem_setOf_eq, taylor_eval, h₁, ← Int.cast_add, h₁, add_zero]))
  have h₄ : derivative (P 0 - C ((D + 1) * c) * X) = 0 := eq_of_infinite_eval_eq _ _ (hinf.mono (by
    rintro _ ⟨b, rfl⟩
    have := h₂ b
    rw [h₃, taylor_coeff_one] at this
    simp [this]))
  have h₅ := eq_C_of_derivative_eq_zero h₄
  have e₀ := congrArg (eval ((0 : ℤ) : ℝ)) h₅
  have e₁ := congrArg (eval ((1 : ℤ) : ℝ)) h₅
  rw [eval_sub, h₁, eval_C, eval_mul, eval_C, eval_X] at e₀ e₁
  simp only [add_zero, Int.cast_zero, Int.cast_one] at e₀ e₁
  linarith

theorem isSelfInter_shift : GlobalTheory.Published.ArExists → GlobalTheory.Published.ArChange → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (a : ℝ) (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ), L.IsSelfInter a → (L.shift t ht).IsSelfInter (a + ((D : ℝ) + 1) * ∑ᶠ σ, t σ * (L.φ σ).chernInt D Set.univ (fun _ => 1)) := by
  intro hE hC k _ X _ p D hX L a t ht ha
  have hu (σ : k →+* ℂ) (y : CxPts p σ) : CInfAt (fun _ => 2 * t σ) y := cInfAt_const _ y
  have hc (σ σ' : k →+* ℂ) : (Weight.ofFun (p := p) (σ := σ) fun _ => 2 * t σ).IsConj
      (Weight.ofFun (σ := σ') fun _ => 2 * t σ') := fun _ y y' h _ =>
    congrArg (2 * ·) ((congrArg t (eq_conj_of_conj h)).trans (ht σ))
  let T := fnB (fun σ _ => 2 * t σ) hu hc
  have hT : Const T fun σ => 2 * t σ := ⟨fun _ _ _ _ _ _ _ => map_one _, fun _ _ _ _ => rfl⟩
  let M : Option Unit → HermLB p := fun o => o.elim T fun _ => L
  obtain ⟨Φ, hΦ⟩ := ((hE k X p D hX).2 _ fun o : Option (Option Unit) => o.elim T M).1
  have hs (n : ℤ) (σ) : n * t ((starRingEnd ℂ).comp σ) = n * t σ := congrArg _ (ht σ)
  choose f hf using fun n : ℤ => (hE k X p D hX).1 (L.shift (fun σ => n * t σ) (hs n))
  have key := step_of_linear Φ (MvPolynomial.X none) (MvPolynomial.X (some none)) (MvPolynomial.X (some (some ()))) D
    (fun n => f n (genericPoint X)) (∑ᶠ σ, t σ * (L.φ σ).chernInt D Set.univ (fun _ => 1)) (fun a b => by
      let n : Option (Option Unit) → ℤ := fun o => o.elim a fun o => o.elim b fun _ => 1
      obtain ⟨π, hπ⟩ := refines_comb (fun o : Option (Option Unit) => o.elim T M) n (some (some ())) rfl rfl
        (s := fun σ => 2 * t σ) (by rintro (_ | _ | _) h; exacts [hT, hT, absurd rfl h])
      obtain ⟨g, hg, e⟩ := hΦ.1 n
      have hπ' : Refines _ L π fun σ => 2 * (((a + b : ℤ) : ℝ) * t σ) := by
        refine hπ.congr fun σ => ?_
        simp [n, Fintype.sum_option]
        ring
      rw [← ((hπ'.shift (hs _)).isArithHeight hX hg).unique hX (hf _), e]
      simp [lin, n, Fintype.sum_option, MvPolynomial.smul_eq_C_mul]) (fun b => by
      let n : Option Unit → ℤ := fun o => o.elim b fun _ => 1
      obtain ⟨π, hπ⟩ := refines_comb (L := L) M n (some ()) rfl rfl
        (s := fun σ => 2 * t σ) (by rintro (_ | _) h; exacts [hT, absurd rfl h])
      have e := hC k X p D hX _ M _ hu hc Φ hΦ n
      rw [chInt, mul_finsum] at e
      refine Eq.trans ?_ (e.trans (finsum_congr fun σ => ?_))
      · simp [lin, n, Fintype.sum_option, MvPolynomial.smul_eq_C_mul]
      · rw [hπ.chernInt, ← mul_one (2 * t σ), Weight.chernInt_const_mul]
        ring)
  have hid (s : (k →+* ℂ) → ℝ) (hs) : Refines (L.shift s hs) L id fun σ => 2 * s σ :=
    ⟨fun _ => le_rfl, fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  have h₀ : L.IsArithHeight (f 0) :=
    ((hid (fun σ => (0 : ℤ) * t σ) (hs 0)).congr fun σ => by simp).isArithHeight hX (hf 0)
  have h₁ : (L.shift t ht).IsArithHeight (f 1) :=
    (((hid (fun σ => (1 : ℤ) * t σ) (hs 1)).congr fun σ => by simp).shift ht).isArithHeight hX (hf 1)
  exact ⟨_, h₁, key.trans (congrArg (· + _) (HermLB.IsSelfInter.unique hX ⟨_, h₀, rfl⟩ ha))⟩

end GlobalTheory.TwistTop
