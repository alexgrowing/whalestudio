import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnectionDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeWedgeAnticomm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SgnInsertOfNotMemNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrPullOperatorEq
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsionForm.OneVec.CurvPull

section Lin
variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem fderiv_cplx (D : V →L[ℝ] W) (c : ℂ) (w : V) :
    D (c • w) = (c.re : ℂ) • D w + (c.im : ℂ) • D (Complex.I • w) := by
  have hc : c • w = c.re • w + c.im • (Complex.I • w) := by
    conv_lhs => rw [← Complex.re_add_im c]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  rw [hc, map_add, map_smul, map_smul, Complex.coe_smul, Complex.coe_smul]

theorem dz_add_vector (f : V → W) (P v w : V) : d10 f P (v + w) = d10 f P v + d10 f P w := by
  unfold d10; simp only [smul_add, map_add]; module

theorem d10_smul (f : V → W) (P v : V) (c : ℂ) : d10 f P (c • v) = c • d10 f P v := by
  unfold d10
  rw [smul_smul, fderiv_cplx _ c v, fderiv_cplx _ (Complex.I * c) v]
  have e1 : (Complex.I * c).re = - c.im := by simp
  have e2 : (Complex.I * c).im = c.re := by simp
  rw [e1, e2]
  conv_rhs => rw [← Complex.re_add_im c]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem dbar_add_vector (f : V → W) (P v w : V) : d01 f P (v + w) = d01 f P v + d01 f P w := by
  unfold d01; simp only [smul_add, map_add]; module

theorem d01_smul (f : V → W) (P v : V) (c : ℂ) : d01 f P (c • v) = star c • d01 f P v := by
  unfold d01
  rw [smul_smul, fderiv_cplx _ c v, fderiv_cplx _ (Complex.I * c) v]
  have e1 : (Complex.I * c).re = - c.im := by simp
  have e2 : (Complex.I * c).im = c.re := by simp
  rw [e1, e2]
  conv_rhs => rw [← Complex.re_add_im c]
  simp only [star_add, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

end Lin

section Lin2
variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

def d10Linear (f : V → W) (P : V) : V →ₗ[ℂ] W where
  toFun := d10 f P
  map_add' := dz_add_vector f P
  map_smul' := fun c v => d10_smul f P v c

def d01ConjLinear (f : V → W) (P : V) : V →ₗ⋆[ℂ] W where
  toFun := d01 f P
  map_add' := dbar_add_vector f P
  map_smul' := fun c v => d01_smul f P v c

theorem d10_finset_sum' {n : ℕ} (f : V → W) (P : V) (a : Fin n → ℂ) (v : Fin n → V) :
    d10 f P (∑ i, a i • v i) = ∑ i, a i • d10 f P (v i) := by
  show d10Linear f P _ = _
  rw [map_sum]; simp only [map_smul]; rfl

theorem d01_sum {n : ℕ} (f : V → W) (P : V) (a : Fin n → ℂ) (v : Fin n → V) :
    d01 f P (∑ i, a i • v i) = ∑ i, star (a i) • d01 f P (v i) := by
  show d01ConjLinear f P _ = _
  rw [map_sum]; simp only [map_smulₛₗ]; rfl

theorem d10_comp_continuousLinearMap {m m' : ℕ} (L : Ext m →L[ℂ] Ext m') (s : V → Ext m) (P v : V)
    (hs : DifferentiableAt ℝ s P) : d10 (fun Q => L (s Q)) P v = L (d10 s P v) := by
  have hd : fderiv ℝ (fun Q => L (s Q)) P = (L.restrictScalars ℝ).comp (fderiv ℝ s P) :=
    ((L.restrictScalars ℝ).hasFDerivAt.comp P hs.hasFDerivAt).fderiv
  unfold d10; rw [hd]; simp [map_sub, map_smul]

theorem d01_comp_continuousLinearMap {m m' : ℕ} (L : Ext m →L[ℂ] Ext m') (s : V → Ext m) (P v : V)
    (hs : DifferentiableAt ℝ s P) : d01 (fun Q => L (s Q)) P v = L (d01 s P v) := by
  have hd : fderiv ℝ (fun Q => L (s Q)) P = (L.restrictScalars ℝ).comp (fderiv ℝ s P) :=
    ((L.restrictScalars ℝ).hasFDerivAt.comp P hs.hasFDerivAt).fderiv
  unfold d01; rw [hd]; simp [map_add, map_smul]

end Lin2

section Ops
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

theorem hor_sum {n : ℕ} (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) (a : Fin n → ℂ) (β : Fin n → E) :
    hor τ P (∑ i, a i • β i) = ∑ i, a i • hor τ P (β i) := by
  unfold hor
  ext1
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum, map_sum, map_smul]

theorem nab10_sum {m n : ℕ} (h : Pt E g → ℝ) (s : Pt E g → Ext (m + m + g)) (P : Pt E g) (a : Fin n → ℂ)
    (v : Fin n → Pt E g) : pointDifference h s P (∑ i, a i • v i) = ∑ i, a i • pointDifference h s P (v i) := by
  unfold pointDifference
  rw [d10_finset_sum', d10_finset_sum', Finset.sum_smul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_add, smul_smul, smul_eq_mul]

theorem nab10_comp {m m' : ℕ} (h : Pt E g → ℝ) (L : Ext (m + m + g) →L[ℂ] Ext (m' + m' + g))
    (s : Pt E g → Ext (m + m + g)) (P v : Pt E g) (hs : DifferentiableAt ℝ s P) :
    pointDifference h (fun Q => L (s Q)) P v = L (pointDifference h s P v) := by
  unfold pointDifference; rw [d10_comp_continuousLinearMap L s P v hs, map_add, map_smul]

theorem wedge_smul' {m : ℕ} (i : Fin m) (c : ℂ) (w : Ext m) : wedge i (c • w) = c • wedge i w :=
  (wedgeL i).map_smul c w

theorem wedge_neg' {m : ℕ} (i : Fin m) (w : Ext m) : wedge i (-w) = -wedge i w :=
  (wedgeL i).map_neg w

theorem wedge_sum' {m : ℕ} (i : Fin m) {ι : Type} (s : Finset ι) (f : ι → Ext m) :
    wedge i (∑ k ∈ s, f k) = ∑ k ∈ s, wedge i (f k) :=
  map_sum (wedgeL i) f s

def contrL {m : ℕ} (i : Fin m) : Ext m →L[ℂ] Ext m :=
  LinearMap.toContinuousLinearMap
    { toFun := contr i
      map_add' := fun x y => by funext S; simp only [contr, Pi.add_apply]; split_ifs <;> ring
      map_smul' := fun c x => by
        funext S; simp only [contr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring }

theorem contr_smul' {m : ℕ} (i : Fin m) (c : ℂ) (w : Ext m) : contr i (c • w) = c • contr i w :=
  (contrL i).map_smul c w

theorem connForm_sum {n m : ℕ} (τ : E → Matrix (Fin g) (Fin g) ℂ) (b : E) (a : Fin n → ℂ)
    (β : Fin n → E) (w : Ext (m + m + g)) :
    connForm τ b (∑ i, a i • β i) w = ∑ i, star (a i) • connForm τ b (β i) w := by
  unfold connForm
  simp only [d01_sum, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul, Finset.sum_smul,
    Finset.smul_sum, smul_smul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul, mul_assoc]

end Ops

section JoinLemmas
open GlobalTheory.TorsionForm.OneVec.StrPull

theorem filter_castAdd_join {m g : ℕ} (k : Fin m) (S : Finset (Fin m)) (I : Finset (Fin g)) :
    (join S I).filter (· < Fin.castAdd g k) = join (S.filter (· < k)) ∅ := by
  ext x
  refine Fin.addCases (fun i => ?_) (fun c => ?_) x
  · simp only [Finset.mem_filter, mem_join_castAdd]
    exact and_congr_right fun _ => by rw [Fin.lt_def, Fin.lt_def]; simp
  · simp only [Finset.mem_filter, mem_join_natAdd]
    simp only [Finset.notMem_empty, iff_false, not_and]
    intro _ h
    simp [Fin.lt_iff_val_lt_val] at h
    omega

theorem filter_natAdd_join {m g : ℕ} (c : Fin g) (S : Finset (Fin m)) (I : Finset (Fin g)) :
    (join S I).filter (· < Fin.natAdd m c) = join S (I.filter (· < c)) := by
  ext x
  refine Fin.addCases (fun i => ?_) (fun c' => ?_) x
  · simp only [Finset.mem_filter, mem_join_castAdd, and_iff_left_iff_imp]
    intro _
    simp [Fin.lt_iff_val_lt_val]
    omega
  · simp only [Finset.mem_filter, mem_join_natAdd]
    exact and_congr_right fun _ => by rw [Fin.lt_def, Fin.lt_def]; simp

theorem card_join {m g : ℕ} (S : Finset (Fin m)) (I : Finset (Fin g)) :
    (join S I).card = S.card + I.card := by
  unfold join
  rw [Finset.card_union_of_disjoint, Finset.card_map, Finset.card_map]
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_map] at hx hx'
  obtain ⟨i, _, rfl⟩ := hx
  obtain ⟨c, _, h⟩ := hx'
  have := congrArg Fin.val h
  simp at this
  omega

theorem erase_castAdd_join {m g : ℕ} (k : Fin m) (S : Finset (Fin m)) (I : Finset (Fin g)) :
    (join S I).erase (Fin.castAdd g k) = join (S.erase k) I := by
  ext x
  refine Fin.addCases (fun i => ?_) (fun c => ?_) x
  · simp only [Finset.mem_erase, mem_join_castAdd]
    simp [Fin.ext_iff]
  · simp only [Finset.mem_erase, mem_join_natAdd, and_iff_right_iff_imp]
    intro _ h
    have := congrArg Fin.val h
    simp at this
    omega

theorem erase_natAdd_join {m g : ℕ} (c : Fin g) (S : Finset (Fin m)) (I : Finset (Fin g)) :
    (join S I).erase (Fin.natAdd m c) = join S (I.erase c) := by
  ext x
  refine Fin.addCases (fun i => ?_) (fun c' => ?_) x
  · simp only [Finset.mem_erase, mem_join_castAdd, and_iff_right_iff_imp]
    intro _ h
    have := congrArg Fin.val h
    simp at this
    omega
  · simp only [Finset.mem_erase, mem_join_natAdd]
    simp [Fin.ext_iff]

theorem insert_natAdd_join {m g : ℕ} (c : Fin g) (S : Finset (Fin m)) (I : Finset (Fin g)) :
    insert (Fin.natAdd m c) (join S I) = join S (insert c I) := by
  ext x
  refine Fin.addCases (fun i => ?_) (fun c' => ?_) x
  · simp only [Finset.mem_insert, mem_join_castAdd, or_iff_right_iff_imp]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  · simp only [Finset.mem_insert, mem_join_natAdd]
    simp [Fin.ext_iff]

theorem wedge_castAdd_join {m g : ℕ} (k : Fin m) (x : Ext (m + g)) (S : Finset (Fin m))
    (I : Finset (Fin g)) : wedge (Fin.castAdd g k) x (join S I) = wedge k (fun S' => x (join S' I)) S := by
  have hs : sgn (Fin.castAdd g k) (join S I) = sgn k S := by
    unfold sgn; rw [filter_castAdd_join, card_join]; simp
  simp only [wedge, mem_join_castAdd, hs, erase_castAdd_join]

theorem sgn_natAdd_join {m g : ℕ} (c : Fin g) (S : Finset (Fin m)) (I : Finset (Fin g)) :
    sgn (Fin.natAdd m c) (join S I) = (-1) ^ S.card * sgn c I := by
  unfold sgn; rw [filter_natAdd_join, card_join, pow_add]

theorem wedge_natAdd_join {m g : ℕ} (c : Fin g) (x : Ext (m + g)) (S : Finset (Fin m))
    (I : Finset (Fin g)) :
    wedge (Fin.natAdd m c) x (join S I) = (-1) ^ S.card * wedge c (fun I' => x (join S I')) I := by
  simp only [wedge, mem_join_natAdd, sgn_natAdd_join, erase_natAdd_join]
  split_ifs <;> ring

theorem contr_natAdd_join {m g : ℕ} (c : Fin g) (x : Ext (m + g)) (S : Finset (Fin m))
    (I : Finset (Fin g)) :
    contr (Fin.natAdd m c) x (join S I) = (-1) ^ S.card * contr c (fun I' => x (join S I')) I := by
  simp only [contr, mem_join_natAdd, sgn_natAdd_join, insert_natAdd_join]
  split_ifs <;> ring

end JoinLemmas

section Coord
open GlobalTheory.TorsionForm.OneVec.StrPull

theorem finset_fin_two_eq_cases (S : Finset (Fin (1 + 1))) :
    S = ∅ ∨ S = {Fin.castAdd 1 (0 : Fin 1)} ∨ S = {Fin.natAdd 1 (0 : Fin 1)} ∨ S = Finset.univ := by
  revert S; decide

theorem fin_two_finset_facts : (Finset.univ : Finset (Fin (1 + 1))) ≠ {0} ∧ (Finset.univ : Finset (Fin (1 + 1))) ≠ {1} ∧
    (Finset.univ : Finset (Fin (1 + 1))).erase 0 = {1} ∧ (Finset.univ : Finset (Fin (1 + 1))).erase 1 = {0} ∧
    (Finset.univ.filter (fun x : Fin (1 + 1) => x = 0)).card = 1 ∧
    (({1} : Finset (Fin (1 + 1))).filter (fun x => x = 0)).card = 0 ∧
    ({0} : Finset (Fin (1 + 1))) ≠ {1} ∧ ({1} : Finset (Fin (1 + 1))) ≠ {0} := by decide

theorem castAdd_ne_addNat {n : ℕ} (i k : Fin n) : Fin.castAdd n i ≠ k.addNat n := fun h => by
  have := congrArg Fin.val h; simp at this; omega

theorem addNat_ne_castAdd {n : ℕ} (i k : Fin n) : k.addNat n ≠ Fin.castAdd n i := fun h =>
  castAdd_ne_addNat i k h.symm

theorem castAdd_lt_addNat {n : ℕ} (i k : Fin n) : Fin.castAdd n i < k.addNat n := by
  rw [Fin.lt_def]; simp; omega

theorem not_addNat_lt_castAdd {n : ℕ} (i k : Fin n) : ¬ k.addNat n < Fin.castAdd n i :=
  not_lt.2 (castAdd_lt_addNat i k).le

theorem pullBase_sign {n : ℕ} (a : Fin n → ℂ) (y : Ext (n + n)) (S : Finset (Fin (1 + 1))) :
    pullBase a (fun S' => (-1) ^ S'.card * y S') S = (-1) ^ S.card * pullBase a y S := by
  obtain ⟨f1, f2, -, -, -, -, -, -⟩ := fin_two_finset_facts
  rcases finset_fin_two_eq_cases S with rfl | rfl | rfl | rfl
  · simp [pullBase]
  · simp [pullBase, Finset.mul_sum]
  · simp [pullBase, Finset.mul_sum]
  · simp [pullBase, f1, f2, Finset.card_pair (castAdd_ne_addNat _ _)]

theorem pullBase_wedge_castAdd {n : ℕ} (a : Fin n → ℂ) (i : Fin n) (y : Ext (n + n)) :
    pullBase a (wedge (Fin.castAdd n i) y) = a i • wedge (Fin.castAdd 1 (0 : Fin 1)) (pullBase a y) := by
  funext S
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := fin_two_finset_facts
  rcases finset_fin_two_eq_cases S with rfl | rfl | rfl | rfl
  · simp [pullBase, wedge]
  · simp [pullBase, wedge, sgn, Finset.filter_singleton]
  · simp [pullBase, wedge, sgn, Finset.filter_singleton, castAdd_ne_addNat]
  · simp [pullBase, wedge, sgn, Finset.filter_singleton, Finset.filter_insert, castAdd_ne_addNat,
      not_addNat_lt_castAdd, f1, f2, f3, f7, Finset.mul_sum, Finset.erase_insert_eq_erase,
      Finset.erase_singleton]
    rw [if_neg (by decide)]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem pullBase_wedge_natAdd {n : ℕ} (a : Fin n → ℂ) (i : Fin n) (y : Ext (n + n)) :
    pullBase a (wedge (Fin.natAdd n i) y) = star (a i) • wedge (Fin.natAdd 1 (0 : Fin 1)) (pullBase a y) := by
  funext S
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := fin_two_finset_facts
  rcases finset_fin_two_eq_cases S with rfl | rfl | rfl | rfl
  · simp [pullBase, wedge]
  · simp [pullBase, wedge, sgn, Finset.filter_singleton, addNat_ne_castAdd]
  · simp [pullBase, wedge, sgn, Finset.filter_singleton, f7]
  · simp [pullBase, wedge, sgn, Finset.filter_singleton, Finset.filter_insert, addNat_ne_castAdd,
      castAdd_lt_addNat, f1, f2, f4, f5, f6, Finset.mul_sum, Finset.erase_insert_of_ne (castAdd_ne_addNat _ _),
      Finset.erase_singleton]
    rw [if_neg (by decide)]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun _ _ => by ring)

theorem pullBase_const_mul {n : ℕ} (a : Fin n → ℂ) (k : ℂ) (y : Ext (n + n)) (S : Finset (Fin (1 + 1))) :
    pullBase a (fun S' => k * y S') S = k * pullBase a y S := by
  exact congrFun ((pullBaseL a).map_smul k y) S

theorem pullBase_zero {n : ℕ} (a : Fin n → ℂ) (S : Finset (Fin (1 + 1))) :
    pullBase a (fun _ => (0 : ℂ)) S = 0 := by
  exact congrFun ((pullBaseL a).map_zero) S

theorem pullFull_wedge_dt {n g : ℕ} (a : Fin n → ℂ) (i : Fin n) (x : Ext (n + n + g)) :
    pullFull a (wedge (dt g i) x) = a i • wedge (dt g (0 : Fin 1)) (pullFull a x) := by
  funext U
  obtain ⟨S, I, rfl⟩ : ∃ S I, U = join S I := ⟨_, _, (join_parts U).symm⟩
  rw [pullFull_join, Pi.smul_apply, show dt g (0 : Fin 1) = Fin.castAdd g (Fin.castAdd 1 (0 : Fin 1)) from rfl,
    wedge_castAdd_join, show dt g i = Fin.castAdd g (Fin.castAdd n i) from rfl]
  simp only [pullFull_join, wedge_castAdd_join]
  exact congrFun (pullBase_wedge_castAdd a i _) S

theorem pullFull_wedge_dtb {n g : ℕ} (a : Fin n → ℂ) (i : Fin n) (x : Ext (n + n + g)) :
    pullFull a (wedge (dtb g i) x) = star (a i) • wedge (dtb g (0 : Fin 1)) (pullFull a x) := by
  funext U
  obtain ⟨S, I, rfl⟩ : ∃ S I, U = join S I := ⟨_, _, (join_parts U).symm⟩
  rw [pullFull_join, Pi.smul_apply, show dtb g (0 : Fin 1) = Fin.castAdd g (Fin.natAdd 1 (0 : Fin 1)) from rfl,
    wedge_castAdd_join, show dtb g i = Fin.castAdd g (Fin.natAdd n i) from rfl]
  simp only [pullFull_join, wedge_castAdd_join]
  exact congrFun (pullBase_wedge_natAdd a i _) S

theorem pullFull_wedge_dzb {n g : ℕ} (a : Fin n → ℂ) (c : Fin g) (x : Ext (n + n + g)) :
    pullFull a (wedge (dzb n c) x) = wedge (dzb 1 c) (pullFull a x) := by
  funext U
  obtain ⟨S, I, rfl⟩ : ∃ S I, U = join S I := ⟨_, _, (join_parts U).symm⟩
  rw [pullFull_join, show dzb 1 c = Fin.natAdd (1 + 1) c from rfl, wedge_natAdd_join,
    show dzb n c = Fin.natAdd (n + n) c from rfl]
  simp only [wedge_natAdd_join, pullFull_join]
  rw [pullBase_sign]
  congr 1
  by_cases hc : c ∈ I
  · simp only [wedge, hc, if_true]
    exact pullBase_const_mul a _ _ S
  · simp only [wedge, hc, if_false]
    exact pullBase_zero a S

theorem pullFull_contr_dzb {n g : ℕ} (a : Fin n → ℂ) (c : Fin g) (x : Ext (n + n + g)) :
    pullFull a (contr (dzb n c) x) = contr (dzb 1 c) (pullFull a x) := by
  funext U
  obtain ⟨S, I, rfl⟩ : ∃ S I, U = join S I := ⟨_, _, (join_parts U).symm⟩
  rw [pullFull_join, show dzb 1 c = Fin.natAdd (1 + 1) c from rfl, contr_natAdd_join,
    show dzb n c = Fin.natAdd (n + n) c from rfl]
  simp only [contr_natAdd_join, pullFull_join]
  rw [pullBase_sign]
  congr 1
  by_cases hc : c ∈ I
  · simp only [contr, hc, if_true]
    exact pullBase_zero a S
  · simp only [contr, hc, if_false]
    exact pullBase_const_mul a _ _ S

end Coord

section Key
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

def epsS (S : Finset (Fin (1 + 1))) : ℂ :=
  (if Fin.castAdd 1 (0 : Fin 1) ∈ S then -1 else 1) * (if Fin.natAdd 1 (0 : Fin 1) ∈ S then -1 else 1)

theorem epsS_mul_self (S : Finset (Fin (1 + 1))) : epsS S * epsS S = 1 := by
  unfold epsS; split_ifs <;> norm_num

theorem lamL_comm (S : Finset (Fin (1 + 1))) (T : Ext (1 + 1 + g) → Ext (1 + 1 + g))
    (h1 : ∀ y, wedge (dt g (0 : Fin 1)) (T y) = -T (wedge (dt g (0 : Fin 1)) y))
    (h2 : ∀ y, wedge (dtb g (0 : Fin 1)) (T y) = -T (wedge (dtb g (0 : Fin 1)) y)) (y : Ext (1 + 1 + g)) :
    lamL S (T y) = epsS S • T (lamL S y) := by
  unfold lamL epsS
  by_cases h0 : Fin.castAdd 1 (0 : Fin 1) ∈ S <;> by_cases h1' : Fin.natAdd 1 (0 : Fin 1) ∈ S <;>
    simp only [h0, h1', ite_true, ite_false, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.id_apply, wedgeL, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
      AddHom.coe_mk] <;>
    simp [h1, h2, wedge_neg']

theorem dzb_ne_dt {m : ℕ} (c : Fin g) (i : Fin m) : dzb m c ≠ dt g i := by
  intro e; have := congrArg Fin.val e; simp [dzb, dt] at this; omega

theorem dzb_ne_dtb {m : ℕ} (c : Fin g) (i : Fin m) : dzb m c ≠ dtb g i := by
  intro e; have := congrArg Fin.val e; simp [dzb, dtb] at this; omega

theorem connForm_L {n : ℕ} (τ : E → Matrix (Fin g) (Fin g) ℂ) (b v : E)
    (L : Ext (n + n + g) →L[ℂ] Ext (1 + 1 + g)) (ε : ℂ) (hε : ε * ε = 1)
    (hzw : ∀ c x, wedge (dzb 1 c) (L x) = ε • L (wedge (dzb n c) x))
    (hzc : ∀ c x, contr (dzb 1 c) (L x) = ε • L (contr (dzb n c) x)) (x : Ext (n + n + g)) :
    connForm τ b v (L x) = L (connForm τ b v x) := by
  unfold connForm
  simp only [hzc, wedge_smul', hzw, smul_smul, hε, one_smul, map_sum, map_smul]

theorem superconn_comp {n : ℕ} (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E)
    (a : Fin n → ℂ) (L : Ext (n + n + g) →L[ℂ] Ext (1 + 1 + g)) (ε : ℂ) (hε : ε * ε = 1)
    (hdt : ∀ i x, a i • wedge (dt g (0 : Fin 1)) (L x) = ε • L (wedge (dt g i) x))
    (hdtb : ∀ i x, star (a i) • wedge (dtb g (0 : Fin 1)) (L x) = ε • L (wedge (dtb g i) x))
    (hzw : ∀ c x, wedge (dzb 1 c) (L x) = ε • L (wedge (dzb n c) x))
    (hzc : ∀ c x, contr (dzb 1 c) (L x) = ε • L (contr (dzb n c) x))
    (u : ℝ) (s : Pt E g → Ext (n + n + g)) (P : Pt E g) (hs : DifferentiableAt ℝ s P) :
    superconn τ h ![∑ i, a i • β i] u (fun Q => L (s Q)) P = ε • L (superconn τ h β u s P) := by
  have hnab : nablaE τ h ![∑ i, a i • β i] (fun Q => L (s Q)) P = ε • L (nablaE τ h β s P) := by
    unfold nablaE
    rw [Fin.sum_univ_one]
    simp only [Matrix.cons_val_zero]
    rw [nab10_comp h L s P _ hs, d01_comp_continuousLinearMap L s P _ hs, connForm_L τ P.1 _ L ε hε hzw hzc, hor_sum,
      nab10_sum, d01_sum, connForm_sum, ← map_add, ← Finset.sum_add_distrib]
    simp only [← smul_add]
    simp only [map_sum, map_smul]
    simp only [wedge_sum', wedge_smul', hdt, hdtb]
    simp only [map_sum, Finset.smul_sum, map_add, smul_add, Finset.sum_add_distrib]
  have hdbar : dbarV (fun Q => L (s Q)) P = ε • L (dbarV s P) := by
    unfold dbarV
    simp only [d01_comp_continuousLinearMap L s P _ hs, hzw, map_sum, Finset.smul_sum]
  have hadj : dbarAdj τ h (fun Q => L (s Q)) P = ε • L (dbarAdj τ h s P) := by
    unfold dbarAdj
    simp only [nab10_comp h L s P _ hs, hzc, map_neg, map_sum, map_smul, smul_neg, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    rw [smul_comm]
  unfold superconn
  rw [hnab, hdbar, hadj, map_add, map_smul, map_add]
  module

end Key

section Main
variable {g : ℕ}

theorem lamL_wedge (S : Finset (Fin (1 + 1))) (k : Fin (1 + 1 + g)) (y : Ext (1 + 1 + g)) :
    lamL S (wedge k y) = epsS S • wedge k (lamL S y) :=
  lamL_comm S (wedge k) (fun _ => by rw [GlobalTheory.WedgeAnticomm.wedge_wedge_anticomm]) (fun _ => by rw [GlobalTheory.WedgeAnticomm.wedge_wedge_anticomm]) y

theorem lamL_contr (S : Finset (Fin (1 + 1))) (c : Fin g) (y : Ext (1 + 1 + g)) :
    lamL S (contr (dzb 1 c) y) = epsS S • contr (dzb 1 c) (lamL S y) :=
  lamL_comm S _ (fun _ => by rw [contr_wedge_of_ne (dzb_ne_dt c 0), neg_neg])
    (fun _ => by rw [contr_wedge_of_ne (dzb_ne_dtb c 0), neg_neg]) y

theorem pullFullL_apply {n : ℕ} (a : Fin n → ℂ) (x : Ext (n + n + g)) : pullFullL a x = pullFull a x := rfl

variable {n : ℕ} (a : Fin n → ℂ) (S : Finset (Fin (1 + 1))) (c : ℂ)

theorem pull_dt (i : Fin n) (x : Ext (n + n + g)) :
    a i • wedge (dt g (0 : Fin 1)) ((c • (lamL S).comp (pullFullL a)) x) =
      epsS S • (c • (lamL S).comp (pullFullL a)) (wedge (dt g i) x) := by
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, pullFullL_apply,
    pullFull_wedge_dt, map_smul, lamL_wedge, wedge_smul', smul_smul]
  congr 1
  linear_combination (-(a i * c)) * epsS_mul_self S

theorem pull_dtb (i : Fin n) (x : Ext (n + n + g)) :
    star (a i) • wedge (dtb g (0 : Fin 1)) ((c • (lamL S).comp (pullFullL a)) x) =
      epsS S • (c • (lamL S).comp (pullFullL a)) (wedge (dtb g i) x) := by
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, pullFullL_apply,
    pullFull_wedge_dtb, map_smul, lamL_wedge, wedge_smul', smul_smul]
  congr 1
  linear_combination (-(star (a i) * c)) * epsS_mul_self S

theorem pull_dzb (k : Fin g) (x : Ext (n + n + g)) :
    wedge (dzb 1 k) ((c • (lamL S).comp (pullFullL a)) x) =
      epsS S • (c • (lamL S).comp (pullFullL a)) (wedge (dzb n k) x) := by
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, pullFullL_apply,
    pullFull_wedge_dzb, map_smul, lamL_wedge, wedge_smul', smul_smul]
  congr 1
  linear_combination (-c) * epsS_mul_self S

theorem pull_contr (k : Fin g) (x : Ext (n + n + g)) :
    contr (dzb 1 k) ((c • (lamL S).comp (pullFullL a)) x) =
      epsS S • (c • (lamL S).comp (pullFullL a)) (contr (dzb n k) x) := by
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, pullFullL_apply,
    pullFull_contr_dzb, map_smul, lamL_contr, contr_smul', smul_smul]
  congr 1
  linear_combination (-c) * epsS_mul_self S

end Main

theorem curv_pull : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)} {j : Fl g → Pt E g → ℂ} {h : Pt E g → ℝ}, IsDatum B τ M j h → ∀ (β : Fin n → E) (a : Fin n → ℂ) {b : E}, b ∈ B → ∀ (S : Finset (Fin (1 + 1))) (G : (Fin g → ℂ) → Ext (n + n + g)), ContDiff ℝ ∞ G → ∀ (u : ℝ) (z : Fin g → ℂ), curv τ h ![∑ i, a i • β i] b u (fun y => lamL S (pullFullL a (G y))) z = lamL S (pullFullL a (curv τ h β b u G z)) := by
  intro E _ _ _ g n B τ M j h hD β a b hb S G hG u z
  have key : ∀ (c : ℂ) (s : Pt E g → Ext (n + n + g)) (P : Pt E g), DifferentiableAt ℝ s P →
      superconn τ h ![∑ i, a i • β i] u (fun Q => (c • (lamL S).comp (pullFullL a)) (s Q)) P =
        epsS S • (c • (lamL S).comp (pullFullL a)) (superconn τ h β u s P) := fun c s P hs =>
    superconn_comp τ h β a _ (epsS S) (epsS_mul_self S) (pull_dt a S c) (pull_dtb a S c)
      (pull_dzb a S c) (pull_contr a S c) u s P hs
  have hG' : ∀ P : Pt E g, DifferentiableAt ℝ (fun P : Pt E g => G P.2) P := fun P =>
    (hG.differentiable (by simp)).differentiableAt.comp P differentiableAt_snd
  have inner : (superconn τ h ![∑ i, a i • β i] u fun P => lamL S (pullFullL a (G P.2))) =
      fun P => (epsS S • (lamL S).comp (pullFullL a)) (superconn τ h β u (fun P => G P.2) P) := by
    funext P
    have := key 1 (fun P => G P.2) P (hG' P)
    simpa using this
  unfold curv
  rw [inner, key (epsS S) _ (b, z) (GlobalTheory.SuperconnDiff.superconn_differentiableAt hD β hb G hG u z)]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_smul,
    epsS_mul_self, one_smul]
end GlobalTheory.TorsionForm.OneVec.CurvPull
