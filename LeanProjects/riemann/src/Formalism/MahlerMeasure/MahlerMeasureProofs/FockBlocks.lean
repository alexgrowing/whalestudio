import Formalism.MahlerMeasure.LevelLattice
import Formalism.MahlerMeasure.MahlerMeasureProofs.RemoveS
import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelDecomp

namespace Formalism.GM.FockB

open MvPolynomial Finset

section Ops
variable {k σ : Type} [Field k]

def atoms (S : Set σ) : Set (Module.End k (MvPolynomial σ k)) :=
  {T | ∃ u ∈ S, T = LinearMap.mulLeft k (X u) ∨ T = (pderiv u).toLinearMap}

noncomputable def Ops (S : Set σ) : Subalgebra k (Module.End k (MvPolynomial σ k)) :=
  Algebra.adjoin k (atoms S)

theorem atoms_commute {S S' : Set σ} (hS : Disjoint S S') {T T' : Module.End k (MvPolynomial σ k)}
    (hT : T ∈ atoms S) (hT' : T' ∈ atoms S') : Commute T T' := by
  obtain ⟨u, hu, hTu⟩ := hT
  obtain ⟨v, hv, hTv⟩ := hT'
  have huv : u ≠ v := fun h => Set.disjoint_left.mp hS hu (h ▸ hv)
  rw [commute_iff_eq]
  refine LinearMap.ext fun f => ?_
  rcases hTu with rfl | rfl <;> rcases hTv with rfl | rfl <;>
    simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
  · ring
  · rw [pderiv_mul, pderiv_X_of_ne huv]; ring
  · rw [pderiv_mul, pderiv_X_of_ne (Ne.symm huv)]; ring
  · exact ProjS.pderiv_comm _ _ _

theorem ops_commute {S S' : Set σ} (hS : Disjoint S S') {T T' : Module.End k (MvPolynomial σ k)}
    (hT : T ∈ Ops S) (hT' : T' ∈ Ops S') : Commute T T' := by
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hT' (fun b hb => ?_)
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hT
    (fun a ha => (atoms_commute hS ha hb).symm)).symm

theorem ops_apply_comm {S S' : Set σ} (hS : Disjoint S S') {T T' : Module.End k (MvPolynomial σ k)}
    (hT : T ∈ Ops S) (hT' : T' ∈ Ops S') (y : MvPolynomial σ k) : T (T' y) = T' (T y) := by
  have := (ops_commute hS hT hT').eq
  exact LinearMap.congr_fun this y

theorem ops_mono {S S' : Set σ} (h : S ⊆ S') : Ops (k := k) S ≤ Ops S' := by
  apply Algebra.adjoin_mono
  rintro T ⟨u, hu, hT⟩
  exact ⟨u, h hu, hT⟩

theorem mulLeftX_mem {S : Set σ} {u : σ} (hu : u ∈ S) : LinearMap.mulLeft k (X u : MvPolynomial σ k) ∈ Ops S :=
  Algebra.subset_adjoin ⟨u, hu, Or.inl rfl⟩

theorem pderiv_mem {S : Set σ} {u : σ} (hu : u ∈ S) :
    ((pderiv u : Derivation k (MvPolynomial σ k) (MvPolynomial σ k)).toLinearMap) ∈ Ops S :=
  Algebra.subset_adjoin ⟨u, hu, Or.inr rfl⟩

theorem mulLeft_mem {S : Set σ} {f : MvPolynomial σ k} (hf : f ∈ Algebra.adjoin k (X '' S)) :
    LinearMap.mulLeft k f ∈ Ops S := by
  have e1 : LinearMap.mulLeft k f = Algebra.lmul k (MvPolynomial σ k) f := by
    refine LinearMap.ext fun g => ?_
    simp
  rw [e1]
  have h2 : Algebra.lmul k (MvPolynomial σ k) f ∈ (Algebra.adjoin k (X '' S)).map (Algebra.lmul k _) :=
    Subalgebra.mem_map.mpr ⟨f, hf, rfl⟩
  rw [AlgHom.map_adjoin] at h2
  refine Algebra.adjoin_mono ?_ h2
  rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  refine ⟨u, hu, Or.inl ?_⟩
  refine LinearMap.ext fun g => ?_
  simp

end Ops

end Formalism.GM.FockB

namespace Formalism.GM.FockB

open MvPolynomial Finset

section Pair
variable {k σ : Type} [Field k] {r : ℕ}

def V (w e : Fin r → σ) (zv sv : σ) : Set σ := Set.range w ∪ Set.range e ∪ {zv, sv}

noncomputable def Ehp (w e : Fin r → σ) (zv sv : σ) : MvPolynomial σ k :=
  X zv * X sv + ∑ c, X (w c) * X (e c)

noncomputable def Pop (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) : Module.End k (MvPolynomial σ k) :=
  ∑ l ∈ range (o + 1), (((-1 : k) ^ l) / (((l.factorial : k) ^ 2) * ((o + n + r + z - 1).choose l : k))) •
    (M.tieEh w e zv sv ^ l * Formalism.GM.tieF w e ^ l * LinearMap.mulLeft k (X zv ^ z))

def Good (w e : Fin r → σ) (zv sv : σ) (o n : ℕ) (y : MvPolynomial σ k) : Prop :=
  ProjS.eulL w y = (o : k) • y ∧ ProjS.eulL e y = (n : k) • y ∧ pderiv zv y = 0 ∧ pderiv sv y = 0

variable {w e : Fin r → σ} {zv sv : σ}

theorem w_mem (c : Fin r) : w c ∈ V w e zv sv := Set.mem_union_left _ (Set.mem_union_left _ ⟨c, rfl⟩)
theorem e_mem (c : Fin r) : e c ∈ V w e zv sv := Set.mem_union_left _ (Set.mem_union_right _ ⟨c, rfl⟩)
theorem zv_mem : zv ∈ V w e zv sv := Set.mem_union_right _ (Set.mem_insert _ _)
theorem sv_mem : sv ∈ V w e zv sv := Set.mem_union_right _ (Set.mem_insert_of_mem _ rfl)

theorem X_mem {S : Set σ} {u : σ} (hu : u ∈ S) : (X u : MvPolynomial σ k) ∈ Algebra.adjoin k (X '' S) :=
  Algebra.subset_adjoin ⟨u, hu, rfl⟩

theorem Ehp_mem : (Ehp w e zv sv : MvPolynomial σ k) ∈ Algebra.adjoin k (X '' V w e zv sv) :=
  add_mem (mul_mem (X_mem zv_mem) (X_mem sv_mem)) (sum_mem fun c _ => mul_mem (X_mem (w_mem c)) (X_mem (e_mem c)))

theorem tieEh_eq_mulLeft : (M.tieEh w e zv sv : Module.End k (MvPolynomial σ k)) =
    LinearMap.mulLeft k (Ehp w e zv sv) := rfl

theorem tieEh_mem : (M.tieEh w e zv sv : Module.End k (MvPolynomial σ k)) ∈ Ops (V w e zv sv) := by
  rw [tieEh_eq_mulLeft]; exact mulLeft_mem Ehp_mem

theorem tieE_mem : (Formalism.GM.tieE w e : Module.End k (MvPolynomial σ k)) ∈ Ops (V w e zv sv) :=
  mulLeft_mem (sum_mem fun c _ => mul_mem (X_mem (w_mem c)) (X_mem (e_mem c)))

theorem tieF_mem : (Formalism.GM.tieF w e : Module.End k (MvPolynomial σ k)) ∈ Ops (V w e zv sv) := by
  unfold Formalism.GM.tieF
  refine sum_mem fun c _ => ?_
  rw [← Module.End.mul_eq_comp]
  exact mul_mem (pderiv_mem (w_mem c)) (pderiv_mem (e_mem c))

theorem tiePhi_mem (o n z : ℕ) :
    (Formalism.GM.tiePhi w e o n z : Module.End k (MvPolynomial σ k)) ∈ Ops (V w e zv sv) := by
  unfold Formalism.GM.tiePhi
  refine sum_mem fun j _ => Subalgebra.smul_mem _ ?_ _
  rw [← Module.End.mul_eq_comp]
  exact mul_mem (pow_mem tieE_mem _) (pow_mem tieF_mem _)

theorem eulL_mem {s : ℕ} {S : Set σ} (t : Fin s → σ) (ht : ∀ c, t c ∈ S) :
    (ProjS.eulL t : Module.End k (MvPolynomial σ k)) ∈ Ops S := by
  unfold ProjS.eulL
  refine sum_mem fun c _ => ?_
  rw [← Module.End.mul_eq_comp]
  exact mul_mem (mulLeftX_mem (ht c)) (pderiv_mem (ht c))

theorem Pop_mem (o n z : ℕ) : (Pop w e zv sv o n z : Module.End k (MvPolynomial σ k)) ∈ Ops (V w e zv sv) := by
  unfold Pop
  refine sum_mem fun l _ => Subalgebra.smul_mem _ ?_ _
  exact mul_mem (mul_mem (pow_mem tieEh_mem _) (pow_mem tieF_mem _))
    (mulLeft_mem (pow_mem (X_mem zv_mem) _))

theorem tieP_eq_Pop (o n z : ℕ) (y : MvPolynomial σ k) :
    M.tieP w e zv sv o n z y = Pop w e zv sv o n z y := by
  simp [M.tieP, Pop, LinearMap.sum_apply, Module.End.mul_apply]

theorem good_of_ops {S : Set σ} (hS : Disjoint (V w e zv sv) S) {T : Module.End k (MvPolynomial σ k)}
    (hT : T ∈ Ops S) {o n : ℕ} {y : MvPolynomial σ k} (hy : Good w e zv sv o n y) :
    Good w e zv sv o n (T y) := by
  obtain ⟨h1, h2, h3, h4⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ops_apply_comm hS (eulL_mem w (fun c => w_mem c)) hT, h1, map_smul]
  · rw [ops_apply_comm hS (eulL_mem e (fun c => e_mem c)) hT, h2, map_smul]
  · have := ops_apply_comm hS (pderiv_mem (k := k) (zv_mem (w := w) (e := e) (sv := sv))) hT y
    simp only [Derivation.coeFn_coe] at this
    rw [this, h3, map_zero]
  · have := ops_apply_comm hS (pderiv_mem (k := k) (sv_mem (w := w) (e := e) (zv := zv))) hT y
    simp only [Derivation.coeFn_coe] at this
    rw [this, h4, map_zero]

theorem biHom_of_good [CharZero k] {o n : ℕ} {y : MvPolynomial σ k} (h : Good w e zv sv o n y) :
    BiHom w e o n y :=
  Formalism.GM.ld_biHom_of_euler (by rw [← ProjS.eulL_apply]; exact h.1) (by rw [← ProjS.eulL_apply]; exact h.2.1)

theorem free_of_pderiv [CharZero k] {v : σ} {y : MvPolynomial σ k} (h : pderiv v y = 0) :
    ∀ m ∈ y.support, m v = 0 := by
  classical
  intro m hm
  by_contra hne
  have hle : Finsupp.single v 1 ≤ m := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hne)
  have hc := congrArg (coeff (m - Finsupp.single v 1)) h
  rw [coeff_pderiv, tsub_add_cancel_of_le hle, coeff_zero] at hc
  have h1 : ((((m - Finsupp.single v 1 : σ →₀ ℕ)) v : ℕ) : k) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  exact (mem_support_iff.mp hm) ((mul_eq_zero.mp hc).resolve_right h1)

theorem zsfree_of_good [CharZero k] {o n : ℕ} {y : MvPolynomial σ k} (h : Good w e zv sv o n y) :
    M.ZSFree zv sv y :=
  fun m hm => ⟨free_of_pderiv h.2.2.1 m hm, free_of_pderiv h.2.2.2 m hm⟩

theorem tieEh_pow_apply (j : ℕ) (u : MvPolynomial σ k) :
    (M.tieEh w e zv sv ^ j) u = Ehp w e zv sv ^ j * u := by
  rw [tieEh_eq_mulLeft, LinearMap.pow_mulLeft, LinearMap.mulLeft_apply]

theorem step_same [CharZero k] (hv : M.TieVars w e zv sv) (hr : 1 ≤ r) {o n z : ℕ} {y y' : MvPolynomial σ k}
    (hy : BiHom w e o n y) (hy' : BiHom w e o n y') (hz : M.ZSFree zv sv y) (hz' : M.ZSFree zv sv y')
    (j : ℕ) :
    M.fockK (Ehp w e zv sv ^ j * M.tieP w e zv sv o n z y) (Ehp w e zv sv ^ j * M.tieP w e zv sv o n z y') =
      ((j.factorial : k) ^ 2 * (((o + n + r + z + 1 + j - 1).choose j : ℕ) : k) * (z.factorial : k)) *
        M.fockK y (Formalism.GM.tiePhi w e o n z y') := by
  have h := ProjS.fockForm_raiseAug_pow_augLift (z := z) hv hr hy hy' hz hz' j j
  rw [if_pos rfl, ProjS.fockK_smul_left, ProjS.fockK_smul_right, tieEh_pow_apply, tieEh_pow_apply] at h
  have hf : (j.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have h2 : M.fockK (Ehp w e zv sv ^ j * M.tieP w e zv sv o n z y) (Ehp w e zv sv ^ j * M.tieP w e zv sv o n z y') =
      (j.factorial : k) * ((j.factorial : k) * (((j.factorial : k))⁻¹ * (((j.factorial : k))⁻¹ *
        M.fockK (Ehp w e zv sv ^ j * M.tieP w e zv sv o n z y) (Ehp w e zv sv ^ j * M.tieP w e zv sv o n z y')))) := by
    field_simp
  rw [h2, h]
  ring

theorem step_orth [CharZero k] (hv : M.TieVars w e zv sv) (hr : 1 ≤ r) {o n o' n' z : ℕ}
    {y y' : MvPolynomial σ k}
    (hy : BiHom w e o n y) (hy' : BiHom w e o' n' y') (hz : M.ZSFree zv sv y) (hz' : M.ZSFree zv sv y')
    {j j' : ℕ} (hjj : j ≠ j') :
    M.fockK (Ehp w e zv sv ^ j * M.tieP w e zv sv o n z y) (Ehp w e zv sv ^ j' * M.tieP w e zv sv o' n' z y') = 0 := by
  have hFP := ProjS.fh_P (z := z) hv hr hy hz
  have hFP' := ProjS.fh_P (z := z) hv hr hy' hz'
  have hE := ProjS.eig_P (z := z) hv hy' hz' (fun l => ((-1 : k) ^ l) / (((l.factorial : k) ^ 2) *
    ((o' + n' + r + z - 1).choose l : k)))
  rw [← ProjS.tieP_eq, ProjS.eulL_apply, ProjS.eulL_apply] at hE
  have key := Formalism.GM.F_pow_E_pow (ProjS.tv_w hv) (ProjS.tv_e hv) (ProjS.tv_we hv) (M.tieP w e zv sv o' n' z y')
    (o' + z) n' (o' + z + n' + r) hE.1 hE.2 hFP' (by omega) j j'
  rw [← tieEh_pow_apply, ← tieEh_pow_apply, ProjS.tieEh_eq, ProjS.fockK_tieE_pow, key, ProjS.fockK_smul_right]
  rcases Nat.lt_or_gt_of_ne hjj with hlt | hgt
  · have hd : j' - j = (j' - j - 1) + 1 := by omega
    rw [ProjS.fockK_tieE_pow_right, hd, pow_succ, Module.End.mul_apply, hFP, map_zero, ProjS.fockK_zero_left]
    simp
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hgt]
    simp

end Pair

end Formalism.GM.FockB

namespace Formalism.GM.FockB

open MvPolynomial Finset

section Chain
variable {k σ α : Type} [Field k] {r : ℕ} (w e : α → Fin r → σ) (zv sv : α → σ) (z : α → ℕ)

def Va (a : α) : Set σ := V (w a) (e a) (zv a) (sv a)

def VL (L : List α) : Set σ := {v | ∃ b ∈ L, v ∈ Va w e zv sv b}

noncomputable def chainP (o n : α → ℕ) (L : List α) (y : MvPolynomial σ k) : MvPolynomial σ k :=
  L.foldr (fun a acc => M.tieP (w a) (e a) (zv a) (sv a) (o a) (n a) (z a) acc) y

noncomputable def chainE (j : α → ℕ) (L : List α) : MvPolynomial σ k :=
  (L.map fun a => Ehp (w a) (e a) (zv a) (sv a) ^ j a).prod

noncomputable def chainPhi (o n : α → ℕ) (L : List α) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  L.foldr (fun a acc => Formalism.GM.tiePhi (w a) (e a) (o a) (n a) (z a) ∘ₗ acc) LinearMap.id

noncomputable def cst (o n j : α → ℕ) (L : List α) : k :=
  (L.map fun a => ((j a).factorial : k) ^ 2 * (((o a + n a + r + z a + 1 + j a - 1).choose (j a) : ℕ) : k) *
    ((z a).factorial : k)).prod

variable {w e zv sv z}

theorem Va_sub {a : α} {L : List α} (h : a ∈ L) : Va w e zv sv a ⊆ VL w e zv sv L := fun _ hv => ⟨a, h, hv⟩

theorem VL_cons_sub {a : α} {L : List α} : VL w e zv sv L ⊆ VL w e zv sv (a :: L) :=
  fun _ ⟨b, hb, hv⟩ => ⟨b, List.mem_cons_of_mem _ hb, hv⟩

theorem disj_VL {a : α} {L : List α} (h : ∀ b ∈ L, Disjoint (Va w e zv sv a) (Va w e zv sv b)) :
    Disjoint (Va w e zv sv a) (VL w e zv sv L) :=
  Set.disjoint_left.mpr fun _ hv ⟨b, hb, hvb⟩ => Set.disjoint_left.mp (h b hb) hv hvb

theorem exists_op_eq_chainP (o n : α → ℕ) (L : List α) :
    ∃ T ∈ Ops (k := k) (VL w e zv sv L), ∀ y, chainP w e zv sv z o n L y = T y := by
  induction L with
  | nil => exact ⟨1, one_mem _, fun y => rfl⟩
  | cons a L ih =>
    obtain ⟨T, hT, hTe⟩ := ih
    refine ⟨Pop (w a) (e a) (zv a) (sv a) (o a) (n a) (z a) * T,
      mul_mem (ops_mono (Va_sub (List.mem_cons_self ..)) (Pop_mem _ _ _)) (ops_mono VL_cons_sub hT), fun y => ?_⟩
    show M.tieP _ _ _ _ _ _ _ (chainP w e zv sv z o n L y) = _
    rw [hTe, tieP_eq_Pop, Module.End.mul_apply]

theorem chainE_mem (j : α → ℕ) (L : List α) :
    (chainE w e zv sv j L : MvPolynomial σ k) ∈ Algebra.adjoin k (X '' VL w e zv sv L) := by
  induction L with
  | nil => simp only [chainE, List.map_nil, List.prod_nil]; exact one_mem _
  | cons a L ih =>
    simp only [chainE, List.map_cons, List.prod_cons]
    exact mul_mem (pow_mem (Algebra.adjoin_mono (Set.image_mono (Va_sub (List.mem_cons_self ..))) Ehp_mem) _)
      (Algebra.adjoin_mono (Set.image_mono VL_cons_sub) ih)

theorem chainPhi_mem (o n : α → ℕ) (L : List α) :
    (chainPhi w e z o n L : Module.End k (MvPolynomial σ k)) ∈ Ops (VL w e zv sv L) := by
  induction L with
  | nil => exact one_mem _
  | cons a L ih =>
    show Formalism.GM.tiePhi (w a) (e a) (o a) (n a) (z a) * chainPhi w e z o n L ∈ _
    exact mul_mem (ops_mono (Va_sub (List.mem_cons_self ..)) (tiePhi_mem (zv := zv a) (sv := sv a) _ _ _))
      (ops_mono VL_cons_sub ih)

theorem chain_rw (o n j : α → ℕ) (a : α) (L : List α) (hdisj : Disjoint (Va w e zv sv a) (VL w e zv sv L))
    (Y0 : MvPolynomial σ k) :
    chainE w e zv sv j (a :: L) * chainP w e zv sv z o n (a :: L) Y0 =
      Ehp (w a) (e a) (zv a) (sv a) ^ j a * M.tieP (w a) (e a) (zv a) (sv a) (o a) (n a) (z a)
        (chainE w e zv sv j L * chainP w e zv sv z o n L Y0) := by
  have hHm := mulLeft_mem (chainE_mem (w := w) (e := e) (zv := zv) (sv := sv) (k := k) j L)
  have hPa := Pop_mem (k := k) (w := w a) (e := e a) (zv := zv a) (sv := sv a) (o a) (n a) (z a)
  show (Ehp (w a) (e a) (zv a) (sv a) ^ j a * chainE w e zv sv j L) *
    M.tieP _ _ _ _ _ _ _ (chainP w e zv sv z o n L Y0) = _
  rw [mul_assoc, tieP_eq_Pop, tieP_eq_Pop]
  congr 1
  exact (ops_apply_comm hdisj hPa hHm _).symm

theorem good_chain (o n j : α → ℕ) (a : α) (L : List α) (hdisj : Disjoint (Va w e zv sv a) (VL w e zv sv L))
    {o0 n0 : ℕ} (Y0 : MvPolynomial σ k) (h : Good (w a) (e a) (zv a) (sv a) o0 n0 Y0) :
    Good (w a) (e a) (zv a) (sv a) o0 n0 (chainE w e zv sv j L * chainP w e zv sv z o n L Y0) := by
  obtain ⟨T, hT, hTe⟩ := exists_op_eq_chainP (k := k) (w := w) (e := e) (zv := zv) (sv := sv) (z := z) o n L
  have hHm := mulLeft_mem (chainE_mem (w := w) (e := e) (zv := zv) (sv := sv) (k := k) j L)
  rw [hTe]
  exact good_of_ops hdisj hHm (good_of_ops hdisj hT h)

theorem phi_chain (o n j : α → ℕ) (a : α) (L : List α) (hdisj : Disjoint (Va w e zv sv a) (VL w e zv sv L))
    (o0 n0 z0 : ℕ) (Y0 : MvPolynomial σ k) :
    Formalism.GM.tiePhi (w a) (e a) o0 n0 z0 (chainE w e zv sv j L * chainP w e zv sv z o n L Y0) =
      chainE w e zv sv j L * chainP w e zv sv z o n L (Formalism.GM.tiePhi (w a) (e a) o0 n0 z0 Y0) := by
  obtain ⟨T, hT, hTe⟩ := exists_op_eq_chainP (k := k) (w := w) (e := e) (zv := zv) (sv := sv) (z := z) o n L
  have hHm := mulLeft_mem (chainE_mem (w := w) (e := e) (zv := zv) (sv := sv) (k := k) j L)
  have hPhi := tiePhi_mem (k := k) (w := w a) (e := e a) (zv := zv a) (sv := sv a) o0 n0 z0
  rw [hTe, hTe]
  have h1 := ops_apply_comm hdisj hPhi hHm (T Y0)
  have h2 := ops_apply_comm hdisj hPhi hT Y0
  simp only [LinearMap.mulLeft_apply] at h1
  rw [h1, h2]

theorem chain_main [CharZero k] (hr : 1 ≤ r) (o n j : α → ℕ) (L : List α)
    (hv : ∀ a ∈ L, M.TieVars (w a) (e a) (zv a) (sv a))
    (hd : L.Pairwise fun a b => Disjoint (Va w e zv sv a) (Va w e zv sv b))
    (Y : MvPolynomial σ k) (hY : ∀ a ∈ L, Good (w a) (e a) (zv a) (sv a) (o a) (n a) Y) :
    ∀ Y' : MvPolynomial σ k, (∀ a ∈ L, Good (w a) (e a) (zv a) (sv a) (o a) (n a) Y') →
      M.fockK (chainE w e zv sv j L * chainP w e zv sv z o n L Y)
          (chainE w e zv sv j L * chainP w e zv sv z o n L Y') =
        cst (r := r) z o n j L * M.fockK Y (chainPhi w e z o n L Y') := by
  induction L with
  | nil =>
    intro Y' _
    simp [chainE, chainP, chainPhi, cst]
  | cons a L ih =>
    intro Y' hY'
    obtain ⟨hda, hdL⟩ := List.pairwise_cons.mp hd
    have hvA := hv a (List.mem_cons_self ..)
    have hdisj := disj_VL hda
    rw [chain_rw o n j a L hdisj, chain_rw o n j a L hdisj]
    have gY := good_chain (z := z) o n j a L hdisj Y (hY a (List.mem_cons_self ..))
    have gY' := good_chain (z := z) o n j a L hdisj Y' (hY' a (List.mem_cons_self ..))
    rw [step_same hvA hr (biHom_of_good gY) (biHom_of_good gY') (zsfree_of_good gY) (zsfree_of_good gY'),
      phi_chain o n j a L hdisj]
    have hPhi := tiePhi_mem (k := k) (w := w a) (e := e a) (zv := zv a) (sv := sv a) (o a) (n a) (z a)
    rw [ih (fun b hb => hv b (List.mem_cons_of_mem _ hb)) hdL (fun b hb => hY b (List.mem_cons_of_mem _ hb)) _
      (fun b hb => good_of_ops (hda b hb).symm hPhi (hY' b (List.mem_cons_of_mem _ hb)))]
    have e2 : chainPhi w e z o n (a :: L) Y' =
        chainPhi w e z o n L (Formalism.GM.tiePhi (w a) (e a) (o a) (n a) (z a) Y') := by
      show Formalism.GM.tiePhi (w a) (e a) (o a) (n a) (z a) (chainPhi w e z o n L Y') = _
      exact ops_apply_comm hdisj hPhi (chainPhi_mem (zv := zv) (sv := sv) o n L) _
    rw [e2]
    simp only [cst, List.map_cons, List.prod_cons]
    ring

theorem chain_orth [CharZero k] (hr : 1 ≤ r) (o n j o' n' j' : α → ℕ) (L : List α)
    (hv : ∀ a ∈ L, M.TieVars (w a) (e a) (zv a) (sv a))
    (hd : L.Pairwise fun a b => Disjoint (Va w e zv sv a) (Va w e zv sv b))
    (hon : ∀ a ∈ L, j a = j' a → o a = o' a ∧ n a = n' a) (hne : ∃ a ∈ L, j a ≠ j' a)
    (Y : MvPolynomial σ k) (hY : ∀ a ∈ L, Good (w a) (e a) (zv a) (sv a) (o a) (n a) Y) :
    ∀ Y' : MvPolynomial σ k, (∀ a ∈ L, Good (w a) (e a) (zv a) (sv a) (o' a) (n' a) Y') →
      M.fockK (chainE w e zv sv j L * chainP w e zv sv z o n L Y)
          (chainE w e zv sv j' L * chainP w e zv sv z o' n' L Y') = 0 := by
  induction L with
  | nil =>
    obtain ⟨a, ha, _⟩ := hne
    simp at ha
  | cons a L ih =>
    intro Y' hY'
    obtain ⟨hda, hdL⟩ := List.pairwise_cons.mp hd
    have hvA := hv a (List.mem_cons_self ..)
    have hdisj := disj_VL hda
    rw [chain_rw o n j a L hdisj, chain_rw o' n' j' a L hdisj]
    have gY := good_chain (z := z) o n j a L hdisj Y (hY a (List.mem_cons_self ..))
    have gY' := good_chain (z := z) o' n' j' a L hdisj Y' (hY' a (List.mem_cons_self ..))
    by_cases hja : j a = j' a
    · obtain ⟨ho, hn⟩ := hon a (List.mem_cons_self ..) hja
      rw [← ho, ← hn] at gY'
      rw [← hja, ← ho, ← hn]
      rw [step_same hvA hr (biHom_of_good gY) (biHom_of_good gY') (zsfree_of_good gY) (zsfree_of_good gY'),
        phi_chain o' n' j' a L hdisj]
      have hPhi := tiePhi_mem (k := k) (w := w a) (e := e a) (zv := zv a) (sv := sv a) (o a) (n a) (z a)
      have hneL : ∃ b ∈ L, j b ≠ j' b := by
        obtain ⟨b, hb, hjb⟩ := hne
        rcases List.mem_cons.mp hb with rfl | hb
        · exact absurd hja hjb
        · exact ⟨b, hb, hjb⟩
      rw [ih (fun b hb => hv b (List.mem_cons_of_mem _ hb)) hdL
        (fun b hb => hon b (List.mem_cons_of_mem _ hb)) hneL
        (fun b hb => hY b (List.mem_cons_of_mem _ hb)) _
        (fun b hb => good_of_ops (hda b hb).symm hPhi (hY' b (List.mem_cons_of_mem _ hb))), mul_zero]
    · exact step_orth hvA hr (biHom_of_good gY) (biHom_of_good gY') (zsfree_of_good gY) (zsfree_of_good gY') hja

end Chain

end Formalism.GM.FockB

namespace Formalism.GM.FockB

open MvPolynomial Finset Formalism.GM.M

section Block
variable {N r : ℕ} (D : BlockData N)

def wA : Option (Fin D.T.t) → Fin r → BVar N r D.T.t :=
  fun a c => a.elim (Sum.inl (Fin.castSucc D.uPos, c)) (fun i => Sum.inl (finPos N (D.T.pos i), c))
def eA : Option (Fin D.T.t) → Fin r → BVar N r D.T.t :=
  fun a c => a.elim (xiVar N r D.T.t c) (fun i => Sum.inl (finPos N (D.T.pos i + 1), c))
def zA : Option (Fin D.T.t) → BVar N r D.T.t :=
  fun a => a.elim (scalZ N r D.T.t (Fin.last D.T.t)) (fun i => scalZ N r D.T.t (Fin.castSucc i))
def sA : Option (Fin D.T.t) → BVar N r D.T.t :=
  fun a => a.elim (scalS N r D.T.t (Fin.last D.T.t)) (fun i => scalS N r D.T.t (Fin.castSucc i))
def zzA : Option (Fin D.T.t) → ℕ := fun a => a.elim D.zPlus D.T.z
def oA (j : Fin D.T.t → ℕ) (jp : ℕ) : Option (Fin D.T.t) → ℕ :=
  fun a => a.elim (D.LL.deg D.uPos - jp) (fun i => (D.lettersAt j jp).deg (D.letterAt (D.T.pos i)))
def nA (j : Fin D.T.t → ℕ) (jp : ℕ) : Option (Fin D.T.t) → ℕ :=
  fun a => a.elim (D.B - jp) (fun i => (D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)))
def jA (j : Fin D.T.t → ℕ) (jp : ℕ) : Option (Fin D.T.t) → ℕ := fun a => a.elim jp j
def LA : List (Option (Fin D.T.t)) := none :: (List.finRange D.T.t).map some

variable (p : ℕ) [Fact p.Prime]

theorem pall_eq (j : Fin D.T.t → ℕ) (jp : ℕ) (Y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    D.Pall p j jp Y = chainP (wA D) (eA D) (zA D) (sA D) (zzA D) (oA D j jp) (nA D j jp) (LA D) Y := by
  simp only [chainP, LA, List.foldr_cons, List.foldr_map]
  rfl

theorem phi_eq (j : Fin D.T.t → ℕ) (jp : ℕ) :
    D.phiAll p (r := r) j jp = chainPhi (wA D) (eA D) (zzA D) (oA D j jp) (nA D j jp) (LA D) := by
  simp only [chainPhi, LA, List.foldr_cons, List.foldr_map]
  rfl

theorem ehat_eq (j : Fin D.T.t → ℕ) (jp : ℕ) :
    (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp =
      chainE (wA D) (eA D) (zA D) (sA D) (jA D j jp) (LA D) := by
  simp only [chainE, LA, List.map_cons, List.prod_cons, List.map_map]
  rw [mul_comm, Fin.prod_univ_def]
  rfl

variable {D}

theorem pos_ne (hB : D.BlockOK) {i i' : Fin D.T.t} (h : i ≠ i') : D.T.pos i ≠ D.T.pos i' :=
  fun h' => h (hB.1.1.injective h')

theorem pos_ne_succ (hB : D.BlockOK) (i i' : Fin D.T.t) : D.T.pos i ≠ D.T.pos i' + 1 := by
  intro h
  obtain ⟨h1, hv1, -⟩ := hB.1.2.1 i
  obtain ⟨h2, -, hv2⟩ := hB.1.2.1 i'
  have e : (⟨D.T.pos i, by omega⟩ : Fin N) = ⟨D.T.pos i' + 1, h2⟩ := Fin.ext h
  rw [e] at hv1
  rw [hv1] at hv2
  exact Bool.noConfusion hv2

theorem letterAt_val {k : ℕ} (h : k ≤ N - 1) : (D.letterAt k : ℕ) = k := by
  simp [BlockData.letterAt, h]

theorem degU (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) :
    (D.lettersAt j jp).deg D.uPos = D.LL.deg D.uPos - jp := by
  simp only [BlockData.lettersAt]
  rw [Finset.sum_eq_zero (fun i _ => if_neg (by have := hB.2.1 i; omega))]
  simp

theorem deg_fst (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) :
    (D.lettersAt j jp).deg (D.letterAt (D.T.pos i)) = D.LL.deg (D.letterAt (D.T.pos i)) - j i := by
  have h1 := hB.2.1 i
  have h2 := hB.2.2.2
  have hv : (D.letterAt (D.T.pos i) : ℕ) = D.T.pos i := letterAt_val (by omega)
  simp only [BlockData.lettersAt]
  rw [Finset.sum_eq_single i (fun i' _ hi' => if_neg (by
      rw [hv]; have := pos_ne hB (Ne.symm hi'); have := pos_ne_succ hB i i'; omega)) (by simp),
    if_pos (Or.inl hv), if_neg (by intro h; rw [h] at hv; omega)]
  simp

theorem deg_snd (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) :
    (D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)) = D.LL.deg (D.letterAt (D.T.pos i + 1)) - j i := by
  have h1 := hB.2.1 i
  have h2 := hB.2.2.2
  have hv : (D.letterAt (D.T.pos i + 1) : ℕ) = D.T.pos i + 1 := letterAt_val (by omega)
  simp only [BlockData.lettersAt]
  rw [Finset.sum_eq_single i (fun i' _ hi' => if_neg (by
      rw [hv]; have := pos_ne hB (Ne.symm hi'); have := pos_ne_succ hB i' i; omega)) (by simp),
    if_pos (Or.inr hv), if_neg (by intro h; rw [h] at hv; omega)]
  simp

end Block

end Formalism.GM.FockB

namespace Formalism.GM.FockB

open MvPolynomial Finset Formalism.GM.M

section Block2
variable {N r : ℕ} {D : BlockData N}

theorem finPos_val {k : ℕ} (h : k ≤ N) : (finPos N k : ℕ) = k := by
  simp [finPos, h]

theorem tvA (hB : D.BlockOK) (a : Option (Fin D.T.t)) :
    M.TieVars (wA (r := r) D a) (eA D a) (zA D a) (sA D a) := by
  have h2 := hB.2.2.2
  rcases a with _ | i
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c d h; simpa [wA] using h
    · intro c d h; simpa [eA, xiVar] using h
    · intro c d h
      simp only [wA, eA, xiVar, Option.elim, Sum.inl.injEq, Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc,
        Fin.val_last] at h
      omega
    · intro c; simp [wA, eA, zA, sA, xiVar, scalZ, scalS]
    · simp [zA, sA, scalZ, scalS]
  · have h1 := hB.2.1 i
    have hv0 : (finPos N (D.T.pos i) : ℕ) = D.T.pos i := finPos_val (by omega)
    have hv1 : (finPos N (D.T.pos i + 1) : ℕ) = D.T.pos i + 1 := finPos_val (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c d h; simpa [wA] using h
    · intro c d h; simpa [eA] using h
    · intro c d h
      simp only [wA, eA, Option.elim, Sum.inl.injEq, Prod.mk.injEq, Fin.ext_iff] at h
      omega
    · intro c; simp [wA, eA, zA, sA, scalZ, scalS]
    · simp [zA, sA, scalZ, scalS]

theorem disjA (hB : D.BlockOK) {a b : Option (Fin D.T.t)} (hab : a ≠ b) :
    Disjoint (Va (wA (r := r) D) (eA D) (zA D) (sA D) a) (Va (wA D) (eA D) (zA D) (sA D) b) := by
  have h2 := hB.2.2.2
  rw [Set.disjoint_left]
  intro v hva hvb
  simp only [Va, V, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hva hvb
  rcases a with _ | i <;> rcases b with _ | i'
  · exact hab rfl
  · have h1 := hB.2.1 i'
    have hv0 : (finPos N (D.T.pos i') : ℕ) = D.T.pos i' := finPos_val (by omega)
    have hv1 : (finPos N (D.T.pos i' + 1) : ℕ) = D.T.pos i' + 1 := finPos_val (by omega)
    have hi := i'.isLt
    rcases hva with ((⟨c, rfl⟩ | ⟨c, rfl⟩) | rfl | rfl) <;> rcases hvb with ((⟨c', h⟩ | ⟨c', h⟩) | h | h) <;>
      simp only [wA, eA, zA, sA, xiVar, scalZ, scalS, Option.elim, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
        Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_last] at h <;> omega
  · have h1 := hB.2.1 i
    have hv0 : (finPos N (D.T.pos i) : ℕ) = D.T.pos i := finPos_val (by omega)
    have hv1 : (finPos N (D.T.pos i + 1) : ℕ) = D.T.pos i + 1 := finPos_val (by omega)
    have hi := i.isLt
    rcases hva with ((⟨c, rfl⟩ | ⟨c, rfl⟩) | rfl | rfl) <;> rcases hvb with ((⟨c', h⟩ | ⟨c', h⟩) | h | h) <;>
      simp only [wA, eA, zA, sA, xiVar, scalZ, scalS, Option.elim, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
        Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_last] at h <;> omega
  · have hii : i ≠ i' := fun h => hab (by rw [h])
    have hii' : (i : ℕ) ≠ i' := fun h => hii (Fin.ext h)
    have h1 := hB.2.1 i
    have h1' := hB.2.1 i'
    have q1 := pos_ne hB hii
    have q2 := pos_ne_succ hB i i'
    have q3 := pos_ne_succ hB i' i
    have hv0 : (finPos N (D.T.pos i) : ℕ) = D.T.pos i := finPos_val (by omega)
    have hv1 : (finPos N (D.T.pos i + 1) : ℕ) = D.T.pos i + 1 := finPos_val (by omega)
    have hv0' : (finPos N (D.T.pos i') : ℕ) = D.T.pos i' := finPos_val (by omega)
    have hv1' : (finPos N (D.T.pos i' + 1) : ℕ) = D.T.pos i' + 1 := finPos_val (by omega)
    rcases hva with ((⟨c, rfl⟩ | ⟨c, rfl⟩) | rfl | rfl) <;> rcases hvb with ((⟨c', h⟩ | ⟨c', h⟩) | h | h) <;>
      simp only [wA, eA, zA, sA, xiVar, scalZ, scalS, Option.elim, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
        Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_last] at h <;> omega

theorem nodupLA : (LA D).Nodup := by
  simp only [LA, List.nodup_cons, List.mem_map, reduceCtorEq, and_false, exists_false, not_false_eq_true,
    true_and]
  exact (List.nodup_finRange _).map (Option.some_injective _)

theorem pairwiseA (hB : D.BlockOK) :
    (LA D).Pairwise fun a b => Disjoint (Va (wA (r := r) D) (eA D) (zA D) (sA D) a) (Va (wA D) (eA D) (zA D) (sA D) b) :=
  List.Pairwise.imp (fun hab => disjA hB hab) nodupLA

end Block2

end Formalism.GM.FockB

namespace Formalism.GM.FockB

open MvPolynomial Finset Formalism.GM.M

section Block3
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem chainEmb_inj (t : ℕ) : Function.Injective (chainEmb N r t) := by
  rintro ⟨a, c⟩ ⟨a', c'⟩ h
  simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq, Fin.castSucc_inj] at h
  rw [h.1, h.2]

theorem supp_Y {t : ℕ} (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (g : MvPolynomial (BVar N r t) ℚ_[p])
    (m : BVar N r t →₀ ℕ) (hm : m ∈ (rename (chainEmb N r t) y * g).support) :
    ∃ m1 ∈ y.support, ∃ m2 ∈ g.support, m = Finsupp.mapDomain (chainEmb N r t) m1 + m2 := by
  classical
  have h := support_mul (rename (chainEmb N r t) y) g hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp h
  rw [support_rename_of_injective (chainEmb_inj t)] at ha
  obtain ⟨m1, hm1, rfl⟩ := Finset.mem_image.mp ha
  exact ⟨m1, hm1, b, hb, rfl⟩

variable {D : BlockData N}

theorem goodA [NeZero r] (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hy : y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr) (g : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hg : g ∈ XiPolZ p N r D.T.t (D.B - jp)) (a : Option (Fin D.T.t)) :
    Good (wA D a) (eA D a) (zA D a) (sA D a) (oA D j jp a) (nA D j jp a)
      (rename (chainEmb N r D.T.t) y * g) := by
  have hyP : ∀ m ∈ y.support, ∀ b, ∑ c, m (b, c) = (D.lettersAt j jp).deg b := by
    have h := (Submodule.mem_inf.mp hy).1
    rw [Pol, mem_restrictSupport_iff] at h
    exact fun m hm => h hm
  have hgP : ∀ m ∈ g.support, (∀ v ∈ m.support, ∃ c, v = xiVar N r D.T.t c) ∧
      ∑ c, m (xiVar N r D.T.t c) = D.B - jp := by
    have h := (Submodule.mem_inf.mp hg).1
    rw [Submodule.restrictScalars_mem, mem_restrictSupport_iff] at h
    exact fun m hm => h hm
  have key : ∀ m ∈ (rename (chainEmb N r D.T.t) y * g).support, ∃ m1 ∈ y.support, ∃ m2 ∈ g.support,
      (∀ b c, m (chainEmb N r D.T.t (b, c)) = m1 (b, c)) ∧ (∀ c, m (xiVar N r D.T.t c) = m2 (xiVar N r D.T.t c)) ∧
      (∀ q, m (Sum.inr q) = 0) := by
    intro m hm
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := supp_Y y g m hm
    have hm2z : ∀ v, (∀ c, v ≠ xiVar N r D.T.t c) → m2 v = 0 := fun v hv => by
      by_contra h
      obtain ⟨c, hc⟩ := (hgP m2 hm2).1 v (Finsupp.mem_support_iff.mpr h)
      exact hv c hc
    refine ⟨m1, hm1, m2, hm2, ?_, ?_, ?_⟩
    · intro b c
      rw [Finsupp.add_apply, Finsupp.mapDomain_apply (chainEmb_inj _),
        hm2z (chainEmb N r D.T.t (b, c)) (fun c' h => (Fin.castSucc_lt_last b).ne
          (congrArg Prod.fst (Sum.inl_injective h : (Fin.castSucc b, c) = (Fin.last N, c')))), add_zero]
    · intro c
      rw [Finsupp.add_apply, Finsupp.mapDomain_notin_range, zero_add]
      rintro ⟨⟨b, c'⟩, h⟩
      exact (Fin.castSucc_lt_last b).ne
        (congrArg Prod.fst (Sum.inl_injective h : (Fin.castSucc b, c') = (Fin.last N, c)))
    · intro q
      rw [Finsupp.add_apply, Finsupp.mapDomain_notin_range, hm2z (Sum.inr q) (fun c h => by simp [xiVar] at h),
        add_zero]
      rintro ⟨x, h⟩
      simp [chainEmb] at h
  have hZS : ∀ q, pderiv (Sum.inr q) (rename (chainEmb N r D.T.t) y * g) = 0 := fun q =>
    ProjS.pderiv_of_free _ _ (fun m hm => by
      obtain ⟨_, _, _, _, _, _, h3⟩ := key m hm
      exact h3 q)
  have h2 := hB.2.2.2
  rcases a with _ | i
  · refine ⟨?_, ?_, hZS _, hZS _⟩
    · apply ProjS.eulL_of_support
      intro m hm
      obtain ⟨m1, hm1, m2, hm2, h1, -, -⟩ := key m hm
      show ∑ c, m (chainEmb N r D.T.t (D.uPos, c)) = _
      simp only [h1]
      rw [hyP m1 hm1, degU hB]
      rfl
    · apply ProjS.eulL_of_support
      intro m hm
      obtain ⟨m1, hm1, m2, hm2, -, h1, -⟩ := key m hm
      show ∑ c, m (xiVar N r D.T.t c) = _
      simp only [h1]
      rw [(hgP m2 hm2).2]
      rfl
  · have hi := hB.2.1 i
    have e0 : finPos N (D.T.pos i) = Fin.castSucc (D.letterAt (D.T.pos i)) := by
      apply Fin.ext
      rw [Fin.val_castSucc, letterAt_val (by omega), finPos_val (by omega)]
    have e1 : finPos N (D.T.pos i + 1) = Fin.castSucc (D.letterAt (D.T.pos i + 1)) := by
      apply Fin.ext
      rw [Fin.val_castSucc, letterAt_val (by omega), finPos_val (by omega)]
    refine ⟨?_, ?_, hZS _, hZS _⟩
    · apply ProjS.eulL_of_support
      intro m hm
      obtain ⟨m1, hm1, m2, hm2, h1, -, -⟩ := key m hm
      show ∑ c, m (Sum.inl (finPos N (D.T.pos i), c)) = _
      rw [e0]
      show ∑ c, m (chainEmb N r D.T.t (D.letterAt (D.T.pos i), c)) = _
      simp only [h1]
      rw [hyP m1 hm1]
      rfl
    · apply ProjS.eulL_of_support
      intro m hm
      obtain ⟨m1, hm1, m2, hm2, h1, -, -⟩ := key m hm
      show ∑ c, m (Sum.inl (finPos N (D.T.pos i + 1), c)) = _
      rw [e1]
      show ∑ c, m (chainEmb N r D.T.t (D.letterAt (D.T.pos i + 1), c)) = _
      simp only [h1]
      rw [hyP m1 hm1]
      rfl

end Block3

end Formalism.GM.FockB

namespace Formalism.GM.FockB

open MvPolynomial Finset Formalism.GM.M

theorem fock_blocks_of_weights : M.FockBlocks := by
  intro p _ N r _ D hB hr
  constructor
  · intro j j' jp jp' _ _ hne y hy y' hy' g hg g' hg'
    rw [ehat_eq D p j jp, ehat_eq D p j' jp', pall_eq, pall_eq]
    have hon : ∀ a ∈ LA D, jA D j jp a = jA D j' jp' a →
        oA D j jp a = oA D j' jp' a ∧ nA D j jp a = nA D j' jp' a := by
      intro a _ h
      rcases a with _ | i
      · simp only [jA, oA, nA, Option.elim] at h ⊢
        rw [h]; exact ⟨rfl, rfl⟩
      · simp only [jA, oA, nA, Option.elim] at h ⊢
        rw [deg_fst hB, deg_fst hB, deg_snd hB, deg_snd hB, h]; exact ⟨rfl, rfl⟩
    have hne' : ∃ a ∈ LA D, jA D j jp a ≠ jA D j' jp' a := by
      by_contra hc
      simp only [not_exists, not_and, not_not] at hc
      apply hne
      have h0 : jp = jp' := hc none (List.mem_cons_self ..)
      have h1 : j = j' := funext fun i =>
        hc (some i) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
      rw [h0, h1]
    exact chain_orth hr (oA D j jp) (nA D j jp) (jA D j jp) (oA D j' jp') (nA D j' jp') (jA D j' jp') (LA D)
      (fun a _ => tvA hB a) (pairwiseA hB) hon hne' _ (fun a _ => goodA hB j jp y hy g hg a) _
      (fun a _ => goodA hB j' jp' y' hy' g' hg' a)
  · intro j jp _ y hy y' hy' g hg g' hg'
    rw [ProjS.fockK_smul_left, ProjS.fockK_smul_right, ehat_eq D p j jp, pall_eq, pall_eq,
      chain_main hr (oA D j jp) (nA D j jp) (jA D j jp) (LA D) (fun a _ => tvA hB a) (pairwiseA hB) _
        (fun a _ => goodA hB j jp y hy g hg a) _ (fun a _ => goodA hB j jp y' hy' g' hg' a), phi_eq]
    have hcst : cst (r := r) (zzA D) (oA D j jp) (nA D j jp) (jA D j jp) (LA D) =
        ((jp.factorial : ℚ_[p]) ^ 2 * (∏ i, ((j i).factorial : ℚ_[p])) ^ 2) *
          ((∏ i, ((((D.lettersAt j jp).deg (D.letterAt (D.T.pos i)) +
                (D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)) + r + D.T.z i + 1 + j i - 1).choose (j i) *
              (D.T.z i).factorial : ℕ) : ℚ_[p])) *
            ((((D.LL.deg D.uPos - jp) + (D.B - jp) + r + D.zPlus + 1 + jp - 1).choose jp *
              D.zPlus.factorial : ℕ) : ℚ_[p])) := by
      simp only [cst, LA, List.map_cons, List.prod_cons, List.map_map]
      rw [← Fin.prod_univ_def]
      simp only [Function.comp_def, jA, oA, nA, zzA, Option.elim]
      push_cast
      simp only [Finset.prod_mul_distrib, Finset.prod_pow]
      ring
    rw [hcst]
    have hf1 : (∏ i, ((j i).factorial : ℚ_[p])) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hf2 : (jp.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp

end Formalism.GM.FockB

namespace Formalism.GM

theorem fock_block_decomposition : M.FockBlocks := FockB.fock_blocks_of_weights

end Formalism.GM
