import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertPowDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.ChiEqOneOfClosure
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Reduce
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.CartierFrobeniusFormLocal

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S

abbrev Av (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : Type :=
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E

instance charZero_Fv (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    CharZero (v.adicCompletion I.F) :=
  charZero_of_injective_algebraMap (algebraMap I.F (v.adicCompletion I.F)).injective

def InR (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α z : Av I v) : Prop :=
  ∃ a b : v.adicCompletion I.F, a ∈ v.adicCompletionIntegers I.F ∧ b ∈ v.adicCompletionIntegers I.F ∧
    z = incL I v a + incL I v b * α

theorem inR_one (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v) : InR I v α 1 :=
  ⟨1, 0, one_mem _, zero_mem _, by simp⟩

theorem inR_self (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v) : InR I v α α :=
  ⟨0, 1, zero_mem _, one_mem _, by simp⟩

theorem inR_neg (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v) {z : Av I v}
    (hz : InR I v α z) : InR I v α (-z) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hz
  exact ⟨-a, -b, neg_mem ha, neg_mem hb, by simp only [map_neg]; ring⟩

theorem inR_mul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v)
    {t : v.adicCompletion I.F} (htO : t ∈ v.adicCompletionIntegers I.F)
    (ht : α * α = incL I v t * α - 1) {x y : Av I v} (hx : InR I v α x) (hy : InR I v α y) :
    InR I v α (x * y) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  obtain ⟨c, d, hc, hd, rfl⟩ := hy
  refine ⟨a * c - b * d, a * d + b * c + b * d * t, sub_mem (mul_mem ha hc) (mul_mem hb hd),
    add_mem (add_mem (mul_mem ha hd) (mul_mem hb hc)) (mul_mem (mul_mem hb hd) htO), ?_⟩
  simp only [map_sub, map_add, map_mul]
  linear_combination (incL I v b * incL I v d) * ht

theorem inR_pow (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v)
    {t : v.adicCompletion I.F} (htO : t ∈ v.adicCompletionIntegers I.F)
    (ht : α * α = incL I v t * α - 1) {x : Av I v} (hx : InR I v α x) (m : ℕ) :
    InR I v α (x ^ m) := by
  induction m with
  | zero => simpa using inR_one I v α
  | succ k ih => rw [pow_succ]; exact inR_mul I v α htO ht ih hx

theorem exists_pow_sub (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v)
    {t : v.adicCompletion I.F} (htO : t ∈ v.adicCompletionIntegers I.F)
    (ht : α * α = incL I v t * α - 1) (N : ℕ) (hN : 0 < N) :
    ∃ i j : ℕ, i < j ∧ ∃ w, InR I v α w ∧ α ^ j - α ^ i = incL I v N * w := by
  classical
  have hpow : ∀ m : ℕ, InR I v α (α ^ m) := fun m => inR_pow I v α htO ht (inR_self I v α) m
  choose a b ha hb hab using hpow
  have hNF : (N : v.adicCompletion I.F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  let NO : Set (v.adicCompletion I.F) :=
    (fun y => (N : v.adicCompletion I.F) * y) '' (v.adicCompletionIntegers I.F : Set _)
  have hOo : IsOpen (v.adicCompletionIntegers I.F : Set (v.adicCompletion I.F)) :=
    Valued.isOpen_integer (R := v.adicCompletion I.F)
  have hNO : IsOpen NO := (Homeomorph.mulLeft₀ (N : v.adicCompletion I.F) hNF).isOpenMap _ hOo
  let U : v.adicCompletionIntegers I.F → Set (v.adicCompletion I.F) :=
    fun x => (fun y => y - (x : v.adicCompletion I.F)) ⁻¹' NO
  have hU : ∀ x, IsOpen (U x) := fun x => hNO.preimage (continuous_id.sub continuous_const)
  have hcov : (v.adicCompletionIntegers I.F : Set (v.adicCompletion I.F)) ⊆ ⋃ x, U x := by
    intro y hy
    refine Set.mem_iUnion.2 ⟨⟨y, hy⟩, ?_⟩
    exact ⟨0, zero_mem _, by simp⟩
  obtain ⟨T, hT⟩ := (PI.WAU.isCompact_Ov v).elim_finite_subcover U hU hcov
  have hsel : ∀ y ∈ (v.adicCompletionIntegers I.F : Set (v.adicCompletion I.F)),
      ∃ x : T, y ∈ U x := by
    intro y hy
    have := hT hy
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hx, hyx⟩ := this
    exact ⟨⟨x, hx⟩, hyx⟩
  choose sel hsel' using hsel
  let f : ℕ → T × T := fun m => (sel (a m) (ha m), sel (b m) (hb m))
  have key : ∀ i j, f i = f j → ∃ w, InR I v α w ∧ α ^ j - α ^ i = incL I v N * w := by
    intro i j hij
    have h1 : sel (a i) (ha i) = sel (a j) (ha j) := congrArg Prod.fst hij
    have h2 : sel (b i) (hb i) = sel (b j) (hb j) := congrArg Prod.snd hij
    obtain ⟨p1, hp1, e1⟩ := hsel' (a i) (ha i)
    obtain ⟨p2, hp2, e2⟩ := hsel' (a j) (ha j)
    obtain ⟨q1, hq1, f1⟩ := hsel' (b i) (hb i)
    obtain ⟨q2, hq2, f2⟩ := hsel' (b j) (hb j)
    rw [h1] at e1
    rw [h2] at f1
    refine ⟨incL I v (p2 - p1) + incL I v (q2 - q1) * α,
      ⟨p2 - p1, q2 - q1, sub_mem hp2 hp1, sub_mem hq2 hq1, rfl⟩, ?_⟩
    have ea : a j - a i = (N : v.adicCompletion I.F) * (p2 - p1) := by
      simp only at e1 e2
      linear_combination e1 - e2
    have eb : b j - b i = (N : v.adicCompletion I.F) * (q2 - q1) := by
      simp only at f1 f2
      linear_combination f1 - f2
    have ea' := congrArg (incL I v) ea
    have eb' := congrArg (incL I v) eb
    simp only [map_sub, map_mul, map_natCast] at ea' eb' ⊢
    rw [hab j, hab i]
    linear_combination ea' + α * eb'
  obtain ⟨i, j, hne, hf⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨i, j, h, key i j hf⟩
  · exact ⟨j, i, h, key j i hf.symm⟩

theorem exists_pow_near_one (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v)
    {t : v.adicCompletion I.F} (htO : t ∈ v.adicCompletionIntegers I.F)
    (hsum : α + sigV I v α = incL I v t) (hα : sigV I v α * α = 1) (N : ℕ) (hN : 0 < N) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ w w', InR I v α w ∧ InR I v α w' ∧ α ^ m - 1 = incL I v N * w ∧
      sigV I v α ^ m - 1 = incL I v N * w' := by
  have ht : α * α = incL I v t * α - 1 := by
    rw [← hsum]
    linear_combination (-1 : Av I v) * hα
  have hsig : InR I v α (sigV I v α) :=
    ⟨t, -1, htO, neg_mem (one_mem _), by
      simp only [map_neg, map_one]
      linear_combination hsum⟩
  obtain ⟨i, j, hij, w0, hw0, e0⟩ := exists_pow_sub I v α htO ht N hN
  obtain ⟨m, rfl⟩ : ∃ m, j = i + m := ⟨j - i, by omega⟩
  have hm : 1 ≤ m := by omega
  have hpi : sigV I v α ^ i * α ^ i = 1 := by rw [← mul_pow, hα, one_pow]
  have hpm : sigV I v α ^ m * α ^ m = 1 := by rw [← mul_pow, hα, one_pow]
  have e1 : α ^ m - 1 = incL I v N * (sigV I v α ^ i * w0) := by
    have : α ^ m - 1 = sigV I v α ^ i * (α ^ (i + m) - α ^ i) := by
      rw [pow_add]
      linear_combination (1 - α ^ m) * hpi
    rw [this, e0]
    ring
  refine ⟨m, hm, sigV I v α ^ i * w0, -(sigV I v α ^ m) * (sigV I v α ^ i * w0),
    inR_mul I v α htO ht (inR_pow I v α htO ht hsig i) hw0,
    inR_mul I v α htO ht (inR_neg I v α (inR_pow I v α htO ht hsig m))
      (inR_mul I v α htO ht (inR_pow I v α htO ht hsig i) hw0), e1, ?_⟩
  have : sigV I v α ^ m - 1 = -(sigV I v α ^ m) * (α ^ m - 1) := by
    linear_combination hpm
  rw [this, e1]
  ring

theorem adelic_bound (I : AutInst) (Mx : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ w ∈ I.Lf, N • (Mx *ᵥ w) ∈ I.Lf := by
  obtain ⟨k, m, hm, hgen⟩ := PI.WAU.B.exists_gen I.L (Module.Finite.iff_fg.mpr I.L_fg)
  obtain ⟨N, hN0, hN⟩ := PI.WAU.B.common_nat
    (fun j N => N • (Mx *ᵥ PI.WAU.B.ivec (F := I.F) (m j)) ∈ I.Lf)
    (fun j N M h => PI.WAU.B.nsmul_lam h M)
    (fun j => PI.WAU.B.exists_nat_vec (F := I.F) I.L_span _)
  refine ⟨N, hN0, fun w hw => ?_⟩
  have := PI.WAU.B.mulVec_lam hm hgen (N • Mx) (fun j => by rw [Matrix.smul_mulVec]; exact hN j) hw
  rwa [Matrix.smul_mulVec] at this

theorem loc_bound (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (Mx : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) {N : ℕ}
    (hM : ∀ w ∈ I.Lf, N • (Mx *ᵥ w) ∈ I.Lf) (z : Fin I.n → Av I v)
    (hz : z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) :
    N • (Mx.map (PI.FinKW.psiV I v).toRingHom *ᵥ z) ∈
      Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
  obtain ⟨w, hwv, hww⟩ := PI.FinKW.local_vector_lift I v z
  have hw : w ∈ I.Lf := PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective I w (fun u => by
    by_cases hu : u = v
    · subst hu
      rwa [hwv]
    · rw [hww u hu]
      exact zero_mem _)
  have h1 := PI.FinKW.LocTo.mem_local_lattice_iff I _ (hM w hw) v
  rwa [vecV_nsmul, vecV_mulVec', hwv] at h1

theorem local_bound (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (M : Matrix (Fin I.n) (Fin I.n) (Av I v)) :
    ∃ N : ℕ, 0 < N ∧ ∀ z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      N • (M *ᵥ z) ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
  obtain ⟨N, hN, h⟩ := adelic_bound I (liftMat I v M)
  refine ⟨N, hN, fun z hz => ?_⟩
  have := loc_bound I v _ h z hz
  rwa [liftMat_map_same] at this

theorem incL_smul_mem (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) {a : v.adicCompletion I.F}
    (ha : a ∈ v.adicCompletionIntegers I.F) {y : Fin I.n → Av I v}
    (hy : y ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) :
    incL I v a • y ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
  have e : incL I v a • y = (⟨a, ha⟩ : v.adicCompletionIntegers I.F) • y := by
    rw [PI.FinKW.LocTo.ov_smul_vec]
    rfl
  rw [e]
  exact Submodule.smul_mem _ _ hy

theorem small_mem (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v)
    (P : Matrix (Fin I.n) (Fin I.n) (Av I v)) (N : ℕ)
    (h1 : ∀ z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      N • (P *ᵥ z) ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)))
    (h2 : ∀ z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      N • ((α • P) *ᵥ z) ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)))
    {w : Av I v} (hw : InR I v α w) (z : Fin I.n → Av I v)
    (hz : z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) :
    (incL I v N * w) • (P *ᵥ z) ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hw
  have e : (incL I v N * (incL I v a + incL I v b * α)) • (P *ᵥ z) =
      incL I v a • (N • (P *ᵥ z)) + incL I v b • (N • ((α • P) *ᵥ z)) := by
    rw [Matrix.smul_mulVec, ← Nat.cast_smul_eq_nsmul (Av I v), ← Nat.cast_smul_eq_nsmul (Av I v),
      smul_smul, smul_smul, smul_smul, ← add_smul, map_natCast]
    congr 1
    ring
  rw [e]
  exact add_mem (incL_smul_mem I v ha (h1 z hz)) (incL_smul_mem I v hb (h2 z hz))

theorem mul_qr {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (P : Matrix n n R) (hP : P * P = P) (x y : R) :
    (1 + x • P) * (1 + y • P) = 1 + (x + y + x * y) • P := by
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP,
    add_smul]
  rw [mul_comm x y]
  abel

theorem qr_pow {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (P : Matrix n n R) (hP : P * P = P) (c : R) (m : ℕ) :
    (1 + (c - 1) • P) ^ m = 1 + (c ^ m - 1) • P := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, mul_qr P hP]
    congr 2
    ring

theorem qReflPow_of (hT : TraceInt) : QReflPow := by
  intro I v hv s hs
  obtain ⟨P, α, hP, hα, hsP⟩ := hs
  obtain ⟨t, htO, hsum⟩ := hT I v hv α hα
  obtain ⟨N1, hN1, hb1⟩ := local_bound I v P
  obtain ⟨N2, hN2, hb2⟩ := local_bound I v (α • P)
  have h1 : ∀ z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      (N1 * N2) • (P *ᵥ z) ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
    intro z hz
    rw [mul_comm, mul_smul]
    exact nsmul_mem (hb1 z hz) N2
  have h2 : ∀ z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      (N1 * N2) • ((α • P) *ᵥ z) ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
    intro z hz
    rw [mul_smul]
    exact nsmul_mem (hb2 z hz) N1
  obtain ⟨m, hm, w, w', hw, hw', e1, e2⟩ :=
    exists_pow_near_one I v α htO hsum hα (N1 * N2) (Nat.mul_pos hN1 hN2)
  refine ⟨m, hm, ?_⟩
  have hmat : (((s ^ m : Uv I v) : GL (Fin I.n) (Av I v)) : Matrix (Fin I.n) (Fin I.n) (Av I v)) =
      1 + (α ^ m - 1) • P := by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hsP, qr_pow P hP α m]
  have hpm : sigV I v α ^ m * α ^ m = 1 := by rw [← mul_pow, hα, one_pow]
  have hinv : (1 + (sigV I v α ^ m - 1) • P) * (1 + (α ^ m - 1) • P) = 1 := by
    rw [mul_qr P hP]
    have : sigV I v α ^ m - 1 + (α ^ m - 1) + (sigV I v α ^ m - 1) * (α ^ m - 1) = 0 := by
      linear_combination hpm
    rw [this, zero_smul, add_zero]
  have hS : ∀ y, (1 + (α ^ m - 1) • P) *ᵥ y = y + (incL I v (N1 * N2 : ℕ) * w) • (P *ᵥ y) := by
    intro y
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, e1]
  have hT' : ∀ y, (1 + (sigV I v α ^ m - 1) • P) *ᵥ y =
      y + (incL I v (N1 * N2 : ℕ) * w') • (P *ᵥ y) := by
    intro y
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, e2]
  intro z
  rw [hmat]
  constructor
  · intro hz
    rw [hS]
    exact add_mem hz (small_mem I v α P (N1 * N2) h1 h2 hw z hz)
  · intro hz
    have := add_mem hz (small_mem I v α P (N1 * N2) h1 h2 hw' _ hz)
    rwa [← hT', Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at this

end PI.UnitaryGroupMassFormula.AdIndexEq

end
