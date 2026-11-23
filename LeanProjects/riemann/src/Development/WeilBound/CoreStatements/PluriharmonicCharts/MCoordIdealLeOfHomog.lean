import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.W

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {L : Type} [Field L]

def IsPt (y : (Σ k, ι k) → Φ) (z : (Σ k, ι k) → L) : Prop :=
  (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ mCoordIdeal y, aeval z f = 0

def HasVal (y : (Σ k, ι k) → Φ) (z : (Σ k, ι k) → L) (s : Φ) (v : L) : Prop :=
  ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧ aeval z h ≠ 0 ∧
    aeval y g = s * aeval y h ∧ aeval z g = v * aeval z h

def penCo (y : (Σ k, ι k) → Φ) (k₀ : K) (A B : ι k₀ → Φ) (t : RatFunc Φ) :
    (Σ o : Option K, ι (o.getD k₀)) → RatFunc Φ
  | ⟨some k, m⟩ => algebraMap Φ (RatFunc Φ) (y ⟨k, m⟩)
  | ⟨none, m⟩ => algebraMap Φ (RatFunc Φ) (A m) + t * algebraMap Φ (RatFunc Φ) (B m)

structure PenFrame (y : (Σ k, ι k) → Φ) (k₀ : K) (B : ι k₀ → Φ) (cf : Φ) (e : K → ℤ)
    (z : (Σ k, ι k) → L) (c : ∀ k, ι k) where
  p : ι k₀ → Φ
  r : ι k₀ → Φ
  α : ι k₀ → Φ
  β : ι k₀ → Φ
  pv : ι k₀ → L
  rv : ι k₀ → L
  αv : ι k₀ → L
  βv : ι k₀ → L
  ε : Φ
  γ : Φ
  δ : Φ
  sv : L
  hp : ∀ m, HasVal y z (p m) (pv m)
  hr : ∀ m, HasVal y z (r m) (rv m)
  hα : ∀ m, HasVal y z (α m) (αv m)
  hβ : ∀ m, HasVal y z (β m) (βv m)
  ε_ne : ε ≠ 0
  γ_ne : γ ≠ 0
  p_eq : ∀ m, p m = ε * y ⟨k₀, m⟩
  r_eq : ∀ m, r m = γ * B m + δ * y ⟨k₀, m⟩
  αp : ∑ m, α m * p m = 1
  αr : ∑ m, α m * r m = 0
  βp : ∑ m, β m * p m = 0
  βr : ∑ m, β m * r m = 1
  hs : HasVal y z (cf * ε * γ / chartMono y c e) sv
  sv_ne : sv ≠ 0

theorem aeval_eq_zero_of_mem {y : (Σ k, ι k) → Φ} {f : MRing ι} (hf : f ∈ mCoordIdeal y) : aeval y f = 0 := by
  have h0 : mConeMap y f = 0 := hf
  have e : (eval fun _ : K => (1 : Φ)).comp (mConeMap y).toRingHom = (aeval y : MRing ι →ₐ[ℤ] Φ).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) fun p => by simp [mConeMap]
  have := RingHom.congr_fun e f
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h0, map_zero] at this
  exact this.symm

theorem mem_iff_of_homog {y : (Σ k, ι k) → Φ} {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d) :
    f ∈ mCoordIdeal y ↔ aeval y f = 0 :=
  ⟨aeval_eq_zero_of_mem, mem_mCoordIdeal_of_aeval_eq_zero y hf⟩

theorem mCoordIdeal_le_of_homog {y : (Σ k, ι k) → Φ} {J : Ideal (MRing ι)}
    (h : ∀ f d, IsMultiHomog f d → aeval y f = 0 → f ∈ J) : mCoordIdeal y ≤ J := by
  obtain ⟨S, hS, e⟩ := CoordinateConeArithVar.isMultiHomogIdeal y
  have hS' : ∀ f ∈ S, f ∈ mCoordIdeal y := fun f hf => by rw [e]; exact Ideal.subset_span hf
  rw [e, Ideal.span_le]
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  exact h f a ha (aeval_eq_zero_of_mem (hS' f hf))

theorem IsPt.le {y : (Σ k, ι k) → Φ} {z : (Σ k, ι k) → L} (hz : IsPt y z) : mCoordIdeal y ≤ mCoordIdeal z :=
  mCoordIdeal_le_of_homog fun f _ hf h0 => (mem_iff_of_homog hf).2 (hz.2 f ((mem_iff_of_homog hf).2 h0))

theorem isPt_of_homog {y : (Σ k, ι k) → Φ} {z : (Σ k, ι k) → L} (h0 : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (h : ∀ (f : MRing ι) d, IsMultiHomog f d → aeval y f = 0 → aeval z f = 0) : IsPt y z :=
  ⟨h0, fun _ hf => (RingHom.mem_ker).1 (mCoordIdeal_le_of_homog
    (J := RingHom.ker (aeval z : MRing ι →ₐ[ℤ] L)) (fun f d hd h1 => (RingHom.mem_ker).2 (h f d hd h1)) hf)⟩

theorem isPt_self {y : (Σ k, ι k) → Φ} (h0 : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) : IsPt y y :=
  ⟨h0, fun _ hf => aeval_eq_zero_of_mem hf⟩

theorem IsPt.aeval_ne {y : (Σ k, ι k) → Φ} {z : (Σ k, ι k) → L} (hz : IsPt y z) {h : MRing ι} {d : K → ℕ}
    (hh : IsMultiHomog h d) (h0 : aeval z h ≠ 0) : aeval y h ≠ 0 := fun e => h0 (hz.2 h ((mem_iff_of_homog hh).2 e))

theorem isMultiHomog_X (p : Σ k, ι k) : IsMultiHomog (X p : MRing ι) (fun k => if k = p.1 then 1 else 0) :=
  isMultiHomog_X_single p

theorem IsPt.coord_ne {y : (Σ k, ι k) → Φ} {z : (Σ k, ι k) → L} (hz : IsPt y z) {q : Σ k, ι k} (h : z q ≠ 0) :
    y q ≠ 0 := by
  have := hz.aeval_ne (isMultiHomog_X q) (by rwa [aeval_X])
  rwa [aeval_X] at this

variable {y : (Σ k, ι k) → Φ} {z : (Σ k, ι k) → L}

theorem HasVal.unique (hz : IsPt y z) {s : Φ} {v w : L} (hv : HasVal y z s v) (hw : HasVal y z s w) : v = w := by
  obtain ⟨d, g, h, hg, hh, h0, e, ev⟩ := hv
  obtain ⟨d', g', h', hg', hh', h0', e', ev'⟩ := hw
  have hsub : IsMultiHomog (g * h' - g' * h) (d + d') := by
    refine isMultiHomog_sub (isMultiHomog_mul hg hh') ?_
    rw [add_comm]
    exact isMultiHomog_mul hg' hh
  have h1 := hz.2 _ ((mem_iff_of_homog hsub).2 (by rw [map_sub, map_mul, map_mul, e, e']; ring))
  rw [map_sub, map_mul, map_mul, ev, ev'] at h1
  have h2 : (v - w) * (aeval z h * aeval z h') = 0 := by linear_combination h1
  exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right (mul_ne_zero h0 h0'))

theorem HasVal.mul {s t : Φ} {v w : L} (hv : HasVal y z s v) (hw : HasVal y z t w) : HasVal y z (s * t) (v * w) := by
  obtain ⟨d, g, h, hg, hh, h0, e, ev⟩ := hv
  obtain ⟨d', g', h', hg', hh', h0', e', ev'⟩ := hw
  refine ⟨d + d', g * g', h * h', isMultiHomog_mul hg hg', isMultiHomog_mul hh hh', ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero h0 h0'
  · rw [map_mul, map_mul, e, e']; ring
  · rw [map_mul, map_mul, ev, ev']; ring

theorem HasVal.add {s t : Φ} {v w : L} (hv : HasVal y z s v) (hw : HasVal y z t w) : HasVal y z (s + t) (v + w) := by
  obtain ⟨d, g, h, hg, hh, h0, e, ev⟩ := hv
  obtain ⟨d', g', h', hg', hh', h0', e', ev'⟩ := hw
  refine ⟨d + d', g * h' + g' * h, h * h', isMultiHomog_add (isMultiHomog_mul hg hh') ?_, isMultiHomog_mul hh hh',
    ?_, ?_, ?_⟩
  · rw [add_comm]; exact isMultiHomog_mul hg' hh
  · rw [map_mul]; exact mul_ne_zero h0 h0'
  · rw [map_add, map_mul, map_mul, map_mul, e, e']; ring
  · rw [map_add, map_mul, map_mul, map_mul, ev, ev']; ring

theorem hasVal_intCast (n : ℤ) : HasVal y z (n : Φ) (n : L) :=
  ⟨0, C n, 1, isMultiHomog_C_zero n, isMultiHomog_one, by simp, by simp, by simp⟩

theorem hasVal_zero : HasVal y z 0 0 := by simpa using hasVal_intCast (y := y) (z := z) 0

theorem hasVal_one : HasVal y z 1 1 := by simpa using hasVal_intCast (y := y) (z := z) 1

theorem HasVal.neg {s : Φ} {v : L} (hv : HasVal y z s v) : HasVal y z (-s) (-v) := by
  simpa using (hasVal_intCast (y := y) (z := z) (-1)).mul hv

theorem HasVal.sub {s t : Φ} {v w : L} (hv : HasVal y z s v) (hw : HasVal y z t w) : HasVal y z (s - t) (v - w) := by
  simpa [sub_eq_add_neg] using hv.add hw.neg

theorem HasVal.ne_zero (hz : IsPt y z) {s : Φ} {v : L} (hv : HasVal y z s v) (h0 : v ≠ 0) : s ≠ 0 := by
  rintro rfl
  exact h0 (hv.unique hz hasVal_zero)

theorem HasVal.inv (hz : IsPt y z) {s : Φ} {v : L} (hv : HasVal y z s v) (hv0 : v ≠ 0) : HasVal y z s⁻¹ v⁻¹ := by
  have hs := hv.ne_zero hz hv0
  obtain ⟨d, g, h, hg, hh, h0, e, ev⟩ := hv
  refine ⟨d, h, g, hh, hg, by rw [ev]; exact mul_ne_zero hv0 h0, ?_, ?_⟩
  · rw [e, inv_mul_cancel_left₀ hs]
  · rw [ev, inv_mul_cancel_left₀ hv0]

theorem HasVal.div (hz : IsPt y z) {s t : Φ} {v w : L} (hv : HasVal y z s v) (hw : HasVal y z t w) (hw0 : w ≠ 0) :
    HasVal y z (s / t) (v / w) := by
  simpa [div_eq_mul_inv] using hv.mul (hw.inv hz hw0)

theorem HasVal.sum {σ : Type} (S : Finset σ) {s : σ → Φ} {v : σ → L} (h : ∀ a ∈ S, HasVal y z (s a) (v a)) :
    HasVal y z (∑ a ∈ S, s a) (∑ a ∈ S, v a) := by
  induction S using Finset.induction_on with
  | empty => simpa using hasVal_zero
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem HasVal.prod {σ : Type} (S : Finset σ) {s : σ → Φ} {v : σ → L} (h : ∀ a ∈ S, HasVal y z (s a) (v a)) :
    HasVal y z (∏ a ∈ S, s a) (∏ a ∈ S, v a) := by
  induction S using Finset.induction_on with
  | empty => simpa using hasVal_one
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem HasVal.pow {s : Φ} {v : L} (hv : HasVal y z s v) (n : ℕ) : HasVal y z (s ^ n) (v ^ n) := by
  simpa using HasVal.prod (Finset.range n) (s := fun _ => s) (v := fun _ => v) fun _ _ => hv

theorem HasVal.zpow (hz : IsPt y z) {s : Φ} {v : L} (hv : HasVal y z s v) (h0 : v ≠ 0) (n : ℤ) :
    HasVal y z (s ^ n) (v ^ n) := by
  cases n with
  | ofNat n => simpa using hv.pow n
  | negSucc n => simpa using (hv.pow (n + 1)).inv hz (pow_ne_zero _ h0)

theorem hasVal_form (hz : IsPt y z) {g h : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) (hh : IsMultiHomog h d)
    (h0 : aeval z h ≠ 0) : HasVal y z (aeval y g / aeval y h) (aeval z g / aeval z h) :=
  ⟨d, g, h, hg, hh, h0, (div_mul_cancel₀ _ (hz.aeval_ne hh h0)).symm, (div_mul_cancel₀ _ h0).symm⟩

theorem hasVal_ratio (hz : IsPt y z) {k : K} (m c : ι k) (hc : z ⟨k, c⟩ ≠ 0) :
    HasVal y z (y ⟨k, m⟩ / y ⟨k, c⟩) (z ⟨k, m⟩ / z ⟨k, c⟩) := by
  simpa using hasVal_form hz (isMultiHomog_X ⟨k, m⟩) (isMultiHomog_X ⟨k, c⟩) (by rwa [aeval_X])

theorem hasVal_self_eq {s v : Φ} (h : HasVal y y s v) : v = s := by
  obtain ⟨d, g, h, -, -, h1, e, ev⟩ := h
  exact mul_right_cancel₀ h1 (ev.symm.trans e)

theorem exists_hasVal_of_regAt {s : Φ} (hs : RegAt y (mCoordIdeal z) s) : ∃ v, HasVal y z s v := by
  obtain ⟨d, g, h, hg, hh, hn, e⟩ := hs
  have h0 : aeval z h ≠ 0 := fun e => hn ((mem_iff_of_homog hh).2 e)
  exact ⟨aeval z g / aeval z h, d, g, h, hg, hh, h0, e, (div_mul_cancel₀ _ h0).symm⟩

def regO (y : (Σ k, ι k) → Φ) (z : (Σ k, ι k) → L) : Subring Φ where
  carrier := {s | ∃ v, HasVal y z s v}
  mul_mem' := fun ⟨_, h⟩ ⟨_, h'⟩ => ⟨_, h.mul h'⟩
  one_mem' := ⟨_, hasVal_one⟩
  add_mem' := fun ⟨_, h⟩ ⟨_, h'⟩ => ⟨_, h.add h'⟩
  zero_mem' := ⟨_, hasVal_zero⟩
  neg_mem' := fun ⟨_, h⟩ => ⟨_, h.neg⟩

theorem mem_regO {s : Φ} : s ∈ regO y z ↔ ∃ v, HasVal y z s v := Iff.rfl

def valO (hz : IsPt y z) : regO y z →+* L where
  toFun s := s.2.choose
  map_one' := (Exists.choose_spec (1 : regO y z).2).unique hz hasVal_one
  map_mul' s t := (Exists.choose_spec (s * t).2).unique hz (s.2.choose_spec.mul t.2.choose_spec)
  map_zero' := (Exists.choose_spec (0 : regO y z).2).unique hz hasVal_zero
  map_add' s t := (Exists.choose_spec (s + t).2).unique hz (s.2.choose_spec.add t.2.choose_spec)

theorem hasVal_valO (hz : IsPt y z) (s : regO y z) : HasVal y z s (valO hz s) := s.2.choose_spec

theorem valO_eq (hz : IsPt y z) (s : regO y z) {v : L} (h : HasVal y z s v) : valO hz s = v :=
  (hasVal_valO hz s).unique hz h

theorem isUnit_of_valO (hz : IsPt y z) (s : regO y z) (h : valO hz s ≠ 0) : IsUnit s :=
  IsUnit.of_mul_eq_one ⟨(s : Φ)⁻¹, _, (hasVal_valO hz s).inv hz h⟩
    (Subtype.ext (mul_inv_cancel₀ ((hasVal_valO hz s).ne_zero hz h)))

theorem isLocalRing_regO (hz : IsPt y z) : IsLocalRing (regO y z) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun s => ?_
  by_cases h : valO hz s = 0
  · exact Or.inr (isUnit_of_valO hz _ (by rw [map_sub, map_one, h, sub_zero]; exact one_ne_zero))
  · exact Or.inl (isUnit_of_valO hz _ h)

theorem HasVal.pull {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
    {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v) (φ : Φ →+* Φ') {y' : (Σ k, ι' k) → Φ'}
    (hy : y' ∘ v = φ ∘ y) {z' : (Σ k, ι' k) → L} {s : Φ} {w : L} (h : HasVal y (z' ∘ v) s w) :
    HasVal y' z' (φ s) w := by
  obtain ⟨d, g, h, hg, hh, h0, e, ev⟩ := h
  refine ⟨_, rename v g, rename v h, CPts.isMultiHomog_rename_block hb hg, CPts.isMultiHomog_rename_block hb hh,
    by rwa [aeval_rename], ?_, by rwa [aeval_rename, aeval_rename]⟩
  rw [aeval_rename, aeval_rename, hy, CPts.aeval_comp_ringHom, CPts.aeval_comp_ringHom, e, map_mul]

theorem IsPt.comp {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
    {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v) (φ : Φ →+* Φ') {y' : (Σ k, ι' k) → Φ'}
    (hy : y' ∘ v = φ ∘ y) {z' : (Σ k, ι' k) → L} (hz : IsPt y' z') : IsPt y (z' ∘ v) := by
  refine isPt_of_homog (fun k => ?_) fun f d hf h0 => ?_
  · obtain ⟨i, hi⟩ := hz.1 (κ k)
    obtain ⟨⟨k', i'⟩, e⟩ := hb.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
    have : k' = k := hb.1 (by have := hb.2.2.1 ⟨k', i'⟩; rw [e] at this; exact this.symm)
    subst this
    exact ⟨i', by show z' (v _) ≠ 0; rwa [e]⟩
  · rw [← aeval_rename]
    refine hz.2 _ ((mem_iff_of_homog (CPts.isMultiHomog_rename_block hb hf)).2 ?_)
    rw [aeval_rename, hy, CPts.aeval_comp_ringHom, h0, map_zero]

theorem eval_map_eq_aeval (z : (Σ k, ι k) → ℂ) (f : MRing ι) : eval z (map (Int.castRingHom ℂ) f) = aeval z f := by
  rw [eval_map, aeval_def]; rfl

theorem isPt_iff_mem_mcPts {z : (Σ k, ι k) → ℂ} : IsPt y z ↔ z ∈ mcPts (mCoordIdeal y) := by
  simp only [IsPt, mcPts, Set.mem_setOf_eq, eval_map_eq_aeval]

theorem hasVal_valAt {z : (Σ k, ι k) → ℂ} (hz : IsPt y z) {s : Φ} (hs : RegAt y (mCoordIdeal z) s) :
    HasVal y z s (valAt y s z) := by
  obtain ⟨v, d, g, h, hg, hh, h0, e, ev⟩ := exists_hasVal_of_regAt hs
  have : IsValueAt y s z v := ⟨d, g, h, hg, hh, hz.aeval_ne hh h0, e, by rwa [eval_map_eq_aeval], by
    rw [eval_map_eq_aeval, eval_map_eq_aeval, ev, mul_div_cancel_right₀ _ h0]⟩
  rw [valAt_eq (isPt_iff_mem_mcPts.1 hz) this]
  exact ⟨d, g, h, hg, hh, h0, e, ev⟩

section Flag

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)

def colsB (N j : ℕ) (a ca cb : Fin N) : Finset (Fin N) := insert cb ((stepCols N j a).erase ca)

def vecB (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (m : ι k₀) : Φ :=
  ∑ I, algebraMap M.Ω Φ (M.coef ⟨k₀, m⟩ I) * minorIJ (M.g τ) I (colsB N j a ca cb)

def cFac (τ : Ψ) (a : Fin N) : Φ :=
  ∏ p, (if IsProperStep N j p.2 then 1 else algebraMap M.Ω Φ (M.lam p) * (if (p.2 : ℕ) + 1 = j then
    (if (a : ℕ) < j then minorIJ (M.g p.1) (wIdx N j) (wIdx N j) else 1) else
      minorIJ (M.g p.1) (omIdx N j) (omIdx N j))) ^ xiCoef τ a p

def eDeg (τ : Ψ) (a : Fin N) (k₀ : K) (k : K) : ℤ :=
  -(∑ p, xiCoef τ a p * M.dy p k) - if k = k₀ then 2 else 0

end Flag

end PositivityTheory.Xgp.W
