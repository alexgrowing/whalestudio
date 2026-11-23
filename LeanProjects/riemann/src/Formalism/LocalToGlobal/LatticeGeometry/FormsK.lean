import Formalism.LocalToGlobal.LatticeGeometry.LevPrPrime
import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.FormData

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open scoped ComplexOrder

namespace Formalism.L2.Geo

section Abs

variable {K : Type} [Field K] [NumberField K]

def expV (b : ℝ) (e : EReal) : ℝ := if e = ⊤ then 0 else b ^ (-e.toReal)

theorem expV_top (b : ℝ) : expV b ⊤ = 0 := by simp [expV]

theorem expV_coe (b x : ℝ) : expV b (x : EReal) = b ^ (-x) := by simp [expV]

theorem expV_nonneg {b : ℝ} (hb : 0 < b) (e : EReal) : 0 ≤ expV b e := by
  unfold expV; split_ifs
  · exact le_rfl
  · exact (Real.rpow_pos_of_pos hb _).le

theorem expV_eq_zero {b : ℝ} (hb : 0 < b) {e : EReal} : expV b e = 0 ↔ e = ⊤ := by
  unfold expV; split_ifs with h
  · simp [h]
  · simp [h, (Real.rpow_pos_of_pos hb _).ne']

theorem expV_anti {b : ℝ} (hb : 1 ≤ b) {e e' : EReal} (he : e ≠ ⊥) (h : e ≤ e') : expV b e' ≤ expV b e := by
  induction e' using EReal.rec with
  | bot => exact absurd (le_bot_iff.mp h) he
  | top => rw [expV_top]; exact expV_nonneg (by linarith) e
  | coe y =>
    induction e using EReal.rec with
    | bot => exact absurd rfl he
    | top => exact absurd h (by simp)
    | coe x =>
      rw [expV_coe, expV_coe]
      exact Real.rpow_le_rpow_of_exponent_le hb (by have := EReal.coe_le_coe_iff.mp h; linarith)

theorem expV_add {b : ℝ} (hb : 0 < b) {e e' : EReal} (he : e ≠ ⊥) (he' : e' ≠ ⊥) :
    expV b (e + e') = expV b e * expV b e' := by
  induction e using EReal.rec with
  | bot => exact absurd rfl he
  | top => rw [EReal.top_add_of_ne_bot he', expV_top, zero_mul]
  | coe x =>
    induction e' using EReal.rec with
    | bot => exact absurd rfl he'
    | top => rw [EReal.coe_add_top, expV_top, mul_zero]
    | coe y => rw [← EReal.coe_add, expV_coe, expV_coe, expV_coe, neg_add, Real.rpow_add hb]

theorem expV_min {b : ℝ} (hb : 1 ≤ b) {e e' : EReal} (he : e ≠ ⊥) (he' : e' ≠ ⊥) :
    expV b (min e e') = max (expV b e) (expV b e') := by
  rcases le_total e e' with h | h
  · rw [min_eq_left h, max_eq_left (expV_anti hb he h)]
  · rw [min_eq_right h, max_eq_right (expV_anti hb he' h)]

def nrmP (la : HeightOneSpectrum (𝓞 K)) : ℝ := (Ideal.absNorm la.asIdeal : ℝ)

theorem one_lt_nrmP (la : HeightOneSpectrum (𝓞 K)) : 1 < nrmP la := by
  unfold nrmP
  have h1 : Ideal.absNorm la.asIdeal ≠ 0 := fun h => la.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h2 : Ideal.absNorm la.asIdeal ≠ 1 := fun h => la.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  exact_mod_cast (by omega : 1 < Ideal.absNorm la.asIdeal)

theorem min_vEK_ne_bot (la : HeightOneSpectrum (𝓞 K)) (a b : K) : min (vEK la a) (vEK la b) ≠ ⊥ := by
  rcases min_choice (vEK la a) (vEK la b) with h | h <;> rw [h] <;> exact vEK_ne_bot la _

def avP (la : HeightOneSpectrum (𝓞 K)) : AbsoluteValue K ℝ where
  toFun a := expV (nrmP la) (vEK la a)
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha, vEK_zero, expV_top]
    show expV (nrmP la) (vEK la (a * b)) = expV (nrmP la) (vEK la a) * expV (nrmP la) (vEK la b)
    rw [vEK_mul la ha, vEK_of_ne la ha,
      expV_add (by linarith [one_lt_nrmP la]) (EReal.coe_ne_bot _) (vEK_ne_bot la b)]
  nonneg' a := expV_nonneg (by linarith [one_lt_nrmP la]) _
  eq_zero' a := by
    show expV (nrmP la) (vEK la a) = 0 ↔ a = 0
    rw [expV_eq_zero (by linarith [one_lt_nrmP la])]
    constructor
    · intro h; by_contra ha; rw [vEK_of_ne la ha] at h; exact EReal.coe_ne_top _ h
    · rintro rfl; exact vEK_zero la
  add_le' a b := by
    show expV (nrmP la) (vEK la (a + b)) ≤ expV (nrmP la) (vEK la a) + expV (nrmP la) (vEK la b)
    have hb := one_lt_nrmP la
    calc expV (nrmP la) (vEK la (a + b)) ≤ expV (nrmP la) (min (vEK la a) (vEK la b)) :=
          expV_anti hb.le (min_vEK_ne_bot la a b) (vEK_add la a b)
      _ = max (expV (nrmP la) (vEK la a)) (expV (nrmP la) (vEK la b)) :=
          expV_min hb.le (vEK_ne_bot la a) (vEK_ne_bot la b)
      _ ≤ _ := max_le_add_of_nonneg (expV_nonneg (by linarith) _) (expV_nonneg (by linarith) _)

theorem adicAbv_apply (la : HeightOneSpectrum (𝓞 K)) (a : K) : avP la a = expV (nrmP la) (vEK la a) := rfl

theorem adicAbv_coe_le_one₂ (la : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) : avP la (a : K) ≤ 1 := by
  rw [adicAbv_apply]
  by_cases ha : (a : K) = 0
  · rw [ha, vEK_zero, expV_top]; exact zero_le_one
  · rw [vEK_of_ne la ha, expV_coe]
    have h := fv_vAdd_nonneg la ha
    exact Real.rpow_le_one_of_one_le_of_nonpos (one_lt_nrmP la).le (by
      have : (0 : ℝ) ≤ ((vAdd la (a : K) : ℤ) : ℝ) := by exact_mod_cast h
      linarith)

end Abs

namespace FormsPkg

variable {D : D7} {G : DV.Geo D.what₂.LL} {NW : ℕ → ℕ} {CompW : ℕ → Type} [∀ j, Fintype (CompW j)]
  {algW : ∀ j, AlgPkg G D.what₂.Tau (NW j) (CompW j)} {PtY : ℕ → ℕ → Type}
  (P : FormsPkg D G NW CompW algW PtY)

theorem scal_mul {j : ℕ} (x y : P.FormsS j) : P.scal (x * y) = P.scal x * P.scal y := by
  classical
  unfold FormsPkg.scal
  have hs : ∀ p : WithZero (WeightFamilies.Wt D j) × WithZero (WeightFamilies.Wt D j),
      p ∈ ({((0 : WithZero (WeightFamilies.Wt D j)), (0 : WithZero (WeightFamilies.Wt D j)))} : Finset _) ↔ p.1 + p.2 = 0 := by
    rintro ⟨a, b⟩
    simp only [Finset.mem_singleton, Prod.mk.injEq]
    induction a using WithZero.recZeroCoe <;> induction b using WithZero.recZeroCoe <;>
      simp [← WithZero.coe_add]
  rw [Subalgebra.coe_mul, AddMonoidAlgebra.coeff_mul_antidiag _ _ 0 _ (fun {p} => hs p), Finset.sum_singleton, Prod.fst_mul]

def scalL (j : ℕ) : P.Forms j →ₗ[P.KO] P.KO where
  toFun x := P.scal (x : P.FormsS j)
  map_add' x y := P.scal_add x y
  map_smul' a x := P.scal_smul a x

def cuspF (j : ℕ) : Submodule P.KO (P.Forms j) := LinearMap.ker (P.scalL j)

theorem mem_cuspF {j : ℕ} (x : P.Forms j) : x ∈ P.cuspF j ↔ P.scal (x : P.FormsS j) = 0 := Iff.rfl

theorem cuspF_mul {j : ℕ} (f u : P.Forms j) (hf : f ∈ P.cuspF j) : f * u ∈ P.cuspF j := by
  rw [mem_cuspF] at hf ⊢
  exact (P.scal_mul f u).trans (by rw [hf, zero_mul])

theorem inc_mem_cuspF {j : ℕ} {w : WeightFamilies.Wt D j} (F : P.Cusp j w) : P.inc j w F ∈ P.cuspF j :=
  P.scal_incS F

variable {j : ℕ}

open Classical in

def suppW (x : P.Forms j) : Finset (WeightFamilies.Wt D j) :=
  (P.amb x).coeff.support.preimage (fun w => (w : WithZero (WeightFamilies.Wt D j))) WithZero.coe_injective.injOn

theorem amb_sum {ι : Type} (s : Finset ι) (f : ι → P.Forms j) :
    P.amb (∑ i ∈ s, f i) = ∑ i ∈ s, P.amb (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, P.amb_add, ih]

theorem amb_alg (a : P.KO) : P.amb (algebraMap P.KO (P.Forms j) a) = algebraMap P.KO (P.Amb j) a := rfl

theorem coeff_zero_eq (x : P.Forms j) :
    (P.amb x).coeff 0 = algebraMap P.KO (P.Coef j) (P.scal (x : P.FormsS j)) := by
  obtain ⟨a, ha⟩ := (P.mem_Vm_zero _).mp ((x : P.FormsS j).2 0)
  have h1 : P.scal (x : P.FormsS j) = a := by
    have h := congrArg Prod.fst ha
    simp only [Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h
    exact h.symm
  rw [h1]; exact ha.symm

theorem coeff_coe_eq (x : P.Forms j) (w : WeightFamilies.Wt D j) :
    (P.amb x).coeff (w : WithZero (WeightFamilies.Wt D j)) = P.tup j w (P.Fof w (x : P.FormsS j)) :=
  (P.tup_Fof w x).symm

theorem decomp (x : P.Forms j) :
    x = algebraMap P.KO (P.Forms j) (P.scal (x : P.FormsS j)) +
      ∑ w ∈ P.suppW x, P.inc j w (P.Fof w (x : P.FormsS j)) := by
  classical
  apply P.amb_injective
  rw [P.amb_add, amb_alg, amb_sum]
  refine AddMonoidAlgebra.ext (Finsupp.ext fun m => ?_)
  rw [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sum, Finsupp.add_apply, Finsupp.finsetSum_apply]
  simp only [P.amb_inc, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply]
  induction m using WithZero.recZeroCoe with
  | zero =>
    rw [coeff_zero_eq]
    simp [Finsupp.single_apply]
  | coe w =>
    rw [coeff_coe_eq]
    simp only [Finsupp.single_apply, WithZero.coe_inj, WithZero.zero_ne_coe, if_false, zero_add]
    rw [Finset.sum_ite_eq']
    split_ifs with hw
    · rfl
    · have : (P.amb x).coeff (w : WithZero (WeightFamilies.Wt D j)) = 0 := by
        simpa [suppW, Finsupp.mem_support_iff] using hw
      rw [← coeff_coe_eq, this]

theorem scal_alg (a : P.KO) : P.scal ((algebraMap P.KO (P.Forms j) a : P.Forms j) : P.FormsS j) = a := by
  show ((algebraMap P.KO (P.Amb j) a).coeff 0).1 = a
  simp [AddMonoidAlgebra.coe_algebraMap, Prod.algebraMap_apply]

theorem act_scal_of {H : Type} [Group H] [MulSemiringAction H (P.Forms j)]
    (hs : ∀ (h : H) (a : P.KO) (x : P.Forms j), h • (a • x) = a • (h • x))
    (hw : ∀ (h : H) (w : WeightFamilies.Wt D j) (F : P.Cusp j w), ∃ F' : P.Cusp j w, h • P.inc j w F = P.inc j w F')
    (h : H) (x : P.Forms j) :
    P.scal ((h • x : P.Forms j) : P.FormsS j) = P.scal (x : P.FormsS j) := by
  classical
  have hx := P.decomp x
  have h1 : h • algebraMap P.KO (P.Forms j) (P.scal (x : P.FormsS j)) =
      algebraMap P.KO (P.Forms j) (P.scal (x : P.FormsS j)) := by
    rw [Algebra.algebraMap_eq_smul_one, hs, smul_one]
  have h2 : ∀ w, P.scalL j (h • P.inc j w (P.Fof w (x : P.FormsS j))) = 0 := by
    intro w
    obtain ⟨F', hF'⟩ := hw h w (P.Fof w (x : P.FormsS j))
    rw [hF']; exact P.scal_incS F'
  have key : P.scalL j (h • x) = P.scalL j x := by
    conv_lhs => rw [hx]
    rw [smul_add, Finset.smul_sum, map_add, map_sum, h1]
    simp only [h2, Finset.sum_const_zero, add_zero]
    show P.scal _ = P.scal _
    rw [scal_alg]
  exact key

section Gauss

variable (la : HeightOneSpectrum (𝓞 P.KO)) (y : P.Pt j la)

theorem le_vAt_add {c : EReal} {p q : P.Forms j} (h1 : c ≤ P.vAt la y p) (h2 : c ≤ P.vAt la y q) :
    c ≤ P.vAt la y (p + q) := (le_min h1 h2).trans (P.vAt_add la y p q)

theorem vAt_alg (a : P.KO) : P.vAt la y (algebraMap P.KO (P.Forms j) a) = vEK la a := by
  show min (vEK la (P.scal _)) (⨅ w, P.vAtC j la y w (P.Fof w _)) = _
  have h0 : ∀ w, P.Fof w ((algebraMap P.KO (P.Forms j) a : P.Forms j) : P.FormsS j) = 0 := fun w => by
    apply P.Fof_eq_zero_of_coeff
    show (algebraMap P.KO (P.Amb j) a).coeff (w : WithZero (WeightFamilies.Wt D j)) = 0
    simp [AddMonoidAlgebra.coe_algebraMap, Finsupp.single_apply]
  simp only [h0, P.vAtC_zero, iInf_top, scal_alg]
  exact min_eq_left le_top

theorem vAt_le_scal (x : P.Forms j) : P.vAt la y x ≤ vEK la (P.scal (x : P.FormsS j)) := min_le_left _ _

theorem vAt_le_part (x : P.Forms j) (w : WeightFamilies.Wt D j) :
    P.vAt la y x ≤ P.vAt la y (P.inc j w (P.Fof w (x : P.FormsS j))) := by
  rw [P.vAt_inc]; exact (min_le_right _ _).trans (iInf_le _ w)

theorem smul_ge (a : P.KO) (z : P.Forms j) : vEK la a + P.vAt la y z ≤ P.vAt la y (a • z) := by
  by_cases ha : a = 0
  · subst ha; rw [zero_smul, P.vAt_zero]; exact le_top
  · rw [P.vAt_smul la y a z ha, vEK_of_ne la ha]

theorem smul_ge' (a : P.KO) (z : P.Forms j) :
    vEK la a + P.vAt la y z ≤ P.vAt la y (algebraMap P.KO (P.Forms j) a * z) := by
  rw [← Algebra.smul_def]; exact P.smul_ge la y a z

theorem le_vAt_mul_sum {c : EReal} (A : P.Forms j) {κ : Type} (t : Finset κ) (g : κ → P.Forms j)
    (h : ∀ u ∈ t, c ≤ P.vAt la y (A * g u)) : c ≤ P.vAt la y (A * ∑ u ∈ t, g u) := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.sum_empty, mul_zero, P.vAt_zero]; exact le_top
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, mul_add]
    exact P.le_vAt_add la y (h a (Finset.mem_insert_self a t))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem le_vAt_sum_mul {c : EReal} (B : P.Forms j) {ι : Type} (s : Finset ι) (f : ι → P.Forms j)
    (h : ∀ w ∈ s, c ≤ P.vAt la y (f w * B)) : c ≤ P.vAt la y ((∑ w ∈ s, f w) * B) := by
  rw [mul_comm]; exact P.le_vAt_mul_sum la y B s f fun w hw => by rw [mul_comm]; exact h w hw

theorem expand_le {c : EReal} (A B : P.Forms j) {ι κ : Type} (s : Finset ι) (t : Finset κ)
    (f : ι → P.Forms j) (g : κ → P.Forms j) (h1 : c ≤ P.vAt la y (A * B))
    (h2 : ∀ u ∈ t, c ≤ P.vAt la y (A * g u)) (h3 : ∀ w ∈ s, c ≤ P.vAt la y (f w * B))
    (h4 : ∀ w ∈ s, ∀ u ∈ t, c ≤ P.vAt la y (f w * g u)) :
    c ≤ P.vAt la y ((A + ∑ w ∈ s, f w) * (B + ∑ u ∈ t, g u)) := by
  rw [add_mul, mul_add, mul_add]
  exact P.le_vAt_add la y (P.le_vAt_add la y h1 (P.le_vAt_mul_sum la y A t g h2))
    (P.le_vAt_add la y (P.le_vAt_sum_mul la y B s f h3)
      (P.le_vAt_sum_mul la y _ s f fun w hw => P.le_vAt_mul_sum la y _ t g (h4 w hw)))

theorem vAt_mul_le (x x' : P.Forms j) : P.vAt la y x + P.vAt la y x' ≤ P.vAt la y (x * x') := by
  classical
  have hA : P.vAt la y x ≤ vEK la (P.scal (x : P.FormsS j)) := P.vAt_le_scal la y x
  have hB : P.vAt la y x' ≤ vEK la (P.scal (x' : P.FormsS j)) := P.vAt_le_scal la y x'
  have e : x * x' = (algebraMap P.KO (P.Forms j) (P.scal (x : P.FormsS j)) +
      ∑ w ∈ P.suppW x, P.inc j w (P.Fof w (x : P.FormsS j))) *
      (algebraMap P.KO (P.Forms j) (P.scal (x' : P.FormsS j)) +
      ∑ u ∈ P.suppW x', P.inc j u (P.Fof u (x' : P.FormsS j))) := by
    rw [← P.decomp x, ← P.decomp x']
  rw [e]
  refine P.expand_le la y _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · refine (add_le_add hA hB).trans ?_
    rw [← P.vAt_alg la y (P.scal (x' : P.FormsS j))]; exact P.smul_ge' la y _ _
  · exact fun u _ => (add_le_add hA (P.vAt_le_part la y x' u)).trans (P.smul_ge' la y _ _)
  · intro w _
    rw [mul_comm]
    refine (add_le_add (P.vAt_le_part la y x w) hB).trans ?_
    rw [add_comm]; exact P.smul_ge' la y _ _
  · intro w _ u _
    rw [P.vAt_mul]
    exact add_le_add (P.vAt_le_part la y x w) (P.vAt_le_part la y x' u)

end Gauss

end FormsPkg

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}

open Classical in

structure FormsKPkg (F : ShimFam D G Lev) : Type 1 where

  κs : Lev

  fs : FormsPkg D G (fun j => (datW D κs j).N) (fun j => (F.U (datW D κs j)).Comp)
    (fun j => (F.U (datW D κs j)).alg)
    (fun j p => ((F.U (datW D κs j)).pad.loc p).Pt ((F.U (datW D κs j)).pad.loc p).YY)

  Hb : Type
  [grpHb : Group Hb]
  [act : ∀ j, MulSemiringAction Hb (fs.Forms j)]

  act_smul : ∀ j (h : Hb) (a : fs.KO) (x : fs.Forms j), h • (a • x) = a • (h • x)

  act_wt : ∀ j (h : Hb) (w : WeightFamilies.Wt D j) (F : fs.Cusp j w), ∃ F' : fs.Cusp j w, h • fs.inc j w F = fs.inc j w F'

  mv : ∀ j (la : HeightOneSpectrum (𝓞 fs.KO)), Hb → fs.Pt j la → fs.Pt j la

  vAt_act : ∀ j la (h : Hb) (y : fs.Pt j la) (x : fs.Forms j), fs.vAt la y (h • x) = fs.vAt la (mv j la h y) x

  ip : ∀ j, (fs.KO →+* ℂ) → fs.Forms j → fs.Forms j → ℂ
  ip_add_left : ∀ j σ (f f' g : fs.Forms j), f ∈ fs.cuspF j → f' ∈ fs.cuspF j → g ∈ fs.cuspF j →
    ip j σ (f + f') g = ip j σ f g + ip j σ f' g
  ip_add_right : ∀ j σ (f g g' : fs.Forms j), f ∈ fs.cuspF j → g ∈ fs.cuspF j → g' ∈ fs.cuspF j →
    ip j σ f (g + g') = ip j σ f g + ip j σ f g'
  ip_smul_left : ∀ j σ (a : fs.KO) (f g : fs.Forms j), f ∈ fs.cuspF j → g ∈ fs.cuspF j →
    ip j σ (a • f) g = star (σ a) * ip j σ f g
  ip_smul_right : ∀ j σ (a : fs.KO) (f g : fs.Forms j), f ∈ fs.cuspF j → g ∈ fs.cuspF j →
    ip j σ f (a • g) = σ a * ip j σ f g
  ip_conj : ∀ j σ (f g : fs.Forms j), f ∈ fs.cuspF j → g ∈ fs.cuspF j → ip j σ g f = star (ip j σ f g)
  ip_nonneg : ∀ j σ (f : fs.Forms j), f ∈ fs.cuspF j → 0 ≤ (ip j σ f f).re

  ip_inc : ∀ j σ (w : WeightFamilies.Wt D j) (F : fs.Cusp j w), ip j σ (fs.inc j w F) (fs.inc j w F) = ((fs.l2NormAlt j w σ F ^ 2 : ℝ) : ℂ)

  ip_orth : ∀ j σ (w w' : WeightFamilies.Wt D j) (F : fs.Cusp j w) (F' : fs.Cusp j w'), w ≠ w' →
    ip j σ (fs.inc j w F) (fs.inc j w' F') = 0
  ip_act : ∀ j σ (h : Hb) (f g : fs.Forms j), f ∈ fs.cuspF j → g ∈ fs.cuspF j → ip j σ (h • f) (h • g) = ip j σ f g

  supv : ∀ j, (fs.KO →+* ℂ) → fs.Forms j → ℝ
  supv_inc : ∀ j σ (w : WeightFamilies.Wt D j) (F : fs.Cusp j w), supv j σ (fs.inc j w F) = fs.supN j w σ F
  supv_act : ∀ j σ (h : Hb) (u : fs.Forms j), supv j σ (h • u) = supv j σ u
  ip_mul : ∀ j σ (f u : fs.Forms j), f ∈ fs.cuspF j → u ∈ fs.cuspF j →
    (ip j σ (f * u) (f * u)).re ≤ supv j σ u ^ 2 * (ip j σ f f).re

  CmpK : ℕ → Type
  [cmpKFin : ∀ j, Fintype (CmpK j)]

  orbK : ∀ j, (F.U (datW D κs j)).Comp → CmpK j
  orbK_surj : ∀ j, Function.Surjective (orbK j)

  cmpPt : ∀ j la, fs.Pt j la → CmpK j

  prC : ∀ j, CmpK j → fs.cuspF j →ₗ[fs.KO] fs.cuspF j
  prC_sum : ∀ j (x : fs.cuspF j), ∑ c, prC j c x = x
  prC_orth : ∀ j c d (x : fs.cuspF j), c ≠ d → prC j c (prC j d x) = 0

  prC_inc : ∀ j o (w : WeightFamilies.Wt D j) (F : fs.Cusp j w), ∃ F' : fs.Cusp j w,
    (prC j o ⟨fs.inc j w F, fs.inc_mem_cuspF F⟩ : fs.Forms j) = fs.inc j w F' ∧
      ∀ c', fs.cmp j w c' F' = if orbK j c' = o then fs.cmp j w c' F else 0
  vAt_prC_self : ∀ j la (y : fs.Pt j la) (x : fs.cuspF j),
    fs.vAt la y (prC j (cmpPt j la y) x : fs.Forms j) = fs.vAt la y (x : fs.Forms j)
  vAt_prC_ne : ∀ j la (y : fs.Pt j la) c (x : fs.cuspF j), c ≠ cmpPt j la y → fs.vAt la y (prC j c x : fs.Forms j) = ⊤
  ip_prC : ∀ j σ c d (f g : fs.cuspF j), c ≠ d → ip j σ (prC j c f : fs.Forms j) (prC j d g : fs.Forms j) = 0

  ip_posDef : ∀ j σ (m : ℕ) (e : Fin m → fs.Forms j), (∀ a, e a ∈ fs.cuspF j) → LinearIndependent fs.KO e →
    (Matrix.of fun a c => ip j σ (e a) (e c)).PosDef

attribute [instance] FormsKPkg.grpHb FormsKPkg.act FormsKPkg.cmpKFin

namespace FormsKPkg

variable {F : ShimFam D G Lev} (P : FormsKPkg F)

def sn {j : ℕ} (la : HeightOneSpectrum (𝓞 P.fs.KO)) (y : P.fs.Pt j la) (x : P.fs.Forms j) : ℝ :=
  expV (nrmP la) (P.fs.vAt la y x)

theorem act_scal {j : ℕ} (h : P.Hb) (x : P.fs.Forms j) :
    P.fs.scal ((h • x : P.fs.Forms j) : P.fs.FormsS j) = P.fs.scal (x : P.fs.FormsS j) :=
  P.fs.act_scal_of (P.act_smul j) (P.act_wt j) h x

theorem cusp_act {j : ℕ} (h : P.Hb) (f : P.fs.Forms j) (hf : f ∈ P.fs.cuspF j) : h • f ∈ P.fs.cuspF j := by
  rw [FormsPkg.mem_cuspF] at hf ⊢
  rw [P.act_scal, hf]

def toFormData (j : ℕ) : ExtensionFiltration.FormData P.fs.KO (P.fs.Forms j) P.Hb where
  W := HeightOneSpectrum (𝓞 P.fs.KO)
  Pt := fun la => P.fs.Pt j la
  av := fun la => avP la
  av_int := fun la a => adicAbv_coe_le_one₂ la a
  sn := fun la y x => P.sn la y x
  sn_nonneg := fun la _ _ => expV_nonneg (by linarith [one_lt_nrmP la]) _
  sn_smul := fun la y a x => by
    show expV (nrmP la) (P.fs.vAt la y (a • x)) = avP la a * expV (nrmP la) (P.fs.vAt la y x)
    by_cases ha : a = 0
    · subst ha; rw [zero_smul, P.fs.vAt_zero, expV_top, map_zero, zero_mul]
    · rw [P.fs.vAt_smul la y a x ha, adicAbv_apply, vEK_of_ne la ha,
        expV_add (by linarith [one_lt_nrmP la]) (EReal.coe_ne_bot _) (P.fs.vAt_ne_bot la y x)]
  sn_add := fun la y x x' => by
    show expV (nrmP la) (P.fs.vAt la y (x + x')) ≤
      max (expV (nrmP la) (P.fs.vAt la y x)) (expV (nrmP la) (P.fs.vAt la y x'))
    have hb := one_lt_nrmP la
    have hne : min (P.fs.vAt la y x) (P.fs.vAt la y x') ≠ ⊥ := by
      rcases min_choice (P.fs.vAt la y x) (P.fs.vAt la y x') with h | h <;> rw [h] <;> exact P.fs.vAt_ne_bot la y _
    rw [← expV_min hb.le (P.fs.vAt_ne_bot la y x) (P.fs.vAt_ne_bot la y x')]
    exact expV_anti hb.le hne (P.fs.vAt_add la y x x')
  sn_mul := fun la y x x' => by
    show expV (nrmP la) (P.fs.vAt la y (x * x')) ≤
      expV (nrmP la) (P.fs.vAt la y x) * expV (nrmP la) (P.fs.vAt la y x')
    have hb := one_lt_nrmP la
    have hne : P.fs.vAt la y x + P.fs.vAt la y x' ≠ ⊥ :=
      EReal.add_ne_bot_iff.mpr ⟨P.fs.vAt_ne_bot la y x, P.fs.vAt_ne_bot la y x'⟩
    rw [← expV_add (by linarith) (P.fs.vAt_ne_bot la y x) (P.fs.vAt_ne_bot la y x')]
    exact expV_anti hb.le hne (P.fs.vAt_mul_le la y x x')
  mv := fun h la y => P.mv j la h y
  sn_act := fun h la y x => by
    show expV (nrmP la) (P.fs.vAt la y (h • x)) = expV (nrmP la) (P.fs.vAt la (P.mv j la h y) x)
    rw [P.vAt_act]
  cusp := P.fs.cuspF j
  cusp_act := fun h f hf => P.cusp_act h f hf
  cusp_mul := fun f u hf => P.fs.cuspF_mul f u hf
  ip := fun v => P.ip j v.embedding
  ip_add_left := fun v => P.ip_add_left j v.embedding
  ip_add_right := fun v => P.ip_add_right j v.embedding
  ip_smul_left := fun v => P.ip_smul_left j v.embedding
  ip_smul_right := fun v => P.ip_smul_right j v.embedding
  ip_conj := fun v => P.ip_conj j v.embedding
  ip_nonneg := fun v => P.ip_nonneg j v.embedding
  ip_act := fun v => P.ip_act j v.embedding
  supv := fun v => P.supv j v.embedding
  supv_act := fun v => P.supv_act j v.embedding
  ip_mul := fun v => P.ip_mul j v.embedding

def toFormDataG (j : ℕ) : ExtensionFiltration.FormDataG P.fs.KO (P.fs.Forms j) P.Hb where
  toFormData := P.toFormData j
  ip_posDef := fun v => P.ip_posDef j v.embedding

theorem comp_laws (j : ℕ) :
    (∀ x : P.fs.cuspF j, ∑ c, P.prC j c x = x) ∧
    (∀ c d (x : P.fs.cuspF j), c ≠ d → P.prC j c (P.prC j d x) = 0) ∧
    (∀ la (y : P.fs.Pt j la) (x : P.fs.cuspF j),
      (P.toFormData j).sn la y (P.prC j (P.cmpPt j la y) x : P.fs.Forms j) = (P.toFormData j).sn la y x) ∧
    (∀ la (y : P.fs.Pt j la) c (x : P.fs.cuspF j), c ≠ P.cmpPt j la y →
      (P.toFormData j).sn la y (P.prC j c x : P.fs.Forms j) = 0) ∧
    (∀ v c d (f g : P.fs.cuspF j), c ≠ d →
      (P.toFormData j).ip v (P.prC j c f : P.fs.Forms j) (P.prC j d g : P.fs.Forms j) = 0) := by
  refine ⟨P.prC_sum j, P.prC_orth j, fun la y x => ?_, fun la y c x hc => ?_, fun v c d f g h => P.ip_prC j _ c d f g h⟩
  · show expV _ _ = expV _ _
    rw [P.vAt_prC_self]
  · show expV _ _ = 0
    rw [P.vAt_prC_ne j la y c x hc, expV_top]

end FormsKPkg

end Formalism.L2.Geo
