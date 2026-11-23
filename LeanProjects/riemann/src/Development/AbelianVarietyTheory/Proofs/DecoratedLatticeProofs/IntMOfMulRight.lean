import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CongAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantThird
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralPowerExpansion
import Formalism.LocalToGlobal.Columns.ChainInst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Transport.Last

section Val

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

def IntM {a b : Type} (M : Matrix a b K) : Prop := ∀ i j, v (M i j) ≤ 1

def SmallM {a b : Type} (M : Matrix a b K) : Prop := ∀ i j, v (M i j) < 1

variable {v} {a b c : Type}

theorem SmallM.int {M : Matrix a b K} (h : SmallM v M) : IntM v M := fun i j => (h i j).le

theorem IntM.add {M N : Matrix a b K} (h : IntM v M) (h' : IntM v N) : IntM v (M + N) :=
  fun i j => v.map_add_le (h i j) (h' i j)

theorem IntM.sub {M N : Matrix a b K} (h : IntM v M) (h' : IntM v N) : IntM v (M - N) :=
  fun i j => v.map_sub_le (h i j) (h' i j)

theorem SmallM.add {M N : Matrix a b K} (h : SmallM v M) (h' : SmallM v N) : SmallM v (M + N) :=
  fun i j => v.map_add_lt (h i j) (h' i j)

theorem SmallM.sub {M N : Matrix a b K} (h : SmallM v M) (h' : SmallM v N) : SmallM v (M - N) :=
  fun i j => v.map_sub_lt (h i j) (h' i j)

theorem IntM.mul [Fintype b] {M : Matrix a b K} {N : Matrix b c K} (h : IntM v M) (h' : IntM v N) : IntM v (M * N) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact v.map_sum_le fun l _ => by rw [map_mul]; exact mul_le_one' (h i l) (h' l j)

theorem SmallM.mul_int [Fintype b] {M : Matrix a b K} {N : Matrix b c K} (h : SmallM v M) (h' : IntM v N) :
    SmallM v (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact v.map_sum_lt one_ne_zero fun l _ => by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right' (h' l j)) (h i l)

theorem IntM.mul_small [Fintype b] {M : Matrix a b K} {N : Matrix b c K} (h : IntM v M) (h' : SmallM v N) :
    SmallM v (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact v.map_sum_lt one_ne_zero fun l _ => by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (h i l)) (h' l j)

theorem intM_one [DecidableEq a] : IntM v (1 : Matrix a a K) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem intM_of_near [DecidableEq a] {A : Matrix a a K} (h : SmallM v (A - 1)) : IntM v A := by
  simpa using h.int.add intM_one

theorem intM_of_mul_left [Fintype a] [DecidableEq a] {A : Matrix a a K} (h : SmallM v (A - 1)) {Y : Matrix a b K}
    (hY : IntM v (A * Y)) : IntM v Y := by
  intro i j
  obtain ⟨l, -, hl⟩ := Finset.exists_max_image Finset.univ (fun l => v (Y l j)) ⟨i, Finset.mem_univ _⟩
  refine (hl i (Finset.mem_univ _)).trans ?_
  by_contra hn
  push_neg at hn
  have h0 : v (Y l j) ≠ 0 := (zero_lt_one.trans hn).ne'
  have e : Y l j = (A * Y : Matrix a b K) l j - ((A - 1) * Y : Matrix a b K) l j := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, sub_sub_cancel]
  have h1 : v (((A - 1) * Y : Matrix a b K) l j) < v (Y l j) := by
    rw [Matrix.mul_apply]
    refine v.map_sum_lt h0 fun t _ => ?_
    rw [map_mul]
    refine lt_of_le_of_lt (mul_le_mul_right (hl t (Finset.mem_univ _)) _) ?_
    exact mul_lt_of_lt_one_left (zero_lt_one.trans hn) (h l t)
  have h2 := v.map_sub_lt ((hY l j).trans_lt hn) h1
  rw [← e] at h2
  exact lt_irrefl _ h2

theorem intM_of_mul_right [Fintype a] [DecidableEq a] {A : Matrix a a K} (h : SmallM v (A - 1)) {Y : Matrix b a K}
    (hY : IntM v (Y * A)) : IntM v Y := by
  have h1 : SmallM v (Aᵀ - 1) := fun i j => by
    have := h j i
    simpa [Matrix.one_apply, eq_comm] using this
  have h2 : IntM v (Aᵀ * Yᵀ) := fun i j => by
    rw [← Matrix.transpose_mul]
    exact hY j i
  exact fun i j => intM_of_mul_left h1 h2 j i

theorem two_sided [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {A : Matrix a a K} {C : Matrix b b K}
    (hA : SmallM v (A - 1)) (hC : SmallM v (C - 1)) {Y Z : Matrix a b K} (e : A * Y = Z * C) :
    (IntM v Y ↔ IntM v Z) ∧ (IntM v Y → SmallM v (Y - Z)) := by
  have h1 : IntM v Y ↔ IntM v Z :=
    ⟨fun h => intM_of_mul_right hC (e ▸ (intM_of_near hA).mul h),
      fun h => intM_of_mul_left hA (e ▸ h.mul (intM_of_near hC))⟩
  refine ⟨h1, fun h => ?_⟩
  have e2 : Y - Z = Z * (C - 1) - (A - 1) * Y := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, e]
    abel
  rw [e2]
  exact ((h1.1 h).mul_small hC).sub (hA.mul_int h)

end Val

section Frames

open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.TopStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

def ratM (P : HeightOneSpectrum (𝓞 E)) {a b : ℕ} (x : HomE E a b) : Matrix (Fin b) (Fin a) (P.adicCompletion E) :=
  (LinearMap.toMatrix' x).map (algebraMap E (P.adicCompletion E))

variable (F) in

def locM (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (g : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (P.adicCompletion E) :=
  (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P)

omit [StarRing E] in
theorem ratM_comp (P : HeightOneSpectrum (𝓞 E)) {a b c : ℕ} (x : HomE E b c) (y : HomE E a b) :
    ratM P (x ∘ₗ y) = ratM P x * ratM P y := by
  unfold ratM
  rw [LinearMap.toMatrix'_comp, Matrix.map_mul]

omit [StarRing E] in
theorem locM_mul (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (g h : GL (Fin n) (AfE F E)) :
    locM F P (g * h) = locM F P g * locM F P h := by
  unfold locM
  rw [Units.val_mul, Matrix.map_mul]

omit [StarRing E] in
theorem locM_one (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} : locM F P (1 : GL (Fin n) (AfE F E)) = 1 := by
  unfold locM
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

omit [StarRing E] in
theorem ratM_apply (P : HeightOneSpectrum (𝓞 E)) {a b : ℕ} (x : HomE E a b) (i : Fin b) (j : Fin a) :
    ratM P x i j = algebraMap E _ (x (Pi.single j 1) i) := by
  simp [ratM, LinearMap.toMatrix'_apply]

omit [StarRing E] in
theorem intM_ratM (P : HeightOneSpectrum (𝓞 E)) {a b : ℕ} (x : HomE E a b) :
    IntM Valued.v (ratM P x) ↔ ∀ j i, IntAt P (x (Pi.single j 1) i) := by
  unfold IntM
  simp only [ratM_apply, valued_algebraMap, GlobalTheory.Proof.IntegralPowerExpansion.intAt_iff_val]
  exact forall_comm

omit [StarRing E] in
theorem intAt_div_of_val {P : HeightOneSpectrum (𝓞 E)} (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {a : E}
    (h : P.valuation E a < 1) : IntAt P (a / (qOf P : E)) := by
  have ha : IntAt P a := (GlobalTheory.Proof.IntegralPowerExpansion.intAt_iff_val P a).2 h.le
  refine intAt_div_of_redP hq ha ?_
  obtain ⟨r, s, hs, e⟩ := ha
  have h1 := reduction_spec P hs e
  have hr : r ∈ P.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E r) < 1
    rw [← e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (P.valuation_le_one s)) h
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hr] at h1
  have := P.isPrime
  exact (mul_eq_zero.1 h1).resolve_left fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0)

theorem single_std {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (j : Fin n) : (Pi.single j 1 : Sp E n) ∈ stdAt E n P :=
  mem_stdAt.2 fun i => by
    rw [Pi.single_apply]
    split_ifs
    · exact intAt_one
    · exact intAt_zero

variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem frame_near {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (w : SG) :
    SmallM Valued.v (locM F w.1 g⁻¹ * ratM w.1 (p.deco.1.liftFr w).toLinearMap - 1) := by
  intro i j
  obtain ⟨h1, h2⟩ := liftFr_spec p.deco.2 w
  have hz := (h1 _).2 (single_std w.1 j)
  have hb := h2 _ (single_std w.1 j)
  set z := p.deco.1.liftFr w (Pi.single j 1) with hzdef
  have hs := p.deco.2.be_smul w
  obtain ⟨s, hs0, hsz⟩ : ∃ s ∈ w.1.asIdeal.primeCompl, s • z ∈ p.deco.1.N := id hz
  obtain ⟨r, hr, hv⟩ := h.be w _ hsz i
  rw [hs s z hz, hb] at hr
  have hδ : ∃ d : 𝓞 E, redV w.1 (Pi.single j 1 : Sp E n) i = Ideal.Quotient.mk _ d ∧
      (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j = algebraMap E _ (algebraMap (𝓞 E) E d) := by
    unfold redV
    rw [Pi.single_apply, Matrix.one_apply]
    split_ifs
    · exact ⟨1, by rw [reduction_one₂, map_one], by simp⟩
    · exact ⟨0, by rw [reduction_zero, map_zero], by simp⟩
  obtain ⟨d, hd, hd'⟩ := hδ
  rw [Pi.smul_apply, hd, smul_eq_mul, ← map_mul] at hr
  have hr' : Valued.v (algebraMap E (w.1.adicCompletion E) (algebraMap (𝓞 E) E (r - s * d))) < 1 := by
    rw [valued_algebraMap, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact Ideal.Quotient.eq.1 hr
  have hs1 : Valued.v (algebraMap E (w.1.adicCompletion E) (algebraMap (𝓞 E) E s)) = 1 := by
    rw [valued_algebraMap]
    refine le_antisymm (w.1.valuation_le_one s) (not_lt.1 fun hlt => hs0 ?_)
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w.1 s).1 hlt
  have e : adAt F w.1 (Col2.pullV g (s • z) i) = algebraMap E (w.1.adicCompletion E) (algebraMap (𝓞 E) E s) *
      (locM F w.1 g⁻¹ * ratM w.1 (p.deco.1.liftFr w).toLinearMap : Matrix (Fin n) (Fin n) _) i j := by
    rw [Matrix.mul_apply, Finset.mul_sum]
    unfold Col2.pullV
    rw [Matrix.mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, adAt_inclE, ratM_apply, Pi.smul_apply, Algebra.smul_def, map_mul]
    change locM F w.1 g⁻¹ i l * _ = _ * (_ * algebraMap E _ (z l))
    ring
  have h3 := Valuation.map_add_lt _ hv hr'
  rw [e, map_sub, map_sub, map_mul, map_mul, sub_add_sub_cancel, ← mul_sub, map_mul, hs1, one_mul, ← hd'] at h3
  exact h3

theorem locM_int {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (hN : p.deco.1.N = Formalism.L2.Col.stdLat E n) (w : SG) :
    IntM Valued.v (locM F w.1 g) ∧ IntM Valued.v (locM F w.1 g⁻¹) := by
  have h0 := frame_near h w
  have h1 : ∀ x, p.deco.1.liftFr w x ∈ stdAt E n w.1 ↔ x ∈ stdAt E n w.1 := fun x => by
    have := (liftFr_spec p.deco.2 w).1 x
    rwa [Deco.at, hN] at this
  set f := p.deco.1.liftFr w
  have hf : IntM Valued.v (ratM w.1 f.toLinearMap) :=
    (intM_ratM _ _).2 fun j => mem_stdAt.1 ((h1 _).2 (single_std w.1 j))
  have hf' : IntM Valued.v (ratM w.1 f.symm.toLinearMap) :=
    (intM_ratM _ _).2 fun j => mem_stdAt.1 ((h1 _).1 (by
      rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]; exact single_std w.1 j))
  constructor
  · refine intM_of_mul_right h0 ?_
    rwa [← Matrix.mul_assoc, ← locM_mul, mul_inv_cancel, locM_one, Matrix.one_mul]
  · have := (intM_of_near h0).mul hf'
    rwa [Matrix.mul_assoc, ← ratM_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
      ratM, LinearMap.toMatrix'_id, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this

theorem read_cong {a b : ℕ} {ST' : Finset (HeightOneSpectrum (𝓞 E))} {k y : GL (Fin a) (AfE F E)} {k' y' : GL (Fin b) (AfE F E)}
    {p q : DecoF E a ST SG Q} {p' q' : DecoF E b ST' SG Q} (hp : IsPtOf hc k p) (hN : p.deco.1.N = Formalism.L2.Col.stdLat E a)
    (hp' : IsPtOf hc k' p') (hN' : p'.deco.1.N = Formalism.L2.Col.stdLat E b) (hq : IsPtOf hc (y * k) q) (hq' : IsPtOf hc (y' * k') q') (w : SG)
    (x x₀ : HomE E a b) (hx : SmallM Valued.v (locM F w.1 y'⁻¹ * ratM w.1 x * locM F w.1 y - ratM w.1 x₀)) :
    (IntM Valued.v (ratM w.1 (inFr (p.deco.1.liftFr w) (p'.deco.1.liftFr w) x₀)) ↔
      IntM Valued.v (ratM w.1 (inFr (q.deco.1.liftFr w) (q'.deco.1.liftFr w) x))) ∧
    (IntM Valued.v (ratM w.1 (inFr (p.deco.1.liftFr w) (p'.deco.1.liftFr w) x₀)) →
      SmallM Valued.v (ratM w.1 (inFr (p.deco.1.liftFr w) (p'.deco.1.liftFr w) x₀) -
        ratM w.1 (inFr (q.deco.1.liftFr w) (q'.deco.1.liftFr w) x))) := by
  have key : ∀ (g : GL (Fin a) (AfE F E)) (g' : GL (Fin b) (AfE F E)) (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b)
      (z : HomE E a b), (locM F w.1 g'⁻¹ * ratM w.1 f'.toLinearMap) * ratM w.1 (inFr f f' z) =
        (locM F w.1 g'⁻¹ * ratM w.1 z * locM F w.1 g) * (locM F w.1 g⁻¹ * ratM w.1 f.toLinearMap) := by
    intro g g' f f' z
    have e : f'.toLinearMap ∘ₗ inFr f f' z = z ∘ₗ f.toLinearMap := by
      ext v l
      simp [inFr]
    rw [Matrix.mul_assoc, ← ratM_comp, e, ratM_comp, Matrix.mul_assoc _ (locM F w.1 g), ← Matrix.mul_assoc (locM F w.1 g),
      ← locM_mul, mul_inv_cancel, locM_one, Matrix.one_mul, Matrix.mul_assoc]
  obtain ⟨a1, a2⟩ := two_sided (frame_near hp' w) (frame_near hp w) (key _ _ _ _ x₀)
  obtain ⟨b1, b2⟩ := two_sided (frame_near hq' w) (frame_near hq w) (key _ _ _ _ x)
  have hD := ((locM_int hp' hN' w).2.mul_small hx).mul_int (locM_int hp hN w).1
  have e : locM F w.1 k'⁻¹ * (locM F w.1 y'⁻¹ * ratM w.1 x * locM F w.1 y - ratM w.1 x₀) * locM F w.1 k =
      locM F w.1 (y' * k')⁻¹ * ratM w.1 x * locM F w.1 (y * k) - locM F w.1 k'⁻¹ * ratM w.1 x₀ * locM F w.1 k := by
    rw [_root_.mul_inv_rev, locM_mul, locM_mul, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
  rw [e] at hD
  have c1 : IntM Valued.v (locM F w.1 k'⁻¹ * ratM w.1 x₀ * locM F w.1 k) ↔
      IntM Valued.v (locM F w.1 (y' * k')⁻¹ * ratM w.1 x * locM F w.1 (y * k)) :=
    ⟨fun h => by simpa using hD.int.add h, fun h => by simpa using h.sub hD.int⟩
  have c2 := a1.trans (c1.trans b1.symm)
  refine ⟨c2, fun h => ?_⟩
  have := ((a2 h).sub hD).sub (b2 (c2.1 h))
  convert this using 1
  abel

end Frames

section Top

open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.TopStep

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {m2 : ℕ}

theorem locTop_shift (hc : cst.Ok) {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs)
    (y : HomE X.E (R.N (m2 + 1)) (R.N R.m)) {a b : Sp X.E (R.N (m2 + 1))} (ha : ∀ i, IntAt P.1 ((qOf P.1 : X.E) * a i))
    (hb : ∀ i, IntAt P.1 (b i - a i)) : locTop Ch sel mu cst m2 P y b = locTop Ch sel mu cst m2 P y a := by
  unfold locTop
  congr 1
  generalize atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y = η
  unfold ftY
  rw [if_pos hP, if_pos hP]
  split_ifs with h
  · have ev : ∀ z : Sp X.E (R.N (m2 + 1)), η z = ∑ j, z j * η (Pi.single j 1) := fun z => by
      conv_lhs => rw [pi_eq_sum_univ' z]
      simp [map_sum]
    have he : IntAt P.1 ((epsSg : ℤ) : X.E) := intCast_mem (intRing P.1) _
    have hd : IntAt P.1 ((epsSg : X.E) * η (b - a)) := by
      rw [ev]
      exact he.mul (intAt_sum _ fun j _ => (hb j).mul (h j))
    have hz' : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * η a)) := by
      obtain ⟨D, hD⟩ : ∃ D, cst.D P = D + 1 := ⟨cst.D P - 1, by have := hc.D_pos P; omega⟩
      have := (intAt_pow (intAt_nat (P := P.1) (qOf P.1)) D).mul
        (he.mul (intAt_sum Finset.univ fun j _ => (ha j).mul (h j)))
      convert this using 1
      rw [hD, ev, pow_succ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have := hc.psi_add P _ _ hz' ((intAt_pow (intAt_nat (P := P.1) (qOf P.1)) _).mul hd)
    rw [hc.psi_int P _ hd, mul_one, ← mul_add, ← map_add, add_sub_cancel] at this
    exact this
  · rfl

theorem rep_sub_int {u : Pr.Word} {j : ℕ} (h : j + 1 = R.m) (p q : PtAt R sel mu cst u j) (e : cosetIn q = cosetIn p)
    {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs) (i : Fin (R.N j)) :
    IntAt P.1 ((frsF sel mu p.1.1 P).symm (repY p.1.2) i - (frsF sel mu q.1.1 P).symm (repY q.1.2) i) := by
  have h1 : (frsF sel mu p.1.1 P).symm (repY p.1.2) ∈ cosetIn p P :=
    ⟨_, p.repY_mem h, by rw [sub_self, smul_zero]; exact zero_mem _⟩
  rw [← e] at h1
  obtain ⟨z, hz1, h2⟩ := h1
  rw [if_pos hP, pow_zero, inv_one, one_smul] at h2
  have h3 := q.repY_mem h
  obtain ⟨y, -, hY⟩ := q.mem_ybSet h
  have h4 := (mem_locLat _ _ _ _).1 ((Set.ext_iff.1 hY _).1 hz1) P
  have h5 := (mem_locLat _ _ _ _).1 ((Set.ext_iff.1 hY _).1 h3) P
  simp only [if_pos hP, zpow_zero, inv_one, one_smul] at h4 h5
  have h6 : z - repY q.1.2 ∈ q.1.1.deco.1.at P.1 := by
    have := sub_mem h4 h5
    rwa [sub_sub_sub_cancel_right] at this
  rw [← (frsF sel mu q.1.1 P).apply_symm_apply (z - _), frsF_mem, map_sub] at h6
  have h7 := add_mem h2 h6
  rw [sub_add_sub_cancel] at h7
  exact mem_stdAt.1 h7 i

theorem locTop_of_cong (hm : R.m = m2 + 2) (hc : cst.Ok) {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs)
    (hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2) {j : ℕ} (h : R.N j = R.N R.m) (y z : HomE X.E (R.N (m2 + 1)) (R.N j))
    {a : Sp X.E (R.N (m2 + 1))} (ha : ∀ i, IntAt P.1 ((qOf P.1 : X.E) * a i))
    (H : (IntM Valued.v (ratM P.1 y) ↔ IntM Valued.v (ratM P.1 z)) ∧
      (IntM Valued.v (ratM P.1 y) → SmallM Valued.v (ratM P.1 y - ratM P.1 z))) :
    locTop Ch sel mu cst m2 P (castSp X.E h ∘ₗ y) a = locTop Ch sel mu cst m2 P (castSp X.E h ∘ₗ z) a := by
  have supp : ∀ w : HomE X.E (R.N (m2 + 1)) (R.N j), locTop Ch sel mu cst m2 P (castSp X.E h ∘ₗ w) a ≠ 0 →
      IntM Valued.v (ratM P.1 w) := fun w hw =>
    (intM_ratM _ _).2 fun s i => mem_stdAt.1 (locTop_supp hm hP hw s) (Fin.cast h i)
  by_cases hy : IntM Valued.v (ratM P.1 y)
  · refine locTop_congr hm hc hP ha fun s l => ⟨(intM_ratM _ _).1 hy s _, (intM_ratM _ _).1 (H.1.1 hy) s _, ?_⟩
    refine intAt_div_of_val hq ?_
    have := H.2 hy (Fin.cast h.symm l) s
    rwa [Matrix.sub_apply, ratM_apply, ratM_apply, ← map_sub, valued_algebraMap] at this
  · have h1 : locTop Ch sel mu cst m2 P (castSp X.E h ∘ₗ y) a = 0 := by
      by_contra h0
      exact hy (supp _ h0)
    have h2 : locTop Ch sel mu cst m2 P (castSp X.E h ∘ₗ z) a = 0 := by
      by_contra h0
      exact hy (H.1.2 (supp _ h0))
    rw [h1, h2]

end Top

end GlobalTheory.Transport.Last
