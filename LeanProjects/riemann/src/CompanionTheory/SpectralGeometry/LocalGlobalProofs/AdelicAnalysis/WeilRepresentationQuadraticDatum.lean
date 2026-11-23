import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureLinearChangeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesSelfDualStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AnnihilatorOfAnnihilatorLeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Core.SelfDual

def OhR (F : Type) [Field F] [NumberField F] : Subring (A F) where
  carrier := Oh F
  mul_mem' := fun {_ _} ha hb v => mul_mem (ha v) (hb v)
  one_mem' := fun _ => one_mem _
  add_mem' := fun {_ _} ha hb v => add_mem (ha v) (hb v)
  zero_mem' := fun _ => zero_mem _
  neg_mem' := fun {_} ha v => neg_mem (ha v)

variable {F : Type} [Field F] [NumberField F] {ι : Type}

def LL (ι : Type) (c : F) : AddSubgroup (ι → A F) where
  carrier := {x | ∀ i, algebraMap F (A F) c⁻¹ * x i ∈ Oh F}
  add_mem' := fun {a b} ha hb i => by
    have h : _ ∈ OhR F := (OhR F).add_mem (ha i) (hb i)
    rw [Pi.add_apply, mul_add]
    exact h
  zero_mem' := fun i => by
    rw [Pi.zero_apply, mul_zero]
    exact (OhR F).zero_mem
  neg_mem' := fun {a} ha i => by
    rw [Pi.neg_apply, mul_neg]
    exact (OhR F).neg_mem (ha i)

variable [Fintype ι] [DecidableEq ι]

lemma Bf_mul (g h : Matrix ι ι F) : Bf (g * h) = Bf g * Bf h := Matrix.map_mul

lemma Bf_one : Bf (1 : Matrix ι ι F) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

lemma Bf_transpose (g : Matrix ι ι F) : Bf gᵀ = (Bf g)ᵀ := by
  ext i j; rfl

lemma Bf_inv_mul {g : Matrix ι ι F} (hg : g.det ≠ 0) : Bf g⁻¹ * Bf g = 1 := by
  rw [← Bf_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hg), Bf_one]

lemma Bf_mul_inv {g : Matrix ι ι F} (hg : g.det ≠ 0) : Bf g * Bf g⁻¹ = 1 := by
  rw [← Bf_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hg), Bf_one]

lemma Bf_smul_one (c : F) : Bf (c • (1 : Matrix ι ι F)) = algebraMap F (A F) c • 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Bf]
  · simp [Bf, Matrix.one_apply, h]

def Gs (g : Matrix ι ι F) (S : Set (A F)) : Set (ι → A F) :=
  (fun x => Bf g *ᵥ x) '' Set.univ.pi fun _ => S

lemma mem_Gs_iff {g : Matrix ι ι F} (hg : g.det ≠ 0) {S : Set (A F)} {y : ι → A F} :
    y ∈ Gs g S ↔ ∀ i, (Bf g⁻¹ *ᵥ y) i ∈ S := by
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    simp only [Matrix.mulVec_mulVec, Bf_inv_mul hg, Matrix.one_mulVec]
    exact hx i (Set.mem_univ i)
  · intro h
    refine ⟨Bf g⁻¹ *ᵥ y, fun i _ => h i, ?_⟩
    simp only [Matrix.mulVec_mulVec, Bf_mul_inv hg, Matrix.one_mulVec]

lemma continuous_mulVec' (M : Matrix ι ι (A F)) : Continuous fun y : ι → A F => M *ᵥ y :=
  Continuous.matrix_mulVec continuous_const continuous_id

lemma isOpen_Gs {g : Matrix ι ι F} (hg : g.det ≠ 0) {S : Set (A F)} (hS : IsOpen S) :
    IsOpen (Gs g S) := by
  have h : Gs g S = (fun y => Bf g⁻¹ *ᵥ y) ⁻¹' Set.univ.pi fun _ => S := by
    ext y
    simp [mem_Gs_iff hg]
  rw [h]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => hS).preimage (continuous_mulVec' _)

lemma isCompact_Gs (g : Matrix ι ι F) {S : Set (A F)} (hS : IsCompact S) :
    IsCompact (Gs g S) :=
  (isCompact_univ_pi fun _ => hS).image (continuous_mulVec' _)

lemma Gs_mono (g : Matrix ι ι F) {S T : Set (A F)} (h : S ⊆ T) : Gs g S ⊆ Gs g T :=
  Set.image_mono (Set.pi_mono fun _ _ => h)

lemma det_inv_ne {g : Matrix ι ι F} (hg : g.det ≠ 0) : (g⁻¹).det ≠ 0 := by
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero hg

lemma psi_sum {R : Type} [CommRing R] (ψ : AddChar R ℂ) (s : Finset ι) (f : ι → R) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

lemma perp_Gs (ψ : AddChar (A F) ℂ) (B g : Matrix ι ι F) (hg : (gᵀ * B).det ≠ 0) {S : Set (A F)}
    (h0 : (0 : A F) ∈ S) :
    perp (chiB ψ (Bf B)) (Gs g S) = Gs (gᵀ * B)⁻¹ (perp (fun x y => ψ (x * y)) S) := by
  have key : ∀ s y : ι → A F, chiB ψ (Bf B) (Bf g *ᵥ s) y = ψ (s ⬝ᵥ (Bf (gᵀ * B) *ᵥ y)) := by
    intro s y
    unfold chiB
    rw [Bf_mul, Bf_transpose, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec s,
      Matrix.vecMul_transpose]
  ext y
  rw [mem_Gs_iff (det_inv_ne hg), Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 hg)]
  constructor
  · intro h i a ha
    have h1 := h (Bf g *ᵥ Pi.single i a) ⟨_, fun j _ => by
      by_cases hj : j = i
      · subst hj; simpa using ha
      · simpa [hj] using h0, rfl⟩
    rw [key] at h1
    simpa using h1
  · rintro h x ⟨s, hs, rfl⟩
    show chiB ψ (Bf B) (Bf g *ᵥ s) y = 1
    rw [key, dotProduct, psi_sum]
    exact Finset.prod_eq_one fun i _ => h i (s i) (hs i (Set.mem_univ i))

lemma norm_inv' (x : F) (hx : x ≠ 0) : Algebra.norm ℚ x⁻¹ = (Algebra.norm ℚ x)⁻¹ := by
  have h := map_mul (Algebra.norm ℚ) x x⁻¹
  rw [mul_inv_cancel₀ hx, map_one] at h
  exact (inv_eq_of_mul_eq_one_right h.symm).symm

lemma coe_LL {c : F} (hc : c ≠ 0) :
    (LL ι c : Set (ι → A F)) = Gs (c • (1 : Matrix ι ι F)) (Oh F) := by
  have hd : (c • (1 : Matrix ι ι F)).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hc
  have hi : (c • (1 : Matrix ι ι F))⁻¹ = c⁻¹ • 1 := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  ext x
  have e : (algebraMap F (A F) c⁻¹ • (1 : Matrix ι ι (A F))) *ᵥ x =
      fun i => algebraMap F (A F) c⁻¹ * x i := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  rw [mem_Gs_iff hd, hi, Bf_smul_one, e]
  exact Iff.rfl

section Measure

variable [MeasurableSpace (A F)] [BorelSpace (A F)]

lemma pi_Gs (lf : Measure (A F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf (Oh F) = 1)
    {g : Matrix ι ι F} (hg : g.det ≠ 0) {S : Set (A F)} (hS : MeasurableSet S) :
    (Measure.pi fun _ : ι => lf) (Gs g S) =
      ENNReal.ofReal (|((Algebra.norm ℚ g.det : ℚ) : ℝ)|⁻¹) * lf S ^ Fintype.card ι := by
  obtain ⟨hlc, hsc, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI := hlc
  haveI := hsc
  haveI : SigmaFinite lf := inferInstance
  have h := (GlobalTheory.T.adelic_haar_measure_linear_change F lf hlf h1 ι).1 g hg (Set.univ.pi fun _ => S)
    (MeasurableSet.univ_pi fun _ => hS)
  rw [Gs, h, Measure.pi_pi]
  simp

end Measure

lemma exists_LL_subset {U : Set (ι → A F)} (hU : U ∈ 𝓝 (0 : ι → A F)) :
    ∃ N : ℕ, 0 < N ∧ (LL ι (N : F) : Set (ι → A F)) ⊆ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  have hU' : (⋂ i, t i) ∈ 𝓝 (0 : A F) := Filter.iInter_mem.2 fun i => ht i
  obtain ⟨-, -, -, -, -, -, -, hnb, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨N, hN, hNU⟩ := hnb _ hU'
  refine ⟨N, hN, fun x hx => hsub fun i _ => ?_⟩
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h := hNU _ (hx i)
  have e : (N : A F) * (algebraMap F (A F) (N : F)⁻¹ * x i) = x i := by
    rw [← mul_assoc, ← map_natCast (algebraMap F (A F)) N, ← map_mul, mul_inv_cancel₀ hN', map_one,
      one_mul]
  rw [e] at h
  exact Set.mem_iInter.1 h i

lemma exists_subset_LL {K : Set (ι → A F)} (hK : IsCompact K) :
    ∃ N : ℕ, 0 < N ∧ K ⊆ (LL ι ((N : F)⁻¹) : Set (ι → A F)) := by
  have hK' : IsCompact (⋃ i, (fun x : ι → A F => x i) '' K) :=
    isCompact_iUnion fun i => hK.image (continuous_apply i)
  obtain ⟨-, -, -, -, -, -, -, -, hcp, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨N, hN, hNK⟩ := hcp _ hK'
  refine ⟨N, hN, fun x hx i => ?_⟩
  rw [inv_inv, map_natCast]
  exact hNK _ (Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩)

section Main

variable [MeasurableSpace (A F)] [BorelSpace (A F)]

lemma real_id (k s d : ℝ) (n : ℕ) (hk : k ≠ 0) (hs : s ≠ 0) (hd : d ≠ 0) :
    k ^ n * s⁻¹ * d⁻¹ * (k ^ n * s⁻¹ * (d * (s * s) * ((k * k)⁻¹) ^ n)) = 1 := by
  have h : ((k * k)⁻¹) ^ n = (k ^ n)⁻¹ * (k ^ n)⁻¹ := by rw [inv_pow, mul_pow, mul_inv]
  have hkn := pow_ne_zero n hk
  rw [h]
  field_simp

lemma mass_one (lf : Measure (A F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf (Oh F) = 1)
    {B g : Matrix ι ι F} (hB : B.det ≠ 0) (hg : g.det ≠ 0) {P : Set (A F)} (hPm : MeasurableSet P)
    (hP : ENNReal.ofReal (kap F) * (ENNReal.ofReal (kap F) * lf P) = 1) :
    muF B lf (Gs g (Oh F)) * muF B lf (Gs (gᵀ * B)⁻¹ P) = 1 := by
  have hk : 0 < kap F := by
    have : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
    unfold kap
    positivity
  have hnorm : ∀ {x : F}, x ≠ 0 → 0 < |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    intro x hx
    have : Algebra.norm ℚ x ≠ 0 := Algebra.norm_ne_zero_iff.2 hx
    have : ((Algebra.norm ℚ x : ℚ) : ℝ) ≠ 0 := by exact_mod_cast this
    positivity
  have hd : (gᵀ * B).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hg hB
  have hOm : MeasurableSet (Oh F) := by
    obtain ⟨-, -, -, -, hOo, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
    exact hOo.measurableSet
  have hlP : lf P = ENNReal.ofReal ((kap F * kap F)⁻¹) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul hk.le] at hP
    rw [ENNReal.ofReal_inv_of_pos (mul_pos hk hk)]
    exact ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm] at hP)
  have e2 : |((Algebra.norm ℚ ((gᵀ * B)⁻¹).det : ℚ) : ℝ)|⁻¹ =
      |((Algebra.norm ℚ g.det : ℚ) : ℝ)| * |((Algebra.norm ℚ B.det : ℚ) : ℝ)| := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv' _ hd, Matrix.det_mul,
      Matrix.det_transpose, map_mul]
    push_cast
    rw [abs_inv, inv_inv, abs_mul]
  simp only [muF, Measure.smul_apply, smul_eq_mul]
  rw [pi_Gs lf hlf h1 hg hOm, pi_Gs lf hlf h1 (det_inv_ne hd) hPm, h1, hlP, e2, one_pow, mul_one]
  have hnd := hnorm hg
  have hnD := hnorm hB
  set nd := |((Algebra.norm ℚ g.det : ℚ) : ℝ)|
  set nD := |((Algebra.norm ℚ B.det : ℚ) : ℝ)|
  set n := Fintype.card ι
  have hs : Real.sqrt nD * Real.sqrt nD = nD := Real.mul_self_sqrt hnD.le
  have hsp : 0 < Real.sqrt nD := Real.sqrt_pos.2 hnD
  have ha : 0 ≤ kap F ^ n * (Real.sqrt nD)⁻¹ := by positivity
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul ha,
    ← ENNReal.ofReal_mul (p := nd * nD) (by positivity), ← ENNReal.ofReal_mul ha,
    ← ENNReal.ofReal_mul (by positivity)]
  have : kap F ^ n * (Real.sqrt nD)⁻¹ * nd⁻¹ *
      (kap F ^ n * (Real.sqrt nD)⁻¹ * (nd * nD * ((kap F * kap F)⁻¹) ^ n)) = 1 := by
    have h := real_id (kap F) (Real.sqrt nD) nd n hk.ne' hsp.ne' hnd.ne'
    rwa [hs] at h
  rw [this, ENNReal.ofReal_one]

lemma LL_good (lf : Measure (A F)) (hlf : lf.IsAddHaarMeasure) (h1 : lf (Oh F) = 1)
    (ψ : AddChar (A F) ℂ) {B : Matrix ι ι F} (hS : B.IsSymm) (hB : B.det ≠ 0)
    (hOc : IsCompact (Oh F)) (hOo : IsOpen (Oh F))
    (hPc : IsCompact (perp (fun x y => ψ (x * y)) (Oh F)))
    (hPo : IsOpen (perp (fun x y => ψ (x * y)) (Oh F)))
    (hPP : perp (fun x y => ψ (x * y)) (perp (fun x y => ψ (x * y)) (Oh F)) ⊆ Oh F)
    (hP : ENNReal.ofReal (kap F) *
      (ENNReal.ofReal (kap F) * lf (perp (fun x y => ψ (x * y)) (Oh F))) = 1)
    {c : F} (hc : c ≠ 0) :
    IsCompact (LL ι c : Set (ι → A F)) ∧ IsOpen (LL ι c : Set (ι → A F)) ∧
      IsCompact (perp (chiB ψ (Bf B)) (LL ι c : Set (ι → A F))) ∧
      IsOpen (perp (chiB ψ (Bf B)) (LL ι c : Set (ι → A F))) ∧
      perp (chiB ψ (Bf B)) (perp (chiB ψ (Bf B)) (LL ι c : Set (ι → A F))) ⊆ LL ι c ∧
      muF B lf (LL ι c : Set (ι → A F)) *
        muF B lf (perp (chiB ψ (Bf B)) (LL ι c : Set (ι → A F))) = 1 := by
  set g : Matrix ι ι F := c • 1 with hgdef
  have hg : g.det ≠ 0 := by
    rw [hgdef, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hc
  have hh : (gᵀ * B).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hg hB
  have h0 : (0 : A F) ∈ Oh F := (OhR F).zero_mem
  have h0P : (0 : A F) ∈ perp (fun x y => ψ (x * y)) (Oh F) := by
    intro x _
    simp
  have hperp := perp_Gs ψ B g hh h0
  have hhe : gᵀ * B = c • B := by
    simp [hgdef, Matrix.transpose_smul]
  have hmat : (((gᵀ * B)⁻¹)ᵀ * B)⁻¹ = g := by
    apply Matrix.inv_eq_right_inv
    have hsym : (gᵀ * B)ᵀ = gᵀ * B := by
      rw [hhe, Matrix.transpose_smul, hS.eq]
    rw [Matrix.transpose_nonsing_inv, hsym, Matrix.mul_assoc]
    have : B * g = gᵀ * B := by
      rw [hhe, hgdef]
      simp
    rw [this]
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hh)
  have hh' : (((gᵀ * B)⁻¹)ᵀ * B).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (det_inv_ne hh) hB
  have hperp2 := perp_Gs ψ B (gᵀ * B)⁻¹ hh' h0P
  rw [coe_LL hc, ← hgdef]
  rw [hperp, hperp2, hmat]
  refine ⟨isCompact_Gs g hOc, isOpen_Gs hg hOo, isCompact_Gs _ hPc, isOpen_Gs (det_inv_ne hh) hPo,
    Gs_mono g hPP, mass_one lf hlf h1 hB hg hPo.measurableSet hP⟩

theorem naQuad : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)]
    (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 →
    ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F), B.IsSymm → B.det ≠ 0 → NAQuad ψ (hf F) (Bf B) (muF B lf) := by
  intro F _ _ _ _ lf hlf h1 ψ hψ ι _ _ B hS hB
  obtain ⟨hlc, hsc, ht2, hOc, hOo, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI := hlc
  haveI := hsc
  haveI := ht2
  haveI : SigmaFinite lf := inferInstance
  obtain ⟨hnorm, -, -⟩ := (GlobalTheory.T.standard_adelic_character F).2 ψ hψ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hL⟩ := GlobalTheory.T.adeles_self_dual F lf hlf h1 ψ hψ
  have hO : IsCompact (perp (fun x y => ψ (x * y)) (Oh F)) ∧
      IsOpen (perp (fun x y => ψ (x * y)) (Oh F)) ∧
      perp (fun x y => ψ (x * y)) (perp (fun x y => ψ (x * y)) (Oh F)) ⊆ Oh F ∧
      (ENNReal.ofReal (kap F) • lf) (Oh F) *
        (ENNReal.ofReal (kap F) • lf) (perp (fun x y => ψ (x * y)) (Oh F)) = 1 :=
    hL (OhR F).toAddSubgroup hOc hOo
  obtain ⟨hPc, hPo, hPP, hPm⟩ := hO
  have hP : ENNReal.ofReal (kap F) *
      (ENNReal.ofReal (kap F) * lf (perp (fun x y => ψ (x * y)) (Oh F))) = 1 := by
    simpa [Measure.smul_apply, h1] using hPm
  have good : ∀ {c : F}, c ≠ 0 → _ := fun {c} hc =>
    LL_good (ι := ι) lf hlf h1 ψ hS hB hOc hOo hPc hPo hPP hP hc
  have hk : 0 < kap F := by
    have : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
    unfold kap
    positivity
  have hnB : 0 < |((Algebra.norm ℚ B.det : ℚ) : ℝ)| := by
    have : Algebra.norm ℚ B.det ≠ 0 := Algebra.norm_ne_zero_iff.2 hB
    have : ((Algebra.norm ℚ B.det : ℚ) : ℝ) ≠ 0 := by exact_mod_cast this
    positivity
  have hhaar : (muF B lf).IsAddHaarMeasure := by
    haveI : (Measure.pi fun _ : ι => lf).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    refine Measure.IsAddHaarMeasure.smul _ ?_ ENNReal.ofReal_ne_top
    have : 0 < kap F ^ Fintype.card ι * (Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|)⁻¹ := by
      have := Real.sqrt_pos.2 hnB
      positivity
    exact (ENNReal.ofReal_pos.2 this).ne'
  have hsym : ∀ x y : ι → A F, chiB ψ (Bf B) x y = chiB ψ (Bf B) y x := by
    intro x y
    unfold chiB
    have hsB : (Bf B)ᵀ = Bf B := (hS.map (algebraMap F (A F))).eq
    rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hsB]
  have hadd : ∀ x x' y : ι → A F,
      chiB ψ (Bf B) (x + x') y = chiB ψ (Bf B) x y * chiB ψ (Bf B) x' y := by
    intro x x' y
    unfold chiB
    rw [add_dotProduct, AddChar.map_add_eq_mul]
  refine ⟨inferInstance, ?_, hψ.1, hnorm, hS.map _, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hhaar, ?_, ?_, ?_, ?_, fun _ _ => hnorm _, ?_, ?_⟩
  · rw [hf, ← map_ofNat (algebraMap F (A F)) 2, ← map_mul]
    simp
  · intro U hU
    obtain ⟨N, hN, hNU⟩ := exists_LL_subset hU
    have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    exact ⟨LL ι (N : F), (good hN').1, (good hN').2.1, hNU⟩
  · intro x
    obtain ⟨N, hN, hNK⟩ := exists_subset_LL (isCompact_singleton (x := x))
    have hN' : ((N : F)⁻¹) ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 hN.ne')
    exact ⟨LL ι ((N : F)⁻¹), (good hN').1, (good hN').2.1, hNK rfl⟩
  · exact hψ.1.comp (Continuous.dotProduct continuous_fst
      (Continuous.matrix_mulVec continuous_const continuous_snd))
  · exact hsym
  · exact hadd
  · intro L hLc hLo
    obtain ⟨N, hN, hNU⟩ := exists_LL_subset (hLo.mem_nhds L.zero_mem)
    obtain ⟨M, hM, hMK⟩ := exists_subset_LL hLc
    have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have hM' : ((M : F)⁻¹) ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 hM.ne')
    obtain ⟨-, h1o, h1c, -, h1p, h1m⟩ := good hN'
    obtain ⟨h2c, -, -, h2o, h2p, h2m⟩ := good hM'
    exact GlobalTheory.T.annihilator_of_annihilator_le (ι → A F) (chiB ψ (Bf B)) (muF B lf) hhaar
      hsym (fun _ _ => hnorm _) hadd (LL ι (N : F)) L (LL ι ((M : F)⁻¹))
      hNU hMK h1o h2c h1c h2o h1p h2p h1m h2m

end Main

end GlobalTheory.CompanionTheory.SW.Core.SelfDual
