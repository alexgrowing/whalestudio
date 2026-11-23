import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.PolyMem
import GroundTheory.AutomorphicForms.Satake
import GroundTheory.AutomorphicForms.MacdonaldWhittakerHecke
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

noncomputable section

open GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.HeckeAlgebra.HeckeAlgebraLevel Matrix
open ValuativeRel (valuation)
open scoped ValuativeRel

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

private theorem sum_ite_val_lt {m : ℕ} (hm : m ≤ n) :
    ∑ l : Fin n, (if (l : ℕ) < m then (1 : ℤ) else 0) = m := by
  rw [Fin.sum_univ_eq_sum_range (fun l => if l < m then (1 : ℤ) else 0) n, Finset.sum_boole]
  have : (Finset.range n).filter (fun l => l < m) = Finset.range m := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.card_range]

private theorem eq_ite_of_antitone {μ : Fin n → ℤ} (hμ : Antitone μ) (h0 : ∀ i, 0 ≤ μ i) (h1 : ∀ i, μ i ≤ 1)
    {j : ℕ} (hs : ∑ i, μ i = j) (i : Fin n) : μ i = if (i : ℕ) < j then 1 else 0 := by
  split_ifs with h
  · by_contra hne
    have hi : μ i = 0 := by have := h0 i; have := h1 i; omega
    have hle : ∑ l : Fin n, μ l ≤ ∑ l : Fin n, (if (l : ℕ) < (i : ℕ) then (1 : ℤ) else 0) := by
      refine Finset.sum_le_sum fun l _ => ?_
      split_ifs with hl
      · exact h1 l
      · exact (hμ (show i ≤ l from Fin.le_def.2 (by omega))).trans hi.le
    rw [hs, sum_ite_val_lt i.2.le] at hle
    omega
  · by_contra hne
    have hi : μ i = 1 := by have := h0 i; have := h1 i; omega
    have hle : ∑ l : Fin n, (if (l : ℕ) < (i : ℕ) + 1 then (1 : ℤ) else 0) ≤ ∑ l : Fin n, μ l := by
      refine Finset.sum_le_sum fun l _ => ?_
      split_ifs with hl
      · exact hi.symm.le.trans (hμ (show l ≤ i from Fin.le_def.2 (by omega)))
      · exact h0 l
    rw [hs, sum_ite_val_lt (show (i : ℕ) + 1 ≤ n from i.2)] at hle
    omega

private theorem exponent_nonneg {m : ℤ} (h : (uniformizer F : F) ^ m ∈ 𝒪[F]) : 0 ≤ m := by
  by_contra hm
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -((k : ℤ) + 1) := ⟨(-m - 1).toNat, by omega⟩
  have h1 : (uniformizer F) ^ (k + 1) * (⟨_, h⟩ : 𝒪[F]) = 1 := by
    refine Subtype.ext ?_
    have h2 : ((uniformizer F : F)) ≠ 0 := Cartan.uniformizer_ne_zero F
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_one]
    rw [_root_.zpow_neg, ← Nat.cast_succ, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ h2)]
  exact (irreducible_uniformizer F).not_isUnit
    ((isUnit_pow_succ_iff).1 (IsUnit.of_mul_eq_one _ h1))

private theorem valuation_det_diagPow (μ : Fin n → ℤ) :
    valuation F ((Cartan.diagPow F n μ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det =
      valuation F (uniformizer F : F) ^ (∑ i, μ i) := by
  have hv : valuation F (uniformizer F : F) ≠ 0 := valuation_uniformizer_ne_zero F
  rw [Cartan.coe_diagPow, det_diagonal, map_prod]
  simp only [map_zpow₀]
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hv, ih]

private theorem diagPow_mem_minusculeSet {j : ℕ} (hj : j ≤ n) :
    Cartan.diagPow F n (fun i => if (i : ℕ) < j then 1 else 0) ∈ minusculeSet F n j := by
  have hπ : (uniformizer F : F) ∈ 𝒪[F] := (uniformizer F).2
  refine ⟨fun a b => ?_, fun a b => ?_, ?_⟩
  · change ((Cartan.diagPow F n (fun i => if (i : ℕ) < j then 1 else 0) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) a b ∈ 𝒪[F]
    rw [Cartan.coe_diagPow, diagonal_apply]
    split_ifs <;> simp [hπ, (𝒪[F]).one_mem, (𝒪[F]).zero_mem]
  · have : ((Cartan.diagPow F n (fun i => if (i : ℕ) < j then 1 else 0))⁻¹ : GL (Fin n) F) a b =
        (diagonal fun i : Fin n => (uniformizer F : F) ^ (-(if (i : ℕ) < j then (1 : ℤ) else 0))) a b := rfl
    rw [this, diagonal_apply]
    have h2 : ((uniformizer F : F)) ≠ 0 := Cartan.uniformizer_ne_zero F
    split_ifs <;> simp [hπ, h2, (𝒪[F]).one_mem, (𝒪[F]).zero_mem]
  · rw [valuation_det_diagPow, sum_ite_val_lt hj, zpow_natCast]

private theorem mem_minusculeSet_iff {j : ℕ} (hj : j ≤ n) (g : GL (Fin n) F) :
    g ∈ minusculeSet F n j ↔ ∃ a ∈ integralGL F n, ∃ b ∈ integralGL F n,
      g = a * Cartan.diagPow F n (fun i => if (i : ℕ) < j then 1 else 0) * b := by
  constructor
  · intro hg
    obtain ⟨μ, hdom, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul F n g
    have hm : Cartan.diagPow F n μ ∈ minusculeSet F n j := by
      have := mul_mem_minusculeSet hg (inv_mem hk₁) (inv_mem hk₂)
      simpa [mul_assoc] using this
    obtain ⟨m1, m2, m3⟩ := hm
    have h0 : ∀ i, 0 ≤ μ i := fun i => exponent_nonneg (by
      have := m1 i i
      rwa [show (Cartan.diagPow F n μ) i i = (uniformizer F : F) ^ μ i by
        change ((Cartan.diagPow F n μ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i = _
        rw [Cartan.coe_diagPow, diagonal_apply_eq]] at this)
    have h1 : ∀ i, μ i ≤ 1 := fun i => by
      have h2 : ((uniformizer F : F)) ≠ 0 := Cartan.uniformizer_ne_zero F
      have e : (uniformizer F : F) * ((Cartan.diagPow F n μ)⁻¹ : GL (Fin n) F) i i =
          (uniformizer F : F) ^ (1 - μ i) := by
        have : ((Cartan.diagPow F n μ)⁻¹ : GL (Fin n) F) i i =
          (diagonal fun i : Fin n => (uniformizer F : F) ^ (-μ i)) i i := rfl
        rw [this, diagonal_apply_eq, sub_eq_add_neg, zpow_add₀ h2, zpow_one]
      have := exponent_nonneg (F := F) (e ▸ m2 i i)
      omega
    have hs : ∑ i, μ i = j := by
      have hv : valuation F (uniformizer F : F) ≠ 0 := valuation_uniformizer_ne_zero F
      rw [valuation_det_diagPow, ← zpow_natCast] at m3
      exact (zpow_right_strictAnti₀ (zero_lt_iff.2 hv) (valuation_uniformizer_lt_one F)).injective m3
    have hμ : μ = fun i : Fin n => if (i : ℕ) < j then (1 : ℤ) else 0 :=
      funext (eq_ite_of_antitone hdom h0 h1 hs)
    exact ⟨k₁, hk₁, k₂, hk₂, by rw [← hμ]⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact mul_mem_minusculeSet (diagPow_mem_minusculeSet hj) ha hb

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  (m : Measure (GL (Fin n) F)) [m.IsHaarMeasure]

private theorem heckeAct_eq_finsum {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) F) V) (hm : m.real (integralGL F n : Set (GL (Fin n) F)) = 1)
    (H : SphericalHecke m (F := F) (n := n)) {v : V} (hv : v ∈ fixedVectors ρ (integralGL F n)) :
    (Function.support fun c : GL (Fin n) F ⧸ integralGL F n =>
      (H : HeckeAlgebra m) c.out).Finite ∧
    heckeAct m ρ (H : HeckeAlgebra m) v = ∑ᶠ c : GL (Fin n) F ⧸ integralGL F n,
      (H : HeckeAlgebra m) c.out • ρ c.out v := by
  classical
  have hcH : HasCompactSupport ((H : HeckeAlgebra m) : GL (Fin n) F → ℂ) := (H : HeckeAlgebra m).mem.2
  have hfin0 : (Function.support fun c : GL (Fin n) F ⧸ integralGL F n =>
      (H : HeckeAlgebra m) c.out).Finite := by
    refine (finite_image_mk_tsupport (integralOpen F n) hcH).subset
      fun (c : GL (Fin n) F ⧸ integralGL F n) hc' => ?_
    exact ⟨c.out, subset_tsupport _ hc', QuotientGroup.out_eq' c⟩
  refine ⟨hfin0, eq_of_forall_dual fun φ => ?_⟩
  have hsm := smooth_of_mem_fixedVectors (isOpen_integralGL F n) hv
  set Φ : GL (Fin n) F → ℂ := fun g => (H : HeckeAlgebra m) g * φ (ρ g v) with hΦ
  have hcs : HasCompactSupport Φ := hcH.mul_right
  have hKΦ : ∀ x, ∀ k ∈ integralOpen F n, Φ (x * k) = Φ x := by
    intro x k hk
    simp only [hΦ]
    rw [(HeckeAlgebraLevel.val_mem _ _ H k hk x).2, map_mul, Module.End.mul_apply, hv k hk]
  have hfin : (Function.support fun c : GL (Fin n) F ⧸ integralGL F n =>
      (H : HeckeAlgebra m) c.out • ρ c.out v).Finite := by
    refine hfin0.subset fun c hc' h0 => hc' ?_
    exact (congrArg (fun t : ℂ => t • ρ c.out v) h0).trans (zero_smul ℂ _)
  rw [dual_heckeAct m (H : HeckeAlgebra m).mem hsm φ,
    integral_eq_smul_finsum_coset m (integralOpen F n) (isCompact_integralGL F n) hcs hKΦ]
  have hmap := AddMonoidHom.map_finsum (φ : V →+ ℂ) hfin
  have h1 : m.real ((integralOpen F n : OpenSubgroup _) : Set (GL (Fin n) F)) = 1 := hm
  rw [h1, one_smul]
  change (∑ᶠ x : GL (Fin n) F ⧸ integralGL F n, Φ x.out) = _
  refine Eq.trans ?_ hmap.symm
  refine finsum_congr fun c => ?_
  simp [hΦ]

end Local

section Loc2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
  [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  (m : Measure (GL (Fin n) F)) [m.IsHaarMeasure]

private def Hs (i : Fin n) : SphericalHecke m (F := F) (n := n) :=
  (sqrtQ F ^ (((i : ℕ) + 1) * (n - ((i : ℕ) + 1))))⁻¹ • minusculeHecke m ((i : ℕ) + 1)

private theorem sat_Hs (hm : m.real (integralGL F n : Set (GL (Fin n) F)) = 1) (i : Fin n) :
    satakeTransform m (Hs m i) = polyEmb n (esymm (Fin n) ℂ ((i : ℕ) + 1)) := by
  have h0 : sqrtQ F ^ (((i : ℕ) + 1) * (n - ((i : ℕ) + 1))) ≠ 0 := pow_ne_zero _ sqrtQ_ne_zero
  rw [Hs, map_smul, satakeTransform_minusculeHecke (Nat.succ_le_of_lt i.2), polyEmb_esymm, hm,
    smul_smul, Complex.ofReal_one, one_mul, inv_mul_cancel₀ h0, one_smul]

private theorem eq_aeval (hm : m.real (integralGL F n : Set (GL (Fin n) F)) = 1)
    (H : SphericalHecke m (F := F) (n := n)) (p : MvPolynomial (Fin n) ℂ)
    (hS : satakeTransform m H = polyEmb n (aeval (fun i : Fin n => esymm (Fin n) ℂ (i + 1)) p)) :
    H = aeval (Hs m) p := by
  refine satakeTransform_injective ?_
  have e : (satakeTransform m (F := F) (n := n)).comp (aeval (Hs m)) =
      (polyEmb n).comp (aeval fun i : Fin n => esymm (Fin n) ℂ (i + 1)) :=
    MvPolynomial.algHom_ext fun i => by simp [sat_Hs m hm]
  rw [hS]
  exact (DFunLike.congr_fun e p).symm

end Loc2

section Glob

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K)

private def rr : Representation ℂ (GL (Fin n) (w.adicCompletion K)) (LL μ) where
  toFun g := (rhoL μ w g : LL μ →ₗ[ℂ] LL μ)
  map_one' := by
    obtain ⟨-, -, -, -, -, -, hone, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥
    simp only [rhoL, map_one, hone]
    rfl
  map_mul' g g' := by
    obtain ⟨-, -, -, -, -, hmul, -, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥
    simp only [rhoL, map_mul, hmul]
    rfl

private theorem rr_apply (g : GL (Fin n) (w.adicCompletion K)) (v : LL μ) : rr μ w g v = rhoL μ w g v := rfl

private theorem mem_fix (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (u : LL μ) :
    u ∈ fixL μ w J ↔ u ∈ fixedVectors (rr μ w) J := by
  obtain ⟨-, hmem, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ (J.map (AdelicGLn.localEmbedding w))
  constructor
  · intro h k hk
    exact (hmem u).1 h _ ⟨k, hk, rfl⟩
  · intro h
    refine (hmem u).2 ?_
    rintro _ ⟨k, hk, rfl⟩
    exact h k hk

private theorem sphOp_apply (h : GL (Fin n) (w.adicCompletion K) → ℂ)
    (hfin : (Function.support fun c : GL (Fin n) (w.adicCompletion K) ⧸ integralGL (w.adicCompletion K) n =>
      h c.out).Finite) (u : LL μ) :
    sphOp μ w h u = ∑ᶠ c : GL (Fin n) (w.adicCompletion K) ⧸ integralGL (w.adicCompletion K) n,
      h c.out • rhoL μ w c.out u := by
  let E : (LL μ →L[ℂ] LL μ) →+ LL μ := { toFun := fun T => T u, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hf : (Function.support fun c : GL (Fin n) (w.adicCompletion K) ⧸ integralGL (w.adicCompletion K) n =>
      h c.out • rhoL μ w c.out).Finite := by
    refine hfin.subset fun c hc h0 => hc ?_
    exact (congrArg (fun t : ℂ => t • rhoL μ w c.out) h0).trans (zero_smul ℂ _)
  exact AddMonoidHom.map_finsum E hf

private theorem scal_eq (N : ℕ) :
    (((Ideal.absNorm w.asIdeal : ℝ) ^ (-(N : ℝ) / 2) : ℝ) : ℂ) = (sqrtQ (w.adicCompletion K) ^ N)⁻¹ := by
  have hq : qF (w.adicCompletion K) = Ideal.absNorm w.asIdeal := GroundTheory.Global.natCard_residueField_adicCompletion w
  have hq0 : (0 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := Nat.cast_nonneg _
  have hs : sqrtQ (w.adicCompletion K) = ((Real.sqrt (Ideal.absNorm w.asIdeal : ℝ) : ℝ) : ℂ) := by
    rw [sqrtQ, hq, Real.coe_sqrt, NNReal.coe_natCast]
  rw [hs, ← Complex.ofReal_pow, ← Complex.ofReal_inv]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq0, ← Real.rpow_neg hq0]
  congr 1
  ring

end Glob

section Main

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K)
  [MeasurableSpace (GL (Fin n) (w.adicCompletion K))] [BorelSpace (GL (Fin n) (w.adicCompletion K))]
  (m : Measure (GL (Fin n) (w.adicCompletion K))) [m.IsHaarMeasure]

private theorem out_mem_iff (i : Fin n) (c : GL (Fin n) (w.adicCompletion K) ⧸ integralGL (w.adicCompletion K) n) :
    c.out ∈ minusculeSet (w.adicCompletion K) n ((i : ℕ) + 1) ↔
      ∃ k ∈ integralGL (w.adicCompletion K) n, c = QuotientGroup.mk
        (k * Cartan.diagPow (w.adicCompletion K) n fun a => if a ≤ i then 1 else 0) := by
  have hx : (fun a : Fin n => if (a : ℕ) < (i : ℕ) + 1 then (1 : ℤ) else 0) = fun a => if a ≤ i then 1 else 0 := by
    funext a
    simp only [Nat.lt_succ_iff, Fin.le_def]
  rw [mem_minusculeSet_iff (Nat.succ_le_of_lt i.2), hx]
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    exact ⟨a, ha, by rw [← c.out_eq', e]; exact QuotientGroup.mk_mul_of_mem _ hb⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul (integralGL (w.adicCompletion K) n)
      (k * Cartan.diagPow (w.adicCompletion K) n fun a => if a ≤ i then 1 else 0)
    exact ⟨k, hk, b, b.2, hb⟩

private theorem heckeAct_Hs (hm : m.real (integralGL (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) = 1)
    (i : Fin n) {u : LL μ} (hu : u ∈ fixedVectors (rr μ w) (integralGL (w.adicCompletion K) n)) :
    heckeAct m (rr μ w) (Hs m i : HeckeAlgebra m) u = Tsph μ w i u := by
  classical
  have hKo := isOpen_integralGL (w.adicCompletion K) n
  have hKc := isCompact_integralGL (w.adicCompletion K) n
  obtain ⟨hS, -⟩ := UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w (integralGL (w.adicCompletion K) n)
    (Cartan.diagPow (w.adicCompletion K) n fun a => if a ≤ i then 1 else 0) hKo hKc
  have hp : prj (fixL μ w (integralGL (w.adicCompletion K) n)) u = u :=
    (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.2.2.1 u ((mem_fix μ w _ u).2 hu)
  have hT := (heckeAct_eq_finsum m (rr μ w) hm (minusculeHecke m ((i : ℕ) + 1)) hu).2
  have hsm := smooth_of_mem_fixedVectors hKo hu
  rw [Hs, val_smul, HeckeAlgebra.coe_smul, heckeAct_smul_left _ (minusculeHecke m ((i : ℕ) + 1) : HeckeAlgebra m).mem hsm,
    hT, Tsph, ContinuousLinearMap.smul_apply, Hop, ContinuousLinearMap.comp_apply, hp, scal_eq]
  congr 1
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, ContinuousLinearMap.sum_apply,
    finsum_eq_sum_of_support_subset (s := hS.toFinset)]
  · refine Finset.sum_congr rfl fun c hc => ?_
    rw [minusculeHecke_apply, Set.indicator_of_mem ((out_mem_iff w i c).2 ((Set.Finite.mem_toFinset hS).1 hc)), one_smul,
      rr_apply]
  · intro c hc
    rw [Set.Finite.coe_toFinset]
    refine (out_mem_iff w i c).1 ?_
    by_contra h
    apply hc
    simp only [minusculeHecke_apply, Set.indicator_of_notMem h, zero_smul]

private theorem core (hm : m.real (integralGL (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) = 1)
    {𝔞 : Amp μ} {ev : PR K n →+* (LL μ →L[ℂ] LL μ)} (hev : 𝔞.IsEv ev) (hw : w ∉ 𝔞.S) (p : MvPolynomial (Fin n) ℂ) :
    ∀ v : fixedVectors (rr μ w) (integralGL (w.adicCompletion K) n),
      ((aeval (Hs m) p • v : fixedVectors (rr μ w) (integralGL (w.adicCompletion K) n)) : LL μ) =
        ev (map C (atPl w p)) (v : LL μ) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    intro v
    rw [aeval_C, algebraMap_smul_fixedVectors]
    simp [atPl, hev.const]
  | add p q hp hq =>
    intro v
    rw [map_add, add_smul, Submodule.coe_add, hp, hq]
    simp [atPl]
  | mul_X p i ih =>
    intro v
    rw [map_mul, aeval_X, mul_smul, ih]
    have h1 : (((Hs m i) • v : fixedVectors (rr μ w) (integralGL (w.adicCompletion K) n)) : LL μ) = Tsph μ w i v :=
      heckeAct_Hs μ w m hm i v.2
    have h2 : (map C (atPl w (p * X i)) : PR K n) = map C (atPl w p) * X (w, i) := by
      simp [atPl]
    rw [h1, h2, map_mul, hev.hecke w hw i]
    rfl

end Main

theorem UpperTheory.ConvolutionTheory.GM.sphAct :
    SphAct := by
  intro K _ _ n _ μ _ 𝔞 ev hev w hw p h hsph u hu
  obtain ⟨_, _, m, _, hm1, H, hH, hS⟩ := hsph
  have hm : m.real (integralGL (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) = 1 := by
    simp [Measure.real, hm1]
  obtain rfl : h = fun x => (H : HeckeAlgebra m) x := funext fun x => (hH x).symm
  have hu' := (mem_fix μ w _ u).1 hu
  obtain ⟨hfin, he⟩ := heckeAct_eq_finsum m (rr μ w) hm H hu'
  have hc := core μ w m hm hev hw p ⟨u, hu'⟩
  rw [← eq_aeval m hm H p hS] at hc
  rw [sphOp_apply μ w _ hfin u]
  exact (he.symm.trans hc)
