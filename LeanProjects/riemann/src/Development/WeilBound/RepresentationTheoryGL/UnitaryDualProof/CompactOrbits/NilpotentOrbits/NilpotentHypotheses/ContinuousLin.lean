import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.NilpotentHypotheses.PiZLin

noncomputable section

open Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Asm

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem free_etale_sheaf_zmod_exists_hom_sending_generator : ∃ t : kˣ, 0 < nabs k t ∧ nabs k t < 1 := by
  obtain ⟨r', hr', hr⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation k)
  have hr0 : r' ≠ 0 := by
    intro h
    simp [h] at hr'
  refine ⟨Units.mk0 r' hr0, nabs_pos k _, ?_⟩
  have h1 := nabs_lt_of_valuation_lt (k := k) (x := Units.mk0 r' hr0) (y := 1) (by simpa using hr)
  simpa [nabs_one] using h1

theorem nabs_inv (t : kˣ) : nabs k t⁻¹ = (nabs k t)⁻¹ := by
  simp [nabs]

variable {k}

theorem bz_add {n : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {x y : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z)
    (hy : y ∈ Bz Z) : x + y ∈ Bz Z := by
  simp only [Bz, Set.mem_setOf_eq] at hx hy ⊢
  intro a ha
  rw [mul_add, add_mul, hx a ha, hy a ha]

theorem bz_sub {n : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {x y : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z)
    (hy : y ∈ Bz Z) : x - y ∈ Bz Z := by
  simp only [Bz, Set.mem_setOf_eq] at hx hy ⊢
  intro a ha
  rw [mul_sub, sub_mul, hx a ha, hy a ha]

theorem bz_smul {n : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (c : k) {x : Matrix (Fin n) (Fin n) k}
    (hx : x ∈ Bz Z) : c • x ∈ Bz Z := by
  simp only [Bz, Set.mem_setOf_eq] at hx ⊢
  intro a ha
  rw [Matrix.mul_smul, hx a ha, Matrix.smul_mul]

theorem z_bz {n : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) {c : Matrix (Fin n) (Fin n) k}
    (hc : c ∈ Z) : c ∈ Bz Z := by
  simp only [Bz, Set.mem_setOf_eq]
  intro a ha
  exact hZ.1 a ha c hc

variable [CharZero k]

theorem sig_eq {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (L : Matrix (Fin n) (Fin n) k →ₗ[k] Matrix (Fin n) (Fin n) k)
    (hL : ∀ x, piZ Z x = L x) (t : kˣ) (p : Sp k n) : sig Z t p = (L p.1 + (t : k) • (p.1 - L p.1), p.2) := by
  simp [sig, hL]

theorem sig_sig {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (s t : kˣ) (p : Sp k n) :
    sig Z s (sig Z t p) = sig Z (s * t) p := by
  obtain ⟨L, hL, hLZ, -, hLc⟩ := piZ_lin k Z hZ
  have hLL : ∀ x, L (L x) = L x := fun x => hLc _ (hLZ x)
  simp only [sig_eq Z L hL]
  refine Prod.ext ?_ rfl
  simp only [map_add, map_smul, map_sub, hLL, sub_self, smul_zero, add_zero, add_sub_cancel_left,
    Units.val_mul, mul_smul]

theorem sig_one {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (p : Sp k n) : sig Z 1 p = p := by
  obtain ⟨L, hL, -, -, -⟩ := piZ_lin k Z hZ
  rw [sig_eq Z L hL]
  refine Prod.ext ?_ rfl
  simp

theorem sig_inv_sig {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (t : kˣ) (p : Sp k n) :
    sig Z t⁻¹ (sig Z t p) = p := by
  rw [sig_sig Z hZ, inv_mul_cancel, sig_one Z hZ]

theorem sig_sig_inv {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (t : kˣ) (p : Sp k n) :
    sig Z t (sig Z t⁻¹ p) = p := by
  rw [sig_sig Z hZ, mul_inv_cancel, sig_one Z hZ]

theorem continuous_lin {n : ℕ} (L : Matrix (Fin n) (Fin n) k →ₗ[k] Matrix (Fin n) (Fin n) k) : Continuous L := by
  have hL : (L : Matrix (Fin n) (Fin n) k → Matrix (Fin n) (Fin n) k) =
      fun x => ∑ i, ∑ j, x i j • L (Matrix.single i j 1) := by
    funext x
    conv_lhs => rw [Matrix.matrix_eq_sum_single x]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hL]
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (continuous_id.matrix_elem i j).smul continuous_const

theorem continuous_sig {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (t : kˣ) :
    Continuous (sig Z t) := by
  obtain ⟨L, hL, -, -, -⟩ := piZ_lin k Z hZ
  have h1 : sig Z t = fun p => (L p.1 + (t : k) • (p.1 - L p.1), p.2) := funext (sig_eq Z L hL t)
  rw [h1]
  have hc : Continuous (fun p : Matrix (Fin n) (Fin n) k × (Fin n → k) => p.1) := continuous_fst
  have hLc : Continuous (fun p : Matrix (Fin n) (Fin n) k × (Fin n → k) => L p.1) :=
    (continuous_lin L).comp hc
  have hs : Continuous (fun p : Matrix (Fin n) (Fin n) k × (Fin n → k) => (t : k) • (p.1 - L p.1)) :=
    (continuous_const (y := (t : k))).smul (hc.sub hLc)
  exact (hLc.add hs).prodMk continuous_snd

def sigH {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (t : kˣ) : Sp k n ≃ₜ Sp k n where
  toFun := sig Z t
  invFun := sig Z t⁻¹
  left_inv := sig_inv_sig Z hZ t
  right_inv := sig_sig_inv Z hZ t
  continuous_toFun := continuous_sig Z hZ t
  continuous_invFun := continuous_sig Z hZ t⁻¹

theorem comp_sig_mem {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (t : kˣ) {f : Sp k n → ℂ}
    (hf : f ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ) : f ∘ sig Z t ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ := by
  obtain ⟨h1, h2⟩ := (show f ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ ↔
    IsLocallyConstant f ∧ HasCompactSupport f from Iff.rfl).1 hf
  exact (show f ∘ sig Z t ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ ↔
    IsLocallyConstant (f ∘ sig Z t) ∧ HasCompactSupport (f ∘ sig Z t) from Iff.rfl).2
    ⟨h1.comp_continuous (continuous_sig Z hZ t), h2.comp_homeomorph (sigH Z hZ t)⟩

theorem pull_apply {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (t : kˣ) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ)
    (f : Sp k n → ℂ) : pull Z t ξ f = ξ (f ∘ sig Z t) := rfl

theorem pull_supp {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (t : kˣ) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ)
    (h : Supp ξ (Bz Z ×ˢ Set.univ)) : Supp (pull Z t ξ) (Bz Z ×ˢ Set.univ) := by
  obtain ⟨L, hL, hLZ, -, -⟩ := piZ_lin k Z hZ
  intro f hf hvan
  rw [pull_apply]
  have hf' : f ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ ∧ Function.support f ⊆ Set.univ := hf
  refine h (f ∘ sig Z t) (show f ∘ sig Z t ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ ∧
    Function.support (f ∘ sig Z t) ⊆ Set.univ from ⟨comp_sig_mem Z hZ t hf'.1, Set.subset_univ _⟩) ?_
  intro p hp
  refine hvan _ ⟨?_, Set.mem_univ _⟩
  rw [sig_eq Z L hL]
  exact bz_add (z_bz hZ (hLZ _)) (bz_smul _ (bz_sub hp.1 (z_bz hZ (hLZ _))))

theorem pull_inv {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (t : kˣ) :
    pull Z t ∘ₗ pull Z t⁻¹ = LinearMap.id ∧ pull Z t⁻¹ ∘ₗ pull Z t = LinearMap.id := by
  refine ⟨LinearMap.ext fun ξ => LinearMap.ext fun f => ?_, LinearMap.ext fun ξ => LinearMap.ext fun f => ?_⟩
  · show ξ ((f ∘ sig Z t) ∘ sig Z t⁻¹) = ξ f
    congr 1; funext p; simp [sig_sig_inv Z hZ]
  · show ξ ((f ∘ sig Z t⁻¹) ∘ sig Z t) = ξ f
    congr 1; funext p; simp [sig_inv_sig Z hZ]

theorem pull_kills {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (t : kˣ) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ)
    (h : Kills ξ UU) : Kills (pull Z t ξ) UU := by
  intro f hf
  rw [pull_apply]
  have hf' : f ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ ∧ Function.support f ⊆ UU := hf
  refine h (f ∘ sig Z t) (show f ∘ sig Z t ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ ∧
    Function.support (f ∘ sig Z t) ⊆ UU from ⟨comp_sig_mem Z hZ t hf'.1, ?_⟩)
  intro p hp
  have h3 := hf'.2 (show sig Z t p ∈ Function.support f from hp)
  exact h3

theorem supp_sub {n : ℕ} {C : Set (Sp k n)} {ξ η : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (h1 : Supp ξ C) (h2 : Supp η C) (a b : ℂ) :
    Supp (a • ξ - b • η) C := fun f hf h0 => by simp [h1 f hf h0, h2 f hf h0]

theorem prod_supp {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (t : kˣ) (e : ℂ) (a : List ℝ)
    (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) (hξ : Supp ξ (Bz Z ×ˢ Set.univ)) :
    Supp (((a.map fun x => e • pull Z t⁻¹ - (((((nabs k t)⁻¹ : ℝ) ^ x : ℝ)) : ℂ) • LinearMap.id).prod :
      Module.End ℂ ((Sp k n → ℂ) →ₗ[ℂ] ℂ)) ξ) (Bz Z ×ˢ Set.univ) := by
  induction a with
  | nil => simpa using hξ
  | cons x a ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    exact supp_sub (pull_supp Z hZ t⁻¹ _ ih) ih _ _

def Aop {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (t : kˣ) (x : ℝ) :
    Module.End ℂ ((Sp k n → ℂ) →ₗ[ℂ] ℂ) :=
  ((((nabs k t)⁻¹ : ℝ) ^ (dB0 Z : ℝ) : ℝ) : ℂ) • pull Z t⁻¹ - (((((nabs k t)⁻¹ : ℝ) ^ x : ℝ)) : ℂ) • LinearMap.id

def Bop {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (t : kˣ) (x : ℝ) :
    Module.End ℂ ((Sp k n → ℂ) →ₗ[ℂ] ℂ) :=
  pull Z t - (((((nabs k t)⁻¹ : ℝ) ^ x : ℝ)) : ℂ) • LinearMap.id

def Agree {n : ℕ} (η η' : (Sp k n → ℂ) →ₗ[ℂ] ℂ) : Prop := ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), η f = η' f

theorem bop_agree {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (t : kˣ) (x : ℝ)
    {η η' : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (h : Agree η η') : Agree (Bop Z t x η) (Bop Z t x η') := by
  intro f hf
  have hf' : f ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ ∧ Function.support f ⊆ Set.univ := hf
  have hfs : f ∘ sig Z t ∈ supportedIn (Set.univ : Set (Sp k n)) :=
    (show f ∘ sig Z t ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ ∧
      Function.support (f ∘ sig Z t) ⊆ Set.univ from ⟨comp_sig_mem Z hZ t hf'.1, Set.subset_univ _⟩)
  simp only [Bop, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, pull_apply]
  rw [h f hf, h _ hfs]

theorem four_one {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))
    (𝓕 : ((Sp k n → ℂ) →ₗ[ℂ] ℂ) →ₗ[ℂ] ((Sp k n → ℂ) →ₗ[ℂ] ℂ))
    (hF5 : ∀ (t : kˣ) ξ, Supp ξ (Bz Z ×ˢ Set.univ) → ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)),
        𝓕 (pull Z t ξ) f = ((((nabs k t)⁻¹ ^ dB0 Z : ℝ)) : ℂ) * pull Z t⁻¹ (𝓕 ξ) f)
    (t : kˣ) (x : ℝ) (η : (Sp k n → ℂ) →ₗ[ℂ] ℂ) (hη : Supp η (Bz Z ×ˢ Set.univ)) :
    Agree (𝓕 (Aop Z t x η)) (Bop Z t x (𝓕 η)) := by
  intro f hf
  simp only [Aop, Bop, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
  rw [hF5 t⁻¹ η hη f hf, nabs_inv k t, inv_inv t]
  have hpos : 0 < nabs k t := nabs_pos k t
  have hone : (((nabs k t)⁻¹ ^ (dB0 Z : ℝ) : ℝ) : ℂ) * (((nabs k t)⁻¹⁻¹ ^ dB0 Z : ℝ) : ℂ) = 1 := by
    rw [Real.rpow_natCast, ← Complex.ofReal_mul, ← mul_pow, inv_inv, inv_mul_cancel₀ hpos.ne', one_pow,
      Complex.ofReal_one]
  congr 1
  rw [smul_eq_mul, ← mul_assoc, hone, one_mul]

theorem four_prod {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z)
    (𝓕 : ((Sp k n → ℂ) →ₗ[ℂ] ℂ) →ₗ[ℂ] ((Sp k n → ℂ) →ₗ[ℂ] ℂ))
    (hF0 : ∀ ξ, Supp ξ (Bz Z ×ˢ Set.univ) → Supp (𝓕 ξ) (Bz Z ×ˢ Set.univ))
    (hF6 : ∀ ξ, (∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), ξ f = 0) →
        ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), 𝓕 ξ f = 0)
    (hF5 : ∀ (t : kˣ) ξ, Supp ξ (Bz Z ×ˢ Set.univ) → ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)),
        𝓕 (pull Z t ξ) f = ((((nabs k t)⁻¹ ^ dB0 Z : ℝ)) : ℂ) * pull Z t⁻¹ (𝓕 ξ) f)
    (t : kˣ) (a : List ℝ) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) (hξ : Supp ξ (Bz Z ×ˢ Set.univ)) :
    ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)),
    𝓕 (((a.map fun x => ((((nabs k t)⁻¹ : ℝ) ^ (dB0 Z : ℝ) : ℝ) : ℂ) • pull Z t⁻¹ -
        (((((nabs k t)⁻¹ : ℝ) ^ x : ℝ)) : ℂ) • LinearMap.id).prod : Module.End ℂ ((Sp k n → ℂ) →ₗ[ℂ] ℂ)) ξ) f =
      ((a.map fun x => pull Z t - (((((nabs k t)⁻¹ : ℝ) ^ x : ℝ)) : ℂ) • LinearMap.id).prod :
        Module.End ℂ ((Sp k n → ℂ) →ₗ[ℂ] ℂ)) (𝓕 ξ) f := by
  have key : Agree (𝓕 ((a.map fun x => Aop Z t x).prod ξ)) ((a.map fun x => Bop Z t x).prod (𝓕 ξ)) := by
    induction a with
    | nil =>
      intro f hf
      simp
    | cons x a ih =>
      intro f hf
      have hs : Supp ((a.map fun x => Aop Z t x).prod ξ) (Bz Z ×ˢ Set.univ) :=
        prod_supp Z hZ t _ a ξ hξ
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      exact (four_one Z 𝓕 hF5 t x _ hs f hf).trans (bop_agree Z hZ t x ih f hf)
  exact key

end PositivityTheory.RgUd.T.Nil.Asm
