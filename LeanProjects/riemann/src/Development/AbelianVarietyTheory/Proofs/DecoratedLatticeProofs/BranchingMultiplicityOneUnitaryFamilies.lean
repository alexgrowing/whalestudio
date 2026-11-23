import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BrEqv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSmulOfUnitaryEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanTprodOfCommuteAtEachPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPiTensorMvPolynomialEquivBlocks
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.GlobalTheory.GL4.BranchingNormalisedOfAdjoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.BranchFamily

open MvPolynomial

variable {ι : Type} [Fintype ι]

theorem fnOf_ten {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ)
    (y : Frames G) :
    fnOf G s 1 (ten f) y = ∏ σ, ((y.1 σ).det ^ s σ * eval (fun p : Fin n × Fin n => y.1 σ p.1 p.2) (f σ)) := by
  simp only [fnOf, ten, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul, map_prod, eval_rename,
    Finset.prod_mul_distrib]
  rfl

theorem eval_rowAct {n : ℕ} (g y : Matrix (Fin n) (Fin n) ℂ) (f : MvPolynomial (Fin n × Fin n) ℂ) :
    eval (fun p : Fin n × Fin n => y p.1 p.2) (Formalism.GradedWeylDivisibility.rowAct ℂ g f) =
      eval (fun p : Fin n × Fin n => (g * y) p.1 p.2) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]

theorem fnOf_ten_update {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (f : ι → MvPolynomial (Fin n × Fin n) ℂ) (τ : ι) (g : Matrix (Fin n) (Fin n) ℂ) (z z' : Frames G)
    (hz : IsTr (Function.update (1 : ι → Matrix (Fin n) (Fin n) ℂ) τ g) z z') :
    fnOf G s 1 (ten (Function.update f τ (g.det ^ s τ • Formalism.GradedWeylDivisibility.rowAct ℂ g (f τ)))) z = fnOf G s 1 (ten f) z' := by
  rw [fnOf_ten, fnOf_ten]
  refine Finset.prod_congr rfl fun σ _ => ?_
  have h := hz σ
  by_cases hσ : σ = τ
  · subst hσ
    rw [Function.update_self] at h ⊢
    rw [h, smul_eval, eval_rowAct, Matrix.det_mul, mul_zpow]
    ring
  · rw [Function.update_of_ne hσ] at h ⊢
    rw [h, Pi.one_apply, Matrix.one_mul]

def blockDet {n : ℕ} (τ : ι) : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  (Matrix.of fun a b : Fin n => (X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)).det

omit [Fintype ι] in
theorem eval_blockDet {n : ℕ} (τ : ι) (x : ι × Fin n × Fin n → ℂ) :
    eval x (blockDet τ) = (Matrix.of fun a b : Fin n => x (τ, a, b)).det := by
  rw [blockDet, RingHom.map_det]
  congr 1
  ext a b
  simp

theorem fnOf_inj {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (h : ∀ y, fnOf G s 1 P y = 0) : P = 0 := by
  have hD : (∏ τ, blockDet (n := n) τ) * P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero, map_prod]
    by_cases hx : ∀ τ, (Matrix.of fun a b : Fin n => x (τ, a, b)).det ≠ 0
    · let y : Frames G := ⟨fun τ => Matrix.of fun a b => x (τ, a, b), fun τ => isUnit_iff_ne_zero.mpr (hx τ)⟩
      have hy := h y
      simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul] at hy
      have hp : (∏ τ, (y.1 τ).det ^ s τ) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hx τ)
      have he : eval x P = 0 := by
        have := (mul_eq_zero.mp hy).resolve_left hp
        simpa [y] using this
      rw [he, mul_zero]
    · push_neg at hx
      obtain ⟨τ, hτ⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [eval_blockDet]; exact hτ), zero_mul]
  have hne : (∏ τ : ι, blockDet (n := n) τ) ≠ 0 := by
    intro h0
    have := congrArg (eval (fun v : ι × Fin n × Fin n => if v.2.1 = v.2.2 then (1 : ℂ) else 0)) h0
    rw [map_prod, map_zero] at this
    refine (Finset.prod_ne_zero_iff.mpr fun τ _ => ?_) this
    rw [eval_blockDet]
    have : (Matrix.of fun a b : Fin n => if a = b then (1 : ℂ) else 0) = 1 := by
      ext a b
      simp [Matrix.one_apply]
    simp only
    rw [this, Matrix.det_one]
    exact one_ne_zero
  exact (mul_eq_zero.mp hD).resolve_left hne

theorem rowAct_mem {N : ℕ} (lam : DomWeight N) (g : Matrix (Fin N) (Fin N) ℂ) (hg : IsUnit g.det)
    (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ∈ delSq ℂ N lam) : Formalism.GradedWeylDivisibility.rowAct ℂ g f ∈ delSq ℂ N lam := by
  have hgt : IsUnit gᵀ.det := by rwa [Matrix.det_transpose]
  have h := (Formalism.BasicNotions.factSqStable ℂ N lam (Matrix.nonsingInvUnit gᵀ hgt)).2 f hf
  rw [sqAct] at h
  have hne : detPow ℂ N (Matrix.nonsingInvUnit gᵀ hgt) lam.detShift ≠ 0 := by
    rw [detPow]; exact Units.ne_zero _
  rw [Submodule.smul_mem_iff _ hne] at h
  have hv : ((Matrix.nonsingInvUnit gᵀ hgt : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Matrix (Fin N) (Fin N) ℂ)ᵀ = g :=
    Matrix.transpose_transpose g
  rw [← hv]
  simpa using h

def actL {N : ℕ} (lam : DomWeight N) (c : ℤ) (g : Matrix (Fin N) (Fin N) ℂ) : delSq ℂ N lam →ₗ[ℂ] delSq ℂ N lam :=
  if h : ∀ f ∈ delSq ℂ N lam, Formalism.GradedWeylDivisibility.rowAct ℂ g f ∈ delSq ℂ N lam then
    (g.det ^ c) • (Formalism.GradedWeylDivisibility.rowAct ℂ g).toLinearMap.restrict h
  else 0

theorem actL_apply {N : ℕ} (lam : DomWeight N) (c : ℤ) (g : Matrix (Fin N) (Fin N) ℂ) (hg : IsUnit g.det)
    (f : delSq ℂ N lam) : (actL lam c g f).1 = g.det ^ c • Formalism.GradedWeylDivisibility.rowAct ℂ g f.1 := by
  rw [actL, dif_pos (fun f hf => rowAct_mem lam g hg f hf)]
  rfl

theorem span_map_mult_one {V W : ι → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
    [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (C : ∀ τ, Set (V τ →ₗ[ℂ] W τ))
    (hC : ∀ τ, ∀ t ∈ C τ, ∀ t₀ ∈ C τ, t₀ ≠ 0 → ∃ c : ℂ, t = c • t₀)
    (Q Q₀ : PiTensorProduct ℂ V →ₗ[ℂ] PiTensorProduct ℂ W)
    (hQ : Q ∈ Submodule.span ℂ {T | ∃ t : ∀ τ, V τ →ₗ[ℂ] W τ, (∀ τ, t τ ∈ C τ) ∧ T = PiTensorProduct.map t})
    (hQ₀ : Q₀ ∈ Submodule.span ℂ {T | ∃ t : ∀ τ, V τ →ₗ[ℂ] W τ, (∀ τ, t τ ∈ C τ) ∧ T = PiTensorProduct.map t})
    (h0 : Q₀ ≠ 0) : ∃ c : ℂ, Q = c • Q₀ := by
  by_cases hex : ∀ τ, ∃ t ∈ C τ, t ≠ 0
  · choose t0 ht0 hne using hex
    have hle : Submodule.span ℂ {T | ∃ t : ∀ τ, V τ →ₗ[ℂ] W τ, (∀ τ, t τ ∈ C τ) ∧ T = PiTensorProduct.map t} ≤
        ℂ ∙ PiTensorProduct.map t0 := by
      rw [Submodule.span_le]
      rintro _ ⟨t, ht, rfl⟩
      choose c hc using fun τ => hC τ (t τ) (ht τ) (t0 τ) (ht0 τ) (hne τ)
      have : t = fun τ => c τ • t0 τ := funext hc
      have h2 : PiTensorProduct.map t = (∏ τ, c τ) • PiTensorProduct.map t0 := by
        rw [this]
        exact (PiTensorProduct.mapMultilinear ℂ V W).map_smul_univ c t0
      rw [h2]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hle hQ)
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hle hQ₀)
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact h0 (by rw [← hb, zero_smul])
    refine ⟨a / b, ?_⟩
    rw [← ha, ← hb, smul_smul, div_mul_cancel₀ _ hb0]
  · push_neg at hex
    obtain ⟨τ, hτ⟩ := hex
    have hle : Submodule.span ℂ {T | ∃ t : ∀ τ, V τ →ₗ[ℂ] W τ, (∀ τ, t τ ∈ C τ) ∧ T = PiTensorProduct.map t} ≤ ⊥ := by
      rw [Submodule.span_le]
      rintro _ ⟨t, ht, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_bot, ← PiTensorProduct.mapMultilinear_apply]
      exact MultilinearMap.map_coord_zero _ τ (hτ _ (ht τ))
    exact absurd ((Submodule.mem_bot ℂ).mp (hle hQ₀)) h0

theorem isBlock_one {N n : ℕ} (hN : N = n + 1) :
    GlobalTheory.BranchFormula.IsBlock hN (1 : Matrix (Fin N) (Fin N) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ) 1 := by
  subst hN
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, Matrix.one_apply_eq _⟩
  · simp [Formalism.L2.Col.Br.iC, Matrix.one_apply, Fin.ext_iff]
  · refine Matrix.one_apply_ne fun h => ?_
    have := congrArg Fin.val h
    simp [Formalism.L2.Col.Br.iC, Formalism.L2.Col.Br.iL] at this
    omega
  · refine Matrix.one_apply_ne fun h => ?_
    have := congrArg Fin.val h
    simp [Formalism.L2.Col.Br.iC, Formalism.L2.Col.Br.iL] at this
    omega

def emb {N : ℕ} (G : ι → Matrix (Fin N) (Fin N) ℂ) (lam : ι → DomWeight N)
    (e : PiTensorProduct ℂ (fun _ : ι => MvPolynomial (Fin N × Fin N) ℂ) ≃ₗ[ℂ] MvPolynomial (ι × Fin N × Fin N) ℂ) :
    PiTensorProduct ℂ (fun τ => delSq ℂ N (lam τ)) →ₗ[ℂ] (Frames G → ℂ) :=
  fnOf G (shiftOf lam) 1 ∘ₗ e.toLinearMap ∘ₗ PiTensorProduct.map (fun τ => (delSq ℂ N (lam τ)).subtype)

theorem emb_update {N : ℕ} (G : ι → Matrix (Fin N) (Fin N) ℂ) (lam : ι → DomWeight N)
    (e : PiTensorProduct ℂ (fun _ : ι => MvPolynomial (Fin N × Fin N) ℂ) ≃ₗ[ℂ] MvPolynomial (ι × Fin N × Fin N) ℂ)
    (he : ∀ f : ι → MvPolynomial (Fin N × Fin N) ℂ, e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ))
    (τ : ι) (g : Matrix (Fin N) (Fin N) ℂ) (hg : IsUnit g.det) (x : PiTensorProduct ℂ (fun τ => delSq ℂ N (lam τ)))
    (y y' : Frames G) (hy : IsTr (Function.update (1 : ι → Matrix (Fin N) (Fin N) ℂ) τ g) y y') :
    emb G lam e (PiTensorProduct.map (Function.update (fun σ => (LinearMap.id : delSq ℂ N (lam σ) →ₗ[ℂ] delSq ℂ N (lam σ))) τ
      (actL (lam τ) (shiftOf lam τ) g)) x) y = emb G lam e x y' := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, Pi.smul_apply, emb, LinearMap.comp_apply, PiTensorProduct.map_tprod, LinearEquiv.coe_coe, he]
    congr 1
    have hfun : ∀ σ, ((Function.update (fun σ => (LinearMap.id : delSq ℂ N (lam σ) →ₗ[ℂ] delSq ℂ N (lam σ))) τ
        (actL (lam τ) (shiftOf lam τ) g) σ) (f σ) : MvPolynomial (Fin N × Fin N) ℂ) =
        Function.update (fun σ => (f σ : MvPolynomial (Fin N × Fin N) ℂ)) τ
          (g.det ^ shiftOf lam τ • Formalism.GradedWeylDivisibility.rowAct ℂ g (f τ)) σ := by
      intro σ
      by_cases hσ : σ = τ
      · subst hσ
        simp only [Function.update_self]
        exact actL_apply _ _ _ hg _
      · simp only [Function.update_of_ne hσ, LinearMap.id_apply]
    simp only [Submodule.subtype_apply, hfun]
    exact fnOf_ten_update G (shiftOf lam) (fun σ => (f σ : MvPolynomial (Fin N × Fin N) ℂ)) τ g y y' hy
  | add a b ha hb =>
    simp only [map_add, Pi.add_apply, ha, hb]

theorem range_emb {N : ℕ} (G : ι → Matrix (Fin N) (Fin N) ℂ) (lam : ι → DomWeight N)
    (e : PiTensorProduct ℂ (fun _ : ι => MvPolynomial (Fin N × Fin N) ℂ) ≃ₗ[ℂ] MvPolynomial (ι × Fin N × Fin N) ℂ)
    (hU : LinearMap.range (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (delSq ℂ N (lam τ)).subtype) =
      Submodule.span ℂ {p | ∃ f : ι → MvPolynomial (Fin N × Fin N) ℂ, (∀ τ, f τ ∈ delSq ℂ N (lam τ)) ∧
        p = ∏ τ, rename (Prod.mk τ) (f τ)}) :
    LinearMap.range (emb G lam e) = ValC G lam := by
  rw [emb, LinearMap.range_comp, hU]
  rfl

theorem emb_inj {N : ℕ} (G : ι → Matrix (Fin N) (Fin N) ℂ) (lam : ι → DomWeight N)
    (e : PiTensorProduct ℂ (fun _ : ι => MvPolynomial (Fin N × Fin N) ℂ) ≃ₗ[ℂ] MvPolynomial (ι × Fin N × Fin N) ℂ)
    (hI : Function.Injective (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (delSq ℂ N (lam τ)).subtype)) :
    Function.Injective (emb G lam e) := by
  intro x x' h
  apply hI
  rw [← sub_eq_zero]
  apply fnOf_inj G (shiftOf lam)
  intro y
  have := congrFun h y
  rw [map_sub, Pi.sub_apply, sub_eq_zero]
  exact this

theorem isUnit_of_unitary {n : ℕ} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    IsUnit k.det :=
  Matrix.isUnit_det_of_left_inverse (Matrix.mem_unitaryGroup_iff'.mp hk)

theorem mult_one_families : ∀ (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1) (G : ι → Matrix (Fin N) (Fin N) ℂ)
    (G' : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Formalism.L2.Col.Br.Interlace hN (lam τ) (sg τ)) → ∀ T₀, BrEqv hN G G' lam sg T₀ →
      (∃ Φ ∈ ValC G lam, T₀ Φ ≠ 0) → ∀ T, BrEqv hN G G' lam sg T → ∃ c : ℂ, ∀ Φ ∈ ValC G lam, T Φ = c • T₀ Φ := by
  intro ι _ N n hN G G' lam sg hI T₀ hT₀ hex T hT
  obtain ⟨eN, heN, hUN⟩ := GlobalTheory.BlockPoly.exists_blockEquiv ι (Fin N × Fin N)
  obtain ⟨en, hen, hUn⟩ := GlobalTheory.BlockPoly.exists_blockEquiv ι (Fin n × Fin n)
  have rN := range_emb G lam eN (hUN fun τ => delSq ℂ N (lam τ)).2
  have rn := range_emb G' sg en (hUn fun τ => delSq ℂ n (sg τ)).2
  have inj := emb_inj G' sg en (hUn fun τ => delSq ℂ n (sg τ)).1
  have mkQ : ∀ T' : (Frames G → ℂ) →ₗ[ℂ] (Frames G' → ℂ), BrEqv hN G G' lam sg T' →
      ∃ Q' : PiTensorProduct ℂ (fun τ => delSq ℂ N (lam τ)) →ₗ[ℂ] PiTensorProduct ℂ (fun τ => delSq ℂ n (sg τ)),
        ∀ x, emb G' sg en (Q' x) = T' (emb G lam eN x) := by
    intro T' hT'
    have hmem : ∀ x, (T' ∘ₗ emb G lam eN) x ∈ LinearMap.range (emb G' sg en) := fun x => by
      rw [rn]
      exact hT'.1 _ (by rw [← rN]; exact LinearMap.mem_range_self _ x)
    refine ⟨(LinearEquiv.ofInjective _ inj).symm.toLinearMap ∘ₗ (T' ∘ₗ emb G lam eN).codRestrict _ hmem, fun x => ?_⟩
    have h := congrArg Subtype.val ((LinearEquiv.ofInjective _ inj).apply_symm_apply
      ((T' ∘ₗ emb G lam eN).codRestrict _ hmem x))
    rw [LinearEquiv.ofInjective_apply] at h
    exact h
  let R : ∀ τ, Set ((delSq ℂ N (lam τ) →ₗ[ℂ] delSq ℂ N (lam τ)) × (delSq ℂ n (sg τ) →ₗ[ℂ] delSq ℂ n (sg τ))) :=
    fun τ => {p | ∃ (k : Matrix (Fin n) (Fin n) ℂ) (kt : Matrix (Fin N) (Fin N) ℂ),
      k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ GlobalTheory.BranchFormula.IsBlock hN kt k 1 ∧
        p = (actL (lam τ) (shiftOf lam τ) kt, actL (sg τ) (shiftOf sg τ) k)}
  have equiv : ∀ (T' : (Frames G → ℂ) →ₗ[ℂ] (Frames G' → ℂ)) (Q' : PiTensorProduct ℂ (fun τ => delSq ℂ N (lam τ)) →ₗ[ℂ]
      PiTensorProduct ℂ (fun τ => delSq ℂ n (sg τ))), BrEqv hN G G' lam sg T' →
      (∀ x, emb G' sg en (Q' x) = T' (emb G lam eN x)) → ∀ τ, ∀ p ∈ R τ,
        Q' ∘ₗ PiTensorProduct.map (Function.update (fun σ => (LinearMap.id : delSq ℂ N (lam σ) →ₗ[ℂ] delSq ℂ N (lam σ))) τ p.1) =
        PiTensorProduct.map (Function.update (fun σ => (LinearMap.id : delSq ℂ n (sg σ) →ₗ[ℂ] delSq ℂ n (sg σ))) τ p.2) ∘ₗ Q' := by
    rintro T' Q' hT' hQ' τ p ⟨k, kt, hk, hb, rfl⟩
    have hku := isUnit_of_unitary hk
    have hktu : IsUnit kt.det := by rw [hb.det, mul_one]; exact hku
    apply LinearMap.ext
    intro x
    apply inj
    funext z
    have hz' : ∀ σ, IsUnit (Function.update (1 : ι → Matrix (Fin n) (Fin n) ℂ) τ k σ * z.1 σ).det := by
      intro σ
      rw [Matrix.det_mul]
      refine IsUnit.mul ?_ (z.2 σ)
      by_cases hσ : σ = τ
      · subst hσ; rw [Function.update_self]; exact hku
      · rw [Function.update_of_ne hσ, Pi.one_apply, Matrix.det_one]; exact isUnit_one
    let z' : Frames G' := ⟨fun σ => Function.update (1 : ι → Matrix (Fin n) (Fin n) ℂ) τ k σ * z.1 σ, hz'⟩
    have hz : IsTr (Function.update (1 : ι → Matrix (Fin n) (Fin n) ℂ) τ k) z z' := fun σ => rfl
    have hU : IsUni (Function.update (1 : ι → Matrix (Fin n) (Fin n) ℂ) τ k) := by
      intro σ
      by_cases hσ : σ = τ
      · subst hσ; rw [Function.update_self]; exact hk
      · rw [Function.update_of_ne hσ]; exact one_mem _
    have hB : ∀ σ, GlobalTheory.BranchFormula.IsBlock hN (Function.update (1 : ι → Matrix (Fin N) (Fin N) ℂ) τ kt σ)
        (Function.update (1 : ι → Matrix (Fin n) (Fin n) ℂ) τ k σ) 1 := by
      intro σ
      by_cases hσ : σ = τ
      · subst hσ; rw [Function.update_self, Function.update_self]; exact hb
      · rw [Function.update_of_ne hσ, Function.update_of_ne hσ]; exact isBlock_one hN
    simp only [LinearMap.comp_apply]
    rw [hQ', emb_update G' sg en hen τ k hku (Q' x) z z' hz, hQ']
    exact hT'.2 _ _ hU hB (emb G lam eN x) (by rw [← rN]; exact LinearMap.mem_range_self _ x) _
      (fun y y' hy => emb_update G lam eN heN τ kt hktu x y y' hy) z z' hz
  haveI : ∀ τ, FiniteDimensional ℂ (delSq ℂ N (lam τ)) := fun τ => Formalism.L2.GlobalTheoryTheory.TraceIntegrality.delSq_fd _
  let C : ∀ τ, Set (delSq ℂ N (lam τ) →ₗ[ℂ] delSq ℂ n (sg τ)) := fun τ => {t | ∀ p ∈ R τ, t ∘ₗ p.1 = p.2 ∘ₗ t}
  have hC : ∀ τ, ∀ t ∈ C τ, ∀ t₀ ∈ C τ, t₀ ≠ 0 → ∃ c : ℂ, t = c • t₀ := by
    intro τ t ht t₀ ht₀ hne
    refine GlobalTheory.BranchMultOne.eq_smul_of_unitary_equivariant N n hN (lam τ) (sg τ) (hI τ) t t₀
      (fun s hs k hk kt hb f f' hf' => ?_) hne
    have hku := isUnit_of_unitary hk
    have hktu : IsUnit kt.det := by rw [hb.det, mul_one]; exact hku
    have hsC : s ∈ C τ := by rcases hs with rfl | rfl; exacts [ht, ht₀]
    have h0 := LinearMap.congr_fun (hsC _ ⟨k, kt, hk, hb, rfl⟩) f
    simp only [LinearMap.comp_apply] at h0
    have h1 : actL (lam τ) (shiftOf lam τ) kt f = (k.det ^ (lam τ).detShift) • f' := by
      apply Subtype.ext
      rw [actL_apply _ _ _ hktu, Submodule.coe_smul, hf', hb.det, mul_one]
      rfl
    rw [h1, map_smul] at h0
    have h2 := congrArg Subtype.val h0
    rw [Submodule.coe_smul, actL_apply _ _ _ hku] at h2
    exact h2
  obtain ⟨Q, hQ⟩ := mkQ T hT
  obtain ⟨Q₀, hQ₀⟩ := mkQ T₀ hT₀
  have hQ0 : Q₀ ≠ 0 := by
    rintro rfl
    obtain ⟨Φ, hΦ, hne⟩ := hex
    rw [← rN] at hΦ
    obtain ⟨x, rfl⟩ := hΦ
    apply hne
    rw [← hQ₀]
    simp
  obtain ⟨c, hc⟩ := span_map_mult_one C hC Q Q₀
    (GlobalTheory.PiTensorCommute.mem_span_map_of_commute ι _ _ R Q (equiv T Q hT hQ))
    (GlobalTheory.PiTensorCommute.mem_span_map_of_commute ι _ _ R Q₀ (equiv T₀ Q₀ hT₀ hQ₀)) hQ0
  refine ⟨c, fun Φ hΦ => ?_⟩
  rw [← rN] at hΦ
  obtain ⟨x, rfl⟩ := hΦ
  rw [← hQ, ← hQ₀, hc, LinearMap.smul_apply, map_smul]

end GlobalTheory.BranchFamily

end
