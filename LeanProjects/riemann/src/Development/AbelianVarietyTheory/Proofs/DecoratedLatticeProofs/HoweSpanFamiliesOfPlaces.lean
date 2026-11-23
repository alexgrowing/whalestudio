import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockSubstitutionIdentitiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HoweDualityUnitarySubstitutionSpanUnitStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanTprodOfCommuteAtEachPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPiTensorMvPolynomialEquivBlocksStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylDeterminantTwistTensorFiniteDimensionalStablStatement
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.KJInf.HoweDualityMaps

variable {ι : Type} {a b : ℕ}

def jY (a : ℕ) (τ : ι) : PY Unit a →ₐ[ℂ] PY ι a := rename fun x => (τ, x.2)

def jZ (a b : ℕ) (τ : ι) : FP Unit a b →ₐ[ℂ] FP ι a b := rename fun x => (τ, x.2)

theorem lft_jY (g : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) (F : PY Unit a) :
    lft g (jY a τ F) = jY a τ (lft (fun _ => g τ) F) := by
  have : (lft g).comp (jY a τ) = (jY a τ).comp (lft (fun _ : Unit => g τ)) := by
    apply MvPolynomial.algHom_ext; intro v
    simp [lft, jY, aeval_X, rename_X, map_sum, map_mul, rename_C]
  exact DFunLike.congr_fun this F

theorem mvZ_jZ (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ) (τ : ι) (P : FP Unit a b) :
    mvZ g h (jZ a b τ P) = jZ a b τ (mvZ (fun _ => g τ) (fun _ => h τ) P) := by
  have : (mvZ g h).comp (jZ a b τ) = (jZ a b τ).comp (mvZ (fun _ : Unit => g τ) (fun _ => h τ)) := by
    apply MvPolynomial.algHom_ext; intro v
    simp [mvZ, jZ, aeval_X, rename_X, map_sum, map_mul, rename_C]
  exact DFunLike.congr_fun this P

theorem subY_jY (hab : a ≤ b) (y' : ι → Matrix (Fin b) (Fin b) ℂ) (τ : ι) (F : PY Unit a) :
    subY hab y' (jY a τ F) = jZ a b τ (subY hab (fun _ => y' τ) F) := by
  have : (subY hab y').comp (jY a τ) = (jZ a b τ).comp (subY hab (fun _ : Unit => y' τ)) := by
    apply MvPolynomial.algHom_ext; intro v
    simp [subY, jZ, jY, aeval_X, rename_X, map_sum, map_mul, rename_C]
  exact DFunLike.congr_fun this F

theorem tenU (ι σ : Type) [Fintype ι] [DecidableEq ι] :
    ∃ e : PiTensorProduct ℂ (fun _ : ι => MvPolynomial (Unit × σ) ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ,
      (∀ f, e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (fun x : Unit × σ => (τ, x.2)) (f τ)) ∧
      ∀ U : ι → Submodule ℂ (MvPolynomial (Unit × σ) ℂ),
        Function.Injective (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) ∧
        LinearMap.range (e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) =
          Submodule.span ℂ {p | ∃ f : ι → MvPolynomial (Unit × σ) ℂ, (∀ τ, f τ ∈ U τ) ∧
            p = ∏ τ, rename (fun x : Unit × σ => (τ, x.2)) (f τ)} := by
  obtain ⟨e0, h1, h2⟩ := GlobalTheory.T.exists_piTensorMvPolynomialEquiv_blocks ι (Unit × σ)
  let r : MvPolynomial (ι × Unit × σ) ℂ ≃ₐ[ℂ] MvPolynomial (ι × σ) ℂ :=
    renameEquiv ℂ (Equiv.prodCongr (Equiv.refl ι) (Equiv.uniqueProd σ Unit))
  have hr : ∀ τ (p : MvPolynomial (Unit × σ) ℂ), r (rename (Prod.mk τ) p) = rename (fun x : Unit × σ => (τ, x.2)) p := by
    intro τ p
    simp only [r, renameEquiv_apply, rename_rename]
    rfl
  refine ⟨e0.trans r.toLinearEquiv, ?_, ?_⟩
  · intro f
    simp only [LinearEquiv.trans_apply, h1, AlgEquiv.toLinearEquiv_apply, map_prod, hr]
  · intro U
    obtain ⟨hi, hran⟩ := h2 U
    have hc : (e0.trans r.toLinearEquiv).toLinearMap ∘ₗ (PiTensorProduct.map fun τ => (U τ).subtype) =
        r.toLinearEquiv.toLinearMap ∘ₗ (e0.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (U τ).subtype) := rfl
    rw [hc]
    refine ⟨r.toLinearEquiv.injective.comp hi, ?_⟩
    rw [LinearMap.range_comp, hran, Submodule.map_span]
    congr 1
    ext p
    constructor
    · rintro ⟨q, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, hf, by simp only [LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply, map_prod, hr]⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨_, ⟨f, hf, rfl⟩, by simp only [LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply, map_prod, hr]⟩

theorem mem_vn_unit (l : DomWeight a) (n : ℕ) (F : PY Unit a) :
    F ∈ Vn (fun _ : Unit => l) (fun _ => n) ↔
      ∃ f ∈ delSq ℂ a l, F = rename (Prod.mk ()) f * frDet ℂ a () ^ n := by
  have hS : {p | ∃ f : Unit → MvPolynomial (Fin a × Fin a) ℂ, (∀ τ, f τ ∈ delSq ℂ a l) ∧ p = ten f} =
      (rename (Prod.mk () : Fin a × Fin a → Unit × Fin a × Fin a) : _ →ₐ[ℂ] PY Unit a).toLinearMap '' (delSq ℂ a l : Set _) := by
    ext p
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f (), hf (), by simp [ten]⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨fun _ => f, fun _ => hf, by simp [ten]⟩
  have hC : CSpan (fun _ : Unit => l) = (delSq ℂ a l).map (rename (Prod.mk () : Fin a × Fin a → Unit × Fin a × Fin a) : _ →ₐ[ℂ] PY Unit a).toLinearMap := by
    rw [CSpan, hS, Submodule.span_image, Submodule.span_eq]
  simp only [Vn, hC, Submodule.mem_map]
  constructor
  · rintro ⟨G, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨f, hf, by simp⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨_, ⟨f, hf, rfl⟩, by simp⟩

theorem span_jY [Fintype ι] (lam : ι → DomWeight a) (n : ι → ℕ) :
    Submodule.span ℂ {p | ∃ f : ι → PY Unit a, (∀ τ, f τ ∈ Vn (fun _ : Unit => lam τ) (fun _ => n τ)) ∧
      p = ∏ τ, rename (fun x : Unit × Fin a × Fin a => (τ, x.2)) (f τ)} = Vn lam n := by
  have hj : ∀ (τ : ι) (f : MvPolynomial (Fin a × Fin a) ℂ),
      rename (fun x : Unit × Fin a × Fin a => (τ, x.2)) (rename (Prod.mk ()) f) = rename (Prod.mk τ) f := by
    intro τ f; rw [rename_rename]; rfl
  have hd : ∀ τ : ι, rename (fun x : Unit × Fin a × Fin a => (τ, x.2)) (frDet ℂ a ()) = frDet ℂ a τ := by
    intro τ; simp only [frDet]; rw [AlgHom.map_det]; congr 1; ext i j; simp [rename_X]
  rw [Vn, CSpan, Submodule.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨F, hF, rfl⟩
    choose f hf hF using fun τ => (mem_vn_unit (lam τ) (n τ) (F τ)).1 (hF τ)
    refine ⟨ten f, ⟨f, hf, rfl⟩, ?_⟩
    simp [hF, map_mul, map_pow, hj, hd, ten, Finset.prod_mul_distrib]
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨fun τ => rename (Prod.mk ()) (f τ) * frDet ℂ a () ^ n τ,
      fun τ => (mem_vn_unit _ _ _).2 ⟨f τ, hf τ, rfl⟩, ?_⟩
    simp [map_mul, map_pow, hj, hd, ten, Finset.prod_mul_distrib]

theorem lftMap [Fintype ι] [DecidableEq ι] (eY : PiTensorProduct ℂ (fun _ : ι => PY Unit a) ≃ₗ[ℂ] PY ι a)
    (hY1 : ∀ f, eY (PiTensorProduct.tprod ℂ f) = ∏ τ, jY a τ (f τ)) (V : ι → Submodule ℂ (PY Unit a))
    (hV : ∀ τ k, ∀ F ∈ V τ, lft (fun _ : Unit => k) F ∈ V τ) (τ : ι) (k : Matrix (Fin a) (Fin a) ℂ) :
    eY.toLinearMap ∘ₗ PiTensorProduct.map (fun σ => (V σ).subtype) ∘ₗ
      PiTensorProduct.map (Function.update (fun σ => (LinearMap.id : V σ →ₗ[ℂ] V σ)) τ
        ((lft (fun _ : Unit => k)).toLinearMap.restrict (fun F hF => hV τ k F hF))) =
    (lft (Function.update 1 τ k)).toLinearMap ∘ₗ eY.toLinearMap ∘ₗ PiTensorProduct.map (fun σ => (V σ).subtype) := by
  apply PiTensorProduct.ext; apply MultilinearMap.ext; intro f
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    PiTensorProduct.map_tprod, LinearEquiv.coe_coe, hY1, AlgHom.toLinearMap_apply, map_prod, lft_jY]
  apply Finset.prod_congr rfl; intro σ _
  by_cases h : σ = τ
  · subst h; simp [LinearMap.restrict_apply]; rfl
  · simp [Function.update_of_ne h, (GlobalTheory.T.fockSubstitution_identities Unit a a le_rfl).2.2.2.2.1]

theorem mvZMap [Fintype ι] [DecidableEq ι] (hab : a ≤ b) (eZ : PiTensorProduct ℂ (fun _ : ι => FP Unit a b) ≃ₗ[ℂ] FP ι a b)
    (hZ1 : ∀ f, eZ (PiTensorProduct.tprod ℂ f) = ∏ τ, jZ a b τ (f τ)) (τ : ι) (k : Matrix (Fin a) (Fin a) ℂ) :
    eZ.toLinearMap ∘ₗ PiTensorProduct.map (Function.update (fun σ => (LinearMap.id : FP Unit a b →ₗ[ℂ] FP Unit a b)) τ
        (mvZ (fun _ : Unit => k) (fun _ => 1)).toLinearMap) =
    (mvZ (Function.update 1 τ k) (fun _ => 1)).toLinearMap ∘ₗ eZ.toLinearMap := by
  apply PiTensorProduct.ext; apply MultilinearMap.ext; intro f
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    PiTensorProduct.map_tprod, LinearEquiv.coe_coe, hZ1, AlgHom.toLinearMap_apply, map_prod, mvZ_jZ]
  apply Finset.prod_congr rfl; intro σ _
  by_cases h : σ = τ
  · subst h; simp
  · simp [Function.update_of_ne h, (GlobalTheory.T.fockSubstitution_identities Unit a b hab).2.2.1]

def RepMaps {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [Fintype ι] (hab : a ≤ b)
    (Φ : A →ₗ[ℂ] PY ι a) (eZ : B ≃ₗ[ℂ] FP ι a b) : Submodule ℂ (A →ₗ[ℂ] B) where
  carrier := {T | ∃ (m : ℕ) (y' : Fin m → ι → Matrix (Fin b) (Fin b) ℂ) (s : Fin m → ℂ),
    (∀ j, IsInv (y' j)) ∧ ∀ v, eZ (T v) = ∑ j, s j • subY hab (y' j) (Φ v)}
  zero_mem' := ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun v => by simp⟩
  add_mem' := by
    rintro T1 T2 ⟨m1, y1, s1, i1, h1⟩ ⟨m2, y2, s2, i2, h2⟩
    refine ⟨m1 + m2, Fin.append y1 y2, Fin.append s1 s2, ?_, ?_⟩
    · intro j; refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [i1, i2]
    · intro v; simp [Fin.sum_univ_add, h1, h2]
  smul_mem' := by
    rintro c T ⟨m, y, s, i, h⟩
    refine ⟨m, y, fun j => c * s j, i, fun v => ?_⟩
    simp [h, Finset.smul_sum, mul_smul]

theorem pure_rep [Fintype ι] [DecidableEq ι] (hab : a ≤ b) (ha : 0 < a) (lam : ι → DomWeight a) (n : ι → ℕ)
    (eY : PiTensorProduct ℂ (fun _ : ι => PY Unit a) ≃ₗ[ℂ] PY ι a)
    (hY1 : ∀ f, eY (PiTensorProduct.tprod ℂ f) = ∏ τ, jY a τ (f τ))
    (eZ : PiTensorProduct ℂ (fun _ : ι => FP Unit a b) ≃ₗ[ℂ] FP ι a b)
    (hZ1 : ∀ f, eZ (PiTensorProduct.tprod ℂ f) = ∏ τ, jZ a b τ (f τ))
    (hV : ∀ τ k, ∀ F ∈ Vn (fun _ : Unit => lam τ) (fun _ => n τ), lft (fun _ : Unit => k) F ∈ Vn (fun _ : Unit => lam τ) (fun _ => n τ))
    (t : ∀ τ, Vn (fun _ : Unit => lam τ) (fun _ => n τ) →ₗ[ℂ] FP Unit a b)
    (ht : ∀ τ, ∀ k ∈ Matrix.unitaryGroup (Fin a) ℂ,
      t τ ∘ₗ (lft (fun _ : Unit => k)).toLinearMap.restrict (fun F hF => hV τ k F hF) =
        (mvZ (fun _ : Unit => k) (fun _ => 1)).toLinearMap ∘ₗ t τ) :
    PiTensorProduct.map t ∈ RepMaps hab
      (eY.toLinearMap ∘ₗ PiTensorProduct.map (fun τ => (Vn (fun _ : Unit => lam τ) (fun _ => n τ)).subtype)) eZ := by
  have hext : ∀ τ, ∃ T : PY Unit a →ₗ[ℂ] FP Unit a b, T ∘ₗ (Vn (fun _ : Unit => lam τ) (fun _ => n τ)).subtype = t τ :=
    fun τ => LinearMap.exists_extend (t τ)
  choose T hT using hext
  have hH : ∀ τ, ∃ (m : ℕ) (y' : Fin m → Unit → Matrix (Fin b) (Fin b) ℂ) (s : Fin m → ℂ), (∀ j, IsInv (y' j)) ∧
      ∀ F ∈ Vn (fun _ : Unit => lam τ) (fun _ => n τ), T τ F = ∑ j, s j • subY hab (y' j) F := by
    intro τ
    refine GlobalTheory.T.howeDualityUnitarySubstitutionSpan_unit a b hab ha (fun _ => lam τ) (fun _ => n τ) (T τ) ?_
    intro k hk F hF
    have hk' : k = fun _ => k () := funext fun u => by cases u; rfl
    have e1 : T τ (lft k F) = t τ ((lft (fun _ : Unit => k ())).toLinearMap.restrict (fun F hF => hV τ (k ()) F hF) ⟨F, hF⟩) := by
      rw [← hT τ, hk']; rfl
    have e2 : T τ F = t τ ⟨F, hF⟩ := by rw [← hT τ]; rfl
    rw [e1, e2, hk']
    exact LinearMap.congr_fun (ht τ (k ()) (hk ())) ⟨F, hF⟩
  choose m y' s hinv hrep using hH
  let eC := Fintype.equivFin (∀ τ, Fin (m τ))
  refine ⟨Fintype.card (∀ τ, Fin (m τ)), fun i τ => y' τ (eC.symm i τ) (), fun i => ∏ τ, s τ (eC.symm i τ), ?_, ?_⟩
  · intro i τ; exact hinv τ _ ()
  · intro v
    suffices H : eZ.toLinearMap ∘ₗ PiTensorProduct.map t = ∑ i, (∏ τ, s τ (eC.symm i τ)) •
        ((subY hab (fun τ => y' τ (eC.symm i τ) ())).toLinearMap ∘ₗ eY.toLinearMap ∘ₗ
          PiTensorProduct.map (fun τ => (Vn (fun _ : Unit => lam τ) (fun _ => n τ)).subtype)) by
      have := LinearMap.congr_fun H v
      simpa using this
    apply PiTensorProduct.ext; apply MultilinearMap.ext; intro f
    have hy : ∀ τ j, (fun _ : Unit => y' τ j ()) = y' τ j := fun τ j => funext fun u => by cases u; rfl
    have ht' : ∀ τ, t τ (f τ) = ∑ j, s τ j • subY hab (y' τ j) (f τ : PY Unit a) := by
      intro τ; rw [← hT τ]; exact hrep τ _ (f τ).2
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      PiTensorProduct.map_tprod, LinearEquiv.coe_coe, hY1, hZ1, LinearMap.sum_apply,
      LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_prod, subY_jY, ht', map_sum, map_smul, hy,
      Submodule.coe_subtype]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, ← Equiv.sum_comp eC.symm]
    apply Finset.sum_congr rfl; intro i _
    simp only [Algebra.smul_def, Finset.prod_mul_distrib, map_prod]

end GlobalTheory.KJInf.HoweDualityMaps

open GlobalTheory.KJInf.HoweDualityMaps in

theorem GlobalTheory.KJInf.howeSpan_all : ∀ (ι : Type) [Fintype ι], HoweSpan ι := by
  intro ι _ a b hab ha lam n Q hQ
  classical
  obtain ⟨eY, hY1, hY2⟩ := tenU ι (Fin a × Fin a)
  obtain ⟨eZ, hZ1, -⟩ := tenU ι (Fin b × Fin a)
  have hY1' : ∀ f, eY (PiTensorProduct.tprod ℂ f) = ∏ τ, jY a τ (f τ) := hY1
  have hZ1' : ∀ f, eZ (PiTensorProduct.tprod ℂ f) = ∏ τ, jZ a b τ (f τ) := hZ1
  let V : ι → Submodule ℂ (PY Unit a) := fun τ => Vn (fun _ : Unit => lam τ) (fun _ => n τ)
  have hV : ∀ τ k, ∀ F ∈ V τ, lft (fun _ : Unit => k) F ∈ V τ := fun τ k F hF =>
    (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable Unit a (fun _ => lam τ) (fun _ => n τ)).2 (fun _ => k) F hF
  haveI : ∀ τ, FiniteDimensional ℂ (V τ) := fun τ => (GlobalTheory.T.weylDeterminantTwistTensor_finiteDimensional_stable Unit a (fun _ => lam τ) (fun _ => n τ)).1
  let ΦY := eY.toLinearMap ∘ₗ PiTensorProduct.map (fun τ => (V τ).subtype)
  have hrange : LinearMap.range ΦY = Vn lam n := by
    rw [(hY2 V).2]; exact span_jY lam n
  let Q' := eZ.symm.toLinearMap ∘ₗ Q ∘ₗ ΦY
  let R : ∀ τ, Set ((V τ →ₗ[ℂ] V τ) × (FP Unit a b →ₗ[ℂ] FP Unit a b)) := fun τ =>
    {p | ∃ k ∈ Matrix.unitaryGroup (Fin a) ℂ, p = ((lft (fun _ : Unit => k)).toLinearMap.restrict
      (fun F hF => hV τ k F hF), (mvZ (fun _ : Unit => k) (fun _ => 1)).toLinearMap)}
  have hcomm : ∀ τ, ∀ p ∈ R τ, Q' ∘ₗ PiTensorProduct.map (Function.update (fun σ => (LinearMap.id : V σ →ₗ[ℂ] V σ)) τ p.1) =
      PiTensorProduct.map (Function.update (fun σ => (LinearMap.id : FP Unit a b →ₗ[ℂ] FP Unit a b)) τ p.2) ∘ₗ Q' := by
    rintro τ _ ⟨k, hk, rfl⟩
    have hU : IsUni (Function.update (1 : ι → Matrix (Fin a) (Fin a) ℂ) τ k) := by
      intro σ
      by_cases h : σ = τ
      · subst h; simpa using hk
      · simp only [Function.update_of_ne h, Pi.one_apply]; exact one_mem _
    apply LinearMap.ext; intro v
    apply eZ.injective
    have h1 := LinearMap.congr_fun (lftMap eY hY1' V hV τ k) v
    have h2 := LinearMap.congr_fun (mvZMap hab eZ hZ1' τ k) (Q' v)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply] at h1 h2
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Q', ΦY, LinearEquiv.apply_symm_apply] at h2 ⊢
    rw [h2, h1]
    exact hQ _ hU _ (hrange ▸ LinearMap.mem_range_self ΦY v)
  have hsp := GlobalTheory.T.mem_span_tprod_of_commute_at_each_place ι (fun τ => V τ) (fun _ => FP Unit a b) R Q' hcomm
  have hle : Submodule.span ℂ {T | ∃ t : ∀ τ, V τ →ₗ[ℂ] FP Unit a b, (∀ τ, ∀ p ∈ R τ, t τ ∘ₗ p.1 = p.2 ∘ₗ t τ) ∧
      T = PiTensorProduct.map t} ≤ RepMaps hab ΦY eZ := by
    rw [Submodule.span_le]
    rintro T ⟨t, ht, rfl⟩
    exact pure_rep hab ha lam n eY hY1' eZ hZ1' hV t (fun τ k hk => ht τ _ ⟨k, hk, rfl⟩)
  obtain ⟨m, y', s, hinv, hrep⟩ := hle hsp
  refine ⟨m, y', s, hinv, ?_⟩
  intro F hF
  rw [← hrange] at hF
  obtain ⟨v, rfl⟩ := hF
  have := hrep v
  simpa [Q'] using this

example : ∀ (ι : Type) [Fintype ι], HoweSpan ι := GlobalTheory.KJInf.howeSpan_all
