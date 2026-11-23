import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightHighestWeightExistsUniqueAntitoneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightPolyMatrixMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolynomialRepGLComplexAlgebraicWeightEvalPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBorelEigenvectorOfPolynomialRepGLComplexStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRationalPointOrbitAlgebraicWeight
import Formalism.LocalToGlobal.Columns.MtAdWtIrr
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwFixEx
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwFixLine
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GLDense
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulVecEqProdSmul

noncomputable section

namespace GlobalTheory.WtClass
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW Filter Topology

section Eig
variable {n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]

theorem exists_beig_mem {Ψ : GL (Fin n) ℂ → Matrix κ κ ℂ} (hΨ : IsPolyRep Ψ) (S : Submodule ℂ (κ → ℂ)) (hS : S ≠ ⊥)
    (hst : ∀ A, ∀ x ∈ S, Ψ A *ᵥ x ∈ S) : ∃ v ∈ S, ∃ lam, IsBEig Ψ v lam := by
  haveI : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS
  let b := Module.finBasis ℂ S
  haveI : Nonempty (Fin (Module.finrank ℂ S)) := b.index_nonempty
  let e : (Fin (Module.finrank ℂ S) → ℂ) →ₗ[ℂ] (κ → ℂ) := S.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have he : Function.Injective e := S.subtype_injective.comp b.equivFun.symm.injective
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective e (LinearMap.ker_eq_bot.2 he)
  have heS : ∀ y, e y ∈ S := fun y => (b.equivFun.symm y).2
  have hep : ∀ x ∈ S, e (p x) = x := by
    intro x hx
    have h1 : x = e (b.equivFun ⟨x, hx⟩) := by simp [e]
    have h2 := LinearMap.congr_fun hp (b.equivFun ⟨x, hx⟩)
    rw [LinearMap.comp_apply, ← h1] at h2
    rw [h2, LinearMap.id_apply, ← h1]
  set I := LinearMap.toMatrix' e with hI
  set Pm := LinearMap.toMatrix' p with hPm
  have hIv : ∀ y, I *ᵥ y = e y := fun y => LinearMap.toMatrix'_mulVec e y
  have hPv : ∀ y, Pm *ᵥ y = p y := fun y => LinearMap.toMatrix'_mulVec p y
  have hact : ∀ A y, (Pm * Ψ A * I) *ᵥ y = p (Ψ A *ᵥ e y) := by
    intro A y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hIv, hPv]
  have hR : IsPolyRep (fun A => Pm * Ψ A * I) := by
    refine ⟨?_, fun A B => ?_, fun i j => ?_⟩
    · refine Matrix.ext_iff_mulVec.2 fun y => ?_
      rw [hact, hΨ.one, Matrix.one_mulVec, Matrix.one_mulVec]
      exact LinearMap.congr_fun hp y
    · refine Matrix.ext_iff_mulVec.2 fun y => ?_
      rw [hact, ← Matrix.mulVec_mulVec, hact, hact, hep _ (hst _ _ (heS y)), hΨ.mul, Matrix.mulVec_mulVec]
    · choose Q hQ using hΨ.poly
      refine ⟨∑ l, (∑ k, MvPolynomial.C (Pm i k) * Q k l) * MvPolynomial.C (I l j), fun B => ?_⟩
      simp only [Matrix.mul_apply, map_sum, map_mul, MvPolynomial.eval_C, hQ]
  obtain ⟨w, lam, hw0, hw⟩ := GlobalTheory.T.exists_borelEigenvector_of_polynomialRepGLComplex n _ _ hR
  refine ⟨e w, heS w, lam, fun h => hw0 (he (by rw [h, map_zero])), fun B hB => ?_⟩
  have h1 := hw B hB
  simp only [hact] at h1
  rw [← hep _ (hst B _ (heS w)), h1, map_smul]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_joint_beig [Nonempty κ] {Φ : (ι → GL (Fin n) ℂ) → Matrix κ κ ℂ} (hmul : ∀ g h, Φ (g * h) = Φ g * Φ h)
    (hpoly : ∀ τ, IsPolyRep fun B => Φ (Pi.mulSingle τ B)) :
    ∃ (v : κ → ℂ) (lam : ι → Fin n → ℤ), v ≠ 0 ∧ ∀ τ, IsBEig (fun B => Φ (Pi.mulSingle τ B)) v (lam τ) := by
  suffices h : ∀ s : Finset ι, ∃ (v : κ → ℂ) (lam : ι → Fin n → ℤ), v ≠ 0 ∧
      ∀ τ ∈ s, IsBEig (fun B => Φ (Pi.mulSingle τ B)) v (lam τ) by
    obtain ⟨v, lam, h0, h1⟩ := h Finset.univ
    exact ⟨v, lam, h0, fun τ => h1 τ (Finset.mem_univ τ)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 1, 0, fun h => one_ne_zero (congrFun h (Classical.arbitrary κ)), by simp⟩
  | insert t s ht ih =>
    obtain ⟨v, lam, hv0, hv⟩ := ih
    let S : Submodule ℂ (κ → ℂ) :=
      { carrier := {w | ∀ τ ∈ s, ∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id →
          Φ (Pi.mulSingle τ B) *ᵥ w = (∏ i, (B.val i i) ^ (lam τ i)) • w}
        add_mem' := fun {a b} ha hb τ hτ B hB => by
          rw [Matrix.mulVec_add, ha τ hτ B hB, hb τ hτ B hB, smul_add]
        zero_mem' := fun τ hτ B hB => by simp
        smul_mem' := fun c a ha τ hτ B hB => by
          rw [Matrix.mulVec_smul, ha τ hτ B hB, smul_comm] }
    have hvS : v ∈ S := fun τ hτ B hB => (hv τ hτ).2 B hB
    have hS : S ≠ ⊥ := fun h => hv0 (by rw [h] at hvS; exact (Submodule.mem_bot ℂ).1 hvS)
    obtain ⟨w, hwS, mu, hw⟩ := exists_beig_mem (hpoly t) S hS (fun A x hx τ hτ B hB => by
      have hne : τ ≠ t := fun h => ht (h ▸ hτ)
      have hcm : (Pi.mulSingle τ B : ι → GL (Fin n) ℂ) * Pi.mulSingle t A = Pi.mulSingle t A * Pi.mulSingle τ B := by
        funext σ
        by_cases h1 : σ = τ
        · subst h1; simp [hne]
        · simp [h1]
      rw [Matrix.mulVec_mulVec, ← hmul, hcm, hmul,
        ← Matrix.mulVec_mulVec, hx τ hτ B hB, Matrix.mulVec_smul])
    refine ⟨w, Function.update lam t mu, hw.1, fun τ hτ => ?_⟩
    rcases Finset.mem_insert.1 hτ with rfl | hτ
    · rwa [Function.update_self]
    · have hne : τ ≠ t := fun h => ht (h ▸ hτ)
      rw [Function.update_of_ne hne]
      exact ⟨hw.1, hwS τ hτ⟩

theorem joint_upper {Φ : (ι → GL (Fin n) ℂ) → Matrix κ κ ℂ} (hone : Φ 1 = 1) (hmul : ∀ g h, Φ (g * h) = Φ g * Φ h)
    {v : κ → ℂ} {lam : ι → Fin n → ℤ} (hv : ∀ τ, IsBEig (fun B => Φ (Pi.mulSingle τ B)) v (lam τ))
    (g : ι → GL (Fin n) ℂ) (hg : ∀ τ, (g τ).val.BlockTriangular id) :
    Φ g *ᵥ v = (∏ τ, ∏ i, ((g τ).val i i) ^ (lam τ i)) • v := by
  first
  | exact @_root_.GlobalTheory.MulVecProduct.mulVec_eq_prod_smul
  | exact _root_.GlobalTheory.MulVecProduct.mulVec_eq_prod_smul
  | (apply _root_.GlobalTheory.MulVecProduct.mulVec_eq_prod_smul <;> assumption)
  | (intros; apply _root_.GlobalTheory.MulVecProduct.mulVec_eq_prod_smul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MulVecProduct.mulVec_eq_prod_smul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MulVecProduct.mulVec_eq_prod_smul ..)

def trGL (B : GL (Fin n) ℂ) : GL (Fin n) ℂ :=
  ⟨B.valᵀ, (B⁻¹).valᵀ, by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]⟩

theorem trGL_mul (A B : GL (Fin n) ℂ) : trGL (A * B) = trGL B * trGL A :=
  Units.ext (Matrix.transpose_mul A.val B.val)

theorem trGL_one : trGL (1 : GL (Fin n) ℂ) = 1 := Units.ext Matrix.transpose_one

theorem trGL_trGL (A : GL (Fin n) ℂ) : trGL (trGL A) = A := Units.ext rfl

theorem isPolyRep_tr {Ψ : GL (Fin n) ℂ → Matrix κ κ ℂ} (hΨ : IsPolyRep Ψ) : IsPolyRep fun B => (Ψ (trGL B))ᵀ := by
  refine ⟨by rw [trGL_one, hΨ.one, Matrix.transpose_one], fun A B => by rw [trGL_mul, hΨ.mul, Matrix.transpose_mul],
    fun i j => ?_⟩
  obtain ⟨Q, hQ⟩ := hΨ.poly j i
  refine ⟨MvPolynomial.rename (Sum.map Prod.swap Prod.swap) Q, fun B => ?_⟩
  rw [Matrix.transpose_apply, hQ, MvPolynomial.eval_rename]
  congr 2
  funext p
  rcases p with p | p <;> rfl

theorem exists_covec [Nonempty κ] {Φ : (ι → GL (Fin n) ℂ) → Matrix κ κ ℂ} (hone : Φ 1 = 1)
    (hmul : ∀ g h, Φ (g * h) = Φ g * Φ h) (hpoly : ∀ τ, IsPolyRep fun B => Φ (Pi.mulSingle τ B)) :
    ∃ u : κ → ℂ, u ≠ 0 ∧ ∀ l : ι → GL (Fin n) ℂ, (∀ τ, PI.UnitaryGroupMassFormula.HwConjInf.LowUni (l τ).val) → u ᵥ* Φ l = u := by
  let Φt : (ι → GL (Fin n) ℂ) → Matrix κ κ ℂ := fun g => (Φ fun τ => trGL (g τ))ᵀ
  have h1 : Φt 1 = 1 := by
    have : (fun τ => trGL ((1 : ι → GL (Fin n) ℂ) τ)) = 1 := funext fun τ => trGL_one
    simp only [Φt, this, hone, Matrix.transpose_one]
  have h2 : ∀ g h, Φt (g * h) = Φt g * Φt h := by
    intro g h
    have : (fun τ => trGL ((g * h) τ)) = (fun τ => trGL (h τ)) * fun τ => trGL (g τ) := funext fun τ => trGL_mul _ _
    simp only [Φt, this, hmul, Matrix.transpose_mul]
  have h3 : ∀ τ, IsPolyRep fun B => Φt (Pi.mulSingle τ B) := by
    intro τ
    have : (fun B => Φt (Pi.mulSingle τ B)) = fun B => (Φ (Pi.mulSingle τ (trGL B)))ᵀ := by
      funext B
      simp only [Φt]
      congr 2
      funext σ
      by_cases h : σ = τ
      · subst h; simp
      · simp [h, trGL_one]
    rw [this]
    exact isPolyRep_tr (hpoly τ)
  obtain ⟨u, lam, hu0, hu⟩ := exists_joint_beig h2 h3
  refine ⟨u, hu0, fun l hl => ?_⟩
  have h := joint_upper h1 h2 hu (fun τ => trGL (l τ)) (fun τ i j hij => (hl τ).1 j i hij)
  have hd : ∀ τ i, (trGL (l τ)).val i i = 1 := fun τ i => (hl τ).2 i
  simp only [Φt, trGL_trGL, hd, _root_.one_zpow, Finset.prod_const_one, one_smul, Matrix.mulVec_transpose] at h
  exact h

end Eig

section Uniq
variable {n : ℕ} {ι : Type} [Fintype ι]

theorem eq_zero_of_LU {f : (ι → GL (Fin n) ℂ) → ℂ} (hf : Continuous f)
    (h : ∀ l b : ι → GL (Fin n) ℂ, (∀ τ, PI.UnitaryGroupMassFormula.HwConjInf.LowUni (l τ).val) → (∀ τ, (b τ).val.BlockTriangular id) →
      f (l * b) = 0) (g : ι → GL (Fin n) ℂ) : f g = 0 := by
  classical
  let M : ℂ → ι → Matrix (Fin n) (Fin n) ℂ := fun x τ => (g τ).val + x • (1 : Matrix (Fin n) (Fin n) ℂ)
  let c : ℂ → ι → GL (Fin n) ℂ := fun x τ =>
    if hx : (M x τ).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero _ hx else 1
  have hev : ∀ᶠ x in 𝓝[≠] (0 : ℂ), ∀ τ, (M x τ).det ≠ 0 ∧ ∃ L U : Matrix (Fin n) (Fin n) ℂ,
      PI.UnitaryGroupMassFormula.HwConjInf.LowUni L ∧ PI.UnitaryGroupMassFormula.HwConjInf.UpTri U ∧ M x τ = L * U :=
    Filter.eventually_all.2 fun τ => PI.UnitaryGroupMassFormula.HwConjInf.dense_LU (g τ).val
  have hval : ∀ x τ, (M x τ).det ≠ 0 → (c x τ).val = M x τ := by
    intro x τ hx
    simp only [c, dif_pos hx]
    rfl
  have hc : Tendsto c (𝓝[≠] 0) (𝓝 g) := by
    refine tendsto_pi_nhds.2 fun τ => ?_
    have t1 : Tendsto (fun x => M x τ) (𝓝[≠] 0) (𝓝 (g τ).val) := PI.UnitaryGroupMassFormula.HwConjInf.tendsto_add_smul _
    have hdet : IsUnit ((g τ).val).det := (Matrix.isUnit_iff_isUnit_det _).1 (g τ).isUnit
    have t2 : Tendsto (fun x => (M x τ)⁻¹) (𝓝[≠] 0) (𝓝 ((g τ).val)⁻¹) :=
      (continuousAt_matrix_inv _ (NormedRing.inverse_continuousAt hdet.unit)).tendsto.comp t1
    rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
    refine Filter.Tendsto.prodMk_nhds (t1.congr' ?_) ((MulOpposite.continuous_op.tendsto _).comp ?_)
    · filter_upwards [hev] with x hx
      exact (hval x τ (hx τ).1).symm
    · rw [Matrix.coe_units_inv]
      refine t2.congr' ?_
      filter_upwards [hev] with x hx
      rw [Matrix.coe_units_inv, hval x τ (hx τ).1]
  have h0 : ∀ᶠ x in 𝓝[≠] (0 : ℂ), (0 : ℂ) = f (c x) := by
    filter_upwards [hev] with x hx
    choose hd L U hL hU hLU using hx
    have hLd : ∀ τ, (L τ).det ≠ 0 := fun τ => by rw [PI.UnitaryGroupMassFormula.HwConjInf.det_lowUni (hL τ)]; exact one_ne_zero
    have hUd : ∀ τ, (U τ).det ≠ 0 := fun τ h0 => hd τ (by rw [hLU τ, Matrix.det_mul, h0, mul_zero])
    have : c x = (fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hLd τ)) *
        fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hUd τ) := by
      funext τ
      apply Units.ext
      rw [hval x τ (hd τ), hLU τ]
      rfl
    rw [this]
    exact (h _ _ hL (fun τ i j hij => hU τ i j hij)).symm
  exact tendsto_nhds_unique ((hf.tendsto g).comp hc) (tendsto_const_nhds.congr' h0)

variable {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

def coef {G : Type} (Φ : G → Matrix κ κ ℂ) (u : κ → ℂ) : (κ → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun x g := u ⬝ᵥ (Φ g *ᵥ x)
  map_add' x y := by funext g; simp [Matrix.mulVec_add, dotProduct_add]
  map_smul' c x := by funext g; simp [Matrix.mulVec_smul, dotProduct_smul]

theorem coef_injective {G : Type} {Φ : G → Matrix κ κ ℂ} {u : κ → ℂ} (hu : u ≠ 0)
    (hspan : ∀ x, x ≠ 0 → ∀ w, w ∈ Submodule.span ℂ (Set.range fun g => Φ g *ᵥ x)) : Function.Injective (coef Φ u) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  apply hu
  have h : ∀ w, u ⬝ᵥ w = 0 := by
    intro w
    refine Submodule.span_induction (p := fun w _ => u ⬝ᵥ w = 0) ?_ (dotProduct_zero u) ?_ ?_ (hspan x hx0 w)
    · rintro _ ⟨g, rfl⟩
      exact congrFun hx g
    · intro a b _ _ ha hb
      rw [dotProduct_add, ha, hb, add_zero]
    · intro c a _ ha
      rw [dotProduct_smul, ha, smul_zero]
  funext i
  simpa using h (Pi.single i 1)

theorem coef_act {G : Type} [Mul G] {Φ : G → Matrix κ κ ℂ} (hmul : ∀ g h, Φ (g * h) = Φ g * Φ h) (u x : κ → ℂ) (g h : G) :
    coef Φ u (Φ h *ᵥ x) g = coef Φ u x (g * h) := by
  show u ⬝ᵥ (Φ g *ᵥ (Φ h *ᵥ x)) = u ⬝ᵥ (Φ (g * h) *ᵥ x)
  rw [hmul, Matrix.mulVec_mulVec]

theorem range_coef_le {G : Type} [Mul G] {Φ : G → Matrix κ κ ℂ} {Φ' : G → Matrix κ' κ' ℂ}
    (hmul : ∀ g h, Φ (g * h) = Φ g * Φ h) (hmul' : ∀ g h, Φ' (g * h) = Φ' g * Φ' h) {u v : κ → ℂ} {u' v' : κ' → ℂ}
    (hspan : ∀ w, w ∈ Submodule.span ℂ (Set.range fun g => Φ g *ᵥ v)) {c c' : ℂ} (hc' : c' ≠ 0)
    (h : ∀ g, c' * coef Φ u v g = c * coef Φ' u' v' g) :
    LinearMap.range (coef Φ u) ≤ LinearMap.range (coef Φ' u') := by
  rintro _ ⟨w, rfl⟩
  have : Submodule.span ℂ (Set.range fun g => Φ g *ᵥ v) ≤ (LinearMap.range (coef Φ' u')).comap (coef Φ u) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨(c'⁻¹ * c) • (Φ' k *ᵥ v'), ?_⟩
    funext g
    rw [map_smul, Pi.smul_apply, coef_act hmul', coef_act hmul, smul_eq_mul, mul_assoc, ← h, inv_mul_cancel_left₀ hc']
  exact this (hspan w)

theorem exists_equiv {Φ : (ι → GL (Fin n) ℂ) → Matrix κ κ ℂ} {Φ' : (ι → GL (Fin n) ℂ) → Matrix κ' κ' ℂ}
    (hmul : ∀ g h, Φ (g * h) = Φ g * Φ h) (hmul' : ∀ g h, Φ' (g * h) = Φ' g * Φ' h)
    (hc : Continuous Φ) (hc' : Continuous Φ')
    (hspan : ∀ x, x ≠ 0 → ∀ w, w ∈ Submodule.span ℂ (Set.range fun g => Φ g *ᵥ x))
    (hspan' : ∀ x, x ≠ 0 → ∀ w, w ∈ Submodule.span ℂ (Set.range fun g => Φ' g *ᵥ x))
    {u v : κ → ℂ} {u' v' : κ' → ℂ} (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu0' : u' ≠ 0) (hv0' : v' ≠ 0)
    (hu : ∀ l : ι → GL (Fin n) ℂ, (∀ τ, PI.UnitaryGroupMassFormula.HwConjInf.LowUni (l τ).val) → u ᵥ* Φ l = u)
    (hu' : ∀ l : ι → GL (Fin n) ℂ, (∀ τ, PI.UnitaryGroupMassFormula.HwConjInf.LowUni (l τ).val) → u' ᵥ* Φ' l = u')
    (χ : (ι → GL (Fin n) ℂ) → ℂ)
    (hv : ∀ b : ι → GL (Fin n) ℂ, (∀ τ, (b τ).val.BlockTriangular id) → Φ b *ᵥ v = χ b • v)
    (hv' : ∀ b : ι → GL (Fin n) ℂ, (∀ τ, (b τ).val.BlockTriangular id) → Φ' b *ᵥ v' = χ b • v') :
    ∃ e : (κ → ℂ) ≃ₗ[ℂ] (κ' → ℂ), ∀ g x, e (Φ g *ᵥ x) = Φ' g *ᵥ e x := by
  have hi := coef_injective hu0 hspan
  have hi' := coef_injective hu0' hspan'
  have hf : Continuous (coef Φ u v) := continuous_const.dotProduct (hc.matrix_mulVec continuous_const)
  have hf' : Continuous (coef Φ' u' v') := continuous_const.dotProduct (hc'.matrix_mulVec continuous_const)
  have hLU : ∀ l b : ι → GL (Fin n) ℂ, (∀ τ, PI.UnitaryGroupMassFormula.HwConjInf.LowUni (l τ).val) →
      (∀ τ, (b τ).val.BlockTriangular id) → coef Φ u v (l * b) = χ b * (u ⬝ᵥ v) := by
    intro l b hl hb
    show u ⬝ᵥ (Φ (l * b) *ᵥ v) = _
    rw [hmul, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hu l hl, hv b hb, dotProduct_smul, smul_eq_mul]
  have hLU' : ∀ l b : ι → GL (Fin n) ℂ, (∀ τ, PI.UnitaryGroupMassFormula.HwConjInf.LowUni (l τ).val) →
      (∀ τ, (b τ).val.BlockTriangular id) → coef Φ' u' v' (l * b) = χ b * (u' ⬝ᵥ v') := by
    intro l b hl hb
    show u' ⬝ᵥ (Φ' (l * b) *ᵥ v') = _
    rw [hmul', ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hu' l hl, hv' b hb, dotProduct_smul, smul_eq_mul]
  have hcc : u ⬝ᵥ v ≠ 0 := fun h0 => hv0 (hi (by
    rw [map_zero]
    exact funext (eq_zero_of_LU hf fun l b hl hb => by rw [hLU l b hl hb, h0, mul_zero])))
  have hcc' : u' ⬝ᵥ v' ≠ 0 := fun h0 => hv0' (hi' (by
    rw [map_zero]
    exact funext (eq_zero_of_LU hf' fun l b hl hb => by rw [hLU' l b hl hb, h0, mul_zero])))
  have key : ∀ g, (u' ⬝ᵥ v') * coef Φ u v g = (u ⬝ᵥ v) * coef Φ' u' v' g := fun g =>
    sub_eq_zero.1 (eq_zero_of_LU (f := fun g => (u' ⬝ᵥ v') * coef Φ u v g - (u ⬝ᵥ v) * coef Φ' u' v' g)
      ((continuous_const.mul hf).sub (continuous_const.mul hf'))
      (fun l b hl hb => by rw [hLU l b hl hb, hLU' l b hl hb]; ring) g)
  have hr : LinearMap.range (coef Φ u) = LinearMap.range (coef Φ' u') :=
    le_antisymm (range_coef_le hmul hmul' (hspan v hv0) hcc' key)
      (range_coef_le hmul' hmul (hspan' v' hv0') hcc fun g => (key g).symm)
  let e : (κ → ℂ) ≃ₗ[ℂ] (κ' → ℂ) :=
    ((LinearEquiv.ofInjective _ hi).trans (LinearEquiv.ofEq _ _ hr)).trans (LinearEquiv.ofInjective _ hi').symm
  have he : ∀ x, coef Φ' u' (e x) = coef Φ u x := fun x => by
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.ofInjective_symm_apply]
    rfl
  refine ⟨e, fun g x => hi' ?_⟩
  funext k
  rw [he, coef_act hmul, coef_act hmul', he]

end Uniq

section Wt
open Formalism.L2.Col
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  (emb : ι → L →+* ℂ) (hinj : Function.Injective emb)
  (hcm : ∀ τ τ', emb τ ≠ ComplexEmbedding.conjugate (emb τ'))
  (hall : ∀ σ : L →+* ℂ, ∃ t, σ = emb t ∨ σ = ComplexEmbedding.conjugate (emb t))

def ptOf (g : ι → GL (Fin n) ℂ) : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ :=
  fun σ => Matrix.of fun i j => mtwPtOf emb g (σ, i, j)

include hinj hcm

theorem ptOf_emb (g : ι → GL (Fin n) ℂ) (τ : ι) : ptOf emb g (emb τ) = (g τ).val := by
  ext i j; exact mtwPtOf_emb emb hinj hcm g τ i j

theorem ptOf_conj (g : ι → GL (Fin n) ℂ) (τ : ι) :
    ptOf emb g (ComplexEmbedding.conjugate (emb τ)) = ((g τ)⁻¹).valᵀ := by
  ext i j; exact mtwPtOf_conj emb hinj hcm g τ i j

include hall

theorem isUPt_ptOf (g : ι → GL (Fin n) ℂ) : IsUPt (ptOf emb g) := by
  intro σ
  obtain ⟨t, rfl | rfl⟩ := hall σ
  · rw [ptOf_emb emb hinj hcm, ptOf_conj emb hinj hcm, Matrix.transpose_transpose, ← Units.val_mul, mul_inv_cancel,
      Units.val_one]
  · rw [conj_conj, ptOf_emb emb hinj hcm, ptOf_conj emb hinj hcm, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.transpose_one]

theorem ptOf_mul (g h : ι → GL (Fin n) ℂ) : ptOf emb (g * h) = fun σ => ptOf emb g σ * ptOf emb h σ := by
  funext σ
  obtain ⟨t, rfl | rfl⟩ := hall σ
  · simp only [ptOf_emb emb hinj hcm, Pi.mul_apply, Units.val_mul]
  · simp only [ptOf_conj emb hinj hcm, Pi.mul_apply, _root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem ptOf_one : ptOf emb (1 : ι → GL (Fin n) ℂ) = fun _ => 1 := by
  funext σ
  obtain ⟨t, rfl | rfl⟩ := hall σ
  · simp only [ptOf_emb emb hinj hcm, Pi.one_apply, Units.val_one]
  · simp only [ptOf_conj emb hinj hcm, Pi.one_apply, inv_one, Units.val_one, Matrix.transpose_one]

theorem ptOf_single (τ : ι) (B : GL (Fin n) ℂ) : upt (ptOf emb (Pi.mulSingle τ B)) = evPt (emb τ) B := by
  rw [evPt_eq_upt]
  congr 1
  funext σ
  obtain ⟨t, rfl | rfl⟩ := hall σ
  · rw [ptOf_emb emb hinj hcm]
    by_cases h : t = τ
    · subst h; simp [tauPt]
    · have h1 : emb t ≠ emb τ := fun e => h (hinj e)
      simp [tauPt, h, h1, hcm t τ]
  · rw [ptOf_conj emb hinj hcm]
    have h2 : ComplexEmbedding.conjugate (emb t) ≠ emb τ := fun e => hcm τ t e.symm
    by_cases h : t = τ
    · subst h; simp only [tauPt, if_neg h2, if_true, Pi.mulSingle_eq_same]
    · have h1 : ComplexEmbedding.conjugate (emb t) ≠ ComplexEmbedding.conjugate (emb τ) := fun e => h (hinj (by
        have := congrArg ComplexEmbedding.conjugate e
        rwa [conj_conj, conj_conj] at this))
      simp only [tauPt, if_neg h2, if_neg h1, Pi.mulSingle_eq_of_ne h, inv_one, Units.val_one, Matrix.transpose_one]

theorem ptOf_rat (γ₀ : GL (Fin n) L) (h : γ₀ ∈ GQ0 L n) : ptOf emb (mtwEmb emb γ₀) = ratPt γ₀.val := by
  funext σ
  obtain ⟨t, rfl | rfl⟩ := hall σ
  · rw [ptOf_emb emb hinj hcm]; rfl
  · rw [ptOf_conj emb hinj hcm]
    have h1 := isUPt_ratPt γ₀ h (emb t)
    have h2 : ratPt γ₀.val (emb t) = (mtwEmb emb γ₀ t).val := rfl
    rw [h2] at h1
    rw [Matrix.coe_units_inv, Matrix.inv_eq_right_inv h1, Matrix.transpose_transpose]

theorem continuous_ptOf {κ : Type} (P : κ → κ → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) :
    Continuous fun g : ι → GL (Fin n) ℂ => evM P (upt (ptOf emb g)) := by
  refine continuous_matrix fun i j => (MvPolynomial.continuous_eval (P i j)).comp (continuous_pi fun p => ?_)
  obtain ⟨σ, a, b⟩ := p
  obtain ⟨t, rfl | rfl⟩ := hall σ
  · simp only [upt, ptOf_emb emb hinj hcm]
    exact (Units.continuous_val.comp (continuous_apply t)).matrix_elem a b
  · simp only [upt, ptOf_conj emb hinj hcm, Matrix.transpose_apply]
    exact (Units.continuous_coe_inv.comp (continuous_apply t)).matrix_elem b a

theorem iso_of_hwAt (a a' : AlgWt L n) (lam : ι → Fin n → ℤ) (ha : ∀ τ, a.HWAt (emb τ) (lam τ))
    (ha' : ∀ τ, a'.HWAt (emb τ) (lam τ)) : a.Iso a' := by
  have data : ∀ (c : AlgWt L n), (∀ τ, c.HWAt (emb τ) (lam τ)) → ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ)
      (b : Module.Basis κ ℂ c.W) (Φ : (ι → GL (Fin n) ℂ) → Matrix κ κ ℂ) (u v : κ → ℂ),
      (∀ g h, Φ (g * h) = Φ g * Φ h) ∧ Continuous Φ ∧
      (∀ x, x ≠ 0 → ∀ w, w ∈ Submodule.span ℂ (Set.range fun g => Φ g *ᵥ x)) ∧ u ≠ 0 ∧ v ≠ 0 ∧
      (∀ l : ι → GL (Fin n) ℂ, (∀ τ, PI.UnitaryGroupMassFormula.HwConjInf.LowUni (l τ).val) → u ᵥ* Φ l = u) ∧
      (∀ g : ι → GL (Fin n) ℂ, (∀ τ, (g τ).val.BlockTriangular id) →
        Φ g *ᵥ v = (∏ τ, ∏ i, ((g τ).val i i) ^ (lam τ i)) • v) ∧
      ∀ γ, LinearMap.toMatrix b b (c.ρ γ) = Φ (mtwEmb emb (mtwRat γ)) := by
    intro c hc
    obtain ⟨_, κ, _, _, b, P, hP⟩ := c.alg
    have hP' : Agrees c b P := hP
    haveI : Nontrivial c.W := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      have := c.irr
      exact bot_ne_top (α := Subrepresentation c.ρ)
        (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
    haveI := b.index_nonempty
    obtain ⟨h1, h2⟩ := GlobalTheory.T.algebraicWeight_polyMatrix_multiplicative L n c κ b P hP'
    have hone : evM P (upt (ptOf emb (1 : ι → GL (Fin n) ℂ))) = 1 := by rw [ptOf_one emb hinj hcm hall, h1]
    have hmul : ∀ g h : ι → GL (Fin n) ℂ, evM P (upt (ptOf emb (g * h))) =
        evM P (upt (ptOf emb g)) * evM P (upt (ptOf emb h)) := fun g h => by
      rw [ptOf_mul emb hinj hcm hall, h2 _ _ (isUPt_ptOf emb hinj hcm hall g) (isUPt_ptOf emb hinj hcm hall h)]
    have hpoly : ∀ τ, IsPolyRep fun B => evM P (upt (ptOf emb (Pi.mulSingle τ B))) := fun τ => by
      simp only [ptOf_single emb hinj hcm hall]
      exact GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n c κ b P hP' (emb τ)
    obtain ⟨v, mu, hv0, hv⟩ := exists_joint_beig (Φ := fun g => evM P (upt (ptOf emb g))) hmul hpoly
    obtain ⟨u, hu0, hu⟩ := exists_covec (Φ := fun g => evM P (upt (ptOf emb g))) hone hmul hpoly
    have hmu : mu = lam := by
      funext τ
      refine algebraic_weight_highest_unique L n c (emb τ) _ _ ⟨κ, inferInstance, inferInstance, b, P, hP, v, hv0, fun B hB => ?_⟩ (hc τ)
      have := (hv τ).2 B hB
      simp only [ptOf_single emb hinj hcm hall] at this
      exact this
    subst hmu
    refine ⟨κ, inferInstance, inferInstance, b, fun g => evM P (upt (ptOf emb g)), u, v, hmul,
      continuous_ptOf emb hinj hcm hall P, fun x hx w => ?_, hu0, hv0, hu,
      joint_upper (Φ := fun g => evM P (upt (ptOf emb g))) hone hmul hv, fun γ => ?_⟩
    · refine Submodule.span_mono ?_ (span_ratPt_orbit L n c κ b P hP' x hx w)
      rintro _ ⟨γ₀, hγ, rfl⟩
      exact ⟨mtwEmb emb γ₀, by simp only [ptOf_rat emb hinj hcm hall γ₀ hγ]⟩
    · simp only [ptOf_rat emb hinj hcm hall _ (mtwRat_mem γ)]
      exact hP' γ (mtwRat γ) (congrArg Units.val (mtwInc_mtwRatFun γ)).symm
  obtain ⟨κ, _, _, b, Φ, u, v, m1, m2, m3, m4, m5, m6, m7, m8⟩ := data a ha
  obtain ⟨κ', _, _, b', Φ', u', v', n1, n2, n3, n4, n5, n6, n7, n8⟩ := data a' ha'
  obtain ⟨e, he⟩ := exists_equiv m1 n1 m2 n2 m3 n3 m4 m5 n4 n5 m6 n6 _ m7 n7
  refine ⟨(b.equivFun.trans e).trans b'.equivFun.symm, fun γ x => b'.equivFun.injective ?_⟩
  have k1 : b.equivFun (a.ρ γ x) = Φ (mtwEmb emb (mtwRat γ)) *ᵥ b.equivFun x := by
    rw [← m8]; exact (LinearMap.toMatrix_mulVec_repr b b _ x).symm
  have k2 : ∀ y, b'.equivFun (a'.ρ γ y) = Φ' (mtwEmb emb (mtwRat γ)) *ᵥ b'.equivFun y := fun y => by
    rw [← n8]; exact (LinearMap.toMatrix_mulVec_repr b' b' _ y).symm
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, k1, k2, he]

end Wt

open Formalism.BasicNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Col in

theorem exists_equiv_VV : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι]
    (emb : ι → L →+* ℂ), Function.Injective emb → (∀ t t', emb t ≠ ComplexEmbedding.conjugate (emb t')) →
    (∀ σ : L →+* ℂ, ∃ t, σ = emb t ∨ σ = ComplexEmbedding.conjugate (emb t)) → ∀ a : NG.AlgWt L n,
    ∃ (lam : ι → DomWeight n) (T : a.W ≃ₗ[ℂ] VV ℂ lam), ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L),
      (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom →
      ∀ x, T (a.ρ γ x) = rhoVr emb lam γ₀ (T x) := by
  intro L _ _ _ n ι _ emb hinj hcm hall a
  classical
  have hinj' := mtwConj_injective emb hinj
  have hcm' := mtwConj_cm emb hcm
  have hall' : ∀ σ : L →+* ℂ, ∃ t, σ = mtwConj emb t ∨ σ = ComplexEmbedding.conjugate (mtwConj emb t) := fun σ => by
    obtain ⟨t, h | h⟩ := hall σ
    · exact ⟨t, Or.inr (by rw [h, mtwConj, conj_conj])⟩
    · exact ⟨t, Or.inl h⟩
  choose mu hmu using fun τ => (GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone L n a (mtwConj emb τ)).1.exists
  let lam : ι → DomWeight n := fun τ => ⟨mu τ, (GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone L n a (mtwConj emb τ)).2 _ (hmu τ)⟩
  have hirr : TenIrr (mtwConj (mtwConj emb)) lam :=
    tenIrr_of' highest_weight_fixed_exists highest_weight_fixed_line _ (mtwConj_injective _ hinj') (mtwConj_cm _ hcm') lam
  obtain ⟨T, hT⟩ := iso_of_hwAt (mtwConj emb) hinj' hcm' hall' a (tenWt (mtwConj emb) lam hirr) mu hmu
    (fun τ => tenWt_hwAt (mtwConj emb) hinj' hcm' lam hirr τ)
  refine ⟨lam, T, fun γ γ₀ hγ x => ?_⟩
  obtain rfl := mtwRat_eq_of_match γ γ₀ hγ
  refine (hT γ x).trans ?_
  show tenRep (mtwConj emb) lam γ (T x) = _
  rw [← mtRep_eq_tenRep]
  rfl

end GlobalTheory.WtClass
