import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictPlan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.RationalPointsLeHolds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual

noncomputable section
namespace PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix

theorem dictTop_sig (I : AutInst) : ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) = starRingEnd I.E :=
  RingHom.ext fun _ => rfl

theorem dictTop_mul_inv (I : AutInst) (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  simp [Formalism.MainNotions.S.AutInst.fmat]

theorem dictTop_inv_mul (I : AutInst) (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  simp [Formalism.MainNotions.S.AutInst.fmat]

theorem dictTop_fmat_mul (I : AutInst) (x y : I.Gf) : I.fmat (x * y) = I.fmat x * I.fmat y := rfl

private theorem hform_eq_dotProduct_mulVec {A : Type} [CommRing A] {k : ℕ} (σ : A →+* A)
    (J : Matrix (Fin k) (Fin k) A) (x y : Fin k → A) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

private theorem hform_mulVec_mulVec_eq_hform_cT_mul_mul {A : Type} [CommRing A] {k : ℕ} (σ : A →+* A)
    (J M : Matrix (Fin k) (Fin k) A) (a b : Fin k → A) :
    Formalism.UG.hform σ J (M *ᵥ a) (M *ᵥ b) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) a b := by
  rw [hform_eq_dotProduct_mulVec, hform_eq_dotProduct_mulVec]
  show _ = (fun i => σ (a i)) ⬝ᵥ (((M.map σ)ᵀ * J * M) *ᵥ b)
  have e : (fun i => σ ((M *ᵥ a) i)) = M.map σ *ᵥ (fun i => σ (a i)) := by
    funext i
    exact RingHom.map_mulVec σ M a i
  rw [e, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose (M.map σ) (fun i => σ (a i)),
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem dictTop_hhat_unit (I : AutInst) (x : I.Gf) (a b : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hhat I (I.fmat x *ᵥ a) (I.fmat x *ᵥ b) = hhat I a b := by
  have hx : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.fmat x) *
      I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * I.fmat x =
      I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := x.2
  unfold hhat
  rw [hform_mulVec_mulVec_eq_hform_cT_mul_mul, hx]

private theorem sigR_inclE' (I : AutInst) (e : I.E) :
    Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E e) :=
  Algebra.TensorProduct.map_tmul I.cm.sig (AlgHom.id I.F (Af I.F)) e 1

private theorem inclE_hform (I : AutInst) (w v : Fin I.n → I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J w v) =
      hhat I (iv I w) (iv I v) := by
  unfold hhat iv
  simp only [Formalism.UG.hform, map_sum, map_mul, Matrix.map_apply, sigR_inclE']

private theorem sigR_mem_intAf (I : AutInst) (c : I.E ⊗[I.F] Af I.F) (hc : c ∈ IntAf I.F I.E) :
    Formalism.UG.sigR I.cm.sig (Af I.F) c ∈ IntAf I.F I.E := by
  have hle : IntAf I.F I.E ≤ (IntAf I.F I.E).comap (Formalism.UG.sigR I.cm.sig (Af I.F)) := by
    refine (Subring.closure_le).2 ?_
    rintro _ (⟨⟨e, he⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
    · obtain ⟨o, rfl⟩ := he
      show Formalism.UG.sigR I.cm.sig (Af I.F)
        (Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E o)) ∈ IntAf I.F I.E
      rw [sigR_inclE']
      have hs : starRingEnd I.E (algebraMap (𝓞 I.E) I.E o) ∈ Formalism.UG.intOE I.E :=
        ⟨⟨star (o : I.E),
          (NumberField.RingOfIntegers.isIntegral_coe o).map (starRingEnd I.E).toIntAlgHom⟩, rfl⟩
      exact Subring.subset_closure (Or.inl ⟨⟨_, hs⟩, rfl⟩)
    · show Formalism.UG.sigR I.cm.sig (Af I.F) ((1 : I.E) ⊗ₜ[I.F] a) ∈ IntAf I.F I.E
      have h1 := Algebra.TensorProduct.map_tmul I.cm.sig (AlgHom.id I.F (Af I.F)) (1 : I.E) a
      rw [map_one] at h1
      have e1 : Formalism.UG.sigR I.cm.sig (Af I.F) ((1 : I.E) ⊗ₜ[I.F] a) = (1 : I.E) ⊗ₜ[I.F] a := h1
      rw [e1]
      exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  exact hle hc

private theorem hhat_zero_left' (I : AutInst) (z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hhat I 0 z = 0 := by
  simp [hhat, Formalism.UG.hform]

private theorem hhat_add_left' (I : AutInst) (a b z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hhat I (a + b) z = hhat I a z + hhat I b z := by
  simp only [hhat, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

private theorem hhat_smul_left' (I : AutInst) (r : I.E ⊗[I.F] Af I.F)
    (a z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hhat I (r • a) z = Formalism.UG.sigR I.cm.sig (Af I.F) r * hhat I a z := by
  simp only [hhat, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem mDual_of (hDI : DInter) (hLI : LHatInt) (hLD : LHatDual) (hG : MGen) : MDual := by
  intro I x v
  constructor
  · intro hv w hw
    apply hDI I.F I.E
    rw [inclE_hform, ← dictTop_hhat_unit I x⁻¹]
    exact hLI I (I.fmat x⁻¹ *ᵥ iv I w) hw (I.fmat x⁻¹ *ᵥ iv I v) hv
  · intro hv
    show I.fmat x⁻¹ *ᵥ iv I v ∈ I.Lf
    apply hLD I
    intro y hy
    rw [← dictTop_hhat_unit I x y, Matrix.mulVec_mulVec, dictTop_mul_inv, Matrix.one_mulVec]
    refine Submodule.span_induction (p := fun z _ => hhat I z (iv I v) ∈ IntAf I.F I.E)
      (fun z hz => ?_) ?_ (fun z w _ _ hz hw => ?_) (fun c z _ hz => ?_) (hG I x y hy)
    · obtain ⟨w, rfl⟩ := hz
      obtain ⟨o, ho⟩ := hv w w.2
      rw [← inclE_hform, ← ho]
      exact Subring.subset_closure (Or.inl ⟨⟨(o : I.E), o, rfl⟩, rfl⟩)
    · rw [hhat_zero_left']
      exact (IntAf I.F I.E).zero_mem
    · rw [hhat_add_left']
      exact (IntAf I.F I.E).add_mem hz hw
    · show hhat I ((c : I.E ⊗[I.F] Af I.F) • z) (iv I v) ∈ IntAf I.F I.E
      rw [hhat_smul_left']
      exact (IntAf I.F I.E).mul_mem (sigR_mem_intAf I _ c.2) hz

theorem dictTop_into (hG : MGen) (I : AutInst) (a b : I.Gf) (h : abelian₂ I a = abelian₂ I b)
    (z : Fin I.n → I.E ⊗[I.F] Af I.F) (hz : z ∈ I.Lf) : I.fmat a⁻¹ *ᵥ (I.fmat b *ᵥ z) ∈ I.Lf := by
  refine Submodule.span_induction (p := fun y _ => I.fmat a⁻¹ *ᵥ y ∈ I.Lf)
    (fun y hy => ?_) ?_ (fun y w _ _ hy hw => ?_) (fun c y _ hy => ?_) (hG I b z hz)
  · obtain ⟨v, rfl⟩ := hy
    have hv : (v : Fin I.n → I.E) ∈ abelian₂ I a := by
      rw [h]
      exact v.2
    exact hv
  · rw [Matrix.mulVec_zero]
    exact I.Lf.zero_mem
  · rw [Matrix.mulVec_add]
    exact I.Lf.add_mem hy hw
  · show I.fmat a⁻¹ *ᵥ ((c : I.E ⊗[I.F] Af I.F) • y) ∈ I.Lf
    rw [Matrix.mulVec_smul]
    exact I.Lf.smul_mem c hy

theorem mInj_of (hG : MGen) : MInj := by
  intro I x y h
  refine ⟨x⁻¹ * y, fun z => ?_, (mul_inv_cancel_left x y).symm⟩
  show z ∈ I.Lf ↔ I.fmat (x⁻¹ * y) *ᵥ z ∈ I.Lf
  rw [dictTop_fmat_mul, ← Matrix.mulVec_mulVec]
  constructor
  · intro hz
    exact dictTop_into hG I x y h z hz
  · intro hz
    have h2 := dictTop_into hG I y x h.symm _ hz
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc] at h2
    rwa [← Matrix.mul_assoc (I.fmat x), dictTop_mul_inv, Matrix.one_mul, dictTop_inv_mul,
      Matrix.one_mulVec] at h2

theorem dictTop_map_mulVec (I : AutInst) (M : Matrix (Fin I.n) (Fin I.n) I.E) (w : Fin I.n → I.E) :
    M.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *ᵥ iv I w = iv I (M *ᵥ w) := by
  funext i
  exact (RingHom.map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F)) M w i).symm

theorem lattice_m_equiv : MEquiv := by
  intro I γ hγ
  have hmem : Units.map (RingHom.mapMatrix (Formalism.UG.inclE (F := I.F) (Af I.F))).toMonoidHom γ ∈
      Formalism.UG.UPts I.cm.sig I.J (Af I.F) := by
    show Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F))
        ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))) *
        I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) =
        I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))
    have hg : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J *
        (γ : Matrix (Fin I.n) (Fin I.n) I.E) = I.J := hγ
    have hc : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F))
        ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))) =
        (Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E)).map
          (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
      ext i j
      simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
      exact sigR_inclE' I _
    rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg]
  let c : I.Gf := ⟨_, hmem⟩
  have hfc : I.fmat c =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := rfl
  refine ⟨c, ⟨γ, hγ, rfl⟩, rfl, fun x v => ?_⟩
  have K : ∀ z, I.fmat (c * x)⁻¹ *ᵥ (I.fmat c *ᵥ z) = I.fmat x⁻¹ *ᵥ z := by
    intro z
    rw [Matrix.mulVec_mulVec, ← dictTop_fmat_mul, mul_inv_rev, inv_mul_cancel_right]
  constructor
  · intro hv
    refine ⟨((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ v, ?_, ?_⟩
    · show I.fmat x⁻¹ *ᵥ iv I (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ v) ∈ I.Lf
      rw [← K, hfc, dictTop_map_mulVec, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact hv
    · rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  · rintro ⟨w, hw, rfl⟩
    show I.fmat (c * x)⁻¹ *ᵥ iv I ((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ w) ∈ I.Lf
    rw [← dictTop_map_mulVec, ← hfc, K]
    exact hw

end PIW.AdelClassFin
