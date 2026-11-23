import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocalStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertSph

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hTens_eq {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α]
    [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  simp only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem symp_mul_transpose {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (c : A →ₐ[R] A) {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (ξ : A) (JA : Matrix α α A)
    (JB : Matrix β β A) (g : Matrix β β A) (hg : gᵀ * JB * g.map c = JB) (x : Matrix α β A) :
    symp c ξ JA JB (x * gᵀ) (x * gᵀ) = symp c ξ JA JB x x := by
  have e : (x * gᵀ) * JB * ((x * gᵀ).map c)ᵀ = x * JB * (x.map c)ᵀ := by
    have hm : (x * gᵀ).map c = x.map c * (gᵀ).map c := Matrix.map_mul (f := c.toRingHom)
    rw [hm, Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose]
    calc x * gᵀ * JB * (g.map c * (x.map c)ᵀ) = x * (gᵀ * JB * g.map c) * (x.map c)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg]
  unfold symp
  rw [hTens_eq, hTens_eq, e]

variable {σ : E →ₐ[F] E}

theorem vecMulVec_mem_latAtV {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F) {x : Fin n → E} (hx : x ∈ X.L)
    {w : Fin d → AE F E} (hw : w ∈ latAt W v) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) w ∈ latAtV X W v := by
  let f : (Fin d → AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun w => Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) w
      map_zero' := by ext i j; simp [Matrix.vecMulVec_apply]
      map_add' := fun w w' => by ext i j; simp [Matrix.vecMulVec_apply, mul_add] }
  have : latAt W v ≤ (latAtV X W v).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, y, hy, rfl⟩
    refine AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, y, hy, ?_⟩
    ext i j
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, incM,
      Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]
    ring
  exact this hw

theorem mul_transpose_inv_mem_latAtV {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F) {h : UA σ W.J}
    (hh : h ∈ KAt σ W v) {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    γ * (mat h⁻¹)ᵀ ∈ latAtV X W v := by
  let f : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun γ => γ * (mat h⁻¹)ᵀ
      map_zero' := by simp
      map_add' := fun γ γ' => by simp [Matrix.add_mul] }
  have : latAtV X W v ≤ (latAtV X W v).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    show (a • incM F (Matrix.vecMulVec x y)) * (mat h⁻¹)ᵀ ∈ latAtV X W v
    have hz : (a • fun i => inclR (F := F) (AF F) (y i)) ∈ latAt W v :=
      AddSubgroup.subset_closure ⟨a, ha, hai, y, hy, rfl⟩
    have e : (a • incM F (Matrix.vecMulVec x y)) * (mat h⁻¹)ᵀ =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i))
          (mat h⁻¹ *ᵥ (a • fun i => inclR (F := F) (AF F) (y i))) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Matrix.transpose_apply, Matrix.mulVec,
        dotProduct, Pi.smul_apply, incM, Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]
    exact vecMulVec_mem_latAtV X W v hx (hh.2 _ hz).2
  exact this hγ

end GlobalTheory.InertSph

namespace GlobalTheory.InertSph

theorem acts_vacCond_of_mem_KAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, k)) φ φ₁ →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ)) →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ₁
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v θ hθ k hk φ hφ φ₁ hφ₁ hAct hvac γ hγ r hr
  have hS := IsUWeilPair.isUSplitting hTr.weil'
  have etens : ∀ (c : ℂ) (f : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • f) r = c • tens (evFin F v) f r := fun c f => by
    funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring
  by_cases h0 : φ₁ = 0
  · subst h0
    have e0 : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
      funext x; simp [tens]
    rw [smul_zero, e0]
    funext x
    simp [Darboux.rho, schr]
  have hrφ : Rest (evFin F v) φ r := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v φ₁ φ r h0 hφ hr
  set γ' := actAB (cA σ) ((1 : UA σ G.V'.J), k⁻¹) γ
  have eγ' : γ' = γ * (mat k⁻¹)ᵀ := by
    simp [γ', actAB, mat]
  have hγ' : γ' ∈ latAtV G.V' G.W v := by
    rw [eγ']; exact mul_transpose_inv_mem_latAtV G.V' G.W v hk hγ
  have hsym : symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ' γ' =
      symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ := by
    rw [eγ']
    exact symp_mul_transpose (cA σ) _ _ _ (mat k⁻¹) (k⁻¹).2 γ
  have e1 : actAB (cA σ) ((1 : UA σ G.V'.J), k) γ' = γ := by
    simp only [γ', actAB]
    simp [Matrix.mul_assoc, ← Matrix.transpose_mul]
  have hi := hS.impl ((1 : UA σ G.V'.J), k) γ' _ hrφ.2
  rw [e1] at hi
  rw [← hAct r hrφ, ← hi, hvac γ' hγ' r hrφ, hsym, etens, map_smul, hAct r hrφ, etens]

end GlobalTheory.InertSph
