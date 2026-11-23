import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
open scoped TensorProduct

namespace GlobalTheory.T.ScalarParabolicLeviProjection

private theorem aeval_intertwine {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (Φ : V →ₗ[ℂ] W) (B : Module.End ℂ V) (A : Module.End ℂ W) (h : ∀ v, Φ (B v) = A (Φ v))
    (q : Polynomial ℂ) (v : V) : Φ (Polynomial.aeval B q v) = Polynomial.aeval A q (Φ v) := by
  induction q using Polynomial.induction_on generalizing v with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul (Polynomial.aeval B), map_mul (Polynomial.aeval A),
      Polynomial.aeval_X, Polynomial.aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih, h]

private theorem aeval_smInd {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (P : Subgroup G) (σ : Representation ℂ P W) (z : G) (hz : z ∈ P)
    (hc : ∀ x, x * z = z * x) (q : Polynomial ℂ) (hq : Polynomial.aeval (σ ⟨z, hz⟩) q = 0) :
    Polynomial.aeval (smInd P σ z) q = 0 := by
  refine LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => ?_))
  let ev : smoothPart (ind P σ) →ₗ[ℂ] W :=
    (LinearMap.proj x) ∘ₗ (indSpace P σ).subtype ∘ₗ (smoothPart (ind P σ)).subtype
  have := aeval_intertwine ev (smInd P σ z) (σ ⟨z, hz⟩) (fun F => by
    show F.1.1 (x * z) = σ ⟨z, hz⟩ (F.1.1 x)
    rw [hc]
    exact F.1.2 ⟨z, hz⟩ x) q F
  rw [hq] at this
  exact this

section
variable {k : Type} [Field k] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

private theorem val_scalar (t : kˣ) (i j : n) :
    ((GeneralLinearGroup.scalar n t : GL n k) : Matrix n n k) i j = if i = j then (t : k) else 0 := by
  simp [GeneralLinearGroup.scalar, Matrix.diagonal_apply]

private theorem scalar_mem_parab (e : (Σ a, m a) ≃ n) (t : kˣ) :
    GeneralLinearGroup.scalar n t ∈ parab k e := by
  refine mem_parab.2 fun i j h => ?_
  rw [val_scalar, if_neg]
  rintro rfl
  exact lt_irrefl _ h

private theorem leviProj_scalar (e : (Σ a, m a) ≃ n) (t : kˣ) (h) (a : α) :
    leviProj k e ⟨GeneralLinearGroup.scalar n t, h⟩ a = GeneralLinearGroup.scalar (m a) t := by
  ext i j
  rw [leviProj_apply, val_scalar, val_scalar]
  simp

private theorem det_scalar (t : kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar n t) = t ^ Fintype.card n := by
  ext; simp [GeneralLinearGroup.scalar]

private theorem scalar_comm (t : kˣ) (x : GL n k) :
    x * GeneralLinearGroup.scalar n t = GeneralLinearGroup.scalar n t * x := by
  ext i j
  simp [GeneralLinearGroup.scalar, mul_comm]
end

section
variable {k : Type} [Field k] {m : Type} [Fintype m] [DecidableEq m] {d : Bool → Type}
  [∀ a, Fintype (d a)] [∀ a, DecidableEq (d a)]

private def spl (φ : (Σ j, d j) ≃ m) (e1 : Fin 1 ≃ d false) : Fin 1 ⊕ d true ≃ m :=
  Equiv.trans
    { toFun := fun y => match y with
        | Sum.inl i => ⟨false, e1 i⟩
        | Sum.inr j => ⟨true, j⟩
      invFun := fun x => match x with
        | ⟨false, i⟩ => Sum.inl (e1.symm i)
        | ⟨true, j⟩ => Sum.inr j
      left_inv := by rintro (_ | _) <;> simp
      right_inv := by rintro ⟨_ | _, _⟩ <;> simp } φ

private theorem mem_unipRad_spl (φ : (Σ j, d j) ≃ m) (e1 : Fin 1 ≃ d false) {u : GL m k}
    (hu : u ∈ unipRad k (two (spl φ e1))) : u ∈ unipRad k φ := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 hu
  refine mem_unipRad.2 ⟨mem_parab_iff.2 ?_, ?_⟩
  · rintro (_ | _) (_ | _) i j hlt
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · obtain ⟨j, rfl⟩ := e1.surjective j
      exact (mem_parab_two k).1 h1 i j
    · exact absurd hlt (by decide)
  · rintro (_ | _) i j
    · obtain ⟨i, rfl⟩ := e1.surjective i
      obtain ⟨j, rfl⟩ := e1.surjective j
      obtain rfl : i = j := Subsingleton.elim _ _
      exact (h2 false i i).trans (by simp)
    · exact h2 true i j

private theorem leviEmb_spl (φ : (Σ j, d j) ≃ m) (e1 : Fin 1 ≃ d false) (t : kˣ) (h : Levi k d)
    (h0 : h false = GeneralLinearGroup.scalar _ t) (h1 : h true = 1) :
    leviEmb k φ h = leviEmb k (two (spl φ e1))
      (leviTwo k (Fin 1) (d true) (GeneralLinearGroup.scalar (Fin 1) t, 1)) := by
  ext x y
  obtain ⟨⟨a, i⟩, rfl⟩ := φ.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := φ.surjective y
  rcases a with _ | _ <;> rcases b with _ | _
  · obtain ⟨i, rfl⟩ := e1.surjective i
    obtain ⟨j, rfl⟩ := e1.surjective j
    obtain rfl : i = j := Subsingleton.elim _ _
    rw [leviEmb_apply_same, h0, val_scalar, if_pos rfl]
    refine Eq.symm ((leviEmb_apply_same k (two (spl φ e1)) _ false i i).trans ?_)
    exact (val_scalar t i i).trans (if_pos rfl)
  · obtain ⟨i, rfl⟩ := e1.surjective i
    rw [leviEmb_apply_ne k φ h (by decide)]
    exact (leviEmb_apply_ne k (two (spl φ e1)) _ (a := false) (b := true) (by decide) i j).symm
  · obtain ⟨j, rfl⟩ := e1.surjective j
    rw [leviEmb_apply_ne k φ h (by decide)]
    exact (leviEmb_apply_ne k (two (spl φ e1)) _ (a := true) (b := false) (by decide) i j).symm
  · rw [leviEmb_apply_same, h1]
    exact (leviEmb_apply_same k (two (spl φ e1))
      (leviTwo k (Fin 1) (d true) (GeneralLinearGroup.scalar (Fin 1) t, 1)) true i j).symm
end

private theorem modExp_false (d : Bool → Type) [∀ a, Fintype (d a)] :
    modExp d false = Fintype.card (d true) := by
  simp [modExp, Finset.sum_filter]

private theorem modExp_true (d : Bool → Type) [∀ a, Fintype (d a)] :
    modExp d true = -Fintype.card (d false) := by
  simp [modExp, Finset.sum_filter]

private theorem key {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {m : Type} [Fintype m] [DecidableEq m] {Y : Type} [AddCommGroup Y]
    [Module ℂ Y] (τ : Representation ℂ (GL m k) Y) (ξ : kˣ →* ℂˣ) (ϖ : kˣ)
    {c : Bool → Bool → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    (f : ∀ i, (Σ j, c i j) ≃ Two (Fin 1) m i) (h00 : Fintype.card (c false false) = 0)
    (e1 : Fin 1 ≃ c true false) (h : ∀ i, Levi k (c i))
    (h0 : ∀ i, h i false = GeneralLinearGroup.scalar _ ϖ) (h1 : ∀ i, h i true = 1) (q : Polynomial ℂ)
    (hq : Polynomial.aeval (jac₂ (spl (m := m) (f true) e1) τ
      (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) q = 0) :
    Polynomial.aeval (relJac f ((extTensor (detRep (Fin 1) ξ) τ).comp
        (leviTwo k (Fin 1) m).symm.toMonoidHom) h) q = 0 := by
  set ρ : Representation ℂ (Levi k (Two (Fin 1) m)) (ℂ ⊗[ℂ] Y) :=
    (extTensor (detRep (Fin 1) ξ) τ).comp (leviTwo k (Fin 1) m).symm.toMonoidHom with hρ
  have hρ1 : ∀ (g : Levi k (Two (Fin 1) m)) (y : Y), GeneralLinearGroup.det (g false) = 1 →
      ρ g ((1 : ℂ) ⊗ₜ[ℂ] y) = (1 : ℂ) ⊗ₜ[ℂ] τ (g true) y := by
    intro g y hg
    refine (extTensor_tmul (detRep (Fin 1) ξ) τ (g false, g true) 1 y).trans ?_
    congr 1
    refine (ofChar_apply _ _ _).trans ?_
    rw [detChar_apply, mul_one]
    exact (congrArg (fun x => ((ξ x : ℂˣ) : ℂ)) hg).trans (by simp)
  let Φ : Jacquet τ (unipRad k (two (spl (m := m) (f true) e1))) →ₗ[ℂ] Jacquet ρ (relUnip k f) :=
    Submodule.mapQ _ _ (TensorProduct.mk ℂ ℂ Y 1) (by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, y, rfl⟩
      have hu : leviTwo k (Fin 1) m (1, u.1) ∈ relUnip k f := by
        rintro (_ | _) -
        · exact one_mem (unipRad k (f false))
        · exact mem_unipRad_spl (m := m) (f true) e1 u.2
      refine Submodule.subset_span ⟨⟨_, hu⟩, (1 : ℂ) ⊗ₜ[ℂ] y, ?_⟩
      rw [hρ1 _ _ (map_one _)]
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
      rfl)
  have hΦ : ∀ y : Y, Φ (Submodule.Quotient.mk y) = Submodule.Quotient.mk ((1 : ℂ) ⊗ₜ[ℂ] y) :=
    fun _ => rfl
  have hc1 : Fintype.card (c true false) = 1 := by
    rw [← Fintype.card_congr e1, Fintype.card_fin]
  have hδ : relDeltaHalf k c h = deltaHalf k (Two (Fin 1) (c true true))
      (leviTwo k (Fin 1) (c true true) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) := by
    rw [deltaHalf_two, relDeltaHalf_apply]
    simp only [deltaHalf_apply, Fintype.prod_bool, h0, h1, det_scalar, h00, hc1, map_one,
      modExp_false, Fintype.card_fin, pow_zero, pow_one, mul_one, one_mul, Int.cast_natCast]
  refine LinearMap.ext fun w => ?_
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨y, rfl⟩ := (TensorProduct.lid ℂ Y).symm.surjective w
  rw [TensorProduct.lid_symm_apply, ← hΦ, ← aeval_intertwine Φ (jac₂ (spl (m := m) (f true) e1) τ
      (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)), hq]
  · simp
  intro v
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  have hd : GeneralLinearGroup.det (relEmb k f h false) = 1 := by
    rw [relEmb_apply, det_leviEmb, Fintype.prod_bool, h0, h1, det_scalar, h00]
    simp
  rw [hΦ, relJac_mk, hρ1 _ _ hd, hδ, relEmb_apply, ← hΦ, ← map_smul]
  congr 1
  refine (jac_mk (two (spl (m := m) (f true) e1)) τ
    (leviTwo k (Fin 1) (c true true) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) v).trans ?_
  rw [← leviEmb_spl (m := m) (f true) e1 ϖ (h true) (h0 true) (h1 true)]

private theorem aeval_relInd {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α β : Type} [Fintype α] [Fintype β] [LinearOrder β]
    {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    {W : Type} [AddCommGroup W] [Module ℂ W] (g : ∀ i, (Σ j, c i j) ≃ m i)
    (σ : Representation ℂ (∀ i, Levi k (c i)) W) (z : Levi k m) (hz : z ∈ relParab k g)
    (hc : ∀ x, x * z = z * x) (hδ : relDeltaHalf k c (relProj k g ⟨z, hz⟩) = 1) (q : Polynomial ℂ)
    (hq : Polynomial.aeval (σ (relProj k g ⟨z, hz⟩)) q = 0) :
    Polynomial.aeval (relInd g σ z) q = 0 := by
  refine aeval_smInd (relParab k g) ((twist σ (relDeltaHalf k c)).comp (relProj k g)) z hz hc q ?_
  have h : ((twist σ (relDeltaHalf k c)).comp (relProj k g)) ⟨z, hz⟩ = σ (relProj k g ⟨z, hz⟩) := by
    refine LinearMap.ext fun v => (twist_apply σ (relDeltaHalf k c) (relProj k g ⟨z, hz⟩) v).trans ?_
    rw [hδ, Units.val_one, one_smul]
  rw [h, hq]

private theorem aeval_cell {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α β : Type} [Fintype α] [Fintype β] [LinearOrder β] [LinearOrder α]
    {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
    (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j)
    (ρ : Representation ℂ (Levi k m) W) (z : Levi k m')
    (hz : z ∈ relParab k (c := fun j i => c i j) g) (hc : ∀ x, x * z = z * x)
    (hδ : relDeltaHalf k (fun j i => c i j) (relProj k (c := fun j i => c i j) g ⟨z, hz⟩) = 1)
    (q : Polynomial ℂ)
    (hq : Polynomial.aeval (relJac f ρ
      (swapBlocks k c (relProj k (c := fun j i => c i j) g ⟨z, hz⟩))) q = 0) :
    Polynomial.aeval (cellFunctor f g ρ z) q = 0 :=
  aeval_relInd (c := fun j i => c i j) g ((relJac f ρ).comp (swapBlocks k c)) z hz hc hδ q hq

section
variable {k : Type} [Field k] {m : Type} [Fintype m] [DecidableEq m]
  {c : Bool → Bool → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]

private theorem z_mem (g : ∀ j, (Σ i, c j i) ≃ Two (Fin 1) m j) (ϖ : kˣ) :
    leviTwo k (Fin 1) m (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) ∈ relParab k g := by
  rintro (_ | _) -
  · exact scalar_mem_parab (n := Fin 1) (g false) ϖ
  · exact one_mem (parab k (n := m) (g true))

private theorem z_false (g : ∀ j, (Σ i, c j i) ≃ Two (Fin 1) m j) (ϖ : kˣ) (i : Bool) :
    relProj k g ⟨_, z_mem g ϖ⟩ false i = GeneralLinearGroup.scalar _ ϖ :=
  leviProj_scalar (n := Fin 1) (g false) ϖ (scalar_mem_parab (n := Fin 1) (g false) ϖ) i

private theorem z_true (g : ∀ j, (Σ i, c j i) ≃ Two (Fin 1) m j) (ϖ : kˣ) (i : Bool) :
    relProj k g ⟨_, z_mem g ϖ⟩ true i = 1 := by
  ext x y
  show (1 : Matrix m m k) (g true ⟨i, x⟩) (g true ⟨i, y⟩) = (1 : Matrix (c true i) (c true i) k) x y
  simp [Matrix.one_apply]

private theorem z_comm (ϖ : kˣ) (x : Levi k (Two (Fin 1) m)) :
    x * leviTwo k (Fin 1) m (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) =
      leviTwo k (Fin 1) m (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) * x := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (leviTwo k (Fin 1) m).surjective x
  rw [← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, scalar_comm, mul_one, one_mul]
end

private theorem delta_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {c : Bool → Bool → Type} [∀ i j, Fintype (c i j)]
    [∀ i j, DecidableEq (c i j)] (h00 : Fintype.card (c false false) = 0) (ϖ : kˣ)
    (h : ∀ i, Levi k (c i)) (h0 : ∀ i, h false i = GeneralLinearGroup.scalar _ ϖ)
    (h1 : ∀ i, h true i = 1) : relDeltaHalf k c h = 1 := by
  rw [relDeltaHalf_apply]
  simp only [deltaHalf_apply, Fintype.prod_bool, h0, h1, det_scalar, h00, map_one,
    modExp_true, pow_zero, mul_one, one_mul]
  simp

private theorem main {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {m : Type} [Fintype m] [DecidableEq m] {Y : Type} [AddCommGroup Y]
    [Module ℂ Y] (τ : Representation ℂ (GL m k) Y) (ξ : kˣ →* ℂˣ) (ϖ : kˣ)
    {c : Bool → Bool → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    (f : ∀ i, (Σ j, c i j) ≃ Two (Fin 1) m i) (g : ∀ j, (Σ i, c i j) ≃ Two (Fin 1) m j)
    (h00 : Fintype.card (c false false) = 0) (e1 : Fin 1 ≃ c true false) (q : Polynomial ℂ)
    (hq : Polynomial.aeval (jac₂ (spl (m := m) (f true) e1) τ
      (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) q = 0) :
    Polynomial.aeval (cellFunctor f g ((extTensor (detRep (Fin 1) ξ) τ).comp
        (leviTwo k (Fin 1) m).symm.toMonoidHom)
        (leviTwo k (Fin 1) m (GeneralLinearGroup.scalar (Fin 1) ϖ, 1))) q = 0 :=
  aeval_cell f g _ _ (z_mem (c := fun j i => c i j) g ϖ) (z_comm ϖ)
    (delta_one (c := fun j i => c i j) h00 ϖ _ (z_false (c := fun j i => c i j) g ϖ)
      (z_true (c := fun j i => c i j) g ϖ)) q
    (key τ ξ ϖ f h00 e1 _ (z_false (c := fun j i => c i j) g ϖ)
      (z_true (c := fun j i => c i j) g ϖ) q hq)

private theorem size_one {m : Type} [Fintype m] (b : SizeMatrix (Two (Fin 1) m) (Two (Fin 1) m))
    (hb : b.1 false false = 0) : 1 = b.1 true false := by
  have h : ∑ i, b.1 i false = Fintype.card (Fin 1) := b.2.2 false
  rw [Fintype.sum_bool, hb, add_zero, Fintype.card_fin] at h
  exact h.symm

end GlobalTheory.T.ScalarParabolicLeviProjection

open GlobalTheory.T.ScalarParabolicLeviProjection in
theorem _root_.GlobalTheory.T.jacquet_polynomial_scalar_eval : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {m : Type} [Fintype m] [DecidableEq m] {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (GL m k) Y) (ξ : kˣ →* ℂˣ) (ϖ : kˣ),
    (∀ (m' : Type) [Fintype m'] [DecidableEq m'] (e' : Fin 1 ⊕ m' ≃ m), ∃ q : Polynomial ℂ,
      q.eval (ξ ϖ : ℂ) ≠ 0 ∧ Polynomial.aeval (jac₂ e' τ (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) q = 0) →
    ∀ b : SizeMatrix (Two (Fin 1) m) (Two (Fin 1) m), b.1 false false = 0 →
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin 1) m i) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin 1) m j)
      (q : Polynomial ℂ), q.eval (ξ ϖ : ℂ) ≠ 0 ∧
      Polynomial.aeval (cellFunctor f g ((extTensor (detRep (Fin 1) ξ) τ).comp
        (leviTwo k (Fin 1) m).symm.toMonoidHom) (leviTwo k (Fin 1) m (GeneralLinearGroup.scalar (Fin 1) ϖ, 1))) q = 0 := by
  intro k _ _ _ _ m _ _ Y _ _ τ ξ ϖ H b hb
  have hq := H (Fin (b.1 true true)) (spl (m := m) (d := fun j => Fin (b.1 true j))
    (b.nonempty_rows.some true) (finCongr (size_one b hb)))
  have h00 : Fintype.card (Fin (b.1 false false)) = 0 := (Fintype.card_fin _).trans hb
  exact hq.elim fun q hq => ⟨b.nonempty_rows.some, b.nonempty_cols.some, q, hq.1,
    main τ ξ ϖ (c := fun i j => Fin (b.1 i j)) _ _ h00 (finCongr (size_one b hb)) q hq.2⟩
