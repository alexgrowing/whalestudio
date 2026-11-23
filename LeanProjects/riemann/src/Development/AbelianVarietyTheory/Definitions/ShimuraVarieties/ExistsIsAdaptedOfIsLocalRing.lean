import Mathlib

open Module TensorProduct

namespace GlobalTheory

noncomputable section

section Dual

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

def basisOfDual (v : ι → M) (c : ι → Dual R M) (h₁ : ∀ i j, c i (v j) = if i = j then 1 else 0)
    (h₂ : ∀ x, ∑ i, c i x • v i = x) : Basis ι R M :=
  Basis.ofEquivFun <| LinearEquiv.ofLinear (LinearMap.pi c) (Fintype.linearCombination R v)
    (by
      refine LinearMap.ext fun a => funext fun i => ?_
      simp [Fintype.linearCombination_apply, h₁])
    (by
      refine LinearMap.ext fun x => ?_
      simp [Fintype.linearCombination_apply, h₂])

@[simp] theorem basisOfDual_apply (v : ι → M) (c : ι → Dual R M) (h₁ h₂) (j : ι) :
    basisOfDual v c h₁ h₂ j = v j := by
  simp [basisOfDual, Fintype.linearCombination_apply, Function.update_apply]

@[simp] theorem basisOfDual_repr (v : ι → M) (c : ι → Dual R M) (h₁ h₂) (x : M) (i : ι) :
    (basisOfDual v c h₁ h₂).repr x i = c i x := by
  simp [basisOfDual]

end Dual

section Action

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

def basisMulGL (b : Basis ι R M) (g : GL ι R) : Basis ι R M :=
  b.map (Matrix.toLinOfInv b b g.mul_inv g.inv_mul)

theorem basisMulGL_apply (b : Basis ι R M) (g : GL ι R) (j : ι) :
    basisMulGL b g j = ∑ i, (g : Matrix ι ι R) i j • b i := by
  simp [basisMulGL, Matrix.toLinOfInv, Matrix.toLin_self]

@[simp] theorem toMatrix_basisMulGL (b : Basis ι R M) (g : GL ι R) :
    b.toMatrix (basisMulGL b g) = g := by
  ext i j
  simp [Basis.toMatrix_apply, basisMulGL_apply, Finsupp.single_apply]

@[simp] theorem basisMulGL_one (b : Basis ι R M) : basisMulGL b 1 = b := by
  ext j
  simp [basisMulGL_apply, Matrix.one_apply]

theorem basisMulGL_mul (b : Basis ι R M) (g h : GL ι R) :
    basisMulGL b (g * h) = basisMulGL (basisMulGL b g) h := by
  ext j
  simp only [basisMulGL_apply, Units.val_mul, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul,
    smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

def basisChange (b b' : Basis ι R M) : GL ι R :=
  ⟨b.toMatrix b', b'.toMatrix b, Basis.toMatrix_mul_toMatrix_flip _ _,
    Basis.toMatrix_mul_toMatrix_flip _ _⟩

@[simp] theorem coe_basisChange (b b' : Basis ι R M) :
    (basisChange b b' : Matrix ι ι R) = b.toMatrix b' := rfl

@[simp] theorem basisMulGL_basisChange (b b' : Basis ι R M) :
    basisMulGL b (basisChange b b') = b' := by
  ext j
  simp [basisMulGL_apply, Basis.toMatrix_apply]

@[simp] theorem basisChange_basisMulGL (b : Basis ι R M) (g : GL ι R) :
    basisChange b (basisMulGL b g) = g := Units.ext (by simp)

@[simps] def glEquivBasis (b : Basis ι R M) : GL ι R ≃ Basis ι R M where
  toFun := basisMulGL b
  invFun := basisChange b
  left_inv := basisChange_basisMulGL b
  right_inv := basisMulGL_basisChange b

theorem basisMulGL_repr (b : Basis ι R M) (g : GL ι R) (x : M) (i : ι) :
    (basisMulGL b g).repr x i = ∑ j, ((g⁻¹ : GL ι R) : Matrix ι ι R) i j * b.repr x j := by
  have h : basisMulGL (basisMulGL b g) g⁻¹ = b := by rw [← basisMulGL_mul]; simp
  have h' : (basisMulGL b g).toMatrix b = ((g⁻¹ : GL ι R) : Matrix ι ι R) := by
    conv_lhs => rw [← h]
    rw [h, ← toMatrix_basisMulGL (basisMulGL b g) g⁻¹, h]
  rw [← h']
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul,
    Basis.toMatrix_apply, mul_comm]

@[reducible] def basisMulAction : MulAction (GL ι R)ᵐᵒᵖ (Basis ι R M) where
  smul g b := basisMulGL b g.unop
  one_smul := basisMulGL_one
  mul_smul g h b := basisMulGL_mul b h.unop g.unop

end Action

section Triangular

variable (ι R : Type*) [CommRing R] [Fintype ι] [LinearOrder ι]

def upperTriangularGL : Subgroup (GL ι R) where
  carrier := {g | (g : Matrix ι ι R).IsUpperTriangular}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' ha hb := Matrix.BlockTriangular.mul ha hb
  inv_mem' {g} hg := by
    let := g.invertible
    change ((g⁻¹ : GL ι R) : Matrix ι ι R).BlockTriangular id
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

variable {ι R}

theorem mem_upperTriangularGL {g : GL ι R} :
    g ∈ upperTriangularGL ι R ↔ ∀ i j, j < i → (g : Matrix ι ι R) i j = 0 :=
  ⟨fun h _ _ hij => h hij, fun h _ _ hij => h _ _ hij⟩

theorem upperTriangular_mul_diag {a b : Matrix ι ι R} (ha : a.IsUpperTriangular)
    (hb : b.IsUpperTriangular) (i : ι) : (a * b) i i = a i i * b i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [ha h, zero_mul]
  · rw [hb h, mul_zero]

def upperTriangularGL.diagChar (i : ι) : upperTriangularGL ι R →* Rˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => (g.1 : Matrix ι ι R) i i
      map_one' := by simp
      map_mul' := fun g h => upperTriangular_mul_diag g.2 h.2 i }

@[simp] theorem upperTriangularGL.coe_diagChar (i : ι) (g : upperTriangularGL ι R) :
    (upperTriangularGL.diagChar i g : R) = (g.1 : Matrix ι ι R) i i := rfl

theorem map_mem_upperTriangularGL {S : Type*} [CommRing S] (f : R →+* S) {g : GL ι R}
    (hg : g ∈ upperTriangularGL ι R) :
    Matrix.GeneralLinearGroup.map f g ∈ upperTriangularGL ι S := by
  rw [mem_upperTriangularGL] at hg ⊢
  intro i j hij
  simp [Matrix.GeneralLinearGroup.map_apply, hg i j hij]

variable {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ}

theorem mem_basis_flag_iff (b : Basis (Fin n) R M) (k : Fin (n + 1)) (x : M) :
    x ∈ b.flag k ↔ ∀ i : Fin n, k ≤ i.castSucc → b.repr x i = 0 := by
  refine ⟨fun hx i hi => b.flag_le_ker_coord hi hx, fun h => ?_⟩
  rw [← b.sum_repr x]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : i.castSucc < k
  · exact Submodule.smul_mem _ _ (b.self_mem_flag hi)
  · simp [h i (not_lt.mp hi)]

theorem flag_basisMulGL_le (b : Basis (Fin n) R M) {g : GL (Fin n) R}
    (hg : g ∈ upperTriangularGL (Fin n) R) (k : Fin (n + 1)) :
    (basisMulGL b g).flag k ≤ b.flag k := by
  rw [Basis.flag_le_iff]
  intro j hj
  rw [mem_basis_flag_iff]
  intro i hi
  have : j < i := Fin.castSucc_lt_castSucc_iff.mp (hj.trans_le hi)
  rw [← Basis.toMatrix_apply, toMatrix_basisMulGL, mem_upperTriangularGL.mp hg i j this]

theorem flag_basisMulGL_eq_iff (b : Basis (Fin n) R M) (g : GL (Fin n) R) :
    (basisMulGL b g).flag = b.flag ↔ g ∈ upperTriangularGL (Fin n) R := by
  constructor
  · intro h
    rw [mem_upperTriangularGL]
    intro i j hij
    have hj : basisMulGL b g j ∈ b.flag j.succ := by
      rw [← h]
      exact Basis.self_mem_flag _ Fin.castSucc_lt_succ
    rw [← toMatrix_basisMulGL b g, Basis.toMatrix_apply]
    exact (mem_basis_flag_iff b _ _).mp hj i (Fin.succ_le_castSucc_iff.mpr hij)
  · intro hg
    funext k
    refine le_antisymm (flag_basisMulGL_le b hg k) ?_
    have h := flag_basisMulGL_le (basisMulGL b g) (inv_mem hg) k
    rwa [← basisMulGL_mul, mul_inv_cancel, basisMulGL_one] at h

theorem flag_eq_flag_iff (b b' : Basis (Fin n) R M) :
    b'.flag = b.flag ↔ basisChange b b' ∈ upperTriangularGL (Fin n) R := by
  rw [← flag_basisMulGL_eq_iff b, basisMulGL_basisChange]

end Triangular

section Flag

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

abbrev SubQuot (P Q : Submodule R M) : Type _ := Q ⧸ P.submoduleOf Q

def subQuotEquivOfSplitting {L : Type*} [AddCommGroup L] [Module R L] {P Q : Submodule R M}
    (π : M →ₗ[R] L) (σ : L →ₗ[R] M) (h₁ : ∀ l, π (σ l) = l) (h₂ : ∀ x ∈ P, π x = 0)
    (h₃ : ∀ l, σ l ∈ Q) (h₄ : ∀ x ∈ Q, x - σ (π x) ∈ P) : SubQuot P Q ≃ₗ[R] L :=
  (Submodule.quotEquivOfEq _ (LinearMap.ker (π ∘ₗ Q.subtype)) (by
    ext x
    refine ⟨fun hx => h₂ _ hx, fun hx => ?_⟩
    have hx' : π x = 0 := hx
    have := h₄ x x.2
    rwa [hx', map_zero, sub_zero] at this)).trans
    ((π ∘ₗ Q.subtype).quotKerEquivOfSurjective fun l => ⟨⟨σ l, h₃ l⟩, h₁ l⟩)

variable (R M) in

@[ext] structure FullFlag (n : ℕ) where

  sub : Fin (n + 1) → Submodule R M
  sub_zero : sub 0 = ⊥
  sub_last : sub (Fin.last n) = ⊤
  castSucc_le_succ : ∀ i : Fin n, sub i.castSucc ≤ sub i.succ
  invertible_step : ∀ i : Fin n, Module.Invertible R (SubQuot (sub i.castSucc) (sub i.succ))

namespace FullFlag

variable {n : ℕ}

abbrev Step (F : FullFlag R M n) (i : Fin n) : Type _ := SubQuot (F.sub i.castSucc) (F.sub i.succ)

instance (F : FullFlag R M n) (i : Fin n) : Module.Invertible R (F.Step i) := F.invertible_step i

theorem monotone (F : FullFlag R M n) : Monotone F.sub :=
  Fin.monotone_iff_le_succ.2 F.castSucc_le_succ

def basisStepEquiv (b : Basis (Fin n) R M) (i : Fin n) :
    SubQuot (b.flag i.castSucc) (b.flag i.succ) ≃ₗ[R] R :=
  subQuotEquivOfSplitting (b.coord i) (LinearMap.toSpanSingleton R M (b i)) (by simp)
    (fun _ hx => b.flag_le_ker_coord le_rfl hx)
    (fun l => Submodule.smul_mem _ _ (b.self_mem_flag Fin.castSucc_lt_succ))
    (fun x hx => by
      rw [mem_basis_flag_iff] at hx ⊢
      intro j hj
      rcases (Fin.castSucc_le_castSucc_iff.mp hj).eq_or_lt with rfl | h
      · simp
      · simp [hx j (Fin.succ_le_castSucc_iff.mpr h), Finsupp.single_apply, h.ne])

def ofBasis (b : Basis (Fin n) R M) : FullFlag R M n where
  sub := b.flag
  sub_zero := b.flag_zero
  sub_last := b.flag_last
  castSucc_le_succ _ := b.flag_mono Fin.castSucc_lt_succ.le
  invertible_step i := Module.Invertible.congr (basisStepEquiv b i).symm

@[simp] theorem ofBasis_sub (b : Basis (Fin n) R M) : (ofBasis b).sub = b.flag := rfl

def IsAdapted (F : FullFlag R M n) (b : Basis (Fin n) R M) : Prop := b.flag = F.sub

theorem isAdapted_iff {F : FullFlag R M n} {b : Basis (Fin n) R M} :
    F.IsAdapted b ↔ ofBasis b = F := ⟨fun h => FullFlag.ext h, fun h => h ▸ rfl⟩

theorem isAdapted_ofBasis (b : Basis (Fin n) R M) : (ofBasis b).IsAdapted b := rfl

theorem ofBasis_eq_ofBasis_iff (b b' : Basis (Fin n) R M) :
    ofBasis b' = ofBasis b ↔ ∃ g ∈ upperTriangularGL (Fin n) R, basisMulGL b g = b' := by
  rw [FullFlag.ext_iff, ofBasis_sub, ofBasis_sub, flag_eq_flag_iff]
  refine ⟨fun h => ⟨_, h, basisMulGL_basisChange b b'⟩, ?_⟩
  rintro ⟨g, hg, rfl⟩
  simpa using hg

theorem IsAdapted.basisMulGL_iff {F : FullFlag R M n} {b : Basis (Fin n) R M} (hb : F.IsAdapted b)
    (g : GL (Fin n) R) : F.IsAdapted (basisMulGL b g) ↔ g ∈ upperTriangularGL (Fin n) R := by
  rw [← flag_basisMulGL_eq_iff b, IsAdapted, ← hb]

theorem exists_retraction (F : FullFlag R M n) (k : Fin (n + 1)) :
    ∃ r : M →ₗ[R] M, (∀ x, r x ∈ F.sub k) ∧ ∀ x ∈ F.sub k, r x = x := by
  induction k using Fin.reverseInduction with
  | last => exact ⟨LinearMap.id, fun x => by simp [F.sub_last], fun _ _ => rfl⟩
  | cast i ih =>
    obtain ⟨r, hr₁, hr₂⟩ := ih
    obtain ⟨s, hs⟩ := Module.projective_lifting_property
      ((F.sub i.castSucc).submoduleOf (F.sub i.succ)).mkQ (LinearMap.id (R := R) (M := F.Step i))
      (Submodule.mkQ_surjective _)
    let r' : M →ₗ[R] F.sub i.succ := r.codRestrict _ hr₁
    refine ⟨r - (F.sub i.succ).subtype ∘ₗ s ∘ₗ Submodule.mkQ _ ∘ₗ r', fun x => ?_, fun x hx => ?_⟩
    · have : r' x - s (Submodule.mkQ _ (r' x)) ∈ (F.sub i.castSucc).submoduleOf (F.sub i.succ) := by
        rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
        exact sub_eq_zero.mpr (congr($hs _)).symm
      exact this
    · have hx' := F.castSucc_le_succ i hx
      have : Submodule.mkQ ((F.sub i.castSucc).submoduleOf (F.sub i.succ)) (r' x) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        change r x ∈ F.sub i.castSucc
        rwa [hr₂ x hx']
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, this, map_zero, hr₂ x hx']
      exact _root_.sub_zero x

theorem exists_isCompl (F : FullFlag R M n) (k : Fin (n + 1)) :
    ∃ Q : Submodule R M, IsCompl (F.sub k) Q := by
  obtain ⟨r, h₁, h₂⟩ := F.exists_retraction k
  exact ⟨_, LinearMap.isCompl_of_proj (f := r.codRestrict _ h₁) fun x => Subtype.ext (h₂ x x.2)⟩

theorem exists_splitting (F : FullFlag R M n) (i : Fin n) :
    ∃ (π : M →ₗ[R] F.Step i) (σ : F.Step i →ₗ[R] M), (∀ l, π (σ l) = l) ∧
      (∀ x ∈ F.sub i.castSucc, π x = 0) ∧ (∀ l, σ l ∈ F.sub i.succ) ∧
      (∀ x ∈ F.sub i.succ, x - σ (π x) ∈ F.sub i.castSucc) := by
  obtain ⟨r, hr₁, hr₂⟩ := F.exists_retraction i.succ
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    ((F.sub i.castSucc).submoduleOf (F.sub i.succ)).mkQ (LinearMap.id (R := R) (M := F.Step i))
    (Submodule.mkQ_surjective _)
  let r' : M →ₗ[R] F.sub i.succ := r.codRestrict _ hr₁
  have hr' : ∀ y : F.sub i.succ, r' y = y := fun y => Subtype.ext (hr₂ y y.2)
  refine ⟨Submodule.mkQ _ ∘ₗ r', (F.sub i.succ).subtype ∘ₗ s, fun l => ?_, fun x hx => ?_,
    fun l => (s l).2, fun x hx => ?_⟩
  · simp only [LinearMap.comp_apply, Submodule.subtype_apply, hr']
    exact congr($hs l)
  · rw [LinearMap.comp_apply, hr' ⟨x, F.castSucc_le_succ i hx⟩, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hx
  · have : (⟨x, hx⟩ : F.sub i.succ) - s (Submodule.mkQ _ ⟨x, hx⟩) ∈
        (F.sub i.castSucc).submoduleOf (F.sub i.succ) := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
      exact sub_eq_zero.mpr (congr($hs _)).symm
    simp only [LinearMap.comp_apply, hr' ⟨x, hx⟩]
    exact this

theorem nonempty_baseChange_step_equiv (F : FullFlag R M n) (S : Type*) [CommRing S] [Algebra R S]
    (i : Fin n) : Nonempty (SubQuot ((F.sub i.castSucc).baseChange S) ((F.sub i.succ).baseChange S)
      ≃ₗ[S] S ⊗[R] F.Step i) := by
  obtain ⟨π, σ, h₁, h₂, h₃, h₄⟩ := F.exists_splitting i
  refine ⟨subQuotEquivOfSplitting (π.baseChange S) (σ.baseChange S) (fun l => ?_) (fun x hx => ?_)
    (fun l => ?_) (fun x hx => ?_)⟩
  · induction l with
    | zero => simp
    | tmul a l => simp [h₁]
    | add x y hx hy => simp [hx, hy]
  · obtain ⟨x, rfl⟩ := hx
    induction x with
    | zero => simp
    | tmul a l => simp [h₂ l l.2]
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  · induction l with
    | zero => simp
    | tmul a l => exact Submodule.tmul_mem_baseChange_of_mem _ (h₃ l)
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  · obtain ⟨x, rfl⟩ := hx
    induction x with
    | zero => simp
    | tmul a l =>
      simp only [LinearMap.baseChange_tmul, Submodule.subtype_apply, ← tmul_sub]
      exact Submodule.tmul_mem_baseChange_of_mem _ (h₄ l l.2)
    | add x y hx hy =>
      simp only [map_add]
      rw [add_sub_add_comm]
      exact add_mem hx hy

def baseChange (F : FullFlag R M n) (S : Type*) [CommRing S] [Algebra R S] :
    FullFlag S (S ⊗[R] M) n where
  sub k := (F.sub k).baseChange S
  sub_zero := by rw [F.sub_zero, Submodule.baseChange_bot]
  sub_last := by rw [F.sub_last, Submodule.baseChange_top]
  castSucc_le_succ i := Submodule.baseChange_mono S (F.castSucc_le_succ i)
  invertible_step i := Module.Invertible.congr (F.nonempty_baseChange_step_equiv S i).some.symm

@[simp] theorem baseChange_sub (F : FullFlag R M n) (S : Type*) [CommRing S] [Algebra R S]
    (k : Fin (n + 1)) : (F.baseChange S).sub k = (F.sub k).baseChange S := rfl

theorem ofBasis_baseChange (b : Basis (Fin n) R M) (S : Type*) [CommRing S] [Algebra R S] :
    ofBasis (b.baseChange S) = (ofBasis b).baseChange S := by
  ext1
  funext k
  simp only [ofBasis_sub, baseChange_sub, Basis.flag, Submodule.baseChange_span, Set.image_image]
  simp

def map {M' : Type*} [AddCommGroup M'] [Module R M'] (F : FullFlag R M n) (e : M ≃ₗ[R] M') :
    FullFlag R M' n where
  sub k := (F.sub k).map e.toLinearMap
  sub_zero := by rw [F.sub_zero, Submodule.map_bot]
  sub_last := by rw [F.sub_last, Submodule.map_top, LinearEquiv.range]
  castSucc_le_succ i := Submodule.map_mono (F.castSucc_le_succ i)
  invertible_step i := by
    obtain ⟨π, σ, h₁, h₂, h₃, h₄⟩ := F.exists_splitting i
    refine Module.Invertible.congr (subQuotEquivOfSplitting (π ∘ₗ e.symm.toLinearMap)
      (e.toLinearMap ∘ₗ σ) (fun l => by simp [h₁]) ?_ ?_ ?_).symm
    · rintro _ ⟨x, hx, rfl⟩
      simp [h₂ x hx]
    · exact fun l => ⟨_, h₃ l, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨_, h₄ x hx, by simp⟩

@[simp] theorem map_sub {M' : Type*} [AddCommGroup M'] [Module R M'] (F : FullFlag R M n)
    (e : M ≃ₗ[R] M') (k : Fin (n + 1)) : (F.map e).sub k = (F.sub k).map e.toLinearMap := rfl

theorem ofBasis_map {M' : Type*} [AddCommGroup M'] [Module R M'] (b : Basis (Fin n) R M)
    (e : M ≃ₗ[R] M') : ofBasis (b.map e) = (ofBasis b).map e := by
  ext1
  funext k
  simp only [ofBasis_sub, map_sub, Basis.flag, Submodule.map_span, Set.image_image]
  rfl

theorem exists_isAdapted_of_free (F : FullFlag R M n) (h : ∀ i, Module.Free R (F.Step i)) :
    ∃ b : Basis (Fin n) R M, F.IsAdapted b := by
  choose π σ h₁ h₂ h₃ h₄ using F.exists_splitting
  have e : ∀ i, F.Step i ≃ₗ[R] R := fun i => (Module.Invertible.free_iff_linearEquiv.mp (h i)).some
  let v : Fin n → M := fun i => σ i ((e i).symm 1)
  have hv : ∀ (i) (l : F.Step i), σ i l = e i l • v i := fun i l => by
    simp only [v, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  have hspan : ∀ k, Submodule.span R (v '' {i | i.castSucc < k}) = F.sub k := by
    intro k
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact F.monotone (Fin.castSucc_lt_iff_succ_le.mp hi) (h₃ i _)
    · induction k using Fin.induction with
      | zero => rw [F.sub_zero]; exact bot_le
      | succ i ih =>
        intro x hx
        rw [← sub_add_cancel x (σ i (π i x))]
        refine add_mem (Submodule.span_mono (Set.image_mono ?_) (ih (h₄ i x hx))) ?_
        · exact fun j hj => lt_trans hj Fin.castSucc_lt_succ
        · rw [hv]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Fin.castSucc_lt_succ, rfl⟩)
  have hli : LinearIndependent R v := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    by_contra hne
    push Not at hne
    classical
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i => a i ≠ 0) id
      (by obtain ⟨i, hi⟩ := hne; exact ⟨i, by simpa using hi⟩)
    have h0 : e i (π i (∑ j, a j • v j)) = a i := by
      rw [map_sum, map_sum, Finset.sum_eq_single i _ (by simp)]
      · simp [v, h₁]
      · intro j _ hj
        by_cases haj : a j = 0
        · simp [haj]
        have hji : j < i := lt_of_le_of_ne (hmax j (by simpa using haj)) hj
        rw [map_smul, h₂ i (v j) (F.monotone (Fin.succ_le_castSucc_iff.mpr hji) (h₃ j _))]
        simp
    rw [ha] at h0
    simp only [map_zero] at h0
    exact (Finset.mem_filter.mp hi).2 h0.symm
  refine ⟨Basis.mk hli ?_, funext fun k => ?_⟩
  · have := hspan (Fin.last n)
    rw [F.sub_last] at this
    exact this.ge.trans (Submodule.span_mono (Set.image_subset_range _ _))
  · rw [Basis.flag, Basis.coe_mk]
    exact hspan k

theorem exists_isAdapted_of_isLocalRing [IsLocalRing R] (F : FullFlag R M n) :
    ∃ b : Basis (Fin n) R M, F.IsAdapted b :=
  F.exists_isAdapted_of_free fun _ => Module.free_of_flat_of_isLocalRing

theorem free_baseChange_of_algHom {L S T : Type*} [AddCommGroup L] [Module R L] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] (φ : S →ₐ[R] T) [Module.Free S (S ⊗[R] L)] :
    Module.Free T (T ⊗[R] L) := by
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq fun r => (φ.commutes r).symm
  exact Module.Free.of_equiv (AlgebraTensorModule.cancelBaseChange R S T T L)

theorem exists_isAdapted_localization (F : FullFlag R M n) (p : Ideal R) [hp : p.IsPrime] :
    ∃ f ∉ p, ∀ (S : Type*) [CommRing S] [Algebra R S], IsUnit (algebraMap R S f) →
      ∃ b : Basis (Fin n) S (S ⊗[R] M), (F.baseChange S).IsAdapted b := by
  have key : ∀ i, ∃ f ∉ p, Module.Free (Localization.Away f)
      (Localization.Away f ⊗[R] F.Step i) := by
    intro i
    obtain ⟨s, hs, hfree⟩ := Module.Invertible.exists_finset_free_localization R (F.Step i)
    obtain ⟨f, hf, hfp⟩ : ∃ f ∈ s, f ∉ p := by
      by_contra hcon
      push Not at hcon
      exact hp.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr hcon))
    have := hfree f hf
    exact ⟨f, hfp, Module.Free.of_equiv (IsLocalizedModule.isBaseChange (.powers f)
      (Localization.Away f) (LocalizedModule.mkLinearMap (.powers f) (F.Step i))).equiv.symm⟩
  choose f hf hfree using key
  refine ⟨∏ i, f i, ?_, fun S _ _ hS => ?_⟩
  · exact fun h => by
      obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      exact hf i hi
  · refine exists_isAdapted_of_free _ fun i => ?_
    have hi : IsUnit (algebraMap R S (f i)) :=
      isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem f (Finset.mem_univ i))) hS
    have := hfree i
    have := free_baseChange_of_algHom (L := F.Step i)
      (IsLocalization.Away.liftAlgHom (S := Localization.Away (f i)) (f i)
        (f := Algebra.ofId R S) hi)
    exact Module.Free.of_equiv (F.nonempty_baseChange_step_equiv S i).some.symm

end FullFlag

end Flag

example (b : Basis (Fin 2) ℤ (Fin 2 → ℤ)) :
    basisMulGL b ⟨!![1, 1; 0, 1], !![1, -1; 0, 1], by decide, by decide⟩ 1 = b 0 + b 1 := by
  simp [basisMulGL_apply]

example : (FullFlag.ofBasis (Pi.basisFun ℤ (Fin 2))).sub 1 =
    Submodule.span ℤ {Pi.single 0 1} := by
  have : {i : Fin 2 | i.castSucc < 1} = {0} := by
    ext i
    fin_cases i <;> simp
  simp [Basis.flag, this]

end

end GlobalTheory
