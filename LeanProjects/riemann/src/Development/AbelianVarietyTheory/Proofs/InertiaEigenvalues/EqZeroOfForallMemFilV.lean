import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

noncomputable section

namespace GlobalTheory.DRFil

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Bil

variable {Qp : Type} [Field Qp] (F : Type) [CommRing F] [Algebra Qp F]
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']

variable (Qp) in

def bil (β : V →ₗ[LL] V' →ₗ[LL] V'') : V ⊗[Qp] F →ₗ[LL] V' ⊗[Qp] F →ₗ[LL] V'' ⊗[Qp] F :=
  TensorProduct.curry
    ((AlgebraTensorModule.map (TensorProduct.lift β) (LinearMap.mul' Qp F)).comp
      (AlgebraTensorModule.tensorTensorTensorComm Qp Qp LL LL V F V' F).toLinearMap)

@[simp] theorem bil_tmul (β : V →ₗ[LL] V' →ₗ[LL] V'') (v : V) (w : V') (b b' : F) :
    bil Qp F β (v ⊗ₜ[Qp] b) (w ⊗ₜ[Qp] b') = β v w ⊗ₜ[Qp] (b * b') := by
  simp [bil]

variable (Qp LL V) in

def sm : LL ⊗[Qp] F →ₗ[LL] V ⊗[Qp] F →ₗ[LL] V ⊗[Qp] F := bil Qp F (LinearMap.lsmul LL V)

@[simp] theorem sm_tmul (c : LL) (v : V) (b b' : F) :
    sm Qp F LL V (c ⊗ₜ[Qp] b) (v ⊗ₜ[Qp] b') = (c • v) ⊗ₜ[Qp] (b * b') := by
  simp [sm]

variable (Qp) in

abbrev ext (f : V →ₗ[LL] V') : V ⊗[Qp] F →ₗ[LL] V' ⊗[Qp] F :=
  AlgebraTensorModule.map f (LinearMap.id : F →ₗ[Qp] F)

variable (Qp LL V) in

abbrev mulR (b : F) : V ⊗[Qp] F →ₗ[LL] V ⊗[Qp] F :=
  AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp b)

variable {F}

theorem sm_tmul_left (c : LL) (b : F) (x : V ⊗[Qp] F) :
    sm Qp F LL V (c ⊗ₜ[Qp] b) x = c • mulR Qp F LL V b x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b' => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

theorem sm_one_tmul (b : F) (x : V ⊗[Qp] F) :
    sm Qp F LL V ((1 : LL) ⊗ₜ[Qp] b) x = mulR Qp F LL V b x := by
  rw [sm_tmul_left, one_smul]

@[simp] theorem sm_one (x : V ⊗[Qp] F) : sm Qp F LL V 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b' => simp [Algebra.TensorProduct.one_def]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem bil_sm_left (β : V →ₗ[LL] V' →ₗ[LL] V'') (r : LL ⊗[Qp] F) (x : V ⊗[Qp] F) (y : V' ⊗[Qp] F) :
    bil Qp F β (sm Qp F LL V r x) y = sm Qp F LL V'' r (bil Qp F β x y) := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add r s hr hs => simp only [map_add, LinearMap.add_apply, hr, hs]
  | tmul c b =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add r s hr hs => simp only [map_add, LinearMap.add_apply, hr, hs]
    | tmul v b' =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add r s hr hs => simp only [map_add, hr, hs]
      | tmul w b'' => simp [mul_assoc]

theorem bil_sm_right (β : V →ₗ[LL] V' →ₗ[LL] V'') (r : LL ⊗[Qp] F) (x : V ⊗[Qp] F) (y : V' ⊗[Qp] F) :
    bil Qp F β x (sm Qp F LL V' r y) = sm Qp F LL V'' r (bil Qp F β x y) := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add r s hr hs => simp only [map_add, LinearMap.add_apply, hr, hs]
  | tmul c b =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add r s hr hs => simp only [map_add, LinearMap.add_apply, hr, hs]
    | tmul v b' =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add r s hr hs => simp only [map_add, hr, hs]
      | tmul w b'' => simp [mul_left_comm]

theorem sm_self (r s : LL ⊗[Qp] F) : sm Qp F LL LL r s = r * s := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add r s hr hs => simp only [map_add, LinearMap.add_apply, hr, hs, add_mul]
  | tmul c b =>
    induction s using TensorProduct.induction_on with
    | zero => simp
    | add r s hr hs => simp only [map_add, hr, hs, mul_add]
    | tmul v b' => simp

theorem sm_mul (r s : LL ⊗[Qp] F) (x : V ⊗[Qp] F) :
    sm Qp F LL V (r * s) x = sm Qp F LL V r (sm Qp F LL V s x) := by
  rw [← sm_self]
  exact bil_sm_left (LinearMap.lsmul LL V) r s x

theorem sm_comm (r s : LL ⊗[Qp] F) (x : V ⊗[Qp] F) :
    sm Qp F LL V r (sm Qp F LL V s x) = sm Qp F LL V s (sm Qp F LL V r x) := by
  rw [← sm_mul, mul_comm, sm_mul]

theorem ext_sm (f : V →ₗ[LL] V') (r : LL ⊗[Qp] F) (x : V ⊗[Qp] F) :
    ext Qp F f (sm Qp F LL V r x) = sm Qp F LL V' r (ext Qp F f x) := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add r s hr hs => simp only [map_add, LinearMap.add_apply, hr, hs]
  | tmul c b =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add r s hr hs => simp only [map_add, hr, hs]
    | tmul v b' => simp

theorem eq_zero_of_forall_ext (x : V ⊗[Qp] F) (h : ∀ φ : V →ₗ[LL] LL, ext Qp F φ x = 0) : x = 0 := by
  classical
  let bV := Basis.ofVectorSpace LL V
  have key : ∀ x : V ⊗[Qp] F, ∃ s : Finset _, ∀ t : Finset _, s ⊆ t →
      x = ∑ i ∈ t, sm Qp F LL V (ext Qp F (bV.coord i) x) (bV i ⊗ₜ[Qp] (1 : F)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨∅, fun t _ => by simp⟩
    | add x y hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨s', hs'⟩ := hy
      refine ⟨s ∪ s', fun t ht => ?_⟩
      simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib]
      rw [← hs t (Finset.subset_union_left.trans ht), ← hs' t (Finset.subset_union_right.trans ht)]
    | tmul v b =>
      refine ⟨(bV.repr v).support, fun t ht => ?_⟩
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, sm_tmul, mul_one,
        Basis.coord_apply, ← TensorProduct.sum_tmul]
      congr 1
      conv_lhs => rw [← bV.linearCombination_repr v]
      rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ ht _ (by simp)]
  obtain ⟨s, hs⟩ := key x
  rw [hs s le_rfl]
  simp [h]

theorem eq_sum_basis {ι : Type} [Fintype ι] (bV : Basis ι LL V) (x : V ⊗[Qp] F) :
    x = ∑ i, sm Qp F LL V (ext Qp F (bV.coord i) x) (bV i ⊗ₜ[Qp] (1 : F)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib]
    rw [← hx, ← hy]
  | tmul v b =>
    simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, sm_tmul, mul_one,
      Basis.coord_apply, ← TensorProduct.sum_tmul]
    rw [bV.sum_repr]

end Bil

section Idem

variable {Qp K : Type} [Field Qp] [Field K] [Algebra Qp K]
    {LL : Type} [Field LL] [Algebra Qp LL]

theorem exists_idem [FiniteDimensional Qp K] [CharZero Qp] (τ : K →ₐ[Qp] LL) :
    ∃ e : LL ⊗[Qp] K, Algebra.TensorProduct.lift (AlgHom.id Qp LL) τ (fun _ _ => Commute.all _ _) e = 1 ∧
      ∀ c : K, ((1 : LL) ⊗ₜ[Qp] c) * e = τ c • e := by
  haveI : Algebra.IsSeparable Qp K := inferInstance
  haveI : Algebra.FormallyUnramified Qp K := Algebra.FormallyUnramified.of_isSeparable Qp K
  obtain ⟨t, ht, ht1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := Qp) (S := K)).1 inferInstance
  refine ⟨Algebra.TensorProduct.map τ (AlgHom.id Qp K) t, ?_, fun c => ?_⟩
  · have : ∀ t : K ⊗[Qp] K, Algebra.TensorProduct.lift (AlgHom.id Qp LL) τ (fun _ _ => Commute.all _ _)
        (Algebra.TensorProduct.map τ (AlgHom.id Qp K) t) = τ (Algebra.TensorProduct.lmul' Qp t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a b => simp
    rw [this, ht1, map_one]
  · have h := congrArg (Algebra.TensorProduct.map τ (AlgHom.id Qp K)) (ht c)
    rw [map_mul, map_sub, map_zero, sub_mul, sub_eq_zero] at h
    simp only [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] at h
    rw [h, Algebra.smul_def]
    rfl

variable [FiniteDimensional Qp K] [CharZero Qp] (F : Type) [CommRing F] [Algebra Qp F] [Algebra K F]
  [IsScalarTower Qp K F]
  {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def idem (τ : K →ₐ[Qp] LL) : LL ⊗[Qp] F :=
  Algebra.TensorProduct.map (AlgHom.id Qp LL) (IsScalarTower.toAlgHom Qp K F) (exists_idem τ).choose

theorem idem_repr (τ : K →ₐ[Qp] LL) : ∃ (n : ℕ) (a : Fin n → LL) (c : Fin n → K),
    idem F τ = ∑ i, a i ⊗ₜ[Qp] algebraMap K F (c i) ∧ ∑ i, a i * τ (c i) = 1 := by
  obtain ⟨n, a, c, h⟩ := TensorProduct.exists_sum_tmul_eq (exists_idem τ).choose
  refine ⟨n, a, c, ?_, ?_⟩
  · rw [idem, h]
    simp [map_sum]
  · have := (exists_idem τ).choose_spec.1
    rw [h] at this
    simpa [map_sum] using this

theorem tmul_mul_idem (τ : K →ₐ[Qp] LL) (c : K) :
    ((1 : LL) ⊗ₜ[Qp] algebraMap K F c) * idem F τ = τ c • idem F τ := by
  have h := congrArg (Algebra.TensorProduct.map (AlgHom.id Qp LL) (IsScalarTower.toAlgHom Qp K F))
    ((exists_idem τ).choose_spec.2 c)
  rw [map_mul, Algebra.smul_def, map_mul] at h
  rw [Algebra.smul_def]
  simpa [idem] using h

variable {F}

theorem mulR_sm_idem (τ : K →ₐ[Qp] LL) (c : K) (x : V ⊗[Qp] F) :
    mulR Qp F LL V (algebraMap K F c) (sm Qp F LL V (idem F τ) x) = τ c • sm Qp F LL V (idem F τ) x := by
  rw [← sm_one_tmul, ← sm_mul, tmul_mul_idem, map_smul, LinearMap.smul_apply]

theorem sm_idem_of_eigen (τ : K →ₐ[Qp] LL) (x : V ⊗[Qp] F)
    (hx : ∀ c : K, mulR Qp F LL V (algebraMap K F c) x = τ c • x) : sm Qp F LL V (idem F τ) x = x := by
  obtain ⟨n, a, c, h, h1⟩ := idem_repr F τ
  rw [h, map_sum, LinearMap.sum_apply]
  simp only [sm_tmul_left, hx, smul_smul, ← Finset.sum_smul, h1, one_smul]

theorem sm_idem_idem (τ : K →ₐ[Qp] LL) (x : V ⊗[Qp] F) :
    sm Qp F LL V (idem F τ) (sm Qp F LL V (idem F τ) x) = sm Qp F LL V (idem F τ) x :=
  sm_idem_of_eigen τ _ fun c => mulR_sm_idem τ c x

theorem idem_mul_idem (τ : K →ₐ[Qp] LL) : idem F τ * idem F τ = idem F τ := by
  have := sm_idem_idem (V := LL) (F := F) τ 1
  simpa only [sm_self, mul_one] using this

theorem idem_ne_zero [Nontrivial F] (τ : K →ₐ[Qp] LL) : idem F τ ≠ 0 := by
  intro h
  have hi : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id Qp LL) (IsScalarTower.toAlgHom Qp K F)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := LL)
      (IsScalarTower.toAlgHom Qp K F).toLinearMap (algebraMap K F).injective
  have h0 : (exists_idem τ).choose = 0 := hi (by rw [map_zero]; exact h)
  have := (exists_idem τ).choose_spec.1
  rw [h0, map_zero] at this
  exact zero_ne_one this

theorem exists_smul_idem (τ : K →ₐ[Qp] LL) (n : ℕ) (a : Fin n → LL) (c : Fin n → K) :
    idem F τ * ∑ i, a i ⊗ₜ[Qp] algebraMap K F (c i) = (∑ i, a i * τ (c i)) • idem F τ := by
  rw [Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : a i ⊗ₜ[Qp] algebraMap K F (c i) = a i • ((1 : LL) ⊗ₜ[Qp] algebraMap K F (c i)) := by
    simp [TensorProduct.smul_tmul']
  rw [this, mul_smul_comm, mul_comm, tmul_mul_idem, smul_smul]

end Idem

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']

theorem fil_antitone : Antitone PD.Fil := antitone_int_of_succ_le PD.Fil_anti

theorem one_notMem_fil_one : (1 : F) ∉ PD.Fil 1 := fun h =>
  PD.not_mem_filtration_two (by simpa using PD.Fil_mul 1 1 _ _ h PD.mem_filtration_one)

include PD in
theorem nontrivial_dR : Nontrivial F :=
  ⟨⟨1, 0, fun h => one_notMem_fil_one PD (h ▸ (PD.Fil 1).zero_mem)⟩⟩

theorem tmul_mem_FilV (v : V) {a : ℤ} {b : F} (hb : b ∈ PD.Fil a) :
    v ⊗ₜ[Qp] b ∈ FilV PD (LL := LL) (V := V) a := ⟨v ⊗ₜ ⟨b, hb⟩, rfl⟩

theorem FilV_induction {a : ℤ} {p : V ⊗[Qp] F → Prop} (h0 : p 0)
    (ht : ∀ v b, b ∈ PD.Fil a → p (v ⊗ₜ[Qp] b)) (ha : ∀ x y, p x → p y → p (x + y))
    {x : V ⊗[Qp] F} (hx : x ∈ FilV PD (LL := LL) (V := V) a) : p x := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simpa using h0
  | tmul v b => exact ht v b b.2
  | add x y hx hy => rw [map_add]; exact ha _ _ hx hy

theorem FilV_antitone : Antitone (FilV PD (LL := LL) (V := V)) := fun a _ hab _ hx =>
  FilV_induction PD (p := fun x => x ∈ FilV PD (LL := LL) (V := V) a) (Submodule.zero_mem _)
    (fun v _ hb => tmul_mem_FilV PD v (fil_antitone PD hab hb)) (fun _ _ => Submodule.add_mem _) hx

theorem exists_mem_FilV (x : V ⊗[Qp] F) : ∃ a, x ∈ FilV PD (LL := LL) (V := V) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v b => exact (PD.Fil_exh b).imp fun a ha => tmul_mem_FilV PD v ha
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (FilV_antitone PD (min_le_left _ _) ha)
      (FilV_antitone PD (min_le_right _ _) hb)⟩

theorem coord_mem_fil {ι : Type} [DecidableEq ι] (b : Basis ι Qp V) {a : ℤ} {x : V ⊗[Qp] F}
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft (N := F) b x i ∈ PD.Fil a := by
  refine FilV_induction PD
    (p := fun x => TensorProduct.equivFinsuppOfBasisLeft (N := F) b x i ∈ PD.Fil a) ?_ ?_ ?_ hx
  · simp
  · intro v c hc
    simpa using ((PD.Fil a).restrictScalars Qp).smul_mem (b.repr v i) hc
  · intro x y hx hy
    simpa only [map_add, Finsupp.add_apply] using Submodule.add_mem _ hx hy

theorem eq_zero_of_forall_mem_FilV (x : V ⊗[Qp] F) (hx : ∀ a, x ∈ FilV PD (LL := LL) (V := V) a) :
    x = 0 := by
  classical
  let b := Basis.ofVectorSpace Qp V
  apply (TensorProduct.equivFinsuppOfBasisLeft (N := F) b).injective
  ext i
  simpa using PD.Fil_sep _ fun a => coord_mem_fil PD b (hx a) i

theorem bil_mem_FilV (β : V →ₗ[LL] V' →ₗ[LL] V'') {a b : ℤ} {x : V ⊗[Qp] F} {y : V' ⊗[Qp] F}
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) (hy : y ∈ FilV PD (LL := LL) (V := V') b) :
    bil Qp F β x y ∈ FilV PD (LL := LL) (V := V'') (a + b) := by
  refine FilV_induction PD (p := fun x => bil Qp F β x y ∈ FilV PD (LL := LL) (V := V'') (a + b))
    (by simp) (fun v c hc => ?_) (fun x x' h h' => ?_) hx
  · refine FilV_induction PD
      (p := fun y => bil Qp F β (v ⊗ₜ[Qp] c) y ∈ FilV PD (LL := LL) (V := V'') (a + b))
      (by simp) (fun w d hd => ?_) (fun x x' h h' => ?_) hy
    · rw [bil_tmul]
      exact tmul_mem_FilV PD _ (PD.Fil_mul _ _ _ _ hc hd)
    · rw [map_add]
      exact Submodule.add_mem _ h h'
  · rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ h h'

theorem sm_mem_FilV {a b : ℤ} {r : LL ⊗[Qp] F} {y : V ⊗[Qp] F}
    (hr : r ∈ FilV PD (LL := LL) (V := LL) a) (hy : y ∈ FilV PD (LL := LL) (V := V) b) :
    sm Qp F LL V r y ∈ FilV PD (LL := LL) (V := V) (a + b) := bil_mem_FilV PD _ hr hy

theorem mul_mem_FilV {a b : ℤ} {r s : LL ⊗[Qp] F}
    (hr : r ∈ FilV PD (LL := LL) (V := LL) a) (hs : s ∈ FilV PD (LL := LL) (V := LL) b) :
    r * s ∈ FilV PD (LL := LL) (V := LL) (a + b) := by
  rw [← sm_self]
  exact sm_mem_FilV PD hr hs

theorem ext_mem_FilV (f : V →ₗ[LL] V') {a : ℤ} {x : V ⊗[Qp] F}
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) : ext Qp F f x ∈ FilV PD (LL := LL) (V := V') a :=
  FilV_induction PD (p := fun x => ext Qp F f x ∈ FilV PD (LL := LL) (V := V') a) (by simp)
    (fun v _ hb => tmul_mem_FilV PD (f v) hb)
    (fun _ _ h h' => by rw [map_add]; exact Submodule.add_mem _ h h') hx

theorem mem_DdR (ρ : Representation LL G V) (x : V ⊗[Qp] F) :
    x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem mem_DdRE (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (x : V ⊗[Qp] F) :
    x ∈ DdRE PD ρ τ ↔ x ∈ DdR PD ρ ∧ ∀ c : K, mulR Qp F LL V (algebraMap K F c) x = τ c • x := by
  simp only [DdRE, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, mulVdR]

@[simp] theorem actVdR_tmul (ρ : Representation LL G V) (g : G) (v : V) (b : F) :
    actVdR PD ρ g (v ⊗ₜ[Qp] b) = ρ g v ⊗ₜ[Qp] PD.actdR g b := by
  simp [actVdR]

theorem act_bil (ρ : Representation LL G V) (ρ' : Representation LL G V') (ρ'' : Representation LL G V'')
    (β : V →ₗ[LL] V' →ₗ[LL] V'') (hβ : ∀ g v w, β (ρ g v) (ρ' g w) = ρ'' g (β v w)) (g : G)
    (x : V ⊗[Qp] F) (y : V' ⊗[Qp] F) :
    actVdR PD ρ'' g (bil Qp F β x y) = bil Qp F β (actVdR PD ρ g x) (actVdR PD ρ' g y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add r s hr hs => simp only [map_add, LinearMap.add_apply, hr, hs]
  | tmul v b' =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add r s hr hs => simp only [map_add, hr, hs]
    | tmul w b'' => simp [hβ]

variable (LL) in

abbrev actR (g : G) : LL ⊗[Qp] F →ₗ[LL] LL ⊗[Qp] F := actVdR PD (Representation.trivial LL G LL) g

theorem act_sm (ρ : Representation LL G V) (g : G) (r : LL ⊗[Qp] F) (x : V ⊗[Qp] F) :
    actVdR PD ρ g (sm Qp F LL V r x) = sm Qp F LL V (actR PD LL g r) (actVdR PD ρ g x) :=
  act_bil PD _ ρ ρ _ (fun g v w => by simp) g r x

theorem actR_mul (g : G) (r s : LL ⊗[Qp] F) :
    actR PD LL g (r * s) = actR PD LL g r * actR PD LL g s := by
  rw [← sm_self, act_sm, sm_self]

theorem act_ext (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (g : G) (x : V ⊗[Qp] F) :
    actVdR PD ρ' g (ext Qp F f x) = ext Qp F f (actVdR PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add r s hr hs => simp only [map_add, hr, hs]
  | tmul v b' => simp [hf]

theorem exists_of_actR_fixed (x : LL ⊗[Qp] F) (hx : ∀ g, actR PD LL g x = x) :
    ∃ (n : ℕ) (a : Fin n → LL) (c : Fin n → K), x = ∑ i, a i ⊗ₜ[Qp] algebraMap K F (c i) := by
  classical
  let b := Module.Basis.ofVectorSpace Qp LL
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := F) b
  have he : ∀ g y i, e (actR PD LL g y) i = PD.actdR g (e y i) := by
    intro g y i
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c =>
      have : ∀ (q : Qp) (z : F), PD.actdR g (q • z) = q • PD.actdR g z := fun q z =>
        ((PD.actdR g).toLinearMap.restrictScalars Qp).map_smul q z
      simp [e, this]
    | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb]
  have hx' : x = (e x).sum fun i c => b i ⊗ₜ[Qp] c := by
    rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
    exact (e.symm_apply_apply x).symm
  choose c hc using fun i => PD.invdR (e x i) fun g => by rw [← he, hx]
  let s := (e x).support
  refine ⟨s.card, fun j => b (s.equivFin.symm j), fun j => c (s.equivFin.symm j), ?_⟩
  conv_lhs => rw [hx']
  rw [Finsupp.sum, ← Finset.sum_coe_sort]
  refine Fintype.sum_equiv s.equivFin _ _ fun i => ?_
  simp [hc]

def Spans (ρ : Representation LL G V) : Prop :=
  ∀ y : V ⊗[Qp] F, ∃ (m : ℕ) (b : Fin m → F) (d : Fin m → V ⊗[Qp] F),
    (∀ i, d i ∈ DdR PD ρ) ∧ y = ∑ i, mulR Qp F LL V (b i) (d i)

def FilSpans (ρ : Representation LL G V) : Prop :=
  ∀ (a : ℤ), ∀ y ∈ FilV PD (LL := LL) (V := V) a,
    ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → F) (d : Fin m → V ⊗[Qp] F),
      (∀ i, d i ∈ DdR PD ρ ∧ d i ∈ FilV PD (LL := LL) (V := V) (k i) ∧ b i ∈ PD.Fil (a - k i)) ∧
        y = ∑ i, mulR Qp F LL V (b i) (d i)

theorem FilSpans.spans {ρ : Representation LL G V} (h : FilSpans PD ρ) : Spans PD ρ := fun y => by
  obtain ⟨a, ha⟩ := exists_mem_FilV PD (LL := LL) y
  obtain ⟨m, k, b, d, h1, h2⟩ := h a y ha
  exact ⟨m, b, d, fun i => (h1 i).1, h2⟩

theorem dual_family (ρ : Representation LL G V) (ρ' : Representation LL G V') (β : V →ₗ[LL] V' →ₗ[LL] LL)
    (hβ : ∀ g x y, β (ρ g x) (ρ' g y) = β x y) {α ι : Type} [Fintype α] [Fintype ι] [DecidableEq α]
    [DecidableEq ι] (v : Basis α LL V) (w : Basis α LL V') (hvw : ∀ a b, β (v a) (w b) = if a = b then 1 else 0)
    (e : LL ⊗[Qp] F) (he : e * e = e) (heG : ∀ g, actR PD LL g e = e) (d : ι → V ⊗[Qp] F)
    (hd : ∀ i, d i ∈ DdR PD ρ) (hed : ∀ i, sm Qp F LL V e (d i) = d i)
    (hind : ∀ r : ι → LL ⊗[Qp] F, ∑ i, sm Qp F LL V (r i) (d i) = 0 → ∀ i, e * r i = 0)
    (r : α → ι → LL ⊗[Qp] F)
    (hr : ∀ a, sm Qp F LL V e (v a ⊗ₜ[Qp] (1 : F)) = ∑ i, sm Qp F LL V (r a i) (d i))
    (d' : ι → V' ⊗[Qp] F)
    (hd' : ∀ i, d' i = sm Qp F LL V' e (∑ a, sm Qp F LL V' (r a i) (w a ⊗ₜ[Qp] (1 : F)))) :
    (∀ i, d' i ∈ DdR PD ρ') ∧ (∀ i j, bil Qp F β (d j) (d' i) = if j = i then e else 0) ∧
      ∀ y, sm Qp F LL V' e y = ∑ i, sm Qp F LL V' (bil Qp F β (d i) y) (d' i) := by
  have hv : ∀ a (x : V ⊗[Qp] F), bil Qp F β x (w a ⊗ₜ[Qp] (1 : F)) = ext Qp F (v.coord a) x := by
    intro a x
    have : ∀ x, β x (w a) = v.coord a x := fun x => by
      have h : β.flip (w a) = v.coord a := v.ext fun b => by
        simp [hvw, Finsupp.single_apply]
      exact LinearMap.congr_fun h x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | tmul x b => simp [this]
  have hw : ∀ a (y : V' ⊗[Qp] F), bil Qp F β (v a ⊗ₜ[Qp] (1 : F)) y = ext Qp F (w.coord a) y := by
    intro a y
    have : ∀ y, β (v a) y = w.coord a y := fun y => by
      have h : β (v a) = w.coord a := w.ext fun b => by
        simp [hvw, Finsupp.single_apply, eq_comm]
      exact LinearMap.congr_fun h y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x b => simp [this]
  have hx : ∀ x, sm Qp F LL V e x = ∑ i, sm Qp F LL V (bil Qp F β x (d' i)) (d i) := by
    intro x
    have h1 : ∀ i, bil Qp F β x (d' i) = e * ∑ a, ext Qp F (v.coord a) x * r a i := by
      intro i
      rw [hd', bil_sm_right, sm_self, map_sum]
      simp only [bil_sm_right, sm_self, hv, mul_comm]
    simp only [h1, sm_mul, map_sum, LinearMap.sum_apply]
    rw [Finset.sum_comm]
    conv_lhs => rw [eq_sum_basis v x, ← he, sm_mul, map_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sm_comm e (ext Qp F (v.coord a) x), hr, map_sum, map_sum]
  have hed' : ∀ i, sm Qp F LL V' e (d' i) = d' i := fun i => by rw [hd', ← sm_mul, he]
  have hδ : ∀ i j, bil Qp F β (d j) (d' i) = if j = i then e else 0 := by
    intro i j
    have h := hind (fun i => bil Qp F β (d j) (d' i) - if j = i then 1 else 0) (by
      simp only [map_sub, LinearMap.sub_apply, Finset.sum_sub_distrib, ← hx, hed]
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp) i
    rw [mul_sub, sub_eq_zero, ← sm_self, ← bil_sm_right, hed'] at h
    rw [h]
    split_ifs <;> simp
  have hz : ∀ z, sm Qp F LL V' e z = z → (∀ j, bil Qp F β (d j) z = 0) → z = 0 := by
    intro z hz h
    have : ∀ a, ext Qp F (w.coord a) z = 0 := by
      intro a
      rw [← hw, ← hz, bil_sm_right, ← bil_sm_left, hr, map_sum, LinearMap.sum_apply]
      simp [bil_sm_left, h]
    rw [eq_sum_basis w z]
    simp [this]
  refine ⟨fun i => (mem_DdR PD ρ' _).2 fun g => ?_, hδ, fun y => ?_⟩
  · rw [← sub_eq_zero]
    refine hz _ ?_ fun j => ?_
    · rw [map_sub, hed', ← heG g, ← act_sm, hed']
    · have h := act_bil PD ρ ρ' (Representation.trivial LL G LL) β (fun g v w => by simp [hβ]) g (d j) (d' i)
      rw [(mem_DdR PD ρ _).1 (hd j)] at h
      rw [map_sub, ← h, hδ]
      split_ifs
      · exact sub_eq_zero.2 (heG g)
      · simp
  · rw [← sub_eq_zero]
    refine hz _ ?_ fun j => ?_
    · rw [map_sub, ← sm_mul, he, map_sum]
      simp only [sm_comm e, hed']
    · rw [map_sub, map_sum]
      simp only [bil_sm_right, hδ, sm_self]
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp [mul_comm]

theorem exists_dual_bases [FiniteDimensional LL V] (β : V →ₗ[LL] V' →ₗ[LL] LL)
    (hβ : Function.Bijective β.flip) : ∃ (v : Basis (Fin (finrank LL V)) LL V)
      (w : Basis (Fin (finrank LL V)) LL V'), ∀ a b, β (v a) (w b) = if a = b then 1 else 0 := by
  let v := Module.finBasis LL V
  let E := LinearEquiv.ofBijective β.flip hβ
  refine ⟨v, v.dualBasis.map E.symm, fun a b => ?_⟩
  have : β.flip (E.symm (v.dualBasis b)) = v.dualBasis b := E.apply_symm_apply _
  have h := LinearMap.congr_fun this (v a)
  rw [LinearMap.flip_apply] at h
  rw [Basis.map_apply, h, Basis.dualBasis_apply_self]

variable [FiniteDimensional Qp K] [CharZero Qp]

theorem idem_mem_FilV (τ : K →ₐ[Qp] LL) : idem F τ ∈ FilV PD (LL := LL) (V := LL) 0 := by
  obtain ⟨n, a, c, h, -⟩ := idem_repr F τ
  rw [h]
  refine Submodule.sum_mem _ fun i _ => tmul_mem_FilV PD _ ?_
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ PD.one_mem

theorem actR_idem (τ : K →ₐ[Qp] LL) (g : G) : actR PD LL g (idem F τ) = idem F τ := by
  obtain ⟨n, a, c, h, -⟩ := idem_repr F τ
  rw [h, map_sum]
  simp

theorem sm_idem_mem_FilV (τ : K →ₐ[Qp] LL) {a : ℤ} {x : V ⊗[Qp] F}
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    sm Qp F LL V (idem F τ) x ∈ FilV PD (LL := LL) (V := V) a := by
  simpa using sm_mem_FilV PD (idem_mem_FilV PD τ) hx

theorem sm_idem_mem_DdRE (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) {x : V ⊗[Qp] F}
    (hx : x ∈ DdR PD ρ) : sm Qp F LL V (idem F τ) x ∈ DdRE PD ρ τ := by
  rw [mem_DdRE, mem_DdR]
  refine ⟨fun g => ?_, fun c => mulR_sm_idem τ c x⟩
  rw [act_sm, actR_idem, (mem_DdR PD ρ x).1 hx]

theorem sm_idem_of_mem_DdRE (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) {x : V ⊗[Qp] F}
    (hx : x ∈ DdRE PD ρ τ) : sm Qp F LL V (idem F τ) x = x :=
  sm_idem_of_eigen τ x ((mem_DdRE PD ρ τ x).1 hx).2

structure Adapted (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) {ι : Type} [Fintype ι]
    (d : ι → V ⊗[Qp] F) (k : ι → ℤ) : Prop where
  mem : ∀ i, d i ∈ FildR PD ρ τ (k i)
  indep : ∀ r : ι → LL ⊗[Qp] F, ∑ i, sm Qp F LL V (r i) (d i) = 0 → ∀ i, idem F τ * r i = 0
  span : ∀ (n : ℤ), ∀ y ∈ FilV PD (LL := LL) (V := V) n, ∃ r : ι → LL ⊗[Qp] F,
    (∀ i, r i ∈ FilV PD (LL := LL) (V := LL) (n - k i)) ∧
      sm Qp F LL V (idem F τ) y = ∑ i, sm Qp F LL V (r i) (d i)

theorem adapted_trivial (τ : K →ₐ[Qp] LL) :
    Adapted PD (Representation.trivial LL G LL) τ (fun _ : Unit => idem F τ) (fun _ => 0) where
  mem _ := by
    refine ⟨?_, idem_mem_FilV PD τ⟩
    have := sm_idem_mem_DdRE PD (Representation.trivial LL G LL) τ (x := 1)
      ((mem_DdR PD _ _).2 fun g => by simp [Algebra.TensorProduct.one_def])
    rwa [sm_self, mul_one] at this
  indep r h i := by
    rw [mul_comm]
    simpa [sm_self] using h
  span n y hy := ⟨fun _ => y, fun _ => by simpa using hy, by simp [sm_self, mul_comm]⟩

end Period

end GlobalTheory.DRFil
