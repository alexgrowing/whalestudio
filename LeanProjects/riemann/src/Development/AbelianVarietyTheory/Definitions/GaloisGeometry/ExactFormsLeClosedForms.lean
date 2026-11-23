import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DifferentiableAtDirD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff

namespace GlobalTheory.CxForm.HolAtlas

variable {M M' M'' : Type} [TopologicalSpace M] [TopologicalSpace M'] [TopologicalSpace M''] {n n' n'' : ℕ}
  (A : HolAtlas M n) (A' : HolAtlas M' n') (A'' : HolAtlas M'' n'')

def closedForms (k : ℕ) : Submodule ℂ A.Fld where
  carrier := {α | A.IsForm α ∧ A.IsDeg k α ∧ A.dExt α = 0}
  add_mem' ha hb := ⟨A.forms.add_mem ha.1 hb.1, fun x => (ha.2.1 x).add (hb.2.1 x),
    by rw [dExt_add ha.1 hb.1, ha.2.2, hb.2.2, add_zero]⟩
  zero_mem' := ⟨A.forms.zero_mem, fun _ => .zero k, A.dExt_zero⟩
  smul_mem' c _ ha := ⟨A.forms.smul_mem ha.1 c, fun x => (ha.2.1 x).smul c, by rw [dExt_smul c ha.1, ha.2.2, smul_zero]⟩

def exactForms (k : ℕ) : Submodule ℂ A.Fld where
  carrier := {α | A.IsDeg k α ∧ ∃ η, A.IsForm η ∧ α = A.dExt η}
  add_mem' ha hb := by
    obtain ⟨h₁, η, hη, rfl⟩ := ha
    obtain ⟨h₂, η', hη', rfl⟩ := hb
    exact ⟨fun x => (h₁ x).add (h₂ x), η + η', A.forms.add_mem hη hη', (dExt_add hη hη').symm⟩
  zero_mem' := ⟨fun _ => .zero k, 0, A.forms.zero_mem, A.dExt_zero.symm⟩
  smul_mem' c _ ha := by
    obtain ⟨h₁, η, hη, rfl⟩ := ha
    exact ⟨fun x => (h₁ x).smul c, c • η, A.forms.smul_mem hη c, (dExt_smul c hη).symm⟩

variable {A}

theorem mem_closedForms {k : ℕ} {α : A.Fld} : α ∈ A.closedForms k ↔ A.IsForm α ∧ A.IsDeg k α ∧ A.dExt α = 0 := Iff.rfl

theorem mem_exactForms {k : ℕ} {α : A.Fld} : α ∈ A.exactForms k ↔ A.IsDeg k α ∧ ∃ η, A.IsForm η ∧ α = A.dExt η := Iff.rfl

theorem mem_exactForms_succ {k : ℕ} {α : A.Fld} :
    α ∈ A.exactForms (k + 1) ↔ ∃ η, A.IsForm η ∧ A.IsDeg k η ∧ α = A.dExt η := by
  constructor
  · rintro ⟨h, η, hη, rfl⟩
    exact ⟨A.degFld k η, hη.degFld k, isDeg_degFld k η, (h.degFld_eq.symm.trans (degFld_dExt hη k).1)⟩
  · rintro ⟨η, hη, hk, rfl⟩
    exact ⟨hk.dExt, η, hη, rfl⟩

variable (A) in

theorem exactForms_zero : A.exactForms 0 = ⊥ := by
  refine eq_bot_iff.2 fun α ⟨h, η, hη, e⟩ => ?_
  rw [Submodule.mem_bot, ← h.degFld_eq, e]
  exact (degFld_dExt hη 0).2

theorem exactForms_le_closedForms (k : ℕ) : A.exactForms k ≤ A.closedForms k := by
  rintro _ ⟨h, η, hη, rfl⟩
  exact ⟨hη.dExt, h, dExt_dExt hη⟩

variable (A) in

def HSm (k : ℕ) : Type := A.closedForms k ⧸ (A.exactForms k).submoduleOf (A.closedForms k)

instance (k : ℕ) : AddCommGroup (A.HSm k) := inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (k : ℕ) : Module ℂ (A.HSm k) := inferInstanceAs (Module ℂ (_ ⧸ _))

namespace HSm

variable (A) in

def mk (k : ℕ) : A.closedForms k →ₗ[ℂ] A.HSm k := Submodule.mkQ _

theorem mk_surjective (k : ℕ) : Function.Surjective (mk A k) := Submodule.mkQ_surjective _

theorem mk_eq_mk {k : ℕ} (α β : A.closedForms k) : mk A k α = mk A k β ↔ (α - β : A.Fld) ∈ A.exactForms k :=
  (Submodule.Quotient.eq _).trans Iff.rfl

theorem mk_eq_zero {k : ℕ} (α : A.closedForms k) : mk A k α = 0 ↔ (α : A.Fld) ∈ A.exactForms k :=
  (Submodule.Quotient.mk_eq_zero _).trans Iff.rfl

@[elab_as_elim] theorem induction_on {k : ℕ} {P : A.HSm k → Prop} (c : A.HSm k) (h : ∀ α, P (mk A k α)) : P c := by
  obtain ⟨α, rfl⟩ := mk_surjective k c
  exact h α

variable (A) in

def fil (p k : ℕ) : Submodule ℂ (A.HSm k) where
  carrier := {c | ∃ α : A.closedForms k, A.TypeGe p α ∧ mk A k α = c}
  add_mem' := by
    rintro _ _ ⟨α, hα, rfl⟩ ⟨β, hβ, rfl⟩
    exact ⟨α + β, typeGe_iff.2 fun x => add_mem (typeGe_iff.1 hα x) (typeGe_iff.1 hβ x), map_add _ _ _⟩
  zero_mem' := ⟨0, typeGe_iff.2 fun _ => zero_mem _, map_zero _⟩
  smul_mem' c := by
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨c • α, typeGe_iff.2 fun x => Submodule.smul_mem _ c (typeGe_iff.1 hα x), map_smul _ _ _⟩

theorem mem_fil {p k : ℕ} {c : A.HSm k} : c ∈ fil A p k ↔ ∃ α : A.closedForms k, A.TypeGe p α ∧ mk A k α = c := Iff.rfl

theorem fil_anti {p q k : ℕ} (h : p ≤ q) : fil A q k ≤ fil A p k := by
  rintro _ ⟨α, hα, rfl⟩
  exact ⟨α, typeGe_iff.2 fun x => holGe_anti h (typeGe_iff.1 hα x), rfl⟩

variable (A) in

theorem fil_zero (k : ℕ) : fil A 0 k = ⊤ :=
  eq_top_iff.2 fun c _ => induction_on c fun α => ⟨α, fun _ _ _ => Nat.zero_le _, rfl⟩

variable (A) in

theorem fil_eq_bot {p : ℕ} (hp : n < p) (k : ℕ) : fil A p k = ⊥ := by
  refine eq_bot_iff.2 ?_
  rintro _ ⟨α, hα, rfl⟩
  rw [Submodule.mem_bot, show α = 0 from Subtype.ext (hα.eq_zero hp), map_zero]

variable (A) in

def mulClosed (k l : ℕ) : A.closedForms k →ₗ[ℂ] A.closedForms l →ₗ[ℂ] A.closedForms (k + l) :=
  LinearMap.mk₂ ℂ (fun α β => ⟨α * β, A.forms.mul_mem α.2.1 β.2.1, α.2.2.1.mul β.2.2.1,
      by rw [dExt_mul α.2.1 β.2.1, α.2.2.2, β.2.2.2, zero_mul, mul_zero, add_zero]⟩)
    (fun _ _ _ => Subtype.ext (add_mul _ _ _)) (fun _ _ _ => Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ => Subtype.ext (mul_add _ _ _)) (fun _ _ _ => Subtype.ext (mul_smul_comm _ _ _))

theorem exact_mul {k l : ℕ} {α β : A.Fld} (hα : α ∈ A.exactForms k) (hβ : β ∈ A.closedForms l) :
    α * β ∈ A.exactForms (k + l) := by
  obtain ⟨h, η, hη, rfl⟩ := hα
  refine ⟨h.mul hβ.2.1, η * β, A.forms.mul_mem hη hβ.1, ?_⟩
  rw [dExt_mul hη hβ.1, hβ.2.2, mul_zero, add_zero]

theorem mul_exact {k l : ℕ} {α β : A.Fld} (hα : α ∈ A.closedForms k) (hβ : β ∈ A.exactForms l) :
    α * β ∈ A.exactForms (k + l) := by
  obtain ⟨h, η, hη, rfl⟩ := hβ
  refine ⟨hα.2.1.mul h, A.parFld α * η, A.forms.mul_mem hα.1.parFld hη, ?_⟩
  rw [dExt_mul hα.1.parFld hη, dExt_parFld hα.1, hα.2.2, map_zero, neg_zero, zero_mul, zero_add]
  exact congrArg (· * _) (funext fun x => (par_par (α x)).symm)

variable (A) in

def cup (k l : ℕ) : A.HSm k →ₗ[ℂ] A.HSm l →ₗ[ℂ] A.HSm (k + l) :=
  LinearMap.liftQ₂ _ _ ((mulClosed A k l).compr₂ (mk A (k + l)))
    (fun α hα => LinearMap.ext fun β => (mk_eq_zero _).2 (exact_mul hα β.2))
    (fun β hβ => LinearMap.ext fun α => (mk_eq_zero _).2 (mul_exact α.2 hβ))

theorem cup_mk {k l : ℕ} (α : A.closedForms k) (β : A.closedForms l) :
    cup A k l (mk A k α) (mk A l β) = mk A (k + l) (mulClosed A k l α β) := rfl

theorem cup_mem_fil {p q k l : ℕ} {c : A.HSm k} {c' : A.HSm l} (hc : c ∈ fil A p k) (hc' : c' ∈ fil A q l) :
    cup A k l c c' ∈ fil A (p + q) (k + l) := by
  obtain ⟨α, hα, rfl⟩ := hc
  obtain ⟨β, hβ, rfl⟩ := hc'
  exact ⟨mulClosed A k l α β, hα.mul hβ, rfl⟩

variable (A) in

def oneClosed : A.closedForms 0 := ⟨1, A.forms.one_mem, fun _ => by simpa using hasDeg_algebraMap (n := n) 1, A.dExt_one⟩

variable (A) in

def one : A.HSm 0 := mk A 0 (oneClosed A)

theorem one_cup {k : ℕ} (c : A.HSm k) : cup A 0 k (one A) c = (Nat.zero_add k).symm ▸ c := by
  induction c using induction_on with
  | h α =>
    have e : ∀ {j : ℕ} (h : k = j), h ▸ mk A k α = mk A j ⟨α, h ▸ α.2⟩ := by rintro _ rfl; rfl
    rw [e, one, cup_mk]
    congr 1
    exact Subtype.ext (one_mul _)

theorem cup_one {k : ℕ} (c : A.HSm k) : cup A k 0 c (one A) = c := by
  induction c using induction_on with
  | h α =>
    rw [one, cup_mk]
    congr 1
    exact Subtype.ext (mul_one _)

theorem mulClosed_comm {k l : ℕ} (α : A.closedForms k) (β : A.closedForms l) :
    (mulClosed A k l α β : A.Fld) = (-1 : ℂ) ^ (k * l) • (mulClosed A l k β α : A.Fld) :=
  α.2.2.1.mul_comm β.2.2.1

variable {A'}

def pullClosed {f : M' → M} (hf : A.IsHolo A' f) (k : ℕ) : A.closedForms k →ₗ[ℂ] A'.closedForms k where
  toFun α := ⟨A.pullback A' f α, α.2.1.pullback hf, α.2.2.1.pullback f,
    by rw [dExt_pullback hf α.2.1, α.2.2.2]; exact map_zero (A.pullbackAlg A' f)⟩
  map_add' α β := Subtype.ext (map_add (A.pullbackAlg A' f) (α : A.Fld) β)
  map_smul' c α := Subtype.ext (map_smul (A.pullbackAlg A' f) c (α : A.Fld))

theorem pullback_exact {f : M' → M} (hf : A.IsHolo A' f) {k : ℕ} {α : A.Fld} (hα : α ∈ A.exactForms k) :
    A.pullback A' f α ∈ A'.exactForms k := by
  obtain ⟨h, η, hη, rfl⟩ := hα
  exact ⟨h.pullback f, A.pullback A' f η, hη.pullback hf, (dExt_pullback hf hη).symm⟩

def pull {f : M' → M} (hf : A.IsHolo A' f) (k : ℕ) : A.HSm k →ₗ[ℂ] A'.HSm k :=
  Submodule.mapQ _ _ (pullClosed hf k) fun α hα => pullback_exact hf hα

theorem pull_mk {f : M' → M} (hf : A.IsHolo A' f) {k : ℕ} (α : A.closedForms k) :
    pull hf k (mk A k α) = mk A' k (pullClosed hf k α) := rfl

theorem pull_id (k : ℕ) : pull (A.isHolo_id) k = LinearMap.id := by
  refine LinearMap.ext fun c => induction_on c fun α => ?_
  rw [pull_mk]
  exact congrArg _ (Subtype.ext (pullback_id α.2.1))

theorem pull_comp {f : M' → M} {g : M'' → M'} (hf : A.IsHolo A' f) (hg : A'.IsHolo A'' g) (k : ℕ) :
    pull (hf.comp hg) k = pull hg k ∘ₗ pull hf k := by
  refine LinearMap.ext fun c => induction_on c fun α => ?_
  rw [LinearMap.comp_apply, pull_mk, pull_mk, pull_mk]
  exact congrArg _ (Subtype.ext (pullback_comp hf hg α))

theorem pull_cup {f : M' → M} (hf : A.IsHolo A' f) {k l : ℕ} (c : A.HSm k) (c' : A.HSm l) :
    pull hf (k + l) (cup A k l c c') = cup A' k l (pull hf k c) (pull hf l c') := by
  induction c using induction_on with
  | h α =>
    induction c' using induction_on with
    | h β =>
      rw [cup_mk, pull_mk, pull_mk, pull_mk, cup_mk]
      exact congrArg _ (Subtype.ext (map_mul (A.pullbackAlg A' f) (α : A.Fld) (β : A.Fld)))

theorem pull_mem_fil {f : M' → M} (hf : A.IsHolo A' f) {p k : ℕ} {c : A.HSm k} (hc : c ∈ fil A p k) :
    pull hf k c ∈ fil A' p k := by
  obtain ⟨α, hα, rfl⟩ := hc
  exact ⟨pullClosed hf k α, hα.pullback f, rfl⟩

end HSm

end GlobalTheory.CxForm.HolAtlas

namespace GlobalTheory.CxForm.HolAtlas

open GlobalTheory.GoodMetric (coordVec)

theorem hasDeg_zero_dim (α : Alt 0) : HasDeg 0 α := fun S _ =>
  Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun a _ => absurd a.2 (by simp))

def pt₀ : (std 0).Pt := ⟨((), 0), Set.mem_univ _⟩

theorem eq_pt₀ (x : (std 0).Pt) : x = pt₀ := Subtype.ext (Prod.ext rfl (Subsingleton.elim _ _))

theorem isForm_std₀ (α : (std 0).Fld) : (std 0).IsForm α := by
  refine ⟨fun i S => contDiffOn_const.congr fun v _ => congrArg (fun w => (bas 0).repr ((std 0).loc α i w) S)
    (Subsingleton.elim v 0), fun x x' _ => ?_⟩
  rw [eq_pt₀ x', eq_pt₀ x, (hasDeg_zero_dim (α pt₀)).eq_algebraMap, AlgHom.commutes]

theorem dExt_std₀ (α : (std 0).Fld) : (std 0).dExt α = 0 :=
  funext fun x => by simp [dExt_apply, opAt]

theorem mem_closedForms_std₀ (α : (std 0).Fld) : α ∈ (std 0).closedForms 0 :=
  ⟨isForm_std₀ α, fun x => hasDeg_zero_dim _, dExt_std₀ α⟩

def evStd₀ : (std 0).closedForms 0 →ₗ[ℂ] ℂ :=
  (bas 0).coord ∅ ∘ₗ LinearMap.proj pt₀ ∘ₗ ((std 0).closedForms 0).subtype

def HSm.std₀Equiv : (std 0).HSm 0 ≃ₗ[ℂ] ℂ := by
  refine LinearEquiv.ofBijective (Submodule.liftQ _ evStd₀ fun α hα => ?_) ⟨?_, fun z => ?_⟩
  · have h : (α : (std 0).Fld) ∈ (std 0).exactForms 0 := hα
    rw [exactForms_zero, Submodule.mem_bot] at h
    simp [evStd₀, h]
  · refine (injective_iff_map_eq_zero _).2 fun c hc => ?_
    induction c using HSm.induction_on with
    | h α =>
      have e : (α : (std 0).Fld) = 0 := funext fun x => by
        rw [eq_pt₀ x, (hasDeg_zero_dim (α.1 pt₀)).eq_algebraMap]
        have : (bas 0).repr (α.1 pt₀) ∅ = 0 := hc
        rw [this, map_zero]; rfl
      rw [show α = 0 from Subtype.ext e]
      exact map_zero _
  · refine ⟨HSm.mk _ 0 ⟨z • 1, mem_closedForms_std₀ _⟩, ?_⟩
    change (bas 0).repr ((z • (1 : (std 0).Fld)) pt₀) ∅ = z
    rw [Pi.smul_apply, Pi.one_apply, ← bas_empty, map_smul, Module.Basis.repr_self]
    simp

theorem HSm.std₀Equiv_one : HSm.std₀Equiv (HSm.one (std 0)) = 1 := by
  change (bas 0).repr ((1 : (std 0).Fld) pt₀) ∅ = 1
  rw [Pi.one_apply, ← bas_empty, Module.Basis.repr_self]
  simp

theorem HSm.finrank_std₀ : Module.finrank ℂ ((std 0).HSm 0) = 1 :=
  (HSm.std₀Equiv.finrank_eq).trans (Module.finrank_self ℂ)

def zFld : (std 1).Fld := fun x => algebraMap ℂ (Alt 1) (x.crd 0)

theorem isForm_zFld : (std 1).IsForm zFld := by
  have hs (x x' : (std 1).Pt) (h : x.pt = x'.pt) : x = x' := Subtype.ext (Prod.ext rfl h)
  refine ⟨fun i S => ?_, fun x x' h => ?_⟩
  · have e : (fun v => (bas 1).repr ((std 1).loc zFld i v) S) = fun v => v 0 * (bas 1).repr 1 S := funext fun v => by
      rw [loc, dif_pos (show v ∈ ((std 1).e i).target from Set.mem_univ v)]
      unfold zFld
      rw [Algebra.algebraMap_eq_smul_one, map_smul, Finsupp.smul_apply, smul_eq_mul]
      rfl
    rw [e]
    exact (((EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ).restrictScalars ℝ).contDiff.mul contDiff_const).contDiffOn
  · rw [← hs x x' h, zFld, AlgHom.commutes]

theorem dExt_zFld (x : (std 1).Pt) : (std 1).dExt zFld x = dz 0 := by
  have hl : (std 1).loc zFld x.1.1 = fun v => (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ) v • bas 1 ∅ := funext fun v => by
    rw [loc, dif_pos (show v ∈ ((std 1).e x.1.1).target from Set.mem_univ v)]
    unfold zFld
    rw [Algebra.algebraMap_eq_smul_one, bas_empty]
    rfl
  have hd : DifferentiableAt ℂ (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ) x.crd :=
    (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ).differentiableAt
  rw [dExt_apply, hl, opAt, opAt, Fin.sum_univ_one, Fin.sum_univ_one,
    coefwise_smul (T := fun f => dirD (Sum.inl 0) f x.crd) (dirD_zero _) (fun v => (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ) v) ∅,
    coefwise_smul (T := fun f => dirD (Sum.inr 0) f x.crd) (dirD_zero _) (fun v => (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ) v) ∅]
  simp only [Fin.sum_univ_one, dirD, del_eq_fderiv hd, dbar_eq_zero hd, ContinuousLinearMap.fderiv, zero_smul,
    ContinuousLinearMap.zero_apply, mul_zero, add_zero, bas_empty, coordVec]
  simp [dz]

theorem dExt_zFld_ne_zero : (std 1).dExt zFld ≠ 0 := fun h => by
  let x₀ : (std 1).Pt := ⟨(((std 1).cover 0).choose, 0), ((std 1).cover 0).choose_spec⟩
  have e : (0 : Alt 1) = dz 0 := by rw [← dExt_zFld x₀, h]; rfl
  rw [dz, ← bas_singleton] at e
  exact (bas 1).ne_zero _ e.symm

end GlobalTheory.CxForm.HolAtlas

namespace GlobalTheory.CxForm

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {k k' : Type} [CommRing k] [CommRing k'] {X Y : Scheme.{0}}

def algAtlas (p : X ⟶ Sp k) (D : ℕ) [SmoothOfRelativeDimension D p] (σ : k →+* ℂ) : HolAtlas (CxPts p σ) D where
  ι := AlgChart p σ D
  e c := c.e
  cover y := AlgChart.exists_mem_source y
  holo c c' := c.holo_trans c'

theorem isHolo_algAtlas {p : X ⟶ Sp k} {D : ℕ} [SmoothOfRelativeDimension D p] {σ : k →+* ℂ} {p' : Y ⟶ Sp k'} {D' : ℕ}
    [SmoothOfRelativeDimension D' p'] {σ' : k' →+* ℂ} {f : Y ⟶ X} {m : CxPts p' σ' → CxPts p σ}
    (hm : ∀ z, (m z).1 = z.1 ≫ f) : (algAtlas p D σ).IsHolo (algAtlas p' D' σ') m :=
  ⟨CxPts.continuous_of_comp hm, fun j i => AlgChart.holo_map hm j i⟩

end GlobalTheory.CxForm

namespace GlobalTheory.CxForm.HolAtlas

example : Module.finrank ℂ ((std 0).HSm 0) = 1 := HSm.finrank_std₀

example : (std 1).dExt zFld ≠ 0 := dExt_zFld_ne_zero

example {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β)
    (h : A.IsDeg 1 α) : A.dExt (α * β) = A.dExt α * β - α * A.dExt β := by
  rw [dExt_mul hα hβ, h.parFld_eq, pow_one, neg_one_smul, neg_mul, sub_eq_add_neg]

example {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (k : ℕ) : HSm.fil A 0 k = ⊤ := HSm.fil_zero A k

end GlobalTheory.CxForm.HolAtlas
