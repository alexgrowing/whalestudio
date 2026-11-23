import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module

namespace GlobalTheory.HeightCounting

section Tensor

variable {Qp LL V B : Type} [Field Qp] [Field LL] [Algebra Qp LL] [AddCommGroup V] [Module LL V] [Module Qp V]
  [IsScalarTower Qp LL V] [AddCommGroup B] [Module Qp B]

def rightCongr (LL V : Type) [Field LL] [Algebra Qp LL] [AddCommGroup V] [Module LL V] [Module Qp V]
    [IsScalarTower Qp LL V] (s : B ≃ₗ[Qp] B) : V ⊗[Qp] B ≃ₗ[LL] V ⊗[Qp] B :=
  AlgebraTensorModule.congr (LinearEquiv.refl LL V) s

@[simp] theorem rightCongr_tmul (s : B ≃ₗ[Qp] B) (v : V) (b : B) :
    rightCongr LL V s (v ⊗ₜ b) = v ⊗ₜ s b := rfl

theorem rightCongr_map (s : B ≃ₗ[Qp] B) (f : V →ₗ[LL] V) (u u' : B →ₗ[Qp] B) (h : ∀ b, s (u b) = u' (s b))
    (x : V ⊗[Qp] B) :
    rightCongr LL V s (AlgebraTensorModule.map f u x) = AlgebraTensorModule.map f u' (rightCongr LL V s x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [h]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem rightCongr_mem_range (s : B ≃ₗ[Qp] B) (F F' : Submodule Qp B) (h : ∀ b ∈ F, s b ∈ F') {x : V ⊗[Qp] B}
    (hx : x ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) F.subtype)) :
    rightCongr LL V s x ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) F'.subtype) := by
  obtain ⟨z, rfl⟩ := hx
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨v ⊗ₜ[Qp] ⟨s b.1, h _ b.2⟩, rfl⟩
  | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy

theorem rightCongr_symm_apply (s : B ≃ₗ[Qp] B) (x : V ⊗[Qp] B) :
    rightCongr LL V s.symm (rightCongr LL V s x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem finrank_eq_of_mem_iff {M : Type} [AddCommGroup M] [Module LL M] (T : M ≃ₗ[LL] M) (S S' : Submodule LL M)
    (h : ∀ x, x ∈ S ↔ T x ∈ S') : finrank LL ↥S = finrank LL ↥S' := by
  have : S.map (T : M →ₗ[LL] M) = S' := by
    ext y
    rw [Submodule.mem_map_equiv, h, T.apply_symm_apply]
  rw [← this, LinearEquiv.finrank_map_eq]

end Tensor

variable {l : ℕ} [Fact l.Prime]

theorem apply_mem_Kur (g : GQ l) {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) : g x ∈ MaximalUnramifiedExtension l := by
  unfold MaximalUnramifiedExtension at hx ⊢
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
    obtain ⟨m, h0, hm, hy⟩ := hy
    exact IntermediateField.subset_adjoin _ _ ⟨m, h0, hm, by rw [← map_pow, hy, map_one]⟩
  | algebraMap y => rw [g.commutes]; exact IntermediateField.algebraMap_mem _ y
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | inv a _ ha => rw [map_inv₀]; exact inv_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

def conjField (g : GQ l) {K₁ K₂ : IntermediateField ℚ_[l] (Om l)} (hK : ∀ x, x ∈ K₁ ↔ g x ∈ K₂) :
    ↥K₁ ≃ₐ[ℚ_[l]] ↥K₂ where
  toFun x := ⟨g x, (hK x).1 x.2⟩
  invFun y := ⟨g.symm y, (hK _).2 (by rw [g.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (g.symm_apply_apply _)
  right_inv y := Subtype.ext (g.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul g _ _)
  map_add' x y := Subtype.ext (map_add g _ _)
  commutes' c := Subtype.ext (g.commutes c)

section Conj

variable (P : LocPrime l) (g : GQ l) {K₁ K₂ : FinExt l} (hK : ∀ x, x ∈ K₁.1 ↔ g x ∈ K₂.1)
include hK

theorem mem_maxUnramifiedSubfield_conj_iff (x : Om l) : x ∈ K0 K₁ ↔ g x ∈ K0 K₂ :=
  ⟨fun h => ⟨(hK x).1 h.1, apply_mem_Kur g h.2⟩, fun h => ⟨(hK x).2 h.1, by
    have := apply_mem_Kur g.symm h.2
    rwa [g.symm_apply_apply] at this⟩⟩

theorem exists_conj_left (σ₁ : ↥(GK K₁)) : ∃ σ₂ : ↥(GK K₂), (σ₂ : GQ l) * g = g * σ₁ := by
  refine ⟨⟨g * σ₁ * g⁻¹, (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => ?_⟩, by simp⟩
  have h1 : g.symm y ∈ K₁.1 := (hK _).2 (by rwa [g.apply_symm_apply])
  change g ((σ₁ : GQ l) (g.symm y)) = y
  rw [(IntermediateField.mem_fixingSubgroup_iff _ _).1 σ₁.2 _ h1, g.apply_symm_apply]

theorem exists_conj_right (σ₂ : ↥(GK K₂)) : ∃ σ₁ : ↥(GK K₁), (σ₂ : GQ l) * g = g * σ₁ := by
  refine ⟨⟨g⁻¹ * σ₂ * g, (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => ?_⟩, by
    simp [mul_assoc]⟩
  change g.symm ((σ₂ : GQ l) (g y)) = y
  rw [(IntermediateField.mem_fixingSubgroup_iff _ _).1 σ₂.2 _ ((hK y).1 hy), g.symm_apply_apply]

variable {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] LL V] {ρ₁ : Representation LL ↥(GK K₁) V} {ρ₂ : Representation LL ↥(GK K₂) V}

omit hK in

theorem actQdR_mem_Fil (K K' : FinExt l) (a : ℤ) {b : P.R.BdR} (hb : b ∈ (P.PD K).Fil a) :
    P.actQdR g b ∈ (P.PD K').Fil a := by
  obtain ⟨K₀, hg⟩ : ∃ K₀ : FinExt l, g ∈ GK K₀ := by
    refine ⟨⟨⊥, inferInstance⟩, ?_⟩
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact g.commutes c
  have h1 : b ∈ (P.PD K₀).Fil a := by
    rw [← SetLike.mem_coe, P.PD_Fil K₀ K]; exact hb
  have h2 := (P.PD K₀).Fil_G ⟨g, hg⟩ a b h1
  rw [P.PD_actdR, ← SetLike.mem_coe, P.PD_Fil K₀ K'] at h2
  exact h2

omit hK in

theorem mem_FilV_iff (K K' : FinExt l) (a : ℤ) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    x ∈ FilV (P.PD K) (LL := LL) (V := V) a ↔
      rightCongr LL V (P.actQdR g).toLinearEquiv x ∈ FilV (P.PD K') (LL := LL) (V := V) a := by
  unfold FilV
  refine ⟨fun h => rightCongr_mem_range (P.actQdR g).toLinearEquiv (((P.PD K).Fil a).restrictScalars ℚ_[l])
    (((P.PD K').Fil a).restrictScalars ℚ_[l]) (fun b hb => actQdR_mem_Fil P g K K' a hb) h, fun h => ?_⟩
  have := rightCongr_mem_range (P.actQdR g).toLinearEquiv.symm (((P.PD K').Fil a).restrictScalars ℚ_[l])
    (((P.PD K).Fil a).restrictScalars ℚ_[l]) (fun b hb => by
      have := actQdR_mem_Fil P g⁻¹ K' K a hb
      rw [map_inv] at this
      exact this) h
  rwa [rightCongr_symm_apply] at this

variable (hρ : ∀ (σ₁ : ↥(GK K₁)) (σ₂ : ↥(GK K₂)), (σ₂ : GQ l) * g = g * σ₁ → ρ₁ σ₁ = ρ₂ σ₂)
include hρ

theorem mem_Dcris_iff (x : V ⊗[ℚ_[l]] P.R.B) :
    x ∈ Dcris (P.PD K₁) ρ₁ ↔ rightCongr LL V (P.actQ g).toLinearEquiv x ∈ Dcris (P.PD K₂) ρ₂ := by
  have key : ∀ (σ₁ : ↥(GK K₁)) (σ₂ : ↥(GK K₂)), (σ₂ : GQ l) * g = g * σ₁ →
      rightCongr LL V (P.actQ g).toLinearEquiv (actVB (P.PD K₁) ρ₁ σ₁ x) =
        actVB (P.PD K₂) ρ₂ σ₂ (rightCongr LL V (P.actQ g).toLinearEquiv x) := fun σ₁ σ₂ h => by
    rw [actVB, actVB, hρ σ₁ σ₂ h]
    refine rightCongr_map _ _ _ _ (fun b => ?_) x
    change P.actQ g ((P.PD K₁).actB σ₁ b) = (P.PD K₂).actB σ₂ (P.actQ g b)
    rw [P.PD_actB, P.PD_actB, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← map_mul, ← map_mul, h]
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  refine ⟨fun h σ₂ => ?_, fun h σ₁ => ?_⟩
  · obtain ⟨σ₁, e⟩ := exists_conj_right g hK σ₂
    rw [← key σ₁ σ₂ e, h]
  · obtain ⟨σ₂, e⟩ := exists_conj_left g hK σ₁
    exact (rightCongr LL V (P.actQ g).toLinearEquiv).injective ((key σ₁ σ₂ e).trans (h σ₂))

theorem mem_DdR_iff (x : V ⊗[ℚ_[l]] P.R.BdR) :
    x ∈ DdR (P.PD K₁) ρ₁ ↔ rightCongr LL V (P.actQdR g).toLinearEquiv x ∈ DdR (P.PD K₂) ρ₂ := by
  have key : ∀ (σ₁ : ↥(GK K₁)) (σ₂ : ↥(GK K₂)), (σ₂ : GQ l) * g = g * σ₁ →
      rightCongr LL V (P.actQdR g).toLinearEquiv (actVdR (P.PD K₁) ρ₁ σ₁ x) =
        actVdR (P.PD K₂) ρ₂ σ₂ (rightCongr LL V (P.actQdR g).toLinearEquiv x) := fun σ₁ σ₂ h => by
    rw [actVdR, actVdR, hρ σ₁ σ₂ h]
    refine rightCongr_map _ _ _ _ (fun b => ?_) x
    change P.actQdR g ((P.PD K₁).actdR σ₁ b) = (P.PD K₂).actdR σ₂ (P.actQdR g b)
    rw [P.PD_actdR, P.PD_actdR, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← map_mul, ← map_mul, h]
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  refine ⟨fun h σ₂ => ?_, fun h σ₁ => ?_⟩
  · obtain ⟨σ₁, e⟩ := exists_conj_right g hK σ₂
    rw [← key σ₁ σ₂ e, h]
  · obtain ⟨σ₂, e⟩ := exists_conj_left g hK σ₁
    exact (rightCongr LL V (P.actQdR g).toLinearEquiv).injective ((key σ₁ σ₂ e).trans (h σ₂))

theorem isCrys_iff : IsCrys (P.PD K₁) ρ₁ ↔ IsCrys (P.PD K₂) ρ₂ := by
  rw [IsCrys, IsCrys, finrank_eq_of_mem_iff _ _ _ (mem_Dcris_iff P g hK hρ),
    (conjField g (mem_maxUnramifiedSubfield_conj_iff g hK)).toLinearEquiv.finrank_eq]

theorem mem_DdRE_iff (τ : ↥K₂.1 →ₐ[ℚ_[l]] LL) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    x ∈ DdRE (P.PD K₁) ρ₁ (τ.comp (conjField g hK).toAlgHom) ↔
      rightCongr LL V (P.actQdR g).toLinearEquiv x ∈ DdRE (P.PD K₂) ρ₂ τ := by
  have key : ∀ c : ↥K₁.1,
      rightCongr LL V (P.actQdR g).toLinearEquiv (mulVdR (K := ↥K₁.1) (LL := LL) c x) =
        mulVdR (K := ↥K₂.1) (LL := LL) (conjField g hK c) (rightCongr LL V (P.actQdR g).toLinearEquiv x) :=
    fun c => by
      refine rightCongr_map _ _ _ _ (fun b => ?_) x
      change P.actQdR g (algebraMap (Om l) P.R.BdR c * b) = algebraMap (Om l) P.R.BdR (g c) * P.actQdR g b
      rw [map_mul, P.actQdR_Om]
  refine and_congr (mem_DdR_iff P g hK hρ x) ?_
  simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smul_apply, sub_eq_zero]
  refine ⟨fun h c => ?_, fun h c => ?_⟩
  · obtain ⟨c, rfl⟩ := (conjField g hK).surjective c
    rw [← key, h, map_smul]
    rfl
  · apply (rightCongr LL V (P.actQdR g).toLinearEquiv).injective
    rw [key, h, map_smul]
    rfl

theorem multV_eq (τ : ↥K₂.1 →ₐ[ℚ_[l]] LL) (a : ℤ) :
    multV (P.PD K₁) ρ₁ (τ.comp (conjField g hK).toAlgHom) a = multV (P.PD K₂) ρ₂ τ a := by
  have h : ∀ a, finrank LL ↥(FildR (P.PD K₁) ρ₁ (τ.comp (conjField g hK).toAlgHom) a) =
      finrank LL ↥(FildR (P.PD K₂) ρ₂ τ a) := fun a =>
    finrank_eq_of_mem_iff (rightCongr LL V (P.actQdR g).toLinearEquiv) _ _ fun x =>
      and_congr (mem_DdRE_iff P g hK hρ τ x) (mem_FilV_iff P g K₁ K₂ a x)
  unfold multV
  rw [h, h]

theorem potCrys_conj (K' : FinExt l) (h : K₁.1 ≤ K'.1)
    (hc : IsCrys (P.PD K') (ρ₁.comp (Subgroup.inclusion (GK_le h)))) :
    ∃ (K'' : FinExt l) (h' : K₂.1 ≤ K''.1), IsCrys (P.PD K'') (ρ₂.comp (Subgroup.inclusion (GK_le h'))) := by
  have := K'.2
  let K'' : FinExt l := ⟨K'.1.map g.toAlgHom,
    (IntermediateField.equivMap K'.1 g.toAlgHom).toLinearEquiv.finiteDimensional⟩
  have hK' : ∀ x, x ∈ K'.1 ↔ g x ∈ K''.1 := fun x =>
    ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, e⟩ => (g.injective e : y = x) ▸ hy⟩
  have h' : K₂.1 ≤ K''.1 := fun y hy => by
    rw [← g.apply_symm_apply y] at hy ⊢
    exact (hK' _).1 (h ((hK _).2 hy))
  exact ⟨K'', h', (isCrys_iff P g hK' fun σ₁ σ₂ e =>
    hρ (Subgroup.inclusion (GK_le h) σ₁) (Subgroup.inclusion (GK_le h') σ₂) e).1 hc⟩

end Conj

section Bridge

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {O₁ O₂ : Type} [CommRing O₁] [Algebra ℤ_[l] O₁] [TopologicalSpace O₁]
  [CommRing O₂] [Algebra ℤ_[l] O₂] [TopologicalSpace O₂]
  (B₁ : LocBridge l E Ω (Dec (F := E) A) O₁) (B₂ : LocBridge l E Ω (Dec (F := E) A) O₂)

omit [NumberField E] in

theorem exists_conj (h₁ : GlobalTheory.Pst.Induces B₁) (h₂ : GlobalTheory.Pst.Induces B₂) :
    ∃ g : GQ l, (∀ x, g (B₁.j x) = B₂.j x) ∧ (∀ x, x ∈ B₁.Kw.1 ↔ g x ∈ B₂.Kw.1) ∧
      ∀ (σ₁ : ↥(GK B₁.Kw)) (σ₂ : ↥(GK B₂.Kw)), (σ₂ : GQ l) * g = g * σ₁ → B₁.e.symm σ₁ = B₂.e.symm σ₂ := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hd := PlaceBridge.denseRange_embedding B₁.j
  obtain ⟨g, hg⟩ := PlaceBridge.exists_algEquiv B₁.j B₂.j hd
    (PlaceBridge.norm_eq_of_le_one_iff _ _ fun x => (h₁ x).symm.trans (h₂ x))
  have he : ∀ σ, (B₂.e σ : GQ l) * g = g * B₁.e σ := fun σ =>
    PlaceBridge.algEquiv_ext hd fun x => by
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hg, B₁.e_comm, B₂.e_comm, hg]
  have hm : ∀ (K : FinExt l) (x : Om l), x ∈ K.1 ↔ ∀ σ : ↥(GK K), (σ : GQ l) x = x := fun K x => by
    rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, IntermediateField.mem_fixedField_iff]
    exact ⟨fun h σ => h σ σ.2, fun h σ hσ => h ⟨σ, hσ⟩⟩
  refine ⟨g, hg, fun x => ?_, fun σ₁ σ₂ e => ?_⟩
  · rw [hm, hm, B₁.e.surjective.forall, B₂.e.surjective.forall]
    refine forall_congr' fun σ => ?_
    rw [← AlgEquiv.mul_apply, he, AlgEquiv.mul_apply, g.injective.eq_iff]
  · obtain ⟨σ, rfl⟩ := B₁.e.surjective σ₁
    rw [← he, mul_left_inj] at e
    rw [Subtype.ext e, B₁.e.symm_apply_apply, B₂.e.symm_apply_apply]

end Bridge

theorem bridge_indep : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (O₁ O₂ : Type) [CommRing O₁] [Algebra ℤ_[l] O₁] [TopologicalSpace O₁] [CommRing O₂] [Algebra ℤ_[l] O₂] [TopologicalSpace O₂] (B₁ : LocBridge l E Ω (Dec (F := E) A) O₁) (B₂ : LocBridge l E Ω (Dec (F := E) A) O₂), GlobalTheory.Pst.Induces B₁ → GlobalTheory.Pst.Induces B₂ → ∀ (L : Loc.FinExt l), B₁.LL.1 ≤ L.1 → ∀ (m : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin m) ↥L.1), (B₁.IsCrysE P L r ↔ B₂.IsCrysE P L r) ∧ (B₁.IsdRE P L r ↔ B₂.IsdRE P L r) ∧ (B₁.IsPotCrysE P L r ↔ B₂.IsPotCrysE P L r) ∧ ∀ (τ : E →+* Loc.Om l) (τ₂ : ↥B₂.Kw.1 →ₐ[ℚ_[l]] ↥L.1), GlobalTheory.Pst.IsInduced B₂ τ τ₂ → ∃ τ₁ : ↥B₁.Kw.1 →ₐ[ℚ_[l]] ↥L.1, GlobalTheory.Pst.IsInduced B₁ τ τ₁ ∧ ∀ a : ℤ, B₁.multE P L r τ₁ a = B₂.multE P L r τ₂ a := by
  intro l _ P E Ω _ _ _ _ _ A O₁ O₂ _ _ _ _ _ _ B₁ B₂ h₁ h₂ L _ m r
  obtain ⟨g, hg, hK, he⟩ := exists_conj B₁ B₂ h₁ h₂
  obtain ⟨g', -, hK', he'⟩ := exists_conj B₂ B₁ h₂ h₁
  have hρ : ∀ (σ₁ : ↥(GK B₁.Kw)) (σ₂ : ↥(GK B₂.Kw)), (σ₂ : GQ l) * g = g * σ₁ →
      B₁.repE L r σ₁ = B₂.repE L r σ₂ := fun σ₁ σ₂ e =>
    congrArg (fun σ => Matrix.toLinAlgEquiv' (r σ : Matrix (Fin m) (Fin m) ↥L.1)) (he σ₁ σ₂ e)
  have hρ' : ∀ (σ₂ : ↥(GK B₂.Kw)) (σ₁ : ↥(GK B₁.Kw)), (σ₁ : GQ l) * g' = g' * σ₂ →
      B₂.repE L r σ₂ = B₁.repE L r σ₁ := fun σ₂ σ₁ e =>
    congrArg (fun σ => Matrix.toLinAlgEquiv' (r σ : Matrix (Fin m) (Fin m) ↥L.1)) (he' σ₂ σ₁ e)
  refine ⟨isCrys_iff P g hK hρ, ?_, ⟨fun ⟨K', h, hc⟩ => potCrys_conj P g hK hρ K' h hc,
    fun ⟨K', h, hc⟩ => potCrys_conj P g' hK' hρ' K' h hc⟩, fun τ τ₂ hτ =>
      ⟨τ₂.comp (conjField g hK).toAlgHom, fun x => ?_, multV_eq P g hK hρ τ₂⟩⟩
  · rw [LocBridge.IsdRE, LocBridge.IsdRE, finrank_eq_of_mem_iff _ _ _ (mem_DdR_iff P g hK hρ),
      (conjField g hK).toLinearEquiv.finrank_eq]
  · rw [hτ x]
    exact congrArg (fun y => ((τ₂ y : ↥L.1) : Om l)) (Subtype.ext (hg _).symm)

end GlobalTheory.HeightCounting
