import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatTw
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMap

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.NodeSep

section Lin

variable {A Y X : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup X] [Module ℂ X]

theorem mem_range_of_ker {ι : Type} (f : ι → A →ₗ[ℂ] X) (x : A ⊗[ℂ] Y)
    (h : ∀ j, TensorProduct.map (f j) (LinearMap.id : Y →ₗ[ℂ] Y) x = 0) :
    x ∈ LinearMap.range (TensorProduct.map (⨅ j, LinearMap.ker (f j)).subtype (LinearMap.id : Y →ₗ[ℂ] Y)) := by
  let B := Module.Basis.ofVectorSpace ℂ Y
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right B x
  have hc : ∀ i, c i ∈ ⨅ j, LinearMap.ker (f j) := by
    intro i
    refine Submodule.mem_iInf _ |>.2 fun j => ?_
    have e : (c.mapRange (f j) (map_zero _)).sum (fun i m => m ⊗ₜ[ℂ] B i) = 0 := by
      rw [Finsupp.sum_mapRange_index (by simp)]
      simpa [Finsupp.sum, map_sum] using h j
    have := TensorProduct.sum_tmul_basis_right_eq_zero B _ e
    simpa using DFunLike.congr_fun this i
  refine Submodule.sum_mem _ fun i _ => ⟨(⟨c i, hc i⟩ : (⨅ j, LinearMap.ker (f j) : Submodule ℂ A)) ⊗ₜ[ℂ] B i, ?_⟩
  simp [TensorProduct.map_tmul]

theorem map_comm' {P Q M N : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (f : M →ₗ[ℂ] P) (g : N →ₗ[ℂ] Q) (x : N ⊗[ℂ] M) :
    TensorProduct.map f g (TensorProduct.comm ℂ N M x) = TensorProduct.comm ℂ Q P (TensorProduct.map g f x) := by
  have : TensorProduct.map f g ∘ₗ (TensorProduct.comm ℂ N M).toLinearMap =
      (TensorProduct.comm ℂ Q P).toLinearMap ∘ₗ TensorProduct.map g f := by
    ext a b
    simp
  exact LinearMap.congr_fun this x

theorem mem_range_of_ker' {ι : Type} (f : ι → A →ₗ[ℂ] X) (x : Y ⊗[ℂ] A)
    (h : ∀ j, TensorProduct.map (LinearMap.id : Y →ₗ[ℂ] Y) (f j) x = 0) :
    x ∈ LinearMap.range (TensorProduct.map (LinearMap.id : Y →ₗ[ℂ] Y) (⨅ j, LinearMap.ker (f j)).subtype) := by
  have h' : ∀ j, TensorProduct.map (f j) (LinearMap.id : Y →ₗ[ℂ] Y) (TensorProduct.comm ℂ Y A x) = 0 := fun j => by
    rw [map_comm', h j, map_zero]
  obtain ⟨z, hz⟩ := mem_range_of_ker f _ h'
  refine ⟨TensorProduct.comm ℂ _ _ z, ?_⟩
  rw [map_comm', hz, ← TensorProduct.comm_symm]
  exact LinearEquiv.symm_apply_apply _ _

theorem map_bot_left (K : Submodule ℂ A) (h : K = ⊥) (u : K ⊗[ℂ] Y) :
    TensorProduct.map K.subtype (LinearMap.id : Y →ₗ[ℂ] Y) u = 0 := by
  subst h
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    have : a = 0 := Subtype.ext ((Submodule.mem_bot ℂ).1 a.2)
    simp [this]
  | add a b ha hb => simp [ha, hb]

theorem map_bot_right (K : Submodule ℂ A) (h : K = ⊥) (u : Y ⊗[ℂ] K) :
    TensorProduct.map (LinearMap.id : Y →ₗ[ℂ] Y) K.subtype u = 0 := by
  subst h
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    have : b = 0 := Subtype.ext ((Submodule.mem_bot ℂ).1 b.2)
    simp [this]
  | add a b ha hb => simp [ha, hb]

variable {G₁ G₂ A₁ A₂ X₁ X₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁] [TopologicalSpace G₂]
  [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂] [AddCommGroup X₁] [Module ℂ X₁]
  [AddCommGroup X₂] [Module ℂ X₂]

theorem extTensor_left (σ₁ : Representation ℂ G₁ A₁) (σ₂ : Representation ℂ G₂ A₂) (u : G₁) :
    GlobalTheory.SmGL.extTensor σ₁ σ₂ (u, 1) = TensorProduct.map (σ₁ u) LinearMap.id := by
  ext a b
  simp

theorem extTensor_right (σ₁ : Representation ℂ G₁ A₁) (σ₂ : Representation ℂ G₂ A₂) (u : G₂) :
    GlobalTheory.SmGL.extTensor σ₁ σ₂ (1, u) = TensorProduct.map LinearMap.id (σ₂ u) := by
  ext a b
  simp

theorem tens_smooth (σ₁ : Representation ℂ G₁ A₁) (σ₂ : Representation ℂ G₂ A₂) {x : A₁ ⊗[ℂ] A₂}
    (hx : SmVec (GlobalTheory.SmGL.extTensor σ₁ σ₂) x) :
    ∃ (K₁ : Submodule ℂ A₁) (K₂ : Submodule ℂ A₂), (∀ a ∈ K₁, SmVec σ₁ a) ∧ (∀ b ∈ K₂, SmVec σ₂ b) ∧
      x ∈ LinearMap.range (TensorProduct.map K₁.subtype K₂.subtype) := by
  obtain ⟨W, hW, hxW⟩ := hx
  have hf : ∀ u ∈ W, GlobalTheory.SmGL.extTensor σ₁ σ₂ u x = x := fun u hu => GlobalTheory.LGrp.mem_fixed.1 hxW u hu
  let U₁ : Subgroup G₁ := W.comap (MonoidHom.inl G₁ G₂)
  let U₂ : Subgroup G₂ := W.comap (MonoidHom.inr G₁ G₂)
  have hU₁ : IsOpen (U₁ : Set G₁) := hW.preimage (continuous_id.prodMk continuous_const)
  have hU₂ : IsOpen (U₂ : Set G₂) := hW.preimage (continuous_const.prodMk continuous_id)
  let f₁ : U₁ → A₁ →ₗ[ℂ] A₁ := fun u => σ₁ u.1 - LinearMap.id
  let f₂ : U₂ → A₂ →ₗ[ℂ] A₂ := fun u => σ₂ u.1 - LinearMap.id
  let K₁ := ⨅ j, LinearMap.ker (f₁ j)
  let K₂ := ⨅ j, LinearMap.ker (f₂ j)
  have m₁ : ∀ a ∈ K₁, SmVec σ₁ a := fun a ha => ⟨U₁, hU₁, GlobalTheory.LGrp.mem_fixed.2 fun u hu => by
    have := (Submodule.mem_iInf _).1 ha ⟨u, hu⟩
    simpa [f₁, sub_eq_zero] using this⟩
  have m₂ : ∀ a ∈ K₂, SmVec σ₂ a := fun a ha => ⟨U₂, hU₂, GlobalTheory.LGrp.mem_fixed.2 fun u hu => by
    have := (Submodule.mem_iInf _).1 ha ⟨u, hu⟩
    simpa [f₂, sub_eq_zero] using this⟩
  refine ⟨K₁, K₂, m₁, m₂, ?_⟩
  obtain ⟨x₁, rfl⟩ := mem_range_of_ker (Y := A₂) f₁ x fun j => by
    have h1 := hf (j.1, 1) j.2
    rw [extTensor_left] at h1
    have e : TensorProduct.map (f₁ j) (LinearMap.id : A₂ →ₗ[ℂ] A₂) = TensorProduct.map (σ₁ j.1) LinearMap.id - LinearMap.id := by
      ext a b
      simp [f₁, TensorProduct.sub_tmul]
    rw [e, LinearMap.sub_apply, h1, LinearMap.id_apply, sub_self]
  have hinj : Function.Injective (TensorProduct.map K₁.subtype (LinearMap.id : A₂ →ₗ[ℂ] A₂)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ K₁.injective_subtype
  obtain ⟨x₂, rfl⟩ := mem_range_of_ker' (Y := K₁) f₂ x₁ fun j => by
    apply hinj
    have h1 := hf (1, j.1) j.2
    rw [extTensor_right] at h1
    rw [map_zero, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
    simp only [f₂, LinearMap.comp_id, LinearMap.id_comp]
    have e : TensorProduct.map K₁.subtype (σ₂ j.1 - LinearMap.id) =
        (TensorProduct.map LinearMap.id (σ₂ j.1) - LinearMap.id) ∘ₗ TensorProduct.map K₁.subtype (LinearMap.id : A₂ →ₗ[ℂ] A₂) := by
      ext a b
      simp [TensorProduct.tmul_sub]
    rw [e, LinearMap.comp_apply, LinearMap.sub_apply, h1, LinearMap.id_apply, sub_self]
  refine ⟨x₂, ?_⟩
  have e : TensorProduct.map K₁.subtype K₂.subtype =
      TensorProduct.map K₁.subtype (LinearMap.id : A₂ →ₗ[ℂ] A₂) ∘ₗ TensorProduct.map (LinearMap.id : K₁ →ₗ[ℂ] K₁) K₂.subtype := by
    ext a b
    simp
  exact LinearMap.congr_fun e x₂

theorem tens_equiv (σ₁ : Representation ℂ G₁ A₁) (σ₂ : Representation ℂ G₂ A₂) (τ₁ : Representation ℂ G₁ X₁)
    (τ₂ : Representation ℂ G₂ X₂) (L₁ : A₁ →ₗ[ℂ] X₁) (L₂ : A₂ →ₗ[ℂ] X₂)
    (h₁ : ∀ g a, SmVec σ₁ a → L₁ (σ₁ g a) = τ₁ g (L₁ a)) (h₂ : ∀ g a, SmVec σ₂ a → L₂ (σ₂ g a) = τ₂ g (L₂ a))
    {x : A₁ ⊗[ℂ] A₂} (hx : SmVec (GlobalTheory.SmGL.extTensor σ₁ σ₂) x) (g : G₁ × G₂) :
    TensorProduct.map L₁ L₂ (GlobalTheory.SmGL.extTensor σ₁ σ₂ g x) = GlobalTheory.SmGL.extTensor τ₁ τ₂ g (TensorProduct.map L₁ L₂ x) := by
  obtain ⟨K₁, K₂, m₁, m₂, z, rfl⟩ := tens_smooth σ₁ σ₂ hx
  clear hx
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [h₁ _ _ (m₁ a.1 a.2), h₂ _ _ (m₂ b.1 b.2)]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem tens_joint {J₁ J₂ : Type} (f : J₁ → A₁ →ₗ[ℂ] X₁) (g : J₂ → A₂ →ₗ[ℂ] X₂)
    (bf : (⨅ j, LinearMap.ker (f j)) = ⊥) (bg : (⨅ j, LinearMap.ker (g j)) = ⊥) (z : A₁ ⊗[ℂ] A₂)
    (h0 : ∀ j₁ j₂, TensorProduct.map (f j₁) (g j₂) z = 0) : z = 0 := by
  have hz : ∀ j₂, TensorProduct.map (LinearMap.id : A₁ →ₗ[ℂ] A₁) (g j₂) z = 0 := fun j₂ => by
    obtain ⟨u, hu⟩ := mem_range_of_ker (Y := X₂) f (TensorProduct.map (LinearMap.id : A₁ →ₗ[ℂ] A₁) (g j₂) z) fun j₁ => by
      have := h0 j₁ j₂
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
      simpa using this
    rw [← hu]
    exact map_bot_left _ bf u
  obtain ⟨u, hu⟩ := mem_range_of_ker' (Y := A₁) g z hz
  rw [← hu]
  exact map_bot_right _ bg u

theorem tens_sep (σ₁ : Representation ℂ G₁ A₁) (σ₂ : Representation ℂ G₂ A₂) {J₁ J₂ : Type}
    (L₁ : J₁ → A₁ →ₗ[ℂ] X₁) (L₂ : J₂ → A₂ →ₗ[ℂ] X₂)
    (h₁ : ∀ a, SmVec σ₁ a → (∀ j, L₁ j a = 0) → a = 0) (h₂ : ∀ a, SmVec σ₂ a → (∀ j, L₂ j a = 0) → a = 0)
    {x : A₁ ⊗[ℂ] A₂} (hx : SmVec (GlobalTheory.SmGL.extTensor σ₁ σ₂) x)
    (h0 : ∀ j₁ j₂, TensorProduct.map (L₁ j₁) (L₂ j₂) x = 0) : x = 0 := by
  obtain ⟨K₁, K₂, m₁, m₂, z, rfl⟩ := tens_smooth σ₁ σ₂ hx
  have bf : (⨅ j, LinearMap.ker (L₁ j ∘ₗ K₁.subtype)) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun a ha => ?_
    have := h₁ a.1 (m₁ a.1 a.2) fun j => (Submodule.mem_iInf _).1 ha j
    exact Subtype.ext this
  have bg : (⨅ j, LinearMap.ker (L₂ j ∘ₗ K₂.subtype)) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun a ha => ?_
    have := h₂ a.1 (m₂ a.1 a.2) fun j => (Submodule.mem_iInf _).1 ha j
    exact Subtype.ext this
  rw [tens_joint _ _ bf bg z fun j₁ j₂ => by
    have := h0 j₁ j₂
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp] at this
    exact this, map_zero]

end Lin

section Fn

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

def prodFn (S₁ : Submodule ℂ (Sm E r)) (S₂ : Submodule ℂ (Sm E s)) : S₁ ⊗[ℂ] S₂ →ₗ[ℂ] (GA E r × GA E s → ℂ) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun a b m => a.1.1 m.1 * b.1.1 m.2)
    (fun a a' b => by funext m; simp [add_mul])
    (fun c a b => by funext m; simp [mul_assoc])
    (fun a b b' => by funext m; simp [mul_add])
    (fun c a b => by funext m; simp; ring))

theorem prodFn_tmul (S₁ : Submodule ℂ (Sm E r)) (S₂ : Submodule ℂ (Sm E s)) (a : S₁) (b : S₂) (m : GA E r × GA E s) :
    prodFn S₁ S₂ (a ⊗ₜ[ℂ] b) m = a.1.1 m.1 * b.1.1 m.2 := rfl

def evAt (S : Submodule ℂ (Sm E r)) (a : GA E r) : S →ₗ[ℂ] ℂ where
  toFun φ := φ.1.1 a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem iInf_ker_evAt (S : Submodule ℂ (Sm E r)) : (⨅ a, LinearMap.ker (evAt S a)) = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun φ hφ => Subtype.ext (Subtype.ext (funext fun a => ?_))
  exact (Submodule.mem_iInf _).1 hφ a

theorem lid_map_evAt (S₁ : Submodule ℂ (Sm E r)) (S₂ : Submodule ℂ (Sm E s)) (a : GA E r) (b : GA E s) (x : S₁ ⊗[ℂ] S₂) :
    TensorProduct.lid ℂ ℂ (TensorProduct.map (evAt S₁ a) (evAt S₂ b) x) = prodFn S₁ S₂ x (a, b) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp [prodFn_tmul, evAt]
  | add u v hu hv => simp only [map_add, hu, hv, Pi.add_apply]

theorem prodFn_injective (S₁ : Submodule ℂ (Sm E r)) (S₂ : Submodule ℂ (Sm E s)) :
    Function.Injective (prodFn S₁ S₂) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  refine tens_joint _ _ (iInf_ker_evAt S₁) (iInf_ker_evAt S₂) x fun a b => ?_
  apply (TensorProduct.lid ℂ ℂ).injective
  rw [lid_map_evAt, hx, map_zero]
  rfl

def prodInv (S₁ : Submodule ℂ (Sm E r)) (S₂ : Submodule ℂ (Sm E s)) : (GA E r × GA E s → ℂ) →ₗ[ℂ] S₁ ⊗[ℂ] S₂ :=
  (LinearMap.exists_leftInverse_of_injective (prodFn S₁ S₂) (LinearMap.ker_eq_bot.2 (prodFn_injective S₁ S₂))).choose

theorem prodInv_prodFn (S₁ : Submodule ℂ (Sm E r)) (S₂ : Submodule ℂ (Sm E s)) (x : S₁ ⊗[ℂ] S₂) :
    prodInv S₁ S₂ (prodFn S₁ S₂ x) = x :=
  LinearMap.congr_fun (LinearMap.exists_leftInverse_of_injective (prodFn S₁ S₂)
    (LinearMap.ker_eq_bot.2 (prodFn_injective S₁ S₂))).choose_spec x

theorem prodFn_prodInv {S₁ : Submodule ℂ (Sm E r)} {S₂ : Submodule ℂ (Sm E s)} {F : GA E r × GA E s → ℂ}
    (hF : F ∈ tens2 S₁ S₂) : prodFn S₁ S₂ (prodInv S₁ S₂ F) = F := by
  obtain ⟨n, ψ₁, ψ₂, h₁, h₂, rfl⟩ := tensor_pair_finite_sum hF
  have : (fun m : GA E r × GA E s => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) =
      prodFn S₁ S₂ (∑ i, (⟨ψ₁ i, h₁ i⟩ : S₁) ⊗ₜ[ℂ] (⟨ψ₂ i, h₂ i⟩ : S₂)) := by
    funext m
    simp [map_sum, Finset.sum_apply, prodFn_tmul]
  rw [this, prodInv_prodFn]

def cc (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) : GA E r × GA E s →* ℂˣ :=
  ((chiDet r (Model.absC E ((s : ℂ) / 2))).comp (MonoidHom.fst _ _)) *
    ((chiDet s (Model.absC E (-(r : ℂ) / 2))).comp (MonoidHom.snd _ _))

def sl (k : Kinf E (r + s)) (y : GL (Fin (r + s)) (Af E)) : Sm E (r + s) →ₗ[ℂ] (GA E r × GA E s → ℂ) where
  toFun φ m := (((cc E r s m)⁻¹ : ℂˣ) : ℂ) * φ.1 (lev (Ad E) r s m * cf (r + s) k y)
  map_add' φ ψ := by funext m; simp [mul_add]
  map_smul' c φ := by funext m; simp; ring

theorem sl_apply (k : Kinf E (r + s)) (y : GL (Fin (r + s)) (Af E)) (φ : Sm E (r + s)) (m : GA E r × GA E s) :
    sl k y φ m = (((cc E r s m)⁻¹ : ℂˣ) : ℂ) * φ.1 (lev (Ad E) r s m * cf (r + s) k y) := rfl

def lw (w : HeightOneSpectrum (𝓞 E)) : GLw r w × GLw s w →* GA E r × GA E s :=
  (embW r w).prodMap (embW s w)

theorem sl_fin (k : Kinf E (r + s)) (y h : GL (Fin (r + s)) (Af E)) (φ : Sm E (r + s)) :
    sl k y (finRep E (r + s) h φ) = sl k (y * h) φ := by
  funext m
  simp only [sl_apply]
  congr 1
  change φ.1 (lev (Ad E) r s m * cf (r + s) k y * finGL E (r + s) h) = _
  rw [cf, cf, map_mul]
  simp only [mul_assoc]

theorem prodFn_rt (w : HeightOneSpectrum (𝓞 E)) {S₁ : Submodule ℂ (Sm E r)} {S₂ : Submodule ℂ (Sm E s)}
    (h₁ : ∀ g, ∀ x ∈ S₁, ((finRep E r).comp (locGL E r w)) g x ∈ S₁)
    (h₂ : ∀ g, ∀ x ∈ S₂, ((finRep E s).comp (locGL E s w)) g x ∈ S₂) (g : GLw r w × GLw s w) (x : S₁ ⊗[ℂ] S₂)
    (m : GA E r × GA E s) :
    prodFn S₁ S₂ (GlobalTheory.SmGL.extTensor (GlobalTheory.PRep.sub _ S₁ h₁) (GlobalTheory.PRep.sub _ S₂ h₂) g x) m = prodFn S₁ S₂ x (m * lw w g) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

end Fn

end GlobalTheory.CompanionTheory.NodeSep
