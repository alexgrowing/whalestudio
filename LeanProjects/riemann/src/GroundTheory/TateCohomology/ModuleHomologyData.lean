import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits

universe u

section ModuleHomologyData

variable {R : Type u} [CommRing R]

noncomputable def moduleKernelIsLimit (S : ShortComplex (ModuleCat.{u} R))
    (K : Type u) [AddCommGroup K] [Module R K] (ι : K →ₗ[R] S.X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker S.g.hom) (wi : ModuleCat.ofHom ι ≫ S.g = 0) :
    IsLimit (KernelFork.ofι (ModuleCat.ofHom ι) wi) :=
  KernelFork.IsLimit.ofι _ _
    (fun {A} k hk => ModuleCat.ofHom ((LinearEquiv.ofInjective ι hι).symm.toLinearMap ∘ₗ
      k.hom.codRestrict (LinearMap.range ι) (fun a => by
        rw [hrange, LinearMap.mem_ker]
        exact congr($hk a))))
    (fun {A} k hk => by
      ext a
      simp)
    (fun {A} k hk m hm => by
      ext a
      apply hι
      simp [← hm])

noncomputable def moduleLeftHomologyData (S : ShortComplex (ModuleCat.{u} R))
    (K : Type u) [AddCommGroup K] [Module R K] (ι : K →ₗ[R] S.X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker S.g.hom) (N : Submodule R K)
    (hN : ∀ x, x ∈ N ↔ ι x ∈ LinearMap.range S.f.hom) : S.LeftHomologyData :=
  have wi : ModuleCat.ofHom ι ≫ S.g = 0 := by
    ext x
    have : ι x ∈ LinearMap.ker S.g.hom := hrange ▸ LinearMap.mem_range_self ι x
    simpa using LinearMap.mem_ker.1 this
  have hi := moduleKernelIsLimit S K ι hι hrange wi
  have hlift : ∀ c, ι ((hi.lift (KernelFork.ofι S.f S.zero)).hom c) = S.f.hom c := fun c =>
    congr($(Fork.IsLimit.lift_ι hi) c)
  have wπ : hi.lift (KernelFork.ofι S.f S.zero) ≫ ModuleCat.ofHom N.mkQ = 0 := by
    ext c
    simp [Submodule.Quotient.mk_eq_zero, hN, hlift]
  { K := ModuleCat.of R K
    H := ModuleCat.of R (K ⧸ N)
    i := ModuleCat.ofHom ι
    wi := wi
    hi := hi
    π := ModuleCat.ofHom N.mkQ
    wπ := wπ
    hπ := CokernelCofork.IsColimit.ofπ _ _
      (fun {A} k hk => ModuleCat.ofHom (N.liftQ k.hom (fun x hx => by
        obtain ⟨c, hc⟩ := (hN x).1 hx
        have : (hi.lift (KernelFork.ofι S.f S.zero)).hom c = x := hι (by rw [hlift, hc])
        rw [LinearMap.mem_ker, ← this]
        exact congr($hk c))))
      (fun {A} k hk => by
        ext x
        simp)
      (fun {A} k hk m hm => by
        ext x
        simp [← hm]) }

variable (S : ShortComplex (ModuleCat.{u} R))
    (K : Type u) [AddCommGroup K] [Module R K] (ι : K →ₗ[R] S.X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker S.g.hom) (N : Submodule R K)
    (hN : ∀ x, x ∈ N ↔ ι x ∈ LinearMap.range S.f.hom)

@[simp]
lemma moduleLeftHomologyData_i_hom :
    (moduleLeftHomologyData S K ι hι hrange N hN).i.hom = ι := rfl

@[simp]
lemma moduleLeftHomologyData_π_hom :
    (moduleLeftHomologyData S K ι hι hrange N hN).π.hom = N.mkQ := rfl

lemma moduleLeftHomologyData_homologyIso_hom_homologyπ [S.HasHomology]
    (z : S.cycles) (x : K) (hx : ι x = S.iCycles.hom z) :
    (moduleLeftHomologyData S K ι hι hrange N hN).homologyIso.hom.hom (S.homologyπ.hom z) =
      Submodule.Quotient.mk x := by
  set h := moduleLeftHomologyData S K ι hι hrange N hN
  have h1 : (S.homologyπ ≫ h.homologyIso.hom).hom z = (h.cyclesIso.hom ≫ h.π).hom z := by
    rw [h.homologyπ_comp_homologyIso_hom]
  have h2 : (h.cyclesIso.hom ≫ h.i).hom z = S.iCycles.hom z := by
    rw [h.cyclesIso_hom_comp_i]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [h1]
  have : h.cyclesIso.hom.hom z = x := hι (by rw [hx, ← h2]; rfl)
  rw [this]
  rfl

variable {S₁ S₂ : ShortComplex (ModuleCat.{u} R)} (φ : S₁ ⟶ S₂)
    (K₁ : Type u) [AddCommGroup K₁] [Module R K₁] (ι₁ : K₁ →ₗ[R] S₁.X₂)
    (hι₁ : Function.Injective ι₁) (hrange₁ : LinearMap.range ι₁ = LinearMap.ker S₁.g.hom)
    (N₁ : Submodule R K₁) (hN₁ : ∀ x, x ∈ N₁ ↔ ι₁ x ∈ LinearMap.range S₁.f.hom)
    (K₂ : Type u) [AddCommGroup K₂] [Module R K₂] (ι₂ : K₂ →ₗ[R] S₂.X₂)
    (hι₂ : Function.Injective ι₂) (hrange₂ : LinearMap.range ι₂ = LinearMap.ker S₂.g.hom)
    (N₂ : Submodule R K₂) (hN₂ : ∀ x, x ∈ N₂ ↔ ι₂ x ∈ LinearMap.range S₂.f.hom)

noncomputable def moduleLeftHomologyMapData (φK : K₁ →ₗ[R] K₂)
    (hφK : ∀ x, ι₂ (φK x) = φ.τ₂.hom (ι₁ x)) (hφN : N₁ ≤ N₂.comap φK) :
    ShortComplex.LeftHomologyMapData φ (moduleLeftHomologyData S₁ K₁ ι₁ hι₁ hrange₁ N₁ hN₁)
      (moduleLeftHomologyData S₂ K₂ ι₂ hι₂ hrange₂ N₂ hN₂) where
  φK := ModuleCat.ofHom φK
  φH := ModuleCat.ofHom (N₁.mapQ N₂ φK hφN)
  commi := by
    ext x
    exact hφK x
  commf' := by
    ext c
    apply hι₂
    have e₁ : ι₁ ((moduleLeftHomologyData S₁ K₁ ι₁ hι₁ hrange₁ N₁ hN₁).f'.hom c) = S₁.f.hom c :=
      congr($((moduleLeftHomologyData S₁ K₁ ι₁ hι₁ hrange₁ N₁ hN₁).f'_i).hom c)
    have e₂ : ι₂ ((moduleLeftHomologyData S₂ K₂ ι₂ hι₂ hrange₂ N₂ hN₂).f'.hom (φ.τ₁.hom c)) =
        S₂.f.hom (φ.τ₁.hom c) :=
      congr($((moduleLeftHomologyData S₂ K₂ ι₂ hι₂ hrange₂ N₂ hN₂).f'_i).hom (φ.τ₁.hom c))
    have e₃ : S₂.f.hom (φ.τ₁.hom c) = φ.τ₂.hom (S₁.f.hom c) := congr($(φ.comm₁₂).hom c)
    exact (hφK _).trans ((congrArg φ.τ₂.hom e₁).trans (e₃.symm.trans e₂.symm))
  commπ := by
    ext x
    rfl

end ModuleHomologyData
section Complexes

variable {R : Type u} [CommRing R]

lemma homologyFunctorIso'_moduleLeftHomologyData_apply {ιc : Type*} {c : ComplexShape ιc}
    (C : HomologicalComplex (ModuleCat.{u} R) c) (i j k : ιc) (hi : c.prev j = i)
    (hk : c.next j = k) (K : Type u) [AddCommGroup K] [Module R K]
    (ι : K →ₗ[R] (C.sc' i j k).X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker (C.sc' i j k).g.hom) (N : Submodule R K)
    (hN : ∀ x, x ∈ N ↔ ι x ∈ LinearMap.range (C.sc' i j k).f.hom)
    (z : C.cycles j) (x : K) (hx : ι x = (C.iCycles j).hom z) :
    (moduleLeftHomologyData _ K ι hι hrange N hN).homologyIso.hom.hom
      (((HomologicalComplex.homologyFunctorIso' _ c i j k hi hk).hom.app C).hom
        ((C.homologyπ j).hom z)) = Submodule.Quotient.mk x := by
  set e := (HomologicalComplex.natIsoSc' (ModuleCat.{u} R) c i j k hi hk).hom.app C
  have h1 : (HomologicalComplex.homologyFunctorIso' _ c i j k hi hk).hom.app C =
      ShortComplex.homologyMap e := by
    simp [HomologicalComplex.homologyFunctorIso', e]
    exact Category.id_comp _
  have h2 : (ShortComplex.homologyMap e).hom ((C.sc j).homologyπ.hom z) =
      (C.sc' i j k).homologyπ.hom ((ShortComplex.cyclesMap e).hom z) :=
    congr(($(ShortComplex.homologyπ_naturality e)).hom z)
  have h3 : (C.sc' i j k).iCycles.hom ((ShortComplex.cyclesMap e).hom z) =
      e.τ₂.hom ((C.sc j).iCycles.hom z) :=
    congr(($(ShortComplex.cyclesMap_i e)).hom z)
  have h4 : (C.sc' i j k).iCycles.hom ((ShortComplex.cyclesMap e).hom z) = (C.iCycles j).hom z := by
    rw [h3]
    simp [e]
    rfl
  rw [h1]
  refine (congrArg (fun w => (moduleLeftHomologyData _ K ι hι hrange N hN).homologyIso.hom.hom w)
    h2).trans ?_
  exact moduleLeftHomologyData_homologyIso_hom_homologyπ _ K ι hι hrange N hN _ x (hx.trans h4.symm)

lemma exists_cycles_of_moduleLeftHomologyData {ιc : Type*} {c : ComplexShape ιc}
    (C : HomologicalComplex (ModuleCat.{u} R) c) (i j k : ιc) (hi : c.prev j = i)
    (hk : c.next j = k) (K : Type u) [AddCommGroup K] [Module R K]
    (ι : K →ₗ[R] (C.sc' i j k).X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker (C.sc' i j k).g.hom) (N : Submodule R K)
    (hN : ∀ x, x ∈ N ↔ ι x ∈ LinearMap.range (C.sc' i j k).f.hom) (x : K) :
    ∃ z : C.cycles j, (C.iCycles j).hom z = ι x := by
  set e := (HomologicalComplex.natIsoSc' (ModuleCat.{u} R) c i j k hi hk).inv.app C
  set h := moduleLeftHomologyData _ K ι hι hrange N hN
  refine ⟨(ShortComplex.cyclesMap e).hom (h.cyclesIso.inv.hom x), ?_⟩
  have h3 : (C.sc j).iCycles.hom ((ShortComplex.cyclesMap e).hom (h.cyclesIso.inv.hom x)) =
      e.τ₂.hom ((C.sc' i j k).iCycles.hom (h.cyclesIso.inv.hom x)) :=
    congr(($(ShortComplex.cyclesMap_i e)).hom (h.cyclesIso.inv.hom x))
  have h4 : (C.sc' i j k).iCycles.hom (h.cyclesIso.inv.hom x) = ι x :=
    congr(($(h.cyclesIso_inv_comp_iCycles)).hom x)
  refine h3.trans ?_
  rw [h4]
  simp [e]
  rfl

end Complexes

end GroundTheory.GroupCoh
