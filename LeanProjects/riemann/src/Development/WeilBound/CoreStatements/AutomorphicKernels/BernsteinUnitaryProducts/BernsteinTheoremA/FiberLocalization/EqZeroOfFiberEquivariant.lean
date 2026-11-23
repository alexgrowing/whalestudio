import Mathlib
import GroundTheory.AutomorphicForms.WhittakerLSpace
import GroundTheory.AutomorphicForms.WhittakerCriterion

noncomputable section

open Set GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.PfBern.Loc

abbrev SC (X : Type*) [TopologicalSpace X] : Submodule ℂ (X → ℂ) :=
  locallyConstantCompactSupport X ℂ ℂ

abbrev Distr (X : Type*) [TopologicalSpace X] : Type _ := Module.Dual ℂ (SC X)

variable {X : Type*} [TopologicalSpace X]

def VanishesOn (D : Distr X) (U : Set X) : Prop :=
  ∀ f : SC X, Function.support (f : X → ℂ) ⊆ U → D f = 0

def SupportedIn (D : Distr X) (Z : Set X) : Prop :=
  VanishesOn D Zᶜ

def mulInd (A : Set X) (hA : IsClopen A) : SC X →ₗ[ℂ] SC X where
  toFun f := ⟨fun x => A.indicator 1 x * (f : X → ℂ) x,
    (indicator_mul_mem (U := univ) hA ⟨f.2, subset_univ _⟩).1⟩
  map_add' f g := Subtype.ext <| funext fun x => by simp [mul_add]
  map_smul' c f := Subtype.ext <| funext fun x => by simp [mul_left_comm]

@[simp]
theorem coe_mulInd (A : Set X) (hA : IsClopen A) (f : SC X) :
    ((mulInd A hA f : SC X) : X → ℂ) = fun x => A.indicator 1 x * (f : X → ℂ) x :=
  rfl

section General

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [TotallyDisconnectedSpace Y]

def FiberStable (p : X → Y) (W : Submodule ℂ (SC X)) : Prop :=
  ∀ V : Set Y, IsClopen V → ∀ hpV : IsClopen (p ⁻¹' V), ∀ w ∈ W, mulInd (p ⁻¹' V) hpV w ∈ W

theorem eq_top_of_fiber {p : X → Y} (hp : Continuous p) (W : Submodule ℂ (SC X))
    (hW : FiberStable p W)
    (hfib : ∀ (y : Y) (D : Distr X), (∀ w ∈ W, D w = 0) → SupportedIn D (p ⁻¹' {y}) → D = 0) :
    W = ⊤ := by
  classical
  rw [eq_top_iff]
  intro g _
  let W' : Submodule ℂ (X → ℂ) := W.map (SC X).subtype
  have hmem : (g : X → ℂ) ∈ W' := by
    refine mem_of_forall_fiber (U := univ) (C := univ) isClosed_univ hp ?_ ?_ ⟨g.2, subset_univ _⟩ ?_
    · rintro f ⟨-, hf0⟩
      have : f = 0 := funext fun x => hf0 x (mem_univ x)
      rw [this]
      exact W'.zero_mem
    · rintro V hV w ⟨w0, hw0, rfl⟩
      exact ⟨mulInd (p ⁻¹' V) (hV.preimage hp) w0, hW V hV (hV.preimage hp) w0 hw0, rfl⟩
    · intro y
      let K : Submodule ℂ (SC X) := (vanishingOn (p ⁻¹' {y})).comap (SC X).subtype
      have hgM : g ∈ W ⊔ K := by
        by_contra hg
        obtain ⟨D, hDg, hDM⟩ := Submodule.exists_le_ker_of_notMem hg
        have hD0 : D = 0 := by
          refine hfib y D (fun w hw => hDM (Submodule.mem_sup_left hw)) ?_
          intro f hf
          refine hDM (Submodule.mem_sup_right ?_)
          intro x hx
          by_contra hfx
          exact hf hfx hx
        exact hDg (by rw [hD0, LinearMap.zero_apply])
      obtain ⟨w, hw, k, hk, hwk⟩ := Submodule.mem_sup.1 hgM
      refine Submodule.mem_sup.2 ⟨(w : X → ℂ), ⟨w, hw, rfl⟩, (k : X → ℂ),
        ⟨⟨k.2, subset_univ _⟩, fun x hx => hk x hx.2⟩, ?_⟩
      rw [← hwk]
      rfl
  obtain ⟨w, hw, hwg⟩ := hmem
  have : w = g := Subtype.ext hwg
  exact this ▸ hw

theorem eq_zero_of_fiber {p : X → Y} (hp : Continuous p) (W : Submodule ℂ (SC X))
    (hW : FiberStable p W)
    (hfib : ∀ (y : Y) (D : Distr X), (∀ w ∈ W, D w = 0) → SupportedIn D (p ⁻¹' {y}) → D = 0)
    (D : Distr X) (hD : ∀ w ∈ W, D w = 0) : D = 0 := by
  have htop := eq_top_of_fiber hp W hW hfib
  ext f
  rw [LinearMap.zero_apply]
  exact hD f (htop ▸ Submodule.mem_top)

def IsEquivariant {ι : Type*} (e : ι → X ≃ₜ X) (χ : ι → ℂ) (D : Distr X) : Prop :=
  ∀ (i : ι) (f : SC X), D (compHomeoL (e i) f) = χ i * D f

def relSpanH {ι : Type*} (e : ι → X ≃ₜ X) (χ : ι → ℂ) : Submodule ℂ (SC X) :=
  Submodule.span ℂ (range fun q : ι × SC X => compHomeoL (e q.1) q.2 - χ q.1 • q.2)

theorem isEquivariant_iff {ι : Type*} (e : ι → X ≃ₜ X) (χ : ι → ℂ) (D : Distr X) :
    IsEquivariant e χ D ↔ ∀ w ∈ relSpanH e χ, D w = 0 := by
  constructor
  · intro hD w hw
    have hle : relSpanH e χ ≤ LinearMap.ker D := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨i, f⟩, rfl⟩
      simp [hD i f]
    exact hle hw
  · intro hD i f
    have := hD _ (Submodule.subset_span ⟨(i, f), rfl⟩)
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at this
    exact this

omit [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y] in
theorem mulInd_compHomeoL {p : X → Y} (e : X ≃ₜ X) (he : ∀ x, p (e x) = p x) (V : Set Y)
    (hpV : IsClopen (p ⁻¹' V)) (f : SC X) :
    mulInd (p ⁻¹' V) hpV (compHomeoL e f) = compHomeoL e (mulInd (p ⁻¹' V) hpV f) := by
  refine Subtype.ext <| funext fun x => ?_
  simp only [coe_mulInd, coe_compHomeoL, Function.comp_apply]
  congr 1
  by_cases hx : p x ∈ V <;> simp [hx, he]

omit [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y] in
theorem fiberStable_relSpanH {ι : Type*} {p : X → Y} (e : ι → X ≃ₜ X) (χ : ι → ℂ)
    (he : ∀ i x, p (e i x) = p x) : FiberStable p (relSpanH e χ) := by
  intro V _ hpV w hw
  have hle : relSpanH e χ ≤ (relSpanH e χ).comap (mulInd (p ⁻¹' V) hpV) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨i, f⟩, rfl⟩
    show mulInd (p ⁻¹' V) hpV (compHomeoL (e i) f - χ i • f) ∈ relSpanH e χ
    rw [map_sub, map_smul, mulInd_compHomeoL (e i) (he i)]
    exact Submodule.subset_span ⟨(i, mulInd (p ⁻¹' V) hpV f), rfl⟩
  exact hle hw

theorem eq_zero_of_fiber_equivariant {ι : Type*} {p : X → Y} (hp : Continuous p)
    (e : ι → X ≃ₜ X) (χ : ι → ℂ) (he : ∀ i x, p (e i x) = p x)
    (hfib : ∀ (y : Y) (D : Distr X), IsEquivariant e χ D → SupportedIn D (p ⁻¹' {y}) → D = 0)
    (D : Distr X) (hD : IsEquivariant e χ D) : D = 0 :=
  eq_zero_of_fiber hp (relSpanH e χ) (fiberStable_relSpanH e χ he)
    (fun y D' hD' hsupp => hfib y D' ((isEquivariant_iff e χ D').2 hD') hsupp)
    D ((isEquivariant_iff e χ D).1 hD)

end General

section Conj

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [TotallyDisconnectedSpace Y]

end Conj

section Restrict

variable {Z : Set X}

def restr (hZ : IsClosed Z) : SC X →ₗ[ℂ] SC Z where
  toFun f := ⟨fun z => (f : X → ℂ) z,
    ⟨f.2.1.comp_continuous continuous_subtype_val,
      f.2.2.comp_isClosedEmbedding hZ.isClosedEmbedding_subtypeVal⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_restr (hZ : IsClosed Z) (f : SC X) :
    ((restr hZ f : SC Z) : Z → ℂ) = fun z : Z => (f : X → ℂ) z :=
  rfl

def extendDistr (hZ : IsClosed Z) (D' : Distr Z) : Distr X :=
  D'.comp (restr hZ)

theorem extendDistr_apply (hZ : IsClosed Z) (D' : Distr Z) (f : SC X) :
    extendDistr hZ D' f = D' (restr hZ f) :=
  rfl

theorem restr_compHomeoL (hZ : IsClosed Z) (e : X ≃ₜ X) (heZ : ∀ x, x ∈ Z ↔ e x ∈ Z)
    (f : SC X) :
    restr hZ (compHomeoL e f) = compHomeoL (e.subtype heZ) (restr hZ f) :=
  rfl

variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

theorem restr_surjective (hZ : IsClosed Z) : Function.Surjective (restr hZ) := by
  intro φ
  obtain ⟨f, hf, hfφ⟩ := exists_lift (U := univ) isOpen_univ (subset_univ Z) φ.2
  exact ⟨⟨f, hf.1⟩, Subtype.ext (funext hfφ)⟩

end Restrict

section FiberSubspace

variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [TotallyDisconnectedSpace Y]

def fiberHomeo {p : X → Y} (e : X ≃ₜ X) (he : ∀ x, p (e x) = p x) (y : Y) :
    (p ⁻¹' {y}) ≃ₜ (p ⁻¹' {y}) :=
  e.subtype fun x => by simp only [Set.mem_preimage, he]

omit [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [T2Space Y]
  [LocallyCompactSpace Y] in

theorem isEquivariant_extendDistr {ι : Type*} {p : X → Y} (hp : Continuous p)
    (e : ι → X ≃ₜ X) (χ : ι → ℂ) (he : ∀ i x, p (e i x) = p x) (y : Y)
    (D' : Distr (p ⁻¹' {y})) (hD' : IsEquivariant (fun i => fiberHomeo (e i) (he i) y) χ D') :
    IsEquivariant e χ (extendDistr (isClosed_singleton.preimage hp) D') := by
  intro i f
  rw [extendDistr_apply, extendDistr_apply, restr_compHomeoL _ (e i)]
  exact hD' i _

end FiberSubspace

section OpenSubset

variable {U : Set X}

open Classical in

def extZeroFun (U : Set X) (φ : U → ℂ) : X → ℂ :=
  fun x => if h : x ∈ U then φ ⟨x, h⟩ else 0

omit [TopologicalSpace X] in
theorem extZeroFun_val (φ : U → ℂ) (x : U) : extZeroFun U φ x = φ x := by
  simp [extZeroFun, x.2]

omit [TopologicalSpace X] in
theorem extZeroFun_of_notMem (φ : U → ℂ) {x : X} (hx : x ∉ U) : extZeroFun U φ x = 0 := by
  simp [extZeroFun, hx]

variable [T2Space X]

theorem extZeroFun_mem (hU : IsOpen U) (φ : SC U) : extZeroFun U φ ∈ SC X := by
  classical
  set K : Set X := Subtype.val '' tsupport (φ : U → ℂ) with hKdef
  have hKc : IsCompact K := φ.2.2.image continuous_subtype_val
  have hK0 : ∀ x ∉ K, extZeroFun U φ x = 0 := by
    intro x hx
    by_cases hxU : x ∈ U
    · rw [show x = ((⟨x, hxU⟩ : U) : X) from rfl, extZeroFun_val]
      exact image_eq_zero_of_notMem_tsupport fun h => hx ⟨⟨x, hxU⟩, h, rfl⟩
    · exact extZeroFun_of_notMem _ hxU
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro hKc hK0⟩
  by_cases hxU : x ∈ U
  · obtain ⟨V, hVo, hxV, hVc⟩ := (IsLocallyConstant.iff_exists_open _).1 φ.2.1 ⟨x, hxU⟩
    obtain ⟨O, hOo, hOV⟩ := isOpen_induced_iff.1 hVo
    have hxO : x ∈ O := by
      have : (⟨x, hxU⟩ : U) ∈ Subtype.val ⁻¹' O := by rw [hOV]; exact hxV
      exact this
    refine ⟨O ∩ U, hOo.inter hU, ⟨hxO, hxU⟩, fun x' hx' => ?_⟩
    have hx'V : (⟨x', hx'.2⟩ : U) ∈ V := by rw [← hOV]; exact hx'.1
    rw [show x' = ((⟨x', hx'.2⟩ : U) : X) from rfl, extZeroFun_val,
      show x = ((⟨x, hxU⟩ : U) : X) from rfl, extZeroFun_val]
    exact hVc _ hx'V
  · have hxK : x ∉ K := fun ⟨z, _, hz⟩ => hxU (hz ▸ z.2)
    refine ⟨Kᶜ, hKc.isClosed.isOpen_compl, hxK, fun x' hx' => ?_⟩
    rw [hK0 x' hx', hK0 x hxK]

def extZero (hU : IsOpen U) : SC U →ₗ[ℂ] SC X where
  toFun φ := ⟨extZeroFun U φ, extZeroFun_mem hU φ⟩
  map_add' φ ψ := Subtype.ext <| funext fun x => by
    by_cases hx : x ∈ U <;> simp [extZeroFun, hx]
  map_smul' c φ := Subtype.ext <| funext fun x => by
    by_cases hx : x ∈ U <;> simp [extZeroFun, hx]

end OpenSubset

section Transport

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]

def pullL (h : A ≃ₜ B) : SC B →ₗ[ℂ] SC A where
  toFun f := ⟨fun a => (f : B → ℂ) (h a), f.2.1.comp_continuous h.continuous, f.2.2.comp_homeomorph h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pullL_pullL_symm (h : A ≃ₜ B) (f : SC A) : pullL h (pullL h.symm f) = f :=
  Subtype.ext <| funext fun a => by simp [pullL]

end Transport

end PositivityTheory.PfBern.Loc

end
