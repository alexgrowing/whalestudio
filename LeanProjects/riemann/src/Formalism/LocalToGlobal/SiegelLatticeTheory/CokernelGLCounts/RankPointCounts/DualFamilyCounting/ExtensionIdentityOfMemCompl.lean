import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NondegenerateOnOrthCompl

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G9

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def formOn (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) : ↥X →ₗ⋆[K] ↥X →ₗ[K] K :=
  (h.comp X.subtype).compl₂ X.subtype

@[simp] theorem formOn_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (x y : ↥X) :
    formOn h X x y = h x y := rfl

theorem formOn_isSymm {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (X : Submodule K V) :
    (formOn h X).IsSymm :=
  ⟨fun x y => hs.eq (x : V) (y : V)⟩

def incl (X : Submodule K V) : ↥X →ₗ[𝓞 K] V := X.subtype.restrictScalars (𝓞 K)

theorem incl_apply (X : Submodule K V) (x : ↥X) : incl X x = x := rfl

theorem incl_injective (X : Submodule K V) : Function.Injective (incl X) := Subtype.val_injective

def push (X : Submodule K V) (L : Submodule (𝓞 K) ↥X) : Submodule (𝓞 K) V := L.map (incl X)

def pull (X : Submodule K V) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) ↥X := L.comap (incl X)

theorem mem_push {X : Submodule K V} {L : Submodule (𝓞 K) ↥X} {v : V} :
    v ∈ push X L ↔ ∃ x ∈ L, (x : V) = v := Submodule.mem_map

theorem coe_mem_push {X : Submodule K V} {L : Submodule (𝓞 K) ↥X} {x : ↥X} :
    (x : V) ∈ push X L ↔ x ∈ L := by
  rw [mem_push]
  constructor
  · rintro ⟨y, hy, e⟩
    rwa [← Subtype.ext e]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem push_le (X : Submodule K V) (L : Submodule (𝓞 K) ↥X) : ∀ v ∈ push X L, v ∈ X := by
  rintro v ⟨x, -, rfl⟩
  exact x.2

theorem pull_push (X : Submodule K V) (L : Submodule (𝓞 K) ↥X) : pull X (push X L) = L :=
  Submodule.comap_map_eq_of_injective (incl_injective X) L

theorem push_pull {X : Submodule K V} {L : Submodule (𝓞 K) V} (hL : ∀ v ∈ L, v ∈ X) :
    push X (pull X L) = L := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hv
    exact ⟨⟨v, hL v hv⟩, hv, rfl⟩

theorem push_injective (X : Submodule K V) : Function.Injective (push X) :=
  Submodule.map_injective_of_injective (incl_injective X)

theorem algebraMap_ne_zero {𝔭 : Ideal (𝓞 F)} (_hp : 𝔭.IsPrime) {t : 𝓞 F} (ht : t ∉ 𝔭) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
  have ht0 : t ≠ 0 := fun e => ht (e ▸ 𝔭.zero_mem)
  have e : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
  rw [e]
  exact (map_ne_zero (algebraMap F K)).mpr (by exact_mod_cast ht0)

theorem mem_of_smul_mem {X : Submodule K V} {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {t : 𝓞 F}
    (ht : t ∉ 𝔭) {v : V} (hv : algebraMap (𝓞 F) (𝓞 K) t • v ∈ X) : v ∈ X := by
  have hne := algebraMap_ne_zero (K := K) hp ht
  have e : v = (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ •
      (algebraMap (𝓞 F) (𝓞 K) t • v) := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) v, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [e]
  exact X.smul_mem _ hv

theorem push_locF (X : Submodule K V) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    push X (locF 𝔭 L) = locF 𝔭 (push X L) := by
  ext v
  rw [LocF.mem_locF_iff hp]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht, hx⟩ := (LocF.mem_locF_iff hp L x).1 hx
    exact ⟨t, ht, ⟨_, hx, (incl X).map_smul _ _⟩⟩
  · rintro ⟨t, ht, hy⟩
    have hv : v ∈ X := mem_of_smul_mem (K := K) hp ht (push_le X L _ hy)
    refine ⟨⟨v, hv⟩, (LocF.mem_locF_iff hp L _).2 ⟨t, ht, ?_⟩, rfl⟩
    rw [← coe_mem_push (X := X)]
    exact hy

theorem push_span (X : Submodule K V) (s : Set ↥X) :
    push X (Submodule.span (𝓞 K) s) = Submodule.span (𝓞 K) (((↑) : ↥X → V) '' s) :=
  Submodule.map_span (incl X) s

theorem isLatIn_push_iff_isLattice {X : Submodule K V} (L : Submodule (𝓞 K) ↥X) :
    IsLatIn X (push X L) ↔ Submodule.IsLattice K L := by
  have hspan : Submodule.span K ((push X L : Submodule (𝓞 K) V) : Set V) =
      (Submodule.span K (L : Set ↥X)).map X.subtype := by
    rw [Submodule.map_span]
    congr 1
  constructor
  · rintro ⟨hfg, hsp⟩
    refine ⟨Submodule.fg_of_fg_map_injective _ (incl_injective X) hfg, ?_⟩
    apply Submodule.map_injective_of_injective X.injective_subtype
    rw [← hspan, hsp, Submodule.map_subtype_top]
  · rintro ⟨hfg, hsp⟩
    refine ⟨hfg.map _, ?_⟩
    rw [hspan, hsp, Submodule.map_subtype_top]

theorem isIntegralLat_push {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} (L : Submodule (𝓞 K) ↥X) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (push X L) ↔ Formalism.HermitianLatticesTheory.IsIntegralLat (formOn h X) L := by
  constructor
  · intro H x hx y hy
    exact H _ (coe_mem_push.mpr hx) _ (coe_mem_push.mpr hy)
  · rintro H _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact H x hx y hy

theorem isJordanIn_top {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) ↥X}
    {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {b : Fin (finrank K X) → V} {a : Fin (finrank K X) → 𝓞 F}
    (H : IsJordanIn h X (push X L) 𝔭 b a) :
    IsJordanIn (formOn h X) ⊤ L 𝔭 (fun i => ⟨b (Fin.cast (finrank_top K ↥X) i), H.1 _⟩)
      (fun i => a (Fin.cast (finrank_top K ↥X) i)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨fun _ => Submodule.mem_top, ?_, fun i j hij => h3 _ _ fun e => hij (Fin.cast_injective _ e),
    fun i => h4 _, fun i => h5 _⟩
  apply push_injective X
  rw [push_locF X hp, push_locF X hp, push_span]
  refine Eq.trans ?_ h2
  congr 2
  ext v
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨i, rfl⟩
    refine ⟨_, ⟨Fin.cast (finrank_top K ↥X).symm i, rfl⟩, ?_⟩
    rfl

section Ext

variable [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}

def extId (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)) : V ≃ₗ[K] V :=
  (Submodule.prodEquivOfIsCompl U (orthK h U) hc).symm.trans
    (((LinearEquiv.refl K ↥U).prodCongr g).trans (Submodule.prodEquivOfIsCompl U (orthK h U) hc))

theorem extId_add (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)) {u w : V}
    (hu : u ∈ U) (hw : w ∈ orthK h U) : extId hc g (u + w) = u + (g ⟨w, hw⟩ : V) := by
  have e1 : (Submodule.prodEquivOfIsCompl U (orthK h U) hc).symm (u + w) = (⟨u, hu⟩, ⟨w, hw⟩) := by
    rw [LinearEquiv.symm_apply_eq, Submodule.coe_prodEquivOfIsCompl']
  simp only [extId, LinearEquiv.trans_apply, e1, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, Submodule.coe_prodEquivOfIsCompl']

theorem exists_add (hc : IsCompl U (orthK h U)) (v : V) :
    ∃ u ∈ U, ∃ w ∈ orthK h U, u + w = v := by
  have hv : v ∈ U ⊔ orthK h U := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  exact Submodule.mem_sup.mp hv

theorem extId_of_mem_U (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)) {u : V}
    (hu : u ∈ U) : extId hc g u = u := by
  have := extId_add hc g hu (orthK h U).zero_mem
  rw [add_zero] at this
  rw [this]
  simp

theorem extension_identity_of_mem_compl (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U))
    (w : ↥(orthK h U)) : extId hc g w = g w := by
  have := extId_add hc g U.zero_mem w.2
  rw [zero_add] at this
  rw [this, zero_add]

theorem extId_mem (hs : h.IsSymm) (hc : IsCompl U (orthK h U)) {g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom (formOn h (orthK h U))) : extId hc g ∈ isomFix h U := by
  refine ⟨fun v v' => ?_, fun u hu => extId_of_mem_U hc g hu⟩
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_add hc v
  obtain ⟨u', hu', w', hw', rfl⟩ := exists_add hc v'
  rw [extId_add hc g hu hw, extId_add hc g hu' hw']
  have hg' : h (g ⟨w, hw⟩ : V) (g ⟨w', hw'⟩ : V) = h w w' := hg _ _
  have o1 : ∀ {x y : V}, x ∈ U → y ∈ orthK h U → h x y = 0 := fun hx hy => mem_orthK.mp hy _ hx
  have o2 : ∀ {x y : V}, x ∈ U → y ∈ orthK h U → h y x = 0 := fun {x y} hx hy => by
    rw [← hs.eq x y, o1 hx hy, map_zero]
  simp only [map_add, LinearMap.add_apply]
  rw [hg', o1 hu (g ⟨w', hw'⟩).2, o2 hu' (g ⟨w, hw⟩).2, o1 hu hw', o2 hu' hw]

theorem map_orthK {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) :
    (orthK h U).map (g : V →ₗ[K] V) = orthK h U := by
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact apply_mem_orthK hg hy
  · intro hx
    exact ⟨g.symm x, apply_mem_orthK ((isomFix h U).inv_mem hg) hx, g.apply_symm_apply x⟩

def restr {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U) :=
  g.ofSubmodules (orthK h U) (orthK h U) (map_orthK hg)

theorem restr_apply {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) (w : ↥(orthK h U)) :
    (restr hg w : V) = g w :=
  LinearEquiv.ofSubmodules_apply _ _ _

theorem restr_mem {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) :
    restr hg ∈ Formalism.HermitianLatticesTheory.isom (formOn h (orthK h U)) := fun x y => by
  simp only [formOn_apply, restr_apply]
  exact hg.1 x y

theorem extId_restr (hc : IsCompl U (orthK h U)) {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) :
    extId hc (restr hg) = g := by
  apply LinearEquiv.ext
  intro v
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_add hc v
  rw [extId_add hc _ hu hw, restr_apply, map_add, hg.2 u hu]

theorem restr_extId (hs : h.IsSymm) (hc : IsCompl U (orthK h U))
    {g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (formOn h (orthK h U))) :
    restr (extId_mem hs hc hg) = g := by
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  exact (restr_apply _ w).trans (extension_identity_of_mem_compl hc g w)

theorem gmap_push {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) (L : Submodule (𝓞 K) ↥(orthK h U)) :
    Formalism.HermitianLatticesTheory.gmap g (push (orthK h U) L) = push (orthK h U) (Formalism.HermitianLatticesTheory.gmap (restr hg) L) := by
  unfold Formalism.HermitianLatticesTheory.gmap push
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1

theorem gmap_extId_push (hs : h.IsSymm) (hc : IsCompl U (orthK h U))
    {g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (formOn h (orthK h U)))
    (L : Submodule (𝓞 K) ↥(orthK h U)) :
    Formalism.HermitianLatticesTheory.gmap (extId hc g) (push (orthK h U) L) = push (orthK h U) (Formalism.HermitianLatticesTheory.gmap g L) := by
  rw [gmap_push (extId_mem hs hc hg), restr_extId hs hc hg]

end Ext

end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass
