import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.HasTraceDistrOfAdmissible

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.ContragredientTranspose
  GroundTheory.Automorphic.Whittaker MeasureTheory

namespace PositivityTheory.PfBern.Unit

section Riesz

variable {V : Type} [AddCommGroup V] [Module ℂ V] (B₀ : Sesq V) (W : Submodule ℂ V)

def IsRieszRepresentative (C : Sesq V) (A : W →ₗ[ℂ] V) (N : Module.End ℂ W) : Prop :=
  ∀ x y : W, B₀ (N x) y = C (A x) y

variable {B₀ W}

theorem riesz_unique (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re) {C : Sesq V} {A : W →ₗ[ℂ] V}
    {N N' : Module.End ℂ W} (h : IsRieszRepresentative B₀ W C A N) (h' : IsRieszRepresentative B₀ W C A N') : N = N' := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  by_contra hne
  have hd : ((N x : V) - (N' x : V)) ≠ 0 := sub_ne_zero.2 hne
  have hp := hpos _ hd
  have h1 := h x (N x - N' x)
  have h2 := h' x (N x - N' x)
  have e : B₀ ((N x : V) - (N' x : V)) ((N x - N' x : W) : V) = 0 := by
    rw [map_sub, LinearMap.sub_apply, h1, h2, sub_self]
  have hc : ((N x - N' x : W) : V) = (N x : V) - (N' x : V) := rfl
  rw [hc] at e
  rw [e] at hp
  simp at hp

theorem antilin_ext_basis [FiniteDimensional ℂ W] (φ ψ : V →ₗ⋆[ℂ] ℂ)
    (h : ∀ i, φ (Module.finBasis ℂ W i : V) = ψ (Module.finBasis ℂ W i : V)) (u : W) : φ u = ψ u := by
  rw [← (Module.finBasis ℂ W).sum_repr u, Submodule.coe_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, h i]

theorem riesz_exists [FiniteDimensional ℂ W] (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re) (C : Sesq V)
    (A : W →ₗ[ℂ] V) : ∃ N, IsRieszRepresentative B₀ W C A N := by
  let b := Module.finBasis ℂ W
  let β : Sesq V → (W →ₗ[ℂ] V) → (W →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ)) := fun C A =>
    LinearMap.pi fun i => (C.flip (b i : V)) ∘ₗ A
  have hβ : ∀ C A w i, β C A w i = C (A w) (b i) := fun _ _ _ _ => rfl
  have hinj : Function.Injective (β B₀ W.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    have := hpos w (fun h' => hne (Subtype.ext h'))
    have hz := antilin_ext_basis (W := W) (B₀ w) 0 (fun i => by
      have := congrFun hw i
      rw [hβ] at this
      simpa using this) w
    rw [hz] at this
    simp at this
  let e := LinearMap.linearEquivOfInjective (β B₀ W.subtype) hinj (by simp)
  refine ⟨e.symm.toLinearMap ∘ₗ β C A, fun x y => ?_⟩
  refine antilin_ext_basis (W := W) (B₀ _) (C (A x)) (fun i => ?_) y
  have h1 : β B₀ W.subtype (e.symm (β C A x)) = β C A x := by
    have := e.apply_symm_apply (β C A x)
    rw [LinearMap.linearEquivOfInjective_apply] at this
    exact this
  have := congrFun h1 i
  rw [hβ, hβ] at this
  exact this

end Riesz

section Rep

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
  {B₀ : Sesq V} (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re)

def BiInv (K : Subgroup G) (f : G → ℂ) : Prop := ∀ k ∈ K, ∀ x, f (k * x) = f x ∧ f (x * k) = f x

def resA (K : Subgroup G) (f : locallyConstantCompactSupport G ℂ ℂ) : fixedVectors ρ K →ₗ[ℂ] V :=
  heckeLin μ hρ.1 f ∘ₗ (fixedVectors ρ K).subtype

def rN {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) (C : Sesq V)
    (f : locallyConstantCompactSupport G ℂ ℂ) : Module.End ℂ (fixedVectors ρ K) :=
  haveI := hρ.2 K hKc hKo
  Classical.choose (riesz_exists hpos C (resA μ hρ K f))

theorem rN_spec {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) (C : Sesq V)
    (f : locallyConstantCompactSupport G ℂ ℂ) : IsRieszRepresentative B₀ _ C (resA μ hρ K f) (rN μ hρ hpos hKc hKo C f) :=
  haveI := hρ.2 K hKc hKo
  Classical.choose_spec (riesz_exists hpos C (resA μ hρ K f))

def DK {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) (C : Sesq V)
    (f : locallyConstantCompactSupport G ℂ ℂ) : ℂ :=
  LinearMap.trace ℂ _ (rN μ hρ hpos hKc hKo C f)

theorem B0_fixedProj (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w) {K : Subgroup G} (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (z y : V) (hy : y ∈ fixedVectors ρ K) :
    B₀ (fixedProj ρ hρ.1 hKc hKo z) y = B₀ z y := by
  have hc : ∀ u ∈ coinvariantsKer ρ K, B₀ u y = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨κ, w⟩, rfl⟩ := hx
      have h1 := hinv κ w y
      rw [hy κ κ.2] at h1
      show B₀ (ρ κ w - w) y = 0
      rw [map_sub, LinearMap.sub_apply, h1, sub_self]
    | zero => simp
    | add x y' _ _ hx hy' => rw [map_add, LinearMap.add_apply, hx, hy', add_zero]
    | smul a x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]
  have := hc _ (sub_fixedProj_mem hρ.1 hKc hKo z)
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
  exact this.symm

theorem heckeLin_fixedProj {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (f : locallyConstantCompactSupport G ℂ ℂ) (hf : BiInv K f) (v : V) :
    heckeLin μ hρ.1 f (fixedProj ρ hρ.1 hKc hKo v) = heckeLin μ hρ.1 f v := by
  let F : HeckeAlgebra μ := f
  have hmem : F ∈ biInvariant μ K := fun k hk x => hf k hk x
  have hri := (mem_biInvariant_iff_idem hKc hKo).1 hmem
  have e : groupConv μ (f : G → ℂ) (idem μ hKc hKo) = f := by
    have := congrArg (fun F' : HeckeAlgebra μ => (F' : G → ℂ)) hri.2
    rw [HeckeAlgebra.coe_mul] at this
    exact this
  rw [heckeLin_apply, heckeLin_apply, ← heckeAct_idem_eq_fixedProj (μ := μ) hKc hKo hρ.1,
    ← heckeAct_groupConv f.2 (idem μ hKc hKo).mem (hρ.1 _), e]

theorem DK_mono (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w) {K K' : Subgroup G} (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (hK'c : IsCompact (K' : Set G)) (hK'o : IsOpen (K' : Set G)) (hle : K' ≤ K)
    (C : Sesq V) (f : locallyConstantCompactSupport G ℂ ℂ) (hf : BiInv K f) :
    DK μ hρ hpos hK'c hK'o C f = DK μ hρ hpos hKc hKo C f := by
  haveI := hρ.2 K hKc hKo
  haveI := hρ.2 K' hK'c hK'o
  have hWW : fixedVectors ρ K ≤ fixedVectors ρ K' := fixedVectors_antitone ρ hle
  let ι : fixedVectors ρ K →ₗ[ℂ] fixedVectors ρ K' := Submodule.inclusion hWW
  let p : fixedVectors ρ K' →ₗ[ℂ] fixedVectors ρ K := fixedProj ρ hρ.1 hKc hKo ∘ₗ (fixedVectors ρ K').subtype
  have sN' := rN_spec μ hρ hpos hK'c hK'o C f
  have sN := rN_spec μ hρ hpos hKc hKo C f
  have h1 : rN μ hρ hpos hK'c hK'o C f = rN μ hρ hpos hK'c hK'o C f ∘ₗ ι ∘ₗ p := by
    refine riesz_unique hpos sN' fun x y => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, sN']
    show C (heckeLin μ hρ.1 f (fixedProj ρ hρ.1 hKc hKo (x : V) : V)) y = C (heckeLin μ hρ.1 f x) y
    rw [heckeLin_fixedProj μ hρ hKc hKo f hf]
  have h2 : p ∘ₗ rN μ hρ hpos hK'c hK'o C f ∘ₗ ι = rN μ hρ hpos hKc hKo C f := by
    refine riesz_unique hpos (fun x y => ?_) sN
    show B₀ (fixedProj ρ hρ.1 hKc hKo (rN μ hρ hpos hK'c hK'o C f (ι x) : V) : V) y = _
    rw [B0_fixedProj hρ hinv hKc hKo _ _ y.2]
    have := sN' (ι x) (ι y)
    exact this
  unfold DK
  calc LinearMap.trace ℂ _ (rN μ hρ hpos hK'c hK'o C f)
      = LinearMap.trace ℂ _ ((rN μ hρ hpos hK'c hK'o C f ∘ₗ ι) ∘ₗ p) := by
        conv_lhs => rw [h1]
        rfl
    _ = LinearMap.trace ℂ _ (p ∘ₗ (rN μ hρ hpos hK'c hK'o C f ∘ₗ ι)) := LinearMap.trace_comp_comm' _ _
    _ = LinearMap.trace ℂ _ (rN μ hρ hpos hKc hKo C f) := congrArg _ h2

end Rep

section Lin

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
  {B₀ : Sesq V} (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re)

theorem BiInv.mono {K K' : Subgroup G} {f : G → ℂ} (hf : BiInv K f) (hle : K' ≤ K) : BiInv K' f :=
  fun k hk x => hf k (hle hk) x

theorem BiInv.add {K : Subgroup G} {f g : G → ℂ} (hf : BiInv K f) (hg : BiInv K g) : BiInv K (f + g) :=
  fun k hk x => ⟨by simp [(hf k hk x).1, (hg k hk x).1], by simp [(hf k hk x).2, (hg k hk x).2]⟩

theorem BiInv.smul {K : Subgroup G} {f : G → ℂ} (c : ℂ) (hf : BiInv K f) : BiInv K (c • f) :=
  fun k hk x => ⟨by simp [(hf k hk x).1], by simp [(hf k hk x).2]⟩

theorem exists_K (f : locallyConstantCompactSupport G ℂ ℂ) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ BiInv (K : Subgroup G) f := by
  obtain ⟨K, hKc, hK⟩ := exists_forall_mul_left_mul_right f.2
  exact ⟨K, hKc, fun k hk x => ⟨by simpa using hK k hk x 1 (one_mem _), by simpa using hK 1 (one_mem _) x k hk⟩⟩

theorem rN_add_C {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) (C₁ C₂ : Sesq V)
    (f : locallyConstantCompactSupport G ℂ ℂ) :
    rN μ hρ hpos hKc hKo (C₁ + C₂) f = rN μ hρ hpos hKc hKo C₁ f + rN μ hρ hpos hKc hKo C₂ f := by
  refine riesz_unique hpos (rN_spec μ hρ hpos hKc hKo _ f) fun x y => ?_
  have s1 := rN_spec μ hρ hpos hKc hKo C₁ f x y
  have s2 := rN_spec μ hρ hpos hKc hKo C₂ f x y
  show B₀ ((rN μ hρ hpos hKc hKo C₁ f x : V) + (rN μ hρ hpos hKc hKo C₂ f x : V)) y = _
  rw [map_add, LinearMap.add_apply, s1, s2, LinearMap.add_apply, LinearMap.add_apply]

theorem rN_smul_C {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) (c : ℂ) (C : Sesq V)
    (f : locallyConstantCompactSupport G ℂ ℂ) :
    rN μ hρ hpos hKc hKo (c • C) f = c • rN μ hρ hpos hKc hKo C f := by
  refine riesz_unique hpos (rN_spec μ hρ hpos hKc hKo _ f) fun x y => ?_
  have s1 := rN_spec μ hρ hpos hKc hKo C f x y
  show B₀ (c • (rN μ hρ hpos hKc hKo C f x : V)) y = _
  rw [map_smul, LinearMap.smul_apply, s1, LinearMap.smul_apply, LinearMap.smul_apply]

theorem rN_add_f {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) (C : Sesq V)
    (f₁ f₂ : locallyConstantCompactSupport G ℂ ℂ) :
    rN μ hρ hpos hKc hKo C (f₁ + f₂) = rN μ hρ hpos hKc hKo C f₁ + rN μ hρ hpos hKc hKo C f₂ := by
  refine riesz_unique hpos (rN_spec μ hρ hpos hKc hKo C _) fun x y => ?_
  have s1 := rN_spec μ hρ hpos hKc hKo C f₁ x y
  have s2 := rN_spec μ hρ hpos hKc hKo C f₂ x y
  show B₀ ((rN μ hρ hpos hKc hKo C f₁ x : V) + (rN μ hρ hpos hKc hKo C f₂ x : V)) y =
    C (heckeLin μ hρ.1 (f₁ + f₂) x) y
  rw [map_add, LinearMap.add_apply, s1, s2, heckeLin_add μ hρ.1, LinearMap.add_apply, map_add, LinearMap.add_apply]
  rfl

theorem rN_smul_f {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) (C : Sesq V) (c : ℂ)
    (f : locallyConstantCompactSupport G ℂ ℂ) :
    rN μ hρ hpos hKc hKo C (c • f) = c • rN μ hρ hpos hKc hKo C f := by
  refine riesz_unique hpos (rN_spec μ hρ hpos hKc hKo C _) fun x y => ?_
  have s1 := rN_spec μ hρ hpos hKc hKo C f x y
  show B₀ (c • (rN μ hρ hpos hKc hKo C f x : V)) y = C (heckeLin μ hρ.1 (c • f) x) y
  rw [map_smul, LinearMap.smul_apply, s1, heckeLin_smul μ hρ.1, LinearMap.smul_apply, map_smul, LinearMap.smul_apply]
  rfl

def DF (C : Sesq V) (f : locallyConstantCompactSupport G ℂ ℂ) : ℂ :=
  DK μ hρ hpos (Classical.choose_spec (exists_K f)).1 (Classical.choose (exists_K f)).isOpen C f

theorem DF_eq (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w) (C : Sesq V) (f : locallyConstantCompactSupport G ℂ ℂ)
    {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) (hf : BiInv K f) :
    DF μ hρ hpos C f = DK μ hρ hpos hKc hKo C f := by
  have hL := Classical.choose_spec (exists_K f)
  set L := Classical.choose (exists_K f)
  have hMc : IsCompact ((K ⊓ (L : Subgroup G) : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKc.inter_right L.isClosed
  have hMo : IsOpen ((K ⊓ (L : Subgroup G) : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKo.inter L.isOpen
  unfold DF
  rw [← DK_mono μ hρ hpos hinv hL.1 L.isOpen hMc hMo inf_le_right C f hL.2,
    DK_mono μ hρ hpos hinv hKc hKo hMc hMo inf_le_left C f hf]

def formD (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w) (Pr : (G → ℂ) →ₗ[ℂ] testFn G) :
    Sesq V →ₗ[ℂ] (G → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun C g => DF μ hρ hpos C (Pr g))
    (fun C₁ C₂ g => by
      unfold DF DK
      rw [rN_add_C, map_add])
    (fun c C g => by
      unfold DF DK
      rw [rN_smul_C, map_smul, smul_eq_mul])
    (fun C g₁ g₂ => by
      obtain ⟨K₁, h₁c, h₁⟩ := exists_K (Pr g₁)
      obtain ⟨K₂, h₂c, h₂⟩ := exists_K (Pr g₂)
      have hMc : IsCompact (((K₁ : Subgroup G) ⊓ (K₂ : Subgroup G) : Subgroup G) : Set G) := by
        rw [Subgroup.coe_inf]; exact h₁c.inter_right K₂.isClosed
      have hMo : IsOpen (((K₁ : Subgroup G) ⊓ (K₂ : Subgroup G) : Subgroup G) : Set G) := by
        rw [Subgroup.coe_inf]; exact K₁.isOpen.inter K₂.isOpen
      have b₁ := h₁.mono (inf_le_left : (K₁ : Subgroup G) ⊓ K₂ ≤ K₁)
      have b₂ := h₂.mono (inf_le_right : (K₁ : Subgroup G) ⊓ K₂ ≤ K₂)
      rw [map_add, DF_eq μ hρ hpos hinv C _ hMc hMo (by exact b₁.add b₂), DF_eq μ hρ hpos hinv C _ hMc hMo b₁,
        DF_eq μ hρ hpos hinv C _ hMc hMo b₂]
      unfold DK
      rw [rN_add_f, map_add])
    (fun c C g => by
      obtain ⟨K₁, h₁c, h₁⟩ := exists_K (Pr g)
      rw [map_smul, DF_eq μ hρ hpos hinv C _ h₁c K₁.isOpen (by exact h₁.smul c), DF_eq μ hρ hpos hinv C _ h₁c K₁.isOpen h₁]
      unfold DK
      rw [rN_smul_f, map_smul, smul_eq_mul])

theorem formD_apply (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w) (Pr : (G → ℂ) →ₗ[ℂ] testFn G) (C : Sesq V)
    (g : G → ℂ) : formD μ hρ hpos hinv Pr C g = DF μ hρ hpos C (Pr g) := rfl

end Lin

end PositivityTheory.PfBern.Unit
