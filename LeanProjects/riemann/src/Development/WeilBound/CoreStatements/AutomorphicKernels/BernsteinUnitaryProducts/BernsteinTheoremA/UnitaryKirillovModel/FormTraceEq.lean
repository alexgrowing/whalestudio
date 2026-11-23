import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.FormTrace

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.ContragredientTranspose
  GroundTheory.Automorphic.Whittaker MeasureTheory

namespace PositivityTheory.PfBern.Unit

section Eq

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
  {B₀ : Sesq V} (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re)

def conjSub (g : G) (K : Subgroup G) : Subgroup G := K.comap (MulAut.conj g⁻¹).toMonoidHom

theorem mem_conjSub {g : G} {K : Subgroup G} {x : G} : x ∈ conjSub g K ↔ g⁻¹ * x * g ∈ K := by
  simp [conjSub, MulAut.conj_apply]

def conjHomeo (g : G) : G ≃ₜ G := (Homeomorph.mulLeft g⁻¹).trans (Homeomorph.mulRight g)

theorem coe_conjSub (g : G) (K : Subgroup G) : (conjSub g K : Set G) = conjHomeo g ⁻¹' (K : Set G) := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_preimage, mem_conjSub, conjHomeo, Homeomorph.trans_apply,
    Homeomorph.coe_mulLeft, Homeomorph.coe_mulRight]

theorem isCompact_conjSub (g : G) {K : Subgroup G} (hKc : IsCompact (K : Set G)) :
    IsCompact (conjSub g K : Set G) := by
  rw [coe_conjSub, ← congrFun (conjHomeo g).image_symm (K : Set G)]
  exact hKc.image (conjHomeo g).symm.continuous

theorem isOpen_conjSub (g : G) {K : Subgroup G} (hKo : IsOpen (K : Set G)) : IsOpen (conjSub g K : Set G) := by
  rw [coe_conjSub]
  exact hKo.preimage (conjHomeo g).continuous

def conjEquiv (g : G) (K : Subgroup G) : fixedVectors ρ K ≃ₗ[ℂ] fixedVectors ρ (conjSub g K) where
  toFun v := ⟨ρ g v, by
    rw [mem_fixedVectors]
    intro x hx
    have h := v.2
    rw [mem_fixedVectors] at h
    have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (ρ g⁻¹),
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, h _ (mem_conjSub.1 hx)]⟩
  map_add' v w := Subtype.ext (map_add _ _ _)
  map_smul' c v := Subtype.ext (map_smul _ _ _)
  invFun w := ⟨ρ g⁻¹ w, by
    rw [mem_fixedVectors]
    intro x hx
    have h := w.2
    rw [mem_fixedVectors] at h
    have hx' : g * x * g⁻¹ ∈ conjSub g K := mem_conjSub.2 (by group; exact hx)
    have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (ρ g),
      ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, h _ hx']⟩
  left_inv v := Subtype.ext (by
    show ρ g⁻¹ (ρ g v) = v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])
  right_inv w := Subtype.ext (by
    show ρ g (ρ g⁻¹ w) = w
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])

theorem conjEquiv_apply (g : G) (K : Subgroup G) (v : fixedVectors ρ K) :
    (conjEquiv g K v : V) = ρ g v := rfl

theorem conjEquiv_symm_apply (g : G) (K : Subgroup G) (w : fixedVectors ρ (conjSub g K)) :
    ((conjEquiv g K).symm w : V) = ρ g⁻¹ w := rfl

theorem biInv_conj (g : G) {K : Subgroup G} {f : G → ℂ} (hf : BiInv K f) : BiInv (conjSub g K) (conjFn g f) := by
  intro k hk x
  have hk' := mem_conjSub.1 hk
  constructor
  · show f (g⁻¹ * (k * x) * g) = f (g⁻¹ * x * g)
    have := (hf _ hk' (g⁻¹ * x * g)).1
    rw [← this]; congr 1; group
  · show f (g⁻¹ * (x * k) * g) = f (g⁻¹ * x * g)
    have := (hf _ hk' (g⁻¹ * x * g)).2
    rw [← this]; congr 1; group

theorem formD_equiv [μ.IsMulRightInvariant] (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w)
    (Pr : (G → ℂ) →ₗ[ℂ] testFn G) (hPr : ∀ f : testFn G, Pr f = f) (g : G) (B : Sesq V) (f : G → ℂ)
    (hf : f ∈ testFn G) :
    formD μ hρ hpos hinv Pr ((B ∘ₗ ρ g).compl₂ (ρ g)) f = formD μ hρ hpos hinv Pr B (conjFn g f) := by
  have hcoe : ((biTranslL g g (⟨f, hf⟩ : testFn G) : testFn G) : G → ℂ) = conjFn g f := by
    ext x
    simp [biTranslL, conjFn]
  have h1 : Pr f = ⟨f, hf⟩ := hPr ⟨f, hf⟩
  have h2 : Pr (conjFn g f) = biTranslL g g (⟨f, hf⟩ : testFn G) := by
    rw [← hcoe]
    exact hPr _
  rw [formD_apply, formD_apply, h1, h2]
  obtain ⟨K, hKc, hKf⟩ := exists_K (⟨f, hf⟩ : testFn G)
  have hKo : IsOpen ((K : Subgroup G) : Set G) := K.isOpen
  have hK'c := isCompact_conjSub g hKc
  have hK'o := isOpen_conjSub g hKo
  have hK'f : BiInv (conjSub g (K : Subgroup G)) (biTranslL g g (⟨f, hf⟩ : testFn G) : G → ℂ) := by
    rw [hcoe]
    exact biInv_conj g hKf
  rw [DF_eq μ hρ hpos hinv _ _ hKc hKo hKf, DF_eq μ hρ hpos hinv _ _ hK'c hK'o hK'f]
  haveI := hρ.2 _ hKc hKo
  haveI := hρ.2 _ hK'c hK'o
  have hR : rN μ hρ hpos hK'c hK'o B (biTranslL g g (⟨f, hf⟩ : testFn G)) =
      (conjEquiv (ρ := ρ) g (K : Subgroup G)).conj
        (rN μ hρ hpos hKc hKo ((B ∘ₗ ρ g).compl₂ (ρ g)) ⟨f, hf⟩) := by
    apply riesz_unique hpos (rN_spec μ hρ hpos hK'c hK'o B _)
    intro x' y'
    have hs := rN_spec μ hρ hpos hKc hKo ((B ∘ₗ ρ g).compl₂ (ρ g)) ⟨f, hf⟩
      ((conjEquiv (ρ := ρ) g (K : Subgroup G)).symm x') ((conjEquiv (ρ := ρ) g (K : Subgroup G)).symm y')
    have ex : (((conjEquiv (ρ := ρ) g (K : Subgroup G)).conj
        (rN μ hρ hpos hKc hKo ((B ∘ₗ ρ g).compl₂ (ρ g)) ⟨f, hf⟩) x' : fixedVectors ρ _) : V) =
        ρ g (rN μ hρ hpos hKc hKo ((B ∘ₗ ρ g).compl₂ (ρ g)) ⟨f, hf⟩
          ((conjEquiv (ρ := ρ) g (K : Subgroup G)).symm x')) := by
      rw [LinearEquiv.conj_apply_apply, conjEquiv_apply]
    have ey : (y' : V) = ρ g ((conjEquiv (ρ := ρ) g (K : Subgroup G)).symm y') := by
      rw [← conjEquiv_apply, LinearEquiv.apply_symm_apply]
    have eA : resA μ hρ (conjSub g (K : Subgroup G)) (biTranslL g g (⟨f, hf⟩ : testFn G)) x' =
        ρ g (heckeAct μ ρ f ((conjEquiv (ρ := ρ) g (K : Subgroup G)).symm x')) := by
      rw [conjEquiv_symm_apply]
      simp only [resA, LinearMap.comp_apply, Submodule.subtype_apply, heckeLin_apply]
      exact heckeAct_biTranslL μ hρ.1 g _ _
    rw [ex, ey, hinv, eA]
    simpa [resA, heckeLin_apply] using hs
  simp only [DK]
  rw [hR, LinearMap.trace_conj']

end Eq

end PositivityTheory.PfBern.Unit
