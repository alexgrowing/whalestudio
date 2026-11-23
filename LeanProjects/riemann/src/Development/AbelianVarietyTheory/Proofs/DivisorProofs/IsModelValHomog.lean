import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem DetGen.smul_cancel {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen) {r s : R} (h : r • δ.1 = s • δ.1) : r = s := by
  haveI := Obj.invertible_detOmega X
  refine FaithfulSMul.eq_of_smul_eq_smul (α := X.DetOmega) fun m ↦ ?_
  have hm : m ∈ Submodule.span R {δ.1} := by rw [δ.2]; exact Submodule.mem_top
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hm
  rw [smul_comm r t, smul_comm s t, h]

theorem isModelVal_homog : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
  (r₀ : Rule (rapObj 𝔠) R₀ k) (M : Scheme.{0}) (U : Obj F 𝔠 M) (R : Type) [CommRing R] [Algebra R₀ R]
  (X : Obj F 𝔠 (Sp R)) (δ δ' : X.DetGen) (c v : R), δ'.1 = c • δ.1 → IsModelVal r₀ U X δ' v →
    IsModelVal r₀ U X δ (c ^ k * v) := by
  intro F _ _ 𝔠 R₀ _ k r₀ M U R _ _ X δ δ' c v hδ hv
  intro R' _ _ σ X' φ' δ'' hX' hδ'' W hW Y φY hY δY h hh ψ χ hχ δY' u hY' hu

  have hδm : δ.1 ∈ Submodule.span R {δ'.1} := by rw [δ'.2]; exact Submodule.mem_top
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hδm
  have hdc : d * c = 1 := DetGen.smul_cancel X δ (by rw [mul_smul, ← hδ, hd, one_smul])

  have hgen : Submodule.span R' {((σ : R →+* R') c) • δ''.1} = ⊤ := by
    refine eq_top_iff.2 fun m _ ↦ ?_
    have hm : m ∈ Submodule.span R' {δ''.1} := by rw [δ''.2]; exact Submodule.mem_top
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hm
    refine Submodule.mem_span_singleton.2 ⟨t * (σ : R →+* R') d, ?_⟩
    rw [smul_smul, _root_.mul_assoc, ← map_mul, hdc, map_one, _root_.mul_one]

  have hcorr : Obj.DetCorr (σ : R →+* R') φ' δ'.1 (((σ : R →+* R') c) • δ''.1) := by
    intro w w' hw
    rw [hδ, AlternatingMap.smul_apply, AlternatingMap.smul_apply, smul_eq_mul, smul_eq_mul, hδ'' w w' hw,
      map_mul]
  obtain ⟨δ''', hδ''', huniq⟩ := hX'.existsUnique_detGen (σ : R →+* R') δ'
  have heq : δ'''.1 = ((σ : R →+* R') c) • δ''.1 :=
    (congrArg Subtype.val (huniq ⟨_, hgen⟩ hcorr)).symm
  have hYm : δY'.1 ∈ Submodule.span R' {δ'''.1} := by rw [δ'''.2]; exact Submodule.mem_top
  obtain ⟨u', hu'⟩ := Submodule.mem_span_singleton.1 hYm
  have hval := hv R' σ X' φ' δ''' hX' hδ''' W hW Y φY hY δY h hh ψ χ hχ δY' u' hY' hu'.symm
  have huu : u = u' * (σ : R →+* R') c := DetGen.smul_cancel X' δ'' (by rw [← hu, ← hu', heq, smul_smul])
  rw [huu, mul_pow, map_mul, map_pow, hval]
  simp only [RingHom.coe_coe]
  ring

end GlobalTheory.RealMult
