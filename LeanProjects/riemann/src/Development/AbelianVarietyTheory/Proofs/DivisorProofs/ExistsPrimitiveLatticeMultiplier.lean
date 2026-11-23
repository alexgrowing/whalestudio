import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualEq
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrderPrimitive

theorem exists_primitive_mul_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X),
    ∃ b : E, (∀ x ∈ L, b * x ∈ L) ∧ IntermediateField.adjoin ℚ {b} = ⊤ := by
  intro E _ _ _ I _ φ L 𝔠 X U
  classical
  set g := Module.finrank ℚ (FR E) with hg
  let emb : E →ₗ[ℚ] (Fin g → ℂ) :=
    { toFun := fun x j => φ (U.e j) x
      map_add' := fun x x' => by funext j; simp
      map_smul' := fun q x => by funext j; simp [Rat.smul_def] }
  have hemb : ∀ x j, emb x j = φ (U.e j) x := fun _ _ => rfl
  have hdc : ∀ x, (fun j => GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord φ 0 x (U.e j)) = emb x := fun x => by
    funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord, hemb]
  have hdim : Module.finrank ℚ E ≤ 2 * g := by
    rw [hg, ← Module.finrank_mul_finrank ℚ (FR E) E, Algebra.IsQuadraticExtension.finrank_eq_two (FR E) E, mul_comm]
  have hgpos : 0 < g := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    omega
  have hinj : Function.Injective emb := fun x y hxy => by
    have := congrFun hxy ⟨0, hgpos⟩
    rw [hemb, hemb] at this
    exact (φ (U.e ⟨0, hgpos⟩)).injective this
  let f : E →ₗ[ℤ] (Fin g → ℂ) := emb.toAddMonoidHom.toIntLinearMap
  have hf : ∀ x, f x = emb x := fun _ => rfl
  have hfinj : Function.Injective f := hinj
  let K : Submodule ℤ E := U.u.Λ.comap f
  have hmemK : ∀ x, x ∈ K ↔ x ∈ L := fun x => by
    show emb x ∈ U.u.Λ ↔ x ∈ L
    rw [U.lat]
    constructor
    · rintro ⟨x', hx', h⟩
      rw [hdc] at h
      exact hinj h ▸ hx'
    · intro hx
      exact ⟨x, hx, (hdc x).symm⟩
  have hmap : Submodule.map f K = U.u.Λ := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hw
      obtain ⟨x, hx, rfl⟩ := (U.lat w).1 hw
      exact ⟨x, (hmemK x).2 hx, by rw [hf, hdc]⟩
  haveI : DiscreteTopology U.u.Λ := U.u.discrete
  haveI : IsZLattice ℝ U.u.Λ := ⟨U.u.full⟩
  have hΛfin : U.u.Λ.FG := Module.Finite.iff_fg.1 (ZLattice.module_finite ℝ U.u.Λ)
  have hKfg : K.FG := Submodule.fg_of_fg_map_injective f hfinj (hmap ▸ hΛfin)
  obtain ⟨T, hTfin, hTspan⟩ := Submodule.fg_def.1 hKfg
  have hsp : Submodule.span ℝ (emb '' (K.toAddSubgroup : Set E)) = ⊤ := by
    have : emb '' (K.toAddSubgroup : Set E) = (U.u.Λ : Set (Fin g → ℂ)) := by
      rw [← hmap]
      ext w
      simp [hf]
    rw [this]
    exact U.u.full
  have full : ∀ x : E, ∃ n : ℕ, 0 < n ∧ n • x ∈ K.toAddSubgroup :=
    GlobalTheory.PeriodLattice.exists_nsmul_mem K.toAddSubgroup emb hdim hsp
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element ℚ E
  choose N hNpos hNmem using fun x : E => full (β * x)
  let Tf := hTfin.toFinset
  let n : ℕ := ∏ t ∈ Tf, N t
  have hnpos : 0 < n := Finset.prod_pos fun t _ => hNpos t
  have hmul : ∀ t ∈ T, (n : E) * β * t ∈ K := by
    intro t ht
    have htT : t ∈ Tf := hTfin.mem_toFinset.2 ht
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N htT
    have e : (n : E) * β * t = m • (N t • (β * t)) := by
      rw [smul_smul, nsmul_eq_mul, mul_comm m, ← hm, _root_.mul_assoc]
    rw [e]
    exact K.smul_of_tower_mem m (hNmem t)
  refine ⟨(n : E) * β, fun x hx => ?_, ?_⟩
  · have hxK : x ∈ K := (hmemK x).2 hx
    have hle : Submodule.span ℤ T ≤ K.comap (LinearMap.mulLeft ℤ ((n : E) * β)) := by
      refine Submodule.span_le.2 fun t ht => ?_
      exact hmul t ht
    rw [hTspan] at hle
    exact (hmemK _).1 (hle hxK)
  · have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hnpos.ne'
    refine top_unique (hβ ▸ IntermediateField.adjoin_simple_le_iff.2 ?_)
    have e : β = algebraMap ℚ E ((n : ℚ)⁻¹) * ((n : E) * β) := by
      rw [← _root_.mul_assoc, map_inv₀, map_natCast, inv_mul_cancel₀ (by exact_mod_cast hnpos.ne'), _root_.one_mul]
    have h2 := mul_mem (IntermediateField.algebraMap_mem (IntermediateField.adjoin ℚ {(n : E) * β}) ((n : ℚ)⁻¹))
      (IntermediateField.mem_adjoin_simple_self ℚ ((n : E) * β))
    rwa [← e] at h2

end GlobalTheory.OrderPrimitive
