import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankEqOfInjectiveOfSpan
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianFormsSameSignatureSameSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LandherrStOfHasseNormSt

open NumberField

namespace GlobalTheory.DataClassCount

open scoped nonZeroDivisors
open Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HermModel

variable {E : Type} [Field E] [NumberField E]

theorem mem_of_forall_mul_smul {V : Type} [AddCommGroup V] [Module E V]
    (AA : Submodule (𝓞 E) E) (hfg : AA.FG) (h0 : AA ≠ ⊥) (N : AddSubmonoid V) (v : V)
    (h : ∀ a ∈ AA, ∀ b : E, (∀ c ∈ AA, ∃ o : 𝓞 E, (o : E) = b * c) → (a * b) • v ∈ N) :
    v ∈ N := by
  let I : FractionalIdeal (𝓞 E)⁰ E := ⟨AA, FractionalIdeal.isFractional_of_fg hfg⟩
  have hI : I ≠ 0 := fun h => h0 ((congrArg FractionalIdeal.coeToSubmodule h).trans
    FractionalIdeal.coe_zero)
  have h1 : (1 : E) ∈ I * I⁻¹ := by
    rw [mul_inv_cancel₀ hI]
    exact FractionalIdeal.one_mem_one _
  have key : ∀ r ∈ I * I⁻¹, r • v ∈ N := by
    intro r hr
    refine FractionalIdeal.mul_induction_on (C := fun r => r • v ∈ N) hr ?_ ?_
    · intro a ha b hb
      refine h a ha b fun c hc => ?_
      exact (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff hI).1 hb c hc)
    · intro x y hx hy
      rw [add_smul]
      exact N.add_mem hx hy
  simpa using key 1 h1

def divLat {r : ℕ} (AA : Submodule (𝓞 E) E) (M : Submodule (𝓞 E) (Fin r → E)) :
    Submodule (𝓞 E) (Fin r → E) where
  carrier := {v | ∀ a ∈ AA, a • v ∈ M}
  add_mem' := fun hx hy a ha => by
    rw [smul_add]; exact M.add_mem (hx a ha) (hy a ha)
  zero_mem' := fun a _ => by rw [smul_zero]; exact M.zero_mem
  smul_mem' := fun c x hx a ha => by
    rw [smul_comm]; exact M.smul_mem c (hx a ha)

theorem smul_mem_divLat {r : ℕ} {AA : Submodule (𝓞 E) E} {M : Submodule (𝓞 E) (Fin r → E)}
    {v : Fin r → E} (hv : v ∈ M) {b : E} (hb : ∀ c ∈ AA, ∃ o : 𝓞 E, (o : E) = b * c) :
    b • v ∈ divLat AA M := by
  intro a ha
  obtain ⟨o, ho⟩ := hb a ha
  rw [smul_smul, mul_comm, ← ho]
  exact M.smul_mem o hv

theorem mem_iff_divLat {r : ℕ} {AA : Submodule (𝓞 E) E} (hfg : AA.FG) (h0 : AA ≠ ⊥)
    (M : Submodule (𝓞 E) (Fin r → E)) (v : Fin r → E) :
    v ∈ M ↔ ∀ b : E, (∀ c ∈ AA, ∃ o : 𝓞 E, (o : E) = b * c) → b • v ∈ divLat AA M := by
  refine ⟨fun hv b hb => smul_mem_divLat hv hb, fun h => ?_⟩
  refine mem_of_forall_mul_smul AA hfg h0 M.toAddSubmonoid v fun a ha b hb => ?_
  rw [mul_smul]
  exact h b hb a ha

theorem isLattice_divLat {r : ℕ} {AA : Submodule (𝓞 E) E} (hfg : AA.FG) (h0 : AA ≠ ⊥)
    {M : Submodule (𝓞 E) (Fin r → E)} (hM : M.FG)
    (hs : Submodule.span E (M : Set (Fin r → E)) = ⊤) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice (divLat AA M) := by
  constructor
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    let f : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := (LinearMap.lsmul E (Fin r → E) a).restrictScalars _
    have hf : Function.Injective f := smul_right_injective _ ha0
    apply Submodule.fg_of_fg_map_injective f hf
    haveI : IsNoetherian (𝓞 E) M := isNoetherian_of_fg_of_noetherian M hM
    refine Submodule.FG.of_le_of_isNoetherian (T := M) ?_
    rintro _ ⟨v, hv, rfl⟩
    exact hv a ha
  · rw [eq_top_iff, ← hs, Submodule.span_le]
    intro v hv
    refine mem_of_forall_mul_smul AA hfg h0 (Submodule.span E _).toAddSubmonoid v fun a _ b hb => ?_
    rw [mul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (smul_mem_divLat hv hb))

variable [IsCMField E]

theorem herm_smul_smul {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (ξ a b : E) (x y : Fin r → E) :
    ξ * FD.herm G (a • x) (b • y) = ξ * FD.herm G x y * a * FD.cc b := by
  rw [herm_smul_left, herm_smul_right]; ring

theorem selfDual_divLat {r : ℕ} {AA : Submodule (𝓞 E) E} (hfg : AA.FG) (h0 : AA ≠ ⊥) (ξ : E)
    (hA : ∀ x : E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ, Algebra.trace ℚ E (ξ * x * a * FD.cc b) = z) ↔
      IsIntegral ℤ x) (G : Matrix (Fin r) (Fin r) E) {M : Submodule (𝓞 E) (Fin r → E)}
    (hM : ∀ v, (∀ y ∈ M, ∃ n : ℤ, Algebra.trace ℚ E (ξ * FD.herm G v y) = n) ↔ v ∈ M) :
    (∀ x ∈ divLat AA M, ∀ y ∈ divLat AA M, IsIntegral ℤ (FD.herm G x y)) ∧
      ∀ x, (∀ y ∈ divLat AA M, IsIntegral ℤ (FD.herm G x y)) → x ∈ divLat AA M := by
  constructor
  · intro x hx y hy
    refine (hA _).1 fun a ha b hb => ?_
    rw [← herm_smul_smul]
    exact (hM _).2 (hx a ha) _ (hy b hb)
  · intro x hx a ha
    refine (hM _).1 fun y hy => ?_
    let N : AddSubmonoid (Fin r → E) :=
      { carrier := {y | ∃ n : ℤ, Algebra.trace ℚ E (ξ * FD.herm G (a • x) y) = n}
        add_mem' := by
          rintro u w ⟨n, hn⟩ ⟨k, hk⟩
          refine ⟨n + k, ?_⟩
          rw [herm_add_right, mul_add, map_add, hn, hk]
          push_cast; rfl
        zero_mem' := ⟨0, by rw [herm_zero_right]; simp⟩ }
    refine mem_of_forall_mul_smul AA hfg h0 N y fun a' ha' b hb => ?_
    change ∃ n : ℤ, _
    rw [mul_smul, herm_smul_smul]
    exact (hA _).2 (hx _ (smul_mem_divLat hy hb)) a ha a' ha'

theorem exists_isometry {H : Host E} (D D' : Datum H) {r : ℕ} (ξ : E)
    (G : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E))
    (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)) (hφ : Function.Injective φ) (hφ' : Function.Injective φ')
    (hE : ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm G (φ x) (φ y)))
    (hE' : ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm G (φ' x) (φ' y)))
    (g : (Fin r → E) ≃ₗ[E] (Fin r → E)) (hg : ∀ x y, FD.herm G (g x) (g y) = FD.herm G x y)
    (hm : ∀ x, x ∈ LinearMap.range φ ↔ g x ∈ LinearMap.range φ') :
    ∃ gam : D.La ≃ₗ[𝓞 E] D'.La, ∀ a b, D'.EF (gam a) (gam b) = D.EF a b := by
  have hmap : (LinearMap.range φ).map
      ((g.restrictScalars (𝓞 E) : (Fin r → E) ≃ₗ[𝓞 E] (Fin r → E)) :
        (Fin r → E) →ₗ[𝓞 E] (Fin r → E)) = LinearMap.range φ' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hm x).1 hx
    · intro hy
      refine ⟨g.symm y, (hm _).2 (by rwa [g.apply_symm_apply]), g.apply_symm_apply y⟩
  let gam : D.La ≃ₗ[𝓞 E] D'.La := ((LinearEquiv.ofInjective φ hφ).trans
    (LinearEquiv.ofSubmodules (g.restrictScalars (𝓞 E)) _ _ hmap)).trans
      (LinearEquiv.ofInjective φ' hφ').symm
  have hgam : ∀ a, φ' (gam a) = g (φ a) := fun a =>
    congrArg Subtype.val ((LinearEquiv.ofInjective φ' hφ').apply_symm_apply _)
  refine ⟨gam, fun a b => ?_⟩
  have : ((D'.EF (gam a) (gam b) : ℤ) : ℚ) = D.EF a b := by
    rw [hE', hE, hgam, hgam, hg]
  exact_mod_cast this

end GlobalTheory.DataClassCount

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open DataClassCount in

theorem card_nonisometric_data_le : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q r : ℕ), r = p + q → ∀ (ξ : E) (AA : Submodule (𝓞 E) E), FD.cc ξ = -ξ → ξ ≠ 0 → AA.FG → AA ≠ ⊥ → (∀ x : E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ, Algebra.trace ℚ E (ξ * x * a * FD.cc b) = z) ↔ IsIntegral ℤ x) → ∀ (m : ℕ) (Di : Fin m → Datum H), (∀ i, (Di i).p = p ∧ (Di i).q = q) → (∀ i j (gam : (Di i).La ≃ₗ[𝓞 E] (Di j).La), (∀ a b, (Di j).EF (gam a) (gam b) = (Di i).EF a b) → i = j) → (m : ℝ) ≤ (1 + 2 * max 1 ((2 * FD.fdeg E * r : ℝ) ^ 4 * FD.dE E ^ 2 / (4 * FD.fdeg E))) ^ (2 * FD.fdeg E * r ^ 2) * (r * max 1 ((2 * FD.fdeg E * r : ℝ) ^ 4 * FD.dE E ^ 2 / (4 * FD.fdeg E))) ^ (2 * FD.fdeg E * r ^ 2) := by
  intro hH E _ _ _ H p q r hr ξ AA hξ hξ0 hfg h0 hA m Di hpq hne
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.cast_zero]
    positivity
  let i0 : Fin m := ⟨0, hm⟩
  obtain ⟨G, φ0, hM0⟩ := GlobalTheory.exists_herm_coord_of_datum E H (Di i0) ξ hξ hξ0 r
    (by rw [(hpq i0).1, (hpq i0).2, hr])
  have hex := fun i => GlobalTheory.model_in_same_space (GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt hH) hH E H
    (Di i0) (Di i) r ξ G φ0 (by rw [(hpq i0).1, (hpq i).1]) (by rw [(hpq i0).2, (hpq i).2]) hξ hM0
  choose φ hφ using hex
  obtain ⟨S, -, hS, hcard, -⟩ := GlobalTheory.exists_finset_selfDual_classes_herm G hM0.2.2.1
  have hcl := fun i => by
    have h := GlobalTheory.HermModel.rank_integral_selfDual E H (Di i) r ξ G (φ i) hξ (hφ i)
    have hsd := selfDual_divLat hfg h0 ξ hA G (M := LinearMap.range (φ i)) fun v => by
      rw [← h.2.2.2 v]
      exact ⟨fun h y => h _ ⟨y, rfl⟩, by rintro h _ ⟨y, rfl⟩; exact h y⟩
    exact hS _ (isLattice_divLat hfg h0 h.2.1 (hφ i).2.1) hsd.1 hsd.2
  choose L hL γ hγ hmem using hcl
  refine le_trans ?_ hcard
  have hinj : Function.Injective L := by
    intro i j hij
    let g : ∀ k : Fin m, (Fin r → E) ≃ₗ[E] (Fin r → E) := fun k =>
      Matrix.toLin'OfInv (γ k).inv_mul (γ k).mul_inv
    have hg : ∀ k x y, FD.herm G (g k x) (g k y) = FD.herm G x y := hγ
    have hgm : ∀ k x, x ∈ L k ↔ g k x ∈ divLat AA (LinearMap.range (φ k)) := hmem
    obtain ⟨gam, hgam⟩ := exists_isometry (Di i) (Di j) ξ G (φ i) (φ j) (hφ i).1 (hφ j).1
      (hφ i).2.2.2.2 (hφ j).2.2.2.2 ((g i).symm.trans (g j))
      (fun x y => by
        rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hg, ← hg i,
          LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
      (fun x => by
        rw [mem_iff_divLat hfg h0, mem_iff_divLat hfg h0]
        refine forall₂_congr fun b _ => ?_
        rw [← map_smul, LinearEquiv.trans_apply, ← hgm, ← hij, hgm, LinearEquiv.apply_symm_apply])
    exact hne i j gam hgam
  have := Finset.card_le_card_of_injOn (s := Finset.univ) (t := S) L (fun i _ => hL i) hinj.injOn
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact_mod_cast this

end GlobalTheory
