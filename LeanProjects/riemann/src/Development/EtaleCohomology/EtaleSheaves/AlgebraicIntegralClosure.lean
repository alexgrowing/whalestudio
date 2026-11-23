import Development.EtaleCohomology.EtaleSheaves.FibreEqvPf
import Development.EtaleCohomology.EtaleSheaves.AICOpenPf
import Development.EtaleCohomology.EtaleSheaves.AlgebraicIntegralClosure.AicLoc

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Polynomial LateralTheory.E.t_E2Cut LateralTheory.E.AICOpenPf

namespace LateralTheory.E.BaseAICPf

theorem aic_of_local {Z : Scheme.{0}} [IsIntegral Z]
    (hloc : ∀ (W : Z.Opens) (y : Z), y ∈ W → ∃ U : Z.Opens, y ∈ U ∧ U ≤ W ∧ AIC Γ(Z, U))
    (W : Z.Opens) (hW : (W : Set Z).Nonempty) : AIC Γ(Z, W) := by
  intro p hm hd
  have : Nonempty W := ⟨⟨_, hW.some_mem⟩⟩
  have hcov : ∀ x : W, ∃ U : Z.Opens, (x : Z) ∈ U ∧ U ≤ W ∧ AIC Γ(Z, U) := fun x => hloc W x x.2
  choose U hxU hUW hUa using hcov
  have hne : ∀ x : W, Nonempty (U x) := fun x => ⟨⟨_, hxU x⟩⟩
  let ψ := Z.germToFunctionField W
  have hroot : ∀ x : W, ∃ β : Z.functionField, (p.map ψ.hom).eval β = 0 := by
    intro x
    have := hne x
    have hA : AIC Γ(Z, U x) := hUa x
    let ρ := (Z.presheaf.map (homOfLE (hUW x)).op).hom
    obtain ⟨r, hr⟩ := hA (p.map ρ) (hm.map ρ) (by rw [hm.natDegree_map]; exact hd)
    refine ⟨Z.germToFunctionField (U x) r, ?_⟩
    rw [← gtf_res_hom (homOfLE (hUW x)), ← Polynomial.map_map, Polynomial.eval_map_apply, hr, map_zero]
  obtain ⟨β, hβ⟩ := hroot ⟨_, hW.some_mem⟩
  have hsec : ∀ x : W, ∃ t : Γ(Z, U x), Z.germToFunctionField (U x) t = β := by
    intro x
    have := hne x
    have hA : AIC Γ(Z, U x) := hUa x
    let ρ := (Z.presheaf.map (homOfLE (hUW x)).op).hom
    exact roots_in (Z.germToFunctionField (U x)).hom hA _ (p.map ρ) rfl (hm.map ρ) β
      (by rw [Polynomial.map_map, gtf_res_hom]; exact hβ)
  choose sf hsf using hsec
  have hcompat : TopCat.Presheaf.IsCompatible Z.sheaf.1 U sf := by
    intro i j
    have := hne i; have := hne j
    have hij : ((U i ⊓ U j : Z.Opens) : Set Z).Nonempty :=
      nonempty_preirreducible_inter (U i).isOpen (U j).isOpen ⟨_, hxU i⟩ ⟨_, hxU j⟩
    have : Nonempty (U i ⊓ U j : Z.Opens) := ⟨⟨_, hij.some_mem⟩⟩
    apply Z.germToFunctionField_injective (U i ⊓ U j)
    change Z.germToFunctionField _ (Z.presheaf.map _ (sf i)) = Z.germToFunctionField _ (Z.presheaf.map _ (sf j))
    rw [gtf_res, gtf_res, hsf, hsf]
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (U := U) (V := W) (iUV := fun x => homOfLE (hUW x))
    (hcover := fun y hy => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxU _⟩) (sf := sf) (h := hcompat)
  have hsβ : ψ s = β := by
    have h0 := hs ⟨_, hW.some_mem⟩
    have := hne ⟨_, hW.some_mem⟩
    rw [← hsf ⟨_, hW.some_mem⟩, ← gtf_res (homOfLE (hUW ⟨_, hW.some_mem⟩)) s]
    exact congrArg _ h0
  obtain ⟨t, ht⟩ : ∃ t : Γ(Z, W), ψ t = β := ⟨s, hsβ⟩
  refine ⟨t, Z.germToFunctionField_injective W ?_⟩
  rw [map_zero]
  have key : ψ.hom (p.eval t) = (p.map ψ.hom).eval (ψ.hom t) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  change ψ.hom (p.eval t) = 0
  rw [key]; change (p.map ψ.hom).eval (ψ t) = 0
  rw [ht]; exact hβ

def BaseInt : Prop := ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S → ∀ x : S, IsIntegral (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0})

def BaseLoc : Prop := ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S → ∀ x : S, ∀ (W : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens)
  (y : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0})), y ∈ W →
  ∃ U : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens, y ∈ U ∧ U ≤ W ∧
    AIC Γ((Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}), U)

def BaseLocLoc : Prop := ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S → ∀ x : S, ∀ (W : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens)
  (y : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0})), y ∈ W →
  ∃ U : (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens, y ∈ U ∧ U ≤ W ∧
    ∃ V : Z.Opens, IsAffineOpen V ∧ (V : Set Z).Nonempty ∧
    ∃ f : Γ(Z, V) →+* Γ((Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}), U), ∃ M : Submonoid Γ(Z, V),
      @IsLocalization _ _ M _ _ f.toAlgebra

theorem BaseLoc_of (h : BaseLocLoc) : BaseLoc := by
  intro Z S c _ _ _ hZ hS x W y hy
  obtain ⟨U, hyU, hUW, V, hV, hne, f, M, hM⟩ := h c hZ hS x W y hy
  letI := f.toAlgebra
  exact ⟨U, hyU, hUW, LateralTheory.E.BaseAICPf.Loc.aic_loc M (hZ.2 V hV hne)⟩

theorem BaseAIC_of (h1 : BaseInt) (h2 : BaseLoc) : LateralTheory.E.FibreEqvPf.BaseAIC := by
  intro Z S c _ _ _ hZ hS x
  have : IsIntegral (Limits.pullback c (S.fromSpecStalk x) : Scheme.{0}) := h1 c hZ hS x
  exact ⟨this, fun U _ hne => aic_of_local (h2 c hZ hS x) U hne⟩

end LateralTheory.E.BaseAICPf
