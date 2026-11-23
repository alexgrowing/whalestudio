import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

theorem eq_top_of_residue {R : Type} {G : Type*} [CommRing R] [AddCommGroup G] [Module R G]
    [Module.Finite R G] [Module.Projective R G] (N : Submodule R (Module.Dual R G))
    (h : ∀ m : Ideal R, m.IsMaximal → ∀ ψ : Module.Dual R G, ∃ χ ∈ N, ∀ x, ψ x - χ x ∈ m) :
    N = ⊤ := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R G
  have hm : ∀ (m : Ideal R) (χ : Module.Dual R G), (∀ x, χ x ∈ m) →
      χ ∈ m • (⊤ : Submodule R (Module.Dual R G)) := fun m χ hχ ↦ by
    have e : χ = ∑ i, χ (f (Pi.single i 1)) • (LinearMap.proj i ∘ₗ g) := by
      ext x
      have e1 : x = f (g x) := (LinearMap.congr_fun hfg x).symm
      conv_lhs => rw [e1, pi_eq_sum_univ' (g x)]
      simp [mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hχ _) Submodule.mem_top
  rw [eq_top_iff]
  intro ψ _
  by_contra hψ
  have hI : N.comap (LinearMap.toSpanSingleton R _ ψ) ≠ ⊤ := fun e ↦ hψ (by
    have : (1 : R) ∈ N.comap (LinearMap.toSpanSingleton R _ ψ) := e ▸ Submodule.mem_top
    simpa using this)
  obtain ⟨m, hmax, hle⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m
    (⊤ : Submodule R (Module.Dual R G ⧸ N)) Module.Finite.fg_top (by
      intro q _
      obtain ⟨φ, rfl⟩ := N.mkQ_surjective q
      obtain ⟨χ, hχ, hx⟩ := h m hmax φ
      have e : N.mkQ φ = N.mkQ (φ - χ) := by
        rw [map_sub, show N.mkQ χ = 0 from (Submodule.Quotient.mk_eq_zero N).2 hχ, sub_zero]
      rw [e, ← Submodule.range_mkQ N, ← Submodule.map_top, ← Submodule.map_smul'']
      exact Submodule.mem_map_of_mem (hm m _ hx))
  have h1 : r ∈ m := hle (by
    have := hr0 (N.mkQ ψ) Submodule.mem_top
    rw [← map_smul] at this
    simpa using (Submodule.Quotient.mk_eq_zero N).1 this)
  exact hmax.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using m.sub_mem h1 hr))

theorem exists_mem_Fil_corr (hF' : AbelianDeRham.Free) (hH : AbelianDeRham.Hodge) (hB : AbelianDeRham.BaseChange)
    {R : Type} [CommRing R] {T : Type} [CommRing T] [Algebra T R]
    (su : Function.Surjective (algebraMap T R)) {C : Over (Sp T)} [GrpObj C] {g : ℕ} (hC : IsAbelianScheme C)
    (gC : SmoothOfRelativeDimension g C.hom) {A : Over (Sp R)} [GrpObj A] {φ : A.left ⟶ C.left}
    (h : IsGrpPullback A C (spMap (algebraMap T R)) φ) {f : HdR A} (hf : f ∈ Fil A) :
    ∃ d ∈ Fil C, (AbelianDeRham.bcMor h).Corr d f := by
  obtain ⟨-, hF⟩ := hB T C g hC gC R A φ h
  obtain ⟨-, ⟨N, hN⟩, -⟩ := hH T C g hC gC
  haveI : Module.Projective T (primDR C) := (hF'.prim hC gC).2.1
  let l : primDR C →ₗ[T] R :=
    { toFun c := f ((AbelianDeRham.bcMor h).pull c)
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun a b => by rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
  obtain ⟨d₀, hd₀⟩ := Module.projective_lifting_property (Algebra.linearMap T R) l su
  have e₀ : ∀ c, algebraMap T R (d₀ c) = f ((AbelianDeRham.bcMor h).pull c) := fun c => LinearMap.congr_fun hd₀ c
  have z : ∀ c ∈ PrimitiveSubmodule C, f ((AbelianDeRham.bcMor h).pull c) = 0 := fun c hc =>
    (Submodule.mem_dualAnnihilator _).1 hf _ (hF ▸ Submodule.subset_span ⟨c, hc, rfl⟩)
  let p : primDR C →ₗ[T] primDR C := N.subtype ∘ₗ N.linearProjOfIsCompl _ hN.symm
  have p0 : ∀ c ∈ PrimitiveSubmodule C, p c = 0 := fun c hc =>
    (congrArg N.subtype (Submodule.linearProjOfIsCompl_apply_right hN.symm ⟨c, hc⟩)).trans (map_zero _)
  have p1 : ∀ c, c - p c ∈ PrimitiveSubmodule C := fun c => by
    obtain ⟨a, b, rfl, -⟩ := Submodule.existsUnique_add_of_isCompl hN c
    have e : p b = b := congrArg N.subtype (Submodule.linearProjOfIsCompl_apply_left hN.symm b)
    rw [map_add, p0 a a.2, e, zero_add, add_sub_cancel_right]
    exact a.2
  refine ⟨d₀ ∘ₗ p, (Submodule.mem_dualAnnihilator _).2 fun c hc => ?_, fun c => ?_⟩
  · rw [LinearMap.comp_apply, p0 c hc, map_zero]
  · rw [LinearMap.comp_apply, e₀, ← sub_eq_zero, ← map_sub, ← map_sub]
    exact z _ (p1 c)

theorem exists_corr (hF' : AbelianDeRham.Free) {R : Type} [CommRing R] {T : Type} [CommRing T] [Algebra T R]
    (su : Function.Surjective (algebraMap T R)) {C : Over (Sp T)} [GrpObj C] {g : ℕ} (hC : IsAbelianScheme C)
    (gC : SmoothOfRelativeDimension g C.hom) {A : Over (Sp R)} [GrpObj A] {φ : A.left ⟶ C.left}
    (h : IsGrpPullback A C (spMap (algebraMap T R)) φ) (f : HdR A) : ∃ d, (AbelianDeRham.bcMor h).Corr d f := by
  haveI : Module.Projective T (primDR C) := (hF'.prim hC gC).2.1
  let l : primDR C →ₗ[T] R :=
    { toFun c := f ((AbelianDeRham.bcMor h).pull c)
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun a b => by rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
  obtain ⟨d₀, hd₀⟩ := Module.projective_lifting_property (Algebra.linearMap T R) l su
  have e₀ : ∀ c, algebraMap T R (d₀ c) = f ((AbelianDeRham.bcMor h).pull c) := fun c => LinearMap.congr_fun hd₀ c
  exact ⟨d₀, fun c ↦ (e₀ c).symm⟩

theorem isPerfPair_of_surjective {R : Type} {G : Type*} [CommRing R] [AddCommGroup G] [Module R G]
    [Module.IsReflexive R G] (ψ : LinearMap.BilinForm R G) (ha : ψ.IsAlt) (hs : Function.Surjective ψ) :
    LinearMap.IsPerfPair ψ := by
  have hi : Function.Injective ψ := (injective_iff_map_eq_zero _).2 fun x hx ↦ by
    refine (Module.bijective_dual_eval R G).1 (LinearMap.ext fun χ ↦ ?_)
    obtain ⟨y, rfl⟩ := hs χ
    rw [Module.Dual.eval_apply, map_zero, LinearMap.zero_apply, ← ha.neg_eq, hx, LinearMap.zero_apply, neg_zero]
  have hf : ∀ x, LinearMap.flip ψ x = ψ (-x) := fun x ↦ LinearMap.ext fun y ↦ by
    rw [LinearMap.flip_apply, map_neg, LinearMap.neg_apply, ha.neg_eq]
  refine ⟨⟨hi, hs⟩, fun x y h ↦ neg_injective (hi (by rw [← hf, ← hf, h])), fun χ ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hs χ
  exact ⟨-y, by rw [hf, neg_neg]⟩

theorem perfect_ring_of (hP : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      ∀ L : LB A.left, L.IsLB → ∀ ψ : LinearMap.BilinForm K (HdR A), IsPolForm (dp0 K) (𝟙 _) A L ψ →
      (∀ x ∈ Fil A, ∀ y ∈ Fil A, ψ x y = 0) → ReciprocityTheory.ChartRestriction.G.Out.KTriv A L → LinearMap.IsPerfPair ψ)
    (hF : AbelianDeRham.Free) (hH : AbelianDeRham.Hodge) (hB : AbelianDeRham.BaseChange) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {L : LB A.left} (hL : L.IsLB) {ψ : LinearMap.BilinForm R (HdR A)} (hψ : IsPolForm (dp0 R) (𝟙 _) A L ψ) (hiso : ∀ x ∈ Fil A, ∀ y ∈ Fil A, ψ x y = 0) (hK : ReciprocityTheory.ChartRestriction.G.Out.KTriv A L) : LinearMap.IsPerfPair ψ := by
  obtain ⟨_, _, -⟩ := hF.prim hA hg
  refine isPerfPair_of_surjective ψ hψ.isAlt (LinearMap.range_eq_top.1 (eq_top_of_residue _ fun m hm χ ↦ ?_))
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have su : Function.Surjective (algebraMap R (R ⧸ m)) := Ideal.Quotient.mk_surjective
  obtain ⟨A', _, φ, h⟩ : ∃ (A' : Over (Sp (R ⧸ m))) (_ : GrpObj A') (φ : A'.left ⟶ A.left),
      IsGrpPullback A' A (spMap (algebraMap R (R ⧸ m))) φ := ⟨_, inferInstance, _, isGrpPullback_pullback A _⟩
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h
  have hg' := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  obtain ⟨ψ', hψ', k⟩ := hψ.pull (AbelianDeRham.bcMor h)
  have hL' : (L.pull φ).IsLB := pull_isLB hL φ
  obtain ⟨w, hw⟩ := GlobalTheory.Cris.ChernExists.lbIso_refl hL'
  have perf := hP (R ⧸ m) A' g hA' hg' _ hL' ψ' hψ' (fun x' hx' y' hy' ↦ by
    obtain ⟨x, hx, ex⟩ := exists_mem_Fil_corr hF hH hB su hA hg h hx'
    obtain ⟨y, hy, ey⟩ := exists_mem_Fil_corr hF hH hB su hA hg h hy'
    rw [k _ _ _ _ ex ey, hiso x hx y hy, map_zero]) (kTriv_pull h hL hL' ((isGen_iff w).1 hw) hK)
  obtain ⟨c, rfl⟩ := (Module.bijective_dual_eval R (primDR A)).2 χ
  obtain ⟨x', hx'⟩ := perf.bijective_left.2 (Module.Dual.eval _ _ ((AbelianDeRham.bcMor h).pull c))
  obtain ⟨x, ex⟩ := exists_corr hF su hA hg h x'
  refine ⟨ψ x, ⟨x, rfl⟩, fun y ↦ ?_⟩
  obtain ⟨y', ey⟩ := (hB R A g hA hg (R ⧸ m) A' φ h).1.exists y
  refine Ideal.Quotient.eq.1 ?_
  have e := k _ _ _ _ ex ey
  rw [hx'] at e
  exact ((ey c).symm.trans e)

end CrystallinePoints.Pd
