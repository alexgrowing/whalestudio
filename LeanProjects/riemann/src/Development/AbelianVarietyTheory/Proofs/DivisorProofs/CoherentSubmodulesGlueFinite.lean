import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiMapMemLocalSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoherentSubmoduleSectionsAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLatticeLocalBasisStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open GlobalTheory.QCoh GlobalTheory.PerfdLat GlobalTheory.LatGlue
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)
open GlobalTheory.Twist (resM resM_resM app_resM)
open GlobalTheory.LB (resG_resG)

namespace GlobalTheory.LatGlue

theorem span_image_le_span_range_of_isUnit {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) {h : ℕ}
    (P : Submodule R (Fin h → R)) (g : R) (hg : IsUnit (σ g)) (b : Fin h → Fin h → R)
    (hb : ∀ u ∈ P, ∃ n : ℕ, g ^ n • u ∈ Submodule.span R (Set.range b)) :
    Submodule.span S (piMap σ (Fin h) '' (P : Set (Fin h → R))) ≤
      Submodule.span S (Set.range fun l => piMap σ (Fin h) (b l)) := by
  rw [Submodule.span_le]
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨n, hn⟩ := hb u hu
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hn
  have h1 : σ g ^ n • piMap σ (Fin h) u ∈ Submodule.span S (Set.range fun l => piMap σ (Fin h) (b l)) := by
    rw [← map_pow, ← LinearMap.map_smulₛₗ, ← ha, map_sum]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  exact (Submodule.smul_mem_iff_of_isUnit _ (hg.pow n)).1 h1

theorem eq_zero_of_sum_smul_piMap {R S : Type} [CommRing R] [CommRing S] [IsDomain S] (σ : R →+* S) {h : ℕ}
    (b : Fin h → Fin h → R) (hb : σ (Matrix.of fun a l => b l a).det ≠ 0) (a : Fin h → S)
    (ha : ∑ l, a l • piMap σ (Fin h) (b l) = 0) : a = 0 := by
  rw [RingHom.map_det] at hb
  refine Matrix.eq_zero_of_mulVec_eq_zero hb (funext fun k => ?_)
  have := congrFun ha k
  simp only [Finset.sum_apply, Pi.smul_apply, piMap_apply, smul_eq_mul, Pi.zero_apply] at this
  simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Pi.zero_apply]
  rw [← this]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem isVB_glueSub (Y : Scheme.{0}) [IsIntegral Y] (h : ℕ) (I : Type) (V : I → Y.Opens)
    (P : ∀ i, Submodule Γ(Y, V i) (Fin h → Γ(Y, V i))) (_haff : ∀ i, IsAffineOpen (V i))
    (hcov : ∀ y : Y, ∃ i, y ∈ V i)
    (hdir : ∀ (i j : I) (y : Y), y ∈ V i → y ∈ V j → ∃ k, y ∈ V k ∧ V k ≤ V i ∧ V k ≤ V j)
    (hcomp : ∀ (i k : I) (hle : V k ≤ V i),
      P k = Submodule.span Γ(Y, V k) (piMap (resG Y hle) (Fin h) '' (P i : Set (Fin h → Γ(Y, V i)))))
    (hfp : ∀ i, Module.Finite Γ(Y, V i) (P i) ∧ Module.Projective Γ(Y, V i) (P i))
    (c : Γ(Y, ⊤)) (hc : c ≠ 0)
    (hcP : ∀ i (x : Fin h → Γ(Y, V i)), resG Y (le_top : V i ≤ ⊤) c • x ∈ P i) :
    GlobalTheory.VB.IsVB (glueSub V P).toMod h := by
  intro y
  obtain ⟨i, hy⟩ := hcov y
  have hinj : ∀ {A B : Y.Opens} (hle : B ≤ A) (z : Y), z ∈ B → Function.Injective (resG Y hle) := by
    intro A B hle z hz
    haveI : Nonempty B := ⟨⟨z, hz⟩⟩
    exact map_injective_of_isIntegral Y (homOfLE hle)
  haveI : Nonempty (V i) := ⟨⟨y, hy⟩⟩
  let q : Ideal Γ(Y, V i) :=
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).comap (Y.presheaf.germ (V i) y hy).hom
  have hq : q.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨g, hg, b, hbP, hdet, hspan⟩ := GlobalTheory.T.projective_lattice_local_basis Γ(Y, V i) h (P i) (hfp i).1 (hfp i).2
    (resG Y (le_top : V i ≤ ⊤) c) ((map_ne_zero_iff _ (hinj _ y hy)).2 hc) (hcP i) q hq
  have hyg : y ∈ Y.basicOpen g := by
    rw [Y.mem_basicOpen g y hy]
    by_contra hn
    exact hg ((IsLocalRing.mem_maximalIdeal _).2 hn)
  have h0 : Y.basicOpen g ≤ V i := Y.basicOpen_le g
  have hmem : ∀ l, (coords Y h (Y.basicOpen g)).symm (piMap (resG Y h0) (Fin h) (b l)) ∈
      (glueSub V P).sec (Y.basicOpen g) := by
    intro l z hz
    refine ⟨_, le_rfl, hz, ?_⟩
    rw [GlobalTheory.Twist.resM_self, LinearEquiv.apply_symm_apply]
    exact Submodule.subset_span ⟨i, h0, b l, hbP l, rfl⟩
  refine ⟨Y.basicOpen g, fun l => (glueSub V P).mkSec _ (hmem l), hyg,
    GlobalTheory.VB.isFrame_of_forall_exists fun V' hV' z hz => ?_⟩
  obtain ⟨W, hW, hzW, hWV⟩ := exists_affine_mem_le z hz
  refine ⟨W, hWV, hzW, ?_⟩
  haveI : Nonempty W := ⟨⟨z, hzW⟩⟩
  have hW0 : W ≤ Y.basicOpen g := hWV.trans hV'
  have hWi : W ≤ V i := hW0.trans h0
  let φ : Γ((glueSub V P).toMod, W) →ₗ[Γ(Y, W)] (Fin h → Γ(Y, W)) :=
    (coords Y h W).toLinearMap ∘ₗ appLinear (glueSub V P).incl W
  have hφ : Function.Injective φ := (coords Y h W).injective.comp ((glueSub V P).incl_app_injective W)
  have hφe : ∀ l, φ (resM _ hW0 ((glueSub V P).mkSec _ (hmem l))) = piMap (resG Y hWi) (Fin h) (b l) := by
    intro l
    have e1 : φ (resM _ hW0 ((glueSub V P).mkSec _ (hmem l))) =
        coords Y h W (resM _ hW0 ((coords Y h (Y.basicOpen g)).symm (piMap (resG Y h0) (Fin h) (b l)))) := rfl
    rw [e1, coords_resM, LinearEquiv.apply_symm_apply]
    exact funext fun k => resG_resG h0 hW0 (b l k)
  have hφc : ∀ a : Fin h → Γ(Y, W), φ (Fintype.linearCombination Γ(Y, W)
      (fun l => resM _ hW0 ((glueSub V P).mkSec _ (hmem l))) a) = ∑ l, a l • piMap (resG Y hWi) (Fin h) (b l) := by
    intro a
    simp only [Fintype.linearCombination_apply, map_sum, map_smul, hφe]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    refine eq_zero_of_sum_smul_piMap (resG Y hWi) b ((map_ne_zero_iff _ (hinj _ z hzW)).2 hdet) a ?_
    rw [← hφc, ha, map_zero]
  · intro s
    have hs : φ s ∈ _ := (GlobalTheory.T.coherent_submodule_sections_affine Y h I V P hdir hcomp i W hW hWi _).1 ((glueSub V P).incl_app_mem s)
    have hu : IsUnit (resG Y hWi g) := by
      rw [← resG_resG h0 hW0]
      exact (Y.toRingedSpace.isUnit_res_basicOpen g).map _
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
      (span_image_le_span_range_of_isUnit (resG Y hWi) (P i) g hu b hspan hs)
    exact ⟨a, hφ ((hφc a).trans ha)⟩

end GlobalTheory.LatGlue
