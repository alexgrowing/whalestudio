import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiMapMemLocalSpan

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent GlobalTheory.LatGlue
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)

namespace GlobalTheory.LatGlue

theorem exists_matrices_of_projective {R : Type} [CommRing R] {h : ℕ} (P : Submodule R (Fin h → R))
    [Module.Finite R P] [Module.Projective R P] (c : R) (hc : ∀ x : Fin h → R, c • x ∈ P) :
    ∃ (m : ℕ) (S : Matrix (Fin m) (Fin h) R) (Q : Matrix (Fin h) (Fin m) R),
      (∀ j, (fun i => Q i j) ∈ P) ∧ (∀ u ∈ P, ∃ r : Fin m → R, S.mulVec u = c • r) ∧
        ∀ x : Fin h → R, Q.mulVec (S.mulVec x) = c • x := by
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' R P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let μ : (Fin h → R) →ₗ[R] P := LinearMap.codRestrict P (c • LinearMap.id) hc
  refine ⟨m, LinearMap.toMatrix' (s ∘ₗ μ), LinearMap.toMatrix' (P.subtype ∘ₗ π), fun j => ?_, fun u hu => ?_, fun x => ?_⟩
  · exact (π (Pi.single j 1)).2
  · refine ⟨s ⟨u, hu⟩, ?_⟩
    rw [LinearMap.toMatrix'_mulVec, ← map_smul]
    rfl
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    exact congrArg Subtype.val (LinearMap.congr_fun hs (μ x))

theorem exists_coeff_of_mem_span {R B : Type} [CommRing R] [CommRing B] [IsDomain B] (ψ : R →+* B) {h m : ℕ}
    (P : Submodule R (Fin h → R)) (c : R) (hc : ψ c ≠ 0) (S : Matrix (Fin m) (Fin h) R) (Q : Matrix (Fin h) (Fin m) R)
    (hS : ∀ u ∈ P, ∃ r : Fin m → R, S.mulVec u = c • r) (hQ : ∀ x : Fin h → R, Q.mulVec (S.mulVec x) = c • x)
    (w : Fin h → B) (hw : w ∈ Submodule.span B {y | ∃ u ∈ P, y = fun i => ψ (u i)}) :
    ∃ t : Fin m → B, (S.map ψ).mulVec w = ψ c • t ∧ w = (Q.map ψ).mulVec t := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨r, hr⟩ := hS u hu
    refine ⟨fun j => ψ (r j), funext fun j => ?_, funext fun i => ?_⟩
    · have := (RingHom.map_mulVec ψ S u j).symm
      rw [hr] at this
      simpa [Function.comp_def] using this
    · have h1 := hQ u
      rw [hr, Matrix.mulVec_smul] at h1
      have h2 := congrArg ψ (congrFun h1 i)
      simp only [Pi.smul_apply, smul_eq_mul, map_mul] at h2
      rw [← mul_left_cancel₀ hc h2, RingHom.map_mulVec]
      rfl
  | zero => exact ⟨0, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨t, h1, h2⟩ := hx
    obtain ⟨t', h1', h2'⟩ := hy
    exact ⟨t + t', by rw [Matrix.mulVec_add, h1, h1', smul_add], by rw [Matrix.mulVec_add, ← h2, ← h2']⟩
  | smul a x _ hx =>
    obtain ⟨t, h1, h2⟩ := hx
    exact ⟨a • t, by rw [Matrix.mulVec_smul, h1, smul_comm], by rw [Matrix.mulVec_smul, ← h2]⟩

theorem comap_eq_span_res : ∀ (X X' : Scheme.{0}) [IsIntegral X] (f : X' ⟶ X) (K' : IntermediateField X.functionField (Kbar X)) (γ : ∀ U : AffOp X, Γ(X', f ⁻¹ᵁ U.1) →+* U.Bp), (∀ U, Function.Injective (γ U)) → (∀ (U U' : AffOp X) (hle : U'.1 ≤ U.1) (a : Γ(X', f ⁻¹ᵁ U.1)), γ U' ((X'.presheaf.map (homOfLE (f.preimage_mono hle)).op).hom a) = AffOp.res hle (γ U a)) → (∀ U, (γ U).range = ringOver K' U) → ∀ (h c : ℕ), (c : Kbar X) ≠ 0 → ∀ (L : ∀ U : AffOp X, Submodule U.Bp (Fin h → U.Bp)), (∀ U, IsDescended K' U (L U) ∧ ∀ x : Fin h → U.Bp, (c : U.Bp) • x ∈ L U) → (∀ (U U' : AffOp X) (hle : U'.1 ≤ U.1), L U' = Submodule.span U'.Bp (piMap (AffOp.res hle) (Fin h) '' (L U : Set (Fin h → U.Bp)))) → ∀ (U U' : AffOp X) (hle : U'.1 ≤ U.1), (L U').comap (piMap (γ U') (Fin h)) = Submodule.span Γ(X', f ⁻¹ᵁ U'.1) (piMap (resG X' (f.preimage_mono hle)) (Fin h) '' ((L U).comap (piMap (γ U) (Fin h)) : Set (Fin h → Γ(X', f ⁻¹ᵁ U.1)))) := by
  intro X X' _ f K' γ hinj hcomp hrange h c hc L hL hres U U' hle
  have hcomp' : ∀ u : Fin h → Γ(X', f ⁻¹ᵁ U.1), piMap (γ U') (Fin h) (piMap (resG X' (f.preimage_mono hle)) (Fin h) u) =
      piMap (AffOp.res hle) (Fin h) (piMap (γ U) (Fin h) u) := fun u => funext fun i => hcomp U U' hle (u i)
  refine le_antisymm (fun v hv => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨⟨hfin, hproj, hspan⟩, hcx⟩ := hL U
    obtain ⟨m, S, Q, hQP, hS, hQ⟩ := exists_matrices_of_projective (descMod K' U (L U)) (c : ringOver K' U) fun x => by
      have := hcx fun i => (x i : U.Bp)
      rw [mem_descMod]
      convert this using 1
      funext i
      simp
    let ψ : ringOver K' U →+* U'.Bp := (AffOp.res hle).comp (ringOver K' U).subtype
    have hψ : ∀ x, ψ x ∈ ringOver K' U' := fun x => x.2
    have hc' : ψ c ≠ 0 := by
      rw [map_natCast]
      intro h0
      apply hc
      simpa using congrArg (algebraMap U'.Bp (Kbar X)) h0
    have hw : piMap (γ U') (Fin h) v ∈
        Submodule.span U'.Bp {y | ∃ u ∈ descMod K' U (L U), y = fun i => ψ (u i)} := by
      have hv' : piMap (γ U') (Fin h) v ∈ L U' := hv
      rw [hres U U' hle] at hv'
      refine Submodule.span_le.2 ?_ hv'
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ L U := hx
      rw [hspan] at hx'
      clear hx
      induction hx' using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, ha, rfl⟩ := hy
        exact Submodule.subset_span ⟨a, ha, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => simpa using add_mem hx hy
      | smul a x _ hx =>
        rw [LinearMap.map_smulₛₗ]
        exact Submodule.smul_mem _ _ hx
    obtain ⟨t, ht, hwt⟩ := exists_coeff_of_mem_span ψ _ _ hc' S Q hS hQ _ hw
    have htK : ∀ j, t j ∈ (γ U').range := fun j => by
      rw [hrange, mem_ringOver]
      have h1 : ψ c * t j ∈ ringOver K' U' := by
        have := congrFun ht j
        rw [Pi.smul_apply, smul_eq_mul] at this
        rw [← this]
        refine Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hψ _) ?_
        rw [← hrange]
        exact ⟨v i, rfl⟩
      rw [mem_ringOver, map_natCast] at h1
      have h2 : (c : Kbar X) * (t j : Kbar X) ∈ K' := by simpa using h1
      have h3 := K'.mul_mem (K'.inv_mem (natCast_mem K' c)) h2
      rwa [inv_mul_cancel_left₀ hc] at h3
    choose r hr using htK
    have hq : ∀ j i, (Q i j : U.Bp) ∈ (γ U).range := fun j i => by
      rw [hrange]; exact (Q i j).2
    choose q hq using hq
    have hv : v = ∑ j, r j • piMap (resG X' (f.preimage_mono hle)) (Fin h) (q j) := by
      funext i
      apply hinj U'
      have h1 := congrFun hwt i
      rw [piMap_apply] at h1
      rw [h1, Finset.sum_apply, map_sum]
      change ∑ j, ψ (Q i j) * t j = _
      refine Finset.sum_congr rfl fun j _ => ?_
      have h2 := congrFun (hcomp' (q j)) i
      rw [piMap_apply] at h2
      rw [Pi.smul_apply, smul_eq_mul, map_mul, hr, h2, piMap_apply, piMap_apply, hq, mul_comm]
      rfl
    rw [hv]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q j, ?_, rfl⟩)
    have h1 : piMap (γ U) (Fin h) (q j) = fun i => (Q i j : U.Bp) := funext fun i => hq j i
    change piMap (γ U) (Fin h) (q j) ∈ L U
    rw [h1]
    exact hQP j
  · rintro _ ⟨u, hu, rfl⟩
    change piMap (γ U') (Fin h) _ ∈ L U'
    rw [hcomp', hres U U' hle]
    exact Submodule.subset_span ⟨_, hu, rfl⟩

end GlobalTheory.LatGlue

end
