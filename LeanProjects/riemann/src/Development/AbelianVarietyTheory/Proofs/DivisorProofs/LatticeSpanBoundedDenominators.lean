import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfMapMemSpanIntegralClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleSectionsFiniteProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc

namespace GlobalTheory.ChainDesc

theorem mem_of_piMap_mem_span {A R L : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing R] [Field L]
    (g : A →+* R) (e : R →+* L) (hg : Function.Injective g) (he : Function.Injective e)
    (hint : ∀ r, (e.comp g).IsIntegralElem (e r)) {n : ℕ} (P : Submodule A (Fin n → A)) [Module.Finite A P]
    [Module.Projective A P] {c : R} (hc : c ≠ 0)
    (hx : ∀ x : Fin n → R, c • x ∈ Submodule.span R (piMap g (Fin n) '' (P : Set _))) (v : Fin n → A)
    (hv : piMap g (Fin n) v ∈ Submodule.span R (piMap g (Fin n) '' (P : Set _))) : v ∈ P := by
  classical
  letI : Algebra A L := (e.comp g).toAlgebra
  have hi : Function.Injective (algebraMap A L) := he.comp hg
  let K := FractionRing A
  letI : Algebra K L := (IsFractionRing.lift (A := A) (K := K) hi).toAlgebra
  have hKL : ∀ a : A, algebraMap K L (algebraMap A K a) = e (g a) := fun a =>
    IsFractionRing.lift_algebraMap (A := A) (K := K) hi a
  haveI : IsScalarTower A K L := .of_algebraMap_eq fun a => (hKL a).symm
  let j : (Fin n → A) →ₗ[A] (Fin n → K) := (Algebra.linearMap A K).compLeft (Fin n)
  have hj : ∀ x i, j x i = algebraMap A K (x i) := fun _ _ => rfl
  have hji : Function.Injective j := fun x y h => funext fun i =>
    IsFractionRing.injective A K (congrFun h i)
  let a := Submodule.equivMapOfInjective j hji P
  have h1 : Module.Finite A (P.map j) := .equiv a
  have h2 : Module.Projective A (P.map j) := .of_equiv a
  have h3 : Submodule.span K (P.map j : Set (Fin n → K)) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
    apply hφ
    have key : ∀ w ∈ Submodule.span R (piMap g (Fin n) '' (P : Set _)),
        ∑ i, e (w i) * algebraMap K L (φ (Pi.single i 1)) = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨u, hu, rfl⟩ := hx
        have h0 : φ (j u) = 0 := by
          have : φ (j u) ∈ (Submodule.span K (P.map j : Set (Fin n → K))).map φ :=
            Submodule.mem_map_of_mem (Submodule.subset_span (Submodule.mem_map_of_mem hu))
          rwa [hφ0, Submodule.mem_bot] at this
        rw [LinearMap.pi_apply_eq_sum_univ] at h0
        have h0' := congrArg (algebraMap K L) h0
        rw [map_sum, map_zero] at h0'
        rw [← h0']
        refine Finset.sum_congr rfl fun i _ => ?_
        have e' : (fun k => if i = k then (1 : K) else 0) = Pi.single i 1 := by
          ext k; simp [Pi.single_apply, eq_comm]
        rw [smul_eq_mul, map_mul, e', hj, hKL]
        rfl
      | zero => simp
      | add x y _ _ hx hy => simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, hx, hy, add_zero]
      | smul b x _ hx =>
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum, hx, mul_zero]
    refine (Pi.basisFun K (Fin n)).ext fun i => ?_
    have h4 := key _ (hx (Pi.single i 1))
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp)] at h4
    have hc' : e c ≠ 0 := fun h => hc (he (h.trans (map_zero e).symm))
    simpa [hc'] using h4
  have h4 : ∀ w ∈ Submodule.span R (piMap g (Fin n) '' (P : Set _)), (fun i => e (w i)) ∈
      Submodule.span (integralClosure A L)
        ((fun (w : Fin n → K) (i : Fin n) => algebraMap K L (w i)) '' (P.map j : Set (Fin n → K))) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      exact Submodule.subset_span ⟨j u, Submodule.mem_map_of_mem hu, funext fun i => hKL (u i)⟩
    | zero =>
      convert Submodule.zero_mem _ using 1
      exact funext fun i => map_zero e
    | add x y _ _ hx hy =>
      convert Submodule.add_mem _ hx hy using 1
      exact funext fun i => map_add e _ _
    | smul b x _ hx =>
      have := Submodule.smul_mem _ (⟨e b, hint b⟩ : integralClosure A L) hx
      convert this using 1
      ext i
      simp [Subalgebra.smul_def]
  have h5 := GlobalTheory.LatticeDescent.mem_of_map_mem_span_integralClosure A K L n (P.map j) h1 h2 h3 (j v) (by
    have := h4 _ hv
    convert this using 1
    exact funext fun i => hKL (v i))
  obtain ⟨u, hu, huv⟩ := h5
  exact hji huv ▸ hu

theorem latOf_eq_comap_of_span : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp), IsCov f g → ∀ (h : ℕ) (E : B'.X.Modules) (ι : E ⟶ freeModule B'.X (Fin h)), GlobalTheory.VB.IsVB E h → Mono ι → ∀ (U : AffOp B.X) (L : Submodule U.Bp (Fin h → U.Bp)) (c : U.Bp), c ≠ 0 → (∀ x : Fin h → U.Bp, c • x ∈ L) → L = Submodule.span U.Bp (piMap (g U) (Fin h) '' (latOf ι (f.f ⁻¹ᵁ U.1) : Set _)) → latOf ι (f.f ⁻¹ᵁ U.1) = L.comap (piMap (g U) (Fin h)) := by
  intro O _ _ _ B B' f g k h E ι hE hι U L c hc hL hs
  subst hs
  haveI := k.1
  have hA := k.isAffineOpen U
  haveI : IsDomain Γ(B'.X, f.f ⁻¹ᵁ U.1) := (k.2.2.1 U).isDomain _
  haveI := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hA
  obtain ⟨h1, h2⟩ := GlobalTheory.T.vector_bundle_sections_finite_projective B'.X E h hE _ hA
  let a := LinearEquiv.ofInjective _ (crd_injective ι (f.f ⁻¹ᵁ U.1))
  haveI : Module.Finite _ (latOf ι (f.f ⁻¹ᵁ U.1)) := .equiv a
  haveI : Module.Projective _ (latOf ι (f.f ⁻¹ᵁ U.1)) := .of_equiv a
  refine le_antisymm (fun x hx => Submodule.mem_comap.2 (Submodule.subset_span (Set.mem_image_of_mem _ hx))) fun x hx => ?_
  refine mem_of_piMap_mem_span (g U) (integralClosure Γ(B.X, U.1) (GlobalTheory.GroupBplus.Kbar B.X)).val.toRingHom (k.2.2.1 U)
    Subtype.val_injective (fun r => ?_) _ hc hL x hx
  obtain ⟨p, hp, hr⟩ := r.2
  refine ⟨p.map (f.f.app U.1).hom, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  convert hr using 2
  · exact RingHom.ext fun y => congrArg Subtype.val (k.2.2.2.1 U y)
  · rfl

end GlobalTheory.ChainDesc
