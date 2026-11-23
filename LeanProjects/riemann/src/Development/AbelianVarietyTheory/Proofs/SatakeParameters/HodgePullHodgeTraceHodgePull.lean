import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormResFormPullFormPull
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

set_option autoImplicit false

open Opposite TensorProduct Limits GlobalTheory.Points

noncomputable section
namespace GlobalTheory.GalTrace

theorem etTrace_eq_sum {B B' K : Type} [CommRing B] [CommRing B'] [Algebra B B'] [Module.Finite B B']
    [Algebra.Etale B B'] [Field K] [IsAlgClosed K] [Algebra B K] {ι : Type} (R : Finset ι)
    (τ : ι → (B' →ₐ[B] K)) (hinj : Set.InjOn τ R) (hsurj : ∀ t : B' →ₐ[B] K, ∃ r ∈ R, τ r = t)
    (b : B') : algebraMap B K (etTrace B B' b) = ∑ r ∈ R, τ r b := by
  classical
  letI : Algebra B' (K ⊗[B] B') := Algebra.TensorProduct.rightAlgebra
  haveI := projective_of_etale B B'
  have h1 : algTrace K (K ⊗[B] B') (algebraMap B' (K ⊗[B] B') b) = algebraMap B K (etTrace B B' b) :=
    algTrace_of_isPushout b
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed K (K ⊗[B] B')
  haveI : IsArtinianRing (K ⊗[B] B') := .of_finite K _
  letI : Fintype (PrimeSpectrum (K ⊗[B] B')) := Fintype.ofFinite _
  let g : PrimeSpectrum (K ⊗[B] B') → (K ⊗[B] B' →ₐ[K] K) := fun p ↦
    (Pi.evalAlgHom K (fun _ ↦ K) p).comp e.toAlgHom
  let f : PrimeSpectrum (K ⊗[B] B') → (B' →ₐ[B] K) := fun p ↦
    ((g p).restrictScalars B).comp Algebra.TensorProduct.includeRight
  have h2 : ∀ a : PrimeSpectrum (K ⊗[B] B') → K, Algebra.trace K _ a = ∑ p, a p := fun a ↦ by
    rw [Algebra.trace_eq_matrix_trace (Pi.basisFun K _)]
    simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul]
  have hf : Function.Injective f := fun p q h ↦ by
    have h3 : g p = g q := Algebra.TensorProduct.ext (Subsingleton.elim _ _) h
    have h4 : e (e.symm (Pi.single p 1)) p = e (e.symm (Pi.single p 1)) q :=
      AlgHom.congr_fun h3 (e.symm (Pi.single p 1))
    by_contra hne
    rw [e.apply_symm_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)] at h4
    exact one_ne_zero h4
  have hs : ∀ t : B' →ₐ[B] K, ∃ p, f p = t := fun t ↦ by
    let t' : K ⊗[B] B' →ₐ[K] K := Algebra.TensorProduct.lift (AlgHom.id K K) t fun _ _ ↦ .all _ _
    obtain ⟨p, hp⟩ := AlgHom.eq_piEvalAlgHom (t'.comp e.symm.toAlgHom)
    refine ⟨p, AlgHom.ext fun x ↦ ?_⟩
    have : t' (e.symm (e (1 ⊗ₜ x))) = f p x := AlgHom.congr_fun hp (e (1 ⊗ₜ x))
    rw [← this, e.symm_apply_apply]
    simp [t']
  rw [← h1, algTrace_eq_trace, ← Algebra.trace_eq_of_algEquiv e, h2,
    ← Finset.sum_image (g := τ) (f := fun t ↦ t b) hinj]
  have h5 : R.image τ = Finset.univ.image f := by
    ext t
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun _ ↦ hs t, fun _ ↦ hsurj t⟩
  rw [h5, Finset.sum_image hf.injOn]
  rfl

theorem eq_zero_of_valR {W : Scheme.{0}} (sW : W ⟶ Sp ℂ) [LocallyOfFiniteType sW] [IsReduced W]
    {V : W.Opens} (f : Γ(W, V))
    (h : ∀ x : Sp ℂ ⟶ W, x ≫ sW = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ V → valR x V f = 0) : f = 0 := by
  rw [← basicOpen_eq_bot_iff]
  by_contra hne
  have : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace sW
  obtain ⟨c, hc, hcc⟩ := nonempty_inter_closedPoints (Z := (W.basicOpen f : Set W))
    (Set.nonempty_iff_ne_empty.2 fun e ↦ hne (SetLike.coe_injective e))
    (W.basicOpen f).isOpen.isLocallyClosed
  have h1 : ⊤ ≤ pointOfClosedPoint sW c hcc ⁻¹ᵁ W.basicOpen f :=
    (le_preimage_iff _ _).2 ((pointOfClosedPoint_apply sW c hcc _).symm ▸ hc)
  have h2 := le_preimage_mono _ (W.basicOpen_le f) h1
  have h3 := (le_preimage_basicOpen_iff _ h2 f).1 h1
  rw [h _ (pointOfClosedPoint_comp sW c hcc) h2] at h3
  exact not_isUnit_zero h3

theorem exists_lift {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Surjective f] (x : Sp ℂ ⟶ Y) :
    ∃ b : Sp ℂ ⟶ X, b ≫ f = x := by
  have : CompactSpace ↥(pullback f x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f x)
  obtain ⟨p, -⟩ := (pullback.snd f x).surjective (default : PrimeSpectrum ℂ)
  obtain ⟨q, -, hq⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback f x)) ⟨p, trivial⟩
  refine ⟨pointOfClosedPoint (pullback.snd f x) q hq ≫ pullback.fst f x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp,
    Category.id_comp]

theorem valR_secTrace {k : Type} [CommRing k] {Z Y : Scheme.{0}} (s : Z ⟶ Sp k) (s' : Y ⟶ Sp k)
    (c : Y ⟶ Z) [IsFinite c] [Etale c] {U : Z.Opens} (hU : IsAffineOpen U) (z : Sp ℂ ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ U) {ι : Type} (R : Finset ι) (y : ι → (Sp ℂ ⟶ Y)) (hy : ∀ r, y r ≫ c = z)
    (hinj : Set.InjOn y R) (hsurj : ∀ t : Sp ℂ ⟶ Y, t ≫ c = z → ∃ r ∈ R, y r = t)
    (b : Sec s' (c ⁻¹ᵁ U)) :
    valR z U (secTrace s s' hU b) = ∑ r ∈ R, valR (y r) (c ⁻¹ᵁ U) b := by
  letI := secAlg s s' c U
  haveI := sec_finite (s := s) (s' := s') (f := c) hU
  haveI := sec_etale (s := s) (s' := s') (f := c) hU
  letI : Algebra (Sec s U) ℂ := RingHom.toAlgebra (R := Sec s U) (valMap z U hz).hom
  have hm : ∀ r, ⊤ ≤ y r ⁻¹ᵁ (c ⁻¹ᵁ U) := fun r ↦ by
    rw [← Scheme.Hom.comp_preimage, hy r]; exact hz
  let τ : ι → (Sec s' (c ⁻¹ᵁ U) →ₐ[Sec s U] ℂ) := fun r ↦
    { (valMap (y r) (c ⁻¹ᵁ U) (hm r)).hom with
      commutes' := fun a ↦ ((valR_eq (y r) _ (hm r) _).symm.trans (valR_comp (y r) c U a).symm).trans
        (by rw [hy r]; exact valR_eq z U hz a) }
  have hτ : ∀ r (b : Sec s' (c ⁻¹ᵁ U)), τ r b = valR (y r) (c ⁻¹ᵁ U) b :=
    fun r b ↦ (valR_eq (y r) _ (hm r) b).symm
  have key := etTrace_eq_sum R τ (fun r hr r' hr' e ↦ hinj hr hr'
    (ext_of_valR (hU.preimage c) (hm r) (hm r') fun b ↦
      (hτ r b).symm.trans ((AlgHom.congr_fun e b).trans (hτ r' b)))) (fun t ↦ ?_) b
  · exact (valR_eq z U hz _).trans (key.trans (Finset.sum_congr rfl fun r _ ↦ hτ r b))
  · let φ : Γ(Y, c ⁻¹ᵁ U) ⟶ CommRingCat.of ℂ := CommRingCat.ofHom t.toRingHom
    have h1 := le_preimage_specMap_fromSpec (hU.preimage c) φ
    have h2 : ∀ b : Γ(Y, c ⁻¹ᵁ U),
        valR (Spec.map φ ≫ (hU.preimage c).fromSpec) (c ⁻¹ᵁ U) b = t b := fun b ↦ by
      rw [valR_eq _ _ h1, valMap_specMap_fromSpec]; rfl
    obtain ⟨r, hr, e⟩ := hsurj (Spec.map φ ≫ (hU.preimage c).fromSpec)
      (ext_of_valR hU h1 hz fun a ↦ by
        rw [valR_comp, h2, valR_eq z U hz]; exact t.commutes a)
    exact ⟨r, hr, AlgHom.ext fun b ↦ (hτ r b).trans (by rw [e]; exact h2 b)⟩

theorem preimage_le {Z Y W : Scheme.{0}} {c : Y ⟶ Z} {π : W ⟶ Z} {σ : W ⟶ Y} (hσ : σ ≫ c = π)
    (U : Z.Opens) : π ⁻¹ᵁ U ≤ σ ⁻¹ᵁ (c ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, hσ]

section Forms

variable {k : Type} [CommRing k] {Z Y W : Scheme.{0}} {s : Z ⟶ Sp k} {s' : Y ⟶ Sp k}
  {sW : W ⟶ Sp k} {c : Y ⟶ Z} {π : W ⟶ Z}

def liftPull {σ : W ⟶ Y} (hσ : σ ≫ c = π) (hσs : σ ≫ s' = sW) (j : ℕ) :
    (Scheme.Modules.pushforward c).obj (Omega s' j) ⟶
      (Scheme.Modules.pushforward π).obj (Omega sW j) :=
  (Scheme.Modules.pushforward c).map (omegaPull hσs j) ≫
    (Scheme.Modules.pushforwardComp σ c).hom.app _ ≫
      (Scheme.Modules.pushforwardCongr hσ).hom.app _

theorem liftPull_app (hc : c ≫ s = s') (hπ : π ≫ s = sW) {σ : W ⟶ Y} (hσ : σ ≫ c = π)
    (hσs : σ ≫ s' = sW) (j : ℕ) (U : Z.Opens) (b : Sec s' (c ⁻¹ᵁ U)) (x : OmU s U j) :
    (liftPull hσ hσs j).app U (toOm s' j (c ⁻¹ᵁ U) (b • formPull hc U j x)) =
      toOm sW j (π ⁻¹ᵁ U) (Sec.res sW (preimage_le hσ U) (appSec s' sW σ (c ⁻¹ᵁ U) b) •
        formPull hπ U j x) := by
  change (Omega sW j).presheaf.map (homOfLE (preimage_le hσ U)).op
    ((omegaPull hσs j).val.app (op (c ⁻¹ᵁ U))
      ((toOmega s' j).app (op (c ⁻¹ᵁ U)) (b • formPull hc U j x))) = _
  rw [omegaPull_toOmega]
  refine (res_toOm sW j (preimage_le hσ U) (formPull hσs (c ⁻¹ᵁ U) j (b • formPull hc U j x))).trans
    (congrArg (toOm sW j (π ⁻¹ᵁ U)) ?_)
  have h : (σ ≫ c) ≫ s = sW := by rw [hσ, hπ]
  rw [formPull_smul hσs (c ⁻¹ᵁ U) b (formPull hc U j x), formRes_smul,
    formPull_formPull hc hσs h U j x]
  exact congrArg (_ • ·) (formRes_formPull_congr hσ h hπ U (preimage_le hσ U) j x)

theorem sum_app {F G : Z.Modules} {ι : Type} (R : Finset ι) (φ : ι → (F ⟶ G)) (U : Z.Opens)
    (y : Γ(F, U)) : (∑ r ∈ R, φ r).app U y = ∑ r ∈ R, (φ r).app U y := by
  classical
  induction R using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert a R ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Scheme.Modules.Hom.add_app]
    exact congrArg ((φ a).app U y + ·) ih

variable [IsFinite c] [Etale c] (hc : c ≫ s = s') (hπ : π ≫ s = sW) {ι : Type} (R : Finset ι)
  {σ : ι → (W ⟶ Y)} (hσ : ∀ r, σ r ≫ c = π) (hσs : ∀ r, σ r ≫ s' = sW)

theorem omegaTrace_omegaPull
    (hF : ∀ (U : Z.Opens) (hU : IsAffineOpen U) (b : Sec s' (c ⁻¹ᵁ U)),
      appSec s sW π U (secTrace s s' hU b) =
        ∑ r ∈ R, Sec.res sW (preimage_le (hσ r) U) (appSec s' sW (σ r) (c ⁻¹ᵁ U) b)) (j : ℕ) :
    omegaTrace hc j ≫ omegaPull hπ j = ∑ r ∈ R, liftPull (hσ r) (hσs r) j := by
  refine hom_ext_affine fun U hU y ↦ ?_
  obtain ⟨z, rfl⟩ := toOm_surjective (s := s') (j := j) (hU.preimage c) y
  refine formOm_induction (P := fun z ↦ (omegaTrace hc j ≫ omegaPull hπ j).app U
      (toOm s' j (c ⁻¹ᵁ U) z) = (∑ r ∈ R, liftPull (hσ r) (hσs r) j).app U
        (toOm s' j (c ⁻¹ᵁ U) z)) hc hU ?_ (fun y z hy hz ↦ ?_) (fun b x ↦ ?_) z
  · erw [map_zero, map_zero, map_zero]
  · erw [map_add, map_add, map_add]; exact congrArg₂ (· + ·) hy hz
  · refine Eq.trans ?_ (sum_app R _ U _).symm
    refine Eq.trans ?_ (Finset.sum_congr rfl fun r _ ↦
      liftPull_app hc hπ (hσ r) (hσs r) j U b x).symm
    rw [Scheme.Modules.Hom.comp_app]
    change (omegaPull hπ j).val.app (op U)
      ((omegaTrace hc j).app U (toOm s' j (c ⁻¹ᵁ U) (b • formPull hc U j x))) = _
    rw [omegaTrace_toOm_smul_formPull hc j hU, toOm_apply, omegaPull_toOmega, formPull_smul, hF,
      Finset.sum_smul]
    exact map_sum (toOm sW j (π ⁻¹ᵁ U)) _ _

theorem hodgePull_hodgeTrace (j : ℕ)
    (H : omegaTrace hc j ≫ omegaPull hπ j = ∑ r ∈ R, liftPull (hσ r) (hσs r) j) (q : ℕ)
    (x : hodgeH s' j q) :
    hodgePull hπ j q (hodgeTrace hc j q x) = ∑ r ∈ R, hodgePull (hσs r) j q x := by
  letI := algΓ s; letI := algΓ s'; letI := algΓ sW
  obtain ⟨y, rfl⟩ := (coh.pushforwardEquiv k (appTop_algebraMap hc) (Omega s' j) q).surjective x
  have e1 : hodgeTrace hc j q (coh.pushforwardEquiv k (appTop_algebraMap hc) (Omega s' j) q y) =
      cohOn.map k (omegaTrace hc j) ⊤ q y :=
    congrArg (cohOn.map k (omegaTrace hc j) ⊤ q)
      ((coh.pushforwardEquiv k (appTop_algebraMap hc) (Omega s' j) q).symm_apply_apply y)
  have e2 : ∀ φ : (Scheme.Modules.pushforward c).obj (Omega s' j) ⟶
      (Scheme.Modules.pushforward π).obj (Omega sW j),
      cohOn.pull (σ := RingHom.id k) (appTop_algebraMap hπ) (𝟙 _) (le_refl (π ⁻¹ᵁ ⊤)) q
        (cohOn.map k φ ⊤ q y) =
      cohOn.pull (σ := RingHom.id k) (appTop_algebraMap hπ) φ (le_refl (π ⁻¹ᵁ ⊤)) q y := fun φ ↦ by
    rw [cohOn.pull_map, Category.comp_id]
  have e4 := cohOn.pull_map (σ := RingHom.id k) (appTop_algebraMap hπ)
    (omegaPull hπ j) (omegaTrace hc j) (le_refl (π ⁻¹ᵁ ⊤)) (n := q) y
  have e5 : cohOn.map k (∑ r ∈ R, liftPull (hσ r) (hσs r) j) ⊤ q =
      ∑ r ∈ R, cohOn.map k (liftPull (hσ r) (hσs r) j) ⊤ q :=
    map_sum (cohOn.mapAddHom k _ _ ⊤ q) _ _
  rw [H, ← e2, e5, LinearMap.sum_apply, map_sum] at e4
  rw [e1]
  refine e4.trans (Finset.sum_congr rfl fun r _ ↦ (e2 _).trans ?_)
  have h : (σ r ≫ c) ≫ s = sW := by rw [hσ, hπ]
  have s2 := cohOn_pull_pull (appTop_algebraMap hc) (appTop_algebraMap (hσs r))
    (appTop_algebraMap h) (𝟙 _) (omegaPull (hσs r) j) (le_refl (c ⁻¹ᵁ ⊤)) (le_refl _) (le_refl _) q y
  have s3 := cohOn_pull_congr (hσ r) (appTop_algebraMap h) (appTop_algebraMap hπ)
    (G := Omega sW j) (𝟙 ((Scheme.Modules.pushforward c).obj (Omega s' j)) ≫
      (Scheme.Modules.pushforward c).map (omegaPull (hσs r) j) ≫
        (Scheme.Modules.pushforwardComp (σ r) c).hom.app _)
    (V := ⊤) (W := σ r ⁻¹ᵁ (c ⁻¹ᵁ ⊤)) (le_refl _) (fun _ _ ↦ trivial) q y
  have hm : liftPull (hσ r) (hσs r) j = (𝟙 ((Scheme.Modules.pushforward c).obj (Omega s' j)) ≫
      (Scheme.Modules.pushforward c).map (omegaPull (hσs r) j) ≫
        (Scheme.Modules.pushforwardComp (σ r) c).hom.app _) ≫
          (Scheme.Modules.pushforwardCongr (hσ r)).hom.app _ := by
    simp [liftPull]
  rw [hm]
  exact s3.symm.trans s2.symm

end Forms

theorem appSec_secTrace {Z Y W : Scheme.{0}} {s : Z ⟶ Sp ℂ} [Smooth s] {s' : Y ⟶ Sp ℂ}
    {c : Y ⟶ Z} (hc : c ≫ s = s') [IsFinite c] [Etale c] {sW : W ⟶ Sp ℂ} {π : W ⟶ Z}
    (hπ : π ≫ s = sW) {w : W ⟶ Y} (hw : w ≫ c = π) [Surjective w] {G : Type} [Group G]
    {act : G → (W ⟶ W)} (hG : IsGal π hπ G act)
    (hst : ∀ a b : CxPts sW (RingHom.id ℂ),
      a.1 ≫ w = b.1 ≫ w ↔ ∃ g : G, act g ≫ w = w ∧ b.1 = a.1 ≫ act g)
    {R : Finset G} (hR : ∀ g : G, ∃! r, r ∈ R ∧ act g ≫ w = act r ≫ w)
    (hσ : ∀ r, (act r ≫ w) ≫ c = π) (U : Z.Opens) (hU : IsAffineOpen U) (b : Sec s' (c ⁻¹ᵁ U)) :
    appSec s sW π U (secTrace s s' hU b) =
      ∑ r ∈ R, Sec.res sW (preimage_le (hσ r) U) (appSec s' sW (act r ≫ w) (c ⁻¹ᵁ U) b) := by
  have hπf := hG.isFinite
  have hπe := hG.etale
  have hinv := hG.act_comp
  have hmul := hG.act_mul
  have hgal := hG.fibre_cx
  haveI : IsFinite w := by
    have : IsFinite (w ≫ c) := hw ▸ hπf
    exact IsFinite.of_comp w c
  haveI : Smooth sW := by rw [← hπ]; infer_instance
  haveI : IsReduced W := GlobalTheory.isReduced_of_smooth_of_isReduced sW
  rw [← sub_eq_zero]
  refine eq_zero_of_valR sW (V := π ⁻¹ᵁ U) _ fun x hx hxU ↦ ?_
  have hx' : ∀ t : Sp ℂ ⟶ W, t ≫ π = x ≫ π → t ≫ sW = spMap (RingHom.id ℂ) := fun t ht ↦ by
    rw [← hπ, ← Category.assoc, ht, Category.assoc, hπ, hx]
    exact (Spec.map_id _).symm
  have ha : ∀ g, (x ≫ act g) ≫ π = x ≫ π := fun g ↦ by rw [Category.assoc, hinv]
  have key := valR_secTrace s s' c hU (x ≫ π) hxU R (fun r ↦ x ≫ act r ≫ w)
    (fun r ↦ by rw [Category.assoc, hσ]) (fun r hr r' hr' e ↦ ?_) (fun t ht ↦ ?_) b
  · let v : Sec sW (π ⁻¹ᵁ U) →+* ℂ := (valMap x (π ⁻¹ᵁ U) hxU).hom
    have hv : ∀ f : Sec sW (π ⁻¹ᵁ U), valR x (π ⁻¹ᵁ U) f = v f := valR_eq x _ hxU
    rw [hv, map_sub, map_sum, sub_eq_zero, ← hv]
    refine ((valR_comp x π U _).symm.trans key).trans (Finset.sum_congr rfl fun r _ ↦ ?_)
    rw [← hv]
    exact (valR_comp x (act r ≫ w) (c ⁻¹ᵁ U) b).trans
      (valR_res x (preimage_le (hσ r) U) hxU _).symm
  · obtain ⟨g, hg, e'⟩ := (hst ⟨x ≫ act r, hx' _ (ha r)⟩ ⟨x ≫ act r', hx' _ (ha r')⟩).1
      (by simpa only [Category.assoc] using e)
    have e2 : r' = g * r :=
      ((hgal ⟨x, hx' x rfl⟩ ⟨x ≫ act r', hx' _ (ha r')⟩).1 (ha r').symm).unique rfl
        (e'.trans (by rw [hmul, Category.assoc]))
    exact (hR r').unique ⟨hr, by rw [e2, hmul, Category.assoc, hg]⟩ ⟨hr', rfl⟩
  · obtain ⟨x', hx''⟩ := exists_lift w t
    have e1 : x' ≫ π = x ≫ π := by rw [← ht, ← hx'', Category.assoc, hw]
    obtain ⟨g, hg⟩ := ((hgal ⟨x, hx' x rfl⟩ ⟨x', hx' x' e1⟩).1 e1.symm).exists
    obtain ⟨r, hr, e⟩ := (hR g).exists
    refine ⟨r, hr, ?_⟩
    change x' = x ≫ act g at hg
    rw [← e, ← hx'', hg, Category.assoc]

theorem hodgePull_hodgeTrace_hodgePull : ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d s], IsProjOver s →
  ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp ℂ) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1], IsFinite c2 → Etale c2 →
  ∀ (W : Scheme.{0}) (sW : W ⟶ Sp ℂ) (π : W ⟶ Z) (hπ : π ≫ s = sW) (w : W ⟶ Y), w ≫ c1 = π → Surjective w → Surjective π →
  ∀ (G : Type) [Group G] [Fintype G] (act : G → (W ⟶ W)), GlobalTheory.W1.IsGal π hπ G act →
  (∀ a b : CxPts sW (RingHom.id ℂ), a.1 ≫ w = b.1 ≫ w ↔ ∃ g : G, act g ≫ w = w ∧ b.1 = a.1 ≫ act g) →
  ∀ (R : Finset G), (∀ g : G, ∃! r, r ∈ R ∧ act g ≫ w = act r ≫ w) →
  ∀ (hc : ∀ r : G, (act r ≫ w ≫ c2) ≫ s = sW) (a b : ℕ) (x : hodgeH s a b),
  hodgePull hπ a b (hodgeTrace h1 a b (hodgePull h2 a b x)) = ∑ r ∈ R, hodgePull (hc r) a b x := by
  intro Z s d _ _ Y s' c1 c2 h1 h2 _ _ _ _ W sW π hπ w hw hws _ G _ _ act hG hst R hR hc a b x
  haveI : Smooth s := SmoothOfRelativeDimension.smooth d s
  have hσ : ∀ r, (act r ≫ w) ≫ c1 = π := fun r ↦ by rw [Category.assoc, hw, hG.act_comp]
  have hσs : ∀ r, (act r ≫ w) ≫ s' = sW := fun r ↦ by rw [← h1, ← Category.assoc, hσ, hπ]
  rw [hodgePull_hodgeTrace h1 hπ R hσ hσs a (omegaTrace_omegaPull h1 hπ R hσ hσs
    (appSec_secTrace h1 hπ hw hG hst hR hσ) a)]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  have h : ((act r ≫ w) ≫ c2) ≫ s = sW := by rw [Category.assoc (act r), hc]
  have hcongr : ∀ {f f' : W ⟶ Z} (_ : f = f') (hf : f ≫ s = sW) (hf' : f' ≫ s = sW),
      hodgePull hf a b x = hodgePull hf' a b x := fun e _ _ ↦ by subst e; rfl
  exact (hodgePull_comp h2 (hσs r) h a b x).trans (hcongr (Category.assoc _ _ _) _ _)

end GlobalTheory.GalTrace
