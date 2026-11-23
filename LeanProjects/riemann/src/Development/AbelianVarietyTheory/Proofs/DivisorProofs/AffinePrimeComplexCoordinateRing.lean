import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnOfHoloOn
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
open GlobalTheory.IrrAn
open scoped GlobalTheory.AffinePoints

noncomputable section

namespace GlobalTheory.IrrAn

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

section Param

variable {Y : Scheme.{0}} {W : Y.Opens}

theorem mem_primeIdealOf_iff (hW : IsAffineOpen W) (x : W) (a : Γ(Y, W)) :
    a ∈ (hW.primeIdealOf x).asIdeal ↔ (x : Y) ∉ Y.basicOpen a := by
  have h : hW.primeIdealOf x ∈ hW.fromSpec ⁻¹ᵁ Y.basicOpen a ↔ (x : Y) ∈ Y.basicOpen a := by
    rw [← hW.fromSpec_primeIdealOf x]
    rfl
  rw [← h, hW.fromSpec_preimage_basicOpen]
  exact not_not.symm

theorem le_primeIdealOf_iff (hW : IsAffineOpen W) (P : Ideal Γ(Y, W)) (x : Sp ℂ ⟶ Y)
    (hx : ⊤ ≤ x ⁻¹ᵁ W) :
    P ≤ (hW.primeIdealOf ⟨_, (le_preimage_iff x W).1 hx⟩).asIdeal ↔ ∀ a ∈ P, valR x W a = 0 := by
  refine forall₂_congr fun a _ => ?_
  rw [mem_primeIdealOf_iff]
  refine ((le_preimage_iff x _).symm.trans
    ((le_preimage_basicOpen_iff x hx a).trans isUnit_iff_ne_zero)).not.trans not_not

def ptOfHom (hW : IsAffineOpen W) (φ : Γ(Y, W) →+* ℂ) : Sp ℂ ⟶ Y :=
  Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec

theorem ptOfHom_mem (hW : IsAffineOpen W) (φ : Γ(Y, W) →+* ℂ) : ⊤ ≤ ptOfHom hW φ ⁻¹ᵁ W :=
  le_preimage_specMap_fromSpec hW (CommRingCat.ofHom φ)

theorem valR_ptOfHom (hW : IsAffineOpen W) (φ : Γ(Y, W) →+* ℂ) (a : Γ(Y, W)) :
    valR (ptOfHom hW φ) W a = φ a :=
  (valR_eq _ _ (ptOfHom_mem hW φ) a).trans
    (congrArg (fun ψ : Γ(Y, W) ⟶ CommRingCat.of ℂ => ψ.hom a)
      (valMap_specMap_fromSpec hW (CommRingCat.ofHom φ) (ptOfHom_mem hW φ)))

theorem ptOfHom_comp (q : Y ⟶ Sp ℂ) (hW : IsAffineOpen W) (φ : Γ(Y, W) →+* ℂ)
    (h : ∀ a, φ (algX q W a) = a) : ptOfHom hW φ ≫ q = 𝟙 _ :=
  (CxPts.ofHom (p := q) (σ := RingHom.id ℂ) hW φ h).2.trans (Spec.map_id _)

theorem analyticAt_valR_of_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (hW : IsAffineOpen W) {s : E → (Sp ℂ ⟶ Y)} {v : E} (hs : ∀ w, ⊤ ≤ s w ⁻¹ᵁ W)
    (hd : ∀ a : Γ(Y, W), AnalyticAt ℂ (fun w => valR (s w) W a) v) {U : Y.Opens} (f : Γ(Y, U))
    (hv : ⊤ ≤ s v ⁻¹ᵁ U) : AnalyticAt ℂ (fun w => valR (s w) U f) v := by
  obtain ⟨g, hgU, hg⟩ := hW.exists_basicOpen_le (V := U) ⟨_, (le_preimage_iff _ U).1 hv⟩
    ((le_preimage_iff _ W).1 (hs v))
  have hg0 : valR (s v) W g ≠ 0 :=
    ((le_preimage_basicOpen_iff _ (hs v) g).1 ((le_preimage_iff _ _).2 hg)).ne_zero
  have := hW.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g ((Y.presheaf.map (homOfLE hgU).op).hom f)
  refine ((hd a).div ((hd g).pow n) (pow_ne_zero n hg0)).congr ?_
  filter_upwards [(hd g).continuousAt.eventually_ne hg0] with w hw
  have hy : ⊤ ≤ s w ⁻¹ᵁ Y.basicOpen g :=
    (le_preimage_basicOpen_iff _ (hs w) g).2 (isUnit_iff_ne_zero.2 hw)
  have h1 := congrArg (valR (s w) (Y.basicOpen g)) ha
  rw [GlobalTheory.Points.valR_mul _ _ hy, GlobalTheory.Points.valR_pow _ _ hy, GlobalTheory.Points.valR_res _ hgU hy] at h1
  have h2 : ∀ t : Γ(Y, W), valR (s w) (Y.basicOpen g) (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen g) t) =
      valR (s w) W t := fun t => GlobalTheory.Points.valR_res _ (Y.basicOpen_le g) hy t
  rw [h2, h2] at h1
  exact ((eq_div_iff (pow_ne_zero n hw)).2 h1).symm

end Param

theorem exists_param : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (T : Set (Limits.pullback p (spMap σ) : Scheme.{0})) (W : (Limits.pullback p (spMap σ) : Scheme.{0}).Opens) (hW : IsAffineOpen W) (P : Ideal Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W)), (∀ x : W, (x : (Limits.pullback p (spMap σ) : Scheme.{0})) ∈ T ↔ P ≤ (hW.primeIdealOf x).asIdeal) → letI : Algebra ℂ Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (Limits.pullback.snd p (spMap σ)) W).toAlgebra; ∃ ι : ((Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W) ⧸ P) →ₐ[ℂ] ℂ) → CxPts p σ, Topology.IsEmbedding ι ∧ Set.range ι = GlobalTheory.IrrAn.ptsOf p σ (T ∩ (W : Set (Limits.pullback p (spMap σ) : Scheme.{0}))) ∧ ∀ (d' : ℕ) (U : X.Opens) (f : Γ(X, U)) (e : OpenPartialHomeomorph ((Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W) ⧸ P) →ₐ[ℂ] ℂ) (Fin d' → ℂ)), GlobalTheory.AffinePoints.IsAlgebraicChart e → AnalyticOnNhd ℂ (GlobalTheory.CxPts.ev p σ U f ∘ ι ∘ e.symm) (e.target ∩ e.symm ⁻¹' (ι ⁻¹' GlobalTheory.CxPts.ptsIn p σ U)) := by
  intro k _ X p σ T W hW P hT
  letI : Algebra ℂ Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W) :=
    (algX (Limits.pullback.snd p (spMap σ)) W).toAlgebra
  let H := PtsOver.baseChangeHomeomorph (IsPullback.of_hasPullback p (spMap σ))
  let j : ((Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W) ⧸ P) →ₐ[ℂ] ℂ) →
      Pts (Limits.pullback.snd p (spMap σ)) := fun φ =>
    ⟨ptOfHom hW ((φ : _ →+* ℂ).comp (Ideal.Quotient.mk P)),
      ptOfHom_comp _ hW _ fun a => φ.commutes a⟩
  have hjm : ∀ φ, ⊤ ≤ (j φ).1 ⁻¹ᵁ W := fun φ => ptOfHom_mem hW _
  have hjv : ∀ φ a, valR (j φ).1 W a = φ (Ideal.Quotient.mk P a) := fun φ a => valR_ptOfHom hW _ a
  have hpt : ∀ z, pt p σ (H z) = z.1 := fun z =>
    Limits.pullback.hom_ext (Limits.pullback.lift_fst _ _ _)
      ((Limits.pullback.lift_snd _ _ _).trans z.2.symm)
  have hc : Continuous j := by
    refine continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun φ =>
      tendsto_of_isAffineOpen hW (hjm φ) (Eventually.of_forall hjm) fun a => ?_)
    simp only [Function.comp_apply, hjv]
    exact (AffinePoints.continuous_eval _).continuousAt
  have he : Topology.IsEmbedding j := by
    refine ⟨isInducing_of_tendsto hc fun φ l hl => AffinePoints.tendsto_nhds_iff.2 fun b => ?_,
      fun φ ψ h => AlgHom.ext fun b => ?_⟩
    · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
      have h := (GlobalTheory.Points.tendsto_iff.1 (tendsto_subtype_rng.1 hl) W (hjm φ)).2 a
      simp only [hjv] at h
      exact h
    · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [← hjv, ← hjv, h]
  refine ⟨H ∘ j, H.isEmbedding.comp he, Set.ext fun y => ⟨?_, ?_⟩, fun d U f e hE v hv => ?_⟩
  · rintro ⟨φ, rfl⟩
    change pt p σ (H (j φ)) (IsLocalRing.closedPoint ℂ) ∈ T ∩ (W : Set _)
    rw [hpt]
    refine ⟨(hT ⟨_, (le_preimage_iff _ W).1 (hjm φ)⟩).2
      ((le_primeIdealOf_iff hW P _ (hjm φ)).2 fun a ha => ?_), (le_preimage_iff _ W).1 (hjm φ)⟩
    rw [hjv, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  · obtain ⟨z, rfl⟩ := H.surjective y
    intro hz
    change pt p σ (H z) (IsLocalRing.closedPoint ℂ) ∈ T ∩ (W : Set _) at hz
    rw [hpt] at hz
    have hm : ⊤ ≤ z.1 ⁻¹ᵁ W := (le_preimage_iff _ W).2 hz.2
    have h0 := (le_primeIdealOf_iff hW P _ hm).1 ((hT ⟨_, hz.2⟩).1 hz.1)
    let ψ : Γ((Limits.pullback p (spMap σ) : Scheme.{0}), W) →ₐ[ℂ] ℂ :=
      { (valMap z.1 W hm).hom with
        commutes' := fun a => (valR_eq _ _ hm _).symm.trans
          (valR_constFn_of_section _ z.1 z.2 W hm a) }
    refine ⟨Ideal.Quotient.liftₐ P ψ fun a ha => (valR_eq _ _ hm a).symm.trans (h0 a ha),
      congrArg H (Subtype.ext (ext_of_valR hW (hjm _) hm fun a => ?_))⟩
    rw [hjv, valR_eq _ _ hm]
    rfl
  · have h := analyticAt_valR_of_affine hW (s := fun w => (j (e.symm w)).1) (v := v)
      (fun w => hjm _) (fun a => by simp only [hjv]; exact hE.analyticOnNhd _ v hv.1)
      ((Limits.pullback.fst p (spMap σ)).app U f) hv.2
    refine h.congr (Eventually.of_forall fun w => ?_)
    exact (GlobalTheory.Points.valR_comp _ _ U f).symm

end GlobalTheory.IrrAn

end
