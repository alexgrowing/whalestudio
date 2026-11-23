import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalizedBlowupSeparated
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetOmIsLBOfAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteFiberAmpleTorsionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetBundleTrivialOnFibersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupDivisorTrivialOnFibersStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.BlowQF

theorem rho_over : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (ρ : gen Y ⟶ gen X),
    Y.jQ ≫ ρ = X.jQ → ρ ≫ genStr X = genStr Y := by
  intro E _ _ _ H D l Xo c X Y ρ hjQ
  have hiso : IsIso (genι Y) := by
    show IsIso (pullback.fst Y.s (spMap (RingHom.id c.F)))
    have : IsIso (spMap (RingHom.id c.F)) := by
      show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
      rw [CommRingCat.ofHom_id, Spec.map_id]
      infer_instance
    infer_instance
  have : IsReduced Y.X := by
    haveI : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x => by
      haveI := (Y.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have : IsReduced (gen Y) := isReduced_of_isOpenImmersion (genι Y)
  have : IsDominant Y.jQ := ⟨Y.jQ_dense⟩
  refine ext_of_isDominant_of_isSeparated (terminal.from (Sp c.F)) (terminal.hom_ext _ _) Y.jQ ?_
  rw [← Category.assoc, hjQ]
  exact X.jQ_over.trans Y.jQ_over.symm

theorem finite_preimage_of_blowup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : GlobalTheory.EffCartierData Y.X) (k n : ℕ)
    (ρ : gen Y ⟶ gen X) (X' : Scheme.{0}) (b : X' ⟶ X.X) (q : gen Y ⟶ X'),
    Y.jQ ≫ ρ = X.jQ → GlobalTheory.IsAmpleLB (polOf Y k BY) → 0 < n →
    (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).comap (ρ ≫ genι X) = (BY.idealSheaf ^ n).comap (genι Y) →
    FinalTheorems.Blowup b (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)) → q ≫ b = ρ ≫ genι X →
    ∀ x : X', (q ⁻¹' {x}).Finite := by
  intro E _ _ _ H D l Xo c X Y BY k n ρ X' b q hjQ hA hn hJ hB hq x
  have hρ : ρ ≫ genStr X = genStr Y := rho_over E H D l Xo c X Y ρ hjQ
  have hPY := isProper_genStr Y
  have hPX := isProper_genStr X
  have hρP : IsProper ρ := by
    have : IsProper (ρ ≫ genStr X) := hρ ▸ hPY
    exact IsProper.of_comp ρ (genStr X)
  have hbs : IsSeparated (b ≫ X.s) := by
    have := (blowup_finite_noeth_sep c.F X.X X' X' X.s _ b (𝟙 X') X.proj hB inferInstance).2
    simpa using this
  let T := pullback (b ≫ X.s) (spMap (algebraMap (𝓞 c.F) c.F))
  let u : T ⟶ X' := pullback.fst _ _
  have hw : q ≫ b ≫ X.s = genStr Y ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [← Category.assoc, hq, Category.assoc, pullback.condition, ← Category.assoc, hρ]
  let qF : gen Y ⟶ T := pullback.lift q (genStr Y) hw
  let bF : T ⟶ gen X := pullback.lift (u ≫ b) (pullback.snd _ _) (by simp [u, pullback.condition])
  have hqF : qF ≫ bF = ρ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hq]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hρ]
  have hqu : qF ≫ u = q := pullback.lift_fst _ _ _
  have hbF : IsSeparated bF := by
    have : IsSeparated (bF ≫ genStr X) := by
      show IsSeparated (bF ≫ pullback.snd _ _)
      rw [pullback.lift_snd]; infer_instance
    exact IsSeparated.of_comp bF (genStr X)
  have hqFP : IsProper qF := by
    have : IsProper (qF ≫ bF) := hqF ▸ hρP
    exact IsProper.of_comp qF bF
  have hu : Function.Injective u.base := by
    have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
      IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
    have : IsPreimmersion u := inferInstance
    exact u.isEmbedding.injective
  have hiso : IsIso (genι Y) := by
    show IsIso (pullback.fst Y.s (spMap (RingHom.id c.F)))
    have : IsIso (spMap (RingHom.id c.F)) := by
      show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
      rw [CommRingCat.ofHom_id, Spec.map_id]
      infer_instance
    infer_instance
  have hD : (GlobalTheory.FlagMod.detOm Y).IsLB := GlobalTheory.PolDet.isLB_detOm_of_ample E H D l Xo c c.F (RingHom.id c.F) Y k BY hA
  have hcls : GlobalTheory.CechPic.cls (polOf Y k BY) hA.isLB =
      k • GlobalTheory.CechPic.cls _ hD + -GlobalTheory.CechPic.cls _ BY.isLB_lb := by
    have h1 := GlobalTheory.CechPic.cls_tens (isLB_lbPow hD k) (GlobalTheory.CechPic.isLB_dual BY.isLB_lb) hA.isLB
    rw [GlobalTheory.CechPic.cls_lbPow hD, GlobalTheory.CechPic.cls_dual BY.isLB_lb] at h1
    exact h1
  have hfin : ∀ t : T, (qF ⁻¹' {t}).Finite := by
    intro t
    refine GlobalTheory.T.finite_fiber_ample_torsion qF (genι Y) (polOf Y k BY) hqFP inferInstance hA t ⟨n, hn, ?_⟩
    have hc : qF.fiberι t ≫ qF = qF.fiberToSpecResidueField t ≫ T.fromSpecResidueField t := pullback.condition
    have h3 := GlobalTheory.T.det_bundle_trivial_on_fibers E H D l Xo c X Y ρ hD hjQ (qF.fiber t) (T.residueField t) (qF.fiberι t)
      (qF.fiberToSpecResidueField t) (T.fromSpecResidueField t ≫ bF)
      (by rw [← hqF, ← Category.assoc, hc, Category.assoc])
    have hI : ((((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).comap b).comap q =
        (BY.idealSheaf ^ n).comap (genι Y) := by
      rw [← Scheme.IdealSheafData.comap_comp, hq, hJ]
    have h4 := GlobalTheory.T.blowup_divisor_trivial_on_fibers BY n (genι Y) q _ hiso hB.1 hI (qF.fiber t) (T.residueField t) (qF.fiberι t)
      (qF.fiberToSpecResidueField t) (T.fromSpecResidueField t ≫ u)
      (by rw [← hqu, ← Category.assoc, hc, Category.assoc])
    rw [hcls, map_nsmul, map_add, map_nsmul, map_neg, h3, smul_zero, zero_add, smul_neg, ← map_nsmul, h4, neg_zero]
  by_cases hx : ∃ t : T, u t = x
  · obtain ⟨t, rfl⟩ := hx
    refine (hfin t).subset fun p hp => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hp ⊢
    rw [← hqu, Scheme.Hom.comp_apply] at hp
    exact hu hp
  · convert Set.finite_empty
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    intro hp
    exact hx ⟨qF p, by rw [← Scheme.Hom.comp_apply, hqu, hp]⟩

end GlobalTheory.BlowQF
