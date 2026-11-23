import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsHomogeneousXPowMulAddXPowMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfPullSections
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackOfEquationsLift
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SubmoduleEqTopOfSupSmulOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFormCorrection
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLimitOfSuccessiveCorrections

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Unif.FormalEmb

open MvPolynomial GlobalTheory.Unif.PolyStep

variable {X X' : Scheme.{0}} {R : Type} [CommRing R] {σ : Type}

def vanIdeal (p : X ⟶ Spec (CommRingCat.of R)) {H : LB X} (s : σ → LB.Sec H) : Ideal (MvPolynomial σ R) :=
  ⨅ k : H.ι, RingHom.ker (eval₂Hom (AbLaw.cst p (H.U k)) (fun j => (s j).f k))

theorem mem_vanIdeal (p : X ⟶ Spec (CommRingCat.of R)) {H : LB X} (s : σ → LB.Sec H) (F : MvPolynomial σ R) :
    F ∈ vanIdeal p s ↔ ∀ k : H.ι, eval₂Hom (AbLaw.cst p (H.U k)) (fun j => (s j).f k) F = 0 := by
  simp only [vanIdeal, Ideal.mem_iInf, RingHom.mem_ker]

theorem mem_vanIdeal_of_sat (p : X ⟶ Spec (CommRingCat.of R)) {H : LB X} (s : σ → LB.Sec H)
    (hs : ⨆ i, nonzeroLocus (s i) = ⊤) {F : MvPolynomial σ R}
    (h : ∀ i, ∃ m : ℕ, MvPolynomial.X i ^ m * F ∈ vanIdeal p s) : F ∈ vanIdeal p s := by
  rw [mem_vanIdeal]
  intro k
  refine fn_ext fun y hy => ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs]; trivial)
  obtain ⟨k', hk'⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  have hy' : y ∈ H.U k' := X.basicOpen_le _ hk'
  have u' : IsUnit (gs (𝟙 X) y _ ((s i).f k')) := by
    rw [gs_eq (𝟙 X) y _ hy']
    exact (X.mem_basicOpen _ y hy').1 hk'
  have u : IsUnit (gs (𝟙 X) y _ ((s i).f k)) := by
    rw [gs_sec (s i) (𝟙 X) y hy hy']
    exact (Units.isUnit _).mul u'
  obtain ⟨m, hm⟩ := h i
  have e := congrArg (gsHom (𝟙 X) y _ hy) ((mem_vanIdeal p s _).1 hm k)
  rw [map_mul, map_pow, eval₂Hom_X', map_mul, map_pow, map_zero, gsHom_apply (𝟙 X) y _ hy,
    gsHom_apply (𝟙 X) y _ hy] at e
  rw [(u.pow m).mul_right_eq_zero.1 e, ← gsHom_apply (𝟙 X) y _ hy, map_zero]

theorem mem_vanIdeal_pull {H : LB X} {H' : LB X'} (hH : H.IsLB) {β : X' ⟶ X} {w : LB.Iso H' (H.pull β)}
    {s : σ → LB.Sec H} {s' : σ → LB.Sec H'} (h : ∀ j, Rel β w (s j) (s' j)) (p : X ⟶ Spec (CommRingCat.of R))
    {F : MvPolynomial σ R} {t : ℕ} (hF : F.IsHomogeneous t) (h0 : F ∈ vanIdeal p s) : F ∈ vanIdeal (β ≫ p) s' := by
  rw [mem_vanIdeal] at h0 ⊢
  intro k'
  refine fn_ext fun z hz => ?_
  obtain ⟨k, hk⟩ := exists_chart hH (β z)
  have e := Rel.form h p hF z k k' hk hz
  rw [h0 k, ← gsHom_apply β z _ hk, map_zero] at e
  rw [(Units.isUnit _).mul_right_eq_zero.1 e.symm, ← gsHom_apply (𝟙 X') z _ hz, map_zero]

theorem component_mem_span (S : Set (MvPolynomial σ R)) (hS : ∀ F ∈ S, ∃ t, F.IsHomogeneous t) :
    ∀ F ∈ Ideal.span S, ∀ t, homogeneousComponent t F ∈ Ideal.span S := by
  intro F hF t
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := R)
  have h := Ideal.homogeneous_span (homogeneousSubmodule σ R) S (fun F hF => hS F hF) t hF
  rwa [show (DirectSum.decompose (homogeneousSubmodule σ R) F t : MvPolynomial σ R) = homogeneousComponent t F from
    decomposition.decompose'_apply F t] at h

theorem exists_form_limit [Finite σ] (a : R) [IsAdicComplete (Ideal.span {a}) R] (K : ℕ → Ideal (MvPolynomial σ R))
    (t : ℕ) (h₁ : ∀ e F, F.IsHomogeneous t → F ∈ K (e + 1) → F ∈ K e) (h₂ : ∀ e, C (a ^ (e + 1)) ∈ K e)
    (h₃ : ∀ e F, F.IsHomogeneous t → F ∈ K e → ∃ G, G.IsHomogeneous t ∧ F - C (a ^ (e + 1)) * G ∈ K (e + 1))
    (e : ℕ) (F : MvPolynomial σ R) (hF : F.IsHomogeneous t) (h : F ∈ K e) :
    ∃ F₁ G : MvPolynomial σ R, F₁.IsHomogeneous t ∧ (∀ e', F₁ ∈ K e') ∧ F - F₁ = C (a ^ (e + 1)) * G := by
  haveI : Module.Finite R (homogeneousSubmodule σ R t) := Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)
  haveI := GlobalTheory.isPrecomplete_of_finite (Ideal.span {a}) (homogeneousSubmodule σ R t)
  obtain ⟨x', y, hx', hy⟩ := GlobalTheory.Unif.exists_limit_of_successive_corrections R a (homogeneousSubmodule σ R t)
    (fun e => ((K e).restrictScalars R).comap (homogeneousSubmodule σ R t).subtype)
    (fun e x hx => h₁ e x.1 x.2 hx)
    (fun e x => by
      show a ^ (e + 1) • x.1 ∈ K e
      rw [smul_eq_C_mul]
      exact Ideal.mul_mem_right _ _ (h₂ e))
    (fun e x hx => by
      obtain ⟨G, hG, h⟩ := h₃ e x.1 x.2 hx
      refine ⟨⟨G, hG⟩, ?_⟩
      show x.1 - a ^ (e + 1) • G ∈ K (e + 1)
      rwa [smul_eq_C_mul]) e ⟨F, hF⟩ h
  refine ⟨x'.1, y.1, x'.2, hx', ?_⟩
  rw [← smul_eq_C_mul]
  exact congrArg Subtype.val hy

end GlobalTheory.Unif.FormalEmb

open GlobalTheory.Unif.PolyStep GlobalTheory.Unif.FormalEmb in

theorem GlobalTheory.Unif.exists_projective_of_formal_embedding : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V (IsLocalRing.maximalIdeal V) e)) → (∀ e, Flat (Y e).hom) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e, (∀ j, (∀ z (k : (H (e + 1)).ι) (k' : (H e).ι), (β e) z ∈ (H (e + 1)).U k → z ∈ (H e).U k' → gs (β e) z _ ((s (e + 1) j).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k')))) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ (B : Over (Spec (CommRingCat.of V))) (H' : LB B.left) (s' : Fin (n + 1) → LB.Sec H') (b : ∀ e, (Y e).left ⟶ B.left) (w : ∀ e, LB.Iso (H e) (H'.pull (b e))), H'.IsLB ∧ VeryAmpleBy B.hom H' s' ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ (∀ e, (w e).IsGen ∧ (∀ j, (∀ z (k : (H').ι) (k' : (H e).ι), (b e) z ∈ (H').U k → z ∈ (H e).U k' → gs (b e) z _ ((s' j).f k) = (Geo.Tor.gw (w e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k')))) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) V), F.IsHomogeneous t → (∀ e, (∀ k : (H e).ι, MvPolynomial.eval₂Hom (cst ((Y (e)).hom ≫ thick V (IsLocalRing.maximalIdeal V) (e)) ((H e).U k)) (fun j => (s e j).f k) (F) = 0)) → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (B.hom) ((H').U k)) (fun j => (s' j).f k) (F) = 0) := by
  intro V _ _ _ _ Y β hβ hflat H v hH n s hs hva
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  haveI : IsAdicComplete (Ideal.span {ϖ}) V := hϖ.maximalIdeal_eq ▸ inferInstance
  have hVA : ∀ e, VeryAmpleBy (Y e).hom (H e) (s e) := by
    rintro (_ | e)
    · exact hva
    · obtain ⟨j₀, hj, w, hw, hr⟩ := tower _ Y β hβ H v hH s hs e
      exact GlobalTheory.AbLaw.veryAmpleBy_of_isNilpotent _ _ _ (Ideal.Quotient.factor_surjective _) (nilpotent_ker hϖ _)
        _ _ _ _ j₀ hj _ _ w n _ _ (hH _).1 (hH _).1 ((isGen_iff _).2 hw) hr hva
  have c₁ : ∀ e, β e ≫ (Y (e + 1)).hom ≫ thick V (IsLocalRing.maximalIdeal V) (e + 1) =
      (Y e).hom ≫ thick V (IsLocalRing.maximalIdeal V) e := fun e => by
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  let K : ℕ → Ideal (MvPolynomial (Fin (n + 1)) V) := fun e =>
    vanIdeal ((Y e).hom ≫ thick V (IsLocalRing.maximalIdeal V) e) (s e)
  let S : Set (MvPolynomial (Fin (n + 1)) V) := {F | (∃ t, F.IsHomogeneous t) ∧ ∀ e, F ∈ K e}
  have hS : ∀ e, Ideal.span S ≤ K e := fun e => Ideal.span_le.2 fun F hF => hF.2 e
  obtain ⟨B, f, H', s', hH', hva', hB⟩ := GlobalTheory.ProjQuot.exists_veryAmpleBy_of_ideal V n (Ideal.span S)
    (component_mem_span S fun F hF => hF.1)
  have hB' : ∀ t (F : MvPolynomial (Fin (n + 1)) V), F.IsHomogeneous t → (∀ e, F ∈ K e) → ∀ k : H'.ι,
      MvPolynomial.eval₂Hom (cst f (H'.U k)) (fun j => (s' j).f k) F = 0 := fun t F hF h =>
    (hB t F hF).2 fun i => ⟨0, by rw [pow_zero, _root_.one_mul]; exact Ideal.subset_span ⟨⟨t, hF⟩, h⟩⟩
  choose b w hb hw hr using fun e => GlobalTheory.exists_hom_of_veryAmpleBy V B f H' n s' hH' hva' _
    ((Y e).hom ≫ thick V (IsLocalRing.maximalIdeal V) e) (H e) (s e) (hH e).1 (hVA e).1 (fun t F hF h =>
      (mem_vanIdeal _ _ _).1 (mem_vanIdeal_of_sat _ _ (hVA e).1 fun i =>
        ((hB t F hF).1 h i).imp fun _ hm => hS e hm))
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.Unif.exists_form_correction V ϖ hϖ Y β hβ hflat H v hH n s hs hva
  have hz : ∀ e, Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (e + 1)) (ϖ ^ (e + 1)) = 0 := fun e =>
    Ideal.Quotient.eq_zero_iff_mem.2 ((mem_pow hϖ _ _).2 dvd_rfl)
  refine ⟨Over.mk f, H', s', b, w, hH', hva', fun e => ?_, fun e => ?_, fun e => ⟨hw e, hr e⟩,
    fun t F hF h => hB' t F hF fun e => (mem_vanIdeal _ _ _).2 (h e)⟩
  · refine GlobalTheory.ProjBaseChange.isPullback_of_equations_lift V B f H' n s' hH' hva' _ _ Ideal.Quotient.mk_surjective
      _ (Y e).hom (H e) (s e) (b e) (w e) (hH e).1 (hVA e) (hb e) (hw e) (hr e) t₀ fun t ht F hF h => ?_
    obtain ⟨F₁, G, hF₁, hK, hG⟩ := exists_form_limit ϖ K t
      (fun e F hF h => by
        have := mem_vanIdeal_pull (hH (e + 1)).1 (hs e) _ hF h
        rwa [c₁] at this)
      (fun e => (mem_vanIdeal _ _ _).2 fun k => by
        rw [MvPolynomial.eval₂Hom_C, GlobalTheory.Unif.PolyStep.cst_comp, RingHom.comp_apply, hz, map_zero])
      (fun e F hF h => (ht₀ t ht e F hF ((mem_vanIdeal _ _ _).1 h)).imp fun G hG =>
        ⟨hG.1, (mem_vanIdeal _ _ _).2 hG.2⟩) e F hF ((mem_vanIdeal _ _ _).2 h)
    refine ⟨F₁, hF₁, hB' t F₁ hF₁ hK, ?_⟩
    rw [eq_comm, ← sub_eq_zero, ← map_sub, hG, map_mul, MvPolynomial.map_C, hz, map_zero, zero_mul]
  · have hv := (isGen_iff _).1 (hH e).2
    have hw' := (isGen_iff _).1 (hw (e + 1))
    obtain ⟨w'', T⟩ := exists_comp (hH (e + 1)).1 (w (e + 1)) (v e) hw' hv hH' (hH e).1
    exact GlobalTheory.MapUniq.hom_eq_of_pull_sections V B f H' n s' hH' hva' _ (H e) (s e) _ _ w'' (w e) (hH e).1
      (by rw [Category.assoc, hb, hb, c₁]) ((isGen_iff _).2 (T.pgen_comp (hH (e + 1)).1 hw' hv)) (hw e)
      (fun j => Rel.comp T (hH (e + 1)).1 (hr (e + 1) j) (hs e j)) (hr e)
