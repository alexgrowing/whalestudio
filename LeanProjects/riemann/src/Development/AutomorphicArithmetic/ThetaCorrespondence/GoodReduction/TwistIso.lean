import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtSection
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit.Nos.TwistIsomorphismSections

private theorem appLE_appLE {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (k : Z ⟶ X) (h : g ≫ f = k)
    {U : X.Opens} {V : Y.Opens} {W : Z.Opens} (e : V ≤ f ⁻¹ᵁ U) (e' : W ≤ g ⁻¹ᵁ V) (e'' : W ≤ k ⁻¹ᵁ U)
    (a : Γ(X, U)) :
    (g.appLE V W e').hom ((f.appLE U V e).hom a) = (k.appLE U W e'').hom a := by
  subst h
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]

private theorem isGen_iff_val {X : Scheme.{0}} {A B : LB X} (w : LB.Iso A B) :
    w.IsGen ↔ ∀ (p : B.ι) (q : A.ι) (p' : B.ι) (q' : A.ι),
      resG X (inf_le_left : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ _)
          (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q))).val *
        resG X (inf_le_inf inf_le_right inf_le_right : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ _)
          (A.g q q').val =
      resG X (inf_le_inf inf_le_left inf_le_left : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ _)
          (B.g p p').val *
        resG X (inf_le_right : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ _)
          (@id (Γ(X, B.U p' ⊓ A.U q')ˣ) (w.s (p', q'))).val := by
  have key : ∀ (p : B.ι) (q : A.ι) (p' : B.ι) (q' : A.ι),
      (res (inf_le_left : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ _)
          (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q))) =
        res (inf_le_inf inf_le_left inf_le_left : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ _) (B.g p p') *
          (res (inf_le_inf inf_le_right inf_le_right : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ _)
            (A.g q q'))⁻¹ *
          res (inf_le_right : B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') ≤ _)
            (@id (Γ(X, B.U p' ⊓ A.U q')ˣ) (w.s (p', q')))) ↔ _ := fun p q p' q' => by
    rw [mul_right_comm, eq_mul_inv_iff_mul_eq, Units.ext_iff, Units.val_mul, Units.val_mul]
  exact ⟨fun h p q p' q' => (key p q p' q').1 (h (p, q) (p', q')),
    fun h p p' => (key p.1 p.2 p'.1 p'.2).2 (h p.1 p.2 p'.1 p'.2)⟩

private theorem appTop_cst {X Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (β : Y ⟶ X)
    (f : X ⟶ Sp R) (f' : Y ⟶ Sp R') (c : R →+* R') (h : β ≫ f = f' ≫ spMap c) (r : R) :
    β.appTop (GlobalTheory.AbLaw.cst f ⊤ r) = GlobalTheory.AbLaw.cst f' ⊤ (c r) := by
  simp only [GlobalTheory.AbLaw.cst, RingHom.comp_apply, GlobalTheory.AbLaw.rs_self]
  have h1 := congrArg (fun φ : Y ⟶ Sp R => φ.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) h
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h1
  rw [h1]
  congr 1
  have h2 := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom c))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2.symm

private theorem sum_f {X : Scheme.{0}} {L : LB X} {J : Type} (S : Finset J) (s : J → L.Sec) (i : L.ι) :
    (∑ k ∈ S, s k).f i = ∑ k ∈ S, (s k).f i := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.LB.add_f, ih]

private theorem secPull_f {X Y : Scheme.{0}} {L : LB X} (s : L.Sec) (f : Y ⟶ X) (j : (L.pull f).ι) :
    (GlobalTheory.Cartier.secPull s f).f j =
      (f.appLE _ _ (GlobalTheory.LB.pull_U_le f j)).hom (s.f (j PUnit.unit)) := rfl

private theorem pull_g_val {X Y : Scheme.{0}} {L : LB X} (f : Y ⟶ X) (i j : (L.pull f).ι) :
    ((L.pull f).g i j).val =
      (f.appLE (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) _
        (inf_le_inf (GlobalTheory.LB.pull_U_le f i) (GlobalTheory.LB.pull_U_le f j))).hom
        (L.g (i PUnit.unit) (j PUnit.unit)).val :=
  (GlobalTheory.LB.resG_self le_rfl _).symm.trans (GlobalTheory.LB.resG_pull_g f i j le_rfl)

private theorem ΓSpec_spMap {K : Type} [CommRing K] (σ : K →+* K) (b : Γ(Sp K, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (((spMap σ).appLE ⊤ ⊤ le_top).hom b) =
      σ ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom b) := by
  have h2 := congrArg (fun φ => φ.hom b) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [← h2]
  congr 1

private theorem transport {Y : Scheme.{0}} (ρ : Y ⟶ Y) {A A' B : LB Y} (τ : A'.ι → A.ι)
    (lA : ∀ i, A'.U i ≤ ρ ⁻¹ᵁ A.U (τ i)) (lB : ∀ n, B.U n ≤ ρ ⁻¹ᵁ B.U n)
    (gA : ∀ i j, (A'.g i j).val = (ρ.appLE (A.U (τ i) ⊓ A.U (τ j)) (A'.U i ⊓ A'.U j)
      (inf_le_inf (lA i) (lA j))).hom (A.g (τ i) (τ j)).val)
    (gB : ∀ i j, (B.g i j).val = (ρ.appLE (B.U i ⊓ B.U j) (B.U i ⊓ B.U j)
      (inf_le_inf (lB i) (lB j))).hom (B.g i j).val)
    (w : LB.Iso A B) (hw : w.IsGen) :
    ∃ w₁ : LB.Iso A' B, w₁.IsGen ∧
      (∀ (a : A.Sec) (a' : A'.Sec) (b b' : B.Sec),
        (∀ i, a'.f i = (ρ.appLE _ _ (lA i)).hom (a.f (τ i))) →
        (∀ n, b'.f n = (ρ.appLE _ _ (lB n)).hom (b.f n)) →
        GlobalTheory.Cartier.SecMaps w a b → GlobalTheory.Cartier.SecMaps w₁ a' b') ∧
      ∀ n i, (@id (Γ(Y, B.U n ⊓ A'.U i)ˣ) (w₁.s (n, i))).val =
        (ρ.appLE (B.U n ⊓ A.U (τ i)) (B.U n ⊓ A'.U i) (inf_le_inf (lB n) (lA i))).hom
          (@id (Γ(Y, B.U n ⊓ A.U (τ i))ˣ) (w.s (n, τ i))).val := by
  have lAB : ∀ n i, B.U n ⊓ A'.U i ≤ ρ ⁻¹ᵁ (B.U n ⊓ A.U (τ i)) := fun n i => inf_le_inf (lB n) (lA i)
  let w₁ : LB.Iso A' B :=
    ⟨fun p => Units.map (ρ.appLE _ _ (lAB p.1 p.2)).hom.toMonoidHom (w.s (p.1, τ p.2))⟩
  have hw₁ : ∀ n i, (@id (Γ(Y, B.U n ⊓ A'.U i)ˣ) (w₁.s (n, i))).val =
        (ρ.appLE (B.U n ⊓ A.U (τ i)) (B.U n ⊓ A'.U i) (lAB n i)).hom
          (@id (Γ(Y, B.U n ⊓ A.U (τ i))ˣ) (w.s (n, τ i))).val := fun _ _ => rfl
  refine ⟨w₁, (isGen_iff_val w₁).2 fun n i n' i' => ?_, fun a a' b b' ha hb H p => ?_, hw₁⟩
  · have l : B.U n ⊓ A'.U i ⊓ (B.U n' ⊓ A'.U i') ≤
        ρ ⁻¹ᵁ (B.U n ⊓ A.U (τ i) ⊓ (B.U n' ⊓ A.U (τ i'))) := inf_le_inf (lAB n i) (lAB n' i')
    have e := congrArg (ρ.appLE _ _ l).hom ((isGen_iff_val w).1 hw n (τ i) n' (τ i'))
    rw [map_mul, map_mul, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG,
      GlobalTheory.LB.appLE_resG] at e
    rw [hw₁, hw₁, gA, gB, GlobalTheory.LB.resG_appLE, GlobalTheory.LB.resG_appLE]
    erw [GlobalTheory.LB.resG_appLE, GlobalTheory.LB.resG_appLE]
    exact e
  · obtain ⟨n, i⟩ := p
    have e := congrArg (ρ.appLE _ _ (lAB n i)).hom (H (n, τ i))
    rw [map_mul, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG] at e
    rw [hw₁, ha, hb, GlobalTheory.LB.resG_appLE, GlobalTheory.LB.resG_appLE]
    exact e

end UpperTheory.Lit.Nos.TwistIsomorphismSections

open UpperTheory.Lit.Nos.TwistIsomorphismSections in
theorem UpperTheory.Lit.Nos.twistIso :
    ∀ {X₁ X₂ Y : Scheme.{0}} {K' : Type} [Field K'] (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (q : Y ⟶ Sp K') (ρ : Y ⟶ Y) (φ : X₁ ⟶ X₁) (σ : K' →+* K'), f₁ ≫ φ = ρ ≫ f₁ → ρ ≫ f₂ = f₂ → ρ ≫ q = q ≫ spMap σ → L₁.IsLB → L₂.IsLB → ∀ (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)), w.IsGen → ∃ w₁ : LB.Iso ((L₁.pull φ).pull f₁) (L₂.pull f₂), w₁.IsGen ∧ (∀ (n : ℕ) (s : Fin n → L₂.Sec) (u : L₁.Sec) (c : Fin n → K'), GlobalTheory.Cartier.SecMaps w (GlobalTheory.Cartier.secPull u f₁) (∑ k, GlobalTheory.AbLaw.cst q ⊤ (c k) • GlobalTheory.Cartier.secPull (s k) f₂) → GlobalTheory.Cartier.SecMaps w₁ (GlobalTheory.Cartier.secPull (GlobalTheory.Cartier.secPull u φ) f₁) (∑ k, GlobalTheory.AbLaw.cst q ⊤ (σ (c k)) • GlobalTheory.Cartier.secPull (s k) f₂)) ∧ (∀ x : Sp K' ⟶ Y, x ≫ ρ = spMap σ ≫ x → ∀ (n : (L₂.pull f₂).ι) (i : ((L₁.pull φ).pull f₁).ι) (h : ⊤ ≤ x ⁻¹ᵁ ((L₂.pull f₂).U n ⊓ ((L₁.pull φ).pull f₁).U i)) (h' : ⊤ ≤ x ⁻¹ᵁ ((L₂.pull f₂).U n ⊓ (L₁.pull f₁).U (fun _ => i PUnit.unit PUnit.unit))), (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h).hom (w₁.s (n, i)).val) = σ ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h').hom (w.s (n, fun _ => i PUnit.unit PUnit.unit)).val))) := by
  intro X₁ X₂ Y K' _ L₁ L₂ f₁ f₂ q ρ φ σ h₁ h₂ hq _ _ w hw
  have lB : ∀ n : (L₂.pull f₂).ι, (L₂.pull f₂).U n ≤ ρ ⁻¹ᵁ (L₂.pull f₂).U n := fun n => by
    rw [GlobalTheory.LB.pull_U, ← Scheme.Hom.comp_preimage, h₂]
  let τ : ((L₁.pull φ).pull f₁).ι → (L₁.pull f₁).ι := fun i _ => i PUnit.unit PUnit.unit
  have lA : ∀ i : ((L₁.pull φ).pull f₁).ι, ((L₁.pull φ).pull f₁).U i ≤
      ρ ⁻¹ᵁ (L₁.pull f₁).U (τ i) := fun i => by
    rw [GlobalTheory.LB.pull_U f₁ (τ i), ← Scheme.Hom.comp_preimage, ← h₁, Scheme.Hom.comp_preimage]
    exact (GlobalTheory.LB.pull_U_le f₁ i).trans (f₁.preimage_mono (GlobalTheory.LB.pull_U_le φ _))
  obtain ⟨w₁, hg, hs, hv⟩ := transport ρ τ lA lB (fun i j => by
      have l : ((L₁.pull φ).pull f₁).U i ⊓ ((L₁.pull φ).pull f₁).U j ≤
          (f₁ ≫ φ) ⁻¹ᵁ (L₁.U (i PUnit.unit PUnit.unit) ⊓ L₁.U (j PUnit.unit PUnit.unit)) :=
        inf_le_inf ((GlobalTheory.LB.pull_U_le f₁ i).trans (f₁.preimage_mono (GlobalTheory.LB.pull_U_le φ _)))
          ((GlobalTheory.LB.pull_U_le f₁ j).trans (f₁.preimage_mono (GlobalTheory.LB.pull_U_le φ _)))
      refine (pull_g_val f₁ i j).trans ((congrArg _ (pull_g_val φ _ _)).trans
        ((appLE_appLE f₁ φ _ rfl _ _ l _).trans ?_))
      exact ((congrArg _ (pull_g_val f₁ (τ i) (τ j))).trans (appLE_appLE ρ f₁ _ h₁.symm _ _ l _)).symm)
    (fun i j => (pull_g_val f₂ i j).trans
      ((congrArg _ (pull_g_val f₂ i j)).trans (appLE_appLE ρ f₂ _ h₂ _ _ _ _)).symm) w hw
  refine ⟨w₁, hg, fun m s u c H => hs _ _ _ _ (fun i => ?_) (fun n => ?_) H, fun x hx n i h h' => ?_⟩
  · have l : ((L₁.pull φ).pull f₁).U i ≤ (f₁ ≫ φ) ⁻¹ᵁ L₁.U (i PUnit.unit PUnit.unit) :=
      (GlobalTheory.LB.pull_U_le f₁ i).trans (f₁.preimage_mono (GlobalTheory.LB.pull_U_le φ _))
    exact (appLE_appLE f₁ φ _ rfl (GlobalTheory.LB.pull_U_le φ _) (GlobalTheory.LB.pull_U_le f₁ i) l _).trans
      (appLE_appLE ρ f₁ _ h₁.symm (GlobalTheory.LB.pull_U_le f₁ (τ i)) (lA i) l _).symm
  · rw [sum_f, sum_f, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [GlobalTheory.LB.smul_f, GlobalTheory.LB.smul_f, map_mul, secPull_f, appLE_appLE ρ f₂ _ h₂ _ _ (GlobalTheory.LB.pull_U_le f₂ n),
      GlobalTheory.LB.appLE_resG, ← appTop_cst ρ q q σ hq]
    rfl
  · have e : (x.appLE _ ⊤ h).hom (w₁.s (n, i)).val =
        ((spMap σ).appLE ⊤ ⊤ le_top).hom ((x.appLE _ ⊤ h').hom (w.s (n, τ i)).val) := by
      have l : ⊤ ≤ (x ≫ ρ) ⁻¹ᵁ ((L₂.pull f₂).U n ⊓ (L₁.pull f₁).U (τ i)) :=
        h.trans (x.preimage_mono (inf_le_inf (lB n) (lA i)))
      exact (congrArg _ (hv n i)).trans ((appLE_appLE x ρ _ rfl _ _ l _).trans
        (appLE_appLE (spMap σ) x _ hx.symm _ _ l _).symm)
    exact (congrArg _ e).trans (ΓSpec_spMap σ _)
