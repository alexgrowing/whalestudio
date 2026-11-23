import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesOfIsoOfIsGen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmpleStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SubmoduleEqTopOfSupSmulOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsVeryAmpleH1Zero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFormCorrectionOfVanishingAfterBaseChangeStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Degen.PolyStepLocal

theorem nilpotent_ker {R : Type} [CommRing R] (I : Ideal R) {n : ℕ} (h : I ^ n ≤ I ^ (0 + 1)) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor h)) := by
  refine ⟨n, ?_⟩
  have hk : RingHom.ker (Ideal.Quotient.factor h) ≤ I.map (Ideal.Quotient.mk (I ^ n)) := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one] at hx
    exact Ideal.mem_map_of_mem _ hx
  rw [Ideal.zero_eq_bot, eq_bot_iff]
  refine (Ideal.pow_right_mono hk n).trans ?_
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

theorem exists_h1Zero_pw (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (hH : H.IsLB)
    (hs : VeryAmpleBy f H s) : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → FirstCohomologyVanishes (GlobalTheory.AbLaw.pw H t) := by
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.serre_vanishing_very_ample.1 R X f H m s hH hs H hH
  refine ⟨t₀.toNat + 1, fun t ht => ?_⟩
  obtain ⟨w, hw⟩ := GlobalTheory.Algebraise.lbIso_tw hH ((t : ℤ) - 1)
  have h := H1Iso.firstCohomologyVanishes_of_iso_of_isGen (isLB_tw hH hH _).cover (isLB_pw hH _) w hw (ht₀ _ (by omega))
  rwa [sub_add_cancel] at h

theorem exists_form_lift {σ R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (hg : Function.Surjective g)
    {F : MvPolynomial σ R'} {t : ℕ} (hF : F.IsHomogeneous t) :
    ∃ G : MvPolynomial σ R, G.IsHomogeneous t ∧ MvPolynomial.map g G = F := by
  obtain ⟨G, rfl⟩ := MvPolynomial.map_surjective g hg F
  refine ⟨MvPolynomial.homogeneousComponent t G, MvPolynomial.homogeneousComponent_isHomogeneous t G, ?_⟩
  ext d
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent]
  split_ifs with h
  · rw [MvPolynomial.coeff_map]
  · rw [map_zero, hF.coeff_eq_zero h]

theorem cst_comp_spec {X : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
    (p : X ⟶ Spec (CommRingCat.of R')) (g : R →+* R') (U : X.Opens) :
    AbLaw.cst (p ≫ Spec.map (CommRingCat.ofHom g)) U = (AbLaw.cst p U).comp g := by
  ext a
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [this]

theorem exists_pull_tower {σ R : Type} [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (H : ∀ e, LB (Y e).left) (hH : ∀ e, (H e).IsLB) (s : ∀ e, σ → LB.Sec (H e))
    (hs : ∀ e, GlobalTheory.MorAlg.IsPull (β e) (s (e + 1)) (s e)) (e : ℕ) :
    ∃ j₀ : (Y 0).left ⟶ (Y (e + 1)).left, IsPullback j₀ (Y 0).hom (Y (e + 1)).hom (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega) : I ^ (e + 1 + 1) ≤ I ^ (0 + 1))))) ∧
      GlobalTheory.MorAlg.IsPull j₀ (s (e + 1)) (s 0) := by
  induction e with
  | zero => exact ⟨β 0, hβ 0, hs 0⟩
  | succ e ih =>
    obtain ⟨j₀, hj, hr⟩ := ih
    refine ⟨j₀ ≫ β (e + 1), ?_, GlobalTheory.MorAlg.IsPull.comp (hH _) (hH _) (hH _) (hs (e + 1)) hr⟩
    convert hj.paste_horiz (hβ (e + 1)) using 1
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp]

end GlobalTheory.Degen.PolyStepLocal

open GlobalTheory.Degen.PolyStepLocal in

theorem GlobalTheory.Degen.exists_form_correction_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Flat (Y e).hom) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, (∀ z (k : (H (e + 1)).ι) (k' : (H e).ι), (β e) z ∈ (H (e + 1)).U k → z ∈ (H e).U k' → gs (β e) z _ ((s (e + 1) j).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k'))) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ t₀ : ℕ, ∀ t, t₀ ≤ t → ∀ (e : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ k : (H e).ι, MvPolynomial.eval₂Hom (cst ((Y (e)).hom ≫ thick R I (e)) ((H e).U k)) (fun j => (s e j).f k) (F) = 0) → ∃ G : MvPolynomial (Fin (n + 1)) R, G.IsHomogeneous t ∧ (∀ d, MvPolynomial.coeff d G ∈ I ^ (e + 1)) ∧ (∀ k : (H (e + 1)).ι, MvPolynomial.eval₂Hom (cst ((Y (e + 1)).hom ≫ thick R I (e + 1)) ((H (e + 1)).U k)) (fun j => (s (e + 1) j).f k) (F - G) = 0) := by
  intro R _ _ _ I hI Y β hβ hflat H v hH n s hs hva
  have hle : ∀ r ∈ I ^ (0 + 1), IsLocalRing.residue R r = 0 := fun r hr => by
    rw [zero_add, pow_one] at hr
    exact (IsLocalRing.residue_eq_zero_iff r).2 (IsLocalRing.le_maximalIdeal hI hr)
  let φ : R ⧸ I ^ (0 + 1) →+* IsLocalRing.ResidueField R := Ideal.Quotient.lift _ (IsLocalRing.residue R) hle
  have hφ : Function.Surjective φ := Ideal.Quotient.lift_surjective_of_surjective _ hle IsLocalRing.residue_surjective
  have hP := IsPullback.of_hasPullback (Y 0).hom (Spec.map (CommRingCat.ofHom φ))
  set π := pullback.fst (Y 0).hom (Spec.map (CommRingCat.ofHom φ))
  set f₀ := pullback.snd (Y 0).hom (Spec.map (CommRingCat.ofHom φ))
  have hL := LB.isLB_pull (hH 0).1 π
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.MorAlg.exists_isPull π (hH 0).1 (s 0)
  have hva₀ : VeryAmpleBy f₀ ((H 0).pull π) s₀ := by
    obtain ⟨w, hw, c⟩ := hs₀
    refine GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull _ _ (Y 0).hom (H 0) n (s 0) (hH 0).1 hva _ φ _ f₀ π hP.w ?_ _ w
      s₀ hL hw c
    have : pullback.lift π f₀ hP.w = 𝟙 _ := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.id_comp]
      · rw [pullback.lift_snd, Category.id_comp]
    rw [this]
    infer_instance
  obtain ⟨t₁, ht₁⟩ := exists_h1Zero_pw _ _ f₀ _ n s₀ hL hva₀
  obtain ⟨t₂, ht₂⟩ := GlobalTheory.T.serre_vanishing_very_ample.2 _ _ f₀ _ n s₀ hL hva₀
  refine ⟨max t₁ t₂, fun t ht e F hF hF0 => ?_⟩
  obtain ⟨j₀, hj, w, hw', hr⟩ := exists_pull_tower _ Y β hβ H (fun e => (hH e).1) s
    (fun e => ⟨v e, (hH e).2, hs e⟩) e
  have hvae : VeryAmpleBy (Y (e + 1)).hom (H (e + 1)) (s (e + 1)) :=
    GlobalTheory.AbLaw.veryAmpleBy_of_isNilpotent _ _ _ (Ideal.Quotient.factor_surjective _) (nilpotent_ker I _) _ _ _ _ j₀ hj
      _ _ w n _ _ (hH _).1 (hH _).1 hw' hr hva
  obtain ⟨w₀, hw₀, c₀⟩ := GlobalTheory.MorAlg.IsPull.comp (hH (e + 1)).1 (hH 0).1 hL ⟨w, hw', hr⟩ hs₀
  have hP₀ := hP.paste_horiz hj
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at hP₀
  have hne : I ^ (e + 1 + 1) ≠ ⊤ := fun h => hI (top_unique (h ▸ Ideal.pow_le_self (by omega)))
  have : Nontrivial (R ⧸ I ^ (e + 1 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
  have : IsLocalRing (R ⧸ I ^ (e + 1 + 1)) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have c₁ : β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := by
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  obtain ⟨G₀, hG₀, hc, hz⟩ := GlobalTheory.T.exists_form_correction_of_vanishing_after_baseChange _ _ (Y (e + 1)).hom (hflat _) _ n _ (hH _).1 hvae _ _
    (hφ.comp (Ideal.Quotient.factor_surjective _)) _ _ _ hP₀ _ w₀ s₀ hL hw₀ c₀ t (ht₁ t (le_of_max_le_left ht))
    (ht₂ t (le_of_max_le_right ht)) _ _ _ (β e) (Y e).hom (hβ e) _ (v e) (s e) (hH e).1 (hH e).2 (hs e)
    (MvPolynomial.map (Ideal.Quotient.mk _) F) (hF.map _) (fun k => by
      rw [MvPolynomial.eval₂Hom_map_hom, ← cst_comp_spec, Category.assoc]
      exact (congrArg (fun p => MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst p ((H e).U k)) (fun j => (s e j).f k) F) c₁).trans
        (hF0 k))
  obtain ⟨G, hG, rfl⟩ := exists_form_lift _ Ideal.Quotient.mk_surjective hG₀
  refine ⟨G, hG, fun d => ?_, fun k => ?_⟩
  · have h := hc d
    rw [MvPolynomial.coeff_map, Ideal.Quotient.factor_mk] at h
    exact Ideal.Quotient.eq_zero_iff_mem.1 h
  · have h := hz k
    rw [← map_sub, MvPolynomial.eval₂Hom_map_hom, ← cst_comp_spec] at h
    exact h
