import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsTwoPoints
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsHomogeneousXPowMulAddXPowMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.ProjFlat

open MvPolynomial TopologicalSpace GlobalTheory.ProjSpace GlobalTheory.ProjQuot GlobalTheory.QCoh.Qcqs

section Algebra

variable {R A σ : Type} [CommRing R] [CommRing A] [Algebra R A] {r : σ → A} {i : σ}
  {I : Ideal (MvPolynomial σ R)}

theorem map_eq_zero_of_forms {B : Type} [CommRing B] (θ : MvPolynomial σ R →+* B)
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I)
    (H : ∀ t F, F.IsHomogeneous t → F ∈ I → θ F = 0) {F : MvPolynomial σ R} (hF : F ∈ I) : θ F = 0 := by
  rw [← sum_homogeneousComponent F, map_sum]
  exact Finset.sum_eq_zero fun t _ => H t _ (homogeneousComponent_isHomogeneous t F) (hI F hF t)

theorem ker_aeval (hi : r i = 1) (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I)
    (H : ∀ t (F : MvPolynomial σ R), F.IsHomogeneous t → (aeval r F = 0 ↔ ∃ k, X i ^ k * F ∈ I)) :
    RingHom.ker (aeval (R := R) r) = I ⊔ Ideal.span {X i - 1} := by
  have h1 : Ideal.span {X i - 1} ≤ RingHom.ker (aeval (R := R) r) := by
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_sub, aeval_X, hi, map_one, sub_self]
  refine le_antisymm (fun p hp => ?_) (sup_le (fun F hF => ?_) h1)
  · let K : Ideal (MvPolynomial σ R) := Ideal.span {X i - 1}
    have hq : Ideal.Quotient.mkₐ R K (X i) = 1 :=
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self _)
    obtain ⟨n, G, hG, e⟩ := exists_isHomogeneous_aeval_eq
      (r := fun j => Ideal.Quotient.mkₐ R K (X j)) (i := i) hq p
    have e0 : aeval (fun j => Ideal.Quotient.mkₐ R K (X j)) = Ideal.Quotient.mkₐ R K :=
      algHom_ext fun j => aeval_X _ _
    rw [e0] at e
    have e1 : G - p ∈ K := Ideal.Quotient.eq.1 e
    have e2 : aeval r G = 0 := by
      have := (RingHom.ker (aeval (R := R) r)).add_mem (h1 e1) hp
      rwa [sub_add_cancel] at this
    obtain ⟨k, hk⟩ := (H n G hG).1 e2
    have e3 : (X i ^ k - 1) * G ∈ K := K.mul_mem_right _ (Ideal.mem_span_singleton.2 (by
      simpa using sub_dvd_pow_sub_pow (X i : MvPolynomial σ R) 1 k))
    have e4 : p = X i ^ k * G + -((X i ^ k - 1) * G + (G - p)) := by ring
    rw [e4]
    exact Submodule.add_mem_sup hk (K.neg_mem (K.add_mem e3 e1))
  · exact map_eq_zero_of_forms (RingHomClass.toRingHom (aeval (R := R) r)) hI
      (fun t G hG jG => (H t G hG).2 ⟨0, by rwa [pow_zero, _root_.one_mul]⟩) hF

theorem finitePresentation_chart [Finite σ] (hi : r i = 1) (hr : Function.Surjective (aeval (R := R) r))
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I)
    (H : ∀ t (F : MvPolynomial σ R), F.IsHomogeneous t → (aeval r F = 0 ↔ ∃ k, X i ^ k * F ∈ I))
    (hfg : I.FG) : Algebra.FinitePresentation R A := by
  refine Algebra.FinitePresentation.of_surjective hr ?_
  have := ker_aeval hi hI H
  exact (congrArg Ideal.FG this).mpr (Submodule.FG.sup hfg (Submodule.fg_span_singleton _))

theorem flat_chart (hi : r i = 1) (hr : Function.Surjective (aeval (R := R) r))
    (H : ∀ t (F : MvPolynomial σ R), F.IsHomogeneous t → (aeval r F = 0 ↔ ∃ k, X i ^ k * F ∈ I)) (d : ℕ)
    (hfl : ∀ e ≥ d, Module.Flat R (↥(homogeneousSubmodule σ R e) ⧸
      (I.restrictScalars R).comap (homogeneousSubmodule σ R e).subtype)) : Module.Flat R A := by
  refine Module.Flat.of_forall_isTrivialRelation fun {l f x} h => ?_
  have h0 : ∀ a, ∃ (n : ℕ) (G : MvPolynomial σ R), G.IsHomogeneous n ∧ aeval r G = x a := fun a => by
    obtain ⟨p, hp⟩ := hr (x a)
    rw [← hp]
    exact exists_isHomogeneous_aeval_eq hi p
  choose n G hG eG using h0
  let m := Finset.univ.sup n
  have hG' : ∀ a, (X i ^ (m - n a) * G a).IsHomogeneous m := fun a => by
    have := (isHomogeneous_X_pow (R := R) i (m - n a)).mul (hG a)
    rwa [Nat.sub_add_cancel (Finset.le_sup (f := n) (Finset.mem_univ a))] at this
  have hS : (∑ a, f a • (X i ^ (m - n a) * G a)).IsHomogeneous m :=
    (homogeneousSubmodule σ R m).sum_mem fun a _ => (homogeneousSubmodule σ R m).smul_mem _ (hG' a)
  obtain ⟨k, hk⟩ := (H m _ hS).1 (by simp only [map_sum, map_smul, aeval_X_pow_mul hi, eG, h])
  have := hfl (d + k + m) (by omega)
  let N := (I.restrictScalars R).comap (homogeneousSubmodule σ R (d + k + m)).subtype
  let y : Fin l → homogeneousSubmodule σ R (d + k + m) := fun a =>
    ⟨X i ^ (d + k) * (X i ^ (m - n a) * G a), (isHomogeneous_X_pow i _).mul (hG' a)⟩
  have hy : ∑ a, f a • N.mkQ (y a) = 0 := by
    simp only [← map_smul, ← map_sum]
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    change (homogeneousSubmodule σ R (d + k + m)).subtype _ ∈ I
    have e : (homogeneousSubmodule σ R (d + k + m)).subtype (∑ a, f a • y a) =
        X i ^ d * (X i ^ k * ∑ a, f a • (X i ^ (m - n a) * G a)) := by
      simp only [map_sum, map_smul, Finset.mul_sum, mul_smul_comm, y, Submodule.subtype_apply, pow_add,
        _root_.mul_assoc]
    rw [e]
    exact I.mul_mem_left _ hk
  let θ : (homogeneousSubmodule σ R (d + k + m) ⧸ N) →ₗ[R] A :=
    N.liftQ ((aeval r).toLinearMap ∘ₗ (homogeneousSubmodule σ R (d + k + m)).subtype) fun F hF =>
      (H _ F.1 F.2).2 ⟨0, by rw [pow_zero, _root_.one_mul]; exact hF⟩
  have hθ : ∀ a, θ (N.mkQ (y a)) = x a := fun a => by
    change aeval r (X i ^ (d + k) * (X i ^ (m - n a) * G a)) = _
    rw [aeval_X_pow_mul hi, aeval_X_pow_mul hi, eG]
  obtain ⟨s, c, z, hz, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hy
  refine ⟨s, c, fun j => θ (z j), fun a => ?_, hc⟩
  rw [← hθ, show N.mkQ (y a) = _ from hz a, map_sum]
  simp only [map_smul]

end Algebra

section Geometry

variable {R A : Type} [CommRing R] [CommRing A] {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

theorem baseRingHom_spMap (c : R →+* A) (W : (Sp A).Opens) :
    (baseRingHom (spMap c) W).hom = (fnOn W).comp c := by
  have h := baseRingHom_comp_SpecMap (𝟙 (Sp A)) (CommRingCat.ofHom c) W
  rw [Category.id_comp] at h
  exact congrArg CommRingCat.Hom.hom h

theorem appLE_pt_aeval (c : R →+* A) (v : Fin (n + 1) → A) (hv : Ideal.span (Set.range v) = ⊤) (i : Fin (n + 1))
    {W : (Sp A).Opens} (h : W ≤ pt c v hv ⁻¹ᵁ chart R n i) {t : ℕ} {G : MvPolynomial (Fin (n + 1)) R}
    (hG : G.IsHomogeneous t) :
    ((pt c v hv).appLE _ W h).hom (aeval (ratio R n i) G) * fnOn W (v i) ^ t = fnOn W (eval₂ c v G) := by
  have e := congrArg (fun θ => θ G) (appLE_comp_aeval_ratio (φ := pt c v hv) (hi := h))
  rw [pt_str, baseRingHom_spMap] at e
  refine (congrArg (· * _) e).trans ?_
  rw [eval₂_comp_left, coe_eval₂Hom, ← ReciprocityTheory.AnForm.R.eval₂_mul_const_of_isHomogeneous _ _ _ hG]
  exact congrArg (eval₂ _ · G) (funext fun j => pullRatio_pt_mul c v hv i j h)

theorem formIdeal_le_ker_pt_iff (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (c : R →+* A) (v : Fin (n + 1) → A)
    (hv : Ideal.span (Set.range v) = ⊤) :
    formIdeal J ≤ (pt c v hv).ker ↔ ∀ t G, G.IsHomogeneous t → G ∈ J → eval₂ c v G = 0 := by
  constructor
  · intro h t G hG jG
    refine eq_zero_of_fnOn_eq_zero hv fun i => ?_
    have h1 := (pt c v hv).ideal_ker_le _
      (h _ ((aeval_mem_formIdeal_iff J i hG).2 ⟨0, by rwa [pow_zero, _root_.one_mul]⟩))
    rw [← appLE_pt_aeval c v hv i (pt_preimage_chart c v hv i).ge hG]
    have h2 : ((pt c v hv).appLE _ _ (pt_preimage_chart c v hv i).ge).hom (aeval (ratio R n i) G) = 0 :=
      (congrArg (resG _ (pt_preimage_chart c v hv i).ge) h1).trans (map_zero _)
    rw [h2, zero_mul]
  · intro h
    have := isProper_str R n
    have : QuasiCompact (pt c v hv ≫ PSpace.str R n) := inferInstance
    have : QuasiCompact (pt c v hv) := QuasiCompact.of_comp _ (PSpace.str R n)
    refine iSup_le fun p => Scheme.IdealSheafData.le_of_iSup_eq_top
      (fun i => ⟨chart R n i, isAffineOpen_chart R n i⟩) (iSup_chart R n) fun i => ?_
    rw [ideal_secIdeal_formSec, Ideal.span_singleton_le_iff_mem, Scheme.Hom.ker_apply, RingHom.mem_ker,
      Scheme.Hom.app_eq_appLE]
    have e := appLE_pt_aeval c v hv i le_rfl p.2.1
    rw [h _ _ p.2.1 p.2.2, map_zero] at e
    have hu : IsUnit (fnOn (pt c v hv ⁻¹ᵁ chart R n i) (v i)) := isUnit_of_basicOpen_eq _ (by
      rw [basicOpen_fnOn, pt_preimage_chart, inf_idem])
    exact (hu.pow _).mul_left_eq_zero.1 e

theorem of_baseRingHom {P : MorphismProperty Scheme.{0}}
    {Q : ∀ {R S : Type} [CommRing R] [CommRing S], (R →+* S) → Prop} [HasRingHomProperty P Q]
    {Z : Scheme.{0}} (s : Z ⟶ Sp R) {κ : Type} (U : κ → Z.affineOpens) (hU : ⨆ i, (U i : Z.Opens) = ⊤)
    (H : ∀ i, Q (baseRingHom s (U i).1).hom) : P s :=
  HasRingHomProperty.of_iSup_eq_top U hU fun i =>
    ((HasRingHomProperty.isLocal_ringHomProperty P).respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv _).1 (H i)

variable {σ : Type} (e : σ ≃ Fin (n + 1)) (I : Ideal (MvPolynomial σ R))

def numbered : Ideal (MvPolynomial (Fin (n + 1)) R) := I.comap (rename e.symm)

abbrev emb := (formIdeal (numbered e I)).subschemeι

theorem chart_spec (i : σ) :
    letI := (baseRingHom (emb e I ≫ PSpace.str R n) (emb e I ⁻¹ᵁ chart R n (e i))).hom.toAlgebra
    ∃ r : σ → Γ((formIdeal (numbered e I)).subscheme, emb e I ⁻¹ᵁ chart R n (e i)), r i = 1 ∧ Function.Surjective (aeval (R := R) r) ∧
      ∀ t (F : MvPolynomial σ R), F.IsHomogeneous t → (aeval r F = 0 ↔ ∃ k, X i ^ k * F ∈ I) := by
  letI := (baseRingHom (emb e I ≫ PSpace.str R n) (emb e I ⁻¹ᵁ chart R n (e i))).hom.toAlgebra
  have key : ∀ F : MvPolynomial σ R,
      aeval (fun j => pullRatio (emb e I) _ (e i) le_rfl (e j)) F =
        ((emb e I).app (chart R n (e i))).hom (aeval (ratio R n (e i)) (rename e F)) := fun F => by
    have h := congrArg (fun θ => θ (rename e F)) (appLE_comp_aeval_ratio (φ := emb e I) (i := e i) (hi := le_rfl))
    rw [Scheme.Hom.app_eq_appLE]
    refine Eq.trans ?_ h.symm
    rw [coe_eval₂Hom, eval₂_rename]
    rfl
  refine ⟨fun j => pullRatio (emb e I) _ (e i) le_rfl (e j), pullRatio_self, fun a => ?_, fun t F hF => ?_⟩
  · obtain ⟨b, rfl⟩ := (emb e I).app_surjective _ (isAffineOpen_chart R n (e i)) a
    obtain ⟨p, rfl⟩ := aeval_ratio_surjective R n (e i) b
    obtain ⟨q, rfl⟩ := rename_surjective (R := R) e e.surjective p
    exact ⟨q, key q⟩
  · rw [key, ← RingHom.mem_ker]
    have h := aeval_mem_formIdeal_iff (numbered e I) (e i) (hF.rename_isHomogeneous (f := e))
    rw [← (formIdeal (numbered e I)).ker_subschemeι_app] at h
    refine h.trans (exists_congr fun k => ?_)
    simp [numbered, rename_rename]

theorem vanish_iff (hI : ∀ F ∈ I, ∀ t, homogeneousComponent t F ∈ I) (c : R →+* A) (v : σ → A) :
    (∀ t G, G.IsHomogeneous t → G ∈ numbered e I → eval₂ c (v ∘ e.symm) G = 0) ↔ ∀ F ∈ I, eval₂ c v F = 0 := by
  refine ⟨fun h F hF => map_eq_zero_of_forms (eval₂Hom c v) hI (fun t G hG jG => ?_) hF, fun h t G _ jG => ?_⟩
  · have := h t (rename e G) hG.rename_isHomogeneous (by simpa [numbered, rename_rename] using jG)
    rwa [eval₂_rename, Function.comp_assoc, e.symm_comp_self, Function.comp_id] at this
  · rw [← eval₂_rename]
    exact h _ jG

theorem projRep_emb (hI : ∀ F ∈ I, ∀ t, homogeneousComponent t F ∈ I) :
    ProjRep I (emb e I ≫ PSpace.str R n) ((O1 R n).pull (emb e I))
      (fun a => Cartier.secPull (coord R n (e a)) (emb e I)) := by
  refine ⟨LB.isLB_pull (O1_isLB R n) _, fun R' _ β x v hx h => ?_, fun R' _ β v hv h => ?_⟩
  · obtain ⟨hv, hp⟩ := (ProjCoord.secCoord_iff e _ β x ((Category.assoc _ _ _).trans hx) v).1 h
    refine ⟨ProjCoord.range_comp_symm e v ▸ hv, (vanish_iff e I hI β v).1 ?_⟩
    rw [← formIdeal_le_ker_pt_iff _ β _ hv, ← hp]
    exact (Scheme.IdealSheafData.ker_subschemeι _).ge.trans (x.le_ker_comp _)
  · have hv' : Ideal.span (Set.range (v ∘ e.symm)) = ⊤ := by rwa [ProjCoord.range_comp_symm]
    have hle : (emb e I).ker ≤ (pt β _ hv').ker := (Scheme.IdealSheafData.ker_subschemeι _).le.trans
      ((formIdeal_le_ker_pt_iff _ β _ hv').2 ((vanish_iff e I hI β v).2 h))
    have hl := IsClosedImmersion.lift_fac (emb e I) _ hle
    have hs : (IsClosedImmersion.lift (emb e I) _ hle ≫ emb e I) ≫ PSpace.str R n = spMap β := by
      rw [hl, pt_str]
    refine ⟨_, ⟨(Category.assoc _ _ _).symm.trans hs, (ProjCoord.secCoord_iff e _ β _ hs v).2 ⟨hv', hl⟩⟩,
      fun x hx => ?_⟩
    obtain ⟨_, hp⟩ := (ProjCoord.secCoord_iff e _ β x ((Category.assoc _ _ _).trans hx.1) v).1 hx.2
    rw [← cancel_mono (emb e I), hl, hp]

theorem iSup_chart_emb : ⨆ i, emb e I ⁻¹ᵁ chart R n (e i) = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, e.iSup_comp (g := chart R n), iSup_chart]
  rfl

end Geometry

theorem projRep_empty {R σ : Type} [CommRing R] [IsEmpty σ] (I : Ideal (MvPolynomial σ R)) :
    ProjRep I (Scheme.emptyTo (Sp R)) (⟨PEmpty, PEmpty.elim, fun i => i.elim⟩ : LB ∅) isEmptyElim := by
  refine ⟨⟨Subsingleton.elim _ _, fun i => i.elim, fun i => i.elim⟩, fun R' _ β x v _ _ => ?_,
    fun R' _ β v hv _ => ?_⟩
  · have : IsEmpty (PrimeSpectrum R') := Function.isEmpty (β := (∅ : Scheme.{0})) x
    have : Subsingleton R' := PrimeSpectrum.isEmpty_iff_subsingleton.1 this
    exact ⟨Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
  · rw [Set.range_eq_empty, Ideal.span_empty] at hv
    have : Subsingleton R' := subsingleton_of_zero_eq_one (Ideal.mem_bot.1 (hv.ge Submodule.mem_top : (1 : R') ∈ _)).symm
    have : IsEmpty (Sp R') := PrimeSpectrum.isEmpty_iff_subsingleton.2 this
    have hi : IsInitial (Sp R') := isInitialOfIsEmpty
    exact ⟨hi.to _, ⟨hi.hom_ext _ _, ⟨fun j => (j ⟨⟩).elim⟩, fun j => (j ⟨⟩).elim, fun i => isEmptyElim i⟩,
      fun _ _ => hi.hom_ext _ _⟩

theorem exists_projRep_flat : ∀ (R σ : Type) [CommRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)) (d : ℕ), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → ∃ (Z : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec), (Nonempty σ → IsProjOver s) ∧ ProjRep I s M th ∧ (I.FG → LocallyOfFinitePresentation s) ∧ ((∀ e ≥ d, Module.Flat R (↥(MvPolynomial.homogeneousSubmodule σ R e) ⧸ (I.restrictScalars R).comap (MvPolynomial.homogeneousSubmodule σ R e).subtype)) → Flat s) := by
  intro R σ _ _ I d hI
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · exact ⟨_, _, _, _, fun h => (not_nonempty_iff.2 hσ h).elim, projRep_empty I, fun _ => inferInstance,
      fun _ => inferInstance⟩
  have := Fintype.ofFinite σ
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card σ = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm⟩
  let e := Fintype.equivFinOfCardEq hn
  let U : σ → (formIdeal (numbered e I)).subscheme.affineOpens := fun i =>
    ⟨emb e I ⁻¹ᵁ chart R n (e i), (isAffineOpen_chart R n (e i)).preimage _⟩
  refine ⟨_, _, _, _, fun _ => ⟨n, emb e I, inferInstance, rfl⟩, projRep_emb e I hI,
    fun h => of_baseRingHom (Q := RingHom.FinitePresentation) _ U (iSup_chart_emb e I) fun i => ?_,
    fun h => of_baseRingHom (Q := RingHom.Flat) _ U (iSup_chart_emb e I) fun i => ?_⟩
  · letI := (baseRingHom (emb e I ≫ PSpace.str R n) (emb e I ⁻¹ᵁ chart R n (e i))).hom.toAlgebra
    obtain ⟨r, hi, hr, H⟩ := chart_spec e I i
    exact finitePresentation_chart hi hr hI H h
  · letI := (baseRingHom (emb e I ≫ PSpace.str R n) (emb e I ⁻¹ᵁ chart R n (e i))).hom.toAlgebra
    obtain ⟨r, hi, hr, H⟩ := chart_spec e I i
    exact flat_chart hi hr H d h

end GlobalTheory.ProjFlat
