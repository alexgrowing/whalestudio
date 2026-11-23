import Development.EtaleCohomology.EtaleSheaves.LeafInj0Of

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafInj0WPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf

theorem fgtInj0 (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E)
    (hU : Subsingleton (H R U F (-1))) (y : Hrel R f F 0) (hy : fgt R f F 0 y = 0) : y = 0 := by
  obtain ⟨z, rfl⟩ := y.mk_surjective
  obtain ⟨β, hβ⟩ : ∃ β : Cochain ((chains R).obj E) (res R F) (-1), δ (-1) 0 β = (Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp z.1 (zero_add 0) := by
    have := hy
    change CohomologyClass.mk _ = 0 at this
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (-1) (by omega)] at this
    obtain ⟨β, hβ⟩ := this
    exact ⟨β, by rw [hβ]; rfl⟩
  have hdec : z.1 = mappingCone.descCochain ((chains R).map f) ((mappingCone.inl ((chains R).map f)).comp z.1 (show -1 + 0 = -1 by omega))
      ((Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp z.1 (zero_add 0)) (show (-1 : ℤ) + 1 = 0 by omega) := by
    rw [mappingCone.ext_cochain_from_iff _ (-1) 0 (by omega)]
    simp [mappingCone.inl_descCochain]
  have hz : δ 0 1 z.1 = 0 := Cocycle.δ_eq_zero z 1
  rw [hdec, mappingCone.δ_descCochain _ _ _ _ _ (by omega)] at hz
  rw [mappingCone.ext_cochain_from_iff _ 0 1 (by omega)] at hz
  obtain ⟨hz1, -⟩ := hz
  simp only [Cochain.comp_zero, Cochain.comp_add, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc, add_zero] at hz1
  have hw : δ (-1) 0 ((mappingCone.inl ((chains R).map f)).comp z.1 (show -1 + 0 = -1 by omega) - (Cochain.ofHom ((chains R).map f)).comp β (zero_add (-1))) = 0 := by
    rw [δ_sub, δ_ofHom_comp, hβ, sub_eq_zero]
    rw [show Int.negOnePow 1 = -1 by decide] at hz1
    simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul, ← sub_eq_add_neg, sub_eq_zero] at hz1
    exact hz1
  obtain ⟨γ, hγ⟩ : ∃ γ : Cochain ((chains R).obj U) (res R F) (-2), δ (-2) (-1) γ = (mappingCone.inl ((chains R).map f)).comp z.1 (show -1 + 0 = -1 by omega) - (Cochain.ofHom ((chains R).map f)).comp β (zero_add (-1)) := by
    have h0 : CohomologyClass.mk (Cocycle.mk _ 0 (by omega) hw) = 0 := Subsingleton.elim _ _
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (-2) (by omega)] at h0
    obtain ⟨γ, hγ⟩ := h0
    exact ⟨γ, by rw [hγ]; rfl⟩
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (-1) (by omega)]
  refine ⟨mappingCone.descCochain ((chains R).map f) γ β (show (-2 : ℤ) + 1 = -1 by omega), ?_⟩
  rw [mappingCone.δ_descCochain _ _ _ _ _ (by omega), hγ, hβ, show Int.negOnePow 0 = 1 by decide, one_smul, sub_add_cancel]
  conv_rhs => rw [hdec]
  rfl

theorem fgtPull (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (y : Hrel R f F n) :
    pull R f F n (fgt R f F n y) = 0 := by
  obtain ⟨y, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk _ = 0
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨n.negOnePow • (mappingCone.inl ((chains R).map f)).comp y.1 (by omega), ?_⟩
  rw [δ_units_smul]
  rw [δ_comp (mappingCone.inl ((chains R).map f)) y.1 (show -1 + n = n - 1 by omega) 0 (n + 1) n (by omega) (by omega) (by omega)]
  simp [zcomp, mappingCone.δ_inl, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, smul_smul, Int.units_mul_self]

theorem fgtNat (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U)
  (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (n : ℤ) (y : Hrel R f F n) :
  fgt R f' F n (rpull R f f' u e comm F n y) = pull R e F n (fgt R f F n y) := by
  obtain ⟨y, rfl⟩ := y.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  have key : mappingCone.inr ((chains R).map f') ≫ mappingCone.map ((chains R).map f') ((chains R).map f) ((chains R).map u) ((chains R).map e) (by rw [← Functor.map_comp, ← Functor.map_comp, comm]) = (chains R).map e ≫ mappingCone.inr ((chains R).map f) := by
    simp [mappingCone.map]
  simp [zcomp, rmap]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, key]

theorem leafRelNat : LeafRelNat := fgtNat

def LeafSecTw : Prop := ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (s : Sec (tw q i) U.left),
  Sec.res (prB ι U) s = 0 → ∀ x : U.left, U.hom x ∈ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Sec.res a.left s = 0

def LeafSec0W : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (h : Ht q (sch.obj U.left) 0 i),
  pull (ZMod q) (sch.map (prB ι U)) (tw q i) 0 h = 0 → ∀ x : U.left, U.hom x ∈ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ pull (ZMod q) (sch.map a.left) (tw q i) 0 h = 0

theorem etale_standing_hypotheses_imply_restriction_axiom (hH : Hyps) : A9 := by
  unfold Hyps at hH
  exact hH.2.2.2.2.2.2.2.1

theorem LeafSec0W_of (hT : LeafSecTw) : LeafSec0W := by
  intro hH q _ k _ hq i B W s ι _ U h h0 x hx
  obtain ⟨e, hnat, -⟩ := ((etale_standing_hypotheses_imply_restriction_axiom hH) (ZMod q) (tw q i)).2
  obtain ⟨t, rfl⟩ := (e U.left).surjective h
  rw [hnat] at h0
  have h1 : Sec.res (prB ι U) t = 0 := (e _).injective (by rw [h0, map_zero])
  obtain ⟨U', a, y, hy, h2⟩ := hT q k hq i s ι U t h1 x hx
  exact ⟨U', a, y, hy, by rw [hnat, h2, map_zero]⟩

theorem LeafInj0W_of (hT : LeafSecTw) : LeafInj0W := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s ι _ V hV p g1 g2 hp1 hp2 hp3 hS U c x hx
  obtain ⟨U', a, y, hy, hz⟩ := LeafSec0W_of hT hH q k hq i s ι U _ (fgtPull (ZMod q) (tw q i) (sch.map (prB ι U)) 0 c) x hx
  refine ⟨U', a, y, hy, Cov.all ?_⟩
  intro U'' b
  apply fgtInj0 (ZMod q) (tw q i) (sch.map (prB ι U''))
  · exact ((etale_standing_hypotheses_imply_restriction_axiom hH) (ZMod q) (tw q i)).1 _ (-1) (by norm_num)
  · rw [fgtNat]
    have e : (b ≫ a).left = b.left ≫ a.left := rfl
    rw [e, Functor.map_comp, pull_comp, hz, map_zero]

end LateralTheory.E.LeafInj0WPf
