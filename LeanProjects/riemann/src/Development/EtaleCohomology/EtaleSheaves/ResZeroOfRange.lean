import Development.EtaleCohomology.EtaleSheaves.CovOfPoints
import Development.EtaleCohomology.EtaleSheaves.LeafNegPf
import Development.EtaleCohomology.EtaleSheaves.PointDetect0Of
import Development.EtaleCohomology.EtaleSheaves.LeafConeExactPf
import Development.EtaleCohomology.EtaleSheaves.LeafTwPtPf
import Development.EtaleCohomology.EtaleSheaves.LeafOfRingsLocSurjPf
import Development.EtaleCohomology.EtaleSheaves.LeafOfRingsLocInjPf
import Development.EtaleCohomology.EtaleSheaves.LeafTwAdjPf
import Development.EtaleCohomology.EtaleSheaves.LeafTwGenPf
import Development.EtaleCohomology.EtaleSheaves.LeafTwFieldZPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafSurj0WPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.E8.TwSec

theorem neg_cochain (R : Type) [CommRing R] (E : Spc) (F : Shv R) (m : ℤ) (hm : m < 0)
    (z : Cochain ((chains R).obj E) (res R F) m) : z = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [Cochain.zero_v]
  by_cases hq : q < 0
  · exact (LateralTheory.E.LeafNegPf.res_isZero R F q hq).eq_of_tgt _ _
  · exact (LateralTheory.E.LeafNegPf.chains_isZero R E p (by omega)).eq_of_src _ _

theorem fgt_zero (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (y : Hrel R f F 0)
    (h : fgt R f F 0 y = 0) : y = 0 := by
  obtain ⟨z, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.inr ((chains R).map f))) z (zero_add 0)) = 0 at h
  rw [CohomologyClass.mk_eq_zero_iff] at h
  obtain ⟨m, hm, β, hβ⟩ := h
  rw [neg_cochain R E F m (by omega) β, δ_zero] at hβ
  have hz : z = 0 := by
    apply Cocycle.ext
    rw [mappingCone.ext_cochain_from_iff _ (-1) 0 (by omega)]
    refine ⟨(neg_cochain R U F _ (by omega) _).trans (neg_cochain R U F _ (by omega) _).symm, ?_⟩
    rw [Cocycle.coe_zero, Cochain.comp_zero]
    exact hβ.symm
  rw [hz]
  rfl

theorem pull_fgt (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) (y : Hrel R f F n) :
    pull R f F n (fgt R f F n y) = 0 := by
  obtain ⟨z, rfl⟩ := y.mk_surjective
  exact LateralTheory.E.LeafConeExactPf.pre_inr_eq_zero _ n z

theorem twPt : LeafTwPt := LeafTwPt_of LeafTwAdj_of LeafTwGen_of LeafTwFieldZ_of

theorem secKill (q : ℕ) [NeZero q] {X Z : Scheme.{0}} (ι : Z ⟶ X) (j : ℤ) (s : Sec (tw q j) X) (hs : Sec.res ι s = 0)
    (z : Z) : ∃ (W : Scheme.{0}) (w : W ⟶ X), Etale w ∧ ι z ∈ Set.range w ∧ Sec.res w s = 0 := by
  obtain ⟨U, w, hw, ⟨u, hu⟩, t, ht⟩ := LateralTheory.E.LeafOfRingsLocSurjPf.LeafOfRingsLocSurj_of (ZMod q) (twF q j) X s (ι z)
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := w) (g := ι) u z hu
  have e2 : Sec.res (F := tw q j) (pullback.fst w ι) (Sec.res w s) = 0 := by
    rw [← res_comp, pullback.condition, res_comp, hs]
    exact map_zero _
  have hP : ofRings.sec (twF q j) _ (((twF q j).map (Scheme.Γ.map (pullback.fst w ι).op)).hom t) = 0 := by
    rw [← sec_res, ← ht]
    exact e2
  obtain ⟨V, v, -, ⟨v0, hv0⟩, hV⟩ := LeafOfRingsLocInj_of (ZMod q) (twF q j) _ _ hP p
  obtain ⟨W, w', hw', ⟨a, ha⟩, hW⟩ := twPt q j U u t V (v ≫ pullback.fst w ι) v0 (by simp [hv0, hp1])
    ((twF_res_comp j _ _ t).trans hV)
  refine ⟨W, w' ≫ w, inferInstance, ⟨a, by simp [ha, hu]⟩, ?_⟩
  rw [res_comp]
  have e := sec_res (twF q j) w' t
  rw [hW] at e
  exact (congrArg (Sec.res w') ht).trans (e.trans (sec_zero _ _))

def zeroLocus {R : Type} [CommRing R] {F : Shv R} {X : Scheme.{0}} (s : Sec F X) : Set X :=
  {x | ∃ (W : Scheme.{0}) (w : W ⟶ X), Etale w ∧ x ∈ Set.range w ∧ Sec.res w s = 0}

theorem isOpen_zeroLocus {R : Type} [CommRing R] {F : Shv R} {X : Scheme.{0}} (s : Sec F X) : IsOpen (zeroLocus s) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨W, w, hw, hx, h0⟩
  exact ⟨Set.range w, fun y hy => ⟨W, w, hw, hy, h0⟩, w.isOpenMap.isOpen_range, hx⟩

theorem res_zero_of_range {R : Type} [CommRing R] {F : Shv R} {X T : Scheme.{0}} (s : Sec F X) (g : T ⟶ X)
    (hg : ∀ t, g t ∈ zeroLocus s) : Sec.res g s = 0 := by
  apply LateralTheory.E.PointDetect0Pf.etSep R F T
  intro t
  obtain ⟨W, w, hw, ⟨u, hu⟩, h0⟩ := hg t
  obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := w) t u hu.symm
  refine ⟨_, pullback.fst g w, inferInstance, ⟨p, hp1⟩, ?_⟩
  rw [← res_comp, pullback.condition, res_comp, h0]
  exact map_zero _

theorem core (h9 : A9) (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (ι : W ⟶ B) (P : Y ⟶ B) [IsProper P]
    (U : B.Etale) (y : Hrel (ZMod q) (sch.map (prU P ι U)) (tw q i) 0) (x : U.left) (hx : U.hom x ∈ Set.range ι) :
    ∃ (U' : B.Etale) (a : U' ⟶ U), x ∈ Set.range a.left ∧
      ∀ (U'' : B.Etale) (b : U'' ⟶ U'), rY q i P ι (b ≫ a) 0 y = 0 := by
  obtain ⟨e, he, -⟩ := (h9 (ZMod q) (tw q i)).2
  obtain ⟨s, hs⟩ := (e (YU P U)).surjective (fgt (ZMod q) (sch.map (prU P ι U)) (tw q i) 0 y)
  have hZ : Sec.res (prU P ι U) s = 0 := by
    apply (e _).injective
    rw [← he, hs, map_zero]
    exact pull_fgt _ _ _ _ _
  have hcl : IsClosed ((toBY P U) '' (zeroLocus s)ᶜ) :=
    (toBY P U).isClosedMap _ (isOpen_zeroLocus s).isClosed_compl
  let O : U.left.Opens := ⟨_, hcl.isOpen_compl⟩
  have hxO : x ∈ O := by
    rintro ⟨t, ht, htx⟩
    obtain ⟨w0, hw0⟩ := hx
    obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd P U.hom ≫ U.hom) (g := ι) t w0
      (by rw [hw0, ← htx]; rfl)
    apply ht
    rw [← hp1]
    exact secKill q (prU P ι U) i s hZ p
  have hU : Etale U.hom := U.prop
  let U' : B.Etale := MorphismProperty.Over.mk ⊤ (O.ι ≫ U.hom) (inferInstanceAs (Etale (O.ι ≫ U.hom)))
  let a : U' ⟶ U := MorphismProperty.Over.homMk O.ι rfl
  refine ⟨U', a, ⟨⟨x, hxO⟩, rfl⟩, fun U'' b => ?_⟩
  apply fgt_zero
  refine (relNat _ _ _ _ _ _ _ _ _).trans ?_
  rw [← hs, he, res_zero_of_range s _ ?_, map_zero]
  intro t
  by_contra hn
  have h1 : resY P (b ≫ a) ≫ toBY P U = (toBY P U'' ≫ b.left) ≫ O.ι := by
    simp only [resY, toBY, pullback.lift_snd]
    rfl
  have h2 : toBY P U (resY P (b ≫ a) t) ∈ O := by
    rw [← Scheme.Hom.comp_apply, h1]
    exact ((toBY P U'' ≫ b.left) t).2
  exact h2 ⟨_, hn, rfl⟩

theorem LeafSurj0W_of : LateralTheory.E.LeafSurj0Pf.LeafSurj0W := by
  intro hy q _ k _ _ i B W Y0 Y1 Y2 _ ι _ V _ p g1 g2 _ _ h2 _ U y x hx
  exact core hy.2.2.2.2.2.2.2.1 q i ι (g2 ≫ g1 ≫ p) U y x hx

end LateralTheory.E.LeafSurj0WPf
