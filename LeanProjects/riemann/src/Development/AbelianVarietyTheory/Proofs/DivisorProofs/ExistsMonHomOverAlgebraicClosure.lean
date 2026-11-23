import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoOfLevel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointFactorIntegralSubalgebraStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ChowRigid

open GlobalTheory.Spread

theorem factor_finite (K B E : Type) [Field K] [CommRing B] [CommRing E] [Algebra K B] [Algebra K E]
    (i : E →ₐ[K] B) (hι : Function.Injective i) (hint : ∀ b : B, _root_.IsIntegral K b → b ∈ i.range)
    (T : Scheme.{0}) (p : T ⟶ Sp K) [IsFinite p] (t : Sp B ⟶ T) (ht : t ≫ p = spMap (algebraMap K B)) :
    ∃ u : Sp E ⟶ T, u ≫ p = spMap (algebraMap K E) ∧ t = spMap i.toRingHom ≫ u :=
  GlobalTheory.T.exists_factor_through_integral_subalgebra K B E i hι hint T p t ht

theorem torsion_factor (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (n : ℕ) (hn : 0 < n) (B E : Type) [CommRing B] [CommRing E] [Algebra K B] [Algebra K E]
    (i : E →ₐ[K] B) (hι : Function.Injective i) (hint : ∀ b : B, IsIntegral K b → b ∈ i.range)
    (T : Over (Sp K)) (y : T ⟶ A) (hy : y ^ n = 1) (t : Sp B ⟶ T.left)
    (ht : t ≫ T.hom = spMap (algebraMap K B)) :
    ∃ x : Over.mk (spMap (algebraMap K E)) ⟶ A, x ^ n = 1 ∧ t ≫ y.left = spMap i.toRingHom ≫ x.left := by
  have := hA.comm; have := hA.smooth; have := hA.proper
  have hu : IsUnit ((n : Γ(Sp K, ⊤))) := by
    have : IsUnit (n : K) := (Nat.cast_ne_zero.mpr hn.ne').isUnit
    simpa using this.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have := GlobalTheory.GrpTangent.isFinite_torsion A hu
  obtain ⟨hη1, huniv⟩ := GlobalTheory.LamF.torsion_universal A n
  obtain ⟨w, hw⟩ := huniv T y hy
  obtain ⟨u, hu1, hu2⟩ := factor_finite K B E i hι hint (torsion A n).left (torsion A n).hom (t ≫ w.left)
    (by rw [Category.assoc, Over.w w, ht])
  refine ⟨Over.homMk u hu1 ≫ torsion.ι A n, ?_, ?_⟩
  · rw [← comp_pow, hη1, comp_one]
  · rw [← hw, Over.comp_left, ← Category.assoc, hu2, Over.comp_left, Category.assoc]
    rfl

theorem compare (K Ω : Type) [Field K] [CharZero K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    (S : Type) [CommRing S] [Algebra K S]
    (i : algebraicClosure K Ω →ₐ[K] S) (j : S →ₐ[K] Ω) (ρ : S →ₐ[K] algebraicClosure K Ω)
    (hj : Function.Injective j) (hji : ∀ x, j (i x) = x) (hρi : ∀ x, ρ (i x) = x)
    (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (hA : IsAbelianScheme A) (hA' : IsAbelianScheme A')
    (gS : (Over.pullback (spMap (algebraMap K S))).obj A ⟶ (Over.pullback (spMap (algebraMap K S))).obj A')
    [IsMonHom gS]
    (g : (Over.pullback (spMap (algebraMap K (algebraicClosure K Ω)))).obj A ⟶
      (Over.pullback (spMap (algebraMap K (algebraicClosure K Ω)))).obj A')
    [IsMonHom g] (hg : g.left ≫ pullback.fst _ _ = bcMap A.hom ρ ≫ gS.left ≫ pullback.fst _ _) :
    bcMap A.hom (algebraicClosure K Ω).val ≫ g.left ≫ pullback.fst _ _ =
      bcMap A.hom j ≫ gS.left ≫ pullback.fst _ _ := by
  have hι : Function.Injective i := fun a b h => Subtype.ext (by rw [← hji a, ← hji b, h])
  have hint : ∀ s : S, _root_.IsIntegral K s → s ∈ i.range := fun s hs => by
    have h1 : j s ∈ (algebraicClosure K Ω) := mem_algebraicClosure_iff'.mpr (hs.map j)
    exact ⟨⟨j s, h1⟩, hj (hji _)⟩
  have hintΩ : ∀ b : Ω, _root_.IsIntegral K b → b ∈ (algebraicClosure K Ω).val.range := fun b hb =>
    ⟨⟨b, mem_algebraicClosure_iff'.mpr hb⟩, rfl⟩
  have hLinj : Function.Injective (algebraicClosure K Ω).val := Subtype.val_injective
  obtain ⟨h, hh, hhe⟩ := GlobalTheory.HomDescent.exists_specialise g (algebraicClosure K Ω).val
  obtain ⟨f, hf, hfe⟩ := GlobalTheory.HomDescent.exists_specialise gS j
  have semi := isSemiAbelian_of_isAbelianScheme _ (isAbelianScheme_pullback_obj (spMap (algebraMap K Ω)) A hA)
  have semi' := isSemiAbelian_of_isAbelianScheme _ (isAbelianScheme_pullback_obj (spMap (algebraMap K Ω)) A' hA')
  have e : f = h := by
    have := hf; have := hh
    refine GlobalTheory.HomExtNormal.hom_eq_of_torsion semi semi' f h fun y n hn hy => ?_

    let P := pushHom (isGrpPullback_pullback A (spMap (algebraMap K Ω))) (𝟙_ (Over (Sp Ω)))
    have hPn : P y ^ n = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨x, hxn, hx⟩ := torsion_factor K A hA n hn Ω (algebraicClosure K Ω) (algebraicClosure K Ω).val hLinj hintΩ _ (P y) hPn (𝟙 _) (by
      change 𝟙 _ ≫ 𝟙 _ ≫ _ = _; simp)
    have hx' : y.left ≫ pullback.fst _ _ = spMap (algebraicClosure K Ω).val.toRingHom ≫ x.left := by
      rw [← hx, Category.id_comp]; rfl
    have hys : y.left ≫ pullback.snd _ _ = 𝟙 _ := Over.w y
    have hxw : x.left ≫ A.hom = spMap (algebraMap K (algebraicClosure K Ω)) := Over.w x
    have eji : spMap j.toRingHom ≫ spMap i.toRingHom = spMap (algebraicClosure K Ω).val.toRingHom := by
      rw [GlobalTheory.HomDescent.spMap_comp]; congr 1; exact RingHom.ext hji
    have eρi : spMap ρ.toRingHom ≫ spMap i.toRingHom = 𝟙 _ := by
      rw [GlobalTheory.HomDescent.spMap_comp, show ρ.toRingHom.comp i.toRingHom = RingHom.id _ from RingHom.ext hρi]
      exact Spec.map_id _
    let xS : Sp S ⟶ pullback A.hom (spMap (algebraMap K S)) :=
      pullback.lift (spMap i.toRingHom ≫ x.left) (𝟙 _) (by
        rw [Category.assoc, hxw, Category.id_comp, spMap_algHom_comp])
    let xL : Sp (algebraicClosure K Ω) ⟶ pullback A.hom (spMap (algebraMap K (algebraicClosure K Ω))) :=
      pullback.lift x.left (𝟙 _) (by rw [hxw, Category.id_comp])
    have c1 : y.left ≫ bcMap A.hom j = spMap j.toRingHom ≫ xS := by
      apply pullback.hom_ext
      · rw [Category.assoc, bcMap_fst, hx', Category.assoc, pullback.lift_fst, ← Category.assoc, eji]
      · rw [Category.assoc, bcMap_snd, ← Category.assoc, hys, Category.assoc, pullback.lift_snd,
          Category.id_comp, Category.comp_id]
    have c2 : y.left ≫ bcMap A.hom (algebraicClosure K Ω).val = spMap (algebraicClosure K Ω).val.toRingHom ≫ xL := by
      apply pullback.hom_ext
      · rw [Category.assoc, bcMap_fst, hx', Category.assoc, pullback.lift_fst]
      · rw [Category.assoc, bcMap_snd, ← Category.assoc, hys, Category.assoc, pullback.lift_snd,
          Category.id_comp, Category.comp_id]
    have c3 : xL ≫ bcMap A.hom ρ = spMap ρ.toRingHom ≫ xS := by
      apply pullback.hom_ext
      · rw [Category.assoc, bcMap_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc,
          eρi, Category.id_comp]
      · rw [Category.assoc, bcMap_snd, Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
          Category.id_comp, Category.comp_id]

    let xS' : 𝟙_ (Over (Sp S)) ⟶ (Over.pullback (spMap (algebraMap K S))).obj A :=
      Over.homMk xS (pullback.lift_snd _ _ _)
    let PS := pushHom (isGrpPullback_pullback A (spMap (algebraMap K S))) (𝟙_ (Over (Sp S)))
    have hPSinj : Function.Injective PS := fun a b e =>
      Over.OverMorphism.ext ((isGrpPullback_pullback A (spMap (algebraMap K S))).1.hom_ext
        (congrArg (fun z => z.left) e) (by rw [Over.w a, Over.w b]))
    let q : Over.mk ((𝟙_ (Over (Sp S))).hom ≫ spMap (algebraMap K S)) ⟶ Over.mk (spMap (algebraMap K (algebraicClosure K Ω))) :=
      Over.homMk (spMap i.toRingHom) (by
        change _ = 𝟙 _ ≫ _
        rw [Category.id_comp]; exact spMap_algHom_comp i)
    have hPS : PS xS' = q ≫ x := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    have hxSn : xS' ^ n = 1 := hPSinj (by rw [map_pow, hPS, ← comp_pow, hxn, comp_one, map_one])
    let P' := pushHom (isGrpPullback_pullback A' (spMap (algebraMap K S))) (𝟙_ (Over (Sp S)))
    have hzn : P' (xS' ≫ gS) ^ n = 1 := by rw [← map_pow, ← pow_comp, hxSn, one_comp, map_one]
    obtain ⟨c, -, hc⟩ := torsion_factor K A' hA' n hn S (algebraicClosure K Ω) i hι hint _ (P' (xS' ≫ gS)) hzn (𝟙 _) (by
      change 𝟙 _ ≫ 𝟙 _ ≫ _ = _; simp)
    have hz : xS ≫ gS.left ≫ pullback.fst _ _ = spMap i.toRingHom ≫ c.left := by
      rw [← hc, Category.id_comp]; rfl
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc]
      rw [hfe, hhe]
      calc y.left ≫ bcMap A.hom j ≫ gS.left ≫ pullback.fst _ _
          = spMap j.toRingHom ≫ xS ≫ gS.left ≫ pullback.fst _ _ := by rw [reassoc_of% c1]
        _ = spMap (algebraicClosure K Ω).val.toRingHom ≫ c.left := by rw [hz, reassoc_of% eji]
        _ = spMap (algebraicClosure K Ω).val.toRingHom ≫ spMap ρ.toRingHom ≫ spMap i.toRingHom ≫ c.left := by
          rw [reassoc_of% eρi]
        _ = spMap (algebraicClosure K Ω).val.toRingHom ≫ xL ≫ bcMap A.hom ρ ≫ gS.left ≫ pullback.fst _ _ := by
          rw [reassoc_of% c3, hz]
        _ = y.left ≫ bcMap A.hom (algebraicClosure K Ω).val ≫ g.left ≫ pullback.fst _ _ := by
          rw [hg, reassoc_of% c2]
    · have e1 : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
      have e2 : h.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w h
      simp only [Over.comp_left, Category.assoc]
      rw [e1, e2]
  rw [← hhe, ← hfe, e]

theorem chow_rigidity : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → IsAbelianScheme A' → ∀ f : (Over.pullback (spMap (algebraMap K Ω))).obj A ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj A', IsMonHom f → ∃ g : (Over.pullback (spMap (algebraMap K (algebraicClosure K Ω)))).obj A ⟶ (Over.pullback (spMap (algebraMap K (algebraicClosure K Ω)))).obj A', IsMonHom g ∧ GlobalTheory.Spread.bcMap A.hom (algebraicClosure K Ω).val ≫ g.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _ := by
  intro K Ω _ _ _ _ _ A A' _ _ hA hA' f hf
  have := hA.proper; have := hA.smooth; have := hA'.proper; have := hA'.smooth
  have := hf
  obtain ⟨R, gR, ⟨s, hs⟩, hgR, hR⟩ := GlobalTheory.HomDescent.exists_fg_isMonHom f
  have := hgR
  haveI : IsAlgClosed (algebraicClosure K Ω) := IsAlgClosure.isAlgClosed K
  let S : Subalgebra (algebraicClosure K Ω) Ω := Algebra.adjoin (algebraicClosure K Ω) (s : Set Ω)
  haveI : Algebra.FiniteType (algebraicClosure K Ω) S := ⟨(Subalgebra.fg_top S).mpr ⟨s, rfl⟩⟩
  obtain ⟨ρ₀⟩ := GlobalTheory.Ex.ThetaDescent.nonempty_algHom (algebraicClosure K Ω) S
  have hRS : ∀ r ∈ R, r ∈ S := fun r hr => by
    have h1 : Algebra.adjoin K (s : Set Ω) ≤
        (Algebra.adjoin (algebraicClosure K Ω) (s : Set Ω)).restrictScalars K :=
      Algebra.adjoin_le Algebra.subset_adjoin
    rw [← hs] at hr
    exact h1 hr
  let inc : R →ₐ[K] S :=
    { toFun := fun r => ⟨r, hRS r r.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let i : algebraicClosure K Ω →ₐ[K] S := IsScalarTower.toAlgHom K (algebraicClosure K Ω) S
  let j : S →ₐ[K] Ω := S.val.restrictScalars K
  let ρ : S →ₐ[K] algebraicClosure K Ω := ρ₀.restrictScalars K
  obtain ⟨gS, hgS, hgSe⟩ := GlobalTheory.HomDescent.exists_specialise gR inc
  have := hgS
  obtain ⟨g, hg, hge⟩ := GlobalTheory.HomDescent.exists_specialise gS ρ
  have := hg
  refine ⟨g, hg, ?_⟩
  rw [compare K Ω S i j ρ Subtype.val_injective (fun _ => rfl) (fun x => ρ₀.commutes x) A A' hA hA' gS g hge,
    hgSe, ← hR, bcMap_comp_of_eq_assoc A.hom inc j R.val fun _ => rfl]

end GlobalTheory.ChowRigid
