import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionFiniteFlatIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndFlatMulAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.TorsOverOpen

open GlobalTheory.TorsionRepresent GlobalTheory.IndefiniteRowSideFullHecke.FlatTorsionIsomorphism

section

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] (k : ℕ)

theorem isPullback_incl :
    IsPullback (incl G k).left (torsScheme G k).hom ((𝟙 G : G ⟶ G) ^ k).left η[G].left := by
  have h := (IsPullback.of_hasPullback ((𝟙 G : G ⟶ G) ^ k) (η : 𝟙_ (Over S) ⟶ G)).map (Over.forget S)
  have e : (pullback.snd ((𝟙 G : G ⟶ G) ^ k) (η : 𝟙_ (Over S) ⟶ G)).left = (torsScheme G k).hom :=
    (Category.comp_id _).symm.trans (Over.w (pullback.snd ((𝟙 G : G ⟶ G) ^ k) (η : 𝟙_ (Over S) ⟶ G)))
  exact e ▸ h

theorem pullback_map_pow :
    (Over.pullback f).map ((𝟙 G : G ⟶ G) ^ k) = (𝟙 ((Over.pullback f).obj G)) ^ k := by
  rw [← (Over.pullback f).map_id]
  exact map_pow (Over.pullback f).homMonoidHom _ _

theorem prop_snd (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange]
    (h : P ((𝟙 ((Over.pullback f).obj G)) ^ k : (Over.pullback f).obj G ⟶ _).left) :
    P (pullback.snd (torsScheme G k).hom f) := by
  rw [← pullback_map_pow] at h
  have hη : η[G].left ≫ G.hom = 𝟙 S := Over.w η[G]
  have hι : (incl G k).left ≫ G.hom = (torsScheme G k).hom := Over.w _
  have hm : ((𝟙 G : G ⟶ G) ^ k).left ≫ G.hom = G.hom := Over.w _
  let s : S' ⟶ pullback G.hom f := pullback.lift (f ≫ η[G].left) (𝟙 _) (by
    rw [Category.assoc, hη]; simp)
  let a : pullback (torsScheme G k).hom f ⟶ pullback G.hom f :=
    pullback.lift (pullback.fst _ _ ≫ (incl G k).left) (pullback.snd _ _) (by
      rw [Category.assoc, hι, pullback.condition])
  let m : pullback G.hom f ⟶ pullback G.hom f := ((Over.pullback f).map ((𝟙 G : G ⟶ G) ^ k)).left
  have m1 : m ≫ pullback.fst G.hom f = pullback.fst G.hom f ≫ ((𝟙 G : G ⟶ G) ^ k).left := pullback.lift_fst _ _ _
  have m2 : m ≫ pullback.snd G.hom f = pullback.snd G.hom f := pullback.lift_snd _ _ _
  have a1 : a ≫ pullback.fst G.hom f = pullback.fst _ _ ≫ (incl G k).left := pullback.lift_fst _ _ _
  have a2 : a ≫ pullback.snd G.hom f = pullback.snd _ _ := pullback.lift_snd _ _ _
  have s1 : s ≫ pullback.fst G.hom f = f ≫ η[G].left := pullback.lift_fst _ _ _
  have s2 : s ≫ pullback.snd G.hom f = 𝟙 _ := pullback.lift_snd _ _ _
  have hr : IsPullback (pullback.fst G.hom f) m ((𝟙 G : G ⟶ G) ^ k).left (pullback.fst G.hom f) := by
    refine IsPullback.of_bot ?_ m1.symm (IsPullback.of_hasPullback G.hom f)
    rw [hm, m2]
    exact IsPullback.of_hasPullback G.hom f
  have ho := (IsPullback.of_hasPullback (torsScheme G k).hom f).paste_horiz (isPullback_incl G k)
  have hl : IsPullback a (pullback.snd (torsScheme G k).hom f) m s := by
    refine IsPullback.of_right ?_ ?_ hr
    · rw [a1, s1]
      exact ho
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, m1, s1, ← Category.assoc, a1]
        exact ho.w
      · rw [Category.assoc, Category.assoc, m2, s2, a2, Category.comp_id]
  exact MorphismProperty.of_isPullback hl h

noncomputable def toTors : (Over.map f).obj ((Over.pullback f).obj (torsScheme G k)) ⟶ torsScheme G k :=
  Over.homMk (pullback.fst (torsScheme G k).hom f) pullback.condition

theorem univ (T : Over S') (x : (Over.map f).obj T ⟶ G) (hx : x ^ k = 1) :
    ∃! h : T ⟶ (Over.pullback f).obj (torsScheme G k), (Over.map f).map h ≫ toTors f G k ≫ incl G k = x := by
  obtain ⟨l, hl⟩ := exists_lift G k x hx
  have hw : l.left ≫ (torsScheme G k).hom = T.hom ≫ f := Over.w l
  refine ⟨Over.homMk (pullback.lift l.left T.hom hw) (pullback.lift_snd _ _ _), ?_, ?_⟩
  · beta_reduce
    rw [← hl, ← Category.assoc]
    congr 1
    ext1
    exact pullback.lift_fst _ _ _
  · intro h hh
    rw [← hl, ← Category.assoc, cancel_mono] at hh
    ext1
    apply pullback.hom_ext
    · exact (congrArg CommaMorphism.left hh).trans (pullback.lift_fst _ _ _).symm
    · exact (Over.w h).trans (pullback.lift_snd _ _ _).symm

end

theorem isAbelianScheme_restrict {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (W : S.Opens)
    (hp : IsProper (G.hom ∣_ W)) : IsAbelianScheme ((Over.pullback W.ι).obj G) := by
  have := hG.comm
  have := hG.smooth
  have := hG.geomConnected
  have hr := isPullback_morphismRestrict G.hom W
  refine ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd G.hom W.ι)), ?_,
    inferInstanceAs (GeometricallyConnected (pullback.snd G.hom W.ι))⟩
  change IsProper (pullback.snd G.hom W.ι)
  rw [← hr.flip.isoPullback_inv_snd]
  infer_instance

theorem torsion_finFlatEt : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => IsAbelianScheme ((Over.pullback W.ι).obj t.G) ∧ TorsFiniteFlat t.G W k ∧ ∃ (Z : Over W.toScheme) (n : overW W Z ⟶ t.G), FinFlatEt Z ∧ n ^ k = 1 ∧ ∀ (T : Over W.toScheme) (x : overW W T ⟶ t.G), x ^ k = 1 → ∃! h : T ⟶ Z, (Over.map W.ι).map h ≫ n = x := by
  intro E _ _ _ H R _ _ _ _ hR t P W _ hp ψW k hk
  have hA := isAbelianScheme_restrict t.G t.semi W hp
  have : IsNoetherianRing R := hR.1
  have : IsNoetherianRing (CommRingCat.of R) := hR.1
  have : IsLocallyNoetherian W.toScheme := isLocallyNoetherian_of_isOpenImmersion W.ι
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.isFinite_and_flat_mul_abelianScheme _ _ hA k hk
  have hfin := prop_snd W.ι t.G k @IsFinite h₁
  have hflat := prop_snd W.ι t.G k @Flat h₂
  have hs := t.semi.smooth
  have hsK : Smooth ((Over.pullback (jK R)).obj t.G).hom := inferInstanceAs (Smooth (pullback.snd t.G.hom (jK R)))
  have hu : IsUnit (k : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)) := by
    have : IsUnit (k : FractionRing R) := (Nat.cast_ne_zero.2 (by omega) : (k : FractionRing R) ≠ 0).isUnit
    simpa using this.map (Scheme.ΓSpecIso (.of (FractionRing R))).inv.hom
  have het : Etale (pullback.snd (torsScheme t.G k).hom (jK R)) :=
    prop_snd (jK R) t.G k @Etale (GlobalTheory.GrpTangent.etale_id_pow _ hu)
  have hn : (toTors W.ι t.G k ≫ incl t.G k) ^ k = 1 := comp_incl_pow t.G k _
  refine ⟨hA, ⟨_, _, hfin, hflat, hn, univ W.ι t.G k⟩, _, _, ⟨hfin, hflat, ?_⟩, hn, univ W.ι t.G k⟩
  have ho : IsOpenImmersion ((Over.pullback (jK R)).map (toTors W.ι t.G k)).left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) _ _
      (inferInstanceAs (IsOpenImmersion (pullback.fst (torsScheme t.G k).hom W.ι)))
  have e : ((Over.pullback (jK R)).map (toTors W.ι t.G k)).left ≫ pullback.snd (torsScheme t.G k).hom (jK R) =
      pullback.snd (overW W ((Over.pullback W.ι).obj (torsScheme t.G k))).hom (jK R) :=
    Over.w ((Over.pullback (jK R)).map (toTors W.ι t.G k))
  rw [← e]
  infer_instance

end GlobalTheory.TorsOverOpen
