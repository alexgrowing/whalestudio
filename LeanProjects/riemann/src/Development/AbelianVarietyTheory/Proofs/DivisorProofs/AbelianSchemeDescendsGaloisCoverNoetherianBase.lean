import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientDescendGrpObj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeometricallyConnectedOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteActionStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquaresStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor

namespace GlobalTheory

namespace GaloisDescentNoetherian

open QuotientDescent (up up_left up_comp)

variable {X Y : Scheme.{0}} {π : X ⟶ Y} {G : Over X} {G' : Over Y} {φ : G.left ⟶ G'.left}
  {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {ν : Ga → (G.left ⟶ G.left)}

noncomputable def act (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    pullback T.hom π ⟶ pullback T.hom π :=
  pullback.lift (pullback.fst T.hom π) (pullback.snd T.hom π ≫ ρ a)
    (by rw [Category.assoc, hc.inv, pullback.condition])

theorem act_fst (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    act hc T a ≫ pullback.fst T.hom π = pullback.fst T.hom π := pullback.lift_fst _ _ _

theorem act_snd (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    act hc T a ≫ pullback.snd T.hom π = pullback.snd T.hom π ≫ ρ a := pullback.lift_snd _ _ _

theorem isGaloisCover_act (hc : IsGaloisCover Ga ρ π) (T : Over Y) :
    IsGaloisCover Ga (act hc T) (pullback.fst T.hom π) :=
  ((GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).2.2 _ _ (pullback.fst T.hom π) (act hc T) (pullback.snd T.hom π) T.hom
    (act_snd hc T) pullback.condition.symm).2 (IsPullback.of_hasPullback T.hom π).flip (act_fst hc T)

theorem cover_ext (hc : IsGaloisCover Ga ρ π) {Z : Scheme.{0}} {f g : Y ⟶ Z} (h : π ≫ f = π ≫ g) :
    f = g :=
  ((GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).1 Z (π ≫ g) fun a ↦ by rw [← Category.assoc, hc.inv]).unique h rfl

theorem up_injective (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π) {T : Over Y}
    {x y : T ⟶ G'} (e : up H x = up H y) : x = y := by
  refine Over.OverMorphism.ext (cover_ext (isGaloisCover_act hc T) ?_)
  rw [← up_left H, ← up_left H, e]

noncomputable def equivariant [GrpObj G] (hc : IsGaloisCover Ga ρ π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (T : Over Y) : Subgroup ((Over.pullback π).obj T ⟶ G) :=
  ⨅ a : Ga, (preHom (Over.homMk (act hc T a) (act_snd hc T a))).eqLocus
    (pushHom (hν a) ((Over.pullback π).obj T))

theorem mem_equivariant [GrpObj G] (hc : IsGaloisCover Ga ρ π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) {T : Over Y} {w : (Over.pullback π).obj T ⟶ G} :
    w ∈ equivariant hc hν T ↔ ∀ a, act hc T a ≫ w.left = w.left ≫ ν a := by
  simp only [equivariant, Subgroup.mem_iInf]
  exact ⟨fun h a ↦ congrArg (fun z ↦ z.left) (h a), fun h a ↦ Over.OverMorphism.ext (h a)⟩

theorem exists_up [GrpObj G] (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (hφ : ∀ a, ν a ≫ φ = φ) {T : Over Y}
    {w : (Over.pullback π).obj T ⟶ G} (hw : w ∈ equivariant hc hν T) : ∃ z : T ⟶ G', up H z = w := by
  have hc' := isGaloisCover_act hc T
  obtain ⟨z, hz, -⟩ := (GlobalTheory.T.galoisCover_descent_and_cartesian_squares _ _ _ Ga _ hc').1 _ (w.left ≫ φ) fun a ↦ by
    rw [← Category.assoc, (mem_equivariant hc hν).mp hw a, Category.assoc, hφ]
  refine ⟨Over.homMk z (cover_ext hc' ?_), QuotientDescent.hom_ext H ((up_left H _).trans hz)⟩
  rw [reassoc_of% hz, H.w, pullback.condition]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ π) (Over.w w))

theorem up_mem [GrpObj G] (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (hφ : ∀ a, ν a ≫ φ = φ) {T : Over Y} (z : T ⟶ G') :
    up H z ∈ equivariant hc hν T := (mem_equivariant hc hν).mpr fun a ↦ by
  have e : (up H z).left ≫ G.hom = pullback.snd T.hom π := Over.w _
  have h₁ := act_fst hc T a
  refine H.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, hφ, up_left, reassoc_of% h₁]
  · rw [Category.assoc, Category.assoc, (hν a).1.w, e, act_snd, reassoc_of% e]

theorem exists_grpObj [GrpObj G] [IsCommMonObj G] (hc : IsGaloisCover Ga ρ π)
    (H : IsPullback φ G.hom G'.hom π) (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a))
    (hφ : ∀ a, ν a ≫ φ = φ) : ∃ _ : GrpObj G', IsCommMonObj G' ∧ IsGrpPullback G G' π φ := by
  have inj {T : Over Y} {x y : T ⟶ G'} (e : up H x = up H y) : x = y := up_injective hc H e
  have mem {T : Over Y} (z : T ⟶ G') := up_mem hc H hν hφ z
  obtain ⟨m, hm⟩ := exists_up hc H hν hφ (mul_mem (mem (fst G' G')) (mem (snd G' G')))
  obtain ⟨e, he⟩ := exists_up hc H hν hφ (T := 𝟙_ _) (one_mem _)
  obtain ⟨i, hi⟩ := exists_up hc H hν hφ (inv_mem (mem (𝟙 G')))
  have hm' {T : Over Y} (u : T ⟶ G' ⊗ G') :
      up H (u ≫ m) = up H (u ≫ fst _ _) * up H (u ≫ snd _ _) := by
    rw [up_comp, hm, MonObj.comp_mul, ← up_comp, ← up_comp]
  have he' {T : Over Y} (u : T ⟶ 𝟙_ _) : up H (u ≫ e) = 1 := by
    rw [up_comp, he, MonObj.comp_one]
  letI : GrpObj G' :=
    { one := e
      mul := m
      one_mul := inj (by
        rw [hm', whiskerRight_fst, he', _root_.one_mul, whiskerRight_snd, leftUnitor_hom])
      mul_one := inj (by
        rw [hm', whiskerLeft_snd, he', _root_.mul_one, whiskerLeft_fst, rightUnitor_hom])
      mul_assoc := inj (by
        rw [← Category.assoc, hm' (m ▷ G'), hm' (_ ≫ G' ◁ m), whiskerRight_fst, whiskerRight_snd,
          Category.assoc, Category.assoc, whiskerLeft_fst, whiskerLeft_snd, hm' (fst _ _),
          ← Category.assoc _ _ m, hm', Category.assoc, Category.assoc, associator_hom_fst,
          associator_hom_snd_fst, associator_hom_snd_snd, _root_.mul_assoc])
      inv := i
      left_inv := inj (by rw [hm', he', lift_fst, lift_snd, hi, inv_mul_cancel])
      right_inv := inj (by rw [hm', he', lift_fst, lift_snd, hi, mul_inv_cancel]) }
  have hmul {T : Over Y} (x y : T ⟶ G') : up H (x * y) = up H x * up H y := by
    rw [Hom.mul_def]
    exact (hm' _).trans (by rw [lift_fst, lift_snd])
  have hcomm : IsCommMonObj G' := ⟨inj (by
    refine (hm' _).trans (Eq.trans ?_ hm.symm)
    rw [braiding_hom_fst, braiding_hom_snd, mul_comm])⟩
  have sec {T : Over X} : ∃ s : T ⟶ (Over.pullback π).obj (Over.mk (T.hom ≫ π)),
      s.left ≫ pullback.fst _ π = 𝟙 T.left :=
    ⟨Over.homMk (pullback.lift (𝟙 T.left) T.hom (Category.id_comp _)) (pullback.lift_snd ..),
      pullback.lift_fst ..⟩
  refine ⟨inferInstance, hcomm, H, fun T x y x₀ y₀ hx hy ↦ ?_⟩
  obtain ⟨s, hs⟩ := sec (T := T)
  have k (z : Over.mk (T.hom ≫ π) ⟶ G') : (s ≫ up H z).left ≫ φ = z.left := by
    rw [Over.comp_left, Category.assoc, up_left, reassoc_of% hs]
  rw [← k, hmul, MonObj.comp_mul, QuotientDescent.hom_ext H ((k x₀).trans hx),
    QuotientDescent.hom_ext H ((k y₀).trans hy)]

end GaloisDescentNoetherian

open GaloisDescentNoetherian

theorem abelianScheme_descends_galoisCover_noetherian :
    ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (G : Over X) [GrpObj G] (ν : Ga → (G.left ⟶ G.left)), IsGaloisCover Ga ρ π → IsQProjOver (G.hom ≫ π ≫ sY) → IsAbelianScheme G → (∀ a, IsGrpPullback G G (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → ∃ (G' : Over Y) (_ : GrpObj G') (φ : G.left ⟶ G'.left), IsAbelianScheme G' ∧ IsGrpPullback G G' π φ ∧ IsGaloisCover Ga ν φ := by
  intro K _ _ X Y π sY Ga _ ρ G _ ν hc hq hG hν h1 hmul
  have := hc.finite
  have hinv (a : Ga) : ν a ≫ G.hom ≫ π = G.hom ≫ π := by
    rw [← Category.assoc, (hν a).1.w, Category.assoc, hc.inv]
  obtain ⟨Z, φ, sZ, -, hφ, -⟩ := GlobalTheory.T.exists_galoisCover_quotient_freeFiniteAction K G.left (G.hom ≫ π ≫ sY) Ga ν hq h1 hmul
    (fun a ↦ by rw [reassoc_of% (hinv a)]) (fun k _ _ y a hy ↦ by
      refine (hc.fibre k (y ≫ G.hom) (y ≫ G.hom) rfl).unique ?_ ?_
      · rw [Category.assoc, ← (hν a).1.w, reassoc_of% hy]
      · rw [hc.one, Category.comp_id])
  obtain ⟨v, hv, -⟩ := (GlobalTheory.T.galoisCover_descent_and_cartesian_squares _ _ φ Ga ν hφ).1 Y (G.hom ≫ π) hinv
  have H : IsPullback φ G.hom (Over.mk v).hom π :=
    (((GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).2.2 _ _ φ ν G.hom v (fun a ↦ (hν a).1.w) hv.symm).1 hφ).flip
  have := hG.comm
  obtain ⟨inst, hcomm, hp⟩ := exists_grpObj (G' := Over.mk v) hc H hν hφ.inv
  refine ⟨Over.mk v, inst, φ, ?_, hp, hφ⟩
  have := hc.fin
  have := hc.etale
  have := hc.onto
  have := hφ.fin
  have := hφ.onto
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) π :=
    ⟨⟨‹_›, inferInstance⟩, inferInstance⟩
  have hs : Smooth (Over.mk v).hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) H.flip hQ ‹_›
  have hu : UniversallyClosed (Over.mk v).hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) H.flip hQ inferInstance
  have hsep : IsSeparated (Over.mk v).hom := by
    have : IsSeparated (φ ≫ (Over.mk v).hom) := by rw [H.w]; infer_instance
    exact SemiAbelianDescent.isSeparated_of_comp φ _
  exact ⟨hcomm, hs, ⟨⟩, SemiAbelianDescent.geometricallyConnected_of_isPullback H⟩

end GlobalTheory
