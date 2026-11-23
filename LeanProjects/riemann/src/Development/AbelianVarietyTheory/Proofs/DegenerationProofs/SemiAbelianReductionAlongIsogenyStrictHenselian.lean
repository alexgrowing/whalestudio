import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeutralGroupModelStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueHomExtensionSmoothConnSemiAbelianDvrStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisibleStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionOfSurjectiveOfDimEqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfSchemeTheoreticallyDominant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothOfRelativeDimensionOfGeneric

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.IsogRed

variable {S T : Scheme.{0}} (f : T ⟶ S)

noncomputable def sec {G : Over S} (s : 𝟙_ (Over S) ⟶ G) : 𝟙_ (Over T) ⟶ (Over.pullback f).obj G :=
  Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map s

theorem sec_comp {G G' : Over S} (s : 𝟙_ (Over S) ⟶ G) (I : G ⟶ G') :
    sec f (s ≫ I) = sec f s ≫ (Over.pullback f).map I := by
  simp only [sec, Functor.map_comp, Category.assoc]

theorem sec_pow {G : Over S} [GrpObj G] (s : 𝟙_ (Over S) ⟶ G) (n : ℕ) : sec f (s ^ n) = sec f s ^ n := by
  simp only [sec, ← MonObj.comp_pow]
  congr 1
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Functor.map_mul, ih]

theorem sec_left {G : Over S} (s : 𝟙_ (Over S) ⟶ G) :
    (sec f s).left ≫ pullback.fst G.hom f = f ≫ s.left := by
  have hw := Over.w (Functor.LaxMonoidal.ε (Over.pullback f))
  have hc := pullback.condition (f := (𝟙_ (Over S)).hom) (g := f)
  simp only [sec, Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]
  simp at hw hc ⊢

theorem sec_eq {G : Over S} (s : 𝟙_ (Over S) ⟶ G) (x : 𝟙_ (Over T) ⟶ (Over.pullback f).obj G)
    (h : f ≫ s.left = x.left ≫ pullback.fst G.hom f) : sec f s = x := by
  ext1
  apply pullback.hom_ext
  · rw [sec_left, h]
  · have h1 := Over.w (sec f s)
    have h2 := Over.w x
    simp only [Over.pullback_obj_hom] at h1 h2
    rw [h1, h2]

theorem sec_injective [IsSchemeTheoreticallyDominant f] {G : Over S} [IsSeparated G.hom]
    {s t : 𝟙_ (Over S) ⟶ G} (h : sec f s = sec f t) : s = t := by
  refine GlobalTheory.over_ext_of_schemeTheoreticallyDominant (Y := 𝟙_ (Over S)) f ?_
  rw [← sec_left, ← sec_left, h]

theorem smConn_baseChange (G : Over S) [GrpObj G] (h : SmConn G) : SmConn ((Over.pullback f).obj G) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩ <;> (try simp only [Over.pullback_obj_hom]) <;> infer_instance

theorem sec_residue_surjective {R : Type} [CommRing R] [HenselianLocalRing R] (G : Over (Sp R)) [Smooth G.hom]
    (x : 𝟙_ _ ⟶ spFibre G) : ∃ s : 𝟙_ _ ⟶ G, sec (spMap (IsLocalRing.residue R)) s = x := by
  have hx : (x.left ≫ pullback.fst G.hom (spMap (IsLocalRing.residue R))) ≫ G.hom =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ 𝟙 _ := by
    have hw := Over.w x
    simp only [Over.pullback_obj_hom] at hw
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
    simp
  obtain ⟨⟨y, hy⟩, hyx⟩ := GlobalTheory.reducePoint_residue_surjective G.hom R (𝟙 _) ⟨_, hx⟩
  refine ⟨Over.homMk y (by simpa using hy), sec_eq _ _ _ ?_⟩
  simpa [GlobalTheory.reducePoint] using congrArg Subtype.val hyx

theorem relDim_spFibre {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] (hG : SmConn G) (g : ℕ)
    (h : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K))).obj G).hom) :
    SmoothOfRelativeDimension g (spFibre G).hom := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hG
  have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{0} g) :=
    smoothOfRelativeDimension_isStableUnderBaseChange g
  have hG0 : SmoothOfRelativeDimension g G.hom := by
    apply GlobalTheory.GenericDim.smoothOfRelativeDimension_of_generic R G g
    unfold ReciprocityTheory.ChartRestriction.G.Out.jK
    obtain ⟨ψ, hψ⟩ : ∃ ψ : K →+* FractionRing R, ψ.comp (algebraMap R K) = algebraMap R (FractionRing R) :=
      ⟨_, (IsLocalization.algEquiv (nonZeroDivisors R) K (FractionRing R)).toAlgHom.comp_algebraMap⟩
    have hK : SmoothOfRelativeDimension g
        (pullback.snd G.hom (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := h
    rw [← hψ, CommRingCat.ofHom_comp, Spec.map_comp]
    have key : pullback.snd G.hom (Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) =
        (pullbackLeftPullbackSndIso G.hom _ _).inv ≫
          pullback.snd (pullback.snd G.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            (Spec.map (CommRingCat.ofHom ψ)) := by
      rw [Iso.eq_inv_comp, pullbackLeftPullbackSndIso_hom_snd]
    rw [key]
    exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension.{0} g)
      (hP := @MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ _
        (smoothOfRelativeDimension_isStableUnderBaseChange g)) _ _).mpr
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (self := smoothOfRelativeDimension_isStableUnderBaseChange g) (IsPullback.of_hasPullback _ _) hK)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (self := smoothOfRelativeDimension_isStableUnderBaseChange g) (IsPullback.of_hasPullback _ _) hG0

theorem pow_comp_isogeny {Z A B : Over T} [GrpObj A] [GrpObj B] (i : A ⟶ B) (r : B ⟶ A) [IsMonHom i] {m : ℕ}
    (hri : r ≫ i = 𝟙 _ ^ m) (c : ℕ) (x : Z ⟶ B) : ((x ≫ r) ^ c) ≫ i = x ^ (m * c) := by
  rw [MonObj.pow_comp, Category.assoc, hri, MonObj.comp_pow, Category.comp_id, pow_mul]

theorem sec_eq_comp {G : Over S} {A : Over T} (e : (Over.pullback f).obj G ≅ A) (s : 𝟙_ (Over S) ⟶ G)
    (a : 𝟙_ (Over T) ⟶ A) (h : f ≫ s.left = a.left ≫ e.inv.left ≫ pullback.fst G.hom f) : sec f s = a ≫ e.inv := by
  apply sec_eq
  rw [h, Over.comp_left, Category.assoc]

theorem exists_section {G G' : Over S} [GrpObj G] [GrpObj G'] [IsSchemeTheoreticallyDominant f] [IsSeparated G'.hom]
    {A : Over T} [GrpObj A] (e : (Over.pullback f).obj G ≅ A) (i : A ⟶ (Over.pullback f).obj G')
    (r : (Over.pullback f).obj G' ⟶ A) [IsMonHom i] {m c : ℕ} (hri : r ≫ i = 𝟙 _ ^ m) (I : G ⟶ G')
    (hI : (Over.pullback f).map I = e.hom ≫ i)
    (hext : ∀ a : 𝟙_ _ ⟶ A, ∃ s : 𝟙_ _ ⟶ G, f ≫ s.left = (a ^ c).left ≫ e.inv.left ≫ pullback.fst G.hom f)
    (z : 𝟙_ _ ⟶ G') : ∃ s : 𝟙_ _ ⟶ G, s ≫ I = z ^ (m * c) := by
  obtain ⟨s, hs⟩ := hext (sec f z ≫ r)
  refine ⟨s, sec_injective f ?_⟩
  rw [sec_comp, sec_eq_comp f e s _ hs, hI, sec_pow, Category.assoc, e.inv_hom_id_assoc,
    pow_comp_isogeny i r hri]

theorem semiAbelian_reduction_of_isogeny : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] (G' : Over (Sp R)) [GrpObj G'] (g m : ℕ), IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom → IsSemiAbelian G' → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K))).obj G').hom → ∀ (i : A ⟶ (Over.pullback (spMap (algebraMap R K))).obj G') (r : (Over.pullback (spMap (algebraMap R K))).obj G' ⟶ A), IsMonHom i → IsMonHom r → 1 ≤ m → r ≫ i = 𝟙 _ ^ m → ∃ (G : Over (Sp R)) (_ : GrpObj G) (e : (Over.pullback (spMap (algebraMap R K))).obj G ≅ A), SmConn G ∧ IsMonHom e.hom ∧ Nonempty (TorusExtension (spFibre G)) := by
  intro R K _ _ _ _ _ hSH A _ G' _ g m hA hP hG' hgA hgG' i r hi hr hm hri
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := id hG'
  have hSG' : SmConn G' := ⟨a1, a2, a3, a4, a5⟩
  have : IsCommMonObj A := hA.1
  obtain ⟨M, hMg, hM, he, c, hc, hext⟩ := GlobalTheory.T.exists_neutral_group_model' R K hSH A hA hP
  obtain ⟨hdvr, hhens, hac, hfr⟩ := hSH
  refine ⟨M.Y, hMg, M.e, hM, he, ?_⟩
  obtain ⟨F, ⟨hF, hFe⟩, -⟩ := GlobalTheory.T.existsUnique_hom_extension_smoothConn_semiAbelian_dvr R K M.Y G' hM hG' (M.e.hom ≫ i) inferInstance
  have hgM : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K))).obj M.Y).hom := by
    have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{0} g) :=
      smoothOfRelativeDimension_isStableUnderBaseChange g
    rw [← Over.w M.e.hom]
    exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension.{0} g)
      (hP := @MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ _
        (smoothOfRelativeDimension_isStableUnderBaseChange g)) ((Over.forget _).mapIso M.e).hom A.hom).mpr hgA
  refine GlobalTheory.T.torusExtension_of_surjective_of_dim_eq' (IsLocalRing.ResidueField R) (spFibre M.Y) (spFibre G') g
    (smConn_baseChange _ _ hM) (smConn_baseChange _ _ hSG')
    (relDim_spFibre M.Y hM g hgM) (relDim_spFibre G' hSG' g hgG')
    (a6 _ _) ((Over.pullback (spMap (IsLocalRing.residue R))).map F) inferInstance ?_
  intro y
  obtain ⟨w, hw⟩ := GlobalTheory.T.torusExtension_points_divisible' (IsLocalRing.ResidueField R) (spFibre G') (a6 _ _) (m * c)
    (by simpa using Nat.mul_le_mul hm hc) y
  obtain ⟨z, hz⟩ := sec_residue_surjective G' w
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) :=
    GlobalTheory.schemeTheoreticallyDominant_fractionField R K
  obtain ⟨s, hs⟩ := exists_section (spMap (algebraMap R K)) M.e i r hri F hFe (fun a => hext a) z
  refine ⟨sec (spMap (IsLocalRing.residue R)) s, ?_⟩
  rw [← sec_comp, hs, sec_pow, hz, hw]

end GlobalTheory.IsogRed
