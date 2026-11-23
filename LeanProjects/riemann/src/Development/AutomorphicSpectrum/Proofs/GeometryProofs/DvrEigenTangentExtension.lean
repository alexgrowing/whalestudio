import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianHomLieExtendsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeMapStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameIffEigenspaceBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.EigLin

theorem model_cast {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x y : Sp R ⟶ S} (h : x = y)
    {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) :
    ∃ M' : LieModel G y L, ∀ l, (M'.pt l).left = (M.pt l).left := by
  subst h
  exact ⟨M, fun _ => rfl⟩

theorem mem_span_iff : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (T : Over (Sp V)) [GrpObj T] [IsCommMonObj T] (GK : Over (Sp K)) [GrpObj GK] (φ₀ : GK.left ⟶ T.left)
    (Oe : Type) [CommRing Oe] (actT : OAct Oe T) (actK : OAct Oe GK) (g n : ℕ) (ML : LieModel GK (𝟙 _) (Fin g → K))
    (ρK : Oe →+* Module.End K (Fin g → K)) (σV : Oe →+* V) (vV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ T)) (b : Fin n → Fin g → K),
    IsGrpPullback GK T (spMap (algebraMap V K)) φ₀ → (∀ a, (actK.act a).left ≫ φ₀ = φ₀ ≫ (actT.act a).left) →
    ML.IsActOf actK.act ρK → IsEigFrame actT (𝟙 _) σV vV →
    (∀ i, (ML.pt (b i)).left ≫ φ₀ = spMap (dualMap (algebraMap V K)) ≫ (vV i).left) →
    ∀ w, w ∈ Submodule.span V (Set.range b) ↔
      (∃ a : epsAt (𝟙 (Sp V)) ⟶ T, IsTanAt T (𝟙 _) a ∧ (ML.pt w).left ≫ φ₀ = spMap (dualMap (algebraMap V K)) ≫ a.left) ∧
        ∀ r, ρK r w = algebraMap V K (σV r) • w := by
  intro V K _ _ _ _ _ _ T _ _ GK _ φ₀ Oe _ actT actK g n ML ρK σV vV b hpull hact hML hF hb w
  have halg : Function.Injective (algebraMap V K) := IsFractionRing.injective V K
  obtain ⟨ET, _, _, ⟨MT⟩⟩ := GlobalTheory.T.exists_lie_model (Sp V) T V (𝟙 _)
  have hpt : 𝟙 (Sp K) ≫ spMap (algebraMap V K) =
      Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ 𝟙 (Sp V) := by simp
  obtain ⟨M', hM'⟩ := model_cast hpt (LieMove.pushModel hpull ML)
  obtain ⟨j, hj1, hj2, -⟩ := GlobalTheory.T.lie_model_base_change_map (Sp V) T V K (𝟙 _) ET (Fin g → K) MT M'
  have key1 : ∀ e, (ML.pt (j e)).left ≫ φ₀ = spMap (dualMap (algebraMap V K)) ≫ (MT.pt e).left := fun e =>
    (hM' (j e)).symm.trans (hj1 e)
  have uniq : ∀ u u' : Fin g → K, (ML.pt u).left ≫ φ₀ = (ML.pt u').left ≫ φ₀ → u = u' := fun u u' h =>
    ML.inj (LieMove.pushEps_inj hpull (Over.OverMorphism.ext h))
  have hjinj : Function.Injective j := fun e e' h =>
    MT.inj (LieTangent.tan_ext halg (MT.tan e) (MT.tan e') ((key1 e).symm.trans (by rw [h]; exact key1 e')))
  have eig : ∀ r e e', MT.pt e' = MT.pt e ≫ actT.act r → j e' = ρK r (j e) := by
    intro r e e' h
    apply uniq
    have h1 : ML.pt (ρK r (j e)) = ML.pt (j e) ≫ actK.act r := hML r (j e)
    rw [key1 e', h1, Over.comp_left, Category.assoc, hact r, ← Category.assoc, key1 e, h, Over.comp_left,
      Category.assoc]
  have htan : ∀ r v, IsTanAt T (𝟙 _) v → IsTanAt T (𝟙 _) (v ≫ actT.act r) := by
    intro r v h
    haveI := actT.hom r
    refine (LieTangent.isTanAt_iff _).2 ?_
    rw [← Category.assoc, (LieTangent.isTanAt_iff _).1 h]
    exact MonObj.one_comp _
  choose eV heV using fun i => MT.onto (vV i) (hF.1 i).1
  obtain rfl : vV = fun i => MT.pt (eV i) := funext fun i => (heV i).symm
  have hbj : ∀ i, b i = j (eV i) := fun i => uniq _ _ ((hb i).trans (key1 (eV i)).symm)
  have jcomb : ∀ c : Fin n → V, j (∑ i, c i • eV i) = ∑ i, c i • b i := fun c => by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hj2, ← hbj, algebraMap_smul]
  constructor
  · intro hw
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 hw
    refine ⟨⟨MT.pt (∑ i, c i • eV i), MT.tan _, ?_⟩, fun r => ?_⟩
    · rw [← jcomb]
      exact key1 _
    · have heig : ∀ i, ρK r (b i) = algebraMap V K (σV r) • b i := by
        intro i
        have h : MT.pt (σV r • eV i) = MT.pt (eV i) ≫ actT.act r :=
          Over.OverMorphism.ext ((MT.smul _ _).trans ((hF.1 i).2 r).symm)
        have h2 := eig r _ _ h
        rw [← hbj i, hj2, ← hbj i] at h2
        exact h2.symm
      have hs : ∀ i, c i • b i = algebraMap V K (c i) • b i := fun i => (algebraMap_smul K (c i) (b i)).symm
      simp only [hs, map_sum, map_smul, heig, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  · rintro ⟨⟨a, ha, hka⟩, hr⟩
    obtain ⟨e, rfl⟩ := MT.onto a ha
    obtain rfl : w = j e := uniq _ _ (hka.trans (key1 e).symm)
    have hE : GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec actT (𝟙 _) σV (MT.pt e) := by
      refine ⟨MT.tan e, fun r => ?_⟩
      obtain ⟨e', he'⟩ := MT.onto _ (htan r _ (MT.tan e))
      have h1 := eig r e e' he'
      rw [hr r, ← hj2] at h1
      rw [← he', hjinj h1]
      exact MT.smul _ _
    obtain ⟨c, hc, -⟩ := hF.2 _ hE
    have he : e = ∑ i, c i • eV i := MT.inj ((LieEigFrame.isComb_pt_iff MT eV c _).1 hc)
    rw [he, jcomb]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Flat.EigLin
