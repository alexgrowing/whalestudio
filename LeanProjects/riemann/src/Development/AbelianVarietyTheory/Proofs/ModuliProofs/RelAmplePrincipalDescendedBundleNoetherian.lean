import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KTrivAwayOfKTrivFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKernelTrivialOfOpenCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.DescentFamily

open GlobalTheory.CechPic

theorem card_ker_pullback {S S' : Scheme.{0}} (t : S' ⟶ S) {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) :
    Nat.card {x : 𝟙_ (Over S') ⟶ (Over.pullback t).obj A // x ≫ (Over.pullback t).map ψ = 1} =
      Nat.card {x : Over.mk ((𝟙_ (Over S')).hom ≫ t) ⟶ A // x ≫ ψ = 1} := by
  have hA := isGrpPullback_pullback A t
  have hB := isGrpPullback_pullback B t
  have inj : ∀ {G : Over S} [GrpObj G] (h : IsGrpPullback ((Over.pullback t).obj G) G t (pullback.fst G.hom t)),
      Function.Injective (pushHom h (𝟙_ (Over S'))) := fun h x y e =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) (by rw [Over.w, Over.w]))
  have surj : Function.Surjective (pushHom hA (𝟙_ (Over S'))) := fun x =>
    ⟨Over.homMk (hA.1.lift x.left (𝟙_ (Over S')).hom (Over.w x)) (hA.1.lift_snd _ _ _),
      Over.OverMorphism.ext (hA.1.lift_fst _ _ _)⟩
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ ⟨inj hA, surj⟩) fun x => ?_)
  have e : pushHom hB (𝟙_ (Over S')) (x ≫ (Over.pullback t).map ψ) = pushHom hA (𝟙_ (Over S')) x ≫ ψ := by
    refine Over.OverMorphism.ext ?_
    show (x.left ≫ ((Over.pullback t).map ψ).left) ≫ pullback.fst B.hom t = (x.left ≫ pullback.fst A.hom t) ≫ ψ.left
    rw [Category.assoc, Category.assoc]
    exact congrArg (x.left ≫ ·) (pullback.lift_fst _ _ _)
  exact (map_eq_one_iff _ (inj hB)).symm.trans (Eq.congr_left e)

theorem kTriv_fibre {S : Scheme.{0}} (P : Out.PolAV S) {n : ℕ} (B : Over S) [GrpObj B] (ψ : P.A ⟶ B) (M : LB B.left)
    (hn : 0 < n) (hB : IsAbelianScheme B) (hM : M.IsLB) [IsMonHom ψ] [IsFinite ψ.left] [Etale ψ.left]
    [Surjective ψ.left] (hiso : LBIso (lbPow P.L n) (M.pull ψ.left)) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (t : Sp k ⟶ S) (hc : Nat.card {x : Over.mk (𝟙 _ ≫ t) ⟶ P.A // x ≫ ψ = 1} = n ^ P.g) :
    Out.KTriv ((Over.pullback t).obj B) (M.pull (pullback.fst B.hom t)) := by
  have hw : ((Over.pullback t).map ψ).left ≫ pullback.fst B.hom t = pullback.fst P.A.hom t ≫ ψ.left :=
    pullback.lift_fst _ _ _
  have hp : IsPullback (pullback.fst P.A.hom t) ((Over.pullback t).map ψ).left ψ.left (pullback.fst B.hom t) := by
    refine IsPullback.of_bot ?_ hw.symm (IsPullback.of_hasPullback B.hom t)
    have e : ((Over.pullback t).map ψ).left ≫ pullback.snd B.hom t = pullback.snd P.A.hom t :=
      Over.w ((Over.pullback t).map ψ)
    rw [e, Over.w ψ]
    exact IsPullback.of_hasPullback _ _
  have hL' := pull_isLB P.isLB (pullback.fst P.A.hom t)
  have hM' := pull_isLB hM (pullback.fst B.hom t)
  have h₁ : (lbPow (P.L.pull (pullback.fst P.A.hom t)) n).IsLB := LB.isLB_linComb hL' _ _
  have h₂ := pull_isLB hM' ((Over.pullback t).map ψ).left
  have h₀ := (cls_eq_iff (LB.isLB_linComb P.isLB _ _) (pull_isLB hM _)).2 hiso
  rw [cls_lbPow P.isLB, cls_pull hM] at h₀
  have he : cls _ h₁ = cls _ h₂ := by
    rw [cls_lbPow hL', cls_pull hM', cls_pull P.isLB, cls_pull hM, ← pull_comp, hw, pull_comp, ← h₀, map_nsmul]
  have hmon : IsMonHom ((Over.pullback t).map ψ) := inferInstance
  refine kTriv_of_descent firstFiveLaws.1 k (StrictPull.polPull P t) n _ ((Over.pullback t).map ψ) _ hn
    (PolPull.isAbelianScheme_of_isGrpPullback hB (isGrpPullback_pullback B t)) hM' hmon
    (MorphismProperty.of_isPullback (P := @IsFinite) hp inferInstance)
    (MorphismProperty.of_isPullback (P := @Etale) hp inferInstance)
    (MorphismProperty.of_isPullback (P := @Surjective) hp inferInstance)
    ((card_ker_pullback t ψ).trans hc) ?_
  refine (cls_eq_iff (LB.isLB_linComb h₁ _ _) (LB.isLB_linComb h₂ _ _)).1 ?_
  refine (cls_cube_two (G := (Over.pullback t).obj P.A) h₁ _ _ _).trans
    (Eq.trans ?_ (cls_cube_two (G := (Over.pullback t).obj P.A) h₂ _ _ _).symm)
  exact congrArg (fun c => lam (G := (Over.pullback t).obj P.A) c _ _) he

end GlobalTheory.DescentFamily

namespace GlobalTheory

open GlobalTheory.CechPic

theorem relAmple_kTriv_of_descent_family : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (n : ℕ) (B : Over (Sp R)) [GrpObj B] (ψ : P.A ⟶ B) (M : LB B.left), (∀ m : ℕ, 0 < m → IsUnit (m : R)) → 0 < n → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R), Nat.card {x : Over.mk t ⟶ P.A // x ≫ ψ = 1} = n ^ P.g) → LBIso (lbPow P.L n) (M.pull ψ.left) → Out.RelAmple B M ∧ Out.KTriv B M := by
  intro R _ _ P n B _ ψ M hu hn hB hM hψ hf he hs hc hiso
  have hA := P.isAb
  have hn' : (lbPow P.L n).IsLB := LB.isLB_linComb P.isLB _ _
  have hid : IsFinite (𝟙 P.A : P.A ⟶ P.A).left := by rw [Over.id_left]; infer_instance
  have a₁ : Out.RelAmple P.A (lbPow P.L n) :=
    (relAmple_finite_pow_iso _ P.A P.A (𝟙 _) P.L n hn hA hA P.isLB hid).2.1.2 P.ample
  have a₂ : Out.RelAmple P.A (M.pull ψ.left) :=
    (relAmple_finite_pow_iso _ P.A P.A (𝟙 _) _ 1 one_pos hA hA hn' hid).2.2.2 _ (pull_isLB hM _) hiso a₁
  have a₃ : Out.RelAmple B M :=
    (relAmple_finite_pow_iso _ P.A B ψ M 1 one_pos hA hB hM hf).2.2.1 inferInstance hs a₂
  refine ⟨a₃, ?_⟩
  have loc : ∀ q : PrimeSpectrum R, ∃ f : R, f ∉ q.asIdeal ∧
      Out.KTriv ((Over.pullback (spMap (algebraMap R (Localization.Away f)))).obj B)
        (M.pull (pullback.fst B.hom (spMap (algebraMap R (Localization.Away f))))) := by
    intro q
    let k := AlgebraicClosure q.asIdeal.ResidueField
    let x : R →+* k := (algebraMap q.asIdeal.ResidueField k).comp (algebraMap R q.asIdeal.ResidueField)
    have : CharZero k := charZero_of_inj_zero fun m hm => by
      by_contra h
      have := (hu m (Nat.pos_of_ne_zero h)).map x
      rw [map_natCast, hm] at this
      exact not_isUnit_zero this
    obtain ⟨f, hf, H⟩ := kTriv_away_of_kTriv_fibre firstFiveLaws.1.globalFns R B M k x hB hM a₃
      (DescentFamily.kTriv_fibre P B ψ M hn hB hM hiso k (spMap x) (hc k _))
    refine ⟨f, fun h => hf ?_, H⟩
    show algebraMap q.asIdeal.ResidueField k (algebraMap R q.asIdeal.ResidueField f) = 0
    rw [Ideal.algebraMap_residueField_eq_zero.2 h, map_zero]
  choose f hf H using loc
  let j : ∀ q, Sp (Localization.Away (f q)) ⟶ Sp R := fun q => spMap (algebraMap R (Localization.Away (f q)))
  have hj : ∀ q, IsOpenImmersion (j q) := fun q => IsOpenImmersion.of_isLocalization (f q)
  let G := fun q => (Over.pullback (j q).isoOpensRange.inv).obj ((Over.pullback (j q)).obj B)
  have gp : ∀ q, IsGrpPullback (G q) ((Over.pullback (j q)).obj B) (j q).isoOpensRange.inv (pullback.fst _ _) :=
    fun q => isGrpPullback_pullback _ _
  have hM₁ := fun q => pull_isLB hM (pullback.fst B.hom (j q))
  have hB₁ := fun q => PolPull.isAbelianScheme_of_isGrpPullback hB (isGrpPullback_pullback B (j q))
  have key := fun q => pol_pull _ _ _ (G q) _ _ _ _ (hM₁ q) (pull_isLB (hM₁ q) _) (hB₁ q) (gp q)
    ((cls_eq_iff (pull_isLB (hM₁ q) _) (pull_isLB (hM₁ q) _)).1 rfl)
  refine CoverGlue.kTriv_of_cover (Sp R) (PrimeSpectrum R) (fun q => (j q).opensRange) B G
    (fun q => pullback.fst _ (j q).isoOpensRange.inv ≫ pullback.fst B.hom (j q)) ?_
    (fun q => ((gp q).comp (isGrpPullback_pullback B (j q))).congr (Scheme.Hom.isoOpensRange_inv_comp _) rfl)
    M _ hM (fun q => pull_isLB (hM₁ q) _) (fun q => ?_) hB (fun q => (key q).1) (fun q => (key q).2.2 (H q))
  · refine top_le_iff.1 fun q _ => TopologicalSpace.Opens.mem_iSup.2 ⟨q, ?_⟩
    have : q ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (f q)))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (f q)) (f q)]
      exact hf q
    exact this
  · rw [← cls_eq_iff (pull_isLB (hM₁ q) _) (pull_isLB hM _), cls_pull (hM₁ q), cls_pull hM, cls_pull hM, pull_comp]

end GlobalTheory
