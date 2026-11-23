import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsMulEqSmulOneOfMulVecInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyPerfectSectionsComplexOfNoetherian
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmplePosPowAffineBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1VanishingAffineBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowH1VanishesGeometricFibreAllStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AmpleSecBC

open GlobalTheory.AbLaw GlobalTheory.AbLaw.SecBC

theorem isProjBy_of_openImmersion {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (hL : L.IsLB)
    (hA : RelAmple A L) {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) [IsOpenImmersion t] :
    IsProjBy (R := R) (fst (Over.mk t) A).left := by
  have hpb := isPullback_snd A (Over.mk t)
  have hL' : (L.pull (snd (Over.mk t) A).left).IsLB := LB.isLB_pull hL _
  have hR : RelAmple (Over.mk (fst (Over.mk t) A).left) (L.pull (snd (Over.mk t) A).left) :=
    relAmple_pull (A' := Over.mk (fst (Over.mk t) A).left) (f := t) hpb hL hL'
      ((isGen_iff _).1 (idIso_isGen hL')) t.opensRange (isAffineOpen_opensRange t) (fun y => ⟨y, rfl⟩) hA
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R _ _ hL').1 hR
  exact ⟨_, isLB_pw hL' d, n, s, hs⟩

theorem fieldVanishing : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → RelAmple B M → ∀ a : ℕ, 1 ≤ a → GlobalTheory.AbLaw.FirstCohomologyVanishes (GlobalTheory.AbLaw.pw M (a : ℤ)) := by
  intro K _ _ B _ _ M hB hM hA a ha
  have hM' := isLB_pw hM (a : ℤ)
  have hR := GlobalTheory.T.relAmple_pos_pow_affine_base K B M hM hA a ha
  have hP : IsProper B.hom := hB.proper
  have : CompactSpace B.left := by
    have : QuasiCompact B.hom := inferInstance
    exact (quasiCompact_iff_compactSpace B.hom).1 this
  exact GlobalTheory.T.firstCohomologyVanishes_of_isRelAcyclic_over_spec K B.left B.hom _ hM' this (GlobalTheory.AmpleGen.ampleVanishing K B hB _ hM' hR)

theorem geomVanishing : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → ∀ a : ℕ, 1 ≤ a → ∀ (T : Over S) (K : Type) [Field K] [IsAlgClosed K] (q : Spec (CommRingCat.of K) ⟶ T.left), ∃ (X' : Scheme.{0}) (π : X' ⟶ (T ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' (fst T A).left q ∧ GlobalTheory.AbLaw.FirstCohomologyVanishes ((LPow A L (a : ℤ) T).pull π) :=
  GlobalTheory.T.lineBundlePow_h1Vanishes_geometricFibre_all fieldVanishing

theorem secBaseChange_relAmple : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Rigidified A L → RelAmple A L → ∀ a : ℕ, 1 ≤ a → ∀ p : S, ∃ V : S.Opens, p ∈ V ∧ ∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (a : ℤ) (overRes (T := baseOver S) V))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S) V).left) (b' : Fin m → LB.Sec (LPow A L (a : ℤ) (baseAt t))), (∀ i, IsPullSec A L (a : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (a : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (a : ℤ) (baseAt t))) = ⊤ := by
  have hB := geomVanishing
  intro S _ A _ _ L hAb hL _ hAmp a ha p
  obtain ⟨R₀, t₀, hto, ⟨q, rfl⟩, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (X := S) (x := p) (U := ⊤) trivial
  obtain ⟨R, _⟩ := R₀
  change Spec (CommRingCat.of R) ⟶ S at t₀
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) := isLocallyNoetherian_of_isOpenImmersion t₀
  have : IsNoetherianRing R := by
    have : AlgebraicGeometry.IsNoetherian (Spec (CommRingCat.of R)) := {}
    exact (isNoetherian_Spec (R := CommRingCat.of R)).1 this
  have hpb := isPullback_snd A (Over.mk t₀)
  have hfl : Flat (fst (Over.mk t₀) A).left := by
    have : Smooth A.hom := hAb.smooth
    exact MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
  have hpr := isProjBy_of_openImmersion A L hL hAmp t₀
  obtain ⟨F⟩ := nonempty_perf_of_noetherian R _ _ hfl hpr (LPow A L (a : ℤ) (Over.mk t₀)) (LB.isLB_linComb hL _ _)
  obtain ⟨K, _, _, g₀, hg₀⟩ := exists_geomPoint (R := R) q
  obtain ⟨X', π, f', hX', hH⟩ := hB S A L hAb hL hAmp a ha (Over.mk t₀) K (Spec.map (CommRingCat.ofHom g₀))
  obtain ⟨r, m, B, hr, hB', hu⟩ := GlobalTheory.exists_matrix_basis_ker_of_exact_at_point R K g₀ _ _ _ F.D₀ F.D₁ F.comp
    (F.exact K g₀ X' π f' hX' hH)
  have aff : ∀ {R' : Type} [CommRing R'] (t : Spec (CommRingCat.of R') ⟶ S), IsAffine (Over.mk t).left :=
    fun {R'} _ _ => inferInstanceAs (IsAffine (Spec (CommRingCat.of R')))
  have := aff t₀
  have ex : ∀ i, ∃ s, RepAt F (𝟙 (Over.mk t₀)) (fun k => cfun (𝟙 (Over.mk t₀)) (B k i)) s := fun i =>
    (repAt_main (F := F) (𝟙 (Over.mk t₀))).1 _ (by
      have e := congrArg (fun Q => Q.map (cfun (𝟙 (Over.mk t₀)))) hB'
      simp only [Matrix.map_mul] at e
      funext l
      exact (congrFun (congrFun e l) i).trans (map_zero (cfun (𝟙 (Over.mk t₀)))))
  choose b₀ hb₀ using ex
  let D : (Spec (CommRingCat.of R)).Opens :=
    (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  have hq : q ∈ D := by
    have : D = PrimeSpectrum.basicOpen r := basicOpen_eq_of_affine (R := CommRingCat.of R) r
    rw [this]
    exact fun hq => hr (hg₀ r hq)
  let l : (t₀ ''ᵁ D).toScheme ⟶ Spec (CommRingCat.of R) := IsOpenImmersion.lift t₀ (t₀ ''ᵁ D).ι (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩)
  have hl : l ≫ t₀ = (t₀ ''ᵁ D).ι := IsOpenImmersion.lift_fac _ _ _
  have hlD : ∀ y, l y ∈ D := fun y => by
    obtain ⟨x, hx, e⟩ := y.2
    have : t₀ (l y) = t₀ x := (congrArg (fun Q => Q y) hl).trans e.symm
    rw [t₀.isOpenEmbedding.injective this]
    exact hx
  let hD : overRes (T := baseOver S) (t₀ ''ᵁ D) ⟶ Over.mk t₀ := Over.homMk l (hl.trans (Category.comp_id _).symm)
  choose b hb using fun i => exists_pullSec A L (a : ℤ) hD (b₀ i)
  refine ⟨t₀ ''ᵁ D, ⟨q, hq, rfl⟩, m, b, fun R' _ t b' hb' => ?_⟩
  have : IsAffine (baseAt t).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R')))
  refine basis_of_rep (F := F) (homAt t ≫ hD ≫ 𝟙 _) B hB' (hu _ _ ?_) b'
    fun i => ((hb₀ i).pull hD (hb i)).pull (homAt t) (hb' i)
  refine (baseAt t).left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => ?_
  refine ((baseAt t).left.mem_basicOpen _ y hy).1 ?_
  have := Scheme.preimage_basicOpen_top (homAt t ≫ hD ≫ 𝟙 _).left ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  exact (congrArg (y ∈ ·) this).mp (hlD (t y))

end GlobalTheory.AmpleSecBC
