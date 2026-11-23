import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifAfterFin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalPolarisationMumfordBundleAlgClosuStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteGaloisDescentPrincipalPolarisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteLocalExtensionFractionRingOfGaloisStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumDesc

set_option maxHeartbeats 1000000 in

theorem exists_polAV_field : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 2) ![(lift (snd A A) (fst A A) : G2 A ⟶ G2 A).left, 𝟙 (G2 A).left] ![1, -1]), u.IsGen) → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 3) ![(lift (fst A (A ⊗ A) * (snd A (A ⊗ A) ≫ fst A A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (lift (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (snd A (A ⊗ A) : A ⊗ (A ⊗ A) ⟶ G2 A).left] ![1, -1, -1]), u.IsGen) → Out.RelAmple A (PP.pull (lift (𝟙 A) (𝟙 A) : A ⟶ G2 A).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : LB.Gen (PP.pull (lift (snd A T ≫ x) (fst A T) : A ⊗ T ⟶ G2 A).left), t.IsGen) → x = toUnit T ≫ η[A]) → ∃ (E : Type) (_ : Field E) (_ : Algebra K E), FiniteDimensional K E ∧ IsGalois K E ∧ ∃ (A₁ : PolAV (Sp E)) (gen : (Over.pullback (spMap (algebraMap K E))).obj A ≅ A₁.A), IsMonHom gen.hom ∧ ∀ κ : (G2 ((Over.pullback (spMap (algebraMap K E))).obj A)).left ⟶ (G2 A).left, Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K E))) κ → LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K E))).obj A) (A₁.L.pull gen.hom.left)) (PP.pull κ) := by
  intro K _ _ A _ _ hA PP hPP hs ha hm hk
  obtain ⟨κ, hκ⟩ : ∃ κ : (G2 ((Over.pullback (spMap (algebraMap K (AlgebraicClosure K)))).obj A)).left ⟶ (G2 A).left,
      Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K (AlgebraicClosure K)))) κ :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare (isGrpPullback_pullback A _).1.w⟩
  obtain ⟨L, hL, hS, hI, hM, hT⟩ := GlobalTheory.T.exists_principalPolarisation_mumfordBundle_algClosure K A hA PP hPP hs ha hm hk (AlgebraicClosure K) κ hκ
  exact GlobalTheory.T.exists_finite_galois_descent_principal_polarisation K A hA PP hPP (AlgebraicClosure K) κ hκ L hL hS hI hM hT

set_option maxHeartbeats 1000000 in

theorem exists_extLam_finExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ PP : LB (G2 G).left, PP.IsLB → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (PP.pull κ₀) (K := Fin 2) ![(lift (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : G2 ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, 𝟙 (G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1]), u.IsGen) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (PP.pull κ₀) (K := Fin 3) ![(lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) * (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1, -1]), u.IsGen) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → Out.RelAmple ((Over.pullback (jK R)).obj G) ((PP.pull κ₀).pull (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left)) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∀ (T : Over (Sp (FractionRing R))) (x : T ⟶ ((Over.pullback (jK R)).obj G)), (∃ t : LB.Gen ((PP.pull κ₀).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left), t.IsGen) → x = toUnit T ≫ η[((Over.pullback (jK R)).obj G)]) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ ExtLam G₁ (A₁.L.pull gen₁.hom.left) (PP.pull β₂) := by
  intro R _ _ _ hR G _ _ hab PP hPP hsym hadd hamp hker
  have hp := isGrpPullback_pullback G (jK R)
  obtain ⟨κ₀, hκ₀⟩ : ∃ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left,
      Geo.Tor.IsSquare (pullback.fst G.hom (jK R)) κ₀ := ⟨_, GlobalTheory.LamPull.exists_isSquare hp.1.w⟩
  haveI : CharZero R := hR.2
  haveI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨E, _, _, hfd, hgal, A₁, gen, hgen, hLam⟩ :=
    exists_polAV_field (FractionRing R) ((Over.pullback (jK R)).obj G) hab (PP.pull κ₀) (pull_isLB hPP κ₀)
      (hsym κ₀ hκ₀) (hadd κ₀ hκ₀) (hamp κ₀ hκ₀) (hker κ₀ hκ₀)
  obtain ⟨R', _, _, _, ρ, t, hρ, ht⟩ := GlobalTheory.T.exists_finiteLocalExtension_fractionRing_of_galois R hR E hfd hgal
  haveI := hgen
  have hsq : (spMap t) ≫ (spMap (algebraMap (FractionRing R) E)) ≫ jK R = jK R' ≫ spMap ρ := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    exact ht r
  have hE := isGrpPullback_pullback ((Over.pullback (jK R)).obj G) (spMap (algebraMap (FractionRing R) E))
  have hβ := isGrpPullback_pullback G (spMap ρ)
  have hp₁ := isGrpPullback_pullback ((Over.pullback (spMap ρ)).obj G) (jK R')
  have hc := (hp₁.comp hβ).congr hsq.symm rfl
  have hAEG := hE.comp hp
  have w1 : (pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ)) ≫ G.hom =
      (((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).hom ≫ (spMap t) ≫ (spMap (algebraMap (FractionRing R) E))) ≫ jK R := by
    simpa only [Category.assoc] using hc.1.w
  let a : ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).left ⟶
      ((Over.pullback (jK R)).obj G).left := pullback.lift _ _ w1
  have w2 : a ≫ ((Over.pullback (jK R)).obj G).hom =
      (((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).hom ≫ (spMap t)) ≫ (spMap (algebraMap (FractionRing R) E)) := by
    exact (pullback.lift_snd _ _ w1).trans (Category.assoc _ _ _).symm
  let φ₁ : ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).left ⟶
      ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G)).left := pullback.lift _ _ w2
  have hφ₁fst : φ₁ ≫ pullback.fst ((Over.pullback (jK R)).obj G).hom (spMap (algebraMap (FractionRing R) E)) ≫ pullback.fst G.hom (jK R) =
      pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ) := by
    simp only [φ₁, a, pullback.lift_fst_assoc, pullback.lift_fst]
  have hφ₁w : φ₁ ≫ ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G)).hom =
      ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).hom ≫ (spMap t) := pullback.lift_snd _ _ _
  have hφ := hAEG.cancel (hc.congr rfl hφ₁fst.symm) hφ₁w
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨A₀, g, hg, hgL⟩ := GlobalTheory.ArcDataDescent.exists_polPull hL.polBaseChange (spMap t) A₁
  have h1 := (hφ.comp (isGrpPullback_of_iso gen)).congr (Category.comp_id _) rfl
  obtain ⟨e, he, heg⟩ := grpPullback_iso h1 hg
  obtain ⟨β₂, hβ₂⟩ : ∃ β₂ : (G2 ((Over.pullback (spMap ρ)).obj G)).left ⟶ (G2 G).left,
      Geo.Tor.IsSquare (pullback.fst G.hom (spMap ρ)) β₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hβ.1.w⟩
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, (Over.pullback (spMap ρ)).obj G, inferInstance, inferInstance,
    pullback.fst G.hom (spMap ρ), β₂, A₀, e, ?_, ?_, ?_, ?_, ?_⟩
  · exact hρ
  · exact hβ
  · exact hβ₂
  · exact he
  refine ⟨pull_isLB hPP β₂, fun κ₂' hκ₂' => ?_⟩
  have hL1 : (A₁.L.pull gen.hom.left).IsLB := pull_isLB A₁.isLB _
  have hL0 : (A₀.L.pull e.hom.left).IsLB := pull_isLB A₀.isLB _
  have hNL : LBIso (A₀.L.pull e.hom.left) ((A₁.L.pull gen.hom.left).pull φ₁) :=
    LBIso.trans hL0 (pull_isLB A₁.isLB _) (pull_isLB hL1 φ₁)
      (GlobalTheory.ArcDataDescent.lbIso_pull hgL e.hom.left heg.symm)
      (GlobalTheory.ArcDataDescent.lbIso_pull_pull A₁.isLB gen.hom.left φ₁ rfl).symm
  obtain ⟨φ₂, hφ₂⟩ : ∃ φ₂, Geo.Tor.IsSquare φ₁ φ₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hφ.1.w⟩
  have h₁ := GlobalTheory.LamPull.lbIso_lam_pull hφ hL1 hL0 hNL hφ₂
  obtain ⟨κ, hκ⟩ : ∃ κ : (G2 ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G))).left ⟶ (G2 ((Over.pullback (jK R)).obj G)).left, Geo.Tor.IsSquare (pullback.fst ((Over.pullback (jK R)).obj G).hom (spMap (algebraMap (FractionRing R) E))) κ :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare hE.1.w⟩
  have hΛ : (abelian₂ ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G)) (A₁.L.pull gen.hom.left)).IsLB :=
    DVR.linComb_isLB _ hL1 _ _
  have hLK : LBIso (abelian₂ ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G)) (A₁.L.pull gen.hom.left))
      (PP.pull (κ ≫ κ₀)) :=
    LBIso.trans hΛ (pull_isLB (pull_isLB hPP _) κ) (pull_isLB hPP _) (hLam κ hκ)
      (GlobalTheory.ArcDataDescent.lbIso_pull_pull hPP κ₀ κ rfl)
  have h₂ := GlobalTheory.ArcDataDescent.lbIso_pull hLK φ₂ (ψ := φ₂ ≫ κ ≫ κ₀) rfl
  have hsq2 : φ₂ ≫ κ ≫ κ₀ = κ₂' ≫ β₂ := by
    apply GlobalTheory.LamPull.isSquare_unique
      (φ := pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ))
    · constructor
      · simp only [Category.assoc, hκ₀.1, reassoc_of% hκ.1, reassoc_of% hφ₂.1, hφ₁fst]
      · simp only [Category.assoc, hκ₀.2, reassoc_of% hκ.2, reassoc_of% hφ₂.2, hφ₁fst]
    · constructor
      · simp only [Category.assoc, hβ₂.1, reassoc_of% hκ₂'.1]
      · simp only [Category.assoc, hβ₂.2, reassoc_of% hκ₂'.2]
  rw [hsq2] at h₂
  have h₃ : LBIso (PP.pull (κ₂' ≫ β₂)) ((PP.pull β₂).pull κ₂') :=
    (GlobalTheory.ArcDataDescent.lbIso_pull_pull hPP β₂ κ₂' rfl).symm
  exact LBIso.trans (DVR.linComb_isLB _ hL0 _ _) (pull_isLB hΛ φ₂) (pull_isLB (pull_isLB hPP β₂) κ₂') h₁
    (LBIso.trans (pull_isLB hΛ φ₂) (pull_isLB hPP _) (pull_isLB (pull_isLB hPP β₂) κ₂') h₂ h₃)

end GlobalTheory.MumDesc
