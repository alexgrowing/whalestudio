import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRestStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionAbelianCompletionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsPlaceOverFiniteExtensionOfIsPlaceOverStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenGaloisSubgroupTraceNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemWeilGroupAtPlaceOfFixesExtensionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtensionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalArtinCompNormCompatStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepCharacterSupportLiftTransTowerStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.ExistsCuspidalCharLiftOfSolvableCmExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupWeilElementCharacterKernelStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.Chl

open GlobalTheory.RoadU

namespace GalTw
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.TorLiftC

theorem exists_cm_lift_fix_charKer : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r → ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)), (∀ j, IsSmoothChar (ξ j)) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, deg g ≠ 0 → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω) (P : CuspSub M n) (χ' : HChar (maximalRealSubfield M)), InScope .all l P χ' ∧ CharLift π P ∧ (∀ x : M, (g : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) ∧ ∀ t : Weil h, deg t = 0 → (∀ x : M, (t : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) → ∀ j, ξ j (a t) = 1 := by
  intro hI Ω _ E _ _ _ _ _ l _ ι n hn π χ hπ r hr w A h ξ hξ a ha g hg
  have lies : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
      [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
      {v : HeightOneSpectrum (𝓞 K)} {u : HeightOneSpectrum (𝓞 L)},
      IsPlaceOver A v → IsPlaceOver A u → u.asIdeal.LiesOver v.asIdeal := by
    intro K L _ _ _ _ _ _ _ _ v u hv hu
    refine ⟨?_⟩
    ext x
    rw [← hv x, Ideal.under, Ideal.mem_comap, ← hu, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  obtain ⟨N₀, hN₀o, hN₀⟩ := GlobalTheory.T.exists_open_galoisSubgroup_trace_ne_zero Ω E l n hn r hr.1
  obtain ⟨M₀, _, _, _, _, _, _, _, hsd₀, hfix₀, hfixR₀⟩ := GlobalTheory.T.exists_solvable_cm_extension_split_place Ω E A w h N₀ hN₀o
  obtain ⟨π₀, χ₀, hπ₀, hl₀⟩ := GlobalTheory.T.exists_cuspidal_charLift_of_solvable_cmExtension hI Ω E M₀ l ι n hn π χ hπ r hr N₀ hN₀ hsd₀
  obtain ⟨v₀, h₀, -⟩ := GlobalTheory.T.exists_isPlaceOver_finiteExtension_of_isPlaceOver E M₀ Ω A w h
  haveI : v₀.asIdeal.LiesOver w.asIdeal := lies h h₀
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.localArtinExists_holds M₀ Ω A v₀ h₀
  have hgfix : ∀ z : M₀, (g : G E Ω) (algebraMap M₀ Ω z) = algebraMap M₀ Ω z := hfix₀ g (Weil_le_Dec h g.2)
  have hg₀ : (AlgEquiv.ofRingEquiv (f := (g : G E Ω).toRingEquiv) hgfix : G M₀ Ω) ∈ Weil h₀ :=
    GlobalTheory.T.mem_weilGroupAtPlace_of_fixes_extension E M₀ Ω A w v₀ h h₀ g _ (fun z => rfl)
  let g₀ : Weil h₀ := ⟨_, hg₀⟩
  have hdeg₀ : deg g₀ ≠ 0 := by
    obtain ⟨t, ht, hd⟩ := GlobalTheory.T.exists_weilGroup_restrict_extension E M₀ Ω A w v₀ h h₀ g₀
    have : t = g := Subtype.ext (AlgEquiv.ext fun z => ht z)
    subst this
    exact fun h0 => hg (hd.2 h0)
  obtain ⟨V, hVo, hVc, hgV, hVine⟩ := GlobalTheory.T.exists_open_subgroup_weilElement_characterKernel Ω M₀ v₀ A h₀ n (fun j => (ξ j).comp (GlobalTheory.BCChar.normU w v₀))
    (fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU w v₀ (hξ j)) a₀ ha₀ g₀ hdeg₀
  have hr₀ : Weak π₀ ι (r.comp (UpperTheory.V.Af.Bc.res E Ω M₀)) := GlobalTheory.T.weaklyAttachedGaloisRepresentation_baseChange_restrict E M₀ Ω l ι n π π₀ hl₀.1 r hr
  obtain ⟨N₁, hN₁o, hN₁⟩ := GlobalTheory.T.exists_open_galoisSubgroup_trace_ne_zero Ω M₀ l n hn _ hr₀.1
  obtain ⟨M₁, _, _, _, _, _, _, _, hsd₁, hV₁⟩ := GlobalTheory.T.exists_solvable_cm_extension_abelianCompletion Ω M₀ A v₀ h₀ hfixR₀ V hVo hVc N₁ hN₁o
  obtain ⟨P, χ₁, hP, hl₁⟩ := GlobalTheory.T.exists_cuspidal_charLift_of_solvable_cmExtension hI Ω M₀ M₁ l ι n hn π₀ χ₀ hπ₀ _ hr₀ N₁ hN₁ hsd₁
  letI : Algebra E M₁ := ((algebraMap M₀ M₁).comp (algebraMap E M₀)).toAlgebra
  haveI : IsScalarTower E M₀ M₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower E M₁ Ω := IsScalarTower.of_algebraMap_eq fun z => by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply M₀ M₁ Ω,
      ← IsScalarTower.algebraMap_apply E M₀ Ω]
  have hl : CharLift π P := GlobalTheory.T.cuspRep_characterSupportLift_trans_tower E M₀ M₁ n π π₀ P hl₀ hl₁
  have hg₁fix : ∀ z : M₁, (g : G E Ω) (algebraMap M₁ Ω z) = algebraMap M₁ Ω z :=
    (hV₁ ⟨(g₀ : G M₀ Ω), Weil_le_Dec h₀ g₀.2⟩).2 hgV
  refine ⟨M₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    P, χ₁, hP, hl, hg₁fix, ?_⟩
  intro t ht0 htfix j
  have htfix₀ : ∀ z : M₀, (t : G E Ω) (algebraMap M₀ Ω z) = algebraMap M₀ Ω z := fun z => by
    rw [IsScalarTower.algebraMap_apply M₀ M₁ Ω]
    exact htfix _
  have ht₀ : (AlgEquiv.ofRingEquiv (f := (t : G E Ω).toRingEquiv) htfix₀ : G M₀ Ω) ∈ Weil h₀ :=
    GlobalTheory.T.mem_weilGroupAtPlace_of_fixes_extension E M₀ Ω A w v₀ h h₀ t _ (fun z => rfl)
  let t₀ : Weil h₀ := ⟨_, ht₀⟩
  have hdt₀ : deg t₀ = 0 := by
    obtain ⟨s, hs, hd⟩ := GlobalTheory.T.exists_weilGroup_restrict_extension E M₀ Ω A w v₀ h h₀ t₀
    have : s = t := Subtype.ext (AlgEquiv.ext fun z => hs z)
    subst this
    exact hd.1 ht0
  have ht₀i : (t₀ : G M₀ Ω) ∈ Ine (F := M₀) A := deg_eq_zero_iff.1 hdt₀
  have hinV : (⟨(t₀ : G M₀ Ω), Weil_le_Dec h₀ t₀.2⟩ : Dec (F := M₀) A) ∈ V :=
    (hV₁ _).1 fun z => htfix z
  have h1 := hVine ⟨_, ht₀i⟩ _ hinV rfl j
  have h2 : ineIncl h₀ ⟨_, ht₀i⟩ = t₀ := Subtype.ext rfl
  rw [h2] at h1
  have h3 := GlobalTheory.T.localArtin_comp_norm_compat E M₀ Ω A w v₀ h h₀ a a₀ ha ha₀ t t₀ (fun z => rfl)
  rw [h3]
  simpa using h1

end GlobalTheory.RoadU.TorLiftC

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.T.weaklyAttached_toral_of_cm_lift : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r → ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)), (∀ j, IsSmoothChar (ξ j)) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, deg g ≠ 0 → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω) (P : CuspSub M n) (χ' : HChar (maximalRealSubfield M)), InScope .all l P χ' ∧ CharLift π P ∧ (∀ x : M, (g : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) ∧ ∀ t : Weil h, deg t = 0 → (∀ x : M, (t : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) → ∀ j, ξ j (a t) = 1 := by
  first | (exact @GlobalTheory.RoadU.TorLiftC.exists_cm_lift_fix_charKer) | (exact GlobalTheory.RoadU.TorLiftC.exists_cm_lift_fix_charKer) | (intros; apply GlobalTheory.RoadU.TorLiftC.exists_cm_lift_fix_charKer  <;> assumption)

end
