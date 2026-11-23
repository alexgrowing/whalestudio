import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEndOfEighthPowerOfPolAVPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisOfPolAVPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationModelFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithBaseFiniteContainingRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationPullbackStable
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFractionRingOfForallDiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLevelStructureOfGenericOfFibrewiseIndep
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfDense
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.SympLevelExt

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) :
    LBIso (L.pull (b ≫ a)) ((L.pull a).pull b) :=
  LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b)
      (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL _)))

theorem map_linComb {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {T : Over S}
    {T' : Over S'} (ρ : (T ⟶ A) →* (T' ⟶ A')) {n : ℕ} (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) :
    ρ (linComb y a) = linComb (fun i => ρ (y i)) a := by
  unfold linComb
  rw [map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  exact map_pow ρ (y i) (a i)

theorem dense_of_bot_mem {R : Type} [CommRing R] [IsDomain R] (D : Set (Sp R))
    (hD : (⊥ : PrimeSpectrum R) ∈ D) : Dense D := by
  intro p
  have hs : (⊥ : PrimeSpectrum R) ⤳ p := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  exact closure_mono (Set.singleton_subset_iff.2 hD) (specializes_iff_mem_closure.1 hs)

theorem extend_torsion {R F : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field F] [Algebra R F] [IsFractionRing R F] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    [IsProper G.hom] (n : ℕ) (hn : IsUnit (n : R))
    (x : Over.mk ((baseOver (Sp F)).hom ≫ spMap (algebraMap R F)) ⟶ G) (hx : x ^ n = 1) :
    ∃ σ : baseOver (Sp R) ⟶ G, σ ^ n = 1 ∧ spMap (algebraMap R F) ≫ σ.left = x.left := by
  have hn' : IsUnit (n : Γ(Sp R, ⊤)) := by
    have := hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  have hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := fun p => by
    refine ⟨inferInstance, ?_⟩
    have : (PrimeSpectrum.asIdeal p).IsPrime := PrimeSpectrum.isPrime p
    have h := StructureSheaf.IsLocalization.to_stalk R p
    exact @isIntegrallyClosed_of_isLocalization R ((Spec.structureSheaf R).presheaf.stalk p) _ _ (_) _ _
      (PrimeSpectrum.asIdeal p).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _) h
  have j₁ : IsPreimmersion (spMap (algebraMap R F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have j₂ : Flat (spMap (algebraMap R F)) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat F (nonZeroDivisors R)))
  have j₃ : IsDominant (spMap (algebraMap R F)) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    intro a ha
    have : a = 0 := IsFractionRing.injective R F (ha.trans (map_zero _).symm)
    rw [this]; exact Ideal.zero_mem _)⟩
  obtain ⟨σ, hσ₁, hσ₂⟩ := exists_section_of_pow_eq_one hT (spMap (algebraMap R F)) G n hn' _ x hx (𝟙 _)
    (by simp)
  let σ' : baseOver (Sp R) ⟶ G := Over.homMk σ (by simpa using hσ₁)
  have hσ : spMap (algebraMap R F) ≫ σ'.left = x.left := by
    show spMap (algebraMap R F) ≫ σ = x.left
    simpa using hσ₂
  refine ⟨σ', ?_, hσ⟩
  let U : Over.mk ((baseOver (Sp F)).hom ≫ spMap (algebraMap R F)) ⟶ baseOver (Sp R) :=
    Over.homMk (spMap (algebraMap R F)) (by simp)
  have hU : U ≫ σ' = x := Over.OverMorphism.ext hσ
  have e : U ≫ σ' ^ n = U ≫ 1 := by rw [MonObj.comp_pow, MonObj.comp_one, hU, hx]
  exact over_points_ext_of_injective _ G R F (algebraMap R F) (IsFractionRing.injective R F) _ _ _
    (congrArg (fun q => q.left) e)

end GlobalTheory.SympLevelExt

namespace GlobalTheory.SympLevelExt

theorem generic_basis {R F : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    {Q : PolAV (Sp F)} (G : Over (Sp R)) [GrpObj G] (φ : Q.A.left ⟶ G.left)
    (hp : IsGrpPullback Q.A G (spMap (algebraMap R F)) φ) (k : ℕ) [NeZero k] (ze₀ : Γ(Sp F, ⊤)ˣ)
    (lev₀ : Out.Level Q k ze₀) (y : Fin (2 * Q.g) → (baseOver (Sp R) ⟶ G))
    (hy : ∀ i, (lev₀.pt i).left ≫ φ = spMap (algebraMap R F) ≫ (y i).left)
    (z : Over.mk (spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap R F)) ⟶ G) (hz : z ^ k = 1) :
    ∃! c : Fin (2 * Q.g) → ZMod k,
      linComb (fun i => (Over.homMk (spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap R F))
        (by simp) : Over.mk (spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap R F)) ⟶
          baseOver (Sp R)) ≫ y i) (fun i => (c i).val) = z := by
  let s : Sp (AlgebraicClosure F) ⟶ Sp F := spMap (algebraMap F (AlgebraicClosure F))
  let T : Over (Sp F) := Over.mk s
  let ρ := pushHom hp T
  have hinj : Function.Injective ρ := fun a b hab => by
    apply Over.OverMorphism.ext
    apply hp.1.hom_ext
    · exact congrArg (fun q => q.left) hab
    · rw [Over.w a, Over.w b]
  have hsurj : ∀ w : Over.mk (T.hom ≫ spMap (algebraMap R F)) ⟶ G, ∃ a, ρ a = w := fun w =>
    ⟨Over.homMk (hp.1.lift w.left T.hom (Over.w w)) (hp.1.lift_snd _ _ _),
      Over.OverMorphism.ext (hp.1.lift_fst _ _ _)⟩
  have hcomp : ∀ i, ρ ((Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp F)) ≫ lev₀.pt i) =
      (Over.homMk (s ≫ spMap (algebraMap R F)) (by simp) :
        Over.mk (s ≫ spMap (algebraMap R F)) ⟶ baseOver (Sp R)) ≫ y i := fun i => by
    apply Over.OverMorphism.ext
    show (s ≫ (lev₀.pt i).left) ≫ φ = (s ≫ spMap (algebraMap R F)) ≫ (y i).left
    rw [Category.assoc, hy, Category.assoc]
  have hlin : ∀ d : Fin (2 * Q.g) → ℕ,
      ρ (linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp F)) ≫ lev₀.pt i) d) =
      linComb (fun i => (Over.homMk (s ≫ spMap (algebraMap R F)) (by simp) :
        Over.mk (s ≫ spMap (algebraMap R F)) ⟶ baseOver (Sp R)) ≫ y i) d := fun d => by
    rw [map_linComb]
    simp only [hcomp]
  obtain ⟨a, rfl⟩ := hsurj z
  have ha : a ^ k = 1 := hinj (by rw [map_pow, hz, map_one])
  obtain ⟨c, hc⟩ := lev₀.span (AlgebraicClosure F) s a ha
  refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_, ?_⟩
  · show linComb _ (fun i => (((c i : ℕ) : ZMod k)).val) = ρ a
    simp only [ZMod.val_natCast_of_lt (Fin.is_lt _)]
    rw [← hlin, hc]
  · intro c' hc'
    have e : ρ (linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp F)) ≫ lev₀.pt i)
        (fun i => ((⟨(c' i).val, ZMod.val_lt (c' i)⟩ : Fin k) : ℕ))) = ρ a := by
      rw [hlin]; exact hc'
    have e' := lev₀.indep (AlgebraicClosure F) s _ c ((hinj e).trans hc.symm)
    funext i
    have := congrArg (fun f => ((f i : ℕ) : ZMod k)) e'
    simpa using this

end GlobalTheory.SympLevelExt

namespace GlobalTheory.SympLevelExt

theorem level_extends : ∀ {R₁ : Type} [CommRing R₁] (P₁ : PolAV (Sp R₁)) (R F : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field F] [Algebra R F] [IsFractionRing R F] (h : R₁ →+* R) (Q : PolAV (Sp F)) (φ : Q.A.left ⟶ P₁.A.left) (K : ℕ) (ze : Rˣ), 0 < K → IsUnit (K : R) → Q.g = P₁.g → IsGrpPullback Q.A P₁.A (spMap ((algebraMap R F).comp h)) φ → LBIso Q.L (P₁.L.pull φ) → Nonempty (Out.Level Q K (unitOn (Units.map (algebraMap R F).toMonoidHom ze))) → ∃ (P : PolAV (Sp R)) (ψ : P.A.left ⟶ P₁.A.left), P.g = P₁.g ∧ IsGrpPullback P.A P₁.A (spMap h) ψ ∧ LBIso P.L (P₁.L.pull ψ) ∧ Nonempty (Out.Level P K (unitOn ze)) := by
  intro R₁ _ P₁ R F _ _ _ _ _ _ _ h Q φ K ze hK hKu hg hpb hQL hlev
  obtain ⟨lev₀⟩ := hlev
  cases Q with
  | mk QA QisAb Qg Qsm QL QisLB Qrig Qsym Qamp Qkt =>
  dsimp only at hg
  subst hg
  have hL := abelianSchemeLaws_all.1
  haveI : NeZero K := ⟨hK.ne'⟩
  let j := spMap (algebraMap R F)
  let P : PolAV (Sp R) := StrictPull.polPull P₁ (spMap h)
  let ψ : P.A.left ⟶ P₁.A.left := pullback.fst P₁.A.hom (spMap h)
  have hψ : IsGrpPullback P.A P₁.A (spMap h) ψ := isGrpPullback_pullback P₁.A (spMap h)
  have hc : spMap ((algebraMap R F).comp h) = j ≫ spMap h := by
    simp only [spMap, j, CommRingCat.ofHom_comp, Spec.map_comp]
  have hw : φ ≫ P₁.A.hom = (QA.hom ≫ j) ≫ spMap h := by rw [hpb.1.w, hc, Category.assoc]
  let φ' : QA.left ⟶ P.A.left := hψ.1.lift φ (QA.hom ≫ j) hw
  have e₁ : φ' ≫ ψ = φ := hψ.1.lift_fst _ _ _
  have e₂ : φ' ≫ P.A.hom = QA.hom ≫ j := hψ.1.lift_snd _ _ _
  have hpb' : IsGrpPullback QA P.A j φ' := hψ.cancel (by rw [e₁, ← hc]; exact hpb) e₂
  have hQL' : LBIso QL (P.L.pull φ') := by
    refine LBIso.trans QisLB (pull_isLB P₁.isLB _) (pull_isLB P.isLB _) hQL ?_
    have := lbIso_pull_comp P₁.isLB ψ φ'
    rw [e₁] at this
    exact this
  have hP : IsProper P.A.hom := P.isAb.proper
  have := P.isAb.comm
  choose y hy₁ hy₂ using fun i : Fin (2 * P₁.g) =>
    extend_torsion (R := R) (F := F) P.A K hKu (pushHom hpb' (baseOver (Sp F)) (lev₀.pt i))
      (by rw [← map_pow, lev₀.torsion, map_one])
  have hy : ∀ i, (lev₀.pt i).left ≫ φ' = j ≫ (y i).left := fun i => (hy₂ i).symm
  have hKu' : IsUnit (K : Γ(Sp R, ⊤)) := by
    have := hKu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  let x : Sp (AlgebraicClosure F) ⟶ Sp R := spMap (algebraMap F (AlgebraicClosure F)) ≫ j
  have hx : (⊥ : PrimeSpectrum R) ∈ Set.range x := by
    obtain ⟨w⟩ : Nonempty (Sp (AlgebraicClosure F)) := inferInstance
    refine ⟨w, ?_⟩
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap R F) (Ideal.comap (algebraMap F (AlgebraicClosure F)) (PrimeSpectrum.asIdeal w)) = ⊥
    rw [@Ideal.eq_bot_of_prime _ _ (PrimeSpectrum.asIdeal w) (PrimeSpectrum.isPrime w),
      Ideal.comap_bot_of_injective _ (algebraMap F (AlgebraicClosure F)).injective,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective R F)]
  have hbasis := torsion_basis_of_dense (Sp R) P.A K (2 * P₁.g) y (Set.range x) P.isAb hK hKu' hy₁
    (dense_of_bot_mem _ hx) (fun p hp => ⟨AlgebraicClosure F, inferInstance, inferInstance, x, hp,
      fun z hz => generic_basis (Q := ⟨QA, QisAb, P₁.g, Qsm, QL, QisLB, Qrig, Qsym, Qamp, Qkt⟩) P.A φ' hpb' K _ lev₀ y hy z hz⟩)
  have hind : ∀ (F' : Type) [Field F'] [IsAlgClosed F'] (s : Spec (CommRingCat.of F') ⟶ Sp R)
      (c c' : Fin (2 * P.g) → Fin K),
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)) =
        linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c' i : ℕ)) →
      c = c' := by
    intro F' _ _ s c c' hcc
    obtain ⟨d, -, hd⟩ := hbasis F' s
      (linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)))
      (DenseBasis.linComb_pow_eq_one _ (fun i => by rw [← MonObj.comp_pow, hy₁, MonObj.comp_one]) _)
    have h₁ := hd (fun i => ((c i : ℕ) : ZMod K)) (by simp only [ZMod.val_natCast_of_lt (Fin.is_lt _)])
    have h₂ := hd (fun i => ((c' i : ℕ) : ZMod K)) (by simp only [ZMod.val_natCast_of_lt (Fin.is_lt _)]; exact hcc.symm)
    funext i
    apply Fin.ext
    have := congrArg (fun f => (f i).val) (h₁.trans h₂.symm)
    simpa only [ZMod.val_natCast_of_lt (Fin.is_lt _)] using this
  obtain ⟨lev, -⟩ := level_of_generic_of_indep hL R F P ⟨QA, QisAb, P₁.g, Qsm, QL, QisLB, Qrig, Qsym, Qamp, Qkt⟩ φ'
    hpb' hQL' rfl K ze _ hKu rfl lev₀ y (fun i₀ i hi => by
      obtain rfl : i₀ = i := Fin.ext hi
      exact hy i₀) hind
  exact ⟨P, ψ, rfl, hψ, GlobalTheory.PolBaseChange.lbIso_refl P.isLB, ⟨lev⟩⟩

end GlobalTheory.SympLevelExt
