import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeIntStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharExistsOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOfMatRel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelOpenAbelianEighthPowerWithBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBaseChangeCompletedLocalAbelianLocStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupEqEighthPowerLatticeOverTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Periods

theorem one_lattice {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ} {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] (D : DegData R (maximalIdeal R)) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W)
    (m : Fin 8 → Fin 8 → (D.toPre.X →+ D.toPre.X)) (P : ∀ T : Trait F, (R →+* T.V) → Prop)
    (h : ∀ T ψ, P T ψ → ∃ ρT : D.toPre.X ≃+ (Fin 8 → T.D.toPre.X),
      (∀ y r, PsiCoord D.toPre y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (ψ r) (T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧
      ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y))) :
    ∃ (Λ : Type) (_ : AddCommGroup Λ) (p : Λ → R) (c : ℕ), 1 ≤ c ∧ ∀ T ψ, P T ψ →
      ∃ e : Λ ≃+ T.D.toPre.X, ∀ y, ∃ k : ℕ, (k : ℤ) = c * T.β (e y) (e y) ∧ Associated (ψ (p y)) (T.ϖ ^ k) := by
  have hc : 0 < W 0 0 := by
    have := hW.1.diag_pos (i := 0)
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply] at this
    have h2 : (0 : ℤ) < W 0 0 + W 0 0 := by exact_mod_cast this
    omega
  by_cases hex : ∃ T ψ, P T ψ
  swap
  · push_neg at hex
    exact ⟨PUnit, inferInstance, fun _ => 0, 1, le_rfl, fun T ψ hP => absurd hP (hex T ψ)⟩
  obtain ⟨T₀, ψ₀, hP₀⟩ := hex
  obtain ⟨e₀, -, he₀⟩ := h T₀ ψ₀ hP₀
  have hcoord : ∀ z, ∃ r, PsiCoord D.toPre (e₀.symm (Pi.single 0 z)) r := fun z =>
    (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff D.toPre _).2 (GlobalTheory.PeriodFormCompare.psiIn_top D _)
  choose p hp using hcoord
  refine ⟨T₀.D.toPre.X, inferInstance, p, (W 0 0).toNat, by omega, fun T ψ hP => ?_⟩
  obtain ⟨ρT, hρ, hm⟩ := h T ψ hP
  obtain ⟨π, hπs, hπ⟩ := exists_diag_of_matRel W hW D.toPre.X T₀.D.toPre.X T.D.toPre.X m e₀ ρT.toAddMonoidHom
    ρT.surjective he₀ hm
  have hsingle : ∀ z, ρT (e₀.symm (Pi.single 0 z)) = Pi.single 0 (π z) := by
    intro z
    funext u
    have := hπ (e₀.symm (Pi.single 0 z)) u
    simp only [AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply] at this
    rw [this]
    by_cases hu : u = 0
    · subst hu; simp
    · simp [Pi.single_apply, hu]
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have h1 : ρT (e₀.symm (Pi.single 0 z)) = 0 := by rw [hsingle, hz, Pi.single_zero]
    have h2 : e₀.symm (Pi.single 0 z) = 0 := by simpa using h1
    have h3 : (Pi.single 0 z : Fin 8 → T₀.D.toPre.X) = 0 := by simpa using h2
    simpa using congrFun h3 0
  refine ⟨AddEquiv.ofBijective π ⟨hinj, hπs⟩, fun z => ?_⟩
  obtain ⟨h0, ha⟩ := hρ _ _ (hp z)
  rw [hsingle] at h0 ha
  have hq : qW W T.β (Pi.single 0 (π z)) = W 0 0 * T.β (π z) (π z) := by
    unfold qW
    rw [Finset.sum_eq_single 0 (fun u _ hu => by simp [Pi.single_eq_of_ne hu]) (by simp)]
    rw [Finset.sum_eq_single 0 (fun v _ hv => by simp [Pi.single_eq_of_ne hv]) (by simp)]
    simp
  refine ⟨(qW W T.β (Pi.single 0 (π z))).toNat, ?_, ha⟩
  rw [Int.toNat_of_nonneg h0, hq, Int.toNat_of_nonneg hc.le]
  rfl

end GlobalTheory.Poinc.Periods

theorem GlobalTheory.Poinc.Periods.trait_iso : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (f : Fin 8 → Fin 8 → (FinalForm.G ⟶ FinalForm.G)), (∀ a b, MatOn FinalForm pr a b (f a b)) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (ξ : Sp R ⟶ M.Z) [IsCommMonObj ((Over.pullback ξ).obj FinalForm.G)] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A ((Over.pullback ξ).obj FinalForm.G)), LBIso U.LG.L (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom ξ)) → (∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus FinalForm.G)) → ∀ (m : Fin 8 → Fin 8 → (D.toPre.X →+ D.toPre.X)), (∀ a b, EndChar U ((Over.pullback ξ).map (f a b)) (m a b)) → ∀ (T : Trait F) (ψ : R →+* T.V), IsLocalHom ψ → ThroughU M V v (𝟙 F.X) T (spMap ψ ≫ ξ) → ∃ ρT : D.toPre.X ≃+ (Fin 8 → T.D.toPre.X), (∀ y r, PsiCoord D.toPre y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (ψ r) (T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧ ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y)) := by
  intro g n o _ ζ F W hW o' Ω _ _ _ hA S ρ u c pr hs M U₀ EE FinalForm hO V v hv f hf R _ _ _ hB ξ _ D A U hL hP m hm T ψ hl ht
  have hVab := (GlobalTheory.T.thetaModel_open_abelian_eighthPower_with_bundle g n o ζ F W o' Ω S ρ u c pr hs M U₀ EE FinalForm hO V v hv).1
  have hBV : GlobalTheory.Mum.Base T.V := ⟨⟨inferInstance, inferInstance, inferInstance, T.complete⟩, inferInstance⟩
  have hgen : ∀ w, (jK T.V ≫ spMap ψ ≫ ξ) w ∈ abLocus FinalForm.G := by
    obtain ⟨ξ₀, hξ₀, -⟩ := ht
    intro w
    rw [← hξ₀]
    exact hVab (ξ₀ w).2
  obtain ⟨G', _, _, D', A', U', gm, ι, hG', hgm, hLB, hC, hE⟩ :=
    GlobalTheory.T.uniformisation_baseChange_completedLocal_abelianLocus M.Z FinalForm.G FinalForm.semi FinalForm.L.L R hB ξ D A U hL hP T.V hBV ψ hl hgen
  refine GlobalTheory.T.characterGroup_eq_eighthPower_lattice_over_trait g n o ζ F W hW o' Ω S ρ u c pr hs M U₀ EE FinalForm hO V v hv f hf R ξ D.toPre m
    T ψ ht G' D' A' U' gm ι hG' hgm hLB hC fun a b => ?_
  obtain ⟨f', hf'm, hf'c, hf'e⟩ := hE (f a b) (hf a b).1
  exact ⟨f', hf'm, hf'c, fun m' hm' => hf'e _ m' (hm a b) hm'⟩

theorem GlobalTheory.Poinc.Periods.main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SharpOver F W ρ.P u → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ x : M.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : M.Z.presheaf.stalk x →+* R) (Λ : Type) (_ : AddCommGroup Λ) (p : Λ → R) (c : ℕ), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ 1 ≤ c ∧ ∀ (T : Trait F) (ψ : R →+* T.V), IsLocalHom ψ → ThroughU M V v (𝟙 F.X) T (spMap (ψ.comp j) ≫ M.Z.fromSpecStalk x) → ∃ e : Λ ≃+ T.D.toPre.X, ∀ y, ∃ k : ℕ, (k : ℤ) = c * T.β (e y) (e y) ∧ Associated (ψ (p y)) (T.ϖ ^ k) := by
  intro g n o _ ζ F W hW o' Ω _ _ _ hA S ρ u hu M U₀ EE FinalForm hO V v hv x
  obtain ⟨c, pr, hs⟩ := (sharpOver_iff F W ρ.P u).1 hu
  have hinjΩ := M.stalkHom_injective x
  haveI : IsDomain (M.Z.presheaf.stalk x) := hinjΩ.isDomain
  haveI : CharZero Ω := hA.char
  haveI : CharZero (M.Z.presheaf.stalk x) := (RingHom.charZero_iff hinjΩ).2 inferInstance
  haveI : IsIntegrallyClosed (M.Z.presheaf.stalk x) := (hO.normal x).2
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  have fg : (maximalIdeal (M.Z.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    AdicCompletion.isLocalRing_of_fg fg
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (M.Z.presheaf.stalk x)
  haveI hRn : IsNoetherianRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  set R := AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x) with hR
  set φ := algebraMap (M.Z.presheaf.stalk x) R with hφ
  have hcpl : IsAdicComplete (maximalIdeal R) R := by
    rw [hm]
    exact AdicCompletion.isAdicComplete_self _ fg
  have hinj : Function.Injective φ := AdicCompletion.of_injective _ _
  haveI : CharZero R := (RingHom.charZero_iff hinj).1 inferInstance
  set ξ : Sp R ⟶ M.Z := spMap φ ≫ M.Z.fromSpecStalk x with hξ
  have hne : (ξ ⁻¹' abLocus FinalForm.G).Nonempty := by
    let w : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
    let p : Sp (M.Z.presheaf.stalk x) := spMap φ w
    have hp : p.asIdeal = ⊥ := by
      show Ideal.comap φ ⊥ = ⊥
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot φ).1 hinj
    have hgen : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact genericPoint_specializes x
    obtain ⟨q, hq⟩ := hgen
    have hpq : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (by
      show p.asIdeal ≤ q.asIdeal
      rw [hp]
      exact bot_le)
    have hsp : ξ w ⤳ genericPoint M.Z := by
      have := hpq.map (M.Z.fromSpecStalk x).continuous
      rw [hq] at this
      exact this
    refine ⟨w, ?_⟩
    show ξ w ∈ abLocus FinalForm.G
    rw [FinalForm.ab]
    exact le_bot_iff.1 ((S.TT_anti M hsp).trans (ThetaSys.TT_genericPoint S M).le)
  haveI : IsCommMonObj ((Over.pullback ξ).obj FinalForm.G) := Functor.isCommMonObj_obj
  obtain ⟨D, A, U, hL, hP⟩ := FinalForm.unif R hRn hRi hcpl ξ hne
  have hB : GlobalTheory.Mum.Base R := ⟨⟨hRn, hRd, hRi, hcpl⟩, inferInstance⟩
  have hGs : IsSemiAbelian ((Over.pullback ξ).obj FinalForm.G) := IsSemiAbelian.pullback _ FinalForm.G FinalForm.semi
  obtain ⟨hsb, hpr, huniq, hlb⟩ := hs
  choose f hf using matOn_exists o' Ω S ρ M U₀ EE FinalForm hO.ne c.A pr hpr huniq
  have hfm : ∀ a b, IsMonHom ((Over.pullback ξ).map (f a b)) := fun a b => by
    have := (hf a b).1
    infer_instance
  choose m hmc using fun a b => endChar_exists_of_isMonHom R hB _ hGs D A U _ (hfm a b)
  obtain ⟨Λ, _, p, c', hc', hall⟩ := GlobalTheory.Poinc.Periods.one_lattice D W hW m
    (fun T ψ => IsLocalHom ψ ∧ ThroughU M V v (𝟙 F.X) T (spMap (ψ.comp φ) ≫ M.Z.fromSpecStalk x))
    (fun T ψ hT => by
      obtain ⟨hl, ht⟩ := hT
      have e : spMap (ψ.comp φ) ≫ M.Z.fromSpecStalk x = spMap ψ ≫ ξ := by
        rw [hξ, ← Category.assoc]
        congr 1
        exact Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)
      rw [e] at ht
      exact GlobalTheory.Poinc.Periods.trait_iso g n o ζ F W hW o' Ω S ρ u c pr ⟨hsb, hpr, huniq, hlb⟩ M U₀ EE FinalForm hO V v hv f hf R hB ξ
        D A U hL hP m hmc T ψ hl ht)
  exact ⟨R, inferInstance, hRd, hloc, φ, Λ, inferInstance, p, c', hB, isCpl_self _, hc', fun T ψ hl ht => hall T ψ ⟨hl, ht⟩⟩
