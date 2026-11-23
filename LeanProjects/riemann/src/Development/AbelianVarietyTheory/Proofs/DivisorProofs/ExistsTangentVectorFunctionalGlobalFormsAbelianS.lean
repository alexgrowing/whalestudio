import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamComparisonBijectiveCupSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePairRestrictionInjectiveFirstCohomologyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormValueOnTangentVectorEqZeroOfGlobalFormZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpFormEqZeroOfTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveOfLocalBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTangentIffTanS
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieDual

theorem eq_top_of_residue {R G : Type} [CommRing R] [AddCommGroup G] [Module R G]
    [Module.Finite R G] [Module.Projective R G] (N : Submodule R (Module.Dual R G))
    (h : ∀ m : Ideal R, m.IsMaximal → ∀ ψ : Module.Dual R G, ∃ χ ∈ N, ∀ x, ψ x - χ x ∈ m) :
    N = ⊤ := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R G
  have hm : ∀ (m : Ideal R) (χ : Module.Dual R G), (∀ x, χ x ∈ m) →
      χ ∈ m • (⊤ : Submodule R (Module.Dual R G)) := fun m χ hχ ↦ by
    have e : χ = ∑ i, χ (f (Pi.single i 1)) • (LinearMap.proj i ∘ₗ g) := by
      ext x
      have e1 : x = f (g x) := (LinearMap.congr_fun hfg x).symm
      conv_lhs => rw [e1, pi_eq_sum_univ' (g x)]
      simp [mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hχ _) Submodule.mem_top
  rw [eq_top_iff]
  intro ψ _
  by_contra hψ
  have hI : N.comap (LinearMap.toSpanSingleton R _ ψ) ≠ ⊤ := fun e ↦ hψ (by
    have : (1 : R) ∈ N.comap (LinearMap.toSpanSingleton R _ ψ) := e ▸ Submodule.mem_top
    simpa using this)
  obtain ⟨m, hmax, hle⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m
    (⊤ : Submodule R (Module.Dual R G ⧸ N)) Module.Finite.fg_top (by
      intro q _
      obtain ⟨φ, rfl⟩ := N.mkQ_surjective q
      obtain ⟨χ, hχ, hx⟩ := h m hmax φ
      have e : N.mkQ φ = N.mkQ (φ - χ) := by
        rw [map_sub, show N.mkQ χ = 0 from (Submodule.Quotient.mk_eq_zero N).2 hχ, sub_zero]
      rw [e, ← Submodule.range_mkQ N, ← Submodule.map_top, ← Submodule.map_smul'']
      exact Submodule.mem_map_of_mem (hm m _ hx))
  have h1 : r ∈ m := hle (by
    have := hr0 (N.mkQ ψ) Submodule.mem_top
    rw [← map_smul] at this
    simpa using (Submodule.Quotient.mk_eq_zero N).1 this)
  exact hmax.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using m.sub_mem h1 hr))

variable {R R' : Type} [CommRing R] [CommRing R']

theorem tanVal_pullForm {σ : R →+* R'} {A : Over (Sp R)} {B : Over (Sp R')} {φ : B.left ⟶ A.left}
    (m : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R') (B.hom ≫ 𝟙 _) σ φ) {v : epsR R ⟶ A} {v' : epsR R' ⟶ B}
    (e : v'.left ≫ φ = spMap (Chart.dualMapR σ) ≫ v.left) (f : Form (A.hom ≫ 𝟙 _)) :
    tanVal v' (m.pullForm f) = σ (tanVal v f) := by
  let E := SqExt.dual R
  let E' := SqExt.dual R'
  have hy := pt_w v
  have hy' := pt_w v'
  have hc : ∀ r : R, Chart.dualMapR σ (algebraMap R (DualNumber R) r) =
      algebraMap R' (DualNumber R') (σ r) := fun r => by
    ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have e₀ : spMap σ ≫ spMap (E.π : E.C →+* E.B) ≫ v.left =
      (spMap (E'.π : E'.C →+* E'.B) ≫ v'.left) ≫ φ := by
    rw [Category.assoc, e, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 2
    ext a <;> simp [Chart.dualMapR, E, E', TrivSqZeroExt.algebraMap_eq_inl]
  let Φ : E.thick _ (E.red_w hy) ⟶ m.obj (E'.thick _ (E'.red_w hy')) :=
    { φ := { Chart.dualMapR σ with commutes' := hc }
      φ₀ := σ
      comm := fun b => by
        change σ b.fst = (Chart.dualMapR σ b).fst
        simp [Chart.dualMapR]
      dp := isDPMorphism_sqDP E.sq E'.sq _ fun a ha => by
        have ha' : a.fst = 0 := ha
        change (Chart.dualMapR σ a).fst = 0
        simp [Chart.dualMapR, ha']
      pt := e₀ }
  let a : Thick.triv E.C _ hy ⟶ m.obj (Thick.triv E'.C _ hy') :=
    Thick.trivHom { Chart.dualMapR σ with commutes' := hc } e.symm
  let b : Thick.triv E.B _ (E.red_w hy) ⟶ m.obj (Thick.triv E'.B _ (E'.red_w hy')) :=
    Thick.trivHom { σ with commutes' := fun _ => rfl } e₀
  have k1 := Form.ev_sq f a (m.functor.map (E'.idHom hy')) (E.idHom hy) Φ rfl rfl fun _ => rfl
  have k2 := Form.ev_sq f b (m.functor.map (E'.secHom (E'.red_w hy') E'.i E'.π_i))
    (E.secHom (E.red_w hy) E.i E.π_i) Φ rfl rfl fun c => (hc c).symm
  have k : E'.val v'.left hy' (m.pullForm f).1 = Chart.dualMapR σ (E.val v.left hy f.1) :=
    (congrArg₂ (fun u v : E'.C => u - v) k2 k1).trans
      ((add_sub_add_right_eq_sub (G := E'.C) _ _ _).trans (map_sub (Chart.dualMapR σ) _ _).symm)
  rw [tanVal_apply, tanVal_apply]
  refine (congrArg (TrivSqZeroExt.snd (R := R')) k).trans ?_
  exact zero_add _

def glob {X : Scheme.{0}} (s : X ⟶ Sp R) : Form s →ₗ[R] GlobForm s :=
  (ClosedForm s).subtype ∘ₗ cmpForm s

theorem isPullForm_glob {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'}
    {φ : X' ⟶ X} (m : IsMor (dp0 R) s (dp0 R') s' σ φ) (f : Form s) :
    IsPullForm m.w (glob s f) (glob s' (m.pullForm f)) := by
  refine isPullForm_iff.2 fun p ↦ ?_
  have k := connForm_pull m (semiHom_secPull m.w p) (affPt_w s p.1.2) (affPt_w s' p.1.1)
    (secPull_affPt s s' p) f.1
  have z : ev f.1 (semiTriv m (semiHom_secPull m.w p) (affPt_w s p.1.2) (affPt_w s' p.1.1)
    (secPull_affPt s s' p)) = 0 := f.2 _ rfl rfl
  rw [z] at k
  exact ((add_zero _).symm.trans (congrArg _ (map_zero _).symm)).trans k.symm

theorem glob_surjective (hC : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hdim : SmoothOfRelativeDimension g A.hom) : Function.Surjective (glob (A.hom ≫ 𝟙 (Sp R))) := by
  have hsm : Smooth (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.smooth; infer_instance
  have hsep : IsSeparated (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.proper; infer_instance
  have hqc : QuasiCompact (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.proper; infer_instance
  have hcmp := (GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth hC R A.left _ hsm hsep hqc).1
  have hcl : Function.Injective (clForm (A.hom ≫ 𝟙 (Sp R))) := (hH R A g hab hdim).2.2.2.2.1.2.1
  have htop : ClosedForm (A.hom ≫ 𝟙 (Sp R)) = ⊤ := (hH R A g hab hdim).2.2.2.2.1.1
  intro ω
  let ωc : ClosedForm (A.hom ≫ 𝟙 (Sp R)) := ⟨ω, htop ▸ Submodule.mem_top⟩
  obtain ⟨c, hc⟩ := hcmp.2 (clForm _ ωc)
  have hF : clForm _ ωc ∈ CechHodgeFiltration (A.hom ≫ 𝟙 (Sp R)) := by rw [cechHodgeFiltration_eq_range]; exact ⟨ωc, rfl⟩
  have h1 : c ∈ F1 (A.hom ≫ 𝟙 (Sp R)) := by
    change toH1O _ c = 0
    apply GlobalTheory.T.structure_sheaf_comparison_injective R A.left _
    rw [← structureSheaf_comparison_comm, map_zero, hc]
    exact hF
  rw [hodgeFiltration_eq_range] at h1
  obtain ⟨f, rfl⟩ := h1
  rw [comparison_formClass] at hc
  exact ⟨f, congrArg Subtype.val (hcl hc)⟩

theorem exists_factor {X : Scheme.{0}} {s : X ⟶ Sp R} (hs : Function.Surjective (glob s))
    (φ : Form s →ₗ[R] R) (hφ : ∀ f, cmpForm s f = 0 → φ f = 0) :
    ∃ ψ : Module.Dual R (GlobForm s), ∀ f, ψ (glob s f) = φ f := by
  have hker : LinearMap.ker (glob s) ≤ LinearMap.ker φ := fun f hf ↦ hφ f (Subtype.ext hf)
  let e := (glob s).quotKerEquivOfSurjective hs
  refine ⟨(LinearMap.ker (glob s)).liftQ φ hker ∘ₗ e.symm.toLinearMap, fun f ↦ ?_⟩
  have : e.symm (glob s f) = Submodule.Quotient.mk f := e.symm_apply_eq.2 rfl
  change (LinearMap.ker (glob s)).liftQ φ hker (e.symm (glob s f)) = _
  rw [this]; rfl

def lieVal (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] :
    Serre.Lie (Serre.intAct A) →ₗ[R] Module.Dual R (Form (A.hom ≫ 𝟙 (Sp R))) where
  toFun v := tanVal v.hom
  map_add' v w := LinearMap.ext fun f ↦ tanVal_mul v.isTangent w.isTangent f
  map_smul' r v := LinearMap.ext fun f ↦ tanVal_epsScale r v.hom f

theorem lieVal_apply (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (v : Serre.Lie (Serre.intAct A)) :
    lieVal A v = tanVal v.hom := rfl

theorem exists_eq_comp {K : Type} [Field K] {L G : Type} {F : Type 1} [AddCommGroup L] [Module K L]
    [AddCommGroup G] [Module K G] [AddCommGroup F] [Module K F] [Module.Finite K L] [Module.Finite K G]
    (hd : Module.finrank K L = Module.finrank K G) (c : F →ₗ[K] G) (hs : Function.Surjective c)
    (l : L →ₗ[K] Module.Dual K F) (hl : Function.Injective l)
    (hf : ∀ v, ∃ ψ : Module.Dual K G, ∀ f, ψ (c f) = l v f) (ψ : Module.Dual K G) :
    ∃ v, ∀ f, l v f = ψ (c f) := by
  choose t ht using hf
  have ext : ∀ {α β : Module.Dual K G}, (∀ f, α (c f) = β (c f)) → α = β :=
    fun h ↦ LinearMap.ext fun x ↦ by
      obtain ⟨f, rfl⟩ := hs x
      exact h f
  let T : L →ₗ[K] Module.Dual K G :=
    { toFun := t
      map_add' := fun v w ↦ ext fun f ↦ by
        rw [LinearMap.add_apply, ht, ht, ht, map_add, LinearMap.add_apply]
      map_smul' := fun r v ↦ ext fun f ↦ by
        rw [LinearMap.smul_apply, ht, ht, map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hinj : Function.Injective T := fun v w h ↦ hl (LinearMap.ext fun f ↦
      (ht v f).symm.trans ((LinearMap.congr_fun h _).trans (ht w f)))
  have hsurj : Function.Surjective T := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    rw [Subspace.dual_finrank_eq, hd])).1 hinj
  obtain ⟨v, rfl⟩ := hsurj ψ
  exact ⟨v, fun f ↦ (ht v f).symm⟩

theorem exists_tangent_field (hC : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    {K : Type} [Field K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (hab : IsAbelianScheme B)
    (hdim : SmoothOfRelativeDimension g B.hom) {y : Fin g → (epsR K ⟶ B)} (hy : IsLieBasis y)
    (ψ : Module.Dual K (GlobForm (B.hom ≫ 𝟙 (Sp K)))) :
    ∃ v : Serre.Lie (Serre.intAct B), ∀ f, tanVal v.hom f = ψ (glob _ f) := by
  have hs := glob_surjective hC hH B g hab hdim
  obtain ⟨hfin, -, hrk⟩ : Module.Finite K (GlobForm (B.hom ≫ 𝟙 (Sp K))) ∧
      Module.Projective K (GlobForm (B.hom ≫ 𝟙 (Sp K))) ∧
      ∀ p : PrimeSpectrum K, Module.rankAtStalk (GlobForm (B.hom ≫ 𝟙 (Sp K))) p = g :=
    (hH K B g hab hdim).2.2.1
  have hG : Module.finrank K (GlobForm (B.hom ≫ 𝟙 (Sp K))) = g := by
    have h := hrk (IsLocalRing.closedPoint K)
    rwa [Module.rankAtStalk_eq_finrank_of_free] at h
  let b := Serre.Lie.basis (Serre.intAct B) hy
  haveI := Module.Finite.of_basis b
  exact exists_eq_comp (by rw [hG, Module.finrank_eq_card_basis b, Fintype.card_fin]) (glob _) hs
    (lieVal B) (fun v w h ↦ Serre.Lie.ext
      (GlobalTheory.LieInjField.eq_of_tanVal_eq hC hH K B g hab hdim _ _ v.isTangent w.isTangent (LinearMap.congr_fun h)))
    (fun v ↦ exists_factor hs (lieVal B v) (GlobalTheory.T.formValueOnTangentVector_eq_zero_of_globalForm_zero K B v.hom)) ψ

theorem dualMapR_comp {R'' : Type} [CommRing R''] (σ : R →+* R') (τ : R' →+* R'') :
    Chart.dualMapR (τ.comp σ) = (Chart.dualMapR τ).comp (Chart.dualMapR σ) := by
  have f : ∀ x, (Chart.dualMapR σ x).fst = σ x.fst := fun _ ↦ add_zero _
  have s : ∀ x, (Chart.dualMapR σ x).snd = σ x.snd := fun _ ↦ zero_add _
  refine RingHom.ext fun x ↦ ?_
  change _ = TrivSqZeroExt.inl (τ (Chart.dualMapR σ x).fst) +
    TrivSqZeroExt.inr (τ (Chart.dualMapR σ x).snd)
  rw [f, s]; rfl

theorem epsScaleR_comp_dualMapR (τ : R →+* R') (c : R) :
    (epsScaleR (τ c)).comp (Chart.dualMapR τ) = (Chart.dualMapR τ).comp (epsScaleR c) := by
  have f : ∀ x, (Chart.dualMapR τ x).fst = τ x.fst := fun _ ↦ add_zero _
  have s : ∀ x, (Chart.dualMapR τ x).snd = τ x.snd := fun _ ↦ zero_add _
  refine RingHom.ext fun x ↦ TrivSqZeroExt.ext ?_ ?_ <;> simp [epsScaleR, f, s]

theorem exists_lieBasis_lift {K : Type} [Field K] (σ : R →+* K) (A : Over (Sp R)) [GrpObj A]
    [IsCommMonObj A] (g : ℕ) (hdim : SmoothOfRelativeDimension g A.hom) :
    ∃ (B : Over (Sp K)) (_ : GrpObj B) (_ : IsCommMonObj B) (φ : B.left ⟶ A.left),
      IsGrpPullback B A (spMap σ) φ ∧ ∃ y : Fin g → (epsR K ⟶ B), IsLieBasis y ∧
        ∀ i, ∃ (u : K) (w : epsR R ⟶ A), u ≠ 0 ∧ IsTangent w ∧
          (spMap (epsScaleR u) ≫ (y i).left) ≫ φ = spMap (Chart.dualMapR σ) ≫ w.left := by
  haveI : Smooth A.hom := hdim.smooth
  obtain ⟨r, hr, hCh, v, hv⟩ := LieProj.exists_chart_lieBasis A g hdim
    ⟨RingHom.ker σ, RingHom.ker_isPrime σ⟩
  have hr' : σ r ≠ 0 := hr
  let τ : Localization.Away r →+* K := IsLocalization.Away.lift r (IsUnit.mk0 _ hr')
  have hτ : τ.comp (algebraMap R _) = σ := IsLocalization.Away.lift_comp r _
  have hτ' : ∀ x, τ (algebraMap R _ x) = σ x := RingHom.congr_fun hτ
  haveI : ∀ s : R, Smooth (Chart.Gs A s).hom := fun s =>
    show Smooth (pullback.snd A.hom _) from inferInstance
  have h₁ := isGrpPullback_pullback A (Chart.fB R (Localization.Away r))
  have h₂ := isGrpPullback_pullback (Chart.Gs A r) (spMap τ)
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.exists_isLieBasis_baseChange _ K τ (Chart.Gs A r) _ _ h₂ inferInstance g v hv
  refine ⟨_, inferInstance, inferInstance, _, (h₂.comp h₁).congr ?_ rfl, y, hy, fun i ↦ ?_⟩
  · exact (Cris.spMap_comp _ _).symm.trans (congrArg spMap hτ)
  · obtain ⟨N, w, hw, he⟩ := LieAway.tan_away_lift r hCh
      ((LieAway.isTangent_iff_tanS r (v i)).1 (hv.1 i))
    refine ⟨σ r ^ N, w, pow_ne_zero _ hr', LieAway.isTangent_of_tanS hw, ?_⟩
    have he' : spMap (Chart.dualMapR (algebraMap R (Localization.Away r))) ≫ w.left =
        spMap (epsScaleR (algebraMap R (Localization.Away r) r ^ N)) ≫ (v i).left ≫
          pullback.fst A.hom (Chart.fB R (Localization.Away r)) := by
      have := congrArg (fun q ↦ q.left) he
      simp only [Over.comp_left, Chart.pushR_left, Chart.spMap_left] at this
      rw [← LieAway.scaleS_toRingHom]
      exact this
    have e1 : Chart.dualMapR σ =
        (Chart.dualMapR τ).comp (Chart.dualMapR (algebraMap R (Localization.Away r))) := by
      rw [← dualMapR_comp, hτ]
    have e2 : (epsScaleR (σ r ^ N)).comp (Chart.dualMapR τ) =
        (Chart.dualMapR τ).comp (epsScaleR (algebraMap R (Localization.Away r) r ^ N)) := by
      rw [← epsScaleR_comp_dualMapR, map_pow, hτ']
    rw [e1, Cris.spMap_comp, Category.assoc, Category.assoc, he', ← Category.assoc (y i).left, hyv,
      ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, e2, Cris.spMap_comp]
    simp only [Category.assoc]

theorem exists_lift_of_basis {K : Type} [Field K] [Algebra R K]
    (hσ : Function.Surjective (algebraMap R K)) {L L' : Type} {F F' : Type 1} [AddCommGroup L]
    [Module R L] [AddCommGroup L'] [Module K L'] [AddCommGroup F] [Module R F] [AddCommGroup F']
    [Module K F'] (l : L →ₗ[R] Module.Dual R F) (l' : L' →ₗ[K] Module.Dual K F') (p : F → F')
    {n : ℕ} (b : Module.Basis (Fin n) K L')
    (h : ∀ i, ∃ u : K, u ≠ 0 ∧ ∃ v, ∀ f, l' (u • b i) (p f) = algebraMap R K (l v f)) (z : L') :
    ∃ v, ∀ f, l' z (p f) = algebraMap R K (l v f) := by
  let S : Submodule K L' :=
    { carrier := {z | ∃ v, ∀ f, l' z (p f) = algebraMap R K (l v f)}
      zero_mem' := ⟨0, fun f ↦ by simp⟩
      add_mem' := by
        rintro a b ⟨v, hv⟩ ⟨w, hw⟩
        exact ⟨v + w, fun f ↦ by simp [hv, hw]⟩
      smul_mem' := by
        rintro c a ⟨v, hv⟩
        obtain ⟨r, rfl⟩ := hσ c
        exact ⟨r • v, fun f ↦ by
          rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
            hv, smul_eq_mul, smul_eq_mul, map_mul]⟩ }
  refine (Submodule.span_le.2 ?_ : Submodule.span K (Set.range b) ≤ S)
    (b.span_eq ▸ Submodule.mem_top)
  rintro _ ⟨i, rfl⟩
  obtain ⟨u, hu, hv⟩ := h i
  exact (S.smul_mem_iff hu).1 hv

set_option maxHeartbeats 1600000 in

theorem exists_tangent_residue (hC : GlobalTheory.Published.CrystallineSmoothLift)
    (hH : GlobalTheory.Published.AbelianHodgeDeRham) (K : Type) [Field K] [Algebra R K]
    (hσ : Function.Surjective (algebraMap R K)) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (g : ℕ)
    (hab : IsAbelianScheme A) (hdim : SmoothOfRelativeDimension g A.hom)
    (ψ : Module.Dual R (GlobForm (A.hom ≫ 𝟙 (Sp R)))) :
    ∃ v : Serre.Lie (Serre.intAct A), ∀ f,
      algebraMap R K (tanVal v.hom f) = algebraMap R K (ψ (glob _ f)) := by
  obtain ⟨B, _, _, φ, hφ, y, hy, hl⟩ := exists_lieBasis_lift (algebraMap R K) A g hdim
  have hab' : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hφ
  have hdim' : SmoothOfRelativeDimension g B.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback hφ.1 hdim
  have m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 K) (B.hom ≫ 𝟙 (Sp K)) (algebraMap R K) φ :=
    IsMor.of_dividedPowersZeroIdeal _ hφ.1.w
  obtain ⟨e, he⟩ : ∃ e : K ⊗[R] GlobForm (A.hom ≫ 𝟙 (Sp R)) ≃ₗ[K] GlobForm (B.hom ≫ 𝟙 (Sp K)),
      ∀ c, IsPullForm m.w c (e (1 ⊗ₜ c)) :=
    ((hH R A g hab hdim).2.2.2.2.2 K B.left B.hom φ hφ.1).2.1
  have hp : ∀ f, glob _ (m.pullForm f) = e (1 ⊗ₜ glob _ f) := fun f ↦
    (GlobalTheory.T.affinePairRestriction_injective_firstCohomology φ (B.hom ≫ 𝟙 (Sp K))).2.1 ((isPullForm_glob m f).symm.trans (he _))
  obtain ⟨v', hv'⟩ := exists_tangent_field hC hH B g hab' hdim' hy
    (Module.Dual.baseChange K ψ ∘ₗ e.symm.toLinearMap)
  have hb : ∀ i, ∃ u : K, u ≠ 0 ∧ ∃ v, ∀ f,
      lieVal B (u • Serre.Lie.basis (Serre.intAct B) hy i) (m.pullForm f) =
        algebraMap R K (lieVal A v f) := fun i ↦
    (hl i).elim fun u h ↦ h.elim fun w h ↦ ⟨u, h.1, Serre.Lie.mk _ w h.2.1, fun f ↦ by
      have k : (u • Serre.Lie.basis (Serre.intAct B) hy i).hom.left ≫ φ =
          spMap (Chart.dualMapR (algebraMap R K)) ≫ w.left := by
        rw [Serre.Lie.hom_smul_left, Serre.Lie.hom_basis]
        exact h.2.2
      rw [lieVal_apply, lieVal_apply, Serre.Lie.hom_mk]
      exact tanVal_pullForm m k f⟩
  obtain ⟨v, hv⟩ := exists_lift_of_basis hσ (lieVal A) (lieVal B) m.pullForm
    (Serre.Lie.basis (Serre.intAct B) hy) hb v'
  refine ⟨v, fun f ↦ (hv f).symm.trans ((hv' _).trans ?_)⟩
  rw [hp, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    Module.Dual.baseChange_apply_tmul, Algebra.smul_def, mul_one]

theorem exists_tangent_of_functional : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ φ : Form (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R, (∀ f, GlobalTheory.CechDR.cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → φ f = 0) → ∃ v : epsR R ⟶ A, IsTangent v ∧ ∀ f, tanVal v f = φ f := by
  intro hC hH R _ A _ g hab hdim φ hφ
  haveI := hab.comm
  have hs := glob_surjective hC hH A g hab hdim
  obtain ⟨hfin, hproj, -⟩ : Module.Finite R (GlobForm (A.hom ≫ 𝟙 (Sp R))) ∧
      Module.Projective R (GlobForm (A.hom ≫ 𝟙 (Sp R))) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (GlobForm (A.hom ≫ 𝟙 (Sp R))) p = g :=
    (hH R A g hab hdim).2.2.1
  obtain ⟨ψ, hψ⟩ := exists_factor hs φ hφ
  have hN := eq_top_of_residue
    ((LinearMap.range (lieVal A)).comap (glob (A.hom ≫ 𝟙 (Sp R))).dualMap) fun m hm α ↦ by
      letI := Ideal.Quotient.field m
      obtain ⟨v, hv⟩ := exists_tangent_residue hC hH (R ⧸ m) Ideal.Quotient.mk_surjective A g hab hdim α
      obtain ⟨χ, hχ⟩ := exists_factor hs (lieVal A v) (GlobalTheory.T.formValueOnTangentVector_eq_zero_of_globalForm_zero R A v.hom)
      refine ⟨χ, ⟨v, LinearMap.ext fun f ↦ (hχ f).symm⟩, fun x ↦ ?_⟩
      obtain ⟨f, rfl⟩ := hs x
      rw [hχ]
      exact Ideal.Quotient.eq.1 (hv f).symm
  obtain ⟨v, hv⟩ : ψ ∈ (LinearMap.range (lieVal A)).comap (glob (A.hom ≫ 𝟙 (Sp R))).dualMap :=
    hN ▸ Submodule.mem_top
  exact ⟨v.hom, v.isTangent, fun f ↦ (LinearMap.congr_fun hv f).trans (hψ f)⟩

end GlobalTheory.LieDual
