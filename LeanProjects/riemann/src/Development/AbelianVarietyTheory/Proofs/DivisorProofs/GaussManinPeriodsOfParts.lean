import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback

set_option autoImplicit false

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CatCoh GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem taylor_congr {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D)
    {f f' : (I → ℂ) → ℂ} (h : f =ᶠ[nhds 0] f') : taylor N t f = taylor N t f' := by
  unfold taylor
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  rw [(h.iteratedFDeriv ℂ k).eq_of_nhds]

theorem isAb_pull {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (h : IsGrpPullback A' A f φ) (hA : IsAbelianScheme A) : IsAbelianScheme A' :=
  GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h

theorem gaussManinPeriods_of_parts : ∀ ε : ℤˣ, GlobalTheory.PeriodFamily.FamUnif → PExist → PHom → PSpan → PLie → PEnd → PChern ε → PFix → PTaylor → GlobalTheory.Published.GaussManinPeriods := by
  intro ε HF HE HH HS HL HEn HC HX HT
  have pm : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      ∀ (L : LB A.left), L.IsLB → ∀ (u : HolUnif A L g) (P : u.Λ →+ HdR A), IsPeriodHom u P → IsPeriodMap ε u P :=
    fun A _ g hA hg L hL u P hP ↦ ⟨(HS A g hA hg L u P hP).1, (HS A g hA hg L u P hP).2, HL A g hA hg L u P hP,
      fun α _ M ↦ HEn A g hA L u P hP α M, fun H χ ψ ↦ HC A g hA L u P hP L u hL rfl H χ ψ⟩
  refine ⟨ε, fun B _ _ _ 𝒜 _ g h𝒜 hg I _ _ U y hU h0 hy A _ φ hφ m L hL A₀ _ φ₀ hφ₀ L₀ hL₀ u₀ ↦ ?_⟩
  obtain ⟨r, u, τ, hr, hrU, hhol, ⟨W, hW, hW0⟩, c1, c2, c3, c4⟩ :=
    HF B 𝒜 g h𝒜 hg I U y hU h0 hy A φ hφ L hL A₀ φ₀ hφ₀ L₀ u₀
  have hA : ∀ z, IsAbelianScheme (A z) := fun z ↦ isAb_pull (hφ z) h𝒜
  have hA₀ : IsAbelianScheme A₀ := isAb_pull hφ₀ h𝒜
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  have gA : ∀ z, SmoothOfRelativeDimension g (A z).hom := fun z ↦
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) (hφ z).1 hg
  have gA₀ : SmoothOfRelativeDimension g A₀.hom :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hφ₀.1 hg
  choose P hP using fun z ↦ HH (A z) g (hA z) (L z) (u z)
  obtain ⟨P₀, hP₀⟩ := HH A₀ g hA₀ L₀ u₀
  let V : Opens (I → ℂ) := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
  have V0 : (0 : I → ℂ) ∈ V := Metric.mem_ball_self hr
  let F : Fam I g u₀.Λ :=
    { V := V
      τ := { toFun x z := (τ z x : Fin g → ℂ)
             map_zero' := funext fun z ↦ by simp
             map_add' a b := funext fun z ↦ by simp }
      hol x := GlobalTheory.SCV.analyticOnNhd_of_differentiableOn Metric.isOpen_ball (c3 x) }
  have ya : ∀ b, AnalyticOnNhd ℂ (fun z ↦ y z b) V := fun b ↦
    GlobalTheory.SCV.analyticOnNhd_of_differentiableOn Metric.isOpen_ball ((hy b).mono hrU)
  let σ : B →ₐ[ℂ] Hol F.V :=
    { toFun b := Hol.mk _ (ya b)
      map_one' := Subtype.ext (funext fun z ↦ map_one (y z))
      map_mul' a b := Subtype.ext (funext fun z ↦ map_mul (y z) a b)
      map_zero' := Subtype.ext (funext fun z ↦ map_zero (y z))
      map_add' a b := Subtype.ext (funext fun z ↦ map_add (y z) a b)
      commutes' a := Subtype.ext (funext fun z ↦ (y z).commutes a) }
  have hσ : ∀ b, ∀ z ∈ V, (σ b).fn z = y z b := fun b z hz ↦ Hol.fn_mk _ (ya b) hz
  let e : Unif F (𝒜.hom ≫ 𝟙 _) (σ : B →+* Hol F.V) :=
    { E q := (show Sp ℂ ⟶ (A q.1).left from ((u q.1).ex q.2).left) ≫ φ q.1
      w p hp := by
        have e1 : (show Sp ℂ ⟶ (A p.1).left from ((u p.1).ex p.2).left) ≫ (A p.1).hom = 𝟙 _ := Over.w ((u p.1).ex p.2)
        rw [Category.comp_id, Category.assoc, (hφ p.1).1.w, ← Category.assoc, e1, Category.id_comp]
        rfl
      per l p _ := by
        have : (u p.1).ex (p.2 + (τ p.1 l : Fin g → ℂ)) = (u p.1).ex p.2 := by
          rw [(u p.1).ex_add, ((u p.1).ker _).2 (τ p.1 l).2, _root_.mul_one]
        exact congrArg (fun x : 𝟙_ (Over (Sp ℂ)) ⟶ A p.1 ↦ (show Sp ℂ ⟶ (A p.1).left from x.left) ≫ φ p.1) this
      hol U' f := by
        have := hhol U' f
        simp only [Set.mem_prod, Set.mem_univ, and_true] at this
        exact this }
  haveI : IsSeparated (𝒜.hom ≫ 𝟙 _) := by
    rw [Category.comp_id]
    haveI := h𝒜.proper
    infer_instance
  choose per hper using HE I g u₀.Λ F B 𝒜.left _ _ e ⟨W, hW, hW0⟩
  have fix : ∀ x (c : primDR 𝒜), ∀ z ∈ V, P z (τ z x) ((m z).pull c) = (per c.1 x).fn z := fun x c z hz ↦
    HX I g u₀.Λ F B 𝒜 h𝒜 _ e z hz _ (fun b ↦ (hσ b z hz).symm) (A z) (hA z) (φ z) (m z) (L z) (u z) (fun _ ↦ rfl)
      (τ z).toAddMonoidHom (fun _ ↦ rfl) (P z) (hP z) c _ (hper c.1) x
  have nV : (V : Set (I → ℂ)) ∈ nhds (0 : I → ℂ) := V.isOpen.mem_nhds V0
  refine ⟨Metric.ball 0 r, u, τ, P, P₀, Metric.isOpen_ball, V0, hrU, pm A₀ g hA₀ gA₀ L₀ hL₀ u₀ P₀ hP₀,
    fun z _ ↦ pm _ g (hA z) (gA z) _ (hL z) _ _ (hP z), c1, c2, c3, c4,
    fun x c ↦ (per c.1 x).analytic.differentiableOn.congr (fix x c), ?_⟩
  intro D _ _ π κ hκ hπ N t ht hN j hj A' _ φ' hφ' m' i h hi k x d hd c
  rw [HT I g B 𝒜 h𝒜 hg (y 0) A₀ φ₀ hφ₀ L₀ u₀ F σ e V0 (fun b ↦ (hσ b 0 V0).symm) c1 (fun x ↦ c2 x) P₀ hP₀ D π κ hκ hπ N t ht hN j
    (fun b ↦ (hj b).trans (taylor_congr N t (Filter.mem_of_superset nV fun z hz ↦ (hσ b z hz).symm)))
    A' φ' hφ' m' i h hi k x d hd c _ (hper c.1)]
  exact taylor_congr N t (Filter.mem_of_superset nV fun z hz ↦ (fix x c z hz).symm)

end GlobalTheory.AnPer
