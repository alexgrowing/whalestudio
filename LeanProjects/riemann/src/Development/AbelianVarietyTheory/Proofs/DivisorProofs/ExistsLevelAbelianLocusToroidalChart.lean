import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NondegOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackSelf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart.AbLevel

theorem torsRat_of_isGrpPullback {R O : Type} [CommRing R] [IsDomain R] [CommRing O] [IsDomain O] (ρ : R →+* O)
    (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G] {A : Over (Sp O)} [GrpObj A] {π : A.left ⟶ G.left}
    (hπ : IsGrpPullback A G (spMap ρ) π) {n : ℕ} (h : TorsRat G n) : TorsRat A n := by
  intro K _ _ κ x hx
  have hj : Function.Injective ((algebraMap O (FractionRing O)).comp ρ) :=
    (IsFractionRing.injective O (FractionRing O)).comp hρ
  let i : FractionRing R →+* FractionRing O := IsFractionRing.lift hj
  have hsq : spMap i ≫ jK R = jK O ≫ spMap ρ := by
    show spMap i ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap O (FractionRing O)) ≫ spMap ρ
    rw [← spMap_comp, ← spMap_comp]
    have hi : ∀ r, i (algebraMap R (FractionRing R) r) = algebraMap O (FractionRing O) (ρ r) := fun r =>
      IsFractionRing.lift_algebraMap (K := FractionRing R) hj r
    exact congrArg spMap (RingHom.ext hi)
  let x0 := GlobalTheory.ObjPull.pushEquiv hπ _ x
  have hx0 : x0 ^ n = 1 := by simp only [x0, ← map_pow, hx, map_one]
  have hT : spMap (κ.comp i) ≫ jK R = (Over.mk (spMap κ ≫ jK O)).hom ≫ spMap ρ := by
    show _ = (spMap κ ≫ jK O) ≫ spMap ρ
    rw [spMap_comp, Category.assoc, hsq, Category.assoc]
  let e : Over.mk (spMap (κ.comp i) ≫ jK R) ⟶ Over.mk ((Over.mk (spMap κ ≫ jK O)).hom ≫ spMap ρ) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans hT.symm)
  obtain ⟨y, hy⟩ := h K (κ.comp i) (e ≫ x0) (by rw [← MonObj.comp_pow, hx0, MonObj.comp_one])
  have hy' : x.left ≫ π = spMap κ ≫ spMap i ≫ y.left := by
    have e₁ : x.left ≫ π = (e ≫ x0).left := (Category.id_comp _).symm
    exact e₁.trans (hy.trans ((congrArg (· ≫ y.left) (spMap_comp i κ)).trans (Category.assoc _ _ _)))
  have hz : (spMap i ≫ y.left) ≫ G.hom = jK O ≫ spMap ρ := by
    rw [Category.assoc, Over.w y]
    exact hsq
  refine ⟨Over.homMk (hπ.1.lift _ (jK O) hz) (hπ.1.lift_snd _ _ _), hπ.1.hom_ext ?_ ?_⟩
  · show x.left ≫ π = (spMap κ ≫ hπ.1.lift _ (jK O) hz) ≫ π
    rw [Category.assoc, hπ.1.lift_fst, hy']
  · show x.left ≫ A.hom = (spMap κ ≫ hπ.1.lift _ (jK O) hz) ≫ A.hom
    rw [Category.assoc, hπ.1.lift_snd]
    exact Over.w x

theorem exists_factor {S S' T : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] {H : Over T} [GrpObj H]
    {f : S' ⟶ S} {t : T ⟶ S'} {u : T ⟶ S} (hu : t ≫ f = u) {π : A.left ⟶ G.left} {π₂ : (A ⊗ A).left ⟶ (G ⊗ G).left}
    (hπ : IsGrpPullback A G f π) (sπ : IsSquare π π₂) {a : H.left ⟶ G.left} {a₂ : (H ⊗ H).left ⟶ (G ⊗ G).left}
    (ha : IsGrpPullback H G u a) (sa : IsSquare a a₂) :
    ∃ (ψ : H.left ⟶ A.left) (ψ₂ : (H ⊗ H).left ⟶ (A ⊗ A).left), IsGrpPullback H A t ψ ∧ IsSquare ψ ψ₂ ∧ a₂ = ψ₂ ≫ π₂ := by
  let ψ := hπ.1.lift a (H.hom ≫ t) (by rw [Category.assoc, hu]; exact ha.1.w)
  have hψ : ψ ≫ π = a := hπ.1.lift_fst _ _ _
  have hpb : IsGrpPullback H A t ψ := hπ.cancel (ha.congr hu.symm hψ.symm) (hπ.1.lift_snd _ _ _)
  have sψ := GlobalTheory.LamPull.exists_isSquare hpb.1.w
  exact ⟨ψ, _, hpb, sψ, GlobalTheory.LamPull.isSquare_unique sa (hψ ▸ AbPol.isSquare_comp sψ sπ)⟩

theorem sameFib_factor {S₁ S₂ S₁' S₂' T : Scheme.{0}} {G₁ : Over S₁} [GrpObj G₁] [IsCommMonObj G₁] {P₁ : LB (G2 G₁).left}
    {G₂ : Over S₂} [GrpObj G₂] [IsCommMonObj G₂] {P₂ : LB (G2 G₂).left} (h₁ : P₁.IsLB) (h₂ : P₂.IsLB)
    {A₁ : Over S₁'} [GrpObj A₁] [IsCommMonObj A₁] {A₂ : Over S₂'} [GrpObj A₂] [IsCommMonObj A₂]
    {f₁ : S₁' ⟶ S₁} {t₁ : T ⟶ S₁'} {u₁ : T ⟶ S₁} (e₁ : t₁ ≫ f₁ = u₁)
    {f₂ : S₂' ⟶ S₂} {t₂ : T ⟶ S₂'} {u₂ : T ⟶ S₂} (e₂ : t₂ ≫ f₂ = u₂)
    {π₁ : A₁.left ⟶ G₁.left} {q₁ : (G2 A₁).left ⟶ (G2 G₁).left} (p₁ : IsGrpPullback A₁ G₁ f₁ π₁) (s₁ : IsSquare π₁ q₁)
    {π₂ : A₂.left ⟶ G₂.left} {q₂ : (G2 A₂).left ⟶ (G2 G₂).left} (p₂ : IsGrpPullback A₂ G₂ f₂ π₂) (s₂ : IsSquare π₂ q₂)
    (h : SameFib G₁ P₁ u₁ G₂ P₂ u₂) : SameFib A₁ (P₁.pull q₁) t₁ A₂ (P₂.pull q₂) t₂ := by
  obtain ⟨H, _, _, a, a₂, a', a₂', ha, sa, ha', sa', e⟩ := h
  obtain ⟨ψ, ψ₂, hψ, sψ, rfl⟩ := exists_factor e₁ p₁ s₁ ha sa
  obtain ⟨χ, χ₂, hχ, sχ, rfl⟩ := exists_factor e₂ p₂ s₂ ha' sa'
  refine ⟨H, inferInstance, inferInstance, ψ, ψ₂, χ, χ₂, hψ, sψ, hχ, sχ, ?_⟩
  have c := (CechPic.cls_eq_iff (pull_isLB h₁ _) (pull_isLB h₂ _)).2 e
  rw [← CechPic.cls_eq_iff (pull_isLB (pull_isLB h₁ _) _) (pull_isLB (pull_isLB h₂ _) _),
    CechPic.cls_pull (pull_isLB h₁ _), CechPic.cls_pull (pull_isLB h₂ _), CechPic.cls_pull h₁, CechPic.cls_pull h₂,
    ← CechPic.pull_comp, ← CechPic.pull_comp]
  rwa [CechPic.cls_pull h₁, CechPic.cls_pull h₂] at c

theorem lbIso_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {N : LB Z} (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB)
    {a : Y ⟶ X} {b : Z ⟶ Y} (e : LBIso M (L.pull a)) (e' : LBIso N (M.pull b)) : LBIso N (L.pull (b ≫ a)) := by
  have c := (CechPic.cls_eq_iff hM (pull_isLB hL _)).2 e
  have c' := (CechPic.cls_eq_iff hN (pull_isLB hM _)).2 e'
  rw [← CechPic.cls_eq_iff hN (pull_isLB hL _), c', CechPic.cls_pull hM, c, CechPic.cls_pull hL, CechPic.cls_pull hL,
    CechPic.pull_comp]

theorem siegPB_trans {h n : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    {s'' : S'' ⟶ Sp B} {u : SiegPre h n ζ s} {c : SiegPre h n ζ s'} {c' : SiegPre h n ζ s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (m' : SiegPB c' c f') (m : SiegPB c u f) : SiegPB c' u (f' ≫ f) := by
  obtain ⟨φ, φ₂, hφ, hs, hw, hl⟩ := m
  obtain ⟨ψ, ψ₂, hψ, hs', hw', hl'⟩ := m'
  exact ⟨ψ ≫ φ, ψ₂ ≫ φ₂, hψ.comp hφ, AbPol.isSquare_comp hs' hs, lbIso_comp u.isLB c.isLB c'.isLB hw hw', fun a =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))⟩

theorem exists_level : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) → TorsRat G₁ n → ∀ (K : Type) [Field K] (κ : Localization.Away (∏ k, C.t k) →+* K) (x₀ : Sp K ⟶ F.X), x₀ ≫ F.s = spMap ((κ.comp (algebraMap C.R (Localization.Away (∏ k, C.t k)))).comp C.b) → SameFib F.univ.A F.univ.P x₀ G₁ P (spMap (κ.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))))) → ∃ c : SiegPre g n (zetaAway n) (spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b)), c.Principal ∧ (∃ (a : c.A.left ⟶ G₁.left) (a₂ : (G2 c.A).left ⟶ (G2 G₁).left), IsGrpPullback c.A G₁ (spMap (algebraMap C.R (Localization.Away (∏ k, C.t k)))) a ∧ IsSquare a a₂ ∧ LBIso c.P (P.pull a₂)) ∧ ∀ yU : Sp (Localization.Away (∏ k, C.t k)) ⟶ F.X, SiegPB c F.univ yU → yU ≫ F.s = spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b) → spMap κ ≫ yU = x₀ := by
  intro g n φ hn hodd F C G₁ _ _ P hM hab hT K _ κ x₀ hx₀ hsf
  obtain ⟨A, _, _, π₀, π₂, hπ, sπ, hA, hP⟩ := AbPol.exists_isPPol_away g n φ hn C G₁ P hM hab
  have hCN := hM.1
  have hPG := hM.2.2.2.1.1
  let t := ∏ k, C.t k
  let O := Localization.Away t
  have ht0 : t ≠ 0 := fun h0 => by
    have hu := (IsLocalization.Away.algebraMap_isUnit (S := O) t).map κ
    have : algebraMap C.R O t = 0 := (congrArg (algebraMap C.R O) h0).trans (map_zero _)
    rw [this, map_zero] at hu
    exact not_isUnit_zero hu
  haveI := hCN.1
  haveI := hCN.2.1
  have hle : Submonoid.powers t ≤ nonZeroDivisors C.R := powers_le_nonZeroDivisors_of_noZeroDivisors ht0
  haveI : IsDomain O := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing (Submonoid.powers t) _ inferInstance
  haveI : IsIntegrallyClosed O := isIntegrallyClosed_of_isLocalization O (Submonoid.powers t) hle
  have hTA : TorsRat A n := torsRat_of_isGrpPullback _ (IsLocalization.injective O hle) hπ hT
  let b : cycAway n →+* O := (algebraMap C.R O).comp C.b
  let c₀ : SiegPre g n (zetaAway n) (spMap (κ.comp b)) := GlobalTheory.LowChart.siegPull F.univ x₀ _ hx₀
  have pb₀ : SiegPB c₀ F.univ x₀ := GlobalTheory.LowChart.siegPB_siegPull _ _ _ _
  have hs₀ : SameFib c₀.A c₀.P (𝟙 _) A (P.pull π₂) (spMap κ) :=
    sameFib_factor F.univ.isLB hPG (Category.id_comp x₀) (spMap_comp _ _).symm
      (Pdiv.PullbackComparison.isGrpPullback x₀ F.univ.A) (Pdiv.PullbackComparison.isSquare x₀ F.univ.A) hπ sπ hsf
  obtain ⟨c, hc, hcc, a, a₂, ha, sa, ea⟩ := GlobalTheory.LevSpread.level_spreads n hn hodd O b A (P.pull π₂) hA hP hTA g K κ c₀
    (GlobalTheory.LowChart.principal_siegPull _ _ _ _ F.princ) hs₀
  refine ⟨c, hc, ⟨a ≫ π₀, a₂ ≫ π₂, (ha.comp hπ).congr (Category.id_comp _) rfl, AbPol.isSquare_comp sa sπ,
    lbIso_comp hPG (pull_isLB hPG _) c.isLB (GlobalTheory.lbIso_refl (pull_isLB hPG _)) ea⟩, fun yU hy hys => ?_⟩
  refine F.inj K _ _ _ c₀ ?_ (siegPB_trans hcc hy) pb₀
  rw [Category.assoc, hys, hx₀, ← spMap_comp, RingHom.comp_assoc]

end GlobalTheory.TChart.AbLevel
