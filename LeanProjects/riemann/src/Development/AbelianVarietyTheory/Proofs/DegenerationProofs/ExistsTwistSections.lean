import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByOfSpans
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsChartUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaPullbackNonzeroOnClosedFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ThetaData

theorem valR_eq_gs {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (x : Sp R ⟶ X) (U : X.Opens)
    (h : x (IsLocalRing.closedPoint R) ∈ U) (f : Γ(X, U)) :
    valR x U f = (stalkClosedPointIso (CommRingCat.of R)).hom.hom (gs x (IsLocalRing.closedPoint R) U f) := by
  have h' := (CrdCalc.top_le_iff x U).2 h
  rw [CrdCalc.valR_eq x U h', gs_eq x _ U h]
  have e := germ_stalkClosedPointIso_hom (CommRingCat.of R)
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    (((Sp R).presheaf.map (homOfLE h').op).hom ((x.app U).hom f)) = _
  rw [← e]
  exact congrArg (stalkClosedPointIso (CommRingCat.of R)).hom.hom
    (TopCat.Presheaf.germ_res_apply (Sp R).presheaf (homOfLE h') _ trivial _)

theorem crd_of_chartSec {R : Type} [CommRing R] [IsLocalRing R] {Y Y' : Scheme.{0}} {A' : LB Y'} {A : LB Y}
    {h : Y' ⟶ Y} (a : ChartPull A' A h) {J : Type} (s : J → A.Sec) (x : Sp R ⟶ Y') (v : J → R)
    (H : Crd A' (fun j => chartSec a (s j)) x v) : Crd A s (x ≫ h) v := by
  obtain ⟨l, c, hl, hv⟩ := H
  have m := (CrdCalc.top_le_iff x _).1 hl
  have m' : (x ≫ h) (IsLocalRing.closedPoint R) ∈ A.U (a.idx l) := a.le l m
  refine ⟨a.idx l, c, (CrdCalc.top_le_iff _ _).2 m', fun j => ?_⟩
  rw [hv, valR_eq_gs x _ m, valR_eq_gs _ _ m', gs_chartSec a (s j) x _ l m]

theorem crd_secPull {R : Type} [CommRing R] [IsLocalRing R] {Y Y' : Scheme.{0}} {A : LB Y}
    (h : Y' ⟶ Y) {J : Type} (s : J → A.Sec) (x : Sp R ⟶ Y') (v : J → R)
    (H : Crd A s (x ≫ h) v) : Crd (A.pull h) (fun j => secPull (s j) h) x v := by
  obtain ⟨l, c, hl, hv⟩ := H
  have m' := (CrdCalc.top_le_iff _ _).1 hl
  have m : x (IsLocalRing.closedPoint R) ∈ (A.pull h).U (fun _ => l) := mem_pull.2 m'
  refine ⟨fun _ => l, c, (CrdCalc.top_le_iff _ _).2 m, fun j => ?_⟩
  rw [hv, valR_eq_gs x _ m, valR_eq_gs _ _ m']
  exact congrArg (fun q => (c : R) * (stalkClosedPointIso (CommRingCat.of R)).hom.hom q)
    (gs_chartSec (GlobalTheory.chartPullPull A h) (s j) x _ (fun _ => l) m).symm

theorem exists_twist_sections {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -1])} (hα : α.IsGen) {J : Type}
    (s : J → LB.Sec (LPow A L a T)) (th : LB.Sec (LPow A L 1 T)) (i₀ : J)
    (H : IsTwistPull A L ψ m hm a 1 α th (s i₀)) {Y : Scheme.{0}} (κ : Y ⟶ (T ⊗ A).left) (F : Y ⟶ A.left)
    (hF : κ ≫ (snd T A).left = F) (n : Y ⟶ Y) (hn : n ≫ κ = κ ≫ ψ.left) :
    ∃ (θ : (L.pull F).Sec) (t : J → ((L.pull F).pull n).Sec),
      (∀ (K : Type) [Field K] (x : Sp K ⟶ Y) (v : J → K), Crd _ t x v → Crd (LPow A L a T) s (x ≫ κ) v) ∧
      ∀ (y : Y) (j : (L.pull F).ι), n y ∈ (L.pull F).U j →
        gs (𝟙 Y) y _ ((t i₀).f (fun _ => j)) = gs n y _ (θ.f j) := by
  have e : κ ≫ m.left = n ≫ F := by
    rw [← hm, Over.comp_left, ← Category.assoc, ← hn, Category.assoc, hF]
  obtain ⟨θ, hθ⟩ := exists_sec hL (φ := fun _ : Fin 1 => F) (ε := fun _ => 1) (φ' := fun _ : PUnit => F)
    (ε' := fun _ => 1) (fun U _ h => by simp)
    (VVRank.pullTo (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => 1) th κ (fun _ => hF))
  have hu := LB.isGen_invGen L _ _ _ (LB.isGen_pullGen L _ _ α hα κ)
  have hσ : ∀ j, ∃ σ : (L.pull (n ≫ F)).Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I), Good L z I →
      sval (φ := fun _ : PUnit => n ≫ F) (ε := fun _ => 1) σ r z I =
        VVRank.sv A (s j) (r ≫ κ) z I * ((val α (r ≫ κ) z I)⁻¹).val := by
    intro j
    obtain ⟨σ, hσ⟩ := exists_sec hL (φ' := fun _ : PUnit => n ≫ F) (ε' := fun _ => 1)
      (fun U _ h => by simp [Fintype.prod_sum_type, e])
      (pullMulSec (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (s j) κ _ hu)
    refine ⟨σ, fun Z r z I hI => (hσ Z r z I hI).trans ((sval_pullMulSec _ κ _ hu r z hI).trans ?_)⟩
    rw [val_inv, val_pull hI]
  choose σ hσ using hσ
  let c := chartPullLinComb L F (fun _ : PUnit => n) (fun _ : PUnit => n ≫ F) (fun _ => 1) (𝟙 Y)
    (fun _ => (Category.id_comp _).symm)
  refine ⟨θ, fun j => chartSec c (σ j), fun K _ x v hv => ?_, fun y j hj => ?_⟩
  · obtain ⟨l, u, hl, hv⟩ := crd_of_chartSec c σ x v hv
    rw [Category.comp_id] at hl hv
    have m₁ := (CrdCalc.top_le_iff _ _).1 hl
    obtain ⟨I, hI, eI⟩ := exists_good L hL (IsLocalRing.closedPoint K : Sp K) (fun _ : PUnit => x ≫ n ≫ F) l
      (fun _ _ _ => rfl) (fun k => Set.mem_iInter.1 m₁ k)
    have m₂ := hI.mem (fun _ : Fin 1 => (snd T A).left) (x ≫ κ)
    refine ⟨fun _ => I ((x ≫ κ) ≫ (snd T A).left), u * Units.map (stalkClosedPointIso (CommRingCat.of K)).hom.hom.toMonoidHom
      (val α (x ≫ κ) _ I)⁻¹, (CrdCalc.top_le_iff _ _).2 m₂, fun j => ?_⟩
    have e₁ := (sval_of (φ := fun _ : PUnit => n ≫ F) (ε := fun _ => 1) (σ j) x _ I l eI).symm.trans (hσ j _ x _ I hI)
    refine (hv j).trans ?_
    refine (congrArg (_ * ·) ((valR_eq_gs x _ m₁ _).trans ((congrArg _ e₁).trans (map_mul _ _ _)))).trans ?_
    rw [Units.val_mul, _root_.mul_assoc, _root_.mul_comm (Units.val (Units.map _ _))]
    exact congrArg (fun q => (u : K) * (q * _)) (valR_eq_gs (x ≫ κ) _ m₂ _).symm
  · have m₁ : (n ≫ F) y ∈ L.U (j PUnit.unit) := mem_pull (F := F).1 hj
    obtain ⟨I, hI, eI⟩ := exists_good L hL y (fun _ : PUnit => n ≫ F) j (fun _ _ _ => rfl) (fun k => m₁)
    refine (gs_chartSec c (σ i₀) (𝟙 Y) y (fun _ => j) (mem_pull (F := n).2 hj)).trans ?_
    have e₁ := (sval_of (φ := fun _ : PUnit => n ≫ F) (ε := fun _ => 1) (σ i₀) (𝟙 Y ≫ 𝟙 Y) y I j
      (fun k => by simpa using eI k)).symm.trans (hσ i₀ _ _ _ I hI)
    have e₂ := (sval_of (φ := fun _ : PUnit => F) (ε := fun _ => 1) θ n y I j eI).symm.trans
      ((hθ _ n y I hI).trans (VVRank.sval_pullTo _ _ _ _ _ hI))
    refine e₁.trans (Eq.trans ?_ e₂.symm)
    rw [VVRank.sv_of_isTwistPull A H _ y hI, mul_right_comm, Units.mul_inv, _root_.one_mul, hn]
    simp only [Category.id_comp]

theorem mulN_eq_id_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = (𝟙 G) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem mulN_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    (mulN G' n).left ≫ φ = φ ≫ (𝟙 G ^ n : G ⟶ G).left := by
  have e := congrArg (fun q => q.left) (map_pow (pushHom h G') (𝟙 G') n)
  have e₂ : pushHom h G' (𝟙 G') ≫ 𝟙 G ^ n = pushHom h G' (𝟙 G') ^ n := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [← e₂, ← mulN_eq_id_pow] at e
  refine Eq.trans e ?_
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem exists_iso [ArithBase o Ω] (hLL : GlobalTheory.UT.LL) {S : ThetaSys o Ω} (ρ : S.Real) {B : Scheme.{0}} (A' : Over B)
    [GrpObj A'] [IsCommMonObj A'] [IsIntegral A'.left] {f : B ⟶ Sp S.R} {F : A'.left ⟶ ρ.P.A.left}
    (h : IsGrpPullback A' ρ.P.A f F) {Y : Scheme.{0}} (a : A'.left ⟶ Y) {O : LB Y} (hO : O.IsLB) (st : S.J → O.Sec)
    (hc : ∀ (K : Type) [Field K] (x : Sp K ⟶ A'.left) (v : S.J → K), ρ.Crd (x ≫ F) v → Crd O st (x ≫ a) v) :
    ∃ (θ : (ρ.P.L.pull F).Sec) (w : LB.Iso ((ρ.P.L.pull F).pull (mulN A' (ρ.n ^ ρ.k)).left) (O.pull a)), w.IsGen ∧
      ∀ (x : A'.left) (i : O.ι) (j : (ρ.P.L.pull F).ι), a x ∈ O.U i →
        (mulN A' (ρ.n ^ ρ.k)).left x ∈ (ρ.P.L.pull F).U j →
        gs a x _ ((st ρ.i₀).f i) = gs (𝟙 _) x _ (w.s (fun _ => i, fun _ => j)).val *
          gs (mulN A' (ρ.n ^ ρ.k)).left x _ (θ.f j) := by
  have : IsIso (snd (baseOver (Sp S.R)) ρ.P.A).left :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (Sp S.R)) ρ.P.A.hom))
  let κ := F ≫ inv (snd (baseOver (Sp S.R)) ρ.P.A).left
  have hκ : κ ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = F := by simp [κ]
  have hn : (mulN A' (ρ.n ^ ρ.k)).left ≫ κ = κ ≫ (mulT ρ.P.A (baseOver (Sp S.R)) (ρ.n ^ ρ.k)).left := by
    rw [← cancel_mono (snd (baseOver (Sp S.R)) ρ.P.A).left, Category.assoc, hκ, mulN_comp h, Category.assoc,
      ← Over.comp_left, mulT, lift_snd, ← hκ, Category.assoc, ← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨θ, t, ht, hθ⟩ := exists_twist_sections ρ.P.A ρ.P.isLB ρ.α_gen ρ.s ρ.th₁ ρ.i₀ ρ.s_zero κ F hκ _ hn
  have hH := LB.isLB_pull (LB.isLB_pull ρ.P.isLB F) (mulN A' (ρ.n ^ ρ.k)).left
  have hcov : ⨆ j, nonzeroLocus (t j) = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨K, _, p, hp⟩ := CrdIso.exists_pt y
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists hH t p
    have h₀ := (ThetaSys.Real.immBy_basis hLL o Ω S ρ).1
    have h₁ : (p ≫ κ) (IsLocalRing.closedPoint K) ∈ ⨆ i ∈ (Set.univ : Set S.J), nonzeroLocus (ρ.s i) := by
      rw [h₀]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h₁
    obtain ⟨-, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    have h₂ := (CrdCalc.crd_isUnit_iff i (ht K p v hv)).2 ((CrdCalc.top_le_iff _ _).2 hi)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hp _).1 ((CrdCalc.crd_isUnit_iff i hv).1 h₂)⟩
  obtain ⟨w, hw, hs⟩ := CrdIso.exists_iso_of_crd _ _ (O.pull a) _ t (fun j => secPull (st j) a) hH
    (LB.isLB_pull hO a) hcov (fun K _ x v hv => crd_secPull a st x v
      (hc K x v ⟨x ≫ κ, by rw [Category.assoc, hκ], ht K x v hv⟩))
  refine ⟨θ, w, hw, fun x i j hi hj => ?_⟩
  have e := hs ρ.i₀ x (fun _ => j) (fun _ => i) (mem_pull.2 hj) (mem_pull.2 hi)
  rw [hθ x j hj] at e
  refine Eq.trans ?_ e
  have e' := gs_chartSec (GlobalTheory.chartPullPull O a) (st ρ.i₀) (𝟙 _) x (fun _ => i) (mem_pull.2 hi)
  rw [Category.id_comp] at e'
  exact e'.symm

theorem exists_theta : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ∃ T : ex.core.Theta, LBIso T.L.L (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) := by
  intro hLL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex hS hG
  have := ArithBase.ded (o := o) (Ω := Ω)
  have : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  have : IsNoetherianRing S.R := Algebra.FiniteType.isNoetherianRing o S.R
  have : IsLocallyNoetherian (Sp S.R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of S.R)))
  have := ex.ab.comm
  have hI : IsIntegral ex.core.A.left := by
    have := ex.core.isIntegral_G
    have := ex.core.isOpenImmersion_a
    have := ex.core.nonempty_A
    exact isIntegral_of_isOpenImmersion ex.core.a
  have : IsIntegral ((Over.pullback Q.u₀).obj ρ.P.A).left := hI
  have h := isGrpPullback_pullback ρ.P.A Q.u₀
  obtain ⟨c⟩ := (hLL.1.cube _ ρ.P ⟨ρ.P.L, ρ.rig, ρ.P.isLB, ρ.rig_gen⟩ rfl).1
  obtain ⟨hL, hr, ⟨c', -⟩, -⟩ := hLL.2.2.1.cubePull _ _ _ _ (cubeMapOf h) _ c
  obtain ⟨θ, w, hw, hs⟩ := exists_iso hLL ρ _ h ex.a (LB.isLB_pull Q.isLB Q.G.ι) (fun j => secPull (Q.st j) Q.G.ι)
    (fun K _ x v hv => crd_secPull _ _ _ _ (by
      have e := Q.crd K x v hv
      rw [← ex.a_eq] at e
      rw [Category.assoc]
      exact e))
  have hm : IsUnit ((ρ.n ^ ρ.k : ℕ) : Γ(M.Z, ⊤)) := by
    have h₁ : IsUnit ((ρ.n ^ ρ.k : ℕ) : o) :=
      isUnit_of_dvd_unit (Nat.cast_dvd_cast (ρ.N_eq ▸ Dvd.dvd.mul_left (dvd_pow_self _ two_ne_zero) S.r)) S.unit
    have h₂ := h₁.map (M.s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom)
    rwa [map_natCast] at h₂
  refine ⟨⟨_, c', θ, ρ.n ^ ρ.k, hm, _, LB.isLB_pull Q.isLB Q.G.ι, secPull (Q.st ρ.i₀) Q.G.ι, w, hw, hs,
    fun z hz => ?_⟩, lbIso_refl hL⟩
  obtain ⟨x, hx, hG', e⟩ := GlobalTheory.T.exists_theta_pullback_nonzero_on_closed_fibre hLL o Ω S ρ M U₀ EE hB Q hS hG z hz
  refine ⟨⟨x, hG'⟩, ?_, e⟩
  erw [nonzeroLocus_secPull]
  exact hx

end GlobalTheory.ZH.ThetaData
end
