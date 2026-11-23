import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GsAppTopOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmSpMapUnitOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishTorsion
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralSectionUnitAt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIsoRel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.Coef

section Nonvanishing

open GlobalTheory.UT

theorem exists_chartSec {Y Y' : Scheme.{0}} {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (s : LB.Sec A) :
    ∃ s' : LB.Sec A', ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (i : A'.ι), r z ∈ A'.U i →
      gs r z (A'.U i) (s'.f i) = gs (r ≫ h) z (A.U (a.idx i)) (s.f (a.idx i)) := by
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (i : A'.ι), r z ∈ A'.U i →
      gs r z (A'.U i) ((Y'.presheaf.map (homOfLE (a.le i)).op).hom ((h.app _).hom (s.f (a.idx i)))) =
        gs (r ≫ h) z (A.U (a.idx i)) (s.f (a.idx i)) := fun Z r z i hi =>
    (gs_res r z _ hi _).trans (gs_pull r h z _ (a.le i hi) _)
  refine ⟨⟨fun i => (Y'.presheaf.map (homOfLE (a.le i)).op).hom ((h.app _).hom (s.f (a.idx i))),
    fun i j => fn_ext fun y hy => ?_⟩, v⟩
  have hm : (𝟙 Y' ≫ h) y ∈ A.U (a.idx i) ⊓ A.U (a.idx j) := ⟨a.le i hy.1, a.le j hy.2⟩
  have e := congrArg (gs (𝟙 Y' ≫ h) y (A.U (a.idx i) ⊓ A.U (a.idx j))) (s.compat (a.idx i) (a.idx j))
  rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_unit _ y _ hm] at e
  refine ((gs_res _ y _ hy _).trans (v _ _ y i hy.1)).trans (e.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans ?_) ((gs_res _ y _ hy _).trans (v _ _ y j hy.2))))))
  rw [a.g y i j hy.1 hy.2, Category.id_comp]

variable {V₁ : Type} [CommRing V₁] [IsDomain V₁] (D : DegPre V₁)

theorem famφB_zero {T : Over (Sp V₁)} (y : T ⟶ D.P.A) : (fun k => y.left ≫ D.famφB 0 k) =
    ![y.left, y.left, (1 : T ⟶ D.P.A).left, (1 : T ⟶ D.P.A).left] := by
  funext k
  fin_cases k
  · exact Category.comp_id _
  · show (y ≫ (𝟙 D.P.A * (toUnit D.P.A ≫ D.c 0))).left = y.left
    rw [ThetaOne.c_zero, MonObj.comp_one, _root_.mul_one, Category.comp_id]
  · show (y ≫ toUnit D.P.A ≫ D.c 0).left = (1 : T ⟶ D.P.A).left
    rw [ThetaOne.c_zero, MonObj.comp_one, MonObj.comp_one]
  · show (y ≫ (1 : D.P.A ⟶ D.P.A)).left = (1 : T ⟶ D.P.A).left
    rw [MonObj.comp_one]

theorem prod_famφB_zero {T : Over (Sp V₁)} (y : T ⟶ D.P.A) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k, h (y.left ≫ D.famφB 0 k) ^ DegPre.famε 1 k = h y.left := by
  have e₃ := fun k => congrFun (famφB_zero D y) k
  simp only [e₃, Fin.prod_univ_four]
  simp [DegPre.famε]

theorem value_ne {K : Type} [Field K] (P : PolAV (Sp K)) (s : LB.Sec (LPow P.A P.L 1 (baseOver (Sp K))))
    (x : baseOver (Sp K) ⟶ P.A)
    (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Sp K)).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1)))
    (v : Γ((baseOver (Sp K)).left, ⊤)) (hv : IsValueAt P.A P.L 1 s x τ v) (hv0 : v ≠ 0) (z : Sp K) (j : Fin 1 → P.L.ι)
    (hz : (𝟙 (Sp K) : Sp K ⟶ Sp K) z ∈ LB.wchart P.L (fun _ : Fin 1 => x.left) j) :
    gs (Y := Sp K) (ptSecT P.A x).left z (LB.wchart P.L (fun _ : Fin 1 => (snd (baseOver (Sp K)) P.A).left) j) (s.f j) ≠ 0 := by
  have e := congrArg (gs (𝟙 (Sp K)) z _) (hv j)
  have e₁ := ((gs_res (𝟙 (Sp K)) z _ hz _).trans (gs_pull (𝟙 (Sp K)) _ z _ (val_le P.A P.L x j hz) _)).symm.trans (e.trans
    ((gs_mul _ z _ hz _ _).trans (congrArg₂ (· * ·) (gs_res _ z _ hz _) (gs_unit _ z _ hz _))))
  rw [Category.id_comp] at e₁
  have e₂ := gs_appTop_of_section (𝟙 (Sp K)) (𝟙 _) (Category.id_comp _) z v
  intro h0
  have h2 := (Units.mul_left_eq_zero _).1 (e₁.symm.trans h0)
  have h1 : toStk z ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom v) = 0 := e₂.symm.trans h2
  rw [map_eq_zero] at h1
  exact hv0 ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective (h1.trans (map_zero _).symm))

theorem exists_sec_fibre {K : Type} [Field K] (ev : V₁ →+* K) (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) :
    ∃ θ' : LB.Sec (LPow (GlobalTheory.StrictPull.polPull D.P (spMap ev)).A (GlobalTheory.StrictPull.polPull D.P (spMap ev)).L 1
      (baseOver (Sp K))), ∀ (Z : Scheme.{0}) (m : Z ⟶ (baseOver (Sp K) ⊗ (GlobalTheory.StrictPull.polPull D.P (spMap ev)).A).left)
        (x : Z ⟶ D.P.A.left) (z : Z) J,
      m ≫ (snd (baseOver (Sp K)) (GlobalTheory.StrictPull.polPull D.P (spMap ev)).A).left ≫ pullback.fst D.P.A.hom (spMap ev) = x →
      Good D.P.L z J →
      m z ∈ LB.wchart (GlobalTheory.StrictPull.polPull D.P (spMap ev)).L
        (fun _ : Fin 1 => (snd (baseOver (Sp K)) (GlobalTheory.StrictPull.polPull D.P (spMap ev)).A).left) (fun _ _ => J x) ∧
      gs m z (LB.wchart (GlobalTheory.StrictPull.polPull D.P (spMap ev)).L
        (fun _ : Fin 1 => (snd (baseOver (Sp K)) (GlobalTheory.StrictPull.polPull D.P (spMap ev)).A).left) (fun _ _ => J x))
        (θ'.f (fun _ _ => J x)) = sval θ x z J := by
  let P' := GlobalTheory.StrictPull.polPull D.P (spMap ev)
  let g := pullback.fst D.P.A.hom (spMap ev)
  obtain ⟨θ₁, v₁⟩ := exists_sec D.P.isLB (K' := Fin 1) (φ' := fun _ => 𝟙 D.P.A.left) (ε' := fun _ => (1 : ℤ))
    (fun U _ h => by
      have := prod_famφB_zero D (𝟙 D.P.A) h
      simp only [Over.id_left, Category.id_comp] at this
      rw [this]; simp) θ
  obtain ⟨θ', v'⟩ := exists_chartSec (chartPullLinComb D.P.L g (fun _ : Fin 1 => (snd (baseOver (Sp K)) P'.A).left)
    (fun _ => 𝟙 D.P.A.left) (fun _ => (1 : ℤ)) ((snd (baseOver (Sp K)) P'.A).left ≫ g)
    (fun _ => (Category.comp_id _).symm)) θ₁
  refine ⟨θ', ?_⟩
  rintro Z m _ z J rfl hJ
  have hm : m z ∈ LB.wchart P'.L (fun _ : Fin 1 => (snd (baseOver (Sp K)) P'.A).left)
      (fun _ _ => J (m ≫ (snd (baseOver (Sp K)) P'.A).left ≫ g)) :=
    Set.mem_iInter.2 fun _ => mem_pull.2 (hJ (m ≫ (snd (baseOver (Sp K)) P'.A).left ≫ g))
  refine ⟨hm, (v' Z m z _ hm).trans ?_⟩
  rw [← v₁ _ _ z J hJ]
  exact (sval_of θ₁ _ z J _ (fun _ => by rw [Category.comp_id]; rfl)).symm

set_option maxHeartbeats 400000 in

theorem exists_torsion_ne {K : Type} [Field K] [IsAlgClosed K] (ev : V₁ →+* K)
    (θ : FieldBaseChange.SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (hθ : ∃ j, (ThetaOne.pullTo D ev θ).f j ≠ 0) (N : ℕ) (hN : 2 ≤ N) (hNK : (N : K) ≠ 0) :
    ∃ p : Over.mk (spMap ev) ⟶ D.P.A, p ^ N = 1 ∧ ∀ (z : Sp K) J, Good D.P.L z J →
      sval (Z := Sp K) θ p.left z J ≠ 0 := by
  let P' := GlobalTheory.StrictPull.polPull D.P (spMap ev)
  let g := pullback.fst D.P.A.hom (spMap ev)
  have hg := isGrpPullback_pullback D.P.A (spMap ev)
  obtain ⟨θ', key⟩ := exists_sec_fibre D ev θ
  obtain ⟨x, hx, τ, v, -, hv, hv0⟩ := theta_nonvanish_torsion K P' N hN hNK θ' (fun h0 => by
    obtain ⟨j, hj⟩ := hθ
    have h0' : ∀ i, θ'.f i = 0 := fun i => congrFun (congrArg Subtype.val h0) i
    refine hj (sec_ext_val D.P.isLB (s' := (0 : FieldBaseChange.SecOver
      (fst (Over.mk (Spec.map (CommRingCat.ofHom ev))) D.P.A).left _)) (fun y J hJ => ?_) j)
    rw [FieldBaseChange.sval_zero' hJ]
    refine (FieldBaseChange.sval_pullOver _ _ θ _ hJ).trans ?_
    let T : Over (Sp K) := Over.mk (fst (Over.mk (spMap ev)) D.P.A).left
    let pt : T ⟶ P'.A := Over.homMk (pullback.lift (snd (Over.mk (spMap ev)) D.P.A).left
      (fst (Over.mk (spMap ev)) D.P.A).left ((Over.w (snd (Over.mk (spMap ev)) D.P.A)).trans
        (Over.w (fst (Over.mk (spMap ev)) D.P.A)).symm)) (pullback.lift_snd _ _ _)
    let b : T ⟶ baseOver (Sp K) := Over.homMk T.hom (Category.comp_id _)
    obtain ⟨k1, k2⟩ := key _ (lift b pt).left (𝟙 _ ≫ (snd (Over.mk (spMap ev)) D.P.A).left) y J
      ((Category.assoc _ _ _).symm.trans ((congrArg (fun m => m.left ≫ g) (lift_snd b pt)).trans
        ((pullback.lift_fst _ _ _).trans (Category.id_comp _).symm))) hJ
    refine k2.symm.trans ?_
    refine (congrArg (gs _ y _) (h0' _)).trans ((gs_eq _ _ _ k1 _).trans ?_)
    erw [map_zero, map_zero])
  let r : Over.mk (spMap ev) ⟶ Over.mk ((baseOver (Sp K)).hom ≫ spMap ev) := Over.homMk (𝟙 _) rfl
  have hl : (r ≫ pushHom hg _ x).left = x.left ≫ g := Category.id_comp _
  refine ⟨r ≫ pushHom hg _ x, (MonObj.comp_pow _ _ _).symm.trans ((congrArg (r ≫ ·) ((map_pow (pushHom hg _) x N).symm.trans
      ((congrArg (pushHom hg _) hx).trans (map_one _)))).trans (MonObj.comp_one _)), fun z J hJ => ?_⟩
  rw [hl]
  obtain ⟨k1, k2⟩ := key (Sp K) (ptSecT P'.A x).left (x.left ≫ g) z J
    ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m.left ≫ g) (lift_snd (𝟙 _) x))) hJ
  exact fun h0 => value_ne P' θ' x τ v hv hv0 z (fun _ _ => J (x.left ≫ g))
    (Set.mem_iInter.2 fun _ => mem_pull.2 (hJ (x.left ≫ g))) (k2.trans h0)

end Nonvanishing

section Terms

open GlobalTheory.UT GlobalTheory.UT.SymFrame ReciprocityTheory.ChartRestriction.G.DVR

theorem term_val {V₁ : Type} [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (F : Type) [Field F]
    [Algebra (FractionRing V₁) F] (th : Fam D F 1)
    (θ : FieldBaseChange.SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (lam : F)
    (h : FieldBaseChange.famProj D F 1 0 th = lam • ThetaOne.termF D F 1 0 θ) (χ : D.X) (β : TF (R := V₁) F ⟶ D.P.A)
    (z : (TF (R := V₁) F).left) (J) (hJ : Good D.P.L z J) :
    sval (th.s χ) (lift (𝟙 _) β).left z J = cst F z lam * sval θ (cP D _ χ * β).left z J *
      (@id ((TF (R := V₁) F).left.presheaf.stalk z)ˣ (val (D.psi χ) (jFK (R := V₁) F) z J) *
        (@id ((TF (R := V₁) F).left.presheaf.stalk z)ˣ (val (D.psi 0) (jFK (R := V₁) F) z J))⁻¹).val := by
  have hG := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := F) hG 1 χ 0
  have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (th.fe χ 0 u hu hc) _ (lift (𝟙 _) β).left z J hJ
  have e₀ : ∀ x, x = 0 + 1 • χ → sval (th.s x) (lift (𝟙 _) β).left z J =
      sval (th.s (0 + 1 • χ)) (lift (𝟙 _) β).left z J := by rintro _ rfl; rfl
  refine (e₀ χ (by rw [zero_add, one_smul])).trans (e.trans (congrArg₂ (· * ·) ?_ (congrArg Units.val ?_)))
  · refine (congrArg (fun s : FieldBaseChange.FamTerm D F 1 0 => sval (show LB.Sec _ from s) _ z J) h).trans ?_
    refine (FieldBaseChange.sval_smul' hJ _ lam _).trans (congrArg₂ (· * ·) ?_ ?_)
    · have : ((lift (𝟙 _) β).left ≫ (DegPre.trF D F χ).left) ≫ FieldBaseChange.famBase D F = 𝟙 _ := by
        rw [Category.assoc, FieldBaseChange.trF_famBase]
        exact congrArg (fun m => m.left) (lift_fst (𝟙 (TF (R := V₁) F)) β)
      rw [this]
      rfl
    · refine (FieldBaseChange.sval_pullOver _ _ θ _ hJ).trans (congrArg (fun x => sval θ x z J) ?_)
      show ((lift (𝟙 _) β ≫ DegPre.trF D F χ) ≫ DegPre.prB D F).left = _
      rw [Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, lift_snd, lift_fst_assoc, Category.id_comp, mul_comm]
  · rw [hv u hu hc _ (lift (𝟙 _) β) z J hJ, val_famMult _ hJ, GlobalTheory.TauTwist.val_tau D _ _ _ hJ, lift_fst]
    have c : ∀ x y : TF (R := V₁) F ⟶ D.P.A, DVR.th D z J 1 x y = 1 := (isCub_cubV D.cub hJ).face
    rw [uVal, cubN, Finset.prod_range_one, cPoint_zero, pow_zero, _root_.mul_one, c, c,
      GlobalTheory.RatioVal.val_powGen, GlobalTheory.RatioVal.val_powGen, add_zero, pow_one, pow_one, Over.id_left, Category.id_comp]
    simp only [id]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel

theorem toStk_surj {K : Type} [Field K] (z : Sp K) : Function.Surjective (toStk z) := fun s => by
  obtain ⟨U, hU, a, rfl⟩ := (Sp K).presheaf.germ_exist s
  exact ⟨_, (toStk_valF_gs (𝟙 _) U z hU a).trans (gs_eq _ _ _ hU _)⟩

theorem root_mem {K : Type} [Field K] {k₀ : Subfield K} (hk₀ : IsAlgClosed k₀) {z : Sp K} {s : (Sp K).presheaf.stalk z}
    {n : ℕ} (hn : 1 ≤ n) (h : ∃ c ∈ k₀, s ^ n = toStk z c) : ∃ c ∈ k₀, s = toStk z c := by
  obtain ⟨y, rfl⟩ := toStk_surj z s
  obtain ⟨c, hc, e⟩ := h
  rw [← map_pow] at e
  exact ⟨y, Frames.mem_of_pow_mem k₀ hn ((toStk z).injective e ▸ hc), rfl⟩

theorem prod_mem {K : Type} [Field K] {k₀ : Subfield K} {z : Sp K} {I : Type} (S : Finset I)
    {s : I → ((Sp K).presheaf.stalk z)ˣ} (h : ∀ i, ∃ c ∈ k₀, (s i).val = toStk z c) :
    ∃ c ∈ k₀, (∏ i ∈ S, s i).val = toStk z c := by
  choose c hc e using h
  exact ⟨∏ i ∈ S, c i, k₀.prod_mem fun i _ => hc i, by rw [Units.coe_prod, map_prod]; exact Finset.prod_congr rfl fun i _ => e i⟩

theorem zpow_mem {K : Type} [Field K] {k₀ : Subfield K} {z : Sp K} {s : ((Sp K).presheaf.stalk z)ˣ}
    (h : ∃ c ∈ k₀, s.val = toStk z c) (n : ℤ) : ∃ c ∈ k₀, (s ^ n).val = toStk z c := by
  obtain ⟨c, hc, e⟩ := h
  have h0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at e
    exact s.ne_zero e
  have : s = Units.map (toStk z).toMonoidHom (Units.mk0 c h0) := Units.ext e
  refine ⟨c ^ n, k₀.zpow_mem hc n, ?_⟩
  rw [this, ← map_zpow]
  show toStk z ((Units.mk0 c h0 ^ n).val) = _
  rw [Units.val_zpow_eq_zpow_val]
  rfl

variable {V₁ W₀ K : Type} [CommRing V₁] [IsDomain V₁] [CommRing W₀] [Field K] [IsAlgClosed K] {D : DegPre V₁}
  {B₀ : Over (Sp W₀)} [GrpObj B₀] {f : W₀ →+* V₁} {q : Fin 8 → (D.P.A.left ⟶ B₀.left)} {ev : V₁ →+* K} {k₀ : Subfield K}
  {X₂ : Scheme.{0}} {L₂ : LB X₂} {I : Type} [Fintype I] {π : I → (D.P.A.left ⟶ X₂)} {e : I → ℤ}
  {u : LB.Iso D.P.L (LB.LinComb L₂ π e)}

theorem gs_gen (a : Γ(Sp V₁, ⊤)) (z : (TF (R := V₁) (FractionRing V₁)).left) :
    gs (toUnit (TF (R := V₁) (FractionRing V₁))).left z ⊤ a = cst (FractionRing V₁) z
      (algebraMap V₁ (FractionRing V₁) ((Scheme.ΓSpecIso (CommRingCat.of V₁)).hom.hom a)) := by
  rw [Frames.toUnit_left_eq, GlobalTheory.RatioVal.gs_specMap]
  exact (GlobalTheory.RatioVal.gs_id_const z _).symm

omit [IsDomain V₁] [IsAlgClosed K] in
theorem gs_ev (ev : V₁ →+* K) (a : Γ(Sp V₁, ⊤)) (z : Sp K) :
    gs (Y := Sp K) (toUnit (Over.mk (spMap ev))).left z ⊤ a = toStk z (ev ((Scheme.ΓSpecIso (CommRingCat.of V₁)).hom.hom a)) :=
  GlobalTheory.RatioVal.gs_specMap ev z a

omit [IsAlgClosed K] in

theorem triv_elt (ev : V₁ →+* K) {P v} (G : GRep D.P.L (𝟙_ (Over (Sp V₁))) P v)
    (hP : ∀ (U : Type) [CommGroup U] (h : _ → U), P U h = 1) :
    ∃ a : V₁, (∀ z J, Good D.P.L z J → (v (TF (R := V₁) (FractionRing V₁)) (toUnit _) z J).val =
      cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) a)) ∧
      ∀ (z : Sp K) J, Good D.P.L z J → (v (Over.mk (spMap ev)) (toUnit _) z J).val = toStk z (ev a) := by
  obtain ⟨s, hs, vs⟩ := G.out D.P.isLB (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun U _ h => (hP U h).trans (Fintype.prod_empty _).symm)
  obtain ⟨ρ, hρ⟩ := Geo.Tor.exists_ratio D.P.isLB rfl s (LB.oneGen D.P.L) hs (Frames.oneGen_gen _)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of V₁)).hom.hom ρ.val, fun z J hJ => ?_, fun z J hJ => ?_⟩
  · rw [← vs _ _ z J hJ, hρ _ _ z J hJ, val_one, _root_.mul_one, ← gs_unit _ z ⊤ trivial]
    exact gs_gen _ z
  · rw [← vs (Over.mk (spMap ev)) _ z J hJ, hρ (Over.mk (spMap ev)).left _ z J hJ, val_one, _root_.mul_one]
    exact (gs_unit _ _ ⊤ trivial _).symm.trans (gs_ev ev _ z)

theorem tele {A U : Type} [CommGroup A] [CommGroup U] (h : A → U) (c b : A) (N : ℕ) (hb : b ^ N = 1) :
    ∏ i ∈ Finset.range N, (h (c * b ^ i * b) * (h (c * b ^ i))⁻¹ * (h (c * b))⁻¹ * (h (b ^ i * b))⁻¹ * h c * h (b ^ i) *
      h b * (h 1)⁻¹) = ((h (c * b))⁻¹ * h c * h b * (h 1)⁻¹) ^ N := by
  have hP : ∀ i, h (c * b ^ i * b) * (h (c * b ^ i))⁻¹ * (h (c * b))⁻¹ * (h (b ^ i * b))⁻¹ * h c * h (b ^ i) *
      h b * (h 1)⁻¹ = (h (c * b ^ (i + 1)) / h (b ^ (i + 1))) / (h (c * b ^ i) / h (b ^ i)) *
        ((h (c * b))⁻¹ * h c * h b * (h 1)⁻¹) := by
    intro i
    rw [_root_.mul_assoc c, ← pow_succ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_div]
    abel
  rw [Finset.prod_congr rfl (fun i _ => hP i), Finset.prod_mul_distrib,
    Finset.prod_range_div (fun i => h (c * b ^ i) / h (b ^ i)), Finset.prod_const, Finset.card_range, hb, pow_zero]
  simp

theorem prod_gt {Z : Scheme.{0}} {U : Type} [CommGroup U] (c b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A)
    (h : ((𝟙_ (Over (Sp V₁))).left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 4, h (𝟙 _ ≫ ![(c * b).left, c.left, b.left, (η[D.P.A]).left] k) ^ DegPre.gtε k =
      (h (c * b).left)⁻¹ * h c.left * h b.left * (h (1 : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four, ← SymFrame.eta_eq]
  simp [DegPre.gtε, zpow_neg, zpow_one]

theorem prod_ln {U : Type} [CommGroup U] (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A)
    (h : ((𝟙_ (Over (Sp V₁))).left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 2, h (𝟙 _ ≫ ![(η[D.P.A]).left, b.left] k) ^ DegPre.lineε 1 k =
      h (1 : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A).left * (h b.left)⁻¹ := by
  rw [Fin.prod_univ_two, ← SymFrame.eta_eq]
  simp [DegPre.lineε, zpow_neg, zpow_one]

theorem char_mem [IsIntegrallyClosed V₁] (H : Desc f q ev k₀ u) {N : ℕ} (hN : 1 ≤ N)
    (htor : ∀ x : Over.mk (spMap ev) ⟶ D.P.A, x ^ N = 1 → RatP q k₀ x.left)
    (g : GtPtF D (FractionRing V₁)) (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A)
    (hgb : g.b = toUnit _ ≫ b) (ho : ∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) (χ : D.X)
    (hχ : RatP q k₀ (toUnit (Over.mk (spMap ev)) ≫ D.c χ).left)
    (t : LB.Gen (LB.LinComb D.P.L ![(D.c χ * b).left, (D.c χ).left, b.left, (η[D.P.A]).left] DegPre.gtε))
    (ht : t.IsGen) :
    ∃ a : V₁ˣ, (∀ z J, Good D.P.L z J → (val (g.s χ) (𝟙 _) z J).val =
      cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) a) *
        (val t (toUnit (TF (R := V₁) (FractionRing V₁))).left z J).val) ∧
      ∀ (z : Sp K) J J₂, Good D.P.L z J → Good L₂ z J₂ → ∃ c ∈ k₀, toStk z (ev a) *
        ((om (Z := Sp K) u z J J₂ (toUnit (Over.mk (spMap ev)) ≫ (D.c χ * b)).left)⁻¹ *
          om (Z := Sp K) u z J J₂ (toUnit (Over.mk (spMap ev)) ≫ D.c χ).left *
          om (Z := Sp K) u z J J₂ (toUnit (Over.mk (spMap ev)) ≫ b).left *
          (om (Z := Sp K) u z J J₂ (1 : Over.mk (spMap ev) ⟶ D.P.A).left)⁻¹ *
          val (Z := Sp K) t (toUnit (Over.mk (spMap ev))).left z J).val = toStk z c := by
  obtain ⟨a, ha, hrel⟩ := Frames.char_unit hN g b hgb ho χ t ht
  have hbN := (Frames.torsion_of_nsmul g b hgb ho).2
  refine ⟨a, ha, fun z J J₂ hJ hJ₂ => root_mem H.hk₀ hN ?_⟩
  obtain ⟨p, hp, hp'⟩ := triv_elt ev ((Frames.grep_cubProd (D.c χ) b N).mul ((grep_gen t ht (𝟙 _)).pow N).inv)
    (fun U _ h => by
      rw [prod_gt (Z := Sp K), tele (fun x : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A => h x.left) _ _ N hbN, mul_inv_cancel])
  have pa : p = (a : V₁) ^ N := by
    obtain ⟨y⟩ := CoefBasic.exists_pt (R := V₁) (F := FractionRing V₁)
    obtain ⟨I, hI⟩ := CoefBasic.exists_good' D.P.isLB y
    have e₁ := hp y I hI
    simp only [Category.comp_id] at e₁
    rw [Units.val_mul, hrel y I hI, _root_.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, _root_.mul_one,
      CoefBasic.cst_eq, CoefBasic.cst_eq, ← map_pow, ← map_pow] at e₁
    exact (IsFractionRing.injective V₁ (FractionRing V₁) (CoefBasic.cstH_inj y e₁)).symm
  have hb' : (toUnit (Over.mk (spMap ev)) ≫ b) ^ N = 1 := by rw [← MonObj.comp_pow, hbN, MonObj.comp_one]
  obtain ⟨c, hc, ec⟩ := prod_mem (Finset.range N) (fun i => cub_mem H (toUnit _ ≫ D.c χ) ((toUnit _ ≫ b) ^ i) (toUnit _ ≫ b) hχ
    (htor _ (by rw [← pow_mul, mul_comm, pow_mul, hb', one_pow])) (htor _ hb') z J J₂ hJ hJ₂)
  refine ⟨c, hc, Eq.trans ?_ ec⟩
  have e₂ := hp' z J hJ
  simp only [Category.comp_id, MonObj.comp_pow] at e₂
  rw [Finset.prod_mul_distrib, tele (fun x : Over.mk (spMap ev) ⟶ D.P.A => om (Z := Sp K) u z J J₂ x.left) _ _ N hb',
    mul_pow, ← map_pow, ← map_pow, ← pa, ← e₂, MonObj.comp_mul, ← Units.val_pow_eq_pow_val]
  refine (Units.val_mul _ _).symm.trans (congrArg Units.val ?_)
  simp only [id, mul_pow]
  exact (mul_left_comm _ _ _).trans (congrArg₂ (· * ·) rfl (inv_mul_cancel_right _ _))

theorem frame_mem [IsNoetherianRing V₁] [IsIntegrallyClosed V₁] (H : Desc f q ev k₀ u) {N : ℕ} (hN : 1 ≤ N)
    (htor : ∀ x : Over.mk (spMap ev) ⟶ D.P.A, x ^ N = 1 → RatP q k₀ x.left)
    (g : GtPtF D (FractionRing V₁)) (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A)
    (hgb : g.b = toUnit _ ≫ b) (ho : ∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) (w : Frm D (FractionRing V₁) 1 g.b)
    (hw : w.IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ z J, Good D.P.L z J →
      val w (𝟙 _) z J ^ (N ^ 2) * val κ g.b.left z J = 1)
    (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))) (ht : t.IsGen) :
    ∃ a : V₁ˣ, (∀ z J, Good D.P.L z J → (val w (𝟙 _) z J).val =
      cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) a) *
        (val t (toUnit (TF (R := V₁) (FractionRing V₁))).left z J).val) ∧
      ∀ (z : Sp K) J J₂, Good D.P.L z J → Good L₂ z J₂ → ∃ c ∈ k₀, toStk z (ev a) *
        (om (Z := Sp K) u z J J₂ (1 : Over.mk (spMap ev) ⟶ D.P.A).left *
          (om (Z := Sp K) u z J J₂ (toUnit (Over.mk (spMap ev)) ≫ b).left)⁻¹ *
          val (Z := Sp K) t (toUnit (Over.mk (spMap ev))).left z J).val = toStk z c := by
  obtain ⟨a, ha, hrel⟩ := Frames.frame_unit hN g b hgb ho w hw t ht
  have hbN := (Frames.torsion_of_nsmul g b hgb ho).2
  obtain ⟨κ, hκ⟩ := exists_kap (D := D) GlobalTheory.abelianSchemeLaws_all.1.mulPull N
  refine ⟨a, ha, fun z J J₂ hJ hJ₂ => root_mem H.hk₀ (n := N ^ 2) (Nat.one_le_pow _ _ (by omega)) ?_⟩
  have alg : ∀ {U : Type} [CommGroup U] (o x : U), (o * x⁻¹) ^ (N ^ 2) *
      (x ^ ((N : ℤ) ^ 2) * o⁻¹ * o ^ (1 - (N : ℤ) ^ 2)) = 1 := fun o x => by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
    rw [← natCast_zsmul]
    push_cast
    module
  obtain ⟨p, hp, hp'⟩ := triv_elt ev (((grep_gen t ht (𝟙 _)).pow (N ^ 2)).mul (grep_kap κ hκ.1 b))
    (fun U _ h => by rw [prod_ln, hbN]; exact alg _ _)
  have pa : (a : V₁) ^ (N ^ 2) * p = 1 := by
    obtain ⟨y⟩ := CoefBasic.exists_pt (R := V₁) (F := FractionRing V₁)
    obtain ⟨I, hI⟩ := CoefBasic.exists_good' D.P.isLB y
    have e₁ := hp y I hI
    simp only [Category.comp_id] at e₁
    have e₂ := hrel κ hκ y I hI
    rw [hgb, mul_comm (val κ _ _ _), e₁, CoefBasic.cst_eq, CoefBasic.cst_eq, ← map_pow, ← map_pow, ← map_mul, ← map_mul,
      ← map_one (CoefBasic.cstH y), ← map_one (algebraMap V₁ (FractionRing V₁))] at e₂
    exact IsFractionRing.injective V₁ (FractionRing V₁) (CoefBasic.cstH_inj y e₂)
  have hb' : (toUnit (Over.mk (spMap ev)) ≫ b) ^ N = 1 := by rw [← MonObj.comp_pow, hbN, MonObj.comp_one]
  obtain ⟨c, hc, ec⟩ := zpow_mem (kap_mem H κ hκ _ (htor _ hb') z J J₂ hJ hJ₂) (-1)
  refine ⟨c, hc, Eq.trans ?_ ec⟩
  have e₂ := hp' z J hJ
  simp only [Category.comp_id] at e₂
  rw [hb', zpow_neg_one]
  refine Units.eq_inv_of_mul_eq_one_right ?_
  have e₃ := congrArg Units.val (alg (om (Z := Sp K) u z J J₂ (1 : Over.mk (spMap ev) ⟶ D.P.A).left)
    (om (Z := Sp K) u z J J₂ (toUnit (Over.mk (spMap ev)) ≫ b).left))
  have e₄ : toStk z (ev a) ^ (N ^ 2) * toStk z (ev p) = 1 := by rw [← map_pow, ← map_pow, ← map_mul, ← map_mul, pa, map_one, map_one]
  have e₅ : (val (Z := Sp K) t (toUnit (Over.mk (spMap ev))).left z J ^ (N ^ 2) *
    val (Z := Sp K) κ (toUnit (Over.mk (spMap ev)) ≫ b).left z J).val = toStk z (ev p) := e₂
  rw [← e₅] at e₄
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, mul_pow, Units.val_one] at e₃ e₄ ⊢
  linear_combination e₄ + (toStk z (ev a) ^ (N ^ 2) * (val (Z := Sp K) t (toUnit (Over.mk (spMap ev))).left z J).val ^ (N ^ 2) *
    (val (Z := Sp K) κ (toUnit (Over.mk (spMap ev)) ≫ b).left z J).val) * e₃

end Terms

end GlobalTheory.Poinc.Sep.Coef
