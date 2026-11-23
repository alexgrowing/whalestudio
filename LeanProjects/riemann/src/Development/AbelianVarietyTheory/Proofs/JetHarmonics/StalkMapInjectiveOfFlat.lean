import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEInst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullLin

theorem stalkMap_injective_of_flat {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] (x : X) :
    Function.Injective (f.stalkMap x).hom := by
  have h := Flat.stalkMap f x
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

theorem sec_eq_zero_of_flat {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (f : Y' ⟶ Y) [Flat f] [Surjective f]
    (h : ∀ x J, Good L x J → sval s f x J = 0) (j : K → L.ι) : s.f j = 0 := by
  refine fn_ext fun y hy => ?_
  obtain ⟨x, rfl⟩ := f.surjective y
  apply stalkMap_injective_of_flat f x
  choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ x)
  refine (gs_stalkMap f x _ hy _).symm.trans (Eq.trans ?_ (gs_stalkMap f x _ hy _))
  refine (sec_trans s f x hy (Good.mem hJ φ f)).trans ?_
  refine (congrArg _ (h x J hJ)).trans ((mul_zero _).trans ?_)
  rw [gs_eq f x _ hy, map_zero, map_zero]

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem aF_fst (oa : D.toPre.OAct O) (a : O) :
    (aF D F oa a).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left :=
  congrArg (fun q => q.left) (lift_fst (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a))

theorem aF_snd (oa : D.toPre.OAct O) (a : O) :
    (aF D F oa a).left ≫ (DegPre.prB D.toPre F).left = (DegPre.prB D.toPre F).left ≫ (oa.onB.act a).left :=
  congrArg (fun q => q.left) (lift_snd (fst _ _) (DegPre.prB D.toPre F ≫ oa.onB.act a))

theorem isPullback_aF (oa : D.toPre.OAct O) (a : O) :
    IsPullback (aF D F oa a).left (DegPre.prB D.toPre F).left (DegPre.prB D.toPre F).left (oa.onB.act a).left := by
  have h₀ : IsPullback (fst (TF (R := V) F) D.toPre.P.A).left (DegPre.prB D.toPre F).left
      (TF (R := V) F).hom D.toPre.P.A.hom := IsPullback.of_hasPullback _ _
  refine IsPullback.of_right ?_ (aF_snd oa a) h₀
  rw [aF_fst, Over.w]
  exact h₀

theorem aF_mul (oa : D.toPre.OAct O) (a b : O) : aF D F oa (a * b) = aF D F oa b ≫ aF D F oa a := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [aF]
  · simp [aF, DegPre.prB, oa.onB.map_mul]

theorem pullAl_val (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (χ : D.toPre.X)
    {u u' : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))} (hu : u.IsGen) (hu' : u'.IsGen)
    {K : Type} [Fintype K] {φ : K → ((TF (R := V) F).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb D.toPre.P.L φ ε)}
    (c : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left) t)
    (c' : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u' (DegPre.zF D.toPre F).left) t)
    (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J) (hJ : Good D.toPre.P.L z J) :
    val u r z J = val u' r z J := by
  have z₁ : DegPre.zF D.toPre F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  refine gen_unique' D.toPre.P.isLB (fun _ _ _ => rfl) (fst (TF (R := V) F) D.toPre.P.A).left
    (DegPre.zF D.toPre F).left (congrArg (fun q => q.left) z₁) (surj_appTop D.toPre F hG) hu hu'
    (fun y I hI => ?_) Z r z J hJ
  have a₁ := val_corr hI c (𝟙 _)
  have a₂ := val_corr hI c' (𝟙 _)
  rw [val_pull hI, Category.id_comp] at a₁ a₂
  exact a₁.trans a₂.symm

theorem pullAl_unique (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) {s : Fam D.toPre F k}
    {t t' : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s t) (h' : PullAl D F oa a k N s t') : t = t' := by
  refine fam_ext fun β j => ?_
  by_cases hβ : ∃ χ, β = star a • χ
  · obtain ⟨χ, rfl⟩ := hβ
    obtain ⟨u, hu, c, e⟩ := h.1 χ
    obtain ⟨u', hu', c', e'⟩ := h'.1 χ
    refine sec_ext_val D.toPre.P.isLB (fun y J hJ => ?_) j
    rw [(secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ _ y J hJ,
      (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u').1 e' _ _ y J hJ,
      pullAl_val hG oa a k N χ hu hu' c c' _ _ y J hJ]
  · exact (h.2 β (fun χ e => hβ ⟨χ, e⟩) j).trans (h'.2 β (fun χ e => hβ ⟨χ, e⟩) j).symm

theorem pullAl_add (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) {s s' : Fam D.toPre F k}
    {t t' : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s t) (h' : PullAl D F oa a k N s' t') :
    PullAl D F oa a k N (s + s') (t + t') := by
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, c, e⟩ := h.1 χ
    obtain ⟨u', hu', c', e'⟩ := h'.1 χ
    refine ⟨u, hu, c, (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_⟩
    rw [sval_add _ _ _ _ y hJ, sval_add _ _ _ _ y hJ,
      (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ _ y J hJ,
      (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u').1 e' _ _ y J hJ,
      pullAl_val hG oa a k N χ hu' hu c' c _ _ y J hJ, add_mul]
  · rw [add_f, h.2 β hβ j, h'.2 β hβ j, add_zero]

theorem pullAl_smul (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (ζ : F) {s : Fam D.toPre F k}
    {t : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s t) : PullAl D F oa a k N (ζ • s) (ζ • t) := by
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, c, e⟩ := h.1 χ
    refine ⟨u, hu, c, (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_⟩
    rw [sval_smul _ _ _ _ y hJ, sval_smul _ _ _ _ y hJ,
      (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ _ y J hJ, Category.assoc, aF_fst, _root_.mul_assoc]
  · rw [smul_f, h.2 β hβ j, mul_zero]

theorem eq_zero_of_pullAl_zero (hM : MulNSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (hN : 1 ≤ N)
    (haa : a * star a = (N : O)) {s : Fam D.toPre F k} (h : PullAl D F oa a k N s 0) : s = 0 := by
  obtain ⟨-, hflat, hsurj, -⟩ := hM _ D.toPre.P N hN
  have hm : oa.onB.act (a * star a) = mulA D.toPre.P.A N := by
    rw [haa, ← _root_.mul_one (N : O), act_nsmul, oa.onB.map_one]
  rw [← hm] at hflat hsurj
  have hp := isPullback_aF (F := F) oa (a * star a)
  have : Flat (aF D F oa (a * star a)).left := MorphismProperty.of_isPullback hp.flip hflat
  have : Surjective (aF D F oa (a * star a)).left := MorphismProperty.of_isPullback hp.flip hsurj
  refine fam_ext fun χ j => sec_eq_zero_of_flat D.toPre.P.isLB (s.s χ) (aF D F oa (a * star a)).left
    (fun x J hJ => ?_) j
  obtain ⟨u, -, -, e⟩ := h.1 χ
  have e₁ := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ (aF D F oa (star a)).left x J hJ
  have e₀ : sval ((0 : Fam D.toPre F (k * N)).s (star a • χ)) (aF D F oa (star a)).left x J = 0 :=
    gs_zero _ x _ (hJ.mem _ _)
  rw [e₀, ← Over.comp_left, ← aF_mul] at e₁
  exact (Units.mul_left_eq_zero _).1 e₁.symm

theorem exists_pull_linearMap : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [CommRing O]
    [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O), TraceFormTwistIso D.toPre oa w0 →
    ∀ (a : O) (N k : ℕ), 1 ≤ N → 1 ≤ k → a * star a = (N : O) →
    ∃ π : Fam D.toPre F k →ₗ[F] Fam D.toPre F (k * N), Function.Injective π ∧
      ∀ s s', PullAl D F oa a k N s s' ↔ s' = π s := by
  intro hL V _ _ _ D F _ _ O _ _ _ oa w0 hw a N k hN _ haa
  have hG := hL.globalFns
  obtain ⟨uΨ, huΨ, -⟩ := id hw
  choose P hP using fun s : Fam D.toPre F k => exists_pullAl D F D.toPre.P.isLB oa w0 uΨ huΨ a N haa hN k s
    (pullSecs_fe' D F hG D.toPre.P.isLB oa w0 hw uΨ huΨ a N haa hN k s)
  let π : Fam D.toPre F k →ₗ[F] Fam D.toPre F (k * N) :=
    { toFun := P
      map_add' := fun s s' => pullAl_unique hG oa a k N (hP _) (pullAl_add hG oa a k N (hP s) (hP s'))
      map_smul' := fun ζ s => pullAl_unique hG oa a k N (hP _) (pullAl_smul oa a k N ζ (hP s)) }
  refine ⟨π, (injective_iff_map_eq_zero π).2 fun s hs => ?_, fun s s' =>
    ⟨fun h => pullAl_unique hG oa a k N h (hP s), fun h => h ▸ hP s⟩⟩
  exact eq_zero_of_pullAl_zero hL.mulN oa a k N hN haa (hs ▸ hP s)

end GlobalTheory.PullLin
