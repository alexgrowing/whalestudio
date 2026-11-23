import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CoeffDofSubMem
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SurjectiveAppTop
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharacterEqWeilPairing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralExpansionsOfValuationGeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToFSurjectiveFractionRing
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.TopLePreimageWchart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FnEigenEquationOfForallGeometricPointStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLiftPointTranslationFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EigenEquationTranslationKernelGenericFibreStatement

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory GlobalTheory.FamGerm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenGerm

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt FB FGLaw ev pt Dof)
open GlobalTheory.FieldBaseChange (constVal constVal_specMap gs_scal)
open GlobalTheory.JetSer (fnVal IsSer1)

theorem gs_comp_eq_constVal {A : Type} [CommRing A] {X Z : Scheme.{0}} (e : Z ⟶ Spec (CommRingCat.of A))
    (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (a : Γ(X, U)) (z : Z) :
    gs (e ≫ p) z U a = constVal e z (fnVal p U a) := by
  rw [fnVal, dif_pos h, constVal]
  have i : ∀ b, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom b) = b :=
    fun b => congrArg (fun q => q.hom b) (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id
  rw [i]
  exact (gs_pull e p z U (h trivial) a).symm.trans (gs_res e z h trivial _).symm

theorem dof_of_tangent (hJ : JetSer.JetAlgSt) (hRep : JetSer.RepSt) (hSer : JetSer.SerSt) {V O : Type} [CommRing V]
    [IsLocalRing V] [CommRing O] (β : V →+* O) (I : Ideal O)
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] {d : ℕ} {x : JetSer.Fam G (Fin d)} (hx : Chart.IsUnivChart G d x)
    (Gl : FGLaw V d) (hGl : JetSer.IsLawOf x Gl.F) {U : G.left.Opens} (hU : ⊤ ≤ η[G].left ⁻¹ᵁ U) {l : ℕ}
    (s : Fin l → Γ(G.left, U)) (S : Fin l → PS V 1 d) (hS : ∀ i, IsSer1 x U (s i) (S i)) (c : Fin l → O)
    {Z : Over (Spec (CommRingCat.of O))} (jZ : Z.left ⟶ G.left)
    (hj : jZ ≫ G.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom β)) (k : Γ(Z.left, ⊤))
    (hall : ∀ (T : Over (Spec (CommRingCat.of V))) (q : T.left ⟶ Z.left) (r g : T ⟶ G), g.left = q ≫ jZ →
      ∀ z : T.left, r.left z ∈ U → (r * g).left z ∈ U →
      ∑ i, constVal (q ≫ Z.hom) z (c i) * gs (r * g).left z U (s i) =
        gs q z ⊤ k * ∑ i, constVal (q ≫ Z.hom) z (c i) * gs r.left z U (s i))
    (e : Fin d → O) (yy : O) (w : Pdiv.specO O (DualNumber (O ⧸ I)) ⟶ Z)
    (φ : Chart.JetR V (Fin d) 1 →+* DualNumber (O ⧸ I))
    (hφ : ∀ i, φ (Chart.zR 1 i) = TrivSqZeroExt.inr (Ideal.Quotient.mk I (e i)))
    (hw : w.left ≫ jZ = Spec.map (CommRingCat.ofHom φ) ≫ (x 1).left)
    (hk : fnVal w.left ⊤ k = 1 + TrivSqZeroExt.inr (Ideal.Quotient.mk I yy)) :
    Dof (fun i => MvPowerSeries.map ((Ideal.Quotient.mk I).comp β) (Gl.F i)) (fun i => Ideal.Quotient.mk I (e i))
        (MvPowerSeries.map (Ideal.Quotient.mk I) (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.map β (S i))) =
      MvPowerSeries.C (Ideal.Quotient.mk I yy) *
        MvPowerSeries.map (Ideal.Quotient.mk I) (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.map β (S i)) := by
  letI : Algebra V (O ⧸ I) := ((Ideal.Quotient.mk I).comp β).toAlgebra
  have hc : φ.comp (algebraMap V _) = (algebraMap O (DualNumber (O ⧸ I))).comp β := by
    have h₁ : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap V _)) =
        Spec.map (CommRingCat.ofHom (algebraMap O (DualNumber (O ⧸ I)))) ≫ Spec.map (CommRingCat.ofHom β) := by
      have a₁ : (x 1).left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap V _)) := Over.w (x 1)
      have a₂ : w.left ≫ Z.hom = Spec.map (CommRingCat.ofHom (algebraMap O (DualNumber (O ⧸ I)))) := Over.w w
      rw [← a₁, ← a₂, ← Category.assoc, ← hw, Category.assoc, Category.assoc, hj]
    rw [← Spec.map_comp, ← Spec.map_comp] at h₁
    exact congrArg (fun q => q.hom) (Spec.map_injective h₁)
  let φ' : Chart.JetR V (Fin d) 1 →ₐ[V] DualNumber (O ⧸ I) := { φ with commutes' := fun v => RingHom.congr_fun hc v }
  have e₀ : MvPowerSeries.map (Ideal.Quotient.mk I) (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.map β (S i)) =
      ∑ i, MvPowerSeries.C (Ideal.Quotient.mk I (c i)) * MvPowerSeries.map (algebraMap V (O ⧸ I)) (S i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPowerSeries.map_C]
    congr 1
  rw [e₀]
  refine dof_baseChange hJ hRep hSer hx Gl hGl hU s S hS _ _ _ φ' hφ fun A _ _ θ r h₁ h₂ => ?_
  refine JetSer.FBOf.eq_of_germ fun z => ?_
  have H := hall (Chart.sp (R₀ := V) A) (Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ w.left) r
    (Chart.spMap θ ≫ Chart.spMap φ' ≫ x 1) (by rw [Category.assoc, hw]; rfl) z (h₁ trivial) (h₂ trivial)
  let Φ := ((Spec (CommRingCat.of A)).presheaf.germ ⊤ z trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have c₀ : ∀ b, constVal (𝟙 (Spec (CommRingCat.of A))) z b = Φ b := fun b => gs_eq _ z ⊤ trivial _
  have c₁ : ∀ o, constVal ((Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ w.left) ≫ Z.hom) z o =
      Φ (θ (TrivSqZeroExt.inl (Ideal.Quotient.mk I o))) := fun o => by
    have a₂ : w.left ≫ Z.hom = Spec.map (CommRingCat.ofHom (algebraMap O (DualNumber (O ⧸ I)))) := Over.w w
    rw [Category.assoc, a₂, constVal_specMap, ← Category.id_comp (Spec.map _), constVal_specMap, c₀]
    rfl
  have c₂ : gs (Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ w.left) z ⊤ k =
      Φ (θ (1 + TrivSqZeroExt.inr (Ideal.Quotient.mk I yy))) := by
    rw [gs_comp_eq_constVal _ _ ⊤ le_top, hk, ← Category.id_comp (Spec.map _), constVal_specMap, c₀]
    rfl
  have c₃ := fun i => PullGerm.gs_eq_germ_fnVal _ U h₁ (s i) z
  have c₄ := fun i => PullGerm.gs_eq_germ_fnVal _ U h₂ (s i) z
  show Φ _ = Φ _
  rw [map_mul, map_sum, map_sum, ← c₂]
  simp only [map_mul, ← c₁]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => congrArg _ (c₄ i).symm) (H.trans ?_)
  exact congrArg _ (Finset.sum_congr rfl fun i _ => congrArg _ (c₃ i))

theorem comp_map_eq_one {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] (a : G ⟶ G) {T : Over S'}
    (x : T ⟶ (Over.pullback f).obj G)
    (h : (x.left ≫ pullback.fst G.hom f) ≫ a.left = (x.left ≫ pullback.fst G.hom f) ≫ (1 : G ⟶ G).left) :
    x ≫ (Over.pullback f).map a = 1 := by
  let P := pushHom (isGrpPullback_pullback G f) T
  have e : P (x ≫ (Over.pullback f).map a) = P 1 := by
    rw [map_one, ← MonObj.comp_one (P x)]
    apply Over.OverMorphism.ext
    refine Eq.trans ?_ h
    show (x.left ≫ ((Over.pullback f).map a).left) ≫ pullback.fst G.hom f = _
    rw [Category.assoc, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg (fun q => q.left) e
  · exact (Over.w _).trans (Over.w _).symm

theorem gs_div_mul {X Z : Scheme.{0}} {L : LB X} (f : X ⟶ X) {N q : ℕ} (k : ℕ) (j : L.ι)
    (mu : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), -1])) (σ : H0 L q)
    (hle : LB.wchart L ![𝟙 X, f] (fun _ => j) ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j))
    (m : Γ(X, LB.wchart L ![𝟙 X, f] (fun _ => j))ˣ) (hm : m = mu.s (fun _ => j))
    (s : Γ(X, LB.wchart L ![𝟙 X, f] (fun _ => j)))
    (hs : s * m.val ^ k = (X.presheaf.map (homOfLE hle).op).hom (σ.f (fun _ => j)))
    (ψ : Z ⟶ X) (z : Z) (hz : ψ z ∈ LB.wchart L ![𝟙 X, f] (fun _ => j)) {J : (Z ⟶ X) → L.ι}
    (hJ : ∀ χ : Z ⟶ X, χ z ∈ L.U j → J χ = j) :
    sval σ ψ z J = gs ψ z (LB.wchart L ![𝟙 X, f] (fun _ => j)) s * (val mu ψ z J).val ^ k := by
  rw [sval_of σ ψ z J (fun _ => j) fun i => hJ _ (Set.mem_iInter.1 (hle hz) i),
    val_of mu ψ z J (fun _ => j) fun i => hJ _ (Set.mem_iInter.1 hz i), ← hm]
  refine (gs_res ψ z hle hz _).symm.trans ((congrArg (gs ψ z _) hs.symm).trans ?_)
  rw [gs_mul ψ z _ hz, ← Units.val_pow_eq_pow_val, gs_unit ψ z _ hz, map_pow, Units.val_pow_eq_pow_val]

theorem solve_germ {A : Type} [CommRing A] {f W R R' M K K' E E' S : A} {k p : ℕ} (hM : IsUnit M)
    (h₁ : W * R ^ p = K * M * E) (hR : R * R' = 1) (hE : E * E' = 1) (hK : K * K' = 1)
    (h₂ : f * W ^ k = S * (M ^ k * R' ^ (k * p))) : f = K' ^ k * S * E' ^ k := by
  have a₁ : f * (K * E) ^ k * M ^ k = S * M ^ k := by
    have b₁ : (W * R ^ p) ^ k = (K * M * E) ^ k := by rw [h₁]
    have b₂ : (R * R') ^ (k * p) = 1 := by rw [hR, one_pow]
    rw [mul_pow, ← pow_mul, mul_comm p k] at b₁
    rw [mul_pow] at b₂
    calc f * (K * E) ^ k * M ^ k = f * (K * M * E) ^ k := by ring
      _ = f * W ^ k * R ^ (k * p) := by rw [← b₁]; ring
      _ = S * M ^ k * (R ^ (k * p) * R' ^ (k * p)) := by rw [h₂]; ring
      _ = _ := by rw [b₂, _root_.mul_one]
  have a₂ := (hM.pow k).mul_right_cancel a₁
  have a₃ : (K * K' * (E * E')) ^ k = 1 := by rw [hK, hE, _root_.mul_one, one_pow]
  calc f = f * (K * K' * (E * E')) ^ k := by rw [a₃, _root_.mul_one]
    _ = _ := by rw [← a₂]; ring

theorem eigen_at_field_points (hL : Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {t : SAB H (Sp V)} (P : PELUnif (maximalIdeal V) t)
    (F : Type) [Field F] [Algebra (FractionRing V) F] (a : 𝓞 E) {N k : ℕ} (hN : 1 ≤ N) (hk : 4 ≤ k)
    (ha : letI := H.starRing; a * star a = (N : 𝓞 E))
    (mu : LB.Gen (LB.LinComb P.U.LG.L (K := Fin 2) ![𝟙 t.G.left, (t.act.act a).left] ![(N : ℤ), -1])) (hmu : mu.IsGen)
    (hn : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of V)) (z : Z) (J), Good P.U.LG.L z J →
      val mu (r ≫ eSec t.G) z J = val (GeneratorPullback.powGen P.U.LG.L _ _ P.U.LG.rig (N - 1)) r z J)
    (pt : QkPt P.D.toPre F (k * N)) (b : TFK (R := V) F ⟶ P.A.A) (hb : P.ToA F (k * N) pt b)
    (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F pt.g.b) (DegPre.lineε (k * N)))) (hw : w.IsGen)
    (s : Fam P.D.toPre F k) (s' t' : Fam P.D.toPre F (k * N))
    (hP : letI := H.starRing; PullAl P.D F P.oD a k N s s') (hΦ : PhiRel P.D.toPre F (k * N) pt w s' t')
    {l : ℕ} (c : Fin l → F) (σ : Fin l → H0 P.U.LG.L (k * N)) (f : Fin l → ∀ α, P.D.toPre.SecB (k * N) α)
    (hσ : ∀ i e, P.U.ExpandsAt e (k * N) (σ i) (f i))
    (hlin : ∀ α, GeneratorPullback.SecLin P.D.toPre.P.L (DegPre.famφ P.D.toPre F α) (DegPre.famε (k * N)) (t'.s α)
      (P.D.toPre.famφB α) (DegPre.famε (k * N)) (fun i => f i α) (DegPre.prB P.D.toPre F).left
      (fun i => scal (fst (TF (R := V) F) P.D.toPre.P.A).left (c i)))
    (z₀ : TFK (R := V) F ⟶ P.A.A) (ε : Fˣ) (hz₀ : letI := H.starRing; z₀ ≫ P.oA.act a = 1)
    (hW : WeilIs P.A.A P.A.L ((k * N : ℕ) : ℤ) z₀ b (unitOn ε))
    (T : Over (Spec (CommRingCat.of V))) (e : T.left ⟶ Spec (CommRingCat.of F)) (r g : T ⟶ t.G)
    (hg : g.left = e ≫ (z₀ ≫ P.U.gen.inv).left ≫ pullback.fst t.G.hom (jK V)) (z : T.left) (J)
    (hJ : Good P.U.LG.L z J) :
    (∑ i, constVal e z (c i) * sval (σ i) (r * g).left z J) * (val mu r.left z J).val ^ k =
      constVal e z (ε : F) *
        ((∑ i, constVal e z (c i) * sval (σ i) r.left z J) * (val mu (r * g).left z J).val ^ k) := by
  let _ := H.starRing
  have hG := hL.globalFns
  have hLB := P.U.LG.isLB
  have hk₁ : 1 ≤ k := by omega
  have hq : 1 ≤ k * N := Nat.mul_pos hk₁ hN
  obtain ⟨u, hu, hc, vu⟩ := PullGerm.exists_generic P.U.LG (t.act.act a) N k mu hmu hn
  obtain ⟨wI, hwI⟩ := P.U.ext
  obtain ⟨θ, rfl, hθ⟩ := ThetaTranslate.exists_theta_actVal P.U F hG hL.kerPow hq pt b hb wI hwI w hw
  obtain ⟨σ₀, hσ₀⟩ := ((FieldBaseChange.expandsG_bijective P.U.toUnifPre F hG hk₁ (P.U.expand k hk₁)).2 s).exists
  have g₂ := (FieldBaseChange.expandsG_bijective P.U.toUnifPre F hG hq (P.U.expand _ hq)).2
  have f₂ := (FieldBaseChange.expandsF_bijective P.U.toUnifPre F hG hq (P.U.expand _ hq) hwI).2
  have e₁ : (TFK (R := V) F ◁ (Over.pullback (jK V)).map (t.act.act a)).left ≫ UnifPre.gFK (G := t.G) F =
      UnifPre.gFK (G := t.G) F ≫ (t.act.act a).left := by
    rw [← Category.assoc, ← Over.comp_left, whiskerLeft_snd, Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have hpow := DVR.pullGen_isGen _ _ _ _ (FrameGeo.powGen_isGen _ _ _ _ hmu k) (UnifPre.gFK (G := t.G) F)
  obtain ⟨σ', hσ'⟩ := exists_sec hLB (φ' := fun _ : Fin 1 => UnifPre.gFK (G := t.G) F)
    (ε' := fun _ => ((k * N : ℕ) : ℤ)) (fun W _ g => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
        Finset.prod_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, mul_neg, _root_.mul_one, zpow_neg,
        Category.comp_id, Nat.cast_mul, e₁]
      rw [mul_left_comm, mul_inv_cancel, _root_.mul_one])
    (pullMulSec σ₀ (TFK (R := V) F ◁ (Over.pullback (jK V)).map (t.act.act a)).left _ hpow)
  have v' : ∀ (y : (UnifPre.GF (G := t.G) F).left) (J), Good P.U.LG.L y J → sval σ' (𝟙 _) y J =
      sval σ₀ (TFK (R := V) F ◁ (Over.pullback (jK V)).map (t.act.act a)).left y J *
        (val mu (UnifPre.gFK (G := t.G) F) y J).val ^ k := fun y J hJ => by
    refine (hσ' _ _ y J hJ).trans ((sval_pullMulSec _ _ _ hpow _ y hJ).trans ?_)
    rw [val_pull hJ, FrameGeo.val_powGen, Category.id_comp, Category.id_comp, Units.val_pow_eq_pow_val]
  obtain ⟨s'', hs'', hE⟩ := PullExpField.of_generic hL P.U P.oD a (t.act.act a) k N hk₁
    (GlobalTheory.T.expansion_commutes_pullback_cmEndo_four_le hL V E H t P a N ha hN k hk) u hu hc F σ₀ s hσ₀ σ' (fun y J hJ => by
      rw [v' y J hJ, vu _ _ y J hJ, Units.val_pow_eq_pow_val])
  obtain rfl := PullLin.pullAl_unique hG _ a k N hP hs''
  obtain ⟨tA', ht'⟩ := (f₂ s').exists
  obtain ⟨tA, ht⟩ := (f₂ t').exists
  have hact := ((hθ tA' tA s' t' ht' ht).1 hΦ).isActOf P.A.isLB
  obtain ⟨σ₂, r₂, x₂⟩ := ht'
  obtain rfl := (g₂ s').unique hE x₂
  obtain ⟨τ, r₃, x₃⟩ := ht
  have lin := (FieldBaseChange.secLin_iff hLB
    (∑ i, c i • FieldBaseChange.extendSec P.U.toUnifPre F (k * N)
      (FieldBaseChange.genericSec P.U.toUnifPre (k * N) (σ i)) : FieldBaseChange.GroupSec P.U.toUnifPre F (k * N)) σ
    (UnifPre.gFK (G := t.G) F) c (fun i => FieldBaseChange.extendSec P.U.toUnifPre F (k * N)
      (FieldBaseChange.genericSec P.U.toUnifPre (k * N) (σ i))) (fun i y J hJ =>
      (FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans ((FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (σ i) q y J) (Category.assoc _ _ _))))).2 rfl
  have eτ := (g₂ t').unique x₃ ⟨l, c, σ, f, hσ, lin, hlin⟩
  rw [← eτ] at lin
  obtain ⟨ρ, a₁, a₂, a₃, a₄⟩ := GlobalTheory.T.exists_lift_point_translation_fieldPoint V t.G F (z₀ ≫ P.U.gen.inv) T e r g hg
  have key := GlobalTheory.T.eigenEquation_translation_kernel_genericFibre V _ P.D P.A t.G P.U.toUnifPre F (t.act.act a) (P.oA.act a) (P.oA.hom a) (P.lin.ext a) N k
    mu hmu wI hwI σ₀ σ' τ tA' tA v' r₂ r₃ θ hact z₀ ε hz₀ hW _ ρ z J hJ
  rw [PullExpField.secLin_val lin _ z hJ, PullExpField.secLin_val lin _ z hJ] at key
  simp only [gs_scal, FieldBaseChange.groupBase] at key
  rw [a₁, a₂, a₃, a₄] at key
  exact key

theorem eigen_germ : Laws → Laws4 → TwistBCSpanStatement → JetSer.JetAlgSt → JetSer.RepSt → JetSer.SerSt →
    JetSer.SerExSt → JetSer.RosIdSt → JetSer.ChartBCSt → FamGerm.GermExSt → EigGermSt := by
  intro hL _ _ hJet hRep hSer hEx hRos _ hGerm E _ _ _ H V _ _ _ F _ _ _ _ _ _ y a p k hp hk ha Λ e yy α hα he
    ⟨κ, Z, jZ, kZ, hκ, hfin, hflat, hred, hjZ, hja, hval, htan⟩ Dw I hco ⟨u₁, u₂, huu⟩
  let _ := H.starRing
  have := y.P.U.smooth
  have := y.t.act.hom a
  have hLB := y.P.U.LG.isLB
  have hk₁ : 1 ≤ k := by omega
  have hq : 1 ≤ k * p := Nat.mul_pos hk₁ hp.pos
  obtain ⟨b, hb, hW⟩ := character_eq_weil_pairing E H V F y.P.A y.P.oA Dw I p k hp.pos hk₁ hco a u₁ u₂ ha huu κ hκ
  obtain ⟨fT, h₁, h₂, -⟩ := y.tors F (k * p) hq
  obtain ⟨pt, hpt⟩ := h₂ b (by rw [pow_mul', pow_eq_one_of_kill y.P.oA.toRingAct ha b hb, one_pow])
  have hTo := (h₁ pt b).2 hpt.symm
  refine ⟨pt, b, hTo, hb, fun w hw s s' t' c hP hΦ hV h ω hh hω f hf l mo => ?_⟩
  obtain ⟨s₂, s₃⟩ := surjective_appTop_sq_cube y.P.U.toUnifPre
  obtain ⟨⟨mu₀, hmu₀⟩, hgeo⟩ := FrameGeo.frame_pullback_geo hJet hRep hSer hEx hRos V y.t.G
    (PullGerm.surjective_appTop s₂) s₂ s₃ y.P.U.LG y.P.U.cubG (𝓞 E) y.t.act y.u y.hu y.d y.x y.hx y.j y.hj y.B y.hB
    H.w0 y.ρ y.hρ a p ha
  obtain ⟨mu, hmu, hn⟩ := PullGerm.exists_norm y.P.U.LG (y.t.act.act a) hp.pos mu₀ hmu₀
  obtain ⟨r, hr⟩ := y.exists_frameSer
  let U : y.t.G.left.Opens := LB.wchart y.P.U.LG.L ![𝟙 y.t.G.left, (y.t.act.act a).left] (fun _ => y.j)
  have hU : ⊤ ≤ η[y.t.G].left ⁻¹ᵁ U := by
    refine GermExist.top_le_preimage_wchart _ _ _ _ fun i => ?_
    have key : η[y.t.G].left ≫ (![𝟙 y.t.G.left, (y.t.act.act a).left] : Fin 2 → _) i = η[y.t.G].left := by
      fin_cases i
      · exact Category.comp_id _
      · show η[y.t.G].left ≫ (y.t.act.act a).left = _
        rw [← Over.comp_left, IsMonHom.one_hom]
    rw [key]; exact y.hj
  have hle : U ≤ LB.wchart y.P.U.LG.L (fun _ : Fin 1 => 𝟙 y.t.G.left) (fun _ => y.j) :=
    fun x hx => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx 0
  have ser := fun g => ((hEx V y.t.G y.d y.x y.hx).1 U hU g).exists
  obtain ⟨M, hM⟩ := ser (mu.s (fun _ => y.j)).val
  obtain ⟨w₁, κ₁, hw₁, hexp⟩ := hgeo mu hmu M r hM hr
  obtain ⟨r', hr'⟩ := (GermExist.isUnit_of_isSer1 hRep hSer y.hx (Units.isUnit _) hr).exists_right_inv
  have hMu := GermExist.isUnit_of_isSer1 hRep hSer y.hx (Units.isUnit _) hM
  obtain ⟨n, cc, σ, fi, hcc, hσ, hlin⟩ := GlobalTheory.T.exists_integralExpansions_of_valuation_ge hL V y.ϖ y.hϖ y.P.D y.P.A y.t.G y.P.U y.Q y.hQ F y.v y.hv
    (k * p) hq (c • t') 0 hV
  let cO : Fin n → TWO.Ov y.v := fun i => ⟨cc i, hcc i⟩
  obtain ⟨m, hm⟩ : ∃ m : Γ(y.t.G.left, U)ˣ, m = mu.s (fun _ => y.j) := ⟨_, rfl⟩
  obtain ⟨sl, hsl⟩ : ∃ sl : Fin n → Γ(y.t.G.left, U), ∀ i, sl i * m.val ^ k =
      (y.t.G.left.presheaf.map (homOfLE hle).op).hom ((σ i).f (fun _ => y.j)) :=
    ⟨fun i => (y.t.G.left.presheaf.map (homOfLE hle).op).hom ((σ i).f (fun _ => y.j)) * (m⁻¹).val ^ k, fun i => by
      rw [_root_.mul_assoc, ← mul_pow, Units.inv_mul, one_pow, _root_.mul_one]⟩
  choose S hS using fun i => ser (sl i)
  have hS' : ∀ i, IsSer1 y.x _ ((σ i).f (fun _ => y.j)) (S i * M ^ k) := fun i => by
    refine isSer1_res hle ?_
    rw [← hsl i]
    exact isSer1_mul_pow hJet (hS i) (by rw [hm]; exact hM) k
  obtain ⟨gm₀, hgm⟩ := hGerm E H V F y (k * p) hq
  have hfe := ((hgm _ _).1 hf).trans ((hgm _ _).1 ⟨n, cc, σ, fi, fun i => S i * (M ^ k * r' ^ (k * p)), r, hσ, hlin,
    hr, fun i => ⟨_, hS' i, by
      rw [_root_.mul_assoc, _root_.mul_assoc, ← mul_pow, _root_.mul_comm r', hr', one_pow, _root_.mul_one]⟩, rfl⟩).symm
  obtain ⟨Φ, hΦ'⟩ := phiFun_of hL V (maximalIdeal V) y.P.D F (k * p) hq pt w hw
  have hΦc : PhiRel y.P.D.toPre F (k * p) pt w (c • s') (c • t') :=
    (hΦ' _ _).2 (by rw [(hΦ' _ _).1 hΦ, map_smul])
  have hall := GlobalTheory.T.fn_eigen_equation_of_forall_geometric_point_alt V (TWO.Ov y.v) F Subtype.val_injective (TWO.fO y.v y.hϖ y.hv) y.t.G inferInstance Z hfin
    hflat hred jZ hjZ U n cO sl kZ (fun T e c₀ r g hg z hz hz' => by
      have w₀ : (c₀.left ≫ jZ) ≫ y.t.G.hom = jFK (R := V) F ≫ jK V := by
        have a₁ : c₀.left ≫ Z.hom = Spec.map (CommRingCat.ofHom (algebraMap (TWO.Ov y.v) F)) := Over.w c₀
        rw [Category.assoc, hjZ, ← Category.assoc, a₁, PullExpField.hom_TF, ← Spec.map_comp]
        rfl
      let x₀ : TFK (R := V) F ⟶ (Over.pullback (jK V)).obj y.t.G :=
        Over.homMk (pullback.lift (c₀.left ≫ jZ) (jFK (R := V) F) w₀) (pullback.lift_snd _ _ _)
      have hx₀ : x₀.left ≫ pullback.fst y.t.G.hom (jK V) = c₀.left ≫ jZ := pullback.lift_fst _ _ _
      have hx₁ : ((x₀ ≫ y.P.U.gen.hom) ≫ y.P.U.gen.inv).left ≫ pullback.fst y.t.G.hom (jK V) = c₀.left ≫ jZ := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, hx₀]
      have hkill : (x₀ ≫ y.P.U.gen.hom) ≫ y.P.oA.act a = 1 := by
        have := y.P.U.gen_hom
        have e₂ : (Over.pullback (jK V)).map (y.t.act.act a) ≫ y.P.U.gen.hom = y.P.U.gen.hom ≫ y.P.oA.act a :=
          y.P.lin.ext a
        rw [Category.assoc, ← e₂, ← Category.assoc, comp_map_eq_one (jK V) _ x₀
          (by rw [hx₀, Category.assoc, Category.assoc, hja]), MonObj.one_comp]
      obtain ⟨J, hJ, hJ'⟩ := JetSer.FBOf.exists_good_const _ hLB y.j z
      have key := eigen_at_field_points hL y.P F a hp.pos hk ha mu hmu hn pt b hTo w hw (c • s) (c • s') (c • t')
        (PullLin.pullAl_smul _ a k p c hP) hΦc cc σ fi hσ hlin _ _ hkill (hW _ hkill) T e r g
        (by rw [hx₁, hg, Category.assoc]) z J hJ
      simp only [fun i => gs_div_mul _ k y.j mu (σ i) hle m hm _ (hsl i) _ z hz hJ',
        fun i => gs_div_mul _ k y.j mu (σ i) hle m hm _ (hsl i) _ z hz' hJ',
        ← _root_.mul_assoc, ← Finset.sum_mul] at key
      rw [gs_comp_eq_constVal e c₀.left ⊤ le_top, hval c₀ _ hx₁]
      refine (((val mu (r * g).left z J).isUnit.pow k).mul ((val mu r.left z J).isUnit.pow k)).mul_right_cancel ?_
      refine (_root_.mul_assoc _ _ _).symm.trans (key.trans ?_)
      exact (mul_right_comm _ _ _).trans (_root_.mul_assoc _ _ _))
  obtain ⟨wt, φ, hφ, hwφ, hwk⟩ := htan l
  have hD := dof_of_tangent hJet hRep hSer (TWO.fO y.v y.hϖ y.hv) _ y.hx y.B.G y.hB.law hU sl S hS cO jZ hjZ kZ hall
    (e l) (yy l) wt φ hφ hwφ hwk
  have eV : TWO.algVF (V := V) (F := F) = algebraMap V F := (IsScalarTower.algebraMap_eq V _ F).symm
  have hβ : (algebraMap (TWO.Ov y.v) F).comp (TWO.fO y.v y.hϖ y.hv) = algebraMap V F := eV
  obtain ⟨Ψ, hΨ⟩ := exists_evHom (a := ![y.B.A.act a]) (TB.WickVanishing.single_point_zero_constant (y.B.A.const a))
  obtain ⟨x, hx, hxe⟩ := coeff_dof_sub_mem (TWO.fO y.v y.hϖ y.hv) (algebraMap (TWO.Ov y.v) F) Subtype.val_injective hβ
    _ y.B a (e l) (α l) (yy l) (hα l) (he l) _ hD r' ((κ₁⁻¹ ^ k : Vˣ) : V) k f (by
      rw [Units.val_pow_eq_pow_val, map_pow, map_pow]
      refine solve_germ (W := FB.toK F ω) (R := FB.toK F r) (R' := FB.toK F r') (M := FB.toK F M)
        (K := MvPowerSeries.C (algebraMap V F κ₁)) (E := FB.toK F (ev (n := 1) ![y.B.A.act a] r)) (p := p)
        (hMu.map _) ?_ ?_ ?_ ?_ ?_
      · rw [hω, ← hexp F h hh, ← map_pow, ← map_mul, hw₁, map_mul, map_mul, MvPowerSeries.map_C]
      · rw [← map_mul, hr', map_one]
      · rw [← map_mul, hΨ, hΨ, ← map_mul, hr', map_one, map_one]
      · rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
      · rw [hfe, map_sum, Finset.sum_mul, eV]
        refine Finset.sum_congr rfl fun i _ => ?_
        have mm : MvPowerSeries.map (algebraMap (TWO.Ov y.v) F) (MvPowerSeries.map (TWO.fO y.v y.hϖ y.hv) (S i)) =
            MvPowerSeries.map (algebraMap V F) (S i) := by
          rw [← hβ]; rfl
        rw [map_mul, map_mul, map_pow, map_pow, map_mul, MvPowerSeries.map_C, mm, _root_.mul_assoc]
        rfl) mo
  obtain ⟨x', rfl⟩ := Ideal.mem_span_singleton'.1 hx
  refine le_of_le_of_eq ?_ (congrArg y.v hxe).symm
  rw [map_mul, map_natCast (algebraMap (TWO.Ov y.v) F), AddValuation.map_mul]
  exact le_add_of_nonneg_left (TWO.v_nonneg y.v x')

end GlobalTheory.EigenGerm
