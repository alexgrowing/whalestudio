import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfForallExistsLsumETwoPi
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArcStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieCombStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangentStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat

noncomputable section

namespace GlobalTheory.ArcType

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries MonObj

theorem ext_dual {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} {p q : Sp (DualNumber R) ⟶ X}
    (h₀ : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ p = spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ q)
    (h₁ : ∀ (V : X.Opens) (f : Γ(X, V)), ⊤ ≤ p ⁻¹ᵁ V → ⊤ ≤ q ⁻¹ᵁ V →
      TrivSqZeroExt.snd (valR p V f) = TrivSqZeroExt.snd (valR q V f)) : p = q := by
  have := ConstTan.isLocalRing_dual R
  have : IsLocalHom (TrivSqZeroExt.fstHom R R R).toRingHom :=
    ⟨fun _ h => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 h⟩
  have hc : spMap (TrivSqZeroExt.fstHom R R R).toRingHom (IsLocalRing.closedPoint R) =
      IsLocalRing.closedPoint (DualNumber R) := IsLocalRing.comap_closedPoint _
  have hpq : p (IsLocalRing.closedPoint (DualNumber R)) = q (IsLocalRing.closedPoint (DualNumber R)) := by
    rw [← hc]
    exact congrArg (fun r : Sp R ⟶ X => r (IsLocalRing.closedPoint R)) h₀
  obtain ⟨_, ⟨V, hV, rfl⟩, hm, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p (IsLocalRing.closedPoint (DualNumber R)))) isOpen_univ
  have hp : ⊤ ≤ p ⁻¹ᵁ V := (Points.le_preimage_iff p V).2 hm
  have hq : ⊤ ≤ q ⁻¹ᵁ V := (Points.le_preimage_iff q V).2 (hpq ▸ hm)
  refine Points.ext_of_valR hV hp hq fun f => TrivSqZeroExt.ext ?_ (h₁ V f hp hq)
  exact (Points.valR_spMap_comp _ p V hp f).symm.trans
    ((congrArg (fun r => valR r V f) h₀).trans (Points.valR_spMap_comp _ q V hq f))

theorem ext_of_injective {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] {k : R →+* S}
    (hi : Function.Injective k) {X : Scheme.{0}} {p q : Sp (DualNumber R) ⟶ X}
    (h₀ : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ p = spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ q)
    (h₁ : spMap (dualMap k) ≫ p = spMap (dualMap k) ≫ q) : p = q := by
  refine ext_dual h₀ fun V f hp hq => hi ?_
  have := (Points.valR_spMap_comp _ p V hp f).symm.trans
    ((congrArg (fun r => valR r V f) h₁).trans (Points.valR_spMap_comp _ q V hq f))
  simpa [dualMap] using congrArg TrivSqZeroExt.snd this

theorem eq_of_sumsAt {s s' : PowerSeries ℂ} {T : ℝ} (h : ∀ w : ℂ, T < w.im → ∃ x, SumsAt s w x ∧ SumsAt s' w x) :
    s = s' := by
  have h0 : ∀ w : ℂ, T < w.im → SumsAt (s - s') w 0 := fun w hw => by
    obtain ⟨x, h₁, h₂⟩ := h w hw
    simpa [SumsAt, sub_mul] using h₁.sub h₂
  have hm := Conv.coe_mem_halfRing.2 fun w hw => ⟨0, h0 w hw⟩
  have := Conv.halfRing_spec.2.2.2.1 T T ⟨_, hm⟩ fun w hw _ =>
    HasSum.unique (Conv.sumsAt_ev hw hm) (h0 w hw)
  have h2 : ((s - s' : PowerSeries ℂ) : ℂ⸨X⸩) = 0 := congrArg Subtype.val this
  exact sub_eq_zero.1 (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (h2.trans (map_zero _).symm))

theorem fderiv_diag {g : ℕ} (a : Fin g → ℂ) (ha : ∀ k, a k ≠ 0) (F : (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) :
    fderiv ℂ (fun z => F (fun k => a k * z k)) 0 z = fderiv ℂ F 0 (fun k => a k * z k) := by
  let L : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) :=
    (LinearEquiv.piCongrRight fun k => LinearEquiv.smulOfNeZero ℂ ℂ (a k) (ha k)).toContinuousLinearEquiv
  have := L.comp_right_fderiv (f := F) (x := 0)
  rw [map_zero] at this
  exact congrArg (fun D => D z) this

section Hol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} [Algebra (FractionRing ℂ) ℂ]
  {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {a : ArcIn Dw l β ℂ (σ.comp β)} {χ : Sp (PowerSeries ℂ) ⟶ Y.X} {W : Wit Y a χ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty} (Ha : HolArc Y σ a χ W Fu)

theorem diff_of {ν : Out.GtPt a.D₀ (epsR ℂ)} {z₀ : Fin g → ℂ} {v : epsR (PowerSeries ℂ) ⟶ W.t.G}
    (h : AnVec Ha ν z₀) (hv : LieImg W ν v) (V : Y.t.G.left.Opens) (f : Γ(Y.t.G.left, V))
    (hV : ⊤ ≤ (v.left ≫ W.m.φ) ⁻¹ᵁ V) : ∃ T' : ℝ, ∀ w : ℂ, T' < w.im →
      ∀ xF : (Fin g → ℂ) → (Sp ℂ ⟶ Y.oF.t.G.left), (∀ z, xF z ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left ∧
        xF z ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ) →
        SumsAt (TrivSqZeroExt.snd (valR (A := DualNumber (PowerSeries ℂ)) (v.left ≫ W.m.φ) V f)) w
          (fderiv ℂ (fun z => valAt' (xF z ≫ Y.m.φ) V f) 0 z₀) := by
  refine Ha.diff z₀ ν v V f h.1 h.2 (fun n ρ κ vn h₁ h₂ h₃ h₄ h₆ => hv n ρ κ vn h₁ h₂ h₃ h₄ ?_ h₆) hV
  rw [← cancel_mono (Out.thick (PowerSeries ℂ) (Ideal.span {PowerSeries.X}) n)]
  have e₁ := Over.w (Out.fstG (Ideal.span {(PowerSeries.X : PowerSeries ℂ)}) n W.t.G)
  refine (Category.assoc _ _ _).trans ((congrArg (vn ≫ ·) e₁.symm).trans ((Category.assoc _ _ _).symm.trans ?_))
  rw [h₆, Category.assoc, Over.w v]
  refine (spMap_comp _ _).symm.trans (Eq.trans (congrArg spMap ?_) (spMap_comp _ _))
  exact RingHom.ext fun r => h₁ r

theorem exists_lift (w : ℂ) (hw : Ha.T < w.im) : ∃ xF : (Fin g → ℂ) → (Sp ℂ ⟶ Y.oF.t.G.left),
    (∀ z, xF z ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left ∧
      xF z ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ) ∧
    ∀ (x : 𝓞 E) z, xF (fun k => ty k (x : E) * z k) ≫ Y.m.φ = (xF z ≫ Y.m.φ) ≫ (Y.t.act.act x).left := by
  have hP := Ha.period w hw
  let yF : Sp ℂ ⟶ Xo.XF c := pullback.lift (Fu.u Ha.i (Ha.Pw w)) (spMap σ)
    ((Fu.over_σ _ _ hP).trans (spMap_comp _ _))
  have C := Y.m0.toSABMap.cart.1
  have hw' : ∀ z, (Fu.ex Ha.i (Ha.Pw w) z).left ≫ Xo.univ.t.G.hom = yF ≫ pullback.fst _ _ := fun z =>
    (Over.w _).trans (pullback.lift_fst _ _ _).symm
  refine ⟨fun z => C.lift _ yF (hw' z), fun z => ⟨C.lift_fst _ _ _, ?_⟩, fun x z => ?_⟩
  · rw [← Category.assoc, C.lift_snd]; exact pullback.lift_snd _ _ _
  · rw [Category.assoc, ← Y.m.act x, ← Category.assoc]
    congr 1
    refine C.hom_ext ?_ ?_
    · rw [Category.assoc, Y.m0.toSABMap.act x, C.lift_fst, ← Category.assoc, C.lift_fst, Fu.ex_lin _ _ hP]
      rfl
    · rw [Category.assoc, Over.w, C.lift_snd, C.lift_snd]

theorem act_eq {ν ν₁ : Out.GtPt a.D₀ (epsR ℂ)} {z₀ : Fin g → ℂ} {v v₁ : epsR (PowerSeries ℂ) ⟶ W.t.G}
    {x : 𝓞 E} (hx : x ≠ 0) (h : AnVec Ha ν z₀) (hv : LieImg W ν v) (ht : IsTangent v)
    (h₁ : AnVec Ha ν₁ (fun k => ty k (x : E) * z₀ k)) (hv₁ : LieImg W ν₁ v₁) (ht₁ : IsTangent v₁) :
    v₁ = v ≫ W.t.act.act x := by
  have := W.t.act.hom x
  have ht₂ : IsTangent (v ≫ W.t.act.act x) :=
    (Chart.isTan_iff _).1 (Chart.isTan_comp ((Chart.isTan_iff _).2 ht) _)
  refine Over.OverMorphism.ext (W.m.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  refine ext_dual (R := PowerSeries ℂ) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ W.m.φ) (Eq.trans ht₁ (Eq.symm ht₂))).trans (Category.assoc _ _ _))) ?_
  have e : (v ≫ W.t.act.act x).left ≫ W.m.cm.F = (v.left ≫ W.m.φ) ≫ (Y.t.act.act x).left := by
    rw [Over.comp_left, Category.assoc, W.m.act x, Category.assoc]
  rw [e]
  intro V f hp hq
  obtain ⟨T₁, H₁⟩ := diff_of Ha h₁ hv₁ V f hp
  obtain ⟨T₂, H₂⟩ := diff_of Ha h hv ((Y.t.act.act x).left ⁻¹ᵁ V) (((Y.t.act.act x).left.app V).hom f) hq
  refine eq_of_sumsAt (T := max Ha.T (max T₁ T₂)) fun w hw => ?_
  simp only [max_lt_iff] at hw
  obtain ⟨xF, hF, hl⟩ := exists_lift Ha w hw.1
  refine ⟨_, H₁ w hw.2.1 xF hF, ?_⟩
  have k := H₂ w hw.2.2 xF hF
  rw [← fderiv_diag _ (fun k => (map_ne_zero _).2 (by simpa using hx))]
  simp only [hl, Points.valAt'_eq_valR] at k ⊢
  simp only [Points.valR_comp _ (Y.t.act.act x).left]
  exact k

end Hol

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {R S : Type} [CommRing R] [CommRing S] [Algebra c.F S] {k : R →+* S} {G : Over (Sp R)} [GrpObj G]
  (y : FrPt Xo c S) {t' : SAB H (Sp S)} (m : SABMap t' Xo.univ.t y.x) {φ : t'.G.left ⟶ G.left}
  (hφ : IsGrpPullback t'.G G (spMap k) φ) (τ : E →+* ℂ) {v : Fin (Dw.mult τ) → (epsR R ⟶ G)}
  {u : Fin (Dw.mult τ) → (epsR S ⟶ t'.G)} (h₁ : ∀ i, (u i).left ≫ m.φ = y.u τ i)
  (h₂ : ∀ i, (u i).left ≫ φ = spMap (dualMap k) ≫ (v i).left)

include hφ h₁ h₂ in

theorem isCombAt_one {cf : Fin (Dw.mult τ) → R} (h : IsLieComb cf v 1) :
    IsCombAt y.x (y.u τ) (fun i => k (cf i)) (1 : tEps y.x ⟶ Xo.univ.t.G).left := by
  have h0 := LieCombBaseChange.prod_left_comp hφ (T := epsR R) (T' := epsR S) _ (LieCombBaseChange.dualMap_over k)
    (n := 0) Fin.elim0 Fin.elim0 (fun i => i.elim0)
  simp only [List.ofFn_zero, List.prod_nil] at h0
  obtain ⟨p, hp, e⟩ := (lieComb_baseChange R S k G t'.G φ hφ _ v 1 cf u 1 h₂ h).1 h0
  refine ⟨fun i => pushHom m.cart (epsR S) (p i), fun i => ?_, ?_⟩
  · exact (congrArg (· ≫ m.φ) (hp i)).trans ((Category.assoc _ _ _).trans (congrArg _ (h₁ i)))
  · have e₁ := map_list_prod (pushHom m.cart (epsR S)) (List.ofFn p)
    rw [← e, map_one, List.map_ofFn] at e₁
    exact congrArg (fun q => q.left) e₁.symm

include hφ h₁ h₂ in

theorem coeff_eq {cf cf' : Fin (Dw.mult τ) → R} (h : IsLieComb cf v 1) (h' : IsLieComb cf' v 1) (i) :
    k (cf i) = k (cf' i) := by
  refine congrFun ((y.basis τ _ ⟨Over.w _, ?_⟩ fun x => ?_).unique (isCombAt_one y m hφ τ h₁ h₂ h)
    (isCombAt_one y m hφ τ h₁ h₂ h')) i
  · let r : Over.mk y.x ⟶ tEps y.x := Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      refine (Category.assoc _ _ _).symm.trans (Eq.trans (congrArg (· ≫ y.x) ?_) (Category.id_comp _))
      exact (spMap_comp _ _).symm.trans (Eq.trans (congrArg spMap (RingHom.ext fun _ => rfl)) (Spec.map_id _)))
    exact congrArg (fun q => q.left) (MonObj.comp_one (M := Xo.univ.t.G) r)
  · have := Xo.univ.t.act.hom x
    let r : tEps y.x ⟶ tEps y.x := Over.homMk (spMap (epsMul (algebraMap c.F S (embK c τ x)))) (by
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ y.x) (LieCombBaseChange.epsScale_over _)))
    exact congrArg (fun q => q.left)
      ((MonObj.one_comp (Xo.univ.t.act.act x)).trans (MonObj.comp_one (M := Xo.univ.t.G) r).symm)

end Frame

theorem left_eq_of_comb {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {s : R} {v w : epsR R ⟶ G}
    (h : IsLieComb (fun _ : Fin 1 => s) (fun _ => v) w) : w.left = spMap (epsScaleR s) ≫ v.left := by
  obtain ⟨u, hu, rfl⟩ := h
  simpa using hu 0

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), GoodEmb c σ → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → Mono Y.j → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ i, AnVec Ha (e τ i) (z τ i)) → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) := by
  intro hL _ E _ _ _ H Dw l Xo c σ r U Uw _ _ O _ β Y a χ W Ha _ y e th z hσ halg _ hF hz τ
  have hG := hL.globalFns
  have ex := GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y ℂ _ a χ W
  have lin := GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y ℂ _ a χ W
  obtain ⟨an₁, an₂, an₃, an₄⟩ := GlobalTheory.T.torusExt_exponential_derivative_bijective_tangent hG E H Dw l Xo c σ O β Y a χ W _ _ _ Ha
  obtain ⟨_, t', m1, m2, _, -, -, -, -, -, hu, -⟩ := hF
  choose v u' hv h₁ h₂ hover using hu τ
  have hi : Function.Injective (HahnSeries.ofPowerSeries ℤ ℂ) := HahnSeries.ofPowerSeries_injective
  let u : Fin (Dw.mult τ) → (epsR ℂ⸨X⸩ ⟶ t'.G) := fun i => Over.homMk (u' i) (hover i)
  refine ⟨Fintype.linearIndependent_iff.2 fun cf hcf i => ?_, fun i jj hjj => ?_⟩
  · obtain ⟨o, ho, -⟩ := an₂ 0
    have c₀ := (an₄ 0 Fin.elim0 Fin.elim0 Fin.elim0 o (fun j => j.elim0)).2 (by simpa using ho)
    have h₀ := (lin 0 _ _ o Fin.elim0 1 (fun j => j.elim0) c₀).2 ⟨Fin.elim0, fun j => j.elim0, by simp⟩
    have c₁ := (lin _ cf _ o v 1 hv ((an₄ _ cf _ _ o (hz τ)).2 (hcf ▸ ho))).1 h₀
    have c₂ := (lin _ 0 _ o v 1 hv ((an₄ _ 0 _ _ o (hz τ)).2 (by simpa using ho))).1 h₀
    exact PowerSeries.C_injective (hi (coeff_eq y m1 m2.cart τ (u := u) h₁ h₂ c₁ c₂ i))
  · refine (GlobalTheory.Relab.relab_good E H l c σ hσ).1.1 ?_
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => ?_)
    by_cases hx : x = 0
    · simp [hx]
    have ht := ((ex _).2 _ (hv i)).1 (an₃ _ _ (hz τ i))
    obtain ⟨ν₁, hν₁, -⟩ := an₂ (fun k => relab c σ (Uw.e k).1 (x : E) * z τ i k)
    obtain ⟨v₁, hv₁, -⟩ := (ex ν₁).1
    have e₁ := act_eq Ha hx (hz τ i) (hv i) ht hν₁ hv₁ (((ex _).2 _ hv₁).1 (an₃ _ _ hν₁))
    obtain ⟨ν₂, hν₂, -⟩ := an₂ (σ (embK c τ x) • z τ i)
    obtain ⟨v₂, hv₂, -⟩ := (ex ν₂).1
    have e₂ := left_eq_of_comb ((lin 1 (fun _ => σ (embK c τ x)) (fun _ => e τ i) ν₂ (fun _ => v i) v₂
      (fun _ => hv i) ((an₄ 1 _ _ (fun _ => z τ i) ν₂ fun _ => hz τ i).2 (by simpa using hν₂))).1 hv₂)
    have e₃ : v₁.left = v₂.left := by
      refine ext_of_injective hi (Eq.trans (((ex _).2 _ hv₁).1 (an₃ _ _ hν₁))
        (Eq.symm (((ex _).2 _ hv₂).1 (an₃ _ _ hν₂)))) ?_
      have e₄ : u' i ≫ (t'.act.act x).left = spMap (epsMul (algebraMap c.F ℂ⸨X⸩ (embK c τ x))) ≫ u' i := by
        refine m1.cart.1.hom_ext ?_ ?_
        · rw [Category.assoc, m1.act x, ← Category.assoc, h₁, Category.assoc, h₁]
          exact y.eig τ i x
        · rw [Category.assoc, Over.w, Category.assoc, hover]
          exact (LieCombBaseChange.epsScale_over _).symm
      have e₅ := congrArg (· ≫ m2.φ) e₄
      simp only [Category.assoc] at e₅
      rw [m2.act x, ← Category.assoc, h₂, halg] at e₅
      rw [e₁, e₂, Over.comp_left]
      refine (Category.assoc _ _ _).symm.trans (e₅.trans ?_)
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (v i).left)
        (LieCombBaseChange.dualMap_epsScale _ _).symm).trans (Category.assoc _ _ _))
    obtain rfl : ν₁ = ν₂ := ConstLie.eq_of_red W hG hv₁ hv₂ (congrArg _ e₃)
    exact mul_right_cancel₀ hjj (congrFun ((an₁ _ (an₃ _ _ hν₁)).unique hν₁ hν₂) jj)

end GlobalTheory.ArcType
