import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.TBIdemDen
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcNilpotent
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
open scoped Classical

namespace GlobalTheory.ArcQ.TorusLetter

open MonoidalCategory CartesianMonoidalCategory MonObj

theorem valR_eq_mul {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {ε : K → ℤ}
    {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht' : t'.IsGen) {F : Type} [Field F] (r : Sp F ⟶ Y) (r' : Sp F ⟶ Y')
    (h : ∀ k, r ≫ φ k = r' ≫ φ' k) (c : F)
    (hv : ∀ z J, Good L z J → (val t r z J).val = TorusExt.stalkConst z c * (val t' r' z J).val)
    (j : K → L.ι) (hj : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ j) :
    ⊤ ≤ r' ⁻¹ᵁ LB.wchart L φ' j ∧ valR r _ (t.s j).val = c * valR r' _ (t'.s j).val := by
  have hj' : ⊤ ≤ r' ⁻¹ᵁ LB.wchart L φ' j := fun z hz => Set.mem_iInter.2 fun k => by
    have : (r ≫ φ k) z ∈ L.U (j k) := Set.mem_iInter.1 (hj hz) k
    rw [h k] at this
    exact this
  let z : Sp F := IsLocalRing.closedPoint F
  choose J hJ using fun q : Sp F ⟶ X => exists_chart hL (q z)
  replace hJ : Good L z J := hJ
  refine ⟨hj', (TorusExt.stalkConst z).injective ?_⟩
  have e₁ : TorusExt.stalkConst z (valR r _ (t.s j).val) = (gm r z (LB.wchart L φ j) (t.s j)).val :=
    (TorusExt.gs_eq_stalkConst r z hj _).symm.trans (gs_unit r z _ (hj trivial) _)
  have e₂ : TorusExt.stalkConst z (valR r' _ (t'.s j).val) = (gm r' z (LB.wchart L φ' j) (t'.s j)).val :=
    (TorusExt.gs_eq_stalkConst r' z hj' _).symm.trans (gs_unit r' z _ (hj' trivial) _)
  have e₃ : trF φ ε r z j (fun k => J (r ≫ φ k)) = trF φ' ε r' z j (fun k => J (r' ≫ φ' k)) :=
    Finset.prod_congr rfl fun k _ =>
      congrArg (fun q => gm q z (L.U (j k) ⊓ L.U (J q)) (L.g (j k) (J q)) ^ ε k) (h k)
  rw [map_mul, e₁, e₂, gen_trans ht r z (hj trivial) (hJ.mem φ r), gen_trans ht' r' z (hj' trivial) (hJ.mem φ' r'),
    e₃, Units.val_mul, Units.val_mul]
  exact (congrArg (_ * ·) (hv z J hJ)).trans (mul_left_comm _ _ _)

theorem gtφT_eq {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R) {T : Over (Sp R)} (b : T ⟶ D.P.A) (x : D.X)
    (k : Fin 4) : Out.DegPre.gtφT D T b x k = b.left ≫ Out.DegPre.gtφT D D.P.A (𝟙 _) x k := by
  have h : ∀ p : 𝟙_ (Over (Sp R)) ⟶ D.P.A, b ≫ toUnit D.P.A ≫ p = toUnit T ≫ p := fun p => by
    rw [← Category.assoc, comp_toUnit]
  fin_cases k
  · change (toUnit _ ≫ D.c x * b).left = (b ≫ (toUnit _ ≫ D.c x * 𝟙 D.P.A)).left
    rw [MonObj.comp_mul, h, Category.comp_id]
  · change (toUnit _ ≫ D.c x).left = (b ≫ toUnit _ ≫ D.c x).left
    rw [h]
  · exact (Category.comp_id _).symm
  · change (toUnit _ ≫ η[D.P.A]).left = (b ≫ toUnit _ ≫ η[D.P.A]).left
    rw [h]

theorem zeroT_left {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R) (T : Over (Sp R)) :
    (Out.DegPre.zeroT D T).left = T.hom ≫ (η[D.P.A]).left := by
  have := Over.w (toUnit T)
  exact congrArg (· ≫ (η[D.P.A]).left) ((Category.comp_id _).symm.trans this)

theorem tf_hom [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] :
    (show Sp ℂ ⟶ Sp ℂ from (Out.TF (R := ℂ) ℂ).hom) = 𝟙 (Sp ℂ) := by
  refine (Spec.map_comp _ _).symm.trans ?_
  refine Eq.trans (congrArg Spec.map ?_) (Spec.map_id _)
  ext x
  exact (IsScalarTower.algebraMap_apply ℂ (FractionRing ℂ) ℂ x).symm

theorem fderiv_of_exp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : V → ℂ} (hf : DifferentiableAt ℂ f 0)
    (v : V) (m : ℂ) (h : ∀ s : ℂ, f (s • v) = eTwoPi (s * m) * f 0) :
    fderiv ℂ f 0 v = 2 * Real.pi * Complex.I * m * f 0 := by
  have h₁ : HasDerivAt (fun s : ℂ => f (s • v)) (fderiv ℂ f 0 v) 0 := by
    have a : HasDerivAt (fun s : ℂ => s • v) v 0 := by simpa using (hasDerivAt_id (0 : ℂ)).smul_const v
    exact HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hf.hasFDerivAt a (zero_smul _ _).symm
  have h₂ : HasDerivAt (fun s : ℂ => eTwoPi (s * m) * f 0) (2 * Real.pi * Complex.I * m * f 0) 0 := by
    have := ((((hasDerivAt_id (0 : ℂ)).mul_const m).const_mul (2 * Real.pi * Complex.I)).cexp).mul_const (f 0)
    refine HasDerivAt.congr_deriv this ?_
    simp
  rw [funext h] at h₁
  exact h₁.unique h₂

theorem sum_dual_mul {E : Type} [Field E] [NumberField E] (τ ρ : E →+* ℂ) :
    ∑ i, τ ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E) i) *
      ρ (integralBasis E i) = if τ = ρ then 1 else 0 := by
  have := idempotent_evaluation E ℂ _ (integralBasis E) ρ τ
  simpa only [TB.evAt, TB.idemOf, TB.trDual, map_sum, Algebra.TensorProduct.productMap_apply_tmul,
      AlgHom.id_apply, RingHom.toRatAlgHom_apply] using this

end GlobalTheory.ArcQ.TorusLetter

namespace GlobalTheory.ArcQ

open TorusLetter MonoidalCategory CartesianMonoidalCategory MonObj

theorem anVec_torusLetter : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (ξ : Module.Dual ℤ a.D₀.X) (t : (Fu.Di Ha.i).La) (τ : E →+* ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)), (∀ v', -(Fu.Di Ha.i).EF t v' = ξ (Ha.y v')) → GtTanR ν → ν.b = Out.DegPre.zeroT a.D₀ (epsR ℂ) → (∀ x, DlogTan ν x (xiVal τ ξ x)) → AnVec Ha ν (fun j => if ty j = conjEmb τ then (2 * Real.pi * Complex.I)⁻¹ * Ha.P₀ t j else 0) := by
  intro _ E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha ξ t τ ν ht hν hb hd
  obtain ⟨nn, hN, -, -, hnn, -, -⟩ := holArc_nilpotent E H Dw l Xo c σ O β Y a χ W g ty Fu Ha
  let b := RingOfIntegers.basis E
  let cf := fun i => τ ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E) i)
  have hbar : ∀ u : 𝓞 E, H.bar (H.bar u) = u := fun u => Subtype.ext (by
    change ((H.bar (H.bar u) : 𝓞 E) : E) = (u : E)
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply])
  have hEF : ∀ i v', -(Fu.Di Ha.i).EF (H.bar (b i) • t) v' = ξ (b i • Ha.y v') := fun i v' => by
    rw [(Fu.Di Ha.i).adj, hbar, ht, map_smul]
  have hr := fun i => (Ha.riemann (H.bar (b i) • t)).1 fun v' hv' => by
    have := hEF i v'
    rwa [hv', smul_zero, map_zero, neg_eq_zero] at this
  have htor : ∀ i (s : ℂ), IsTorusPt (Ha.ex₀ (s • Ha.P₀ (H.bar (b i) • t)))
      (fun x => eTwoPi (s * (ξ (b i • x) : ℤ))) := fun i s => by
    obtain ⟨x, hx, hx'⟩ := (hr i).2 s
    have hxe : x = fun z => eTwoPi (s * (ξ (b i • z) : ℤ)) := funext fun z => by
      obtain ⟨v', rfl⟩ := Ha.y_onto z
      rw [hx', ← hEF]
      congr 1
      push_cast
      ring
    exact hxe ▸ hx
  have hyt : Ha.y t = 0 := ((Ha.riemann t).1 fun v' hv' => by
    have := ht v'
    rwa [hv', map_zero, neg_eq_zero] at this).1
  have hP : ∀ (u : 𝓞 E) j, Ha.P₀ (u • t) j = ty j (u : E) * Ha.P₀ t j := fun u j => by
    have h := (Ha.period (((Ha.T + 1 : ℝ) : ℂ) * Complex.I) (by simp)).1 u t j
    rwa [Ha.Pw_eq, Ha.Pw_eq, hN, hN, hnn t hyt, hnn _ (by rw [map_smul, hyt, smul_zero]), map_zero, smul_zero,
      add_zero, add_zero] at h
  have hz : (fun j => if ty j = conjEmb τ then (2 * Real.pi * Complex.I)⁻¹ * Ha.P₀ t j else 0) =
      ∑ i, ((2 * Real.pi * Complex.I)⁻¹ * cf i) • Ha.P₀ (H.bar (b i) • t) := funext fun j => by
    have h := sum_dual_mul τ (conjEmb (ty j))
    have e : ∀ i, ty j ((H.bar (b i) : 𝓞 E) : E) = conjEmb (ty j) (integralBasis E i) := fun i => by
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, integralBasis_apply]
      rfl
    have hc : ty j = conjEmb τ ↔ τ = conjEmb (ty j) := by
      constructor <;> (intro q; rw [q]; ext u; simp [conjEmb])
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hP, e]
    calc _ = (2 * Real.pi * Complex.I)⁻¹ * (if τ = conjEmb (ty j) then 1 else 0) * Ha.P₀ t j := by
          simp only [hc]; split_ifs <;> simp
      _ = _ := by
          rw [← h, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by simp only [cf]; ring
  rw [hz]
  have h0 : (Ha.ex₀ 0).IsZero := (Ha.ker 0).2 ⟨0, map_zero _, (map_zero _).symm⟩
  have hzF : ∀ p : Out.GtPtF a.D₀ ℂ, p.b = Out.DegPre.zeroF a.D₀ ℂ →
      (show Sp ℂ ⟶ _ from p.b.left) = (η[a.D₀.P.A]).left := fun p hp => by
    rw [hp]
    exact (zeroT_left a.D₀ _).trans ((congrArg (· ≫ (η[a.D₀.P.A]).left) tf_hom).trans (Category.id_comp _))
  have hνb : ν.b.left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (η[a.D₀.P.A]).left := by
    rw [hb]; exact zeroT_left a.D₀ _
  obtain ⟨g₀, hg₀, hp⟩ := hν
  have hfst : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ ν.b.left = (Ha.ex₀ 0).b.left := by
    rw [← hp.1, hg₀.1]
    exact (zeroT_left a.D₀ _).trans ((Category.id_comp _).trans (hzF _ h0.1).symm)
  refine ⟨⟨hfst, fun U hU f => ?_⟩, fun x j hj => ?_⟩
  · have hU0 : ⊤ ≤ (show Sp ℂ ⟶ _ from (Ha.ex₀ 0).b.left) ⁻¹ᵁ U :=
      hfst ▸ (ZH.CrdCalc.valR_spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom _ U hU).1
    have hdf : DifferentiableAt ℂ (fun z => valAt' (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left) U f) 0 :=
      (Ha.hol_b U f).2.differentiableAt ((Ha.hol_b U f).1.mem_nhds ⟨trivial, hU0⟩)
    have hl : valR (A := DualNumber ℂ) ν.b.left U f = algebraMap ℂ _ (valR (A := ℂ) (η[a.D₀.P.A]).left U f) := by
      rw [hνb]
      exact (ZH.CrdCalc.valR_spMap _ _ U (hzF _ h0.1 ▸ hU0)).2 f
    refine (congrArg TrivSqZeroExt.snd ((ZH.CrdCalc.valR_eq _ U hU f).symm.trans hl)).trans ?_
    rw [map_sum]
    refine Eq.trans rfl (Finset.sum_eq_zero fun i _ => ?_).symm
    rw [map_smul, fderiv_of_exp hdf _ 0 fun s => ?_]
    · simp
    · rw [hzF _ (htor i s).1, hzF _ h0.1]
      simp [eTwoPi]
  · have hL := a.D₀.P.isLB
    obtain ⟨-, hv0⟩ := (isZero_iff _).1 h0
    obtain ⟨hj0, e0⟩ := valR_eq_mul hL (ν.isGen x) ((Ha.ex₀ 0).isGen x)
      (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (𝟙 (Sp ℂ)) (fun k => by
        rw [gtφT_eq, ← Category.assoc, hfst]
        exact (gtφT_eq a.D₀ (Ha.ex₀ 0).b x k).symm.trans (Category.id_comp _).symm) 1 (fun z J hJ => by
        have e₁ := (val_corr hJ (hg₀.2 x) (𝟙 _)).trans (val_one _)
        have e₂ := (val_corr hJ (hp.2 x) (𝟙 _)).trans (val_pull hJ _ _ _)
        rw [Category.id_comp] at e₂
        rw [map_one, _root_.one_mul]
        exact congrArg Units.val ((e₂.symm.trans e₁).trans (hv0 x z J hJ).symm)) j (fun z _ => hj trivial)
    have hf : TrivSqZeroExt.fst (valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val) = chiVal (Ha.ex₀ 0) x j := by
      have := (ZH.CrdCalc.valR_spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom (𝟙 _)
        (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) j) hj).2 ((ν.s x).s j).val
      rw [Category.comp_id] at this
      exact this.symm.trans (e0.trans (_root_.one_mul _))
    have hset : ∀ z, (⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Ha.ex₀ z).b x) j) ↔
        ⊤ ≤ (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left) ⁻¹ᵁ
          LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ a.D₀.P.A (𝟙 _) x) j := fun z => by
      have e : Out.DegPre.gtφ a.D₀ ℂ (Ha.ex₀ z).b x =
          fun k => (Ha.ex₀ z).b.left ≫ Out.DegPre.gtφT a.D₀ a.D₀.P.A (𝟙 _) x k :=
        funext fun k => gtφT_eq a.D₀ (Ha.ex₀ z).b x k
      rw [e]
      exact ⟨fun h y _ => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h trivial) k,
        fun h y _ => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h trivial) k⟩
    have hdf : DifferentiableAt ℂ (fun z => chiVal (Ha.ex₀ z) x j) 0 := by
      refine (Ha.hol_chi x j).differentiableAt (IsOpen.mem_nhds ?_ hj0)
      simpa only [hset, Set.mem_univ, true_and] using
        (Ha.hol_b (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ a.D₀.P.A (𝟙 _) x) j) 0).1
    have hder : ∀ i, fderiv ℂ (fun z => chiVal (Ha.ex₀ z) x j) 0 (Ha.P₀ (H.bar (b i) • t)) =
        2 * Real.pi * Complex.I * (ξ (b i • x) : ℤ) * chiVal (Ha.ex₀ 0) x j := fun i =>
      fderiv_of_exp hdf _ _ fun s => by
        obtain ⟨hb₁, hv₁⟩ := (TorusExt.isTorusPtF_iff_val _ _).1
          ((TorusExt.isTorusPtF_iff_isTorusPt _ _).2 (htor i s))
        have hφ : Out.DegPre.gtφ a.D₀ ℂ (Ha.ex₀ (s • Ha.P₀ (H.bar (b i) • t))).b x =
            Out.DegPre.gtφ a.D₀ ℂ (Ha.ex₀ 0).b x := by rw [(htor i s).1, h0.1]
        exact (valR_eq_mul hL ((Ha.ex₀ (s • Ha.P₀ (H.bar (b i) • t))).isGen x) ((Ha.ex₀ 0).isGen x)
          (𝟙 (Sp ℂ)) (𝟙 (Sp ℂ)) (fun k => by rw [hφ]) _ (fun z J hJ => (hv₁ x z J hJ).trans
            ((_root_.mul_one _).symm.trans (congrArg₂ (fun p q : (Sp ℂ).presheaf.stalk z => p * q) rfl
              (congrArg Units.val (hv0 x z J hJ)).symm))) j
          (by rw [hφ]; exact hj0)).2
    refine TrivSqZeroExt.ext (by simpa using hf) ?_
    rw [hd x j hj, hf, map_sum]
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, map_smul, hder,
      smul_eq_mul, xiVal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Complex.two_pi_I_ne_zero
    simp only [cf, b]
    field_simp

end GlobalTheory.ArcQ
