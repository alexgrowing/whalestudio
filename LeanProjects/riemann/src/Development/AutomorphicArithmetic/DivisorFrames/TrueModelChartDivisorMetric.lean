import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AutomorphicArithmetic.DivisorFrames.ExistsAdaptedFlagCharts
import Development.AutomorphicArithmetic.DivisorFrames.ChartFrameDivisor
import Development.AutomorphicArithmetic.DivisorFrames.FlagLineMetricExpBound
import Development.AutomorphicArithmetic.DivisorFrames.GrSqTransposeInverse
import Development.AutomorphicArithmetic.DivisorFrames.TrueModelChartDivisor
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem grSq_lie {r : ℕ} (dual : Bool) {N Q : Matrix (Fin r) (Fin r) ℂ} (hN : N.PosDef) (hQ : IsUnit Q.det)
    (hT : IsTri ((lieMat dual Q).submatrix (pos dual) id)) (hd : ∀ a, lieMat dual Q (pos dual a) a ≠ 0) (i : Fin r) :
    GlobalTheory.GradedNorm.grSq (cond dual (Qᴴ * N * Q)⁻¹ (Qᴴ * N * Q)ᵀ) i =
      ‖lieMat dual Q (pos dual i) i‖ ^ 2 * GlobalTheory.GradedNorm.grSq N (pos dual i) ^ (cond dual (-1) 1 : ℤ) := by
  have hX : (Qᴴ * N * Q).PosDef :=
    hN.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 hQ))
  cases dual
  · simp only [cond_false, zpow_one]
    rw [(UpperTheory.grSq_transpose_inverse r _ hX i).1]
    exact GlobalTheory.GradedNorm.grSq_tri N hT hd i
  · simp only [cond_true, _root_.zpow_neg, zpow_one]
    have e : (Qᴴ * N * Q)⁻¹ᵀ = ((lieMat true Q).submatrix (pos true) id)ᴴ * ((Nᵀ)⁻¹).submatrix Fin.rev Fin.rev *
        (lieMat true Q).submatrix (pos true) id := by
      change _ = ((Q⁻¹)ᵀ.submatrix Fin.rev id)ᴴ * _ * (Q⁻¹)ᵀ.submatrix Fin.rev id
      rw [conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ Fin.rev _ Fin.rev_bijective,
        ← Matrix.submatrix_mul _ _ _ Fin.rev _ Fin.rev_bijective, submatrix_id_id, Matrix.mul_inv_rev,
        Matrix.mul_inv_rev, transpose_mul, transpose_mul, ← conjTranspose_nonsing_inv, ← transpose_nonsing_inv N]
      rfl
    rw [← (UpperTheory.grSq_transpose_inverse r _ hX.inv i).1, e, GlobalTheory.GradedNorm.grSq_tri _ hT hd i, (UpperTheory.grSq_transpose_inverse r _ hN.transpose i).2,
      (UpperTheory.grSq_transpose_inverse r _ hN i.rev).1]
    rfl

theorem UpperTheory.true_model_chart_divisor_metric :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (N : GlobalTheory.TrueGeo.Model C.Y) (τ : E →+* ℂ) (M : N.X.Modules) (dual : Bool) (A : Chart M (Dw.mult τ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) C.Y.Fn) (fl : Vert.Flag M (Dw.mult τ)) (i : Fin (Dw.mult τ)) (s : ((fl.root i).pull N.j).ι → C.Y.Fnˣ) (kind : ℕ → Bool) (Ro : Option ℝ) (w : Pad.Sym E →₀ ℤ), w = Finsupp.single (kind, Ro, Sum.inl (τ, (pos dual i : ℕ))) (cond dual (-1) 1) → IsLie C.f0 τ N.j dual A → IsFlag (genericPt C.Y ≫ N.j) dual A fl → IsGrSec N.j dual A fl i s → ∀ (G : ∀ σ : c.F →+* ℂ, EigMet Z σ) (h : VMetric N.p M (Dw.mult τ)) (hh : h.IsCInf), IsMet C.f0 τ N.j dual A G h → ∀ (σ : F →+* ℂ) (y : Pts C.Y σ) (y' : CxPts N.p (σ.comp (algebraMap (𝓞 F) F))) (k : ((fl.root i).pull N.j).ι), y'.1 = y.1 ≫ N.j → under y ∈ ((fl.root i).pull N.j).U k → (C.met (G (embOf e σ)) (expo Dw w)).h (s k) y = Real.exp (-((VMetric.grLB fl i hh).φ _).φ (k PUnit.unit) y') := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e C N τ M dual A fl i s kind Ro w hw hL hF hG G h hh hM σ y y' k hy' hk
  classical
  have hP : Presents (divOf C (expo Dw w)) ((fl.root i).pull N.j) s :=
    ⟨Semi.LB.isLB_linComb ((VMetric.grLB fl i hh).φ (σ.comp (algebraMap (𝓞 F) F))).isLB _ _, hG.1,
      UpperTheory.true_model_chart_divisor E H Dw l Xo c O β Z F e C N τ M dual A fl i s kind Ro w hw hL hF hG⟩
  obtain ⟨ch, hch, had⟩ := (UpperTheory.exists_adapted_flag_charts _ M _ fl).1 (N.j (Var.base y))
  obtain ⟨t₀, ht₀⟩ := had i
  have hfr := (UpperTheory.exists_adapted_flag_charts _ M _ fl).2 ch had i t₀ ht₀
  have h1 := hG.2 ch had (gen_le N.j hch) t₀ ht₀ hfr
  have hb : y'.1 (IsLocalRing.closedPoint ℂ) = N.j (Var.base y) := by rw [hy']; rfl
  have hz : y' ∈ CxPts.ptsIn N.p _ ch.U := CxPts.mem_ptsIn.2 (hb ▸ hch)
  have h0 := UpperTheory.flag_line_metric_exp_bound _ _ N.p M _ h hh fl ch had i t₀ ht₀ hfr _ y' hz
  let gc : ((fl.root i).pull N.j).ι := fun _ => (⟨ch.U, _, hfr⟩ : Chart (fl.gr i) 1)
  have hgc : y ∈ CxPts.ptsIn C.Y.str σ (((fl.root i).pull N.j).U gc) :=
    Var.mem_ptsIn_iff.2 (Set.mem_iInter.2 fun _ => hch)
  have hk' : y ∈ CxPts.ptsIn C.Y.str σ (((fl.root i).pull N.j).U k) := Var.mem_ptsIn_iff.2 hk
  have hm : ∀ _ : PUnit.{1}, y'.1 = y.1 ≫ N.j := fun _ => hy'
  have hk'' := CxPts.mem_of_mem_linComb (m := fun _ => y') hm hk' PUnit.unit
  have hgv := CxPts.gv_linComb (m := fun _ => y') hm hgc hk'
  rw [Fintype.prod_unique, zpow_one] at hgv
  have htr := ((VMetric.grLB fl i hh).φ _).trans (gc PUnit.unit) (k PUnit.unit) y' hz hk''
  have hne := CxPts.gv_ne_zero (B := (VMetric.grLB fl i hh).B) (i := gc PUnit.unit) hz hk''
  have eg := Var.ptsIn_subset_eqnSet hP gc hgc
  rw [(C.met _ _).trans _ _ y (Var.ptsIn_subset_eqnSet hP k hk') eg, Var.tv_eq_gv hP hgc hk', htr, neg_sub, sub_eq_add_neg,
    Real.exp_add, Real.exp_log (pow_pos (norm_pos_iff.2 hne) 2)]
  refine congrArg₂ (· * ·) (congrArg (‖·‖ ^ 2) hgv) (Eq.trans ?_ h0.symm)
  obtain ⟨⟨t, g₀⟩, -, φ, f, hT, hb₀⟩ := C.exists_adapted y
  obtain ⟨g, hg⟩ := f.exists_isMap (Var.evStalk y) hb₀.2.1 hb₀.1
  have hA : C.Adapted y t g 1 := ⟨φ, f, hT, hg.tri hb₀.2.1 hb₀.1⟩
  obtain ⟨φ', f', hf'⟩ := hL.2 ch (Var.base y) hch
  have hφ : φ = φ' := RingHom.ext fun a => toFn_injective _
    ((RingHom.congr_fun hT.2.1 a).symm.trans (RingHom.congr_fun hf'.1 a))
  subst hφ
  obtain ⟨g', hg'⟩ := f'.exists_isMap (Var.evStalk y) hb₀.2.1 hb₀.1
  obtain ⟨h2, h3⟩ := UpperTheory.chart_frame_divisor E H Dw l Xo c O β Z F e C τ _ N.j M dual A fl hL hF ch had _ hch φ f f' t hT hf'
  have hQ : lieMat dual (g.co g' τ) = (lieMat dual (f.co f' τ)).map (Var.evStalk y) := by
    rw [hg.co τ hg' hb₀.1, lieMat_map _ _ (f.isUnit_det_co f' τ)]
  rw [hM ch σ y y' hy' hz φ f' hf' (C.down y) rfl g' hg', (G _).change _ g g' τ,
    grSq_lie dual ((G _).pos _ g τ) (g.isUnit_det_co g' τ)
      (fun a b hab => by rw [submatrix_apply, hQ, map_apply]; exact (congrArg _ (h2 a b hab)).trans (map_zero _))
      (fun a => by rw [hQ, map_apply]; exact (Var.evStalk_ne_zero_iff _).2 (h3 a).1), hQ, map_apply,
    (C.met _ _).trans _ _ y eg (FlagCpt.prodPow_mem _ hA.mem_eqnSet), FlagCpt.met_h _ _ hA]
  let x : Letter Dw := ⟨τ, pos dual i⟩
  have hx : letterOf Dw (.inl (τ, (pos dual i : ℕ))) = some x := dif_pos x.2.2
  have e₁ : expo Dw w x = cond dual (-1) 1 := by simp [hw, expo, hx]
  have e₂ : ∀ z, z ≠ x → expo Dw w z = 0 := fun z hz => by simp [hw, expo, hx, hz.symm]
  have e₃ : prodPow t (expo Dw w) = t τ (pos dual i) ^ (cond dual (-1) 1 : ℤ) := by
    rw [prodPow, Finset.prod_eq_single x (fun z _ hz => by rw [e₂ z hz, zpow_zero]) (by simp), e₁]
  rw [FlagCpt.genSq, Finset.prod_eq_single x (fun z _ hz => by rw [e₂ z hz, zpow_zero]) (by simp), e₁, e₃, Var.tv,
    div_eq_mul_inv, ← eq_inv_of_mul_eq_one_right h1, mul_comm _ (A ch _ _), (h3 i).2, (Var.hasVal_cx_stalk _).val_eq]
  simp [prodPow, x]
