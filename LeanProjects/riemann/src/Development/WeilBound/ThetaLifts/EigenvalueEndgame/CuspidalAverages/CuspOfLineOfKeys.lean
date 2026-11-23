import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.AvLine
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.KillCoef
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.AeFacts
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.TowerCodimensionTwo
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictSec

noncomputable section

namespace PositivityTheory.ThKEnd.Cusp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEnd.Grp PositivityTheory.ThKEnd.Two

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d j : ℕ}
  {W : Spc F E d} {u u' : Matrix (Fin d) (Fin j) E}

open GlobalTheory.CuspRep GlobalTheory.CuspGeneric GlobalTheory.CuspRep.Generic
open scoped MatrixGroups
open PositivityTheory.ThKG

def chi (C : Ctx σ W) (ψ : AddChar (Ad E) ℂ) : AddChar (AE F E) ℂ := ψ.compAddMonoidHom C.ad.toAddMonoidHom

theorem isChar (C : Ctx σ W) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) : IsChar σ (chi C ψ) := by
  refine ⟨hψ.cont.comp C.ad_cont, fun v t => by_contra fun hn => ?_⟩
  push Not at hn
  obtain ⟨⟨s, hs⟩, -⟩ := PositivityTheory.KCo.section_statement F E σ C.cm v t
  obtain ⟨x, hx⟩ := hψ.ann (C.ad (s (1, 0))) fun c => by
    rw [← C.ad_inc, ← map_mul]
    refine hn _ (fun a ha => ?_) (by rw [map_mul, hs.snd, zero_mul])
    rw [← smul_mul_assoc, hs.at' _ a ha, zero_mul]
  rw [← C.ad_inc] at hx
  have e := C.ad.injective hx
  have h1 := hs.fst (1, 0)
  have h2 := hs.snd (1, 0)
  rw [e, (hs.inc x).1] at h1
  rw [e, (hs.inc x).2, map_eq_zero, map_eq_zero] at h2
  simp [h2] at h1

variable (C : Ctx σ W) (h : Fr (σ : E →+* E) W.J u u') {ct : (UA σ W.J → ℂ) → UA σ W.J → ℂ} (H : IsCt (colSp u) ct)
  {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ)

def wh (ct : (UA σ W.J → ℂ) → UA σ W.J → ℂ) (ψ : AddChar (Ad E) ℂ) (f : UA σ W.J → ℂ) : ℂ :=
  whit ψ (j - 1) (fun g => ct f (lev h (th C j g))) 1

include H

theorem wh_right (f : UA σ W.J → ℂ) (g : GA E j) (x) :
    wh C h ct ψ (fun z => f (z * (lev h (th C j g) * x))) = whit ψ (j - 1) (fun g => ct f (lev h (th C j g) * x)) g := by
  rw [wh, H.right, ← one_mul g, ← whit_rt]
  simp only [map_mul, mul_assoc, one_mul]

include hψ

theorem isWh : IsWh W u (chi C ψ) (wh C h ct ψ) := by
  have h0 : j - 1 < j ∨ j - 1 = 0 := by omega
  have pre : ∀ f, IsAut (W := W) f → Pre ψ (j - 1) fun g => ct f (lev h (th C j g)) := fun f hf => by
    simpa only [mul_one] using ct_pre C h H hf (ψ := ψ) 1
  refine ⟨fun f f' a b => ?_, fun c f => ?_, fun f hf s g e g1 g2 mv => ?_⟩
  · rw [wh, H.add f f' a b]; exact congrFun (whit_add' hψ _ h0 (pre f a) (pre f' b)) 1
  · rw [wh, H.smul]; exact congrFun (whit_smul _ c _) 1
  · have hd : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 (by
      rw [Matrix.det_of_upperTriangular (fun a b q => g1 a b q), Finset.prod_eq_one fun a _ => g2 a]; exact isUnit_one)
    let g' : GA E j := Matrix.GeneralLinearGroup.map C.ad.toRingHom hd.unit
    have e1 : th C j g' = hd.unit := Units.ext (Matrix.ext fun a b => C.ad.symm_apply_apply _)
    have n := par_mem h (g := hd.unit) e (mid_of_move h mv)
    have e2 : (fun x => ct f (lev h (th C j x) * s)) = fun x => ct f (lev h (th C j (x * g'))) := funext fun x => by
      rw [← ct_left C H hf (lev_norm h (th C j x) _ n) (lev h (th C j (x * g'))), map_mul, map_mul, e1]
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    rw [wh, H.right, e2, whit_rt (ψ := ψ) _ (fun x => ct f (lev h (th C j x))), one_mul, ← mul_one g',
      GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E j ψ _ (whit_pre hψ _ h0 (pre f hf)).law g' (fun a b q => (congrArg C.ad (g1 a b q)).trans (map_zero _))
        (fun a => (congrArg C.ad (g2 a)).trans (map_one _))]
    exact congrArg (fun z => ψ z * _) (map_sum C.ad _ _).symm

theorem wh_ne {f : UA σ W.J → ℂ} (hf : IsAut (W := W) f)
    (ih : ∀ r (hr : r ≤ j), 0 < r → r < j → Av σ W (colSp (fst u hr)) f 0) (h0 : ∀ x, wh C h ct ψ (fun z => f (z * x)) = 0) :
    Av σ W (colSp u) f 0 := by
  suffices e : ct f = 0 from e ▸ H.av f hf
  funext x
  have p := ct_pre C h H hf (ψ := ψ) x
  by_contra hx
  refine (whit_good hψ (j - 1) (by omega) ⟨p.cont, p.left, p.law, fun r a b g => ?_⟩).2 (fun e => hx ?_) (funext fun g => ?_)
  · simpa only [map_mul, mul_assoc] using ct_van C h H hf b (ih r _ a (by omega)) (lev h (th C j g) * x)
  · simpa using congrFun e 1
  · rw [← wh_right C h H, h0]; rfl

omit H hψ in

theorem wh_two {u u' : Matrix (Fin d) (Fin 2) E} (h : Fr (σ : E →+* E) W.J u u') {ct : (UA σ W.J → ℂ) → UA σ W.J → ℂ}
    (H : IsCt (colSp u) ct) (hψ : StdPsi ψ) {f : UA σ W.J → ℂ} (hf : IsAut (W := W) f) (hm : Mod f)
    (h1 : Av σ W (colSp (fst u one_le_two)) f 0) {x₀} {V} (hV : V ∈ 𝓝 x₀) {b : ℕ → GL (Fin 2) (AE F E)} {y : ℕ → ℂ} (b0 : b 0 = 1)
    (b1 : ∀ i, Matrix.GeneralLinearGroup.det (b i) = 1) (hy : Tendsto (fun i => ‖y i‖) atTop atTop)
    (K : ∀ x ∈ V, ∃ c : ℂ, ∀ i, wh C h ct ψ (fun z => f (z * (lev h (b i) * x))) = c * y i) : wh C h ct ψ (fun z => f (z * x₀)) = 0 := by
  obtain ⟨l1, l2, hC, -⟩ := ae_facts C.cm
  obtain ⟨s1, s2, s3⟩ := sl_facts (R := AE F E)
  letI : MeasurableSpace SL(2, AE F E) := borel _
  haveI : BorelSpace SL(2, AE F E) := ⟨rfl⟩
  letI : MeasurableSpace (UnipotentBlockColumnIndex 2 1 1 → Ad E) := borel _
  haveI : BorelSpace (UnipotentBlockColumnIndex 2 1 1 → Ad E) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, m1, m2, m3⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice _ _ (isCoLat_ratV E (UnipotentBlockColumnIndex 2 1 1))
  haveI : IsProbabilityMeasure (μ.restrict 𝓕) := ⟨by simpa using m3⟩
  have av : ∀ Φ, Per (ratV E (UnipotentBlockColumnIndex 2 1 1)) Φ → avg (ratV E (UnipotentBlockColumnIndex 2 1 1)) Φ = ∫ x, Φ x ∂μ.restrict 𝓕 := fun Φ hΦ => by
    rw [(GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average _ _ (isCoLat_ratV E _) μ 𝓕 m1 m2 Φ hΦ).2.2.2, m3]; simp
  let t₀ : UnipotentBlockColumnIndex 2 1 1 := ⟨(0, 1), by simp⟩
  haveI : Unique (UnipotentBlockColumnIndex 2 1 1) := ⟨⟨t₀⟩, by decide⟩
  let n : (UnipotentBlockColumnIndex 2 1 1 → Ad E) → SL(2, AE F E) := fun x => uni (.ofAdd (C.ad.symm (x t₀)))
  have cn : Continuous n := continuous_uni.comp ((GlobalTheory.UnitaryHeckeBaseChange.continuous_adeleEquiv_symm C.cm).comp (continuous_apply _))
  let m : SL(2, AE F E) →* UA σ W.J := (lev h).comp Matrix.SpecialLinearGroup.toGL
  have cm : Continuous m := (isLev h).1.comp Matrix.SpecialLinearGroup.continuous_toGL
  have en : ∀ x, m (n x) = lev h (th C 2 (blkU x)) := fun x => congrArg (lev h) (Units.ext (Matrix.ext fun a b => by
    change _ = C.ad.symm ((1 + posM Subtype.val x : Matrix _ _ _) a b)
    rw [Matrix.add_apply, posM_blk_apply]
    fin_cases a <;> fin_cases b <;> simp [n, uni_val, t₀]))
  have er : ∀ γ : SL(2, E), m (Matrix.SpecialLinearGroup.map (inclR (F := F) (E := E) (AF F)) γ) =
      lev h (th C 2 (ratGL E 2 (Matrix.SpecialLinearGroup.toGL γ))) := fun γ => by
    rw [th_rat]; exact congrArg (lev h) (Units.ext rfl)
  let b' : ℕ → SL(2, AE F E) := fun i => ⟨(b i).1, congrArg Units.val (b1 i)⟩
  have eb : ∀ i, m (b' i) = lev h (b i) := fun i => congrArg (lev h) (Units.ext rfl)
  have hC' : Cusp (Matrix.SpecialLinearGroup.map (n := Fin 2) (inclR (F := F) (E := E) (AF F))).range n
      (dia (GlobalTheory.Eis.Conv.halfE F E)⁻¹) := ⟨hC.siegel, fun V hV => (hC.lip V hV).imp fun η q => ⟨q.1, fun Ω hΩ => (q.2 Ω hΩ).imp
    fun D q => q.imp fun Ω' q => ⟨q.1, fun x => q.2 _⟩⟩⟩
  clear_value b' m n
  have ew : ∀ z, wh C h ct ψ (fun w => f (w * z)) = ∫ x, ψ (-dot (eLast 2 1) x) * ct f (m (n x) * z) ∂μ.restrict 𝓕 := fun z => by
    have := av _ ((ct_pre C h H hf (ψ := ψ) z).per hψ 1)
    simp only [mul_one, ← en] at this
    rw [← this, wh, H.right]
    simp only [en]
    change avg _ _ = _
    simp only [mul_one]
  obtain ⟨k, hk⟩ := (hm.av (C.good _) hf.2 (H.av f hf)).gr cm (dia (GlobalTheory.Eis.Conv.halfE F E)⁻¹) x₀
  have D : Dat (Matrix.SpecialLinearGroup.map (n := Fin 2) (inclR (F := F) (E := E) (AF F))).range n (dia (GlobalTheory.Eis.Conv.halfE F E)⁻¹)
      (μ.restrict 𝓕) 0 (fun g => ct f (m g * x₀)) 0 := by
    refine ⟨(ct_cont C H hf).comp (cm.mul continuous_const), ?_, continuous_zero, fun g => ?_, fun g => by simp⟩
    · rintro _ ⟨γ, rfl⟩ g
      rw [map_mul, mul_assoc, er, ct_rat C h H hf]
    · have p := ct_pre C h H hf (ψ := ψ) (m g * x₀)
      have := av _ (per_blk (r := 1) (m := 1) p.cont (fun c => p.left _ (isMir_blkU c)) 1)
      simp only [mul_one] at this
      rw [ct_van C h H hf le_rfl h1] at this
      simpa only [map_mul, mul_assoc, en, Pi.zero_apply] using this
  have := kill_coef hC' cn (hψ.cont.comp (continuous_dot (eLast 2 1)).neg) (fun x => (hψ.norm _).le) b' hy D hk
    (V := (fun z => m z * x₀) ⁻¹' V) (ContinuousAt.preimage_mem_nhds (f := fun z => m z * x₀) (cm.mul continuous_const).continuousAt
      (by rw [map_one, one_mul]; exact hV)) fun z hz i => by
      obtain ⟨c, hc⟩ := K _ hz
      have a0 := hc 0
      have ai := hc i
      rw [b0, map_one, one_mul, ew] at a0
      rw [ew, ← eb] at ai
      simp only [map_mul, mul_assoc, Function.comp, Pi.neg_apply]
      rw [a0, ai]; ring
  rw [ew]
  simpa only [mul_one, Function.comp, Pi.neg_apply] using this

omit C h H hψ

theorem sig_mod (hW : WeilConv) (hD : KDecay) {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (t : IsTriple B G X om om') {f : UA σ G.W.J → ℂ} (hf : f ∈ Sig B G om om') : Mod f := by
  obtain ⟨Φ, hΦ, Φ', hΦ', rfl⟩ := hf
  obtain ⟨-, C, k, h1⟩ := (hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t) (weilCondV t)).1 Φ (polData_le t.geo.hM hΦ)
  obtain ⟨-, -, C', k', h2⟩ := (hD F E σ B a a' G X om om' t).2 Φ' hΦ'.2
  refine ⟨max C 0 + max C' 0, k + k', fun x => ?_⟩
  have h3 : (1 : ℝ) ≤ ht x := by exact_mod_cast one_le_heightGL F x.1
  rw [add_mul]
  refine (norm_sub_le _ _).trans (add_le_add (((norm_integral_le_integral_norm _).trans (h1 x)).trans ?_) ((h2 x).trans ?_))
  · exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ h3 (by omega)) (by positivity) (le_max_right _ _)
  · exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ h3 (by omega)) (by positivity) (le_max_right _ _)

theorem cuspOfLine_of_keys (hW : WeilConv) (hD : KDecay) (hA : IAut) (h3 : KeyThree) (h2 : KeyTwo) : CuspOfLine := by
  intro F E _ _ _ _ _ σ B a a' G X om om' t d₁ W₁ H' hH f hf h0
  have C : Ctx σ G.W := ⟨t.base.cm, t.geo.hW.skew, PositivityTheory.ThKG.Tow.Levi.det_ne_zero t.geo.hW⟩
  have ha := sig_isAut hA t hf
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_standardAdelicAddChar E
  have key : ∀ j, ∀ u u' : Matrix (Fin (a + a')) (Fin j) E, 0 < j → Fr (σ : E →+* E) G.W.J u u' → Av σ G.W (colSp u) f 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
    intro u u' hj h
    obtain ⟨ct, H⟩ := C.ct (colSp u)
    have low : ∀ r (hr : r ≤ j), 0 < r → r < j → Av σ G.W (colSp (fst u hr)) f 0 := fun r hr p q => ih r q _ _ p (fr_fst h hr)
    match j, hj with
    | 1, _ =>
      rw [show colSp u = Submodule.span E {fun i => u i 0} from congrArg _ (Set.range_unique (f := fun k i => u i k))]
      refine av_line C hH ha h0 (fun e => ?_) ?_
      · have := congrFun (congrFun h.vu 0) 0
        simp [Matrix.mul_apply, show ∀ i, u i 0 = 0 from congrFun e] at this
      · have := congrFun (congrFun h.uu 0) 0
        rwa [Matrix.mul_assoc] at this
    | 2, _ =>
      refine wh_ne C h H hψ ha low fun x => ?_
      obtain ⟨V, hV, b, y, p1, p2, p3, p4⟩ := h2 F E σ B a a' G X om om' t u u' ⟨h.uu, h.vv, h.uv⟩ _ (isLev h) _ _ (isChar C hψ)
        (isWh C h H hψ) f hf x
      exact wh_two C h H hψ ha (sig_mod hW hD t hf) (low 1 _ one_pos one_lt_two) hV p1 p2 p3 p4
    | j + 3, _ =>
      exact wh_ne C h H hψ ha low (h3 F E σ B a a' G X om om' t j u u' ⟨h.uu, h.vv, h.uv⟩ _ _ (isChar C hψ) (isWh C h H hψ) f hf)
  intro U hU hi
  obtain ⟨u, u', e, h⟩ := C.frame U hi
  exact C.int_zero (e ▸ key _ u u' (Nat.pos_of_ne_zero fun q => hU (Submodule.finrank_eq_zero.1 q)) h)

end PositivityTheory.ThKEnd.Cusp

end
