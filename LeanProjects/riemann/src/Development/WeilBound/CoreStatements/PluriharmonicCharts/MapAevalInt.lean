import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorEmpty
import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsBlockMapInitialVertex
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem PositivityTheory.Xgp.c_algsq.LC.map_aeval_int {σ S T : Type} [CommRing S] [CommRing T] {_ : Algebra ℤ S} {_ : Algebra ℤ T}
    (θ : S →+* T) (w : σ → S) (f : MvPolynomial σ ℤ) : θ (aeval w f) = aeval (fun q => θ (w q)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [aeval_C, aeval_C, eq_intCast, eq_intCast, map_intCast]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p q hp => rw [map_mul, map_mul, hp, aeval_X, map_mul, aeval_X]

open PositivityTheory.Xgp.c_algsq.LC GlobalTheory.CompanionTheory.Ar.PB.WSq.Pts GlobalTheory.CompanionTheory.Ar.PB.CPts GlobalTheory.CompanionTheory.Ar.PB.ValRing in
set_option maxHeartbeats 1000000 in
theorem PositivityTheory.Xgp.c_algsq.lc : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ (g h : MRing fun o : Option K => ι (o.getD k₀)) (dg dh : Option K → ℕ), IsMultiHomog g dg → IsMultiHomog h dh → (∀ o : Option K, (dg o : ℤ) - dh o = o.elim 1 fun k => -(fun k => ∑ p, xiCoef τ a p * M.dy p k) k - (if M.blk (τ, a) = some k then 1 else 0)) → aeval (M.wCo (τ, a) k₀ ca cb RatFunc.X) g = RatFunc.X * algebraMap Φ (RatFunc Φ) (∏ p, (if IsProperStep N j p.2 then 1 else algebraMap M.Ω Φ (M.lam p) * (if (p.2 : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (M.g p.1) (wIdx N j) (wIdx N j) else 1) else minorIJ (M.g p.1) (omIdx N j) (omIdx N j))) ^ xiCoef τ a p) * aeval (M.wCo (τ, a) k₀ ca cb RatFunc.X) h → ∀ z ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)), ∀ F, M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk (fstPt k₀ z))) → ∀ (hm : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), IsBlockDiag j hm → hm.det ≠ 0 → (∀ i, M.ExactAt F (τ, i) (fstPt k₀ z) hm) → M.ExactAt F (τ, a) (sndPt k₀ z) (hm * (1 + Matrix.single cb ca t)) → eval z (map (Int.castRingHom ℂ) g) = t * (∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk (fstPt k₀ z)) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ hm (wIdx N j) (wIdx N j) else 1) else minorIJ hm (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)) * eval z (map (Int.castRingHom ℂ) h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M d τ a b k₀ ca cb hb hab hk hca hcb _ g h dg dh hg hh hdeg hq z hz F hF hG hm t hmb hmd
    hex hex'
  have hS := same_summand hb hab hca hcb
  have hsnd := basePart_snd M hk z
  have hz0 : fstPt k₀ z ∈ mcPts (mCoordIdeal y) :=
    comp_mem_mcPts (isBlockMap_v₀ k₀) (algebraMap Φ (RatFunc Φ)) rfl hz
  have hzb := base_mem M hz0
  obtain ⟨H0, hH0⟩ := flag_fwd M hF hz0 hG (hex a).1
  let hh' : Ψ → Matrix (Fin N) (Fin N) ℂ := Function.update H0 τ hm
  have hτ : hh' τ = hm := Function.update_self ..
  have hblk : ∀ τ', IsBlockDiag j (hh' τ') := fun τ' => by
    by_cases e : τ' = τ
    · rw [e, hτ]; exact hmb
    · simp only [hh', Function.update_of_ne e]; exact (hH0.2.1 τ').1
  let zb := basePart M.blk (fstPt k₀ z)
  have hfl : ∀ p k, M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ (p.1 = τ → α = 1) ∧ ∀ m : ι k,
      fstPt k₀ z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ (hh' p.1) I (stepCols N j p.2) := by
    rintro ⟨τ', i⟩ k hp
    by_cases e : τ' = τ
    · subst e
      exact ⟨1, one_ne_zero, fun _ => rfl, fun m => by rw [one_mul, hτ]; exact (hex i).2 k hp m⟩
    · obtain ⟨α, hα, h1⟩ := hH0.2.2 _ k hp
      exact ⟨α, hα, fun e' => absurd e' e, fun m => by simp only [hh', Function.update_of_ne e]; exact h1 m⟩
  let A := regRing M.x zb
  let val : A →+* ℂ := regVal hzb
  obtain ⟨L, R, _, _, φ, θ, U, s, i, ρ, cA, B, sR, hi, hθ, hU, hU0, hθX, hic, hρc, hBb, hBi, hBρ, his, hρs⟩ :=
    GlobalTheory.T.generic_flag_elementary_twist M.Ω Φ Ψ N j M.g F.T A val hh' t τ ca cb hcb hS M.g_block M.g_indep hF.1 hblk
  let am := algebraMap M.Ω Φ
  let φΩ : M.Ω →+* L := φ.comp am
  let uA : (Σ k, ι k) → Finset (Fin N) → A := fun q I => ⟨F.u q I, exists_isValueAt hzb (hG.2.1 q I).1⟩
  have hxp : ∀ p, φΩ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') ≠ 0 := fun p => (map_ne_zero _).2
    (Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (M.x_chart_ne (mCoordIdeal_le hzb) hG k'))
  have hdt : ∀ p : Ψ × Fin N, φΩ (detFac j p.2 (F.T p.1)) ≠ 0 := fun p => (map_ne_zero _).2
    (detFac_ne_zero M.j_le p.2 (hF.1 p.1).1 (hF.1 p.1).2)
  have hTg : ∀ τ', (F.T τ').map φΩ * (B τ').map i = (M.g τ').map φ * U τ' := fun τ' => by
    rw [hBi]
    exact map_mul_inv_map _ (hF.1 τ').2 _
  have hstep : ∀ (i₀ : Fin N) (k : K) (D : Matrix (Fin N) (Fin N) R) (c₀ c₁ : L) (W : ι k → L) (α : ℂ) (zz : ι k → ℂ),
      c₀ ≠ 0 → α ≠ 0 →
      (∀ m, c₀ * W m = c₁ * ∑ I, φΩ (F.u ⟨k, m⟩ I) * minorIJ (D.map i) I (stepCols N j i₀)) →
      (∀ m, zz m = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ (D.map ρ) I (stepCols N j i₀)) →
      ∃ (sv : ι k → R), (∀ m, W m = c₁ / c₀ * i (sv m)) ∧ ∀ m, ρ (sv m) = α⁻¹ * zz m := by
    intro i₀ k D c₀ c₁ W α zz h0 hα hW hz
    refine ⟨fun m => ∑ I, cA (uA ⟨k, m⟩ I) * minorIJ D I (stepCols N j i₀), fun m => ?_, fun m => ?_⟩
    · have e1 : i (∑ I, cA (uA ⟨k, m⟩ I) * minorIJ D I (stepCols N j i₀)) =
          ∑ I, φΩ (F.u ⟨k, m⟩ I) * minorIJ (D.map i) I (stepCols N j i₀) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [map_mul, hic, minorIJ_map]
        rfl
      rw [e1, div_mul_eq_mul_div, ← hW m]
      field_simp
    · rw [map_sum, hz m, inv_mul_cancel_left₀ hα]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [map_mul, hρc, ← minorIJ_map]
      rfl
  obtain ⟨V, hVb, hVt, hVd, hV⟩ := GlobalTheory.T.elementary_factor_commutation L N j ca cb (U τ) (θ RatFunc.X) s hcb hS (hU τ).1 (hU τ).2.1
    (hU τ).2.2 hU0 hθX
  have hcbS : cb ∉ stepCols N j a := by
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold lastCol at hca
    split_ifs at hca ⊢ <;> omega
  have hVp : (∏ c ∈ stepCols N j a, V c c) ≠ 0 := Finset.prod_ne_zero_iff.2 fun c hc =>
    hVd c fun e => hcbS (e ▸ hc)
  have hUp : ∀ p : Ψ × Fin N, (∏ c ∈ stepCols N j p.2, U p.1 c c) ≠ 0 := fun p =>
    Finset.prod_ne_zero_iff.2 fun c _ => (hU p.1).2.2 c
  have key : ∀ o : Option K, ∃ (e : L) (t' : ℂ) (sv : ι (o.getD k₀) → R), e ≠ 0 ∧ t' ≠ 0 ∧
      (∀ m, θ (M.wCo (τ, a) k₀ ca cb RatFunc.X ⟨o, m⟩) = e * i (sv m)) ∧ (∀ m, ρ (sv m) = t' * z ⟨o, m⟩) ∧
      (o = none → e = φΩ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, a) k') /
        (φΩ (detFac j a (F.T τ)) * ∏ c ∈ stepCols N j a, V c c) ∧ t' = 1) ∧
      (∀ kb : NonPluckerBlocks M.blk, o = some kb.1 → e = φΩ (M.x ⟨kb, F.c kb⟩) ∧ t' = 1) ∧
      ∀ p k, o = some k → M.blk p = some k → e = φΩ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') /
        (φΩ (detFac j p.2 (F.T p.1)) * ∏ c ∈ stepCols N j p.2, U p.1 c c) ∧ (p.1 = τ → t' = 1) := by
    intro o
    cases o with
    | some k =>
      have hw : ∀ m : ι k, θ (M.wCo (τ, a) k₀ ca cb RatFunc.X ⟨some k, m⟩) = φ (y ⟨k, m⟩) := fun m => hθ _
      by_cases hkb : ∀ p, M.blk p ≠ some k
      · let kb : NonPluckerBlocks M.blk := ⟨k, hkb⟩
        have hxc : M.x ⟨kb, F.c kb⟩ ≠ 0 := M.x_chart_ne (mCoordIdeal_le hzb) hG kb
        have hzc : zb ⟨kb, F.c kb⟩ = 1 := (hex a).1 kb
        have hv : ∀ m : ι k, IsValueAt M.x (M.x ⟨kb, m⟩ / M.x ⟨kb, F.c kb⟩) zb (zb ⟨kb, m⟩ / zb ⟨kb, F.c kb⟩) := fun m =>
          isValueAt_ratio hxc (by rw [hzc]; exact one_ne_zero)
        refine ⟨φΩ (M.x ⟨kb, F.c kb⟩), 1, fun m => cA ⟨_, _, hv m⟩, (map_ne_zero _).2 hxc, one_ne_zero, fun m => ?_,
          fun m => ?_, fun e => (by cases e), fun kb' e => ?_, fun p k' e hp => ?_⟩
        · refine (hw m).trans ?_
          rw [hic, show y ⟨k, m⟩ = am (M.x ⟨kb, m⟩) from M.y_base ⟨kb, m⟩]
          show φ (am _) = φ (am _) * φ (am _)
          rw [← map_mul, ← map_mul]
          congr 2
          exact (mul_div_cancel₀ _ hxc).symm
        · rw [hρc, show val ⟨_, _, hv m⟩ = _ from regVal_eq hzb _ (hv m), hzc, div_one, one_mul]
          rfl
        · obtain rfl : kb = kb' := Subtype.ext (Option.some.inj e)
          exact ⟨rfl, rfl⟩
        · exact absurd (hp.trans e.symm) (hkb p)
      · push Not at hkb
        obtain ⟨p, hp⟩ := hkb
        obtain ⟨α, hα, hα1, hz⟩ := hfl p k hp
        obtain ⟨sv, h1, h2⟩ := hstep p.2 k (B p.1) (φΩ (detFac j p.2 (F.T p.1)) * ∏ c ∈ stepCols N j p.2, U p.1 c c)
          (φΩ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k')) (fun m => φ (y ⟨k, m⟩)) α (fun m => fstPt k₀ z ⟨k, m⟩)
          (mul_ne_zero (hdt p) (hUp p)) hα
          (fun m => frame_gen M hF φ hp m ((hBb p.1).map i) (hU p.1).1 (hU p.1).2.1 (hTg p.1))
          (fun m => by rw [hBρ]; exact hz m)
        refine ⟨_, α⁻¹, sv, div_ne_zero (hxp p) (mul_ne_zero (hdt p) (hUp p)), inv_ne_zero hα,
          fun m => (hw m).trans (h1 m), h2, fun e => (by cases e), fun kb e => ?_, fun p' k' e hp' => ?_⟩
        · exact absurd (hp.trans e) (kb.2 p)
        · obtain rfl := M.blk_inj _ _ _ hp (hp'.trans e.symm)
          exact ⟨rfl, fun e' => by rw [hα1 e', _root_.inv_one]⟩
    | none =>
      have hz1 := hex'.2 k₀ hk
      rw [hsnd] at hz1
      have hEi : (1 + Matrix.single cb ca sR).map i = 1 + Matrix.single cb ca s := by
        rw [transv_map, his]
      have hEρ : (1 + Matrix.single cb ca sR).map ρ = 1 + Matrix.single cb ca t := by
        rw [transv_map, hρs]
      have hEθ : ((M.g τ).map (algebraMap Φ (RatFunc Φ)) * (1 + Matrix.single cb ca RatFunc.X)).map θ =
          (M.g τ).map φ * (1 + Matrix.single cb ca (θ RatFunc.X)) := by
        rw [Matrix.map_mul, transv_map]
        congr 1
        ext r c
        exact hθ _
      obtain ⟨sv, h1, h2⟩ := hstep a k₀ (B τ * (1 + Matrix.single cb ca sR))
        (φΩ (detFac j a (F.T τ)) * ∏ c ∈ stepCols N j a, V c c) (φΩ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, a) k'))
        (fun m => θ (M.wCo (τ, a) k₀ ca cb RatFunc.X ⟨none, m⟩)) 1 (fun m => z ⟨none, m⟩)
        (mul_ne_zero (hdt (τ, a)) hVp) one_ne_zero (fun m => by
          have e1 : θ (M.wCo (τ, a) k₀ ca cb RatFunc.X ⟨none, m⟩) = ∑ I, φΩ (M.coef ⟨k₀, m⟩ I) *
              minorIJ ((M.g τ).map φ * (1 + Matrix.single cb ca (θ RatFunc.X))) I (stepCols N j a) := by
            show θ (∑ I, _) = _
            rw [map_sum]
            refine Finset.sum_congr rfl fun I _ => ?_
            rw [map_mul, hθ, ← hEθ, minorIJ_map]
            rfl
          rw [e1]
          exact frame_any M hF φΩ (p := (τ, a)) hk m (G := (B τ * (1 + Matrix.single cb ca sR)).map i)
            (bb := V) (gg := (M.g τ).map φ * (1 + Matrix.single cb ca (θ RatFunc.X)))
            ((hBb τ).mul (transv_block hS sR) |>.map i) hVb hVt (by
              rw [Matrix.map_mul, hEi]
              show (F.T τ).map φΩ * ((B τ).map i * _) = _
              rw [← Matrix.mul_assoc, hTg, Matrix.mul_assoc, ← hV, Matrix.mul_assoc]))
        (fun m => by
          rw [Matrix.map_mul, hBρ, hEρ, ← snd_self z m, one_mul, hτ]
          exact hz1 m)
      exact ⟨_, 1⁻¹, sv, div_ne_zero (hxp (τ, a)) (mul_ne_zero (hdt (τ, a)) hVp), by simp, h1, h2,
        fun _ => ⟨rfl, _root_.inv_one⟩, fun kb e => (by cases e), fun p k e => (by cases e)⟩
  choose e t' sv he ht has hv k1 k2 k3 using key
  have hprop : ∀ p, ¬ IsProperStep N j p.2 → M.blk p = none := fun p hp => (M.blk_none p).2 hp
  let υA : Fin N → A := fun i₀ => if hp : IsProperStep N j i₀ then 0 else
    ⟨F.υ (τ, i₀), exists_isValueAt hzb (hG.2.2 (τ, i₀) (hprop (τ, i₀) hp)).2.1⟩
  let FR : Fin N → R := fun i₀ => if IsProperStep N j i₀ then 1 else cA (υA i₀) * facM j a (B τ) i₀
  have hFi : ∀ i₀, i (FR i₀) =
      if IsProperStep N j i₀ then 1 else φΩ (F.υ (τ, i₀)) * facM j a ((B τ).map i) i₀ := fun i₀ => by
    simp only [FR, υA]
    split_ifs with hp
    · exact map_one i
    · rw [map_mul, hic, facM_map]; rfl
  have hFρ : ∀ i₀, ρ (FR i₀) =
      if IsProperStep N j i₀ then 1 else valAt M.x (F.υ (τ, i₀)) zb * facM j a hm i₀ := fun i₀ => by
    simp only [FR, υA]
    split_ifs with hp
    · exact map_one ρ
    · rw [map_mul, hρc, ← facM_map, hBρ, hτ]; rfl
  let Ft : R := (∏ i₀ : Fin N, if (i₀ : ℕ) + 1 = a then FR i₀ else 1) * FR b
  have hmapF : ∀ {S : Type} [CommRing S] (f : R →+* S), f Ft =
      (∏ i₀ : Fin N, if (i₀ : ℕ) + 1 = a then f (FR i₀) else 1) * f (FR b) := fun f => by
    simp only [Ft, map_mul, map_prod, apply_ite f, map_one]
  let sq : (Σ o : Option K, ι (o.getD k₀)) → R := fun q => sv q.1 q.2
  have ev1 : ∀ (f : MRing fun o : Option K => ι (o.getD k₀)) (df : Option K → ℕ), IsMultiHomog f df →
      θ (aeval (M.wCo (τ, a) k₀ ca cb RatFunc.X) f) = (∏ o, e o ^ df o) * i (aeval sq f) := fun f df hf => by
    rw [map_aeval_int i, ← PositivityTheory.Xgp.W.aeval_scale' e _ hf, map_aeval_int θ]
    congr 2
    funext q
    exact has q.1 q.2
  have ev2 : ∀ (f : MRing fun o : Option K => ι (o.getD k₀)) (df : Option K → ℕ), IsMultiHomog f df →
      ρ (aeval sq f) = (∏ o, t' o ^ df o) * eval z (map (Int.castRingHom ℂ) f) := fun f df hf => by
    rw [PositivityTheory.Xgp.W.eval_map_eq_aeval, ← PositivityTheory.Xgp.W.aeval_scale' t' _ hf, map_aeval_int ρ]
    congr 2
    funext q
    exact hv q.1 q.2
  have hd1 := prod_deg M hk e he hdeg
  have hd2 := prod_deg M hk t' ht hdeg
  have hbase : ∀ p, (∏ k : NonPluckerBlocks M.blk, e (some k.1) ^ M.b p k) = φΩ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') := fun p => by
    rw [map_prod]
    exact Finset.prod_congr rfl fun k _ => by rw [(k2 _ k rfl).1, map_zpow₀]
  rw [(k1 _ rfl).2, (k3 _ (τ, a) k₀ rfl hk).2 rfl, prod_xi' τ, Finset.prod_eq_one (s := Finset.univ)
    (f := fun i₀ : Fin N => _ ^ xiCoef τ a (τ, i₀)) (fun i₀ _ => by
      rw [Finset.prod_eq_one fun k _ => by rw [(k2 _ k rfl).2, _root_.one_zpow]]
      cases hp : M.blk (τ, i₀) with
      | none => simp
      | some k => simp [(k3 _ (τ, i₀) k rfl hp).2 rfl]), mul_one, mul_one, mul_one] at hd2
  have hq' := congrArg θ hq
  rw [map_mul, map_mul, ev1 g dg hg, ev1 h dh hh, hθ, map_prod] at hq'
  simp only [map_zpow₀] at hq'
  rw [prod_xi' τ] at hq' hd1
  have hsc := scal_main τ M.j_le hb hab hca hcb ((hF.1 τ).1.map φΩ) (by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero _).2 (hF.1 τ).2) ((hBb τ).map i)
    (hU τ).1 (hU τ).2.1 (hU τ).2.2 (hTg τ) hθX hV fun i₀ => φΩ (F.υ (τ, i₀))
  simp only [← hFi, ← hmapF i, detFac_map] at hsc
  have hterm : ∀ i₀ : Fin N, (if IsProperStep N j i₀ then (φΩ (detFac j i₀ (F.T τ)) * ∏ c ∈ stepCols N j i₀, U τ c c)⁻¹
      else φΩ (F.υ (τ, i₀)) / φΩ (detFac j i₀ (F.T τ)) * facM j a ((M.g τ).map φ) i₀) =
      φ (if IsProperStep N j i₀ then 1 else am (M.lam (τ, i₀)) * facM j a (M.g τ) i₀) *
        ((∏ k : NonPluckerBlocks M.blk, e (some k.1) ^ M.b (τ, i₀) k)⁻¹ * (M.blk (τ, i₀)).elim 1 fun k => e (some k)) := by
    intro i₀
    have q1 := hxp (τ, i₀)
    have q2 : φΩ (detFac j i₀ (F.T τ)) ≠ 0 := hdt (τ, i₀)
    have q3 : (∏ c ∈ stepCols N j i₀, U τ c c) ≠ 0 := hUp (τ, i₀)
    rw [hbase]
    split_ifs with hp
    · cases hp' : M.blk (τ, i₀) with
      | none => exact absurd hp ((M.blk_none _).1 hp')
      | some k =>
        rw [Option.elim, (k3 _ (τ, i₀) k rfl hp').1, map_one]
        field_simp
    · have h1 := congrArg φΩ (hF.2.2.2 (τ, i₀) (hprop _ hp))
      rw [map_mul, map_mul] at h1
      rw [hprop (τ, i₀) hp, Option.elim, map_mul, facM_map]
      change _ = φΩ _ * _ * _
      have h2 : φΩ (F.υ (τ, i₀)) = φΩ (detFac j i₀ (F.T τ)) * φΩ (M.lam (τ, i₀)) /
          φΩ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, i₀) k') := by
        rw [eq_div_iff q1, mul_comm]; exact h1.symm
      rw [h2]
      field_simp
  simp only [hterm, mul_zpow, Finset.prod_mul_distrib] at hsc
  simp only [mul_zpow, Finset.prod_mul_distrib] at hd1
  rw [(k1 _ rfl).1, (k3 _ (τ, a) k₀ rfl hk).1] at hd1
  dsimp only at hd1
  change _ = θ RatFunc.X * (∏ i₀ : Fin N, φ (if IsProperStep N j i₀ then 1 else
    am (M.lam (τ, i₀)) * facM j a (M.g τ) i₀) ^ xiCoef τ a (τ, i₀)) * _ at hq'
  have hR : aeval sq g = sR * Ft * aeval sq h := by
    apply hi
    rw [map_mul, map_mul, his, ← hsc]
    have q0 : (∏ o, e o ^ dg o) ≠ 0 := Finset.prod_ne_zero_iff.2 fun o _ => pow_ne_zero _ (he o)
    have q1 := hxp (τ, a)
    have q2 : φΩ (detFac j a (F.T τ)) ≠ 0 := hdt (τ, a)
    have q3 : (∏ c ∈ stepCols N j a, U τ c c) ≠ 0 := hUp (τ, a)
    refine mul_left_cancel₀ q0 (hq'.trans ?_)
    have hd3 := eq_div_of_mul_eq (div_ne_zero q1 (mul_ne_zero q2 hVp)) hd1
    rw [hd3]
    generalize (∏ i₀ : Fin N, φ (if IsProperStep N j i₀ then 1 else
      am (M.lam (τ, i₀)) * facM j a (M.g τ) i₀) ^ xiCoef τ a (τ, i₀)) = P1
    generalize φΩ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, a) k') = X1 at q1 ⊢
    generalize φΩ (detFac j a (F.T τ)) = X2 at q2 ⊢
    field_simp
  have hfin := congrArg ρ hR
  rw [map_mul, map_mul, ev2 g dg hg, ev2 h dh hh, hd2, hρs, hmapF ρ] at hfin
  simp only [hFρ] at hfin
  have q0 : (∏ o, t' o ^ dg o) ≠ 0 := Finset.prod_ne_zero_iff.2 fun o _ => pow_ne_zero _ (ht o)
  have hpa : IsProperStep N j a := by
    by_contra hp
    rw [hprop (τ, a) hp] at hk
    cases hk
  rw [prod_xi τ hb, if_pos hpa, _root_.inv_one, one_pow, mul_one]
  refine mul_left_cancel₀ q0 (hfin.trans ?_)
  unfold facM
  ring
