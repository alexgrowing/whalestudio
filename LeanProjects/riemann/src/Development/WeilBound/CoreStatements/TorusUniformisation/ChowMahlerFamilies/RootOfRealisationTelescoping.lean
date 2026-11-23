import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.PointsIntegralSmallLimit
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.RealisationRoots

open ReciprocityTheory.AnForm.M

section Gen

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}

theorem pts_neg_congr (P : Ideal (MRing ι)) {e : ℕ}
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) {g g' : ((Σ k, ι k) → ℂ) → ℝ} (h : ∀ z ∈ mcPts P, g z = -g' z) :
    ptsIntegral P φ g = -ptsIntegral P φ g' := by
  have key : ∀ Ψ y w, sheetDensity P Ψ φ g y w = -sheetDensity P Ψ φ g' y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs with hγ
    · rw [h _ hγ.choose_spec.2.self_of_nhds.2.1, neg_mul]
    · exact neg_zero.symm
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    simp only [key, finsum_neg_distrib, MeasureTheory.integral_neg]
  · exact neg_zero.symm

theorem h_inv_of_deg {G : HermLine ι} (hG : G.a = 0) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    G.h (fun p => c p.1 * z p) = G.h z := by
  rw [G.smul c z hc, hG]
  simp

theorem smooth_log {G : HermLine ι} (hG : IsSmoothHerm G) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Real.log (G.h z)) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
  ContDiffOn.log hG fun z hz => (G.pos z hz).ne'

theorem continuous_log_lift {e : ℕ} (R : AnLogRes P J e) {G : HermLine ι} (hG : IsSmoothHerm G) (h0 : G.a = 0) :
    Continuous fun x => Real.log (G.h (R.lift x x)) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have h1 : ContinuousOn (fun y => Real.log (G.h (R.lift x y))) (R.U x) :=
    (smooth_log hG).continuousOn.comp (continuousOn_pi.2 fun p => continuousOn_lift R x p)
      fun y hy => (R.mem x y hy).1
  have hn : R.U x ∈ 𝓝 x := (R.isOpen_U x).mem_nhds (R.mem_U x)
  refine (h1.continuousAt hn).congr ?_
  filter_upwards [hn] with y hy
  obtain ⟨c, hc, hcz⟩ := R.compat x y y ⟨hy, R.mem_U y⟩
  rw [hcz, h_inv_of_deg h0 c _ hc]

theorem add_update (hE : ResExistsStatement) {e : ℕ} (R : AnLogRes P J e) (hP : IsArithVar P (e + 1))
    {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) (j : Fin e) {A B C G : HermLine ι}
    (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (hC : IsSmoothHerm C) (hG : IsSmoothHerm G) (h0 : G.a = 0)
    (h : ∀ z ∈ mcPts P, A.h z * B.h z = C.h z) :
    ptsIntegral P (pot (Function.update L j C)) (fun z => Real.log (G.h z)) =
      ptsIntegral P (pot (Function.update L j A)) (fun z => Real.log (G.h z)) +
        ptsIntegral P (pot (Function.update L j B)) (fun z => Real.log (G.h z)) := by
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by have := j.2; omega⟩
  have hg : (fun z => Real.log (G.h z)) = logNorm G.inv 1 := funext fun z => (logNorm_inv_one G z).symm
  have hL' : ∀ i, IsSmoothHerm (j.removeNth L i) := fun i => hL _
  have key : ∀ E : HermLine ι, IsSmoothHerm E →
      ptsIntegral P (pot (Function.update L j E)) (fun z => Real.log (G.h z)) =
        mInt R.A (Fin.cons (potOf R E) fun i => potOf R (j.removeNth L i))
          (fun x => Real.log (G.h (R.lift x x))) := by
    intro E hEs
    have hU : ∀ i, IsSmoothHerm (Function.update L j E i) := by
      intro i
      by_cases hi : i = j
      · subst hi
        rwa [Function.update_self]
      · rw [Function.update_of_ne hi]
        exact hL i
    rw [hg, ptsIntegral_eq_mInt' hE resBridge R hP hU (isSmoothHerm_inv hG) (isSectionOn_inv_one hP.2.1.1 h0),
      ← potOf_cons, ← mIntSymm R.A
        (fun i => potOf R ((Fin.cons E (j.removeNth L) : Fin (n + 1) → HermLine ι) i)) j.cycleRange]
    have hu : Function.update L j E =
        (Fin.cons E (j.removeNth L) : Fin (n + 1) → HermLine ι) ∘ j.cycleRange := by
      rw [Fin.cons_comp_cycleRange, Fin.insertNth_removeNth]
    rw [hu]
    exact mInt_congr _ (fun _ _ _ => rfl) fun x => logNorm_inv_one _ _
  rw [key C hC, key A hA, key B hB]
  have hΦ : ∀ i, IsPotential R.A (potOf R (j.removeNth L i)) := fun i => isPotential_potOf R (hL' i)
  have hPA := isPotential_potOf R hA
  have hPB := isPotential_potOf R hB
  have hc := continuous_log_lift R hG h0
  rw [← mIntAdd R.A _ _ _ hPA hPB hΦ _ (mIntegrableCont _ _ (fun i => Fin.cases hPA hΦ i) _ hc)
    (mIntegrableCont _ _ (fun i => Fin.cases hPB hΦ i) _ hc)]
  refine mInt_congr _ (locDens_cons_congr _ _ fun j y hy => germ_of_eqOn R (fun x z hz => ?_) j y hy)
    fun _ => rfl
  have hm := R.mem x z hz
  show Real.log (C.h (R.lift x z)) = Real.log (A.h (R.lift x z)) + Real.log (B.h (R.lift x z))
  rw [← h _ hm]
  exact Real.log_mul (A.pos _ hm.1).ne' (B.pos _ hm.1).ne'

theorem triv_update (hE : ResExistsStatement) {e : ℕ} (R : AnLogRes P J e) (hP : IsArithVar P (e + 1))
    {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) (j : Fin e) {G : HermLine ι}
    (hG : IsSmoothHerm G) (h0 : G.a = 0) :
    ptsIntegral P (pot (Function.update L j (GlobalTheory.CompanionTheory.Ar.Top.trivLine ι))) (fun z => Real.log (G.h z)) = 0 := by
  have hs : IsSmoothHerm (GlobalTheory.CompanionTheory.Ar.Top.trivLine ι) := contDiffOn_const
  have := add_update hE R hP hL j hs hs hs hG h0 fun z _ => mul_one _
  linarith

theorem tendsto_words (hE : ResExistsStatement) {e : ℕ} (R : AnLogRes P J e) (hP : IsArithVar P (e + 1))
    {σ ρ : Type} {t₀ : ℝ} (ht₀ : 0 < t₀) (ℓ : σ → ℝ → HermLine ι) (x : ℝ → ρ → HermLine ι) (G : ℝ → HermLine ι)
    (hℓ : ∀ a t, 0 < t → t ≤ t₀ → IsSmoothHerm (ℓ a t)) (hx : ∀ t r, IsSmoothHerm (x t r))
    (hG : ∀ t, IsSmoothHerm (G t)) (h0 : ∀ t, (G t).a = 0)
    (hrel : ∀ r, ∃ a, (∃ b, ∀ t, 0 < t → t ≤ t₀ → ∀ z ∈ mcPts P, (x t r).h z * (ℓ a t).h z = (ℓ b t).h z) ∨
      ∀ t, 0 < t → t ≤ t₀ → ∀ z ∈ mcPts P, (x t r).h z * (ℓ a t).h z = 1)
    (hw : ∀ w : Fin e → σ, Tendsto (fun t => ptsIntegral P (pot fun j => ℓ (w j) t)
      (fun z => Real.log ((G t).h z))) (𝓝[>] 0) (𝓝 0))
    (s : Finset (Fin e)) : ∀ L : ℝ → Fin e → HermLine ι, (∀ j ∈ s, ∃ r, ∀ t, L t j = x t r) →
      (∀ j ∉ s, ∃ a, ∀ t, L t j = ℓ a t) →
      Tendsto (fun t => ptsIntegral P (pot (L t)) (fun z => Real.log ((G t).h z))) (𝓝[>] 0) (𝓝 0) := by
  induction s using Finset.induction_on with
  | empty =>
    intro L _ h2
    choose w hw' using fun j => h2 j (Finset.notMem_empty j)
    have : L = fun t j => ℓ (w j) t := funext fun t => funext fun j => hw' j t
    subst this
    exact hw w
  | insert j s hj ih =>
    intro L h1 h2
    obtain ⟨r, hr⟩ := h1 j (Finset.mem_insert_self j s)
    have hup : ∀ a, Tendsto (fun t => ptsIntegral P (pot (Function.update (L t) j (ℓ a t)))
        (fun z => Real.log ((G t).h z))) (𝓝[>] 0) (𝓝 0) := by
      intro a
      refine ih (fun t => Function.update (L t) j (ℓ a t)) (fun i hi => ?_) fun i hi => ?_
      · have hij : i ≠ j := fun h => hj (h ▸ hi)
        simp only [Function.update_of_ne hij]
        exact h1 i (Finset.mem_insert_of_mem hi)
      · by_cases hij : i = j
        · subst hij
          exact ⟨a, fun t => Function.update_self _ _ _⟩
        · simp only [Function.update_of_ne hij]
          exact h2 i fun h => (Finset.mem_insert.1 h).elim hij hi
    have hLs : ∀ t, 0 < t → t ≤ t₀ → ∀ i, IsSmoothHerm (L t i) := by
      intro t a b i
      by_cases hi : i ∈ insert j s
      · obtain ⟨r, hr⟩ := h1 i hi
        rw [hr]
        exact hx t r
      · obtain ⟨c, hc⟩ := h2 i hi
        rw [hc]
        exact hℓ c t a b
    have hself : ∀ t, Function.update (L t) j (x t r) = L t := fun t => by
      rw [← hr t, Function.update_eq_self]
    obtain ⟨a, ⟨b, hb⟩ | hb⟩ := hrel r
    · have h3 := (hup b).sub (hup a)
      rw [sub_zero] at h3
      refine h3.congr' ?_
      filter_upwards [Ioc_mem_nhdsGT ht₀] with t ht
      rw [add_update hE R hP (hLs t ht.1 ht.2) j (hx t r) (hℓ a t ht.1 ht.2) (hℓ b t ht.1 ht.2) (hG t) (h0 t)
        (hb t ht.1 ht.2), hself, add_sub_cancel_right]
    · have h3 := (hup a).neg
      rw [neg_zero] at h3
      refine h3.congr' ?_
      filter_upwards [Ioc_mem_nhdsGT ht₀] with t ht
      have h4 := add_update hE R hP (hLs t ht.1 ht.2) j (C := GlobalTheory.CompanionTheory.Ar.Top.trivLine ι) (hx t r)
        (hℓ a t ht.1 ht.2) contDiffOn_const (hG t) (h0 t) (hb t ht.1 ht.2)
      rw [triv_update hE R hP (hLs t ht.1 ht.2) j (hG t) (h0 t), hself] at h4
      linarith

theorem tendsto_congr_pts (P : Ideal (MRing ι)) {e : ℕ} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (φ : ℝ → Fin e → ((Σ k, ι k) → ℂ) → ℝ) {g g' : ℝ → ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ t, 0 < t → t ≤ t₀ → ∀ z ∈ mcPts P, g t z = -g' t z)
    (h' : Tendsto (fun t => ptsIntegral P (φ t) (g' t)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun t => ptsIntegral P (φ t) (g t)) (𝓝[>] 0) (𝓝 0) := by
  have h3 := h'.neg
  rw [neg_zero] at h3
  refine h3.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT ht₀] with t ht
  exact (pts_neg_congr P _ (h t ht.1 ht.2)).symm

end Gen

theorem telescope {G : Type} [CommMonoid G] {N : ℕ} (x y : Fin N → G)
    (h : ∀ i : Fin N, x i * y i = if h : 0 < (i : ℕ) then y ⟨i - 1, by omega⟩ else 1)
    (i₀ : Fin N) (hi : (i₀ : ℕ) + 1 = N) : (∏ i, x i) * y i₀ = 1 := by
  induction N with
  | zero => exact i₀.elim0
  | succ n ih =>
    obtain rfl : i₀ = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [Fin.prod_univ_castSucc, mul_assoc, h]
    split_ifs with hn
    · simp only [Fin.val_last] at hn
      exact ih (fun i => x i.castSucc) (fun i => y i.castSucc) (fun i => h i.castSucc) ⟨n - 1, by omega⟩
        (by simp only []; omega)
    · simp only [Fin.val_last] at hn
      obtain rfl : n = 0 := by omega
      simp

theorem telescope_add {G : Type} [AddCommMonoid G] {N : ℕ} (x y : Fin N → G)
    (h : ∀ i : Fin N, x i + y i = if h : 0 < (i : ℕ) then y ⟨i - 1, by omega⟩ else 0)
    (i₀ : Fin N) (hi : (i₀ : ℕ) + 1 = N) : (∑ i, x i) + y i₀ = 0 := by
  induction N with
  | zero => exact i₀.elim0
  | succ n ih =>
    obtain rfl : i₀ = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [Fin.sum_univ_castSucc, add_assoc, h]
    split_ifs with hn
    · simp only [Fin.val_last] at hn
      exact ih (fun i => x i.castSucc) (fun i => y i.castSucc) (fun i => h i.castSucc) ⟨n - 1, by omega⟩
        (by simp only []; omega)
    · simp only [Fin.val_last] at hn
      obtain rfl : n = 0 := by omega
      simp

theorem mono_roots {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) (m : Ψ × Fin N →₀ ℕ)
    (d : ℕ) (hm : m.degree = d) (j : Fin d) :
    ∃ r, ∀ t, GlobalTheory.CompanionTheory.Ar.Top.monoLines (M.line t) (m.mapDomain some) d j = M.x t r := by
  have hl : (j : ℕ) < (Finsupp.toMultiset (m.mapDomain (some : _ → Option (Ψ × Fin N)))).toList.length := by
    rw [Multiset.length_toList, ← Finsupp.toMultiset_map, Multiset.card_map, Finsupp.card_toMultiset]
    exact lt_of_lt_of_eq j.2 hm.symm
  have hall : ∀ o ∈ (Finsupp.toMultiset (m.mapDomain (some : _ → Option (Ψ × Fin N)))).toList,
      ∃ r, some r = o := by
    intro o ho
    rw [Multiset.mem_toList, ← Finsupp.toMultiset_map] at ho
    obtain ⟨r, -, hr⟩ := Multiset.mem_map.1 ho
    exact ⟨r, hr⟩
  obtain ⟨r, hr⟩ := hall _ (List.get_mem _ ⟨j, hl⟩)
  refine ⟨r, fun t => ?_⟩
  unfold GlobalTheory.CompanionTheory.Ar.Top.monoLines
  rw [dif_pos hl, ← hr]
  rfl

end PositivityTheory.Xgn.RealisationRoots

open PositivityTheory.Xgn.RealisationRoots in
theorem PositivityTheory.Xgn.root_of_realisation_telescoping : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) (S : GlobalTheory.CompanionTheory.Ar.PB.AnSys (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N) (Option (Ψ × Fin N))) (Re : GlobalTheory.CompanionTheory.Ar.PB.Realis S M.P) (τ : Ψ) (i₀ : Fin N) (F : Type) [Field F] [NumberField F] (φ : F →+* M.Ω) (A : HermLine M.ι) (Sf : FlatHerm M.y φ A), OverInt M.y φ → IsSmoothHerm A → (i₀ : ℕ) + 1 = N → 0 < S.t₀ → A.a = ∑ i, M.xdeg (τ, i) → (∀ (σ : Ψ) (i : Fin N), M.xdeg (σ, i) + (Re.ref (some (σ, i))).a = if h : 0 < (i : ℕ) then (Re.ref (some (σ, ⟨i - 1, by omega⟩))).a else 0) → (∀ t, 0 < t → t ≤ S.t₀ → ∀ (σ : Ψ) (i : Fin N), ∀ z ∈ mcPts M.P, (M.x t (σ, i)).h z * (Re.line (some (σ, i)) t).h z = if h : 0 < (i : ℕ) then (Re.line (some (σ, ⟨i - 1, by omega⟩)) t).h z else 1) → (∀ x, Re.π x ∈ S.open' → -Real.log (A.h (Re.R.lift x x)) = Real.log ((Re.ref (some (τ, i₀))).h (Re.R.lift x x)) + S.ph (some (τ, i₀)) (Re.π x)) → ∃ R : RootFlat M τ, R.ht = Sf.ht := by
  intro hI Ψ _ _ N M S Re τ i₀ F _ _ φ A Sf hO hA hi ht₀ hdeg hxd hxh hph
  let T : ℝ → HermLine M.ι := fun t => GlobalTheory.CompanionTheory.Ar.PB.combLine (fun i : Fin N => M.x t (τ, i)) fun _ => 1
  have hTh : ∀ t z, (T t).h z = ∏ i, (M.x t (τ, i)).h z := fun t z => by
    simp only [T, GlobalTheory.CompanionTheory.Ar.PB.combLine_h, zpow_one]
  have hTs : ∀ t, IsSmoothHerm (T t) := fun t => by
    unfold IsSmoothHerm
    rw [show (T t).h = fun z => ∏ i, (M.x t (τ, i)).h z from funext (hTh t)]
    exact contDiffOn_prod fun i _ => M.x_smooth t (τ, i)
  have hTa : ∀ t, (T t).a = A.a := fun t => by
    funext k
    simp only [T, GlobalTheory.CompanionTheory.Ar.PB.combLine_a, one_mul, hdeg, Finset.sum_apply, M.x_deg]
  let G : ℝ → HermLine M.ι := fun t => A.tensor (T t).inv
  have hGh : ∀ t z, (G t).h z = A.h z * ((T t).h z)⁻¹ := fun t z => rfl
  have hGs : ∀ t, IsSmoothHerm (G t) := fun t => isSmoothHerm_tensor hA (isSmoothHerm_inv (hTs t))
  have hG0 : ∀ t, (G t).a = 0 := fun t => by
    change A.a + -(T t).a = 0
    rw [hTa, add_neg_cancel]
  have hinv : A.inv.a = (Re.ref (some (τ, i₀))).a := by
    have := telescope_add (fun i => M.xdeg (τ, i)) (fun i => (Re.ref (some (τ, i))).a) (hxd τ) i₀ hi
    change -A.a = _
    rw [hdeg]
    exact neg_eq_of_add_eq_zero_right this
  have hw : ∀ w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N) → Option (Ψ × Fin N),
      Tendsto (fun t => ptsIntegral M.P (pot fun j => Re.line (w j) t)
      (fun z => Real.log ((G t).h z))) (𝓝[>] 0) (𝓝 0) := by
    intro w
    refine tendsto_congr_pts M.P ht₀ _ (fun t h0 h1 z hz => ?_)
      (PositivityTheory.Xgn.points_integral_small_limit hI M.K M.ι _ _ S M.P Re (some (τ, i₀)) A.inv w (isSmoothHerm_inv hA) hinv fun x hx => by
        rw [← hph x hx]
        exact Real.log_inv _)
    have h2 := telescope (fun i => (M.x t (τ, i)).h z) (fun i => (Re.line (some (τ, i)) t).h z)
      (fun i => hxh t h0 h1 τ i z hz) i₀ hi
    rw [← hTh] at h2
    rw [hGh, inv_eq_of_mul_eq_one_right h2,
      Real.log_mul (A.pos z hz.1).ne' ((Re.line (some (τ, i₀)) t).pos z hz.1).ne']
    change _ = -(Real.log (A.h z)⁻¹ - _)
    rw [Real.log_inv]
    ring
  refine ⟨{ F := F, φ := φ, overInt := hO, A := A, A_smooth := hA, S := Sf, deg := hdeg.symm
            v := fun t z => Real.log ((G t).h z)
            v_inv := fun t c z hc => by rw [h_inv_of_deg (hG0 t) c z hc]
            v_smooth := fun t => smooth_log (hGs t)
            prod := fun t _ z hz => ?_
            small := fun m hm => ?_ }, rfl⟩
  · rw [Real.exp_neg, Real.exp_log ((G t).pos z hz.1), hGh, ← hTh, mul_inv, inv_inv,
      mul_inv_cancel_left₀ (A.pos z hz.1).ne']
  · refine tendsto_words hI.resExists Re.R Re.arith ht₀ Re.line M.x G Re.line_smooth M.x_smooth hGs hG0
      (fun r => ⟨some r, ?_⟩) hw Finset.univ _ (fun j _ => mono_roots M m _ hm j)
      fun j hj => (hj (Finset.mem_univ j)).elim
    by_cases h : 0 < (r.2 : ℕ)
    · exact Or.inl ⟨_, fun t h0 h1 z hz => by
        have := hxh t h0 h1 r.1 r.2 z hz
        rwa [dif_pos h] at this⟩
    · exact Or.inr fun t h0 h1 z hz => by
        have := hxh t h0 h1 r.1 r.2 z hz
        rwa [dif_neg h] at this
