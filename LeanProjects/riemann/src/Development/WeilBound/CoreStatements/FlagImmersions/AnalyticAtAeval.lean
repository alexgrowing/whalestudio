import Development.WeilBound.CoreStatements.FlagImmersions.NeZeroOfHasVal
import Development.WeilBound.CoreStatements.FlagImmersions.ExistsInverse
import Development.WeilBound.CoreStatements.VolumeEquality.Pieces

noncomputable section

namespace RootFieldNumerics

open AlgebraicGeometry CategoryTheory NumberField Filter Topology MvPolynomial
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB Bh

theorem Bh.analyticAt_aeval {σ : Type} {n : ℕ} {f : σ → (Fin n → ℂ) → ℂ} {t : Fin n → ℂ} (h : ∀ q, AnalyticAt ℂ (f q) t)
    (p : MvPolynomial σ ℤ) : AnalyticAt ℂ (fun u => aeval (fun q => f q u) p) t := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq => simpa using hp.fun_add hq
  | mul_X p i hp => simpa using hp.fun_mul (h i)

theorem biholo_of : Descend → Biholo := by
  intro hD E _ _ _ H D l Xo c Y S RM Sys Fx Or hJ hdeg hamp
  classical
  obtain ⟨m, n, s, hs, hamp⟩ := hamp
  have hd : IsDegreeOff Sys.A Or.Re.R.A Or.Re.π 1 Or.Re.br := by
    have := Or.Re.degree
    rwa [Or.Re_deg, hdeg] at this
  have hsurj := surj_of_degree Or.Re.holo.1 hd
  set R := Or.Re.R with hR
  set π := Or.Re.π with hπ
  let k₀ := Or.k₀
  have hmem : ∀ w, ∀ w' ∈ R.U w, R.lift w w' ∈ mcPts (mCoordIdeal RM.y) := R.mem
  choose z hz using fun w => SheetDecomposition.exists_pt Or.𝔐 (hmem w w (R.mem_U w))
  have hz' : ∀ w, ∀ w' ∈ R.U w, CoordsAt Or.𝔐.ξ RM.y (z w') (R.lift w w') := fun w w' h => by
    obtain ⟨a, ha, e⟩ := R.compat w w' w' ⟨h, R.mem_U w'⟩
    exact SheetDecomposition.coords_of_sat Or.𝔐 (hz w') ⟨_, rfl, a, ha, e⟩
  have hpoly : ∀ i (cc : (k : RM.K) → RM.ι k), (∀ k, RM.y ⟨k, cc k⟩ ≠ 0) → ∃ p : MRing RM.ι,
      aeval (fun q : Σ k, RM.ι k => RM.y q / RM.y ⟨q.1, cc q.1⟩) p = s i * ∏ k, RM.y ⟨k, cc k⟩ ^ (-((m : ℤ) * RM.A.a k - 1)) ∧
      aeval (fun q : Σ k, RM.ι k => RM.y q / RM.y ⟨q.1, cc q.1⟩) p = fn RM.y (s i) m k₀ (cc k₀) cc := fun i cc hc => by
    have h1 := hs i cc hc
    simp only [Nat.cast_one, one_mul] at h1
    obtain ⟨p, hp⟩ := exists_poly Or.𝔐.tie Or.𝔐.normal cc hc h1
    exact ⟨p, hp, hp.trans (fn_eq Or.A_deg cc hc)⟩
  have hchart : ∀ w, ∃ cc : (k : RM.K) → RM.ι k, (∀ k, R.lift w w ⟨k, cc k⟩ ≠ 0) ∧ ∀ k, RM.y ⟨k, cc k⟩ ≠ 0 := fun w => by
    choose cc hc using (hmem w w (R.mem_U w)).1
    exact ⟨cc, hc, fun k => ((hz w).2 k (cc k) (IsUnit.mk0 _ (hc k))).1⟩
  let f : Fin n → RM.ι k₀ → ((k : RM.K) → RM.ι k) → R.X → ℂ := fun i i₀ cc w =>
    if h : ∃ r, ValAt Or.𝔐.ξ (z w) (fn RM.y (s i) m k₀ i₀ cc) r then h.choose else 0
  have hf : ∀ i i₀ cc w r, ValAt Or.𝔐.ξ (z w) (fn RM.y (s i) m k₀ i₀ cc) r → f i i₀ cc w = r := fun i i₀ cc w r h => by
    have h' : ∃ r, ValAt Or.𝔐.ξ (z w) (fn RM.y (s i) m k₀ i₀ cc) r := ⟨r, h⟩
    simp only [f, dif_pos h']
    exact CxVal.unique h'.choose_spec h
  let U : RM.ι k₀ → Set Sys.X := fun i₀ => {x | Fx.pt x (Or.ix.symm i₀) ≠ 0}
  have hU : ∀ i₀ w, π w ∈ U i₀ ↔ R.lift w w ⟨k₀, i₀⟩ ≠ 0 := fun i₀ w => by
    obtain ⟨a, ha⟩ := Or.π_pt w
    have h1 : R.lift w w ⟨k₀, i₀⟩ = a * Fx.pt (π w) (Or.ix.symm i₀) := by
      have := congrFun ha (Or.ix.symm i₀)
      simpa using this
    have h2 : a ≠ 0 := by
      rintro rfl
      obtain ⟨i, hi⟩ := (hmem w w (R.mem_U w)).1 k₀
      have := congrFun ha (Or.ix.symm i)
      exact hi (by simpa using this)
    rw [h1]
    simp [U, h2]
  have hUo : ∀ i₀, IsOpen (U i₀) := fun i₀ => by
    have e : (U i₀)ᶜ = π '' {w | R.lift w w ⟨k₀, i₀⟩ ≠ 0}ᶜ := by
      ext x
      obtain ⟨w, rfl⟩ := hsurj x
      exact ⟨fun h => ⟨w, fun h' => h ((hU _ _).2 h'), rfl⟩, fun ⟨w', h, e⟩ h' => h ((hU _ _).1 (e ▸ h'))⟩
    rw [← isClosed_compl_iff, e]
    exact Or.Re.holo.1.isClosedMap _ (isOpen_lift_ne R _).isClosed_compl
  have hhol : ∀ i i₀ cc, R.A.HoloOn (π ⁻¹' U i₀) (f i i₀ cc) := fun i i₀ cc j t ht => by
    obtain ⟨c', hc', hy'⟩ := hchart ((R.A.chart j).symm t)
    obtain ⟨p, -, hp⟩ := hpoly i c' hy'
    have h0 := (hU _ _).1 ht.2
    set w₁ := (R.A.chart j).symm t with hw₁
    have ha : ∀ q, AnalyticAt ℂ (fun u => R.lift w₁ ((R.A.chart j).symm u) q) t := fun q =>
      R.holo w₁ q j t ⟨ht.1, R.mem_U w₁⟩
    have hA : AnalyticAt ℂ (fun u => aeval (fun q : Σ k, RM.ι k => R.lift w₁ ((R.A.chart j).symm u) q /
        R.lift w₁ ((R.A.chart j).symm u) ⟨q.1, c' q.1⟩) p *
        (∏ k, R.lift w₁ ((R.A.chart j).symm u) ⟨k, cc k⟩ / R.lift w₁ ((R.A.chart j).symm u) ⟨k, c' k⟩) *
        (R.lift w₁ ((R.A.chart j).symm u) ⟨k₀, c' k₀⟩ / R.lift w₁ ((R.A.chart j).symm u) ⟨k₀, i₀⟩) ^ m) t :=
      ((Bh.analyticAt_aeval (fun q => (ha q).fun_div (ha _) (hc' _)) p).fun_mul
        (Finset.analyticAt_fun_prod _ fun k _ => (ha _).fun_div (ha _) (hc' _))).fun_mul
        (((ha _).fun_div (ha _) h0).fun_pow m)
    refine hA.congr ?_
    have e1 : ∀ᶠ u in 𝓝 t, (R.A.chart j).symm u ∈ R.U w₁ :=
      ((R.A.chart j).continuousAt_symm ht.1).eventually_mem ((R.isOpen_U w₁).mem_nhds (R.mem_U w₁))
    have e2 : ∀ᶠ u in 𝓝 t, ∀ k, R.lift w₁ ((R.A.chart j).symm u) ⟨k, c' k⟩ ≠ 0 :=
      Filter.eventually_all.2 fun k => (ha _).continuousAt.eventually_ne (hc' k)
    filter_upwards [e1, e2, (ha _).continuousAt.eventually_ne h0] with u h1 h2 h3
    exact (hf _ _ _ _ _ (val_fn (Or.𝔐.all _) (hz' w₁ _ h1) i₀ cc c' h2 h3 hp)).symm
  choose F hF hFf using fun i i₀ cc =>
    hD _ Sys.X R.X Sys.A R.A π Or.Re.br (U i₀) (f i i₀ cc) Or.Re.holo hd (hUo i₀) (hhol i i₀ cc)
  refine exists_inverse R hJ Sys.A π hsurj fun w₁ => ?_
  obtain ⟨c', hc', hy'⟩ := hchart w₁
  obtain ⟨i, v, hv, hval⟩ := hamp ℂ (R.lift w₁ w₁) ⟨(hmem w₁ w₁ (R.mem_U w₁)).1, fun g hg => by
    have := (hmem w₁ w₁ (R.mem_U w₁)).2 g hg
    rwa [MvPolynomial.eval_map] at this⟩
  obtain ⟨p, hp1, hp2⟩ := hpoly i c' hy'
  have hu := ne_zero_of_hasVal (Or.𝔐.all _) (hz w₁) c' hc' hp1 hv hval
  have hin : π w₁ ∈ U (c' k₀) := (hU _ _).2 (hc' k₀)
  refine ⟨{x ∈ U (c' k₀) | F i (c' k₀) c' x ≠ 0}, fun x q => F i (c' k₀) (Function.update c' q.1 q.2) x, ?_, ⟨hin, ?_⟩,
    fun q j => (hF _ _ _ j).mono fun t ht => ⟨ht.1, ht.2.1⟩, fun w hw => ?_⟩
  · refine isOpen_iff_mem_nhds.2 fun x hx => ?_
    filter_upwards [(hUo _).mem_nhds hx.1, (contAt_of_holoOn (hF i _ c') hx.1).eventually_ne hx.2] with x' h1 h2
    exact ⟨h1, h2⟩
  · rw [hFf _ _ _ _ hin, hf _ _ _ _ _ (val_fn (Or.𝔐.all _) (hz w₁) (c' k₀) c' c' hc' (hc' k₀) hp2)]
    exact mul_ne_zero (mul_ne_zero hu (Finset.prod_ne_zero_iff.2 fun k _ => div_ne_zero (hc' k) (hc' k)))
      (pow_ne_zero _ (div_ne_zero (hc' _) (hc' _)))
  · obtain ⟨c₂, hc₂, hy₂⟩ := hchart w
    obtain ⟨p₂, -, hp₂⟩ := hpoly i c₂ hy₂
    have h0 := (hU _ _).1 hw.1
    obtain ⟨κ, hκ⟩ : ∃ κ : ℂ, ∀ cc, F i (c' k₀) cc (π w) = κ * ∏ k, R.lift w w ⟨k, cc k⟩ := by
      refine ⟨aeval (fun q : Σ k, RM.ι k => R.lift w w q / R.lift w w ⟨q.1, c₂ q.1⟩) p₂ *
        (R.lift w w ⟨k₀, c₂ k₀⟩ / R.lift w w ⟨k₀, c' k₀⟩) ^ m / ∏ k, R.lift w w ⟨k, c₂ k⟩, fun cc => ?_⟩
      rw [hFf _ _ _ _ hw.1, hf _ _ _ _ _ (val_fn (Or.𝔐.all _) (hz w) (c' k₀) cc c₂ hc₂ h0 hp₂), Finset.prod_div_distrib]
      ring
    have h1 := hw.2
    rw [hκ] at h1
    have h2 := left_ne_zero_of_mul h1
    have h3 := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul h1)
    refine SO_symm ⟨fun k => κ * ∏ k' ∈ Finset.univ.erase k, R.lift w w ⟨k', c' k'⟩,
      fun k => mul_ne_zero h2 (Finset.prod_ne_zero_iff.2 fun k' _ => h3 k' (Finset.mem_univ _)), funext fun q => ?_⟩
    obtain ⟨k, j⟩ := q
    show F i (c' k₀) (Function.update c' k j) (π w) = _
    rw [hκ, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k), Function.update_self, mul_assoc]
    congr 2
    exact Finset.prod_congr rfl fun k' hk' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]

end RootFieldNumerics
