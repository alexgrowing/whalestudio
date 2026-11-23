import Development.WeilBound.CoreStatements.CentralCharts.PshAt0LogNorm
import Development.WeilBound.CoreStatements.CentralCharts.CommonMembers
import Development.WeilBound.CoreStatements.CentralCharts.IsPosPotBlock
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsArithVarOfSncModelStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerBoundHeightOnBoundaryStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryPointsClosedStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds

noncomputable section

namespace AnalyticReference.An

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB Filter Topology Metric

theorem weight_orbit {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {σ : Type} (S : Finset σ)
    (A : σ → HermLine J) {z z' : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (h : SameOrbit z z') :
    -∑ k ∈ S, Real.log ((A k).h z) - Real.log ((fsHerm J (-∑ k ∈ S, (A k).a)).h z) =
      -∑ k ∈ S, Real.log ((A k).h z') - Real.log ((fsHerm J (-∑ k ∈ S, (A k).a)).h z') := by
  obtain ⟨c, hc, rfl⟩ := h
  have e : ∀ B : HermLine J, Real.log (B.h fun p => c p.1 * z' p) =
      ∑ k, (B.a k : ℝ) * Real.log ‖c k‖ + Real.log (B.h z') := fun B => by
    rw [B.smul c z' hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k)))
      (B.pos z' hz).ne', Real.log_prod fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))]
    simp only [Real.log_zpow]
  simp only [e, Finset.sum_add_distrib]
  have : ∑ k, (((fsHerm J (-∑ k ∈ S, (A k).a)).a k : ℤ) : ℝ) * Real.log ‖c k‖ =
      -∑ j ∈ S, ∑ k, ((A j).a k : ℝ) * Real.log ‖c k‖ := by
    have e2 : ∀ k, (fsHerm J (-∑ j ∈ S, (A j).a)).a k = -∑ j ∈ S, (A j).a k := fun k => by
      show (-∑ j ∈ S, (A j).a : K → ℤ) k = _
      simp [Finset.sum_apply]
    simp only [e2]
    rw [Finset.sum_comm]
    simp [Finset.sum_mul]
  rw [this]
  ring

theorem one_le_dimFl {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {N : ℕ} (hN : 2 ≤ N) :
    1 ≤ Top.dimFl (CMType H) N := by
  have h1 : Fintype.card (CMType H) = Module.finrank ℚ E / 2 := by
    rw [Fintype.card_eq_nat_card]; exact GlobalTheory.PeriodCoord.card_cmType H
  have h2 : 2 ≤ Module.finrank ℚ E := by
    have := IsTotallyComplex.finrank E
    have h0 : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  have h3 : 2 * 1 ≤ N * (N - 1) := Nat.mul_le_mul hN (by omega)
  unfold Top.dimFl
  exact Nat.mul_pos (by omega) (by omega)

theorem of_local (hI : PB.Inputs) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
    (hp : 1 ≤ D.p) (hq : 1 ≤ D.q) (G : RefGeo Y) (sing : RootIx D → HermLine G.J)
    (hdeg : ∀ r, (sing r).a = G.xdeg r) (hhodge : ∀ r, G.Fl.IsHodgeLine r (G.e r) (sing r))
    (hconj : ∀ r, IsConjInvariantH (sing r))
    (hloc : ∀ (χ : SncChart (mCoordIdeal G.y) (Top.dimFl (CMType H) (D.p + D.q)) (mcPts G.bd)) (τ : CMType H)
      (i : Fin (D.p + D.q)),
      Tame χ.a (fun t => -∑ k ∈ Finset.Iic i, Real.log ((sing (τ, k)).h (χ.γ t))) ∧
      (χ.a = 0 → PshAt0 (fun t => -∑ k ∈ Finset.Iic i, Real.log ((sing (τ, k)).h (χ.γ t))) ∧
        ((i : ℕ) + 1 = D.p + D.q → PshAt0 fun t => ∑ k ∈ Finset.Iic i, Real.log ((sing (τ, k)).h (χ.γ t))))) :
    ∃ A : G.An, (∃ inv : A.Sys.X → A.Re.R.X, ReciprocityTheory.AnForm.M.HoloMap A.Sys.A A.Re.R.A inv ∧
      ∀ x, inv (A.Re.π x) = x) := by
  classical
  have harith := GlobalTheory.T.isArithVar_of_snc_model G.𝔐.X G.Ω G.𝔐.ξ G.K G.J G.y _ G.bd (one_le_dimFl H (by omega)) G.𝔐.tie G.snc
  obtain ⟨y1, y2, y3⟩ := GlobalTheory.T.boundary_points_closed G.𝔐.X G.Ω G.𝔐.ξ G.K G.J G.y (abLocus G.𝔐.t.G) G.bd G.𝔐.tie G.bd_iff
  obtain ⟨R, L, s, nb, m, W, hL, hs, snc, hn, hbd, hrc⟩ := GlobalTheory.T.lowerBound_height_on_boundary G.K G.J G.Ω G.y _ G.bd G.snc harith y1 y2 y3
  have hmem : ∀ x, R.lift x x ∈ mcPts (mCoordIdeal G.y) := fun x => R.mem x x (R.mem_U x)
  have horb : ∀ z ∈ mcPts (mCoordIdeal G.y), ∀ z', SameOrbit z' z → z ∈ mcPts G.bd → z' ∈ mcPts G.bd := by
    rintro z hz z' ⟨c, hc, rfl⟩ h
    exact (y2 z ⟨hz, h⟩ c hc).2
  have hBd : ∀ x₀, ∀ x ∈ R.U x₀, R.lift x₀ x ∈ mcPts G.bd ↔ x ∈ bdry s := fun x₀ x hx => by
    rw [hbd]
    exact ⟨horb _ (R.mem _ _ hx) _ (R.compat _ _ _ ⟨R.mem_U _, hx⟩),
      horb _ (hmem x) _ (R.compat _ _ _ ⟨hx, R.mem_U _⟩)⟩
  have hcb1 : ∀ x x', SameOrbit (R.lift x' x') (Cj.cj (R.lift x x)) → x ∈ bdry s → x' ∈ bdry s := fun x x' h hx => by
    rw [hbd] at hx ⊢
    have := y3 _ ⟨hmem x, hx⟩
    exact horb _ this.1 _ h this.2
  have hcb : ∀ x x', SameOrbit (R.lift x' x') (Cj.cj (R.lift x x)) →
      (x' ∈ bdry s ↔ x ∈ bdry s) ∧ rW L s x' = rW L s x := fun x x' h =>
    ⟨⟨hcb1 x' x (by
      have := Cj.sameOrbit_symm (Cj.sameOrbit_cj h)
      rwa [Cj.cj_cj] at this), hcb1 x x' h⟩, hrc x x' h⟩
  have hemb : Cmp.IsEmbedded R.A (mCoordIdeal G.y) R.U R.lift :=
    ⟨R.isOpen_U, R.mem_U, R.holo, R.mem, R.compat, fun z hz => R.surj z hz (not_mem_top _),
      fun x x' h => R.inj x x' (not_mem_top _) h, fun x p hp j hj => R.immersion x (not_mem_top _) p hp j hj⟩
  have hpos : IsPosPot R.A (potOf R (fsHerm G.J (Pi.single G.k₀ 1))) := isPosPot_block R G.k₀ fun x p hp j hj =>
    (GlobalTheory.T.holomorphic_atlas_coord_compat G.𝔐.X G.Ω G.𝔐.ξ G.K G.J G.y G.k₀ G.𝔐.tie G.embeds _ R.X R.A R.U R.lift hemb (G.J G.k₀)
      (Equiv.refl _) x p hp j hj).2
  let d : RootIx D → G.K → ℤ := fun r => -∑ k ∈ Finset.Iic r.2, (sing (r.1, k)).a
  let wt : RootIx D → ((Σ k, G.J k) → ℂ) → ℝ := fun r z =>
    -∑ k ∈ Finset.Iic r.2, Real.log ((sing (r.1, k)).h z) - Real.log ((fsHerm G.J (d r)).h z)
  have hwt : ∀ r z z', (∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) → SameOrbit z z' → wt r z = wt r z' := fun r z z' hz h =>
    weight_orbit (Finset.Iic r.2) (fun k => sing (r.1, k)) hz h
  let u : RootIx D → R.X → ℝ := fun r x => wt r (R.lift x x)
  have hu : ∀ r x₀, ∀ x ∈ R.U x₀, u r x = wt r (R.lift x₀ x) := fun r x₀ x hx =>
    hwt r _ _ (R.mem _ _ hx).1 (R.compat _ _ _ ⟨R.mem_U _, hx⟩)
  have hball : ∀ᶠ t in 𝓝 (0 : Fin (Top.dimFl (CMType H) (D.p + D.q)) → ℂ), t ∈ ball 0 1 :=
    isOpen_ball.mem_nhds (mem_ball_self one_pos)
  have hsome : ∀ r : RootIx D, ∃ ph phT line C₅ C t₀,
      IsMember R L s (d r) (u r) ((r.2 : ℕ) + 1 = D.p + D.q) ph phT line C₅ C t₀ := by
    intro r
    refine exists_member hI.regGlobal R L s m W hL hs snc hn hcb _ _ _ (fun x x' h => ?_) (fun x => ?_) fun x hx => ?_
    · show wt r _ = wt r _
      rw [hwt r _ _ (Cj.cj_nonzero (hmem x).1) h]
      simp only [wt]
      rw [Cj.fs_conj (d r) (R.lift x x)]
      congr 2
      exact Finset.sum_congr rfl fun k _ => congrArg Real.log (hconj _ _)
    · obtain ⟨ψ, a, M, h⟩ := exists_nchart R.A L s hL hs snc x (R.U x) (R.isOpen_U x) (R.mem_U x)
      refine ⟨ψ, a, M, h, ?_⟩
      have t1 : Tame a _ := (hloc (h.snc R _ (hBd x)) r.1 r.2).1
      have t2 : Tame a fun t => Real.log ((fsHerm G.J (d r)).h (R.lift x (ψ.symm t))) := tame_smooth a fun t ht => by
        obtain ⟨h1, h2, -⟩ := h.2.2.2.2 t ht
        have hz := (R.mem _ _ h2).1
        have hopen : {z : (Σ k, G.J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∈ 𝓝 (R.lift x (ψ.symm t)) := by
          refine Filter.eventually_all.mpr fun k => ?_
          obtain ⟨i, hi⟩ := hz k
          exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
            fun y hy => ⟨i, hy⟩
        have h3 := ((StepW.fsHerm_isSmoothHerm G.K G.J (d r)).contDiffAt hopen).log ((fsHerm G.J (d r)).pos _ hz).ne'
        exact h3.comp t ((analyticAt_lift R h.1 x h1 h2).restrictScalars (𝕜 := ℝ)).contDiffAt
      refine (t1.add (t2.const_mul (-1))).congr ?_
      filter_upwards [hball] with t ht _
      rw [hu r x _ (h.2.2.2.2 t ht).2.1]
      show _ - _ = -∑ k ∈ Finset.Iic r.2, Real.log ((sing (r.1, k)).h (R.lift x (ψ.symm t))) + _
      ring
    · obtain ⟨ψ, a, M, h⟩ := exists_nchart R.A L s hL hs snc x (R.U x) (R.isOpen_U x) (R.mem_U x)
      obtain ⟨p1, p2⟩ := (hloc (h.snc R _ (hBd x)) r.1 r.2).2 (h.zero_of_not_mem hx)
      refine ⟨ψ, h.1, h.2.1, h.2.2.1, p1.congr ?_, fun hc => (p2 hc).congr ?_⟩
      · filter_upwards [hball] with t ht
        rw [hu r x _ (h.2.2.2.2 t ht).2.1]
        show _ + (_ - _) = -∑ k ∈ Finset.Iic r.2, Real.log ((sing (r.1, k)).h (R.lift x (ψ.symm t)))
        ring
      · filter_upwards [hball] with t ht
        rw [hu r x _ (h.2.2.2.2 t ht).2.1]
        show -1 * (_ + (-∑ k ∈ Finset.Iic r.2, Real.log ((sing (r.1, k)).h (R.lift x (ψ.symm t))) - _)) =
          ∑ k ∈ Finset.Iic r.2, Real.log ((sing (r.1, k)).h (R.lift x (ψ.symm t)))
        ring
  choose ph phT line hm using hsome
  obtain ⟨C₅, C, T, hM⟩ := common_members (σ := Option (RootIx D)) (R := R) hL hs snc hn
    (d := fun o => o.elim (Pi.single G.k₀ 1) d) (u := fun o => o.elim 0 u)
    (cen := fun o => o.elim False fun r => (r.2 : ℕ) + 1 = D.p + D.q) (ph := fun o => o.elim 0 ph)
    (phT := fun o => o.elim (fun _ => 0) phT)
    (line := fun o => o.elim (fun _ => fsHerm G.J (Pi.single G.k₀ 1)) line) (by
      rintro (_ | r)
      · exact member_zero R hL hs snc hn _ hpos
      · exact hm r)
  obtain ⟨hA, hfs, hΘ⟩ := fs_pos_potential G.K G.J _ _ R
  let S : AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D)) :=
    { X := R.X
      A := R.A
      Θ := potOf R (fsHerm G.J fun _ => 1)
      L := L
      s := s
      nb := nb
      m := m
      W := W
      potΘ := hA _ hfs
      posΘ := hΘ
      potL := hL
      sec := hs
      snc := snc
      norm_le := hn
      th := fun o => potOf R (fsHerm G.J (o.elim (Pi.single G.k₀ 1) d))
      ph := fun o => o.elim 0 ph
      phT := fun o => o.elim (fun _ => 0) phT
      C₅ := C₅
      C := C
      t₀ := T
      sing := fun o => (hM o).1
      reg := fun o => (hM o).2.1
      c2 := fun o => (hM o).2.2.1 }
  let Re : Realis S (mCoordIdeal G.y) :=
    { arith := harith
      J := ⊤
      R := R
      π := id
      holo := ⟨continuous_id, fun jj k => R.A.holo jj k⟩
      deg := 1
      deg_pos := one_pos
      br := ∅
      degree := FA.degree_id_self R.A
      ref := fun o => fsHerm G.J (o.elim (Pi.single G.k₀ 1) d)
      ref_smooth := fun o => StepW.fsHerm_isSmoothHerm G.K G.J _
      ref_pot := fun o x _ => ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ => analyticOnNhd_const,
          fun z _ => (sub_self _).trans Complex.zero_re.symm⟩
      line := fun o => o.elim (fun _ => fsHerm G.J (Pi.single G.k₀ 1)) line
      line_deg := fun o t => ((hM o).2.2.2.2.1 t).1
      line_smooth := fun o t _ _ => ((hM o).2.2.2.2.1 t).2.1
      line_eq := fun o t h0 h1 x => (hM o).2.2.2.2.2.1 t h0 h1 x }
  have hnd : (Pi.single G.k₀ 1 : G.K → ℤ) G.k₀ = 1 ∧ ∀ k, k ≠ G.k₀ → (Pi.single G.k₀ 1 : G.K → ℤ) k = 0 :=
    ⟨by simp, fun k hk => by simp [hk]⟩
  refine ⟨{ sing := sing, sing_deg := hdeg, hodge := hhodge, Sys := S, Re := Re, J_top := rfl, deg_one := rfl
            π_bij := Function.bijective_id, embedded := hemb, interior := fun x z hz => ?_
            fund_deg := fun τ i => ?_, fund_sing := fun τ i x hx => ?_
            conj := fun o t => ((hM o).2.2.2.2.1 t).2
            none_deg := hnd
            none_h := fun z => fs_single_h G.k₀ z, pos := hpos, ph_none := fun x => ⟨rfl, fun _ => rfl⟩
            flat := fun τ i hi t => (hM (some (τ, i))).2.2.2.2.2.2 hi t },
    id, ⟨continuous_id, fun jj k => R.A.holo jj k⟩, fun _ => rfl⟩
  · have h1 := G.bd_iff z _ hz
    show _ ↔ ¬ x ∈ bdry s
    rw [hbd]
    tauto
  · show d (τ, i) = _
    simp only [d, hdeg]
  · have h1 : ph (τ, i) x = u (τ, i) x := (hM (some (τ, i))).2.2.2.1 x hx
    show Real.log ((fsHerm G.J (d (τ, i))).h (R.lift x x)) + ph (τ, i) x =
      -∑ k ∈ Finset.Iic i, Real.log ((sing (τ, k)).h (R.lift x x))
    rw [h1]
    simp only [u, wt]
    ring

end AnalyticReference.An
