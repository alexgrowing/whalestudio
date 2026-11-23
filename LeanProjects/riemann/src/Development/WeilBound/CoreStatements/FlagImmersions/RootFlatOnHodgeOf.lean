import Development.WeilBound.CoreStatements.FlagImmersions.TauInInjective
import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeetsPoint
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NearRecordOfValue
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSystemSplitFibresStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermRootLineDegreeStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

theorem sum_Iic_step {M : Type} [AddCommGroup M] {N : ℕ} (f : Fin N → M) (i : Fin N) :
    f i + -∑ k ∈ Finset.Iic i, f k =
      if h : 0 < (i : ℕ) then -∑ k ∈ Finset.Iic (⟨i - 1, by omega⟩ : Fin N), f k else 0 := by
  rw [← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
  split_ifs with h
  · have : Finset.Iio i = Finset.Iic (⟨i - 1, by omega⟩ : Fin N) := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_Iic, Fin.lt_def, Fin.le_def]
      omega
    rw [this]; abel
  · have : Finset.Iio i = ∅ := by
      ext k
      simp only [Finset.mem_Iio, Fin.lt_def, Finset.notMem_empty, iff_false]
      omega
    rw [this]; simp

theorem rootFlatOnHodge_of (h1 : CptEx) (h2 : PeriodOf) (h3 : SmoothLine) (h4 : LocalCmp) (h5 : ChiEx) (h6 : Numerics)
    (hFD : FlatDegree) (hG : Top.Given) : RootFlatOnHodge := by
  intro E _ _ _ _ H D Xo l c Y bad M Sys Fx o hY hp hq hbad hom τ
  classical
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨Yl, hg, hYl, -, -, hdom⟩ := hY
  obtain ⟨U, Z, hU, hUi, hgp⟩ := h1 E H D l (Xo l) c Y bad M.Ω M.K M.ι M.y o.𝔐
  obtain ⟨φ, N, k1, k2, k3, k4, k5, k6⟩ := exists_norms hG hFD h2 h5 Xo l c Y U Z τ hg hp hq hU hUi (isGeom_of o Z hgp)
  have hdS : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ bad := fun p hp hd =>
    (hbad p).2 ⟨hp, (hd.mul_left 2).mul_right _⟩
  obtain ⟨-, -, -, -, -, -, hF, -, -, hIn, -⟩ := hG
  obtain ⟨F', _, _, ψ, A, Sf, hO, hAs, hAa, hAh, hnr⟩ := core h3 h4 h6 hF Z φ τ N o.𝔐 o.Fl M.xdeg o.e o.sing _ k1 k2 k3
    k4 k5 k6 hgp M.birational M.arith o.lines o.hodge o.sing_deg
    ((hbad 2).2 ⟨Nat.prime_two, by exact_mod_cast (dvd_mul_right (2 : ℤ) _).mul_right _⟩) hdS hom (by omega)
    (fun p hp hS => GlobalTheory.T.local_system_split_fibres E H D Xo Yl (fun p W hp hW i => ⟨((hYl p W hp hW).2 i).1, ((hYl p W hp hW).2 i).2.1⟩)
      l c hg Y hdom bad M.Ω M.K M.ι M.y o.𝔐 p hp hS (fun hd => hS (hdS p hp hd)) τ)
  let i₀ : Fin (D.p + D.q) := ⟨D.p + D.q - 1, by omega⟩
  have hi₀ : Finset.Iic i₀ = Finset.univ := by
    ext k
    simp only [Finset.mem_Iic, Fin.le_def, Finset.mem_univ, iff_true, i₀]
    omega
  obtain ⟨R, hR⟩ := GlobalTheory.T.flat_herm_root_line_degree hIn (CMType H) (D.p + D.q) M Sys o.Re τ i₀ F' ψ A Sf hO hAs
    (by show D.p + D.q - 1 + 1 = _; omega) (Sys.reg none).1 hAa (fun σ i => by
      rw [o.fund_deg, sum_Iic_step (fun k => M.xdeg (σ, k)) i]
      split_ifs with h
      · rw [o.fund_deg]
      · rfl) (fun t ht ht' σ i z hz => by
      have p1 := (M.x t (σ, i)).pos z hz.1
      have p2 := (o.Re.line (some (σ, i)) t).pos z hz.1
      have e := sum_Iic_step (fun k => Real.log ((M.x t (σ, k)).h z)) i
      rw [← o.fund_reg σ i t ht ht' z hz, ← Real.log_mul p1.ne' p2.ne'] at e
      split_ifs at e ⊢ with h
      · rw [← o.fund_reg σ _ t ht ht' z hz] at e
        exact Real.log_injOn_pos (mul_pos p1 p2) ((o.Re.line _ t).pos z hz.1) e
      · exact Real.log_injOn_pos (mul_pos p1 p2) (Set.mem_Ioi.2 one_pos) (e.trans Real.log_one.symm)) (fun x hx => by
      have hw : o.Re.R.lift x x ∈ mcPts (mCoordIdeal M.y) := o.Re.R.mem x x (o.Re.R.mem_U x)
      obtain ⟨z, -, hz⟩ := SheetDecomposition.ChartForm.exists_point o.𝔐.tie (o.Re.R.lift x x)
        (fun k => (hw.1 k).imp fun _ h => Ne.isUnit h) fun g hg => by
          have := hw.2 g hg
          rwa [MvPolynomial.eval_map] at this
      rw [o.fund_sing τ i₀ x hx, hi₀, hAh z _ hw hz ((o.interior x z hz).2 hx),
        Real.log_prod fun i _ => ((o.sing (τ, i)).pos _ hw.1).ne'])
  exact ⟨R, hR ▸ hnr⟩

end RootFieldNumerics.RF
