import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowValIntCast
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLat
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatPol
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLev
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatReg
import Development.WeilBound.CoreStatements.HodgeTatePoints.Hcptgen
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
import Development.WeilBound.CoreStatements.HodgeTatePoints.BtLink

noncomputable section

namespace GlobalTheory.CompanionTheory.HtLink

open PositivityTheory.HtPt PositivityTheory.HtPt.Htat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem htat_link_of (h758 : type_of% @GlobalTheory.T.HTChartExists_holds) (h576 : type_of% @GlobalTheory.T.hodge_tate_chart_integral) :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)), ∃ (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc ∧ ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (κ : chartRing o (mseg y) s.1), PointHT → IsCp p (κ : Ω) → (Dc s).HasTestPoints κ := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ hpS hpq o _ _ ho
  obtain ⟨h0, hN, hprop, hT, hrk, -, hch⟩ := Hcptgen.hcpt_generic E H D l Xo c O β Y S Ω K J y 𝔐 p hpS o ho
  have hp := (Fact.out : p.Prime)
  have hn : p ^ 𝔐.R p ≠ 0 := pow_ne_zero _ hp.ne_zero
  obtain ⟨ev, ζ₀, hev⟩ := exists_isParam D 𝔐.t 𝔐.ξ level_param (p ^ 𝔐.R p) (Nat.pos_of_ne_zero hn) hpq hprop
    (𝔐.tors p hpS) hT
  obtain ⟨u, hu⟩ := pol_lattice E H D p
  obtain ⟨π, e, hπ, he, hdec, hsurj, hker, halt, hadj, hes, hei⟩ :=
    exists_levPairing (cmConj E) p (𝔐.R p) D.EF u hu
  have key : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0},
      ∃ Dc : HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li), Dc.e = e ∧
      (∀ a w, Dc.ρΩ a w = w ∘ₗ 𝔐.ρ (H.bar a)) ∧
      (∀ w, w ∈ Dc.om ↔ ∀ q, InChart 𝔐.ξ (mseg y) s.1 q → OverZp 𝔐 p q → w ∈ 𝔐.M.omLat q) ∧
      (∀ q, InChart 𝔐.ξ (mseg y) s.1 q → OverZp 𝔐 p q →
        𝔐.M.omLat q = Submodule.span (regAt 𝔐.ξ q) (Dc.om : Set (Module.Dual Ω 𝔐.Li))) ∧
      (∀ q, InChart 𝔐.ξ (mseg y) s.1 q → OverZp 𝔐 p q → ∀ z w',
        𝔐.M.IsHTAt 𝔐.t.PP.L (p ^ 𝔐.R p) (ev (∑ k, z k • u k)) q w' ↔
          ∃ v ∈ 𝔐.M.omLat q, w' = Dc.h z + (p ^ 𝔐.R p) • v) ∧
      ∀ κ : chartRing o (mseg y) s.1, PointHT → IsCp p (κ : Ω) → Dc.HasTestPoints κ := by
    intro s
    obtain ⟨_, _, _, x, hx, hr⟩ := hch s.1 s.2
    obtain ⟨Dc, h1, h2, h3, h4, h5, h6⟩ := exists_chart Twhopf.sec_inj Twexists.exists_torsion' h758 h576 D 𝔐.t 𝔐.ξ 𝔐.tie.gen 𝔐.all 𝔐.M 𝔐.ρ 𝔐.act
      p (𝔐.R p) hev hprop (𝔐.tors p hpS) hrk u hu π e hπ he hsurj hker halt hadj hes hei (chartRing o (mseg y) s.1) x hx
      (fun q hq => chart_le_regAt 𝔐 p o ho s.1 q ((hr q).1 hq).1 ((hr q).1 hq).2)
    exact ⟨Dc, h1, h2, fun w => (h3 w).trans ⟨fun h q a b => h q ((hr q).2 ⟨a, b⟩),
      fun h q hq => h q ((hr q).1 hq).1 ((hr q).1 hq).2⟩, fun q a b => h4 q ((hr q).2 ⟨a, b⟩),
      fun q a b => h5 q ((hr q).2 ⟨a, b⟩), h6⟩
  choose Dc h1 h2 h3 h4 h5 h6 using key
  refine ⟨Dc, ⟨h2, fun s t => (h1 s).trans (h1 t).symm, h3, h4, fun s q hs hq => ?_, fun s t q hs ht hq z => ?_⟩, h6⟩
  · have hz := ModelTest.overZp_of_inFibre 𝔐 hp q hq
    have hpow : ∀ w : Module.Dual Ω 𝔐.Li, ((p : chartRing o (mseg y) s.1) ^ 𝔐.R p) • w = (p ^ 𝔐.R p) • w := fun w => by
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    have hsub := chart_le_regAt 𝔐 p o ho s.1 q hs hz
    have hmem : ∀ z, ∀ v ∈ 𝔐.M.omLat q, (Dc s).h z + (p ^ 𝔐.R p) • v ∈ omP 𝔐 p q := fun z v hv =>
      Submodule.subset_span ⟨_, (hev.onto _).2 ⟨_, rfl⟩, (h5 s q hs hz z _).2 ⟨v, hv, rfl⟩⟩
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 fun w hw => ?_)
    · rintro w ⟨g, hg, hw⟩
      obtain ⟨a, rfl⟩ := (hev.onto g).1 hg
      obtain ⟨z, b, rfl⟩ := hdec a
      rw [hev.add, (hev.ker _).2 ⟨b, rfl⟩, _root_.mul_one] at hw
      obtain ⟨v, hv, rfl⟩ := (h5 s q hs hz z w).1 hw
      refine add_mem (Submodule.subset_span (Submodule.mem_sup_left (Submodule.subset_span ⟨z, rfl⟩))) ?_
      rw [h4 s q hs hz] at hv
      clear hw
      induction hv using Submodule.span_induction with
      | mem v hv => exact Submodule.subset_span (Submodule.mem_sup_right ⟨v, hv, hpow v⟩)
      | zero => simp
      | add v v' _ _ h h' => rw [smul_add]; exact add_mem h h'
      | smul r v _ h => rw [smul_comm]; exact Submodule.smul_mem _ _ h
    · obtain ⟨w₁, hw₁, _, ⟨w₂, hw₂, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hw
      refine add_mem ?_ ?_
      · clear hw
        induction hw₁ using Submodule.span_induction with
        | mem v hv =>
          obtain ⟨z, rfl⟩ := hv
          simpa using hmem z 0 (zero_mem _)
        | zero => exact zero_mem _
        | add v v' _ _ h h' => exact add_mem h h'
        | smul r v _ h => exact Submodule.smul_mem (omP 𝔐 p q) ⟨_, hsub r⟩ h
      · have := hmem 0 w₂ (((h3 s w₂).1 hw₂) q hs hz)
        rw [map_zero, zero_add, ← hpow] at this
        exact this
  · exact (h5 t q ht hq z _).1 ((h5 s q hs hq z _).2 ⟨0, zero_mem _, by simp⟩)

end GlobalTheory.CompanionTheory.HtLink
