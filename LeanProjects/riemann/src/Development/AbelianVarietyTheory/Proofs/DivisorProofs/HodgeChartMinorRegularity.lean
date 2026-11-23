import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorAtMulTriangular
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MvPolynomial Formalism.BasicNotions.DV
open GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag
open GlobalTheory.Cartier GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.WholeFlag
open IsDedekindDomain GlobalTheory.WholeFlag.Glue GlobalTheory.WholeFlag.GlueProof
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WholeFlag.GlueProof

theorem chosen_minor_max : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ) (V : Cover Y) (W : Y.X.Opens) {ι : Type} (U : ι → V.X.Opens) (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (L : Fin g → LB V.X) (m : ℕ) (r : ∀ i, ((L i).pull V.j).ι → V.G.functionFieldˣ), Hyp A p V W U H J d T L m r → ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W → ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ∀ q : Idx ι L, ⊤ ≤ yt ⁻¹ᵁ chartOpen V U H L m r q → ∀ (k : ℕ) (hk : k ≤ g), 0 < e.w (minorAt (valMat V (H q.1) (T (below y.1)) z) k hk (q.2.1 k)) ∧ ∀ σ : Fin k → Fin (g + g), e.w (minorAt (valMat V (H q.1) (T (below y.1)) z) k hk σ) ≤ e.w (minorAt (valMat V (H q.1) (T (below y.1)) z) k hk (q.2.1 k)) := by
  intro F _ _ Y C g A p V W ι U H J d T L m r hH v hv e y hyW z yt hz hyt q hq k hk
  obtain ⟨hp, hg, hJ, hgen, hm, hcov, hcovL, hT, hGd, hrl, hnorm, hreg, htest⟩ := hH
  obtain ⟨ν, hν, hlg, hU⟩ := htest v hv e y hyW z yt hz hyt
  have hq1 : ⊤ ≤ yt ⁻¹ᵁ U q.1 := fun x hx => (hq hx).1
  obtain ⟨hle, hex, -, -⟩ := hU q.1 hq1
  have hc : yt (IsLocalRing.closedPoint e.O) ∈ chartOpen V U H L m r q := hq (x := IsLocalRing.closedPoint e.O) trivial
  have hbπ : V.π (below z) = below y.1 := by rw [← hz]; rfl
  have hjz : V.j (below z) ∈ chartOpen V U H L m r q := by
    have e1 : V.j (below z) = below (spMap e.O.subtype ≫ yt) := by rw [hyt]; rfl
    rw [e1]
    exact hq (x := below (spMap e.O.subtype)) trivial
  have hν0 : ν 0 = 1 := by
    obtain ⟨σ, hσ⟩ := hex 0 (Nat.zero_le g)
    rw [← hσ, minorAt_zero, map_one]
  have hHz : ∀ a b, RegAt (below z) ((H q.1 * ((T (below y.1)).map V.φ)⁻¹) a b) := by
    have := hreg q.1 (below z) hjz.1
    rw [hbπ] at this
    exact this
  have hGd' : ∀ i, UnitAt (V.π (below z)) (genAt (A i).D (below y.1) * d (below y.1) i) := by
    rw [hbπ]; exact fun i => hGd i (below y.1)
  have hrl' : ∀ i, UnitAt (below z) (V.φ (genAt (A i).D (below y.1) ^ m) * (frames r q.2.2 i : V.G.functionField)) := by
    intro i
    have := hrl i (fun _ => q.2.2 i) (below z) ((LB.pull_U V.j (fun _ => q.2.2 i)).ge (hjz.2.1 i))
    rw [hbπ] at this
    exact this
  have hnorm' : ∀ i, (m : ℝ) * (A i).lg v e y =
      Real.log (e.w (valAt z (V.φ (genAt (A i).D (below y.1) ^ m) * (frames r q.2.2 i : V.G.functionField)))) :=
    fun i => hnorm i v hv e y z yt (fun _ => q.2.2 i) hz hyt (fun x hx => (hq hx).2.1 i)
  have hlg' : ∀ i : Fin g, (A i).lg v e y = Real.log (e.w (valAt (z ≫ V.π) (genAt (A i).D (below y.1) * d (below y.1) i))) +
      Real.log (ν ((i : ℕ) + 1)) - Real.log (ν (i : ℕ)) := by
    rw [hz]; exact hlg
  have hw := w_nmin V e z (H q.1) (frames r q.2.2) m k hk (q.2.1 k) (T (below y.1)) (d (below y.1))
    (fun i => genAt (A i).D (below y.1)) (hT _).1 (hT _).2 hHz hGd' hrl' ν hν hν0 (fun i => (A i).lg v e y) hnorm' hlg'
  have h1 := GlobalTheory.NormExt.w_valAt_eq_one e yt (hc.2.2 k hk)
  rw [hyt, valAt_symm] at h1
  rw [h1] at hw
  have hνk := hν k hk
  have hX : e.w (minorAt (valMat V (H q.1) (T (below y.1)) z) k hk (q.2.1 k)) = ν k := by
    have h2 : e.w (minorAt (valMat V (H q.1) (T (below y.1)) z) k hk (q.2.1 k)) ^ m = ν k ^ m := by
      have hpos : 0 < ν k ^ m := pow_pos hνk m
      have := hw.symm
      rw [div_eq_one_iff_eq hpos.ne'] at this
      exact this
    exact (pow_left_inj₀ (e.w.nonneg _) hνk.le hm.ne').1 h2
  rw [hX]
  exact ⟨hνk, fun σ => hle k hk σ⟩

end GlobalTheory.WholeFlag.GlueProof
