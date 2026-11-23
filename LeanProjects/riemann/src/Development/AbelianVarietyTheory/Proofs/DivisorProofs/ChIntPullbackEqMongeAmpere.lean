import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTChartSource
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentMapContinuousSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2DbarChartMeasureTransferStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedChartHolomorphicCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MIntEqDifferencePotentialMeasuresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessianRelationChartCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedNullSetChartsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O.CoverInt

open MeasureTheory GlobalTheory.ChartGlue

theorem chernInt_cover {F : Type} [Field F] [NumberField F] {Y : Var F} {V : Cover Y} {e : ℕ} {M : Man e}
    {I : ManIs M Y} {ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)} {π : ∀ σ, CxPts V.p σ → M.X (ε σ)} (hdim : Y.dim = e)
    (hD : V.IsDown I ε π) {L : HermLB V.p} {P : M.Pot} (hP : ∀ a, IsPotential (M.A a) (P a)) (hH : HessRel ε π L P)
    {f : M.Fun} (hf : M.Smooth f) (σ : 𝓞 F →+* ℂ) :
    (L.φ σ).chernInt e Set.univ (M.pull ε π f σ) = V.deg * mInt (M.A (ε σ)) (fun _ => P (ε σ)) (f (ε σ)) := by
  obtain ⟨hπc, -⟩ := GlobalTheory.T.descent_map_continuous_surjective F Y V e M I ε π hD σ
  have := CxPts.t2Space_cxPts_of_isProjOver σ V.ar.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver σ V.ar.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (I.ε (ε σ)) Y.isProjOver
  have : SecondCountableTopology (M.X (ε σ)) := (I.pt (ε σ)).isEmbedding.secondCountableTopology
  obtain ⟨T, hTc, hTn, hTn', hfib, hch⟩ := GlobalTheory.T.exists_closed_null_set_charts F Y V e M I ε π hdim hD σ
  have hA := GlobalTheory.T.transported_chart_holomorphic_compat F Y e M I (ε σ) (P (ε σ)) (hP _)
  have hcf : Continuous (f (ε σ)) := projLine_continuous_of_smooth _ (hf _)
  have hmap (s : ℤˣ) : Measure.map (π σ) ((L.φ σ).chernPart e s) = (V.deg : ENNReal) • potMeas I (P (ε σ)) s := by
    refine GlobalTheory.T.L2_dbar_chart_measure_transfer e (M.X (ε σ)) (CxPts V.p σ) (AlgChart Y.str (I.ε (ε σ)) e) (AlgChart V.p σ e) (fun c => tChart I c) _
      (fun c => c.e) _ hA.1 (fun c c' x hx hx' => by
        rw [hA.2 c c' x hx hx', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)])
      (fun c c' => c.holo_trans c') (fun c c' y hy hy' => by
        rw [c.chernDens_trans c' (L.cInf σ) hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)])
      (π σ) hπc T hTc hTn hTn' V.deg hfib fun z hz => ?_
    obtain ⟨c, c', hz, hz', hcomp⟩ := hch z hz
    refine ⟨c, c', hz, (mem_tChart_source I c).2 hz', fun w hw hw' => ⟨hcomp w hw ((mem_tChart_source I c).1 hw'), ?_⟩⟩
    show ENNReal.ofReal ((s : ℤ) * c'.chernDens (L.φ σ) w) = ENNReal.ofReal ((s : ℤ) * potDens I (P (ε σ)) c (π σ w))
    rw [GlobalTheory.T.hessian_relation_chart_compat F Y V e M I ε π L P hH σ hπc c c' hcomp w hw ((mem_tChart_source I c).1 hw')]
  have hint (s : ℤˣ) : ∫ y, f (ε σ) (π σ y) ∂((L.φ σ).chernPart e s) =
      V.deg * ∫ x, f (ε σ) x ∂(potMeas I (P (ε σ)) s) := by
    rw [← integral_map hπc.aemeasurable hcf.aestronglyMeasurable, hmap s, integral_smul_measure]
    simp
  rw [Weight.chernInt, Measure.restrict_univ, Measure.restrict_univ]
  change ∫ y, f (ε σ) (π σ y) ∂_ - ∫ y, f (ε σ) (π σ y) ∂_ = _
  rw [hint, hint, GlobalTheory.T.mInt_eq_difference_potential_measures F Y e M I (ε σ) (P (ε σ)) (hP _) _ hcf, mul_sub]

end GlobalTheory.Mean4O.CoverInt

namespace GlobalTheory.Mean4O.CoverInt

theorem bijective_idx {F : Type} [Field F] [NumberField F] {Y : Var F} {V : Cover Y} {e : ℕ} {M : Man e}
    {I : ManIs M Y} {ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)} {π : ∀ σ, CxPts V.p σ → M.X (ε σ)} (hD : V.IsDown I ε π) :
    Function.Bijective ε := by
  refine ⟨fun σ σ' h => ?_, fun a => ⟨(I.ε a).comp (algebraMap (𝓞 F) F),
    I.ε.injective (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) (hD _).1)⟩⟩
  rw [← (hD σ).1, ← (hD σ').1, h]

theorem chInt_pull : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (e : ℕ) (M : Man e)
    (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)), Y.dim = e →
    V.IsDown I ε π → ∀ (L : HermLB V.p) (P : M.Pot), (∀ a, ReciprocityTheory.AnForm.M.IsPotential (M.A a) (P a)) →
    HessRel ε π L P → ∀ f : M.Fun, M.Smooth f → ArInt.chInt L e (M.pull ε π f) = V.ν * M.int (fun _ => P) f := by
  intro F _ _ Y V e M I ε π hdim hD L P hP hH f hf
  have hb := bijective_idx hD
  have hk : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hs : ∑ᶠ σ, (V.deg : ℝ) * mInt (M.A (ε σ)) (fun _ => P (ε σ)) (f (ε σ)) =
      ∑ᶠ a, (V.deg : ℝ) * mInt (M.A a) (fun _ => P a) (f a) :=
    finsum_comp_equiv (Equiv.ofBijective ε hb) (f := fun a => (V.deg : ℝ) * mInt (M.A a) (fun _ => P a) (f a))
  rw [ArInt.chInt, finsum_congr (chernInt_cover hdim hD hP hH hf), hs, finsum_eq_sum_of_fintype, Man.int, I.κ_eq, Cover.ν, ← Finset.mul_sum]
  field_simp

end GlobalTheory.Mean4O.CoverInt
