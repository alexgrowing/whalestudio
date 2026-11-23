import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLineBundleInduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MSmoothAndSemiPosIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetWeightIsCInfOfPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAdelicMetricDivisorRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtOfDivisorRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinedMetricLocalPotentialExists
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.Mean4O.CombLocal.comb_local : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (Mb : Adl (cxSt F) Y) (ι : Type) [Fintype ι] (ρ : ι → Adl (cxSt F) Y) (t : ι → ℝ) (g : ∀ σ : F →+* ℂ, Pts Y σ → ℝ), GlobalTheory.Mean4O.IsComb Mb ρ t g → (∀ i σ, (cxSt F).mSmooth Y σ (ρ i).D ((ρ i).m σ)) → ∀ σ (z0 : Pts Y σ), ∃ (c K aM : ℝ) (a : ι → ℝ) (U fM : Y.Fn) (f : ι → Y.Fn), c ≠ 0 ∧ UnitAt (under z0) U ∧ Mb.D.GeneratesAt (under z0) fM ∧ (∀ i, (ρ i).D.GeneratesAt (under z0) (f i)) ∧ ∀ᶠ z in nhds z0, c * g σ z = Real.log (‖ratVal U z‖ ^ 2) + ∑ i, a i * lnN ((ρ i).m σ) (f i) z + aM * lnN (Mb.m σ) fM z + K := by
  intro F _ _ Y Mb ι _ ρ t g hC hm σ z0
  obtain ⟨q, b, hq, -, hD, hN, -⟩ := hC
  set x0 := under z0 with hx0
  set fM : Y.Fn := genAt Mb.D x0 with hfMdef
  set f : ι → Y.Fn := fun i => genAt (ρ i).D x0 with hfdef
  have hfM : Mb.D.GeneratesAt x0 fM := generatesAt_genAt _ _
  have hf : ∀ i, (ρ i).D.GeneratesAt x0 (f i) := fun i => generatesAt_genAt _ _
  have hU := GlobalTheory.CombUnit.unitAt_quot_of_relation F Y ι Mb.D (fun i => (ρ i).D) q b x0 fM f hD hfM hf
  obtain ⟨V0, hV0, hV0'⟩ := GlobalTheory.CombPot.generatesAt_exists_nhds hfM
  choose V hV hV' using fun i => GlobalTheory.CombPot.generatesAt_exists_nhds (hf i)
  have ev0 : ∀ᶠ z in nhds z0, Mb.D.GeneratesAt (under z) fM :=
    Filter.mem_of_superset ((isOpen_ptsIn _).mem_nhds (mem_ptsIn.2 hV0)) fun z hz => hV0' _ (mem_ptsIn.1 hz)
  have evi : ∀ᶠ z in nhds z0, ∀ i, (ρ i).D.GeneratesAt (under z) (f i) :=
    Filter.eventually_all.2 fun i =>
      Filter.mem_of_superset ((isOpen_ptsIn _).mem_nhds (mem_ptsIn.2 (hV i))) fun z hz => hV' i _ (mem_ptsIn.1 hz)
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.2 hq
  have hn : (0 : ℝ) < ((Mb.n : ℕ) : ℝ) := Nat.cast_pos.2 Mb.n.pos
  refine ⟨2 * q * ((Mb.n : ℕ) : ℝ),
    2 * ((q : ℝ) * ((Mb.n : ℕ) : ℝ) * Mb.ci (InfinitePlace.mk σ) -
      ∑ i, (b i : ℝ) * (((ρ i).n : ℕ) : ℝ) * (ρ i).ci (InfinitePlace.mk σ)),
    -2 * q, fun i => 2 * (b i : ℝ), fM ^ q / ∏ i, f i ^ b i, fM, f, by positivity, hU, hfM, hf, ?_⟩
  filter_upwards [ev0, evi] with z hz0 hzi
  have hk := GlobalTheory.CombUnit.unitAt_quot_of_relation F Y ι Mb.D (fun i => (ρ i).D) q b (under z) _ _ hD
    (generatesAt_genAt _ _) (fun i => generatesAt_genAt (ρ i).D _)
  have hh := GlobalTheory.CombUnit.unitAt_quot_of_relation F Y ι Mb.D (fun i => (ρ i).D) q b (under z) fM f hD hz0 hzi
  have hp : ∀ i, PosAt ((ρ i).m σ) z := fun i =>
    CombForm.pn_pos_of_generatesAt (generatesAt_genAt _ _) (posAt_of_posSet (Var.mSmooth.posSet_eq (hm i σ)) z)
  have e := GlobalTheory.Mean4O.CombGen.lnAdl_comb_change F Y ι Mb ρ q b σ z (g σ z) fM f (hN σ z).1 hp (hN σ z).2
    hz0 hzi hk hh
  rw [Real.log_pow]
  have hs : ∑ i, 2 * (b i : ℝ) * lnN ((ρ i).m σ) (f i) z = 2 * ∑ i, (b i : ℝ) * lnN ((ρ i).m σ) (f i) z := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs]
  push_cast
  linear_combination (2 : ℝ) * e
