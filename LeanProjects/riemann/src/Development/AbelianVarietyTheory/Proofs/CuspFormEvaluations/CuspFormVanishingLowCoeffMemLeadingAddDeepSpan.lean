import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LeMulPowOfExpDecay
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnLeadM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MulProd
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SumMultiLtSucc
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuUnconditional
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ComponentModelWeightDimensionDictionary
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemSpanCuspReadingsIffComponents

noncomputable section

namespace GlobalTheory.Containment

section Model

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
  MeasureTheory Topology GlobalTheory.Shares ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_valBasis (X : Data E r) (G : Wt X.Ψ r) {δ m : ℕ} (xs : Fin δ → Frame X.Ψ r)
    (t : Fin m → Frame X.Ψ r → ℂ) (ht : ∀ k, X.IsBddSec G (t k))
    (hs : ∀ v : Fin δ → ℂ, ∃ a : Fin m → ℂ, ∀ j, ∑ k, a k * t k (xs j) = v j) :
    ∃ t' : Fin δ → Frame X.Ψ r → ℂ, (∀ k, X.IsBddSec G (t' k)) ∧ IsValBasisM X xs t' := by
  classical
  choose a ha using fun i : Fin δ => hs (Pi.single i 1)
  have hv : ∀ i j, (∑ k, a i k • t k) (xs j) = (Pi.single i (1 : ℂ) : Fin δ → ℂ) j := fun i j => by
    rw [← ha i j, Finset.sum_apply]; rfl
  have hsum : ∀ (c : Fin δ → ℂ) j, ∑ i, c i * (∑ k, a i k • t k) (xs j) = c j := fun c j => by
    simp only [hv]
    simp [Pi.single_apply]
  refine ⟨fun i => ∑ k, a i k • t k, fun i => ?_, fun v => ⟨v, hsum v⟩, fun c hc => ?_⟩
  · exact Finset.sum_induction _ (X.IsBddSec G) (fun _ _ h1 h2 => bdd_add X h1 h2) (bdd_zero X G)
      fun k _ => bdd_smul X _ (ht k)
  · funext j
    rw [← hsum c j, hc j]; rfl

theorem division_one (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (hm : Margins X Xa)
    (hfin : ∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS (Xa.Fp + Xa.T • Xa.L),
      ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x)
    {m : ℕ} (t : Fin m → Frame X.Ψ r → ℂ) (ht : ∀ k, X.IsBddSec Xa.Fp (t k))
    (hs : ∀ v : Fin Fl.δ → ℂ, ∃ a : Fin m → ℂ, ∀ j, ∑ k, a k * t k (Fl.xs j) = v j)
    (f : Frame X.Ψ r → ℂ) (hf : f ∈ X.SSgt (Xa.Fp + Xa.T • Xa.L) Xa.c1)
    (cc : (Fin (nd X) → ℕ) → Fin m → ℂ)
    (hO : ∀ j, (fun z : V (nd X) => f (cpt X (Fl.xs j) z) -
      leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ (Xa.T - nd X)) :
    ∃ h : (Fin (nd X) → ℕ) → Frame X.Ψ r → ℂ,
      (∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), h α ∈ X.SS (Xa.Fp + nd X • Xa.L)) ∧
      ∀ x ∈ X.dom, f x - leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc x =
        ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), monoM X Fl.s α x * h α x := by
  obtain ⟨-, hm2, hm3, -, hcusp⟩ := hm
  have hPD := GlobalTheory.ClosedDiscontinuity.propDisc_closed r X
  have hFM := GlobalTheory.DriftCovolume.finMu_unconditional r X
  obtain ⟨x0, ho, FF, hFF, hmu⟩ := id hFM
  obtain ⟨hb, hint⟩ := DivStartStatement_holds r X Xa Fl hPD hFM m t ht x0 ho FF hFF f hf.1
    ((GlobalTheory.highModes_le_pow_w r X Xa f hf).2 x0 FF hFF hmu) cc
  obtain ⟨t', ht', hbas⟩ := exists_valBasis X Xa.Fp Fl.xs t ht hs
  have hl0 : ∀ x, leadM X Fl.s Fl.w0 t' Xa.T (Xa.T - nd X) 0 x = 0 := fun x => by simp [leadM]
  have hvan := GlobalTheory.vanS_of_isBigO r X Xa Fl (Xa.T - nd X) _ hb.1.1.continuousOn hO
  obtain ⟨h, hh, hx⟩ := divCoreStatement_holds r X Xa Fl hPD hFM hm2 hm3 (hcusp _)
    (by simpa using hcusp 0) (hcusp _) hfin _ t' ht' hbas x0 ho FF hFF _ (hcusp _ _ hb) hint 0
    (by simpa only [hl0, sub_zero] using hvan)
  exact ⟨h, fun α hα => hcusp _ _ (hh α hα), fun x hx' => by simpa only [hl0, sub_zero] using hx x hx'⟩

theorem division_one' (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (hm : Margins X Xa) {D Tn : ℕ}
    (hD : nd X = D) (hT : Xa.T = Tn)
    (hfin : ∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS (Xa.Fp + Tn • Xa.L),
      ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x)
    {m : ℕ} (t : Fin m → Frame X.Ψ r → ℂ) (ht : ∀ k, X.IsBddSec Xa.Fp (t k))
    (hs : ∀ v : Fin Fl.δ → ℂ, ∃ a : Fin m → ℂ, ∀ j, ∑ k, a k * t k (Fl.xs j) = v j)
    (f : Frame X.Ψ r → ℂ) (hf : f ∈ X.SSgt (Xa.Fp + Tn • Xa.L) Xa.c1)
    (cc : (Fin D → ℕ) → Fin m → ℂ)
    (hO : ∀ j, (fun z : V (nd X) => f (cpt X (Fl.xs j) z) - ∑ α ∈ multiLt D (Tn - D), ∑ k,
      cc α k * (∏ q, Fl.s (Fin.cast hD.symm q) (cpt X (Fl.xs j) z) ^ α q) *
        Fl.w0 (cpt X (Fl.xs j) z) ^ (Tn - ∑ q, α q) * t k (cpt X (Fl.xs j) z))
        =O[𝓝 0] fun z => ‖z‖ ^ (Tn - D)) :
    ∃ h : (Fin D → ℕ) → Frame X.Ψ r → ℂ,
      (∀ α ∈ Finset.Nat.antidiagonalTuple D (Tn - D), h α ∈ X.SS (Xa.Fp + D • Xa.L)) ∧
      ∀ x ∈ X.dom, f x - ∑ α ∈ multiLt D (Tn - D), ∑ k,
        cc α k * (∏ q, Fl.s (Fin.cast hD.symm q) x ^ α q) * Fl.w0 x ^ (Tn - ∑ q, α q) * t k x =
        ∑ α ∈ Finset.Nat.antidiagonalTuple D (Tn - D), (∏ q, Fl.s (Fin.cast hD.symm q) x ^ α q) * h α x := by
  subst hD hT
  exact division_one X Xa Fl hm hfin t ht hs f hf cc hO

theorem eventually_diff (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {P : Frame X.Ψ r → ℂ}
    (hP : DifferentiableOn ℂ P X.dom) :
    ∀ᶠ z in 𝓝 (0 : V (nd X)), DifferentiableAt ℂ (fun z => P (cpt X x z)) z := by
  have h0 : (0 : V (nd X)) ∈ OmF X x := by
    show cpt X x 0 ∈ X.dom
    rw [GlobalTheory.LeadJets.cpt_zero]; exact hx
  filter_upwards [(OntoB.isOpen_OmF X x).mem_nhds h0] with z hz
  exact (OntoB.hol_comp X x hP).differentiableAt ((OntoB.isOpen_OmF X x).mem_nhds hz)

theorem division_all {κ : Type} (X : κ → Data E r) (Xa : ∀ k, ArchInM (X k)) (Fl : ∀ k, FlatM (X k) (Xa k))
    (hm : ∀ k, Margins (X k) (Xa k)) {D Tn : ℕ} (hD : ∀ k, nd (X k) = D) (hT : ∀ k, (Xa k).T = Tn)
    (hfin : ∀ k, ∃ (K : ℕ) (g : Fin K → Frame (X k).Ψ r → ℂ), ∀ f ∈ (X k).SS ((Xa k).Fp + Tn • (Xa k).L),
      ∃ c : Fin K → ℂ, ∀ x ∈ (X k).dom, f x = ∑ i, c i * g i x)
    {m : ℕ} (t : Fin m → ∀ k, Frame (X k).Ψ r → ℂ) (ht : ∀ i k, (X k).IsBddSec (Xa k).Fp (t i k))
    (hs : ∀ v : (Σ k, Fin (Fl k).δ) → ℂ, ∃ a : Fin m → ℂ, ∀ p, ∑ i, a i * t i p.1 ((Fl p.1).xs p.2) = v p)
    (f : ∀ k, Frame (X k).Ψ r → ℂ) (hf : ∀ k, f k ∈ (X k).SSgt ((Xa k).Fp + Tn • (Xa k).L) (Xa k).c1) :
    ∃ (cc : (Fin D → ℕ) → Fin m → ℂ) (h : ∀ k, (Fin D → ℕ) → Frame (X k).Ψ r → ℂ),
      (∀ k, ∀ α ∈ Finset.Nat.antidiagonalTuple D (Tn - D), h k α ∈ (X k).SS ((Xa k).Fp + D • (Xa k).L)) ∧
      ∀ k, ∀ x ∈ (X k).dom, f k x - ∑ α ∈ multiLt D (Tn - D), ∑ i,
        cc α i * (∏ q, (Fl k).s (Fin.cast (hD k).symm q) x ^ α q) * (Fl k).w0 x ^ (Tn - ∑ q, α q) * t i k x =
        ∑ α ∈ Finset.Nat.antidiagonalTuple D (Tn - D),
          (∏ q, (Fl k).s (Fin.cast (hD k).symm q) x ^ α q) * h k α x := by
  classical
  have hs0 : ∀ k j a, (Fl k).s a ((Fl k).xs j) = 0 := fun k j =>
    ((Fl k).S_eq _ ((Fl k).xs_mem j)).2 ⟨j, 1, one_mem _, nmat (X k) 0, GlobalTheory.LeadJets.nmat_zero_mem_Bor _, by
      rw [GlobalTheory.LeadJets.rmul_nmat_zero, GlobalTheory.LeadJets.lact_one]⟩
  obtain ⟨cc, hcc⟩ := GlobalTheory.JetsPure.main (Σ k, Fin (Fl k).δ) (Fin m) D Tn (Tn - D) (by omega)
    (fun p => nd (X p.1)) (fun p => finCongr (hD p.1))
    (fun p z => f p.1 (cpt (X p.1) ((Fl p.1).xs p.2) z))
    (fun p z => (Fl p.1).w0 (cpt (X p.1) ((Fl p.1).xs p.2) z))
    (fun p q z => (Fl p.1).s (Fin.cast (hD p.1).symm q) (cpt (X p.1) ((Fl p.1).xs p.2) z))
    (fun p i z => t i p.1 (cpt (X p.1) ((Fl p.1).xs p.2) z))
    (fun p => by
      have hx := (Fl p.1).xs_mem p.2
      refine (eventually_diff _ hx (hf p.1).1.1.1.1).and ((eventually_diff _ hx (Fl p.1).weightForm_vanishes.1.1.1.1).and
        (Filter.Eventually.and ?_ ?_))
      · exact Filter.eventually_all.2 fun q => eventually_diff _ hx ((Fl p.1).s_van _).1.1.1.1
      · exact Filter.eventually_all.2 fun i => eventually_diff _ hx (ht i p.1).1.1)
    (fun p => ⟨by simpa only [GlobalTheory.LeadJets.cpt_zero] using (Fl p.1).w0_ne p.2,
      fun q => by simpa only [GlobalTheory.LeadJets.cpt_zero] using hs0 p.1 p.2 _, (Fl p.1).coord p.2⟩)
    (by simpa only [GlobalTheory.LeadJets.cpt_zero] using hs)
  have hsk : ∀ k, ∀ v : Fin (Fl k).δ → ℂ, ∃ a : Fin m → ℂ, ∀ j, ∑ i, a i * t i k ((Fl k).xs j) = v j := by
    intro k v
    obtain ⟨a, ha⟩ := hs fun p => if hp : p.1 = k then v (Fin.cast (by rw [hp]) p.2) else 0
    exact ⟨a, fun j => by simpa using ha ⟨k, j⟩⟩
  choose h hh hx using fun k => division_one' (X k) (Xa k) (Fl k) (hm k) (hD k) (hT k) (hfin k)
    (fun i => t i k) (fun i => ht i k) (hsk k) (f k) (hf k) cc fun j => hcc ⟨k, j⟩
  exact ⟨cc, h, hh, hx⟩

end Model

section Record

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem sp_le_span_fin {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} (R : Rdg X)
    (u : WeightFamilies.Wt D j) : ∃ (m : ℕ) (g : Fin m → R.Y → ℂ), R.sp u Set.univ ≤ Submodule.span ℂ (Set.range g) := by
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := B.KO) (M := B.Cusp j u)
  refine ⟨m, fun i => R.ev (X.inc u (b i)), Submodule.span_le.2 ?_⟩
  rintro _ ⟨F, -, rfl⟩
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun B.KO).1 (hb ▸ Submodule.mem_top : F ∈ Submodule.span B.KO (Set.range b))
  simp only [map_sum, map_smul, R.ev_smul, SetLike.mem_coe]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem main : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → ∀ (CR c : ℝ), c1 = WeightFamilies.c1 D CR Tn c j → (∀ F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tn c j (addL wF wL Tn), ∀ k : (T.U j T.σ₀).Comp, rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j (addL wF wL Tn) k) c1) → ∀ (m : ℕ) (θ : Fin m → R.Y → ℂ), (∀ i, θ i ∈ R.sp wF Set.univ) → Submodule.span ℂ (Set.range (vals xs θ)) = ⊤ → R.sp (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn)) ≤ Submodule.span ℂ (Set.range (R.lead w t Tn (a0 D j Tn) θ)) ⊔ R.deep w t ((recPlusN h j hj n).wF0 wL wF) (a0 D j Tn) := by
  classical
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en hxs hOnto CR c _ hMg m θ hθ hspan
  have hsp := span_readings_components D T h j hj n R e hR
  have hwt : ∀ (k : (T.U j T.σ₀).Comp) (a : ℕ), laR T j (addL wF wL a) k = (A.Xa k).Fp + a • (A.Xa k).L := fun k a => by
    rw [A.hF, A.hL]
    exact (WtDic.weights_dictionary D T h j hj k).2.2.1 wF wL a
  choose θf hθf hθe using fun i => (hsp wF).1 (θ i) (hθ i)
  have hs : ∀ (i : Fin (WeightFamilies.dimY D j + 1)) (y : R.Y),
      R.s w t i y = ∑ k, t (i, k) * rdR h j (w k) (e y).1 (e y).2.1 := fun i y => by
    unfold Rdg.s
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, smul_eq_mul, hR.2]
  have hs0 : ∀ y, R.s w t 0 y = (Fl.Fl (e y).1).w0 (e y).2.1 := fun y => by rw [hs, Fl.h0]
  have hs1 : ∀ (q : Fin (WeightFamilies.dimY D j)) y,
      R.s w t q.succ y = (Fl.Fl (e y).1).s (Fin.cast (A.dim _).symm q) (e y).2.1 := fun q y => by
    rw [hs, Fl.hs]; rfl
  have hfin : ∀ k : (T.U j T.σ₀).Comp, ∃ (K : ℕ) (g : Fin K → Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ),
      ∀ f ∈ ((T.U j T.σ₀).X k).SS ((A.Xa k).Fp + Tn • (A.Xa k).L),
        ∃ c : Fin K → ℂ, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f x = ∑ i, c i * g i x := by
    intro k
    obtain ⟨K, g, hg⟩ := sp_le_span_fin R (addL wF wL Tn)
    refine ⟨K, fun i x => if hx : x ∈ ((T.U j T.σ₀).X k).dom then g i (e.symm ⟨k, x, hx⟩) else 0, fun f hf => ?_⟩
    have hmem := (hsp (addL wF wL Tn)).2.1 _ _ (hOnto Tn) (Pi.single k f) fun k' => by
      by_cases hk : k' = k
      · subst hk
        rw [Pi.single_eq_same, hwt]; exact hf
      · rw [Pi.single_eq_of_ne hk, hwt]
        exact (A.mar k').2.2.2.2 _ _ (BoundedSectionAlgebra.bdd_zero _ _)
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hg hmem)
    refine ⟨cf, fun x hx => ?_⟩
    have h1 := congrFun hcf (e.symm ⟨k, x, hx⟩)
    rw [Equiv.apply_symm_apply, Finset.sum_apply] at h1
    simp only [dif_pos hx]
    simpa using h1.symm
  have hsurj : ∀ v : (Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ) → ℂ, ∃ a : Fin m → ℂ, ∀ p,
      ∑ i, a i * θf i p.1 ((Fl.Fl p.1).xs p.2) = v p := by
    intro v
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1
      (hspan ▸ Submodule.mem_top : (fun q => v (en q)) ∈ Submodule.span ℂ (Set.range (vals xs θ)))
    refine ⟨a, fun p => ?_⟩
    obtain ⟨q, rfl⟩ := en.surjective p
    rw [← congrFun ha q, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ = a i * θ i (xs q)
    rw [hθe, hxs]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨F, hF, rfl⟩
  obtain ⟨cc, g, hg, hx⟩ := division_all (T.U j T.σ₀).X A.Xa Fl.Fl A.mar A.dim A.hT hfin θf
    (fun i k => by rw [A.hF]; exact (hθf i k).1.1) hsurj (rdR h j F)
    (fun k => by rw [← hwt, A.hc]; exact hMg F hF k)
  have hdec : R.ev ((recPlusN h j hj n).inc (addL wF wL Tn) F) =
      ∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (WeightFamilies.dimY D j) (Tn - WeightFamilies.dimY D j), ∑ i,
        cc α i • (R.mon w t α * R.s w t 0 ^ (Tn - ∑ q, α q) * θ i) +
      ∑ α ∈ Finset.Nat.antidiagonalTuple (WeightFamilies.dimY D j) (Tn - WeightFamilies.dimY D j),
        R.mon w t α * fun y => g (e y).1 α (e y).2.1 := by
    funext y
    rw [hR.2, sub_eq_iff_eq_add'.1 (hx (e y).1 (e y).2.1 (e y).2.2)]
    simp only [Rdg.mon, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, Finset.prod_apply,
      Pi.pow_apply, smul_eq_mul, hs0, hs1, hθe, mul_assoc]
  show R.ev ((recPlusN h j hj n).inc (addL wF wL Tn) F) ∈ _
  rw [hdec]
  refine Submodule.add_mem_sup (Submodule.sum_mem _ fun α hα => Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(⟨α, GlobalTheory.LeadJets.mem_multiLt.1 hα⟩, i), rfl⟩))
    (Submodule.sum_mem _ fun α hα => Submodule.subset_span
      ⟨α, _, Finset.Nat.mem_antidiagonalTuple.1 hα, ?_, rfl⟩)
  exact (hsp (addL wF wL (WeightFamilies.dimY D j))).2.1 _ _ (hOnto _) (fun k => g k α) fun k => by
    rw [hwt]; exact hg k α hα

end Record

end GlobalTheory.Containment
