import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairFrameCoordinatesIntegralAndFunctiona
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StarEqHostConj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqMulOfValLtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianStepLevelOfChartFormsLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledLatticeVectorMemDualBaseLatticeCompletion
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace.LastRow

theorem row_lt_of_smul_pair_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (Q : GlobalTheory.LatPair.Pair k (Fin n)) (b b' M : Matrix (Fin n) (Fin n) k) (hb : b * b' = 1) (c : k) (r₀ : Fin n)
    (hQ : ∀ (x : Fin n → k) (a : 𝓀[k]), Q.HasVal x a ↔ ∃ y : Fin n → 𝒪[k], (∀ r, (y r : k) = (b *ᵥ x) r) ∧
      ∃ s : 𝒪[k], (s : k) = c ∧ a = residue 𝒪[k] (s * y r₀))
    (g : GL (Fin n) k) (hg : M = b * g.val * b') (hfix : g • Q = Q) (s : Fin n) :
    valuation k (M r₀ s - (1 : Matrix (Fin n) (Fin n) k) r₀ s) < 1 := by
  obtain ⟨x0, hx0⟩ : ∃ x, Q.fn x ≠ 0 := by
    by_contra h
    exact Q.fn_ne (LinearMap.ext fun x => not_not.1 fun hx => h ⟨x, hx⟩)
  obtain ⟨y0, -, s0, hs0, ha0⟩ := (hQ x0.1 (Q.fn x0)).1 ⟨x0.2, rfl⟩
  have hu : residue 𝒪[k] s0 ≠ 0 := by
    intro h
    apply hx0
    rw [ha0, map_mul, h, zero_mul]
  let yE : Fin n → 𝒪[k] := Pi.single s 1
  have hyE : ∀ r, (yE r : k) = (Pi.single s 1 : Fin n → k) r := by
    intro r
    simp only [yE, Pi.single_apply]
    split_ifs <;> rfl
  have h1 : Q.HasVal (b' *ᵥ Pi.single s 1) (residue 𝒪[k] (s0 * yE r₀)) := by
    refine (hQ _ _).2 ⟨yE, fun r => ?_, s0, hs0, rfl⟩
    rw [Matrix.mulVec_mulVec, hb, Matrix.one_mulVec, hyE]
  have h2 : Q.HasVal (g • (b' *ᵥ (Pi.single s 1 : Fin n → k))) (residue 𝒪[k] (s0 * yE r₀)) := by
    rw [← hfix, GlobalTheory.LatPair.Pair.smul_hasVal, inv_smul_smul]
    exact h1
  obtain ⟨y1, hy1, s1, hs1, ha1⟩ := (hQ _ _).1 h2
  obtain rfl : s1 = s0 := Subtype.ext (hs1.trans hs0.symm)
  have hM : (y1 r₀ : k) = M r₀ s := by
    rw [hy1]
    change (b *ᵥ (g.val *ᵥ (b' *ᵥ (Pi.single s 1 : Fin n → k)))) r₀ = _
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hg, Matrix.mulVec_single_one]
    rfl
  have h3 : residue 𝒪[k] (y1 r₀ - yE r₀) = 0 := by
    rw [map_mul, map_mul] at ha1
    rw [map_sub, mul_left_cancel₀ hu ha1, sub_self]
  have h4 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1
    ((IsLocalRing.mem_maximalIdeal _).1 ((IsLocalRing.residue_eq_zero_iff _).1 h3))
  have h5 : ((y1 r₀ - yE r₀ : 𝒪[k]) : k) = M r₀ s - (1 : Matrix (Fin n) (Fin n) k) r₀ s := by
    rw [AddSubgroupClass.coe_sub, hM, hyE, Pi.single_apply, Matrix.one_apply]
  rw [← h5]
  exact h4

set_option maxHeartbeats 1000000 in

theorem exists_gl {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : GlobalTheory.FinPl.SplitPt D k} {V : HSp D} (β : GlobalTheory.FinPl.Frame p V (Fin V.rank)) (κ : GA D V) :
    ∃ g : GL (Fin V.rank) k, (mt V κ).map p.pr = β.b * g.val * β.b' := by
  have hm : ∀ x y : GA D V, x * y = 1 → (mt V x).map p.pr * (mt V y).map p.pr = 1 := by
    intro x y h
    have e : mt V x * mt V y = 1 := by
      simp only [Formalism.L2.Theta.mt]
      rw [← Units.val_mul, ← map_mul, h, map_one, Units.val_one]
    rw [← Matrix.map_mul, e]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hc : ∀ A A' : Matrix (Fin V.rank) (Fin V.rank) k, A * A' = 1 → (β.b' * A * β.b) * (β.b' * A' * β.b) = 1 := by
    intro A A' h
    calc (β.b' * A * β.b) * (β.b' * A' * β.b) = β.b' * (A * ((β.b * β.b') * A')) * β.b := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [β.bb', Matrix.one_mul, h, Matrix.mul_one, β.b'b]
  refine ⟨⟨β.b' * (mt V κ).map p.pr * β.b, β.b' * (mt V κ⁻¹).map p.pr * β.b, hc _ _ (hm _ _ (mul_inv_cancel κ)),
    hc _ _ (hm _ _ (inv_mul_cancel κ))⟩, ?_⟩
  calc (mt V κ).map p.pr = (β.b * β.b') * (mt V κ).map p.pr * (β.b * β.b') := by rw [β.bb', Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

set_option maxHeartbeats 2000000 in

theorem entry_cong (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : Formalism.L2.NTheta.IsIdemAt p.e P) (T : ℕ)
    (t t' : 𝓞 D.host.E) (h1 : (t' : D.host.E) = star (t : D.host.E)) (h2 : t * t' = (T : 𝓞 D.host.E)) (h3 : IsCoprime t t')
    (h4 : t ∈ P.asIdeal) (h5 : (T : 𝓞 D.host.F) ∈ p.v.asIdeal) (h6 : (T : 𝓞 D.host.F) ∉ p.v.asIdeal ^ 2)
    (V : HSp D) {n : ℕ} (hn : V.rank = n) (κ : GA D V) (r s : Fin n)
    (hi : Formalism.UG.prV (E := D.host.E) p.v (GlobalTheory.AdForm.finM V hn κ r s) ∈ Formalism.BasicNotions.intV D.host.E p.v)
    (hl : valuation k (((mt V κ).map p.pr) ((finCongr hn).symm r) ((finCongr hn).symm s) -
      (1 : Matrix (Fin V.rank) (Fin V.rank) k) ((finCongr hn).symm r) ((finCongr hn).symm s)) < 1) :
    ∃ c ∈ Formalism.BasicNotions.intV D.host.E p.v, Formalism.UG.prV (E := D.host.E) p.v (GlobalTheory.AdForm.finM V hn κ r s) -
      (1 : Matrix (Fin n) (Fin n) (D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F)) r s =
        Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (t : D.host.E) * c := by
  subst hn
  let y : AE D := mt V κ r s - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) r s
  have hy : Formalism.UG.prV (E := D.host.E) p.v (toEAf D y) = Formalism.UG.prV (E := D.host.E) p.v (GlobalTheory.AdForm.finM V rfl κ r s) -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F)) r s := by
    simp only [y]
    rw [RingHom.map_sub, RingHom.map_sub]
    congr 1
    by_cases h : r = s
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, RingHom.map_one]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, RingHom.map_zero, RingHom.map_zero]
  have h7 : p.pr ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) r s) = (1 : Matrix (Fin V.rank) (Fin V.rank) k) r s := by
    simp only [Matrix.one_apply]; split_ifs <;> simp
  rw [← hy]
  refine GlobalTheory.LocMod.SplitUnif.eq_mul_of_val_lt_one D k p P hP T t t' h1 h2 h3 h4 h5 h6 y ?_ ?_
  · rw [hy]
    refine Subring.sub_mem _ hi ?_
    simp only [Matrix.one_apply]; split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · simp only [y]
    rw [map_sub, h7]
    exact hl

end GlobalTheory.FamTrace.LastRow

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.FamTrace.lastRow_cong_of_keepsPairs : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), GlobalTheory.FamTrace.KeepsPairs a κ → (∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (r s : Fin ((I.rec7 l Z).R.N 0)), Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ r s) ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E v) → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), (((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) → ∀ s : Fin ((I.rec7 l Z).R.N 0), ∃ c ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E v, Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ (Formalism.L2.Col.lastIdx _) s) - (1 : Matrix (Fin ((I.rec7 l Z).R.N 0)) (Fin ((I.rec7 l Z).R.N 0)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) (Formalism.L2.Col.lastIdx _) s = Formalism.UG.inclE (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (show (I.rec7 l Z).host.E from (X.piT u : B.fields.E)) * c := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat κ hκ hkp hint v hv s
  letI := a.fld; letI := a.val; letI := a.top; haveI := a.loc
  have htP : ∀ p, p ∈ a.v.tP ↔ ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ p.asIdeal := by
    have hψ := hat.pinX.std
    let row : ∀ t, RowCh (pk W) (lvP W) u a.g t := fun t =>
      { vP := fun _ => 0, vT := fun _ _ => 0,
        sBF := fun j ρ h => (GlobalTheory.Unf.Inhab.nonempty_stepBF hψ _ _).some,
        sFB := fun j σ h => (GlobalTheory.Unf.Inhab.nonempty_stepFB hψ _ _).some,
        io := fun _ => 0, ioT := fun _ _ => 0 }
    exact (ha.tie row (fun t =>
      { kom := fun _ => 1, Ch := fun _ => Unit, fin := fun _ => inferInstance, dd := fun _ _ _ => 0, e := fun _ _ => 0,
        eT := fun _ _ _ => 0, Ram := fun _ => Set.univ, S := fun _ => id, rd := fun _ _ _ _ _ => 0, cV := fun _ => 1,
        cK := fun _ => 1, cP := 1 })).1.tP
  obtain ⟨i, rfl⟩ := (ha.shape.pre.tP v).1 ((htP v).2 hv)
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  obtain ⟨e, he⟩ := hat.std.1
  have hpi : X.piT u ∈ (e i).1.asIdeal := by
    have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := hPr.piT_cop u
    have hne : X.piT u ≠ 0 := by
      intro h0
      rw [h0, map_zero, isCoprime_zero_left] at hcop
      exact not_isUnit_zero hcop
    exact (Formalism.L2.Col.mem_divs hne _).1 (e i).2
  have hn := Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)
  haveI : NeZero ((I.rec7 l Z).R.N 0) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  set r₀ : Fin ((I.rec7 l Z).sp.X 0).rank := (finCongr hn).symm (Formalism.L2.Col.lastIdx _) with hr₀def
  set s' : Fin ((I.rec7 l Z).sp.X 0).rank := (finCongr hn).symm s with hs'def
  have hr₀ : r₀.1 + 1 = ((I.rec7 l Z).sp.X 0).rank := by
    have h1 : (Formalism.L2.Col.lastIdx ((I.rec7 l Z).R.N 0)).1 = (I.rec7 l Z).R.N 0 - 1 := rfl
    have h2 : r₀.1 = (Formalism.L2.Col.lastIdx ((I.rec7 l Z).R.N 0)).1 := rfl
    have h3 := NeZero.ne ((I.rec7 l Z).R.N 0)
    omega
  have hQ := GlobalTheory.AdForm.stdT_pair_coords I l Z u a.k a.ι a.o.p a.o.β a.o.Q _ hat.std 0 (Nat.zero_le _) i r₀ hr₀
  obtain ⟨g, hg⟩ := GlobalTheory.FamTrace.LastRow.exists_gl (a.o.β 0 i) κ
  have hl := GlobalTheory.FamTrace.LastRow.row_lt_of_smul_pair_eq _ _ _ _ (a.o.β 0 i).bb' _ r₀ hQ g hg (hkp i g hg) s'
  exact GlobalTheory.FamTrace.LastRow.entry_cong (I.rec7 l Z) a.k (a.o.p i) (e i).1 (he i) ((I.rec7 l Z).mem u).A.T (X.piT u)
    (B.fields.conjO (X.piT u)) ((B.fields_conjO_coe _).trans (GlobalTheory.RankOneLine.star_eq_hostConj (I.rec7 l Z) _).symm)
    (hPr.piT_norm u) (hPr.piT_cop u) hpi hv (GlobalTheory.LevelUnif.T_notMem_sq (I.rec7 l Z) u (W.R.T.cols.forms u).atT _ hv)
    _ hn κ _ s (hint _ _ s) hl

end
