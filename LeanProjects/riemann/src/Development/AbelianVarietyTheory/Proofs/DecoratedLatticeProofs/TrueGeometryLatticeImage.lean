import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianStepLevelOfChartFormsLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardDatumSplitPlacesOverLevelPrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointBaseLatticeCoordsIntegralLastInPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairFrameCoordinatesIntegralAndFunctionaStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace.PairsFwd

theorem intMat_keeps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] (M M' : Matrix n n k) (hMM : M * M' = 1) (hM : ∀ r s, M r s ∈ 𝒪[k])
    (hM' : ∀ r s, M' r s ∈ 𝒪[k]) (r₀ : n) (hr : ∀ s, valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) < 1) (z : n → k) :
    ((∀ r, (M' *ᵥ z) r ∈ 𝒪[k]) ↔ ∀ r, z r ∈ 𝒪[k]) ∧ ((∀ r, z r ∈ 𝒪[k]) → valuation k ((M' *ᵥ z) r₀ - z r₀) < 1) := by
  have hint : ∀ (N : Matrix n n k), (∀ r s, N r s ∈ 𝒪[k]) → ∀ w : n → k, (∀ r, w r ∈ 𝒪[k]) → ∀ r, (N *ᵥ w) r ∈ 𝒪[k] :=
    fun N hN w hw r => Subring.sum_mem _ fun s _ => Subring.mul_mem _ (hN r s) (hw s)
  refine ⟨⟨fun h r => ?_, fun h => hint M' hM' z h⟩, fun h => ?_⟩
  · have e : M *ᵥ (M' *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
    rw [← e]
    exact hint M hM _ h r
  · have e : (M' *ᵥ z) r₀ - z r₀ = ∑ s, (M' r₀ s - (1 : Matrix n n k) r₀ s) * z s := by
      have : z r₀ = ∑ s, (1 : Matrix n n k) r₀ s * z s := by simp [Matrix.one_apply]
      rw [this]
      simp only [Matrix.mulVec, dotProduct]
      rw [← Finset.sum_sub_distrib]
      simp_rw [sub_mul]
    rw [e]
    refine Valuation.map_sum_lt _ one_ne_zero fun s _ => ?_
    rw [Valuation.map_mul]
    have h1 := hr s
    have h2 : valuation k (z s) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (h s)
    calc valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) * valuation k (z s)
        ≤ valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) * 1 := mul_le_mul' le_rfl h2
      _ < 1 := by rw [mul_one]; exact h1

theorem smul_pair_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (Q : GlobalTheory.LatPair.Pair k (Fin n)) (b b' M M' : Matrix (Fin n) (Fin n) k) (hb : b' * b = 1) (c : k) (r₀ : Fin n)
    (hQ : ∀ (x : Fin n → k) (a : 𝓀[k]), Q.HasVal x a ↔ ∃ y : Fin n → 𝒪[k], (∀ r, (y r : k) = (b *ᵥ x) r) ∧
      ∃ s : 𝒪[k], (s : k) = c ∧ a = residue 𝒪[k] (s * y r₀))
    (g : GL (Fin n) k) (hg : M = b * g.val * b') (hMM : M * M' = 1) (hM : ∀ r s, M r s ∈ 𝒪[k])
    (hM' : ∀ r s, M' r s ∈ 𝒪[k]) (hr : ∀ s, valuation k (M' r₀ s - (1 : Matrix (Fin n) (Fin n) k) r₀ s) < 1) :
    g • Q = Q := by
  have hM'M : M' * M = 1 := mul_eq_one_comm.1 hMM
  have hK := intMat_keeps M M' hMM hM hM' r₀ hr
  have hbg : ∀ x : Fin n → k, b *ᵥ (g⁻¹ • x) = M' *ᵥ (b *ᵥ x) := by
    intro x
    have e1 : b * g.val = M * b := by
      rw [hg, Matrix.mul_assoc, Matrix.mul_assoc, hb, Matrix.mul_one]
    have e2 : b *ᵥ x = M *ᵥ (b *ᵥ (g⁻¹ • x)) := by
      have e3 : x = g.val *ᵥ (g⁻¹ • x) := by
        change x = g.val *ᵥ ((g⁻¹).val *ᵥ x)
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      conv_lhs => rw [e3]
      rw [Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec]
    rw [e2, Matrix.mulVec_mulVec, hM'M, Matrix.one_mulVec]
  refine GlobalTheory.LatPair.Pair.ext fun x a' => ?_
  rw [GlobalTheory.LatPair.Pair.smul_hasVal, hQ, hQ, hbg]
  have hres : ∀ (s y₁ y₂ : 𝒪[k]), valuation k ((y₁ : k) - y₂) < 1 → residue 𝒪[k] (s * y₁) = residue 𝒪[k] (s * y₂) := by
    intro s y₁ y₂ h
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← mul_sub]
    refine Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 ?_)
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 (by simpa using h)
  obtain ⟨hiff, hlast⟩ := hK (b *ᵥ x)
  constructor
  · rintro ⟨y, hy, s, hs, ha⟩
    have hz : ∀ r, (b *ᵥ x) r ∈ 𝒪[k] := hiff.1 fun r => hy r ▸ (y r).2
    refine ⟨fun r => ⟨_, hz r⟩, fun r => rfl, s, hs, ?_⟩
    rw [ha]
    refine hres s _ _ ?_
    rw [hy r₀]
    exact hlast hz
  · rintro ⟨y, hy, s, hs, ha⟩
    have hz : ∀ r, (b *ᵥ x) r ∈ 𝒪[k] := fun r => hy r ▸ (y r).2
    refine ⟨fun r => ⟨_, hiff.2 hz r⟩, fun r => rfl, s, hs, ?_⟩
    rw [ha]
    refine (hres s _ _ ?_).symm
    rw [hy r₀]
    exact hlast hz

theorem col_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) (Lb : Submodule (𝓞 E) (Fin n → E))
    (hL : ∀ x ∈ Lb, ∀ j, ∃ r : 𝓞 E, x j = (r : E)) (v : HeightOneSpectrum (𝓞 F))
    (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))
    (hx : ∀ y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (σ : E →+* E) J Lb)),
      x *ᵥ y - y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) Lb) (s : Fin n) :
    (fun r => x r s - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) r s) ∈
      Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) Lb := by
  subst hJ
  have hd : (Pi.single s 1 : Fin n → E) ∈ Formalism.BasicNotions.dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) Lb := by
    intro z hz
    obtain ⟨r, hr⟩ := hL z hz s
    rw [GlobalTheory.uLocDual_hform_one]
    refine ⟨RingOfIntegers.mapRingHom (σ : E →+* E) r, ?_⟩
    simp [Pi.single_apply, hr]
  have h1 := hx _ (Submodule.subset_span ⟨_, Submodule.subset_span hd, rfl⟩)
  have e : (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) ((Pi.single s 1 : Fin n → E) i)) = Pi.single s 1 := by
    funext i
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs
    · rw [map_one]
    · rw [map_zero]
  beta_reduce at h1
  rw [e, Matrix.mulVec_single_one] at h1
  convert h1 using 1
  funext r
  rw [Pi.sub_apply, Pi.single_apply, Matrix.one_apply]
  rfl

set_option maxHeartbeats 2000000 in

theorem mat_int (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : Formalism.L2.NTheta.IsIdemAt p.e P) (V : HSp D) {n : ℕ}
    (hn : V.rank = n) (t : 𝓞 D.host.E) (ht : t ∈ P.asIdeal) (Lb : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hLb : ∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → t ∣ r)) (κ : GA D V)
    (h3 : ∀ s, (fun r => Formalism.UG.prV (E := D.host.E) p.v (GlobalTheory.AdForm.finM V hn κ r s) -
      (1 : Matrix (Fin n) (Fin n) (D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F)) r s) ∈
        Formalism.UG.latS (F := D.host.F) (p.v.adicCompletion D.host.F) (intV D.host.E p.v) Lb) (r s : Fin V.rank) :
    ((mt V κ).map p.pr) r s ∈ 𝒪[k] ∧ (r.1 + 1 = V.rank →
      valuation k (((mt V κ).map p.pr) r s - (1 : Matrix (Fin V.rank) (Fin V.rank) k) r s) < 1) := by
  subst hn
  let y : Fin V.rank → AE D := fun r' => mt V κ r' s - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) r' s
  have hy : (fun r' => Formalism.UG.prV (E := D.host.E) p.v (toEAf D (y r'))) =
      (fun r' => Formalism.UG.prV (E := D.host.E) p.v (GlobalTheory.AdForm.finM V rfl κ r' s) -
        (1 : Matrix (Fin V.rank) (Fin V.rank) (D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F)) r' s) := by
    funext r'
    simp only [y]
    rw [RingHom.map_sub, RingHom.map_sub]
    congr 1
    by_cases h : r' = s
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, RingHom.map_one]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, RingHom.map_zero, RingHom.map_zero]
  have h4 := GlobalTheory.T.splitPoint_baseLattice_coords_integral_last_in_prime D k p P hP _ t ht _ hLb y (by rw [hy]; exact h3 s) r
  have h1 : p.pr ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) r s) = (1 : Matrix (Fin V.rank) (Fin V.rank) k) r s := by
    simp only [Matrix.one_apply]; split_ifs <;> simp
  simp only [y] at h4
  rw [map_sub, h1] at h4
  refine ⟨?_, fun hr => h4.2 hr⟩
  have := Subring.add_mem _ h4.1 (show (1 : Matrix (Fin V.rank) (Fin V.rank) k) r s ∈ 𝒪[k] by
    simp only [Matrix.one_apply]; split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _)
  rwa [sub_add_cancel] at this

theorem mt_mul_inv {D : D7} (V : HSp D) (κ : GA D V) : mt V κ * mt V κ⁻¹ = 1 := by
  simp only [Formalism.L2.Theta.mt]
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem finM_inv {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (κ : GA D V) (x : GL (Fin n) (GlobalTheory.AdForm.EF D))
    (h : GlobalTheory.AdForm.finM V hn κ = x.1) : GlobalTheory.AdForm.finM V hn κ⁻¹ = (x⁻¹).1 := by
  subst hn
  have e : GlobalTheory.AdForm.finM V rfl κ * GlobalTheory.AdForm.finM V rfl κ⁻¹ = 1 := by
    have e1 : ∀ g, GlobalTheory.AdForm.finM V rfl g = (mt V g).map (toEAf D) := fun g => rfl
    rw [e1, e1, ← Matrix.map_mul, mt_mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [h] at e
  exact (Units.inv_eq_of_mul_eq_one_right e).symm

set_option maxHeartbeats 2000000 in

theorem col_mem_level {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i}
    (F : Formalism.L2.Forms.FormsTiedSym (I.rec7 l Z) u Ch chOf) (hF : I.StdF l Z u F) (i : ℕ) (hi : i ≤ (I.rec7 l Z).R.m)
    (S : Formalism.L2.Forms.StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (Formalism.L2.Forms.sigD (I.rec7 l Z))
      (Formalism.L2.Forms.gramN (I.rec7 l Z) i hi) ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f (Formalism.L2.Forms.badG (I.rec7 l Z)))
    (hLb : ∀ x, x ∈ S.Lb ↔ x ∈ TC.baseL B ((I.rec7 l Z).R.N i) (X.piT u))
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal)
    (x : GL (Fin ((I.rec7 l Z).R.N i)) (GlobalTheory.AdForm.EF (I.rec7 l Z))) (hx : x ∈ S.U) (s : Fin ((I.rec7 l Z).R.N i)) :
    (fun r => Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (x.1 r s) -
      (1 : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i))
        ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) r s) ∈
      Formalism.UG.latS (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (intV (I.rec7 l Z).host.E v) S.Lb := by
  have hgram : Formalism.L2.Forms.gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  haveI : NeZero ((I.rec7 l Z).R.N i) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  let c : 𝓞 (I.rec7 l Z).host.E →+* 𝓞 (I.rec7 l Z).host.E :=
    RingOfIntegers.mapRingHom (Formalism.L2.Forms.sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
  have hsc : ∀ x, (c x : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj (x : (I.rec7 l Z).host.E) :=
    fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
  have hpq : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) * (c F.atT.piU : (I.rec7 l Z).host.E) =
      (((I.rec7 l Z).mem u).A.T : (I.rec7 l Z).host.E) := by
    rw [hsc]; exact F.atT.piU_norm
  have hTp := ((I.rec7 l Z).mem u).A.T_prime
  have hp0 : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) ≠ 0 :=
    fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
  have hL : S.Lb = Formalism.L2.Col.rll_dLat ((I.rec7 l Z).R.N i) (((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E)⁻¹) := by
    refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ F.atT.piU hp0 S.Lb ?_
    rw [hF.piU]; exact hLb
  have h1 := (GlobalTheory.Mem.Col2.Lv.uloc_T_iff (Formalism.L2.Forms.sigD (I.rec7 l Z)) (I.rec7 l Z).sp.cm.deg2 (fun x => star_star x)
    (fun x hx => ((I.rec7 l Z).sp.cm.fixed x).1 hx) (I.rec7 l Z).sp.cm.cmUnram.2.2 hgram S F.atT.piU (c F.atT.piU) rfl hpq hTp hL
    v hv (GlobalTheory.T.levelPrime_dvd_of_adicValuation_lt_one (I.rec7 l Z) u F.atT v hv) _).1 (((S.U_eq x).1 hx).2 v)
  exact col_mem _ hgram S.Lb (fun z hz j => let ⟨r, hr, _⟩ := (hLb z).1 hz j; ⟨r, hr⟩) v _ h1.2 s

set_option maxHeartbeats 4000000 in

theorem stdPair_fixed {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i}
    (F : Formalism.L2.Forms.FormsTiedSym (I.rec7 l Z) u Ch chOf) (hF : I.StdF l Z u F) (j : ℕ) (hj : j ≤ (I.rec7 l Z).R.m)
    (S : Formalism.L2.Forms.StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (Formalism.L2.Forms.sigD (I.rec7 l Z))
      (Formalism.L2.Forms.gramN (I.rec7 l Z) j hj) ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f (Formalism.L2.Forms.badG (I.rec7 l Z)))
    (hLb : ∀ x, x ∈ S.Lb ↔ x ∈ TC.baseL B ((I.rec7 l Z).R.N j) (X.piT u))
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k)
    (β : ∀ j i, GlobalTheory.FinPl.Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → GlobalTheory.LatPair.Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, GlobalTheory.FinPl.Lat ((I.rec7 l Z).sp.X j))
    (hS : GlobalTheory.AdForm.StdT I l Z u p β Q L) (κ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))
    (y : GL (Fin ((I.rec7 l Z).R.N j)) (GlobalTheory.AdForm.EF (I.rec7 l Z)))
    (hy : GlobalTheory.AdForm.finM _ (Formalism.L2.Forms.rankN (I.rec7 l Z) j hj) κ = y.1) (hU : y ∈ S.U) (i : ι)
    (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (hg : (mt _ κ).map (p i).pr = (β j i).b * g.val * (β j i).b') :
    g • Q j i = Q j i := by
  have hv := GlobalTheory.AdForm.stdT_levelPrime_mem_v I hI hP l Z u k ι p β Q L hS i
  obtain ⟨e, he⟩ := hS.1
  have hpi : X.piT u ∈ (e i).1.asIdeal := by
    obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
    have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := hPr.piT_cop u
    have hne : X.piT u ≠ 0 := by
      intro h0
      rw [h0, map_zero, isCoprime_zero_left] at hcop
      exact not_isUnit_zero hcop
    exact (Formalism.L2.Col.mem_divs hne _).1 (e i).2
  have key := fun (κ₀ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (x : GL (Fin ((I.rec7 l Z).R.N j)) (GlobalTheory.AdForm.EF (I.rec7 l Z)))
      (h : GlobalTheory.AdForm.finM _ (Formalism.L2.Forms.rankN (I.rec7 l Z) j hj) κ₀ = x.1) (hx : x ∈ S.U) =>
    mat_int (I.rec7 l Z) k (p i) (e i).1 (he i) _ (Formalism.L2.Forms.rankN (I.rec7 l Z) j hj)
      (X.piT u) hpi _ hLb κ₀ (fun s' => by
        rw [h]
        exact col_mem_level I hI hP l Z u F hF j hj S hLb _ hv x hx s')
  have k1 := key κ y hy hU
  have k2 := key κ⁻¹ y⁻¹ (finM_inv _ _ κ y hy) (inv_mem hU)
  rcases Nat.eq_zero_or_pos ((I.rec7 l Z).sp.X j).rank with h0 | hpos
  · have : g = 1 := Units.ext (Matrix.ext fun b _ => absurd b.2 (by omega))
    rw [this, one_smul]
  let r₀ : Fin ((I.rec7 l Z).sp.X j).rank := ⟨((I.rec7 l Z).sp.X j).rank - 1, by omega⟩
  have hr₀ : r₀.1 + 1 = ((I.rec7 l Z).sp.X j).rank := by simp only [r₀]; omega
  refine smul_pair_eq _ _ _ _ ((mt _ κ⁻¹).map (p i).pr) (β j i).b'b _ r₀
    (GlobalTheory.T.standardPair_frameCoordinates_integral_and_functional I l Z u k ι p β Q L hS j hj i r₀ hr₀) g hg ?_ (fun r s => (k1 r s).1) (fun r s => (k2 r s).1)
    (fun s => (k2 r₀ s).2 hr₀)
  rw [← Matrix.map_mul, mt_mul_inv]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end GlobalTheory.FamTrace.PairsFwd

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.FamTrace.keepsPairs_of_mem_level : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (F0 W u).cls0.lev.U → GlobalTheory.FamTrace.KeepsPairs a κ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a _ hat row col _ κ _ y hy hU i g hg
  obtain ⟨hP⟩ := hA.tr.pins
  obtain ⟨hC⟩ := hA.tr.std
  have hF := hC u
  obtain ⟨k₀, hR⟩ := hF.ends 0 (Nat.zero_le _) (Or.inl rfl)
  exact @GlobalTheory.FamTrace.PairsFwd.stdPair_fixed B X I hA.tr.ok hP l Z u _ _ _ hF 0 (Nat.zero_le _) (F0 W u).cls0.lev
    (fun x => hR.lb () x) a.k a.fld a.val a.top a.loc a.ι _ _ _ _ hat.std κ y.1 hy hU i g hg

end
