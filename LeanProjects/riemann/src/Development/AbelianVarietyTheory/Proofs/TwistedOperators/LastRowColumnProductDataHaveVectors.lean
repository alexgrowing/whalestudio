import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentExistsResidueCardPowMemNhds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffIntegralOnUnitHalf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedModelVacuumEqIntegralMatrixIndicator
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsClearingIntegersPrincipalDatumHost
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFlipStageIsTensorPlaceDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumOverFinitePlacesUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.VecsLast

open ValuativeRel

theorem exists_nat_val_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (d : ℕ) :
    ∃ N : ℕ, 0 < N ∧ valuation k (N : k) ≤ valuation k ((ϖ ^ d : kˣ) : k) := by
  refine ⟨GlobalTheory.SplitWeil.resCard k ^ d, pow_pos ?_ d, ?_⟩
  · unfold GlobalTheory.SplitWeil.resCard
    exact Nat.card_pos
  · rw [Nat.cast_pow, map_pow, Units.val_pow_eq_pow_val, map_pow, hϖ]
    exact pow_le_pow_left₀ zero_le' (le_uniformizer_iff.2 GlobalTheory.RootEx.UnipPow.valuation_resCard_lt_one) d

end GlobalTheory.VecsLast

namespace GlobalTheory.VecsLast

open ValuativeRel

variable {D : D7}

theorem isSBHalf_prodCoord {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {P : Finset (Pl D.host.E)}
    {A B : P → Type} [∀ w, Fintype (A w)] [∀ w, Fintype (B w)]
    (c : ∀ w : P, Mx D m n →+ Matrix (A w) (B w) (Kw w.1))
    (hc : ∀ z, IsHalf e z → (z ∈ Λ ↔ ∀ w : P, GlobalTheory.StepData.IntM (c w z)))
    (d : P → ℕ) (ψ : ∀ w : P, Matrix (A w) (B w) (Kw w.1) → ℂ)
    (h1 : ∀ w M, ψ w M ≠ 0 → GlobalTheory.StepData.IntM M)
    (h2 : ∀ w M N, (∀ i j, valuation (Kw w.1) (N i j) ≤ valuation (Kw w.1) ((unifAt w.1 ^ d w : (Kw w.1)ˣ) : Kw w.1)) →
      ψ w (M + N) = ψ w M) :
    IsSBHalf e Λ (fun z => if IsHalf e z then ∏ w : P, ψ w (c w z) else 0) := by
  classical
  choose N hN0 hN using fun w : P => exists_nat_val_le (isUnif_unifAt (D := D) w.1) (d w)
  have hk0 : 0 < ∏ w : P, N w := Finset.prod_pos fun w _ => hN0 w
  have hhalf : ∀ (a : ℕ) (u : Mx D m n), IsHalf e u → IsHalf e (a • u) := fun a u hu i j => by
    show e * (a • u) i j = (a • u) i j
    rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu i j]
  have hadd : ∀ {t u : Mx D m n}, IsHalf e u → (IsHalf e (t + u) ↔ IsHalf e t) := fun {t u} hu => by
    constructor
    · intro h i j
      have h1 := h i j
      have h2 := hu i j
      simp only [Matrix.add_apply, mul_add] at h1
      linear_combination h1 - h2
    · intro h i j
      simp only [Matrix.add_apply, mul_add, h i j, hu i j]
  refine ⟨fun t ht => ?_, ∏ w : P, N w, hk0, fun u hu hue t => ?_, fun t ht => ?_⟩
  · by_contra hc'
    exact ht (if_neg hc')
  · have hku := hhalf (∏ w : P, N w) u hue
    dsimp only
    by_cases ht : IsHalf e t
    · rw [if_pos ((hadd hku).2 ht), if_pos ht]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [map_add, map_nsmul]
      refine h2 w _ _ fun i j => ?_
      have hint := (hc u hue).1 hu w i j
      rw [Valuation.mem_integer_iff] at hint
      rw [Matrix.smul_apply, nsmul_eq_mul, map_mul]
      have hle : valuation (Kw w.1) (((∏ w : P, N w : ℕ) : Kw w.1)) ≤ valuation (Kw w.1) (N w : Kw w.1) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w), Nat.cast_mul, map_mul]
        exact mul_le_of_le_one_right' (GlobalTheory.RootEx.UnipPow.valuation_natCast_le_one _)
      calc valuation (Kw w.1) (((∏ w : P, N w : ℕ) : Kw w.1)) * valuation (Kw w.1) (c w u i j)
          ≤ valuation (Kw w.1) (((∏ w : P, N w : ℕ) : Kw w.1)) := mul_le_of_le_one_right' hint
        _ ≤ _ := hle.trans (hN w)
    · rw [if_neg (fun h => ht ((hadd hku).1 h)), if_neg ht]
  · dsimp only at ht
    have hE : IsHalf e t := by
      by_contra h
      exact ht (if_neg h)
    rw [if_pos hE] at ht
    have hmem : t ∈ Λ := (hc t hE).2 fun w => h1 w _ (Finset.prod_ne_zero_iff.1 ht w (Finset.mem_univ _))
    exact Λ.nsmul_mem hmem _

end GlobalTheory.VecsLast

namespace GlobalTheory.VecsLast

open ValuativeRel

variable {D : D7}

theorem isSBHalf_frames {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} (hβS : IsFrame βS ΛS) (hβT : IsFrame βT ΛT)
    {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hAA : ∀ w ∈ P, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1))
    {A B : P → Type} [∀ w, Fintype (A w)] [∀ w, Fintype (B w)]
    (c : ∀ w : P, WO S T →+ Matrix (A w) (B w) (Kw w.1))
    (hc : ∀ (w : P) z, GlobalTheory.StepData.IntM (c w z) ↔
      GlobalTheory.StepData.IntM ((Comparison₂.fr βT βS (z.map (toEAf D))).map (cpt (D := D) w.1)))
    (d : P → ℕ) (ψ : ∀ w : P, Matrix (A w) (B w) (Kw w.1) → ℂ)
    (h1 : ∀ w M, ψ w M ≠ 0 → GlobalTheory.StepData.IntM M)
    (h2 : ∀ w M N, (∀ i j, valuation (Kw w.1) (N i j) ≤ valuation (Kw w.1) ((unifAt w.1 ^ d w : (Kw w.1)ˣ) : Kw w.1)) →
      ψ w (M + N) = ψ w M) :
    IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      (fun z => if IsHalf e z then ∏ w : P, ψ w (c w z) else 0) := by
  refine isSBHalf_prodCoord c (fun z hz => ?_) d ψ h1 h2
  rw [GlobalTheory.ColLatDict.mem_latO_iff_intM hS hT hβS hβT he hAA z hz]
  exact ⟨fun h w => (hc w z).2 (h w.1 w.2), fun h w hw => (hc ⟨w, hw⟩ z).1 (h ⟨w, hw⟩)⟩

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem coord_add (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m)
    (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m)
    (x y : Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (Kw w)) :
    B.coord t w hX hY (x + y) = B.coord t w hX hY x + B.coord t w hX hY y := by
  unfold Frames.coord
  rw [Matrix.mul_add, Matrix.add_mul]
  rfl

noncomputable def coordHom (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m)
    (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m) :
    Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (AE D) →+
      Matrix (Fin ((locGrid G t w).rank Y)) (Fin ((locGrid G t w).rank X)) (Kw w) :=
  AddMonoidHom.mk' (fun z => B.coord t w hX hY (z.map fun a => cpt w (toEAf D a))) fun x y => by
    rw [Matrix.map_add _ (fun a b => by rw [RingHom.map_add, RingHom.map_add])]
    exact coord_add B t w hX hY _ _

theorem coordHom_int_iff (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m)
    (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m) (z : Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (AE D)) :
    GlobalTheory.StepData.IntM (coordHom B t w hX hY z) ↔
      GlobalTheory.StepData.IntM ((Comparison₂.fr (B.β X.1 X.2) (B.β Y.1 Y.2) (z.map (toEAf D))).map (cpt (D := D) w)) :=
  GlobalTheory.MixVacBig.coord_int_iff B t w hX hY z

theorem natDatum_props {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} {ϖ : kˣ} {dp : ℕ} {φ : Matrix a b k → ℂ} (h : GlobalTheory.SplitFlip.IsNatDatum ϖ dp φ) :
    (∀ M, φ M ≠ 0 → GlobalTheory.StepData.IntM M) ∧
      ∀ M N, (∀ i j, valuation k (N i j) ≤ valuation k ((ϖ ^ dp : kˣ) : k)) → φ (M + N) = φ M := by
  obtain ⟨hs, hi⟩ := h
  refine ⟨fun M hM i j => ?_, fun M N hN => hi M N ?_⟩
  · by_contra hc
    refine hM (hs M fun hm => hc ?_)
    have := GlobalTheory.SplitFlip.FourierDepth.mem_matLat_diagLat.1 hm i j
    rw [Valuation.mem_integer_iff]
    simpa using this
  · exact GlobalTheory.SplitFlip.FourierDepth.mem_matLat_smul_stdLat.2 hN

end GlobalTheory.VecsLast

namespace GlobalTheory.VecsLast

theorem vecs_last : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → (∀ j : Fin D.R.m, ∃ f, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) f) ∧ ∀ i : Fin D.R.m, ∃ f, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) f := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t e he φ hφ
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hAA : ∀ w ∈ locPl ch.G t, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := by
    intro w hw
    have hb := GlobalTheory.FunObj.Good.badInt_notMem hL (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hch.guard t) hw
    have h2q := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
    have hN := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))
    refine ⟨fun a ha => ?_, ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩⟩
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_le_one_of_mem h2q (Or.inl ha)
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_nat hN
  refine ⟨fun j => ?_, fun i => ?_⟩
  · have hS : IsSelfDualC (ch.G.pS (.mu t D.R.m j)) (ch.G.latS (.mu t D.R.m j)) :=
      (node_isV ch.G hL (X := .grid D.R.m j) ⟨le_rfl, j.2.le⟩).sd
    have hT : IsSelfDualC (ch.G.pT (.mu t D.R.m j)) (ch.G.latT (.mu t D.R.m j)) :=
      (node_isV ch.G hL (X := .grid D.R.m ((j : ℕ) + 1)) ⟨le_rfl, j.2⟩).sd
    have hβS := ch.S.B.isFrame_β hL (i := D.R.m) (j := (j : ℕ)) le_rfl j.2.le
    have hβT := ch.S.B.isFrame_β hL (i := D.R.m) (j := (j : ℕ) + 1) le_rfl j.2
    have hmem : GlobalTheory.SplitFlip.Edge.theta D.R.m j ∈ GlobalTheory.SplitFlip.oppositePath D.R.m := by
      simp [GlobalTheory.SplitFlip.oppositePath]
    have hSB := isSBHalf_frames hS hT hβS hβT he hAA
      (fun w => coordHom ch.S.B t w.1 (X := (D.R.m, (j : ℕ) + 1)) (Y := (D.R.m, (j : ℕ))) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩)
      (fun w z => coordHom_int_iff ch.S.B t w.1 (X := (D.R.m, (j : ℕ) + 1)) (Y := (D.R.m, (j : ℕ))) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ z) (fun w => depthAt ch.G w.1) (fun w => φ w (.theta D.R.m j))
      (fun w => (natDatum_props (hφ w _ hmem)).1) (fun w => (natDatum_props (hφ w _ hmem)).2)
    obtain ⟨f, hf⟩ := GlobalTheory.FunObj.VecEx.exists_isThetaAt_of_vac hS.1 hT.1 hS hT he (ch.rm.vT_is t D.R.m j le_rfl j.2) hSB
    exact ⟨f, hSB, hf⟩
  · have hS : IsSelfDualC (ch.G.pS (.chi i D.R.m)) (ch.G.latS (.chi i D.R.m)) :=
      isSelfDualC_neg (node_isV ch.G hL (X := .grid ((i : ℕ) + 1) D.R.m) ⟨i.2, le_rfl⟩).sd
    have hT : IsSelfDualC (ch.G.pT (.chi i D.R.m)) (ch.G.latT (.chi i D.R.m)) :=
      (node_isV ch.G hL (X := .grid (i : ℕ) D.R.m) ⟨i.2.le, le_rfl⟩).sd
    have hβS := ch.S.B.isFrame_β hL (i := (i : ℕ) + 1) (j := D.R.m) i.2 le_rfl
    have hβT := ch.S.B.isFrame_β hL (i := (i : ℕ)) (j := D.R.m) i.2.le le_rfl
    have hmem : GlobalTheory.SplitFlip.Edge.ex i D.R.m ∈ GlobalTheory.SplitFlip.oppositePath D.R.m := by
      simp [GlobalTheory.SplitFlip.oppositePath]
    have hSB := isSBHalf_frames hS hT hβS hβT he hAA
      (fun w => coordHom ch.S.B t w.1 (X := ((i : ℕ), D.R.m)) (Y := ((i : ℕ) + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩)
      (fun w z => coordHom_int_iff ch.S.B t w.1 (X := ((i : ℕ), D.R.m)) (Y := ((i : ℕ) + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ z) (fun w => depthAt ch.G w.1) (fun w => φ w (.ex i D.R.m))
      (fun w => (natDatum_props (hφ w _ hmem)).1) (fun w => (natDatum_props (hφ w _ hmem)).2)
    obtain ⟨f, hf⟩ := GlobalTheory.FunObj.VecEx.exists_isThetaAt_of_vac hS.1 hT.1 hS hT he (ch.rm.vX_is i D.R.m i.2 le_rfl) hSB
    exact ⟨f, hSB, hf⟩

end GlobalTheory.VecsLast
