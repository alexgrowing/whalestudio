import Mathlib
import Formalism.LocalToGlobal.Columns.ToHLat
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Columns.LocWLemmas
import Formalism.LocalToGlobal.Columns.AtTRank
import Formalism.LocalToGlobal.Columns.DiamondPreservesRamified
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.CmUnramifiedOfFieldConditions
import Formalism.LocalToGlobal.Columns.RowFormsRat
import Formalism.LocalToGlobal.Columns.RowFormsSym
import Formalism.LocalToGlobal.Columns.SliceIntegralDeltaNeBot
import Formalism.LocalToGlobal.Columns.SummandSlopeAtDecoratedLattice
import Formalism.LocalToGlobal.Columns.BrzoPairAtZeroRight
import Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.FormalDegreeBessel.FdegFactorial

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

structure ColObj (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) where

  f : ℕ

  k : ℕ

  m : ℕ

  T : I → ℕ

  Mf : I → HLat K

  M : I → HLat K

  incl : ∀ u, (M u).V →ₗ[K] (Mf u).V

  Vr : ∀ u, InfinitePlace K → Matrix (Mf u).ι (M u).ι ℂ

  dstar : I → ℝ

  overPi : I → HeightOneSpectrum (𝓞 K) → Prop

  Nlam : ∀ u, HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (M u).V

  lamT : I → ℝ

  Nu : ∀ u, Submodule (𝓞 K) (M u).V

  supp : Finset (HeightOneSpectrum (𝓞 K))

  sg : I → HeightOneSpectrum (𝓞 K) → ℝ

  tau : HeightOneSpectrum (𝓞 K) → ℝ

  zLow : I → ℝ

  zUp : I → ℝ

  Dstar : ℝ

  Xu : I → ℝ

  xLow : ℝ

  xUp : ℝ

  xVar : ℝ

  Mtil : HLat K

namespace ColObj

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} (C : ColObj K I)

def S : Finset (Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K) := C.supp.map (plEquiv K).toEmbedding

def sgExpW (u : I) (w : HeightOneSpectrum (𝓞 K)) : ℤ := ⌊(eW w : ℝ) * C.sg u w⌋

def sgExp (u : I) : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K →₀ ℤ :=
  Finsupp.indicator C.S fun z _ => C.sgExpW u ((plEquiv K).symm z)

def tauExpW (w : HeightOneSpectrum (𝓞 K)) : ℤ := ⌊(eW w : ℝ) * C.tau w⌋

def tauExp : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K →₀ ℤ :=
  Finsupp.indicator C.S fun z _ => C.tauExpW ((plEquiv K).symm z)

def ItM (u : I) : Submodule (𝓞 K) (C.M u).V :=
  Formalism.HermitianLatticesTheory.idealSmul ((Formalism.LFunctionChainParameters.slopeLatticeData.idealPow C.tauExp : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
    Submodule (𝓞 K) K) (C.M u).L

def Npr (u : I) : Submodule (𝓞 K) (C.M u).V := Formalism.LFunctionChainParameters.slopeLatticeData.modLat (C.sgExp u) (C.Nu u)

@[reducible] def NuH (u : I) : HLat K := Formalism.L2.GlobalTheoryTheory.HLatOps.withL (C.M u) (C.Nu u)

@[reducible] def NprH (u : I) : HLat K := Formalism.L2.GlobalTheoryTheory.HLatOps.withL (C.M u) (C.Npr u)

def lenMN (u : I) (w : HeightOneSpectrum (𝓞 K)) : ℚ := lenUW w (C.M u).L (C.Nu u)

def du (u : I) : ℕ := Fintype.card (C.M u).ι

def dM (u : I) : ℕ := Fintype.card (C.Mf u).ι

theorem mem_S (z : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K) : z ∈ C.S ↔ (plEquiv K).symm z ∈ C.supp := by
  unfold S
  rw [Finset.mem_map_equiv]

theorem plEquiv_mem_S (w : HeightOneSpectrum (𝓞 K)) : plEquiv K w ∈ C.S ↔ w ∈ C.supp := by
  rw [mem_S, Equiv.symm_apply_apply]

theorem sgExp_of_mem (u : I) {w : HeightOneSpectrum (𝓞 K)} (h : w ∈ C.supp) :
    C.sgExp u (plEquiv K w) = C.sgExpW u w := by
  unfold sgExp
  rw [Finsupp.indicator_of_mem ((C.plEquiv_mem_S w).2 h), Equiv.symm_apply_apply]

theorem sgExp_of_not_mem (u : I) {w : HeightOneSpectrum (𝓞 K)} (h : w ∉ C.supp) : C.sgExp u (plEquiv K w) = 0 := by
  unfold sgExp
  exact Finsupp.indicator_of_notMem (fun h' => h ((C.plEquiv_mem_S w).1 h')) _

theorem tauExp_of_mem {w : HeightOneSpectrum (𝓞 K)} (h : w ∈ C.supp) : C.tauExp (plEquiv K w) = C.tauExpW w := by
  unfold tauExp
  rw [Finsupp.indicator_of_mem ((C.plEquiv_mem_S w).2 h), Equiv.symm_apply_apply]

theorem tauExp_of_not_mem {w : HeightOneSpectrum (𝓞 K)} (h : w ∉ C.supp) : C.tauExp (plEquiv K w) = 0 := by
  unfold tauExp
  exact Finsupp.indicator_of_notMem (fun h' => h ((C.plEquiv_mem_S w).1 h')) _

theorem sgExpW_div_le (u : I) (w : HeightOneSpectrum (𝓞 K)) :
    (C.sgExpW u w : ℝ) / (eW w : ℝ) ≤ C.sg u w ∧ C.sg u w < ((C.sgExpW u w : ℝ) + 1) / (eW w : ℝ) := by
  have he : (0 : ℝ) < (eW w : ℝ) := by exact_mod_cast eW_pos w
  constructor
  · rw [div_le_iff₀ he, mul_comm]
    exact Int.floor_le _
  · rw [lt_div_iff₀ he, mul_comm]
    exact Int.lt_floor_add_one _

end ColObj

structure ColIface (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) extends ColObj K I where

  cplx : IsTotallyComplex K
  f_pos : 0 < f

  T_prime : ∀ u, (T u).Prime

  T_big : ∀ u, 4 * f ≤ T u

  Mf_good : ∀ u, (Mf u).Good

  M_good : ∀ u, (M u).Good
  incl_inj : ∀ u, Function.Injective (incl u)

  incl_norm : ∀ u v (x : (M u).V),
    Formalism.HermitianLatticesTheory.normAt (M u).b (M u).X v x = Formalism.HermitianLatticesTheory.normAt (Mf u).b (Mf u).X v (incl u x)

  M_L : ∀ u, (M u).L = (Mf u).L.comap ((incl u).restrictScalars (𝓞 K))

  Vr_iso : ∀ u v, (Vr u v)ᴴ * Vr u v = 1

  Vr_fcoord : ∀ u v (x : (M u).V),
    Formalism.HermitianLatticesTheory.fcoord (Mf u).b (Mf u).X v (incl u x) = (Vr u v).mulVec (Formalism.HermitianLatticesTheory.fcoord (M u).b (M u).X v x)

  rank_full : ∀ u, (Fintype.card (Mf u).ι : ℝ) = dstar u * ((T u : ℝ) ^ k - 1) ^ f
  dstar_pos : ∀ u, 0 < dstar u

  rank_ram : ∀ u, (Fintype.card (M u).ι : ℝ) = (Fintype.card (Mf u).ι : ℝ) * (1 - 1 / ((T u : ℝ) - 1)) ^ f
  rank_pos : ∀ u, 0 < Fintype.card (M u).ι

  slope_ram : ∀ u, (M u).mu = (Mf u).mu - (f : ℝ) * Real.log ((T u : ℝ) - 1) / ((T u : ℝ) - 2)

  slopeMax_ram : ∀ u, (M u).muMax ≤ (Mf u).muMax

  Nlam_le : ∀ u w, prW w = T u → atW w (Nlam u w) ≤ atW w (M u).L

  Nlam_bar : ∀ u w, prW w = T u → ¬ overPi u w → atW w (Nlam u w) = atW w (M u).L

  Nlam_len : ∀ u w, prW w = T u →
    ((lenUW w (M u).L (Nlam u w) : ℚ) : ℝ) ≤ (Fintype.card (Mf u).ι : ℝ) * lamT u
  lamT_nonneg : ∀ u, 0 ≤ lamT u

  Nu_fg : ∀ u, (Nu u).FG

  Nu_comm : ∀ u, ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ y ∈ (M u).L, c • y ∈ Nu u

  Nu_atT : ∀ u w, prW w = T u → atW w (Nu u) = atW w (Nlam u w)

  Nu_off : ∀ u w, w ∉ supp → atW w (Nu u) = atW w (M u).L

  Nu_le_ItM : ∀ u, Nu u ≤ toColObj.ItM u

  tau_nonneg : ∀ w, 0 ≤ tau w

  tau_eq_zero_at_T : ∀ u w, prW w = T u → tau w = 0

  supp_alt : ∀ u w, prW w = T u → w ∈ supp

  supp_sat : ∀ w ∈ supp, ∀ w', prW w' = prW w → w' ∈ supp

  propZ_low : ∀ u, zLow u ≤ (Mf u).mu

  propZ_up : ∀ u, (Mf u).muMax ≤ zUp u
  Dstar_pos : 0 < Dstar
  Xu_pos : ∀ u, 0 < Xu u

  Xu_pow : ∀ u, Xu u ^ (f * k) = Dstar / dstar u
  log_height_lower_bound : ∀ u, xLow ≤ Real.log (Xu u)
  log_height_upper_bound : ∀ u, Real.log (Xu u) ≤ xUp
  log_height_variation_bound : ∀ u u', |Real.log (Xu u) - Real.log (Xu u')| ≤ xVar

  Mtil_good : Mtil.Good

section Places

variable {K : Type} [Field K] [NumberField K]

theorem plEquiv_spec (w : HeightOneSpectrum (𝓞 K)) :
    Formalism.LFunctionChainParameters.LChain2.prBelow (plEquiv K w) = prW w ∧ Formalism.LFunctionChainParameters.LChain2.ramE (plEquiv K w) = (eW w : ℝ) ∧
      Formalism.LFunctionChainParameters.slopeLatticeData.ell (plEquiv K w) = lW w :=
  ⟨rfl, rfl, rfl⟩

theorem lenUW_eq_lenAt_div {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    ((lenUW w A B : ℚ) : ℝ) =
      ((Formalism.LFunctionChainParameters.slopeLatticeData.lenAt (plEquiv K w) A B).toNat : ℝ) / Formalism.LFunctionChainParameters.LChain2.ramE (plEquiv K w) := by
  unfold lenUW
  rw [lenW_eq_lenAt]
  push_cast
  rfl

end Places

structure ColObj.RecJoint (D : D7) (C : ColObj D.what₂.LL D.what₂.Word) where
  isoF : ∀ u, Formalism.L2.GlobalTheoryTheory.HLatOps.Iso ((D.fm u).lat 0) (C.Mf u)
  isoN : ∀ u, Formalism.L2.GlobalTheoryTheory.HLatOps.Iso (D.div.Nu u) (C.NprH u)
  comm : ∀ u (x : (D.div.Nu u).V), C.incl u ((isoN u).e x) = (isoF u).e (D.nuIn u x)
  mram : ∀ u, (DV.MramL D u).map ((isoN u).e.toLinearMap.restrictScalars (𝓞 D.what₂.LL)) = (C.M u).L
  T_eq : ∀ u, (D.mem u).A.T = C.T u

  f_eq : C.f = D.R.f
  k_eq : C.k = D.R.k
  m_eq : C.m = D.R.m

  Dstar_eq : C.Dstar = D.what₂.Dstar

  duStar_eq : ∀ u, ((D.mem u).A.duStar : ℝ) = C.dstar u

namespace ColIface

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} (C : ColIface K I)

theorem Nu_span (u : I) : Submodule.span K (C.Nu u : Set (C.M u).V) = ⊤ := by
  obtain ⟨c, hc, h⟩ := C.Nu_comm u
  rw [eq_top_iff, ← (C.M_good u).2.2, Submodule.span_le]
  intro x hx
  have h1 : c • x ∈ Submodule.span K (C.Nu u : Set (C.M u).V) := Submodule.subset_span (h x hx)
  have hc' : algebraMap (𝓞 K) K c ≠ 0 := by
    intro h0
    exact hc (FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero]))
  have h2 : x = (algebraMap (𝓞 K) K c)⁻¹ • (c • x) := by
    rw [← algebraMap_smul K c x, smul_smul, inv_mul_cancel₀ hc', one_smul]
  rw [h2]
  exact Submodule.smul_mem _ _ h1

theorem Nu_rank (u : I) : Formalism.HN.rkK (C.Nu u) = Formalism.HN.rkK (C.M u).L := by
  unfold Formalism.HN.rkK
  rw [C.Nu_span u, (C.M_good u).2.2]

theorem NuH_good (u : I) : (C.NuH u).Good := ⟨(C.M_good u).1, C.Nu_fg u, C.Nu_span u⟩

theorem Nu_le_atT (u : I) (w : HeightOneSpectrum (𝓞 K)) (h : prW w = C.T u) : atW w (C.Nu u) ≤ atW w (C.M u).L := by
  rw [C.Nu_atT u w h]
  exact C.Nlam_le u w h

theorem lenMN_atT_le (u : I) (w : HeightOneSpectrum (𝓞 K)) (h : prW w = C.T u) :
    ((C.lenMN u w : ℚ) : ℝ) ≤ (C.dM u : ℝ) * C.lamT u := by
  have h1 : C.lenMN u w = lenUW w (C.M u).L (C.Nlam u w) := by
    unfold ColObj.lenMN lenUW lenW
    rw [C.Nu_atT u w h]
  rw [h1]
  exact C.Nlam_len u w h

theorem lenMN_bar (u : I) (w : HeightOneSpectrum (𝓞 K)) (h : prW w = C.T u) (hb : ¬ C.overPi u w) : C.lenMN u w = 0 := by
  unfold ColObj.lenMN lenUW
  rw [lenW_eq_zero w (le_of_eq ((C.Nu_atT u w h).trans (C.Nlam_bar u w h hb)).symm)]
  simp

theorem lenMN_off (u : I) (w : HeightOneSpectrum (𝓞 K)) (h : w ∉ C.supp) : C.lenMN u w = 0 := by
  unfold ColObj.lenMN lenUW
  rw [lenW_eq_zero w (le_of_eq (C.Nu_off u w h).symm)]
  simp

theorem du_le_dM (u : I) : C.du u ≤ C.dM u := by
  have h1 := C.rank_ram u
  have hT : (4 : ℝ) ≤ (C.T u : ℝ) := by
    have h2 := C.T_big u
    have h3 := C.f_pos
    exact_mod_cast (show 4 ≤ C.T u by omega)
  have h4 : (0 : ℝ) ≤ 1 - 1 / ((C.T u : ℝ) - 1) := by
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  have h5 : 1 - 1 / ((C.T u : ℝ) - 1) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / ((C.T u : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
    linarith
  have h6 : (1 - 1 / ((C.T u : ℝ) - 1)) ^ C.f ≤ 1 := pow_le_one₀ h4 h5
  have h7 : (Fintype.card (C.M u).ι : ℝ) ≤ (Fintype.card (C.Mf u).ι : ℝ) := by
    rw [h1]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) h6
  exact_mod_cast h7

end ColIface

section Sig

open Formalism.L2.GlobalTheoryTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

theorem ColObj.sgExp_eq_famSig (C : ColObj K I) (u : I) (N : NumDatum) (Cs : Arith.Cst) (Lv : Arith.Lev N) (sd : K)
    (δ : Code N) (h1 : C.supp = Arith.supp N Lv K) (h2 : C.sg u = Arith.sg N Cs Lv sd δ) :
    C.sgExp u = Arith.famSig N Cs Lv sd δ := by
  have hS : C.S = Arith.famS N Lv K := by
    unfold ColObj.S Arith.famS
    rw [Finset.map_eq_image, h1]
    rfl
  unfold ColObj.sgExp Arith.famSig
  rw [hS]
  unfold ColObj.sgExpW Arith.sgExp
  rw [h2]
  rfl

theorem ColObj.tauExp_eq_famTau (C : ColObj K I) (N : NumDatum) (Cs : Arith.Cst) (Lv : Arith.Lev N)
    (h1 : C.supp = Arith.supp N Lv K) (h2 : C.tau = fun w => Arith.tau N Cs (Arith.pOf w)) :
    C.tauExp = Arith.famTau N Cs Lv := by
  have hS : C.S = Arith.famS N Lv K := by
    unfold ColObj.S Arith.famS
    rw [Finset.map_eq_image, h1]
    rfl
  unfold ColObj.tauExp Arith.famTau
  rw [hS]
  unfold ColObj.tauExpW Arith.tauExp
  rw [h2]
  rfl

end Sig

section Glue

variable {K : Type} [Field K] [NumberField K]

section
variable {V V' : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

theorem mem_localization_iff (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ L := by
  rw [← atW_restrictScalars]
  exact mem_atW_iff

theorem localizedAt_eq_iff_localized_eq (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    atW w A = atW w B ↔ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B := by
  rw [← atW_restrictScalars, ← atW_restrictScalars]
  exact (Submodule.restrictScalars_injective (𝓞 K) (Ow w) V).eq_iff.symm

theorem isLattice_map_equiv (e : V ≃ₗ[K] V') {L : Submodule (𝓞 K) V} (h : Submodule.IsLattice K L) :
    Submodule.IsLattice K (L.map (e.toLinearMap.restrictScalars (𝓞 K))) where
  fg := h.fg.map _
  span_eq_top := by
    have h1 : ((L.map (e.toLinearMap.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V') : Set V') = e.toLinearMap '' (L : Set V) := rfl
    rw [h1, ← Submodule.map_span, h.span_eq_top, Submodule.map_top, LinearEquiv.range]

theorem locP_map_equiv (e : V ≃ₗ[K] V') (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L.map (e.toLinearMap.restrictScalars (𝓞 K))) =
      (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L).map (e.toLinearMap.restrictScalars (𝓞 K)) := by
  ext y
  rw [mem_localization_iff]
  constructor
  · rintro ⟨s, hs, x, hx, e1⟩
    refine ⟨e.symm y, (mem_localization_iff w L _).2 ⟨s, hs, ?_⟩, e.apply_symm_apply y⟩
    have e2 : e x = s • y := e1
    have e3 : s • e.symm y = x := by
      rw [← algebraMap_smul K s (e.symm y), ← map_smul, algebraMap_smul, ← e2, e.symm_apply_apply]
    rw [e3]
    exact hx
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, hs, h1⟩ := (mem_localization_iff w L x).1 hx
    refine ⟨s, hs, s • x, h1, ?_⟩
    show e (s • x) = s • e x
    rw [← algebraMap_smul K s x, map_smul, algebraMap_smul]

end

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]

theorem glueW (L0 : Submodule (𝓞 K) V) (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) V)
    (h0 : Submodule.IsLattice K L0) (hL : ∀ w, Submodule.IsLattice K (L w))
    (hfin : {w : HeightOneSpectrum (𝓞 K) | Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w) ≠ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L0}.Finite) :
    Submodule.IsLattice K (⨅ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w)) ∧
      ∀ w : HeightOneSpectrum (𝓞 K),
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (⨅ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w)) =
          Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w) := by
  let e : V ≃ₗ[K] (Fin (finrank K V) → K) := (Module.finBasis K V).equivFun
  have hinj : Function.Injective (e.toLinearMap.restrictScalars (𝓞 K)) := e.injective
  have : Nonempty (HeightOneSpectrum (𝓞 K)) := nonempty_places K
  have hG : Formalism.DivisionValues.glueLat (fun w => (L w).map (e.toLinearMap.restrictScalars (𝓞 K))) =
      (⨅ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w)).map (e.toLinearMap.restrictScalars (𝓞 K)) := by
    unfold Formalism.DivisionValues.glueLat
    rw [Submodule.map_iInf _ hinj]
    exact iInf_congr fun w => locP_map_equiv e w (L w)
  have hf' : {w : HeightOneSpectrum (𝓞 K) |
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal ((L w).map (e.toLinearMap.restrictScalars (𝓞 K))) ≠
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L0.map (e.toLinearMap.restrictScalars (𝓞 K)))}.Finite := by
    refine hfin.subset fun w hw h1 => hw ?_
    rw [locP_map_equiv, locP_map_equiv, h1]
  obtain ⟨h1, h2⟩ := Formalism.DivisionValues.lattice_gluing K (finrank K V) (L0.map (e.toLinearMap.restrictScalars (𝓞 K)))
    (fun w => (L w).map (e.toLinearMap.restrictScalars (𝓞 K))) (isLattice_map_equiv e h0)
    (fun w => isLattice_map_equiv e (hL w)) hf'
  rw [hG] at h1 h2
  constructor
  · have h3 := isLattice_map_equiv e.symm h1
    have h4 : ((⨅ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w)).map
        (e.toLinearMap.restrictScalars (𝓞 K))).map (e.symm.toLinearMap.restrictScalars (𝓞 K)) =
        ⨅ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w) := by
      rw [← Submodule.map_comp]
      convert Submodule.map_id _
      ext x
      exact e.symm_apply_apply x
    rw [h4] at h3
    exact h3
  · intro w
    have h3 := h2 w
    rw [locP_map_equiv, locP_map_equiv] at h3
    exact Submodule.map_injective_of_injective hinj h3

theorem finite_places_over {n : ℕ} (hn : n ≠ 0) : {w : HeightOneSpectrum (𝓞 K) | ((n : ℕ) : 𝓞 K) ∈ w.asIdeal}.Finite := by
  have hn' : ((n : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hn
  refine (divs ((n : ℕ) : 𝓞 K)).finite_toSet.subset fun w hw => ?_
  exact Finset.mem_coe.2 ((mem_divs hn' w).2 hw)

theorem exists_smul_le_of_lattice {M N : Submodule (𝓞 K) V} (hM : M.FG) (hN : Submodule.IsLattice K N) :
    ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ y ∈ M, c • y ∈ N := by
  have key : ∀ x : V, ∃ c : 𝓞 K, c ≠ 0 ∧ c • x ∈ N := by
    intro x
    have hx : x ∈ Submodule.span K (N : Set V) := by rw [hN.span_eq_top]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
    | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact N.zero_mem⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, hc, h1⟩ := hy
      obtain ⟨d, hd, h2⟩ := hz
      refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
      have e1 : (c * d) • y = d • (c • y) := by rw [mul_comm, mul_smul]
      have e2 : (c * d) • z = c • (d • z) := mul_smul c d z
      rw [smul_add, e1, e2]
      exact N.add_mem (N.smul_mem d h1) (N.smul_mem c h2)
    | smul a y _ hy =>
      obtain ⟨c, hc, h1⟩ := hy
      obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) a
      refine ⟨c * d, mul_ne_zero hc (nonZeroDivisors.ne_zero d.2), ?_⟩
      have h2 : ((d : 𝓞 K)) • (a • y) = n • y := by
        rw [← algebraMap_smul K (d : 𝓞 K) (a • y), smul_smul, mul_comm, hnd, algebraMap_smul]
      rw [mul_smul, h2, smul_comm]
      exact N.smul_mem n h1
  obtain ⟨s, hs⟩ := hM
  classical
  choose c hc hcs using key
  refine ⟨∏ x ∈ s, c x, Finset.prod_ne_zero_iff.2 fun x _ => hc x, ?_⟩
  intro y hy
  rw [← hs] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.mul_prod_erase s c hx, mul_comm, mul_smul]
    exact N.smul_mem _ (hcs x)
  | zero => rw [smul_zero]; exact N.zero_mem
  | add y z _ _ hy hz => rw [smul_add]; exact N.add_mem hy hz
  | smul a y _ hy => rw [smul_comm]; exact N.smul_mem a hy

end Glue

section ItMLoc

variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem atW_idealPow_smul (w : HeightOneSpectrum (𝓞 K)) {ϖ : 𝓞 K} (hϖ : IsUnifW w ϖ)
    (n : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K →₀ ℤ) (M : Submodule (𝓞 K) V) :
    atW w (Formalism.HermitianLatticesTheory.idealSmul ((Formalism.LFunctionChainParameters.slopeLatticeData.idealPow n : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
      Submodule (𝓞 K) K) M) = scalW w (algebraMap (𝓞 K) K ϖ ^ n (plEquiv K w)) M := by
  rw [scalW_eq_locScal]
  exact @Formalism.LFunctionChainParameters.slopeLatticeData.local_ideal_pow K V _ _ _ _ _ _ (plEquiv K w) (owModule w V) (owTowerO w V) ϖ hϖ.1 hϖ.2 n M

theorem atW_prW_pow_le (w : HeightOneSpectrum (𝓞 K)) {ϖ : 𝓞 K} (hϖ : IsUnifW w ϖ) (t : ℕ) (M : Submodule (𝓞 K) V) :
    atW w (M.map ((((prW w : ℕ) : 𝓞 K) ^ t) • (LinearMap.id : V →ₗ[𝓞 K] V))) ≤
      scalW w (algebraMap (𝓞 K) K ϖ ^ (((eW w * t : ℕ) : ℤ))) M := by
  unfold atW
  rw [Submodule.span_le]
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨u, hu⟩ := prW_eq_unit_mul_pow w hϖ.irreducible
  have h1 : ((prW w : ℕ) : K) = algebraMap (Ow w) K (u : Ow w) * algebraMap (𝓞 K) K ϖ ^ eW w := by
    have h2 := congrArg (algebraMap (Ow w) K) hu
    rw [map_natCast, map_mul, map_pow, ← IsScalarTower.algebraMap_apply (𝓞 K) (Ow w) K] at h2
    exact h2
  have h3 : ((((prW w : ℕ) : 𝓞 K) ^ t) • (LinearMap.id : V →ₗ[𝓞 K] V)) y =
      ((u : Ow w) ^ t) • ((algebraMap (𝓞 K) K ϖ ^ (((eW w * t : ℕ) : ℤ))) • y) := by
    rw [LinearMap.smul_apply, LinearMap.id_apply, ow_smul_def, smul_smul, ← algebraMap_smul K ((((prW w : ℕ) : 𝓞 K)) ^ t) y,
      map_pow, map_pow, map_natCast, h1, mul_pow, ← pow_mul, zpow_natCast]
  rw [h3]
  exact Submodule.smul_mem _ _ (mem_scalW_iff.2 ⟨y, Submodule.subset_span hy, rfl⟩)

theorem atW_le_prW_pow (w : HeightOneSpectrum (𝓞 K)) {ϖ : 𝓞 K} (hϖ : IsUnifW w ϖ) (t : ℕ) {A M : Submodule (𝓞 K) V}
    (h : ∀ x ∈ A, ∃ y ∈ M, (((prW w : ℕ) : 𝓞 K) ^ t) • y = x) :
    atW w A ≤ scalW w (algebraMap (𝓞 K) K ϖ ^ (((eW w * t : ℕ) : ℤ))) M := by
  refine le_trans ?_ (atW_prW_pow_le w hϖ t M)
  refine atW_mono w fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := h x hx
  exact ⟨y, hy, rfl⟩

end ItMLoc

section NuSpec

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}

theorem iface_MramL_isLattice (hX : X.Ok) (u : Pr.Word) : Submodule.IsLattice X.K (MramL W Ch u) :=
  ⟨(MramH_good W Ch hX u).2.1, (MramH_good W Ch hX u).2.2⟩

theorem finite_prW {K : Type} [Field K] [NumberField K] (p : ℕ) : {w : HeightOneSpectrum (𝓞 K) | prW w = p}.Finite := by
  by_cases hp : p = 0
  · refine Set.Finite.subset Set.finite_empty fun w hw => ?_
    exact absurd (hw.trans hp) (prW_prime w).ne_zero
  · refine (finite_places_over (K := K) hp).subset fun w hw => ?_
    show ((p : ℕ) : 𝓞 K) ∈ w.asIdeal
    rw [← (show prW w = p from hw)]
    exact natCast_prW_mem w

theorem localLattice_at_T_eq {u : Pr.Word} (Sv : Serv W Ch u) (w : HeightOneSpectrum (𝓞 X.K)) (h : prW w = Pr.T u) :
    NuAt Sv w = NlamG W Ch u w := by
  unfold NuAt
  rw [if_pos (by rw [← h]; exact natCast_prW_mem w)]

theorem NuAt_of_served (hPr : Pr.Ok) {u : Pr.Word} (Sv : Serv W Ch u) (w : HeightOneSpectrum (𝓞 X.K)) (h : prW w ≠ Pr.T u)
    (hs : prW w ∈ Sv.served) : NuAt Sv w = Sv.NP w := by
  unfold NuAt
  rw [if_neg fun h1 => h (eq_prW_of_mem w (hPr.T_prime u) h1).symm, if_pos hs]

theorem NuAt_off (hPr : Pr.Ok) {u : Pr.Word} (Sv : Serv W Ch u) (w : HeightOneSpectrum (𝓞 X.K)) (h : prW w ≠ Pr.T u)
    (hs : prW w ∉ Sv.served) : NuAt Sv w = MramL W Ch u := by
  unfold NuAt
  rw [if_neg fun h1 => h (eq_prW_of_mem w (hPr.T_prime u) h1).symm, if_neg hs]

theorem NlamG_isLattice (hX : X.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K))
    (hinj : Function.Injective (TUmR W Ch u w)) : Submodule.IsLattice X.K (NlamG W Ch u w) := by
  have : Module.Finite X.K (MramV W Ch u) := Module.Finite.of_basis (MramH W Ch hX u).b
  have h1 := isLattice_map_equiv (LinearEquiv.ofInjectiveEndo (TUmR W Ch u w) hinj) (iface_MramL_isLattice (W := W) (Ch := Ch) hX u)
  rw [NlamG_eq_map]
  have h2 : (LinearEquiv.ofInjectiveEndo (TUmR W Ch u w) hinj).toLinearMap = TUmR W Ch u w :=
    LinearMap.ext fun x => congrFun (LinearEquiv.coe_ofInjectiveEndo (TUmR W Ch u w) hinj) x
  rw [h2] at h1
  exact h1

theorem NuC_spec (hX : X.Ok) (hPr : Pr.Ok) {u : Pr.Word} (Sv : Serv W Ch u)
    (hN : ∀ w, prW w = Pr.T u → Submodule.IsLattice X.K (NlamG W Ch u w))
    (hP : ∀ w, prW w ∈ Sv.served → Submodule.IsLattice X.K (Sv.NP w)) :
    Submodule.IsLattice X.K (NuC Sv) ∧
      ∀ w : HeightOneSpectrum (𝓞 X.K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (NuC Sv) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (NuAt Sv w) := by
  have : Module.Finite X.K (MramV W Ch u) := Module.Finite.of_basis (MramH W Ch hX u).b
  refine glueW (MramL W Ch u) (NuAt Sv) (iface_MramL_isLattice hX u) (fun w => ?_) ?_
  · by_cases h : prW w = Pr.T u
    · rw [localLattice_at_T_eq Sv w h]
      exact hN w h
    · by_cases hs : prW w ∈ Sv.served
      · rw [NuAt_of_served hPr Sv w h hs]
        exact hP w hs
      · rw [NuAt_off hPr Sv w h hs]
        exact iface_MramL_isLattice hX u
  · refine ((finite_prW (K := X.K) (Pr.T u)).union
      (Sv.served.finite_toSet.biUnion fun p _ => finite_prW (K := X.K) p)).subset fun w hw => ?_
    by_contra hc
    rw [Set.mem_union, not_or] at hc
    apply hw
    rw [NuAt_off hPr Sv w hc.1 fun hs => hc.2 (Set.mem_biUnion (Finset.mem_coe.2 hs) rfl)]

theorem NuC_isLattice (hX : X.Ok) (hPr : Pr.Ok) {u : Pr.Word} (Sv : Serv W Ch u)
    (hN : ∀ w, prW w = Pr.T u → Submodule.IsLattice X.K (NlamG W Ch u w))
    (hP : ∀ w, prW w ∈ Sv.served → Submodule.IsLattice X.K (Sv.NP w)) : Submodule.IsLattice X.K (NuC Sv) :=
  (NuC_spec hX hPr Sv hN hP).1

theorem NuC_locP (hX : X.Ok) (hPr : Pr.Ok) {u : Pr.Word} (Sv : Serv W Ch u)
    (hN : ∀ w, prW w = Pr.T u → Submodule.IsLattice X.K (NlamG W Ch u w))
    (hP : ∀ w, prW w ∈ Sv.served → Submodule.IsLattice X.K (Sv.NP w)) (w : HeightOneSpectrum (𝓞 X.K)) :
    atW w (NuC Sv) = atW w (NuAt Sv w) :=
  (localizedAt_eq_iff_localized_eq w _ _).2 ((NuC_spec hX hPr Sv hN hP).2 w)

theorem localization_at_T_eq (hX : X.Ok) (hPr : Pr.Ok) {u : Pr.Word} (Sv : Serv W Ch u)
    (hN : ∀ w, prW w = Pr.T u → Submodule.IsLattice X.K (NlamG W Ch u w))
    (hP : ∀ w, prW w ∈ Sv.served → Submodule.IsLattice X.K (Sv.NP w)) (w : HeightOneSpectrum (𝓞 X.K)) (h : prW w = Pr.T u) :
    atW w (NuC Sv) = atW w (NlamG W Ch u w) := by
  rw [NuC_locP hX hPr Sv hN hP w, localLattice_at_T_eq Sv w h]

theorem atW_NuC_served (hX : X.Ok) (hPr : Pr.Ok) {u : Pr.Word} (Sv : Serv W Ch u)
    (hN : ∀ w, prW w = Pr.T u → Submodule.IsLattice X.K (NlamG W Ch u w))
    (hP : ∀ w, prW w ∈ Sv.served → Submodule.IsLattice X.K (Sv.NP w)) (w : HeightOneSpectrum (𝓞 X.K)) (h : prW w ≠ Pr.T u)
    (hs : prW w ∈ Sv.served) : atW w (NuC Sv) = atW w (Sv.NP w) := by
  rw [NuC_locP hX hPr Sv hN hP w, NuAt_of_served hPr Sv w h hs]

theorem atW_NuC_off (hX : X.Ok) (hPr : Pr.Ok) {u : Pr.Word} (Sv : Serv W Ch u)
    (hN : ∀ w, prW w = Pr.T u → Submodule.IsLattice X.K (NlamG W Ch u w))
    (hP : ∀ w, prW w ∈ Sv.served → Submodule.IsLattice X.K (Sv.NP w)) (w : HeightOneSpectrum (𝓞 X.K)) (h : prW w ≠ Pr.T u)
    (hs : prW w ∉ Sv.served) : atW w (NuC Sv) = atW w (MramL W Ch u) := by
  rw [NuC_locP hX hPr Sv hN hP w, NuAt_off hPr Sv w h hs]

end NuSpec

section SgFin

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

theorem ColObj.sgFin_eq_sgExp (C : ColObj K I) (u : I) (h : ∀ w, w ∉ C.supp → C.sgExpW u w = 0) :
    sgFin (C.sg u) = C.sgExp u := by
  have hz : ∀ z : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K, sgFloor (C.sg u) (ofFinPl z) = C.sgExp u z := by
    intro z
    by_cases hm : z ∈ C.S
    · unfold ColObj.sgExp
      rw [Finsupp.indicator_of_mem hm]
      rfl
    · unfold ColObj.sgExp
      rw [Finsupp.indicator_of_notMem hm]
      exact h _ fun h' => hm ((C.mem_S z).2 h')
  have hfin : (Function.support fun w : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K => sgFloor (C.sg u) (ofFinPl w)).Finite := by
    refine (C.sgExp u).support.finite_toSet.subset fun z hzs => ?_
    rw [Finset.mem_coe, Finsupp.mem_support_iff, ← hz z]
    exact hzs
  unfold sgFin
  rw [dif_pos hfin]
  ext z
  exact hz z

end SgFin

structure ScNum where

  sc : Formalism.BasicNotions.Scale

  Sc : ℝ

  C0 : ℝ

  eta : ℝ

def ScNum.CY (_ : ScNum) : ℝ := 9

@[simp] theorem ScNum.CY_eq (n : ScNum) : n.CY = 9 := rfl

theorem ScNum.CY_nonneg (n : ScNum) : 0 ≤ n.CY := by rw [ScNum.CY_eq]; norm_num

def ScNum.GSizeCY {X : Fields} (Pr : Primes X) (n : ScNum) : Prop := ∀ i, Real.log (Pr.g i) ≤ n.CY * n.sc.L

theorem ScNum.idx_step {X : Fields} {Pr : Primes X} (R : Ranks) (n : ScNum) (h : n.GSizeCY Pr) :
    (X.f : ℝ) * ((R.m : ℝ) * (2 * R.k + R.m - 1) / 2) * Real.log ((Pr.g 0 : ℝ) * Pr.g 1) ≤
      3 * n.CY * X.f * R.m * R.k * n.sc.L := by
  have hg : ∀ i, 0 ≤ Real.log (Pr.g i : ℝ) := fun i => Real.log_natCast_nonneg _
  have hlog : Real.log ((Pr.g 0 : ℝ) * Pr.g 1) ≤ Real.log (Pr.g 0 : ℝ) + Real.log (Pr.g 1 : ℝ) := by
    by_cases h0 : (Pr.g 0 : ℝ) = 0
    · rw [h0, zero_mul, Real.log_zero]; linarith [hg 0, hg 1]
    by_cases h1 : (Pr.g 1 : ℝ) = 0
    · rw [h1, mul_zero, Real.log_zero]; linarith [hg 0, hg 1]
    rw [Real.log_mul h0 h1]
  have hL : Real.log ((Pr.g 0 : ℝ) * Pr.g 1) ≤ 2 * (n.CY * n.sc.L) := by linarith [h 0, h 1]
  have hL0 : 0 ≤ Real.log ((Pr.g 0 : ℝ) * Pr.g 1) := by
    have := Real.log_natCast_nonneg (Pr.g 0 * Pr.g 1)
    push_cast at this
    exact this
  have hk : (R.m : ℝ) + 3 ≤ R.k := by exact_mod_cast R.m_add_three_le_k
  have hm : (2 : ℝ) ≤ R.m := by exact_mod_cast R.two_le_m
  have hc : (R.m : ℝ) * (2 * R.k + R.m - 1) / 2 ≤ 3 * R.m * R.k / 2 := by nlinarith
  have hc0 : 0 ≤ (R.m : ℝ) * (2 * R.k + R.m - 1) / 2 := by nlinarith
  have hf : (0 : ℝ) ≤ X.f := Nat.cast_nonneg _
  calc (X.f : ℝ) * ((R.m : ℝ) * (2 * R.k + R.m - 1) / 2) * Real.log ((Pr.g 0 : ℝ) * Pr.g 1)
      ≤ (X.f : ℝ) * (3 * R.m * R.k / 2) * (2 * (n.CY * n.sc.L)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hc hf) hL hL0 (by positivity)
    _ = 3 * n.CY * X.f * R.m * R.k * n.sc.L := by ring

def logAvC (X : Fields) (n : ScNum) : ℝ := Real.log (n.sc.a * vC X)

theorem vC_pos (X : Fields) : 0 < vC X := by
  unfold vC
  have h : (0 : ℝ) < |(NumberField.discr X.E : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero X.E)
  positivity

theorem logAvC_eq (X : Fields) (n : ScNum) : logAvC X n = Real.log n.sc.x + n.sc.L + Real.log (vC X) := by
  have hx := n.sc.one_lt_alt
  unfold logAvC Scale.a Scale.b
  rw [Real.log_mul (mul_pos (by linarith) (Real.exp_pos _)).ne' (vC_pos X).ne', Real.log_mul (by linarith) (Real.exp_pos _).ne',
    Real.log_exp]

theorem L_lt_logAvC (X : Fields) (n : ScNum) (hv : 1 ≤ vC X) : n.sc.L < logAvC X n := by
  rw [logAvC_eq]
  have := Real.log_pos n.sc.one_lt_alt
  have := Real.log_nonneg hv
  linarith

theorem L_le_logAvC (X : Fields) (n : ScNum) (hv : 1 ≤ vC X) : n.sc.L ≤ logAvC X n := (L_lt_logAvC X n hv).le

theorem one_lt_scL (s : Scale) : 1 < s.L := Real.one_lt_rpow s.one_lt_alt s.eps_pos

theorem one_lt_logAvC (X : Fields) (n : ScNum) (hv : 1 ≤ vC X) : 1 < logAvC X n := (one_lt_scL n.sc).trans (L_lt_logAvC X n hv)

theorem logAvC_le_two (X : Fields) (n : ScNum) (h : Real.log n.sc.x + Real.log (vC X) ≤ n.sc.L) : logAvC X n ≤ 2 * n.sc.L := by
  rw [logAvC_eq]
  linarith

theorem log_av_logAvC (X : Fields) (n : ScNum) : Real.log (n.sc.a * vC X) ≤ logAvC X n := le_rfl

theorem ifz_bprime_ge (s : Scale) (c : ℝ) (h8 : 8 ≤ s.L) (hc : 8 * c ≤ s.L) : c * s.L ≤ s.b' := by
  have hx0 : 0 < s.x := by linarith [s.one_lt_alt]
  set y := s.x ^ (s.eps / 3) with hy
  have hy1 : 1 < y := Real.one_lt_rpow s.one_lt_alt (by linarith [s.eps_pos])
  have hLy : s.L = y ^ 3 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    unfold Scale.L
    congr 1
    push_cast
    ring
  have hb' : s.b' = s.x * Real.exp (s.L - y) := by
    unfold Scale.b' Scale.a Scale.b Scale.X'
    rw [Real.exp_sub, ← hy]
    ring
  have hy2 : 2 ≤ y := by
    by_contra h
    push Not at h
    have : y ^ 3 < 8 := by nlinarith [sq_nonneg y]
    linarith
  have hyL : y ≤ s.L / 2 := by rw [hLy]; nlinarith [sq_nonneg y]
  have he : s.L ^ 2 / 8 ≤ Real.exp (s.L - y) := by
    have h1 := Real.quadratic_le_exp_of_nonneg (x := s.L / 2) (by linarith)
    have h2 : Real.exp (s.L / 2) ≤ Real.exp (s.L - y) := Real.exp_le_exp.2 (by linarith)
    nlinarith
  have hxe : Real.exp (s.L - y) ≤ s.b' := by
    rw [hb']
    have := Real.exp_pos (s.L - y)
    nlinarith [s.one_lt_alt]
  nlinarith

theorem ifz_log_x_le (s : Scale) : s.eps * Real.log s.x ≤ s.L := by
  have hx0 : 0 < s.x := by linarith [s.one_lt_alt]
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 s.eps)
  rw [Real.log_rpow hx0] at h
  unfold Scale.L
  linarith

theorem ifz_b'_le_a (s : Scale) : s.b' ≤ s.a := by
  have ha : 0 < s.a := by unfold Scale.a Scale.b; have := s.one_lt_alt; positivity
  unfold Scale.b'
  have : 1 ≤ s.X' := by unfold Scale.X'; exact Real.one_le_exp (by have := s.one_lt_alt; positivity)
  exact div_le_self ha.le this

theorem ifz_logAvC_le (X : Fields) (n : ScNum) (hv : 1 ≤ vC X) :
    logAvC X n ≤ (1 / n.sc.eps + 1 + Real.log (vC X)) * n.sc.L := by
  rw [logAvC_eq]
  have he := n.sc.eps_pos
  have h1 : Real.log n.sc.x ≤ n.sc.L / n.sc.eps := by rw [le_div_iff₀ he]; linarith [ifz_log_x_le n.sc]
  have h2 := (one_lt_scL n.sc).le
  have h3 := Real.log_nonneg hv
  have h4 : n.sc.L / n.sc.eps = 1 / n.sc.eps * n.sc.L := by ring
  nlinarith

theorem numbersC_logAvC_large (X : Fields) (hv : 1 ≤ vC X) (R : Ranks) (C₀ : ℝ) (hC : 0 ≤ C₀) (eps : ℝ) :
    ∃ Λ : ℝ, ∀ n : ScNum, n.sc.eps = eps → Λ ≤ n.sc.L → n.C0 = C₀ → ∀ (Pr : Primes X) (u : Pr.Word),
      logTC Pr u ≤ C₀ * R.m * logAvC X n → loggC Pr ≤ C₀ * logAvC X n → 0 ≤ n.eta → 0 ≤ n.Sc → n.Sc + n.eta ≤ n.sc.b' / 2 →
      NumbersC Pr R u n.C0 n.sc.a n.sc.b' (logAvC X n) n.eta n.Sc := by
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 1 / eps + 1 + Real.log (vC X) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (R.N R.m : ℝ) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = N * (1 + C₀ * R.m) := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A : ℝ, A = 2 * (R.m : ℝ) * R.t := ⟨_, rfl⟩
  obtain ⟨A3, hA3⟩ : ∃ A : ℝ, A = (1 + 2 * C₀) * (R.m : ℝ) ^ 3 * N := ⟨_, rfl⟩
  refine ⟨max 8 (8 * (|K * D| + A2 + A3 + 1)), fun n he hΛ hC0 Pr u hT hg heta hS hSe => ?_⟩
  rw [hC0]
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ R.N R.m := by unfold Ranks.N; have := R.m_add_three_le_k; omega
    rw [hN]; exact_mod_cast this
  have hm0 : (0 : ℝ) ≤ R.m := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ R.t := Nat.cast_nonneg _
  have hA20 : 0 ≤ A2 := by rw [hA2]; positivity
  have hN0 : 0 ≤ N := by linarith
  have hA30 : 0 ≤ A3 := by rw [hA3]; positivity
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hab := abs_nonneg (K * D)
  have h8 : 8 ≤ n.sc.L := le_trans (le_max_left _ _) hΛ
  have h8c : 8 * (|K * D| + A2 + A3 + 1) ≤ n.sc.L := le_trans (le_max_right _ _) hΛ
  have hb := ifz_bprime_ge n.sc _ h8 h8c
  have hL1 : 1 ≤ n.sc.L := by linarith
  have hcL : |K * D| + A2 + A3 + 1 ≤ (|K * D| + A2 + A3 + 1) * n.sc.L := le_mul_of_one_le_right (by linarith) hL1
  have hLL := ifz_logAvC_le X n hv
  rw [he, ← hD] at hLL
  have hLL1 := one_lt_logAvC X n hv
  have hKLL : K * logAvC X n ≤ n.sc.b' := by
    have h1 : K * logAvC X n ≤ K * (D * n.sc.L) := mul_le_mul_of_nonneg_left hLL hK0
    have h2 : K * (D * n.sc.L) ≤ |K * D| * n.sc.L := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    have h3 : |K * D| * n.sc.L ≤ (|K * D| + A2 + A3 + 1) * n.sc.L := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  have hmt : A2 ≤ n.sc.b' := by linarith
  have hpow : A3 ≤ n.sc.b' := by linarith
  have hb1 : 1 ≤ n.sc.b' := by linarith
  have hTn : 0 ≤ logTC Pr u := Real.log_natCast_nonneg _
  have hLL0 : 0 ≤ logAvC X n := by linarith
  have hCm : 0 ≤ C₀ * R.m * logAvC X n := by positivity
  refine numbersC_of Pr R u hLL1.le hv (log_av_logAvC X n) hb1 (ifz_b'_le_a n.sc) hT hg heta hS ?_ ?_ ?_ ?_
  · have : (R.m : ℝ) * R.t ≤ n.sc.b' / 2 := by rw [hA2] at hmt; linarith
    linarith
  · have h1 : N * (logAvC X n + logTC Pr u) ≤ K * logAvC X n := by
      have : N * (logAvC X n + logTC Pr u) ≤ N * (logAvC X n + C₀ * R.m * logAvC X n) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      rw [hK]; linarith [show N * (logAvC X n + C₀ * R.m * logAvC X n) = N * (1 + C₀ * R.m) * logAvC X n by ring]
    rw [← hN]
    have e : N ^ 2 * (logAvC X n + logTC Pr u) = N * (N * (logAvC X n + logTC Pr u)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (h1.trans hKLL) (by linarith)
  · have h0 : C₀ * R.m * logAvC X n ≤ N * (C₀ * R.m * logAvC X n) := le_mul_of_one_le_left hCm hN1
    have h1 : N * logAvC X n + logTC Pr u ≤ K * logAvC X n := by
      rw [hK]; linarith [show N * (1 + C₀ * R.m) * logAvC X n = N * logAvC X n + N * (C₀ * R.m * logAvC X n) by ring]
    rw [← hN]
    linarith
  · rw [hA3, hN] at hpow; exact hpow

section Conc

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def WtauC (u : Pr.Word) (τ : X.Tau) : ℕ :=
  (Finset.range (R.m + 1)).sup fun j => Finset.univ.sup fun i : Fin (R.N j) =>
    if i.1 = 0 ∧ τ ∈ W.tops then 0 else ((W.lamTrue u j τ).w i).natAbs

def lambdaConstant (u : Pr.Word) : ℝ :=
  (R.m : ℝ) * ∑ τ ∈ W.tops, ((W.aTop u τ : ℝ) / (R.k : ℝ) + 2 * (WtauC W u τ : ℝ) + (R.k : ℝ) - 1)

def cZC (C₀ : ℝ) : ℝ := if h : 0 ≤ C₀ then Classical.choose (propZ_col' C₀ h) else 0

theorem cZC_spec {C₀ : ℝ} (h : 0 ≤ C₀) : 0 ≤ cZC C₀ ∧ ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
    (Ch : Chars X Pr R.m) (hX : X.Ok) (_ : Pr.Ok) (_ : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) (a b' L eta S : ℝ),
    NumbersC Pr R u C₀ a b' L eta S → WtWin W u C₀ a b' S → SummandSlopeAtDecoratedLattice W Ch u → MaxSlopeSummandWithConstant W Ch u C₀ →
    (∀ τ, DualSlope X.K (W.lamTrue u 0 τ)) → (∀ τ, MaxSlopeNablaBound X.K (kap_succ R) (W.lamTrue u 0 τ)) →
    ZiiC W u (cZC C₀) a b' L S ≤ (Mu0H W Ch hX u).mu ∧ (Mu0H W Ch hX u).muMax ≤ ZiiiC W u (cZC C₀) a b' L S := by
  unfold cZC
  rw [dif_pos h]
  exact Classical.choose_spec (propZ_col' C₀ h)

def xLowC (n : ScNum) : ℝ :=
  (∑ j : Fin R.m, (1 / (X.f : ℝ)) * ∑ τ, Real.log ((((W.row τ).e j : ℚ) : ℝ) * vC X / Real.pi))
    + (R.m : ℝ) * ∑ i, Real.log (Pr.g i) - 11 * n.sc.L

def xUpC (R : Ranks) (n : ScNum) : ℝ := (15 + 3 * n.CY) * (R.m : ℝ) * n.sc.L

def xVarC (R : Ranks) : ℝ := 1 + Real.log (R.k : ℝ) + 2 / (R.k : ℝ)

def lamRowC (S : RowPar R) : Fin R.r → ℝ := fun i =>
  if h : i.val < R.k - 1 then (S.v ⟨i.val, h⟩ : ℝ)
  else if h' : i.val - (R.k - 1) < R.m then -(S.b ⟨i.val - (R.k - 1), h'⟩ : ℝ) else 0

theorem lamRowC_of (P : HCParam R) : lamRowC (RowPar.of P) = Formalism.MainNotions.S.lamS R P := rfl

theorem iface_strictAnti_of_succ {n : ℕ} (f : Fin n → ℝ)
    (h : ∀ (i : ℕ) (hi : i + 1 < n), f ⟨i + 1, hi⟩ < f ⟨i, by omega⟩) : StrictAnti f := by
  intro a b hab
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  change a < b at hab
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h1 | h1
    · exact lt_trans (h b hb) (ih (by omega) h1)
    · subst h1; exact h a hb

theorem lamRowC_strictAnti (P : HCParam R) : StrictAnti (lamRowC (RowPar.of P)) := by
  apply iface_strictAnti_of_succ
  intro i hi
  have hr : R.r = R.k + R.m - 1 := rfl
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  simp only [lamRowC, RowPar.of]
  by_cases h1 : i + 1 < R.k - 1
  · rw [dif_pos h1, dif_pos (show i < R.k - 1 by omega)]
    have a1 := P.u_gt_v ⟨i + 1, h1⟩
    have a2 := P.v_gt_u ⟨i, by omega⟩
    exact_mod_cast lt_trans a1 a2
  · by_cases h2 : i < R.k - 1
    · rw [dif_neg h1, dif_pos (show i + 1 - (R.k - 1) < R.m by omega), dif_pos h2]
      have a1 := P.u_last_gt (by omega) (by omega)
      have a2 := P.v_gt_u ⟨i, h2⟩
      have e1 : P.u ⟨i + 1, by omega⟩ = P.u ⟨R.k - 1, by omega⟩ := congrArg P.u (Fin.ext (by simp; omega))
      have e2 : P.b ⟨i + 1 - (R.k - 1), by omega⟩ = P.b ⟨0, by omega⟩ := congrArg P.b (Fin.ext (by simp; omega))
      rw [e2]
      rw [e1] at a2
      have a3 : -P.b ⟨0, by omega⟩ < P.v ⟨i, h2⟩ := lt_trans a1 a2
      exact_mod_cast a3
    · rw [dif_neg h1, dif_neg h2, dif_pos (show i + 1 - (R.k - 1) < R.m by omega),
        dif_pos (show i - (R.k - 1) < R.m by omega)]
      have j1 := P.gap_be ⟨i - (R.k - 1), by omega⟩
      have j2 := P.gap_eb ⟨i - (R.k - 1), by omega⟩ (by simp; omega)
      have e3 : P.b ⟨i + 1 - (R.k - 1), by omega⟩ = P.b ⟨i - (R.k - 1) + 1, by omega⟩ :=
        congrArg P.b (Fin.ext (by simp; omega))
      rw [e3]
      have h3 : (0 : ℚ) < ((R.t : ℚ) + 3) / 2 := by positivity
      have a4 : P.b ⟨i - (R.k - 1), by omega⟩ < P.b ⟨i - (R.k - 1) + 1, by omega⟩ := by linarith
      have a5 : (P.b ⟨i - (R.k - 1), by omega⟩ : ℝ) < (P.b ⟨i - (R.k - 1) + 1, by omega⟩ : ℝ) := by exact_mod_cast a4
      linarith

theorem iface_fdegHC_pos {n : ℕ} {lam : Fin n → ℝ} (h : StrictAnti lam) : 0 < Formalism.QuantumDeterminants.fdegHC lam := by
  unfold Formalism.QuantumDeterminants.fdegHC
  apply div_pos
  · exact Finset.prod_pos fun a _ => Finset.prod_pos fun b hb =>
      abs_pos.2 (sub_ne_zero.2 (h (Finset.mem_filter.1 hb).2).ne')
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    have h1 : a.1 < b.1 := (Finset.mem_filter.1 hb).2
    have h2 : (a.1 : ℝ) < b.1 := by exact_mod_cast h1
    linarith

theorem iface_fdegHC_cast {n n' : ℕ} (h : n = n') (f : Fin n' → ℝ) :
    Formalism.QuantumDeterminants.fdegHC (fun i : Fin n => f (Fin.cast h i)) = Formalism.QuantumDeterminants.fdegHC f := by
  subst h; rfl

def dsigC (τ : X.Tau) : ℝ := Formalism.QuantumDeterminants.fdegHC (lamRowC (W.row τ))

theorem dsigC_pos (hW : W.Ok) (τ : X.Tau) : 0 < dsigC W τ := by
  obtain ⟨P, hP⟩ := hW.row_ok τ
  unfold dsigC
  rw [← hP]
  exact iface_fdegHC_pos (lamRowC_strictAnti P)

theorem dsigC_eq_lamSH {P : HCParam R} {τ : X.Tau} (hP : RowPar.of P = W.row τ) :
    dsigC W τ = Formalism.QuantumDeterminants.fdegHC (Formalism.MainNotions.S.lamSH R P) := by
  unfold dsigC
  rw [← hP, lamRowC_of]
  exact (iface_fdegHC_cast (Formalism.MainNotions.S.dimS_eq R) (Formalism.MainNotions.S.lamS R P)).symm

theorem iface_fdegHC_eq_dimVN {n : ℕ} (lam : Fin n → ℝ) (h : StrictAnti lam) :
    Formalism.QuantumDeterminants.fdegHC lam = Formalism.LogVandermondeBounds.StandardLattice.dimVN (fun i => if hi : i < n then lam ⟨i, hi⟩ else 0) n := by
  rw [Formalism.QuantumDeterminants.fdegDimV n lam h]
  unfold Formalism.LogVandermondeBounds.StandardLattice.dimVN Formalism.LogVandermondeBounds.StandardLattice.vandN
  congr 1
  set x : ℕ → ℝ := fun i => if hi : i < n then lam ⟨i, hi⟩ else 0 with hxdef
  have hx : ∀ a : Fin n, x a.1 = lam a := fun a => by simp [hxdef, a.isLt]
  have e1 : ∀ a : Fin n, ∏ b ∈ Finset.univ.filter (fun b : Fin n => a < b), (lam a - lam b) =
      ∏ j ∈ Finset.Ico (a.1 + 1) n, (x a.1 - x j) := by
    intro a
    calc ∏ b ∈ Finset.univ.filter (fun b : Fin n => a < b), (lam a - lam b)
        = ∏ b : Fin n, (if a < b then lam a - lam b else 1) := Finset.prod_filter _ _
      _ = ∏ b : Fin n, (fun j : ℕ => if a.1 < j then x a.1 - x j else 1) b.1 := by
          refine Finset.prod_congr rfl fun b _ => ?_
          show _ = (if a.1 < b.1 then x a.1 - x b.1 else 1)
          rw [hx a, hx b]
          simp only [Fin.lt_def]
      _ = ∏ j ∈ Finset.range n, (if a.1 < j then x a.1 - x j else 1) :=
          Fin.prod_univ_eq_prod_range (fun j : ℕ => if a.1 < j then x a.1 - x j else 1) n
      _ = ∏ j ∈ (Finset.range n).filter (fun j => a.1 < j), (x a.1 - x j) := (Finset.prod_filter _ _).symm
      _ = ∏ j ∈ Finset.Ico (a.1 + 1) n, (x a.1 - x j) := by
          congr 1
          ext j
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
          omega
  calc ∏ a : Fin n, ∏ b ∈ Finset.univ.filter (fun b : Fin n => a < b), (lam a - lam b)
      = ∏ a : Fin n, (fun i : ℕ => ∏ j ∈ Finset.Ico (i + 1) n, (x i - x j)) a.1 :=
        Finset.prod_congr rfl fun a _ => e1 a
    _ = ∏ i ∈ Finset.range n, ∏ j ∈ Finset.Ico (i + 1) n, (x i - x j) :=
        Fin.prod_univ_eq_prod_range (fun i : ℕ => ∏ j ∈ Finset.Ico (i + 1) n, (x i - x j)) n

theorem dsigC_eq_dimVN (hW : W.Ok) (τ : X.Tau) :
    dsigC W τ = Formalism.LogVandermondeBounds.StandardLattice.dimVN (fun i => if h : i < R.r then lamRowC (W.row τ) ⟨i, h⟩ else 0) R.r := by
  obtain ⟨P, hP⟩ := hW.row_ok τ
  have hs : StrictAnti (lamRowC (W.row τ)) := by rw [← hP]; exact lamRowC_strictAnti P
  exact iface_fdegHC_eq_dimVN _ hs

theorem lamSH_isHCParam {R : Ranks} (P : HCParam R) : Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.S.lamSH R P) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have h := lamRowC_strictAnti P (a := Fin.cast (Formalism.MainNotions.S.dimS_eq R) a) (b := Fin.cast (Formalism.MainNotions.S.dimS_eq R) b)
      hab
    rw [lamRowC_of] at h
    exact h
  · obtain ⟨k', hk'⟩ := R.k_even
    have hn : (((2 * R.rS + R.k + 1 : ℕ) : ℝ) - 1) / 2 = (R.rS : ℝ) + (k' : ℝ) := by
      rw [hk']; push_cast; ring
    rw [hn]
    simp only [Formalism.MainNotions.S.lamSH, Formalism.MainNotions.S.lamS]
    split_ifs with h1 h2
    · obtain ⟨z, hz⟩ := P.v_int ⟨(Fin.cast (Formalism.MainNotions.S.dimS_eq R) a).val, h1⟩
      refine ⟨z - R.rS - k', ?_⟩
      rw [hz]; push_cast; ring
    · obtain ⟨z, hz⟩ := P.b_int ⟨(Fin.cast (Formalism.MainNotions.S.dimS_eq R) a).val - (R.k - 1), h2⟩
      refine ⟨-z - R.rS - k', ?_⟩
      rw [hz]; push_cast; ring
    · exact ⟨-(R.rS : ℤ) - k', by push_cast; ring⟩

theorem dsigC_isFdeg (hHC : HCFormalDegreeCD) {P : HCParam R} {τ : X.Tau} (hP : RowPar.of P = W.row τ) (C : Formalism.BasicNotions.CDHaar)
    {p q : ℕ} (e : Fin p ⊕ Fin q ≃ Fin (2 * R.rS + R.k + 1))
    (h1 : ∀ i, Formalism.MainNotions.S.epsSH R (e (Sum.inl i)) = true) (h2 : ∀ j, Formalism.MainNotions.S.epsSH R (e (Sum.inr j)) = false)
    (μ : MeasureTheory.Measure (Formalism.REAL.UJ (Formalism.MainNotions.S.epsSH R)))
    (hμ : ∀ A : Set (Formalism.REAL.UJ (Formalism.MainNotions.S.epsSH R)), MeasurableSet A →
      μ A = C.cd p q {g | ∃ a ∈ A, Formalism.MainNotions.S.umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)})
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (H →L[ℂ] H)) (w : H)
    (hσ : Formalism.MainNotions.S.IsDS (Formalism.MainNotions.S.epsSH R) (Formalism.MainNotions.S.lamSH R P) σ) (hw : w ≠ 0) :
    Formalism.MainNotions.S.fdegOf μ σ w = dsigC W τ := by
  rw [dsigC_eq_lamSH W hP]
  exact hHC C _ p q (Formalism.MainNotions.S.epsSH R) e h1 h2 μ hμ _ (lamSH_isHCParam P) H σ w hσ hw

structure ColArg where

  num : ScNum

  served : Finset ℕ

  tauP : ℕ → ℕ

  yM : ∀ u, HeightOneSpectrum (𝓞 X.K) → Submodule (𝓞 X.K) (MfV W Ch u)

  supp : Finset (HeightOneSpectrum (𝓞 X.K))

  sg : Pr.Word → HeightOneSpectrum (𝓞 X.K) → ℝ

  sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)

  Sq : Set ℕ

variable {W Ch} (hX : X.Ok) (A : ColArg W Ch)

def ColArg.dsig (_ : ColArg W Ch) : X.Tau → ℝ := dsigC W

theorem ColArg.dsig_eq : A.dsig = dsigC W := rfl

def ColArg.Sv (u : Pr.Word) : Serv W Ch u := ⟨A.served, A.yM u, fun w => A.tauP (prW w)⟩

open Classical in

def ColArg.tau (w : HeightOneSpectrum (𝓞 X.K)) : ℝ := if prW w ∈ A.served then (A.tauP (prW w) : ℝ) else 0

variable (W Ch) in

def ColArg.ofTau (num : ScNum) (supp : Finset (HeightOneSpectrum (𝓞 X.K))) (sg : Pr.Word → HeightOneSpectrum (𝓞 X.K) → ℝ)
    (tau : ℕ → ℝ) (yM : ∀ u, HeightOneSpectrum (𝓞 X.K) → Submodule (𝓞 X.K) (MfV W Ch u))
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sq : Set ℕ) : ColArg W Ch where
  num := num
  served := by classical exact (supp.image prW).filter fun p => tau p ≠ 0
  tauP p := ⌊tau p⌋₊
  yM := yM
  supp := supp
  sg := sg
  sel := sel
  Sq := Sq

theorem ColArg.ofTau_tau (num : ScNum) (supp : Finset (HeightOneSpectrum (𝓞 X.K))) (sg : Pr.Word → HeightOneSpectrum (𝓞 X.K) → ℝ)
    (tau : ℕ → ℝ) (yM : ∀ u, HeightOneSpectrum (𝓞 X.K) → Submodule (𝓞 X.K) (MfV W Ch u))
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sq : Set ℕ) (hnat : ∀ p, ∃ n : ℕ, tau p = n)
    {w : HeightOneSpectrum (𝓞 X.K)} (hw : w ∈ supp) :
    (ColArg.ofTau W Ch num supp sg tau yM sel Sq).tau w = tau (prW w) := by
  classical
  unfold ColArg.tau ColArg.ofTau
  obtain ⟨n, hn⟩ := hnat (prW w)
  by_cases h0 : tau (prW w) = 0
  · rw [h0]
    split_ifs
    · simp [h0]
    · rfl
  · have hm : prW w ∈ (supp.image prW).filter fun p => tau p ≠ 0 :=
      Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hw, h0⟩
    simp only [hm, if_true, hn, Nat.floor_natCast]

variable (W Ch) in

def colObj : ColObj X.K Pr.Word where
  f := X.f
  k := R.k
  m := R.m
  T := Pr.T
  Mf := Mu0H W Ch hX
  M := MramH W Ch hX
  incl := ramInclH W Ch hX
  Vr := VrC W Ch hX
  dstar := dstarC W Ch
  overPi := seenC Pr
  Nlam := NlamG W Ch
  lamT := lambdaConstant W
  Nu u := NuC (A.Sv u)
  supp := A.supp
  sg := A.sg
  tau := A.tau
  zLow u := ZiiC W u (cZC A.num.C0) A.num.sc.a A.num.sc.b' (logAvC X A.num) A.num.Sc
  zUp u := ZiiiC W u (cZC A.num.C0) A.num.sc.a A.num.sc.b' (logAvC X A.num) A.num.Sc
  Dstar := DstarC Pr R A.dsig
  Xu := XuC W Ch A.dsig
  xLow := xLowC W A.num
  xUp := xUpC R A.num
  xVar := xVarC R
  Mtil := MtildeH W Ch hX A.sel (mu0 X.F X.E X.K A.Sq) (rPsymF Ch)

theorem colObj_Npr_eq (u : Pr.Word) (gain F Eu : ℕ → HeightOneSpectrum (𝓞 X.K) → ℝ) (h1 : A.sg u = sgSumOf R.m gain F Eu)
    (h2 : ∀ w, w ∉ A.supp → (colObj W Ch hX A).sgExpW u w = 0) :
    (colObj W Ch hX A).Npr u = NuPrimeC (A.Sv u) gain F Eu := by
  unfold NuPrimeC ColObj.Npr
  rw [← h1, ← (colObj W Ch hX A).sgFin_eq_sgExp u h2]
  rfl

theorem Serv.NP_le {u : Pr.Word} (Sv : Serv W Ch u) (w : HeightOneSpectrum (𝓞 X.K)) :
    ∀ φ ∈ Sv.NP w, ∃ ψ ∈ MramL W Ch u, (((prW w : ℕ) : 𝓞 X.K) ^ Sv.tau w) • ψ = φ := by
  rintro φ ⟨-, ψ, hψ, e⟩
  have e' : (((prW w : ℕ) : 𝓞 X.K) ^ Sv.tau w) • ψ = (φ : MfV W Ch u) := e
  have hp' : algebraMap (𝓞 X.K) X.K (((prW w : ℕ) : 𝓞 X.K) ^ Sv.tau w) ≠ 0 := by
    rw [map_pow, map_natCast]
    exact pow_ne_zero _ (by exact_mod_cast (prW_prime w).ne_zero)
  have h2 : (algebraMap (𝓞 X.K) X.K (((prW w : ℕ) : 𝓞 X.K) ^ Sv.tau w)) • ψ = (φ : MfV W Ch u) := by
    rw [algebraMap_smul]
    exact e'
  have hmem : ψ ∈ MramV W Ch u := by
    have h3 : (algebraMap (𝓞 X.K) X.K (((prW w : ℕ) : 𝓞 X.K) ^ Sv.tau w)) • ψ ∈ MramV W Ch u := by
      rw [h2]
      exact φ.2
    exact (Submodule.smul_mem_iff _ hp').1 h3
  exact ⟨⟨ψ, hmem⟩, hψ, Subtype.ext e'⟩

theorem NuC_le_ItM (hPr : Pr.Ok) (u : Pr.Word)
    (hN : ∀ w, prW w = Pr.T u → Submodule.IsLattice X.K (NlamG W Ch u w))
    (hP : ∀ w, prW w ∈ A.served → Submodule.IsLattice X.K ((A.Sv u).NP w))
    (hle : ∀ w, prW w = Pr.T u → atW w (NlamG W Ch u w) ≤ atW w (MramL W Ch u))
    (hT : Pr.T u ∉ A.served) (hs : ∀ w, prW w ∈ A.served → w ∈ A.supp) :
    NuC (A.Sv u) ≤ (colObj W Ch hX A).ItM u := by
  refine le_of_atW_le fun w => ?_
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifW w
  have hI : atW w ((colObj W Ch hX A).ItM u) =
      scalW w (algebraMap (𝓞 X.K) X.K ϖ ^ (colObj W Ch hX A).tauExp (plEquiv X.K w)) (MramL W Ch u) :=
    atW_idealPow_smul w hϖ _ _
  refine le_trans ?_ hI.symm.le
  by_cases hsv : prW w ∈ A.served
  · have hne : prW w ≠ Pr.T u := fun h => hT (h ▸ hsv)
    have h1 : (colObj W Ch hX A).tauExp (plEquiv X.K w) = ((eW w * A.tauP (prW w) : ℕ) : ℤ) := by
      rw [(colObj W Ch hX A).tauExp_of_mem (hs w hsv)]
      show ⌊(eW w : ℝ) * A.tau w⌋ = _
      unfold ColArg.tau
      rw [if_pos hsv, ← Nat.cast_mul]
      exact Int.floor_natCast _
    rw [h1, atW_NuC_served hX hPr (A.Sv u) hN hP w hne hsv]
    exact atW_le_prW_pow w hϖ _ ((A.Sv u).NP_le w)
  · have h1 : (colObj W Ch hX A).tauExp (plEquiv X.K w) = 0 := by
      by_cases hm : w ∈ A.supp
      · rw [(colObj W Ch hX A).tauExp_of_mem hm]
        show ⌊(eW w : ℝ) * A.tau w⌋ = 0
        unfold ColArg.tau
        rw [if_neg hsv, mul_zero, Int.floor_zero]
      · exact (colObj W Ch hX A).tauExp_of_not_mem hm
    rw [h1, zpow_zero, scalW_one]
    by_cases hTw : prW w = Pr.T u
    · rw [localization_at_T_eq hX hPr (A.Sv u) hN hP w hTw]
      exact hle w hTw
    · rw [atW_NuC_off hX hPr (A.Sv u) hN hP w hTw hsv]

variable (W Ch) in

structure ColArgOk : Prop where

  np_lat : ∀ u w, prW w ∈ A.served → Submodule.IsLattice X.K ((A.Sv u).NP w)

  supp_served : ∀ w, prW w ∈ A.served → w ∈ A.supp

  served_alt : ∀ u, Pr.T u ∉ A.served

  supp_alt : ∀ u w, prW w = Pr.T u → w ∈ A.supp

  supp_sat : ∀ w ∈ A.supp, ∀ w', prW w' = prW w → w' ∈ A.supp

  dsig_pos : ∀ τ, 0 < A.dsig τ

variable (W Ch) in
open Classical in

def ColArg.minimal (num : ScNum) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sq : Set ℕ) : ColArg W Ch where
  num := num
  served := ∅
  tauP _ := 0
  yM _ _ := ⊥
  supp := Finset.univ.biUnion fun u => (finite_prW (K := X.K) (Pr.T u)).toFinset
  sg _ _ := 0
  sel := sel
  Sq := Sq

theorem ColArg.minimal_ok (hW : W.Ok) (num : ScNum) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sq : Set ℕ) :
    ColArgOk W Ch (ColArg.minimal W Ch num sel Sq) where
  np_lat u w hw := absurd hw (Finset.notMem_empty _)
  supp_served w h := absurd h (Finset.notMem_empty _)
  served_alt u := Finset.notMem_empty _
  supp_alt u w h := by
    classical
    show w ∈ Finset.univ.biUnion fun u => (finite_prW (K := X.K) (Pr.T u)).toFinset
    exact Finset.mem_biUnion.2 ⟨u, Finset.mem_univ u, (Set.Finite.mem_toFinset _).2 h⟩
  supp_sat w hw w' h := by
    classical
    change w ∈ Finset.univ.biUnion (fun u => (finite_prW (K := X.K) (Pr.T u)).toFinset) at hw
    show w' ∈ Finset.univ.biUnion fun u => (finite_prW (K := X.K) (Pr.T u)).toFinset
    obtain ⟨u, -, hu⟩ := Finset.mem_biUnion.1 hw
    have hu' : prW w = Pr.T u := (Set.Finite.mem_toFinset (finite_prW (K := X.K) (Pr.T u))).1 hu
    exact Finset.mem_biUnion.2 ⟨u, Finset.mem_univ u, (Set.Finite.mem_toFinset _).2 (h.trans hu')⟩
  dsig_pos τ := dsigC_pos W hW τ

variable (W Ch) in

structure ColOpen : Prop where

  nlam_le : ∀ u w, prW w = Pr.T u → atW w (NlamG W Ch u w) ≤ atW w (MramL W Ch u)

  nlam_len : ∀ u w, prW w = Pr.T u →
    ((lenUW w (MramL W Ch u) (NlamG W Ch u w) : ℚ) : ℝ) ≤ (finrank X.K (MfV W Ch u) : ℝ) * lambdaConstant W u

  tum_inj : ∀ u w, prW w = Pr.T u → Function.Injective (TUmR W Ch u w)

  weightConst_nonneg : 0 ≤ A.num.C0

  numbersZ : ∀ u, NumbersC Pr R u A.num.C0 A.num.sc.a A.num.sc.b' (logAvC X A.num) A.num.eta A.num.Sc

  wtWinZ : ∀ u, WtWin W u A.num.C0 A.num.sc.a A.num.sc.b' A.num.Sc

  z5a : ∀ u, SummandSlopeAtDecoratedLattice W Ch u

  z5b : ∀ u, MaxSlopeSummandWithConstant W Ch u A.num.C0

  dualSlope : ∀ u τ, DualSlope X.K (W.lamTrue u 0 τ)

  z4 : ∀ u τ, MaxSlopeNablaBound X.K (kap_succ R) (W.lamTrue u 0 τ)

  log_height_lower_bound : ∀ u, xLowC W A.num ≤ Real.log (XuC W Ch A.dsig u)

  log_height_upper_bound : ∀ u, Real.log (XuC W Ch A.dsig u) ≤ xUpC R A.num

  weylDim : ∀ u τ, WeylDim (W.lamTrue u 0 τ)

  vandVar : ∀ u u' τ, |Real.log (Formalism.LogVandermondeBounds.StandardLattice.vandN (hcSeq W u τ) R.k) - Real.log (Formalism.LogVandermondeBounds.StandardLattice.vandN (hcSeq W u' τ) R.k)| ≤
    (R.k : ℝ) * (1 + Real.log (R.k : ℝ)) + 2

theorem NlamG_of_not_seenC (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (hw : prW w = Pr.T u)
    (h : ¬ seenC Pr u w) : NlamG W Ch u w = MramL W Ch u :=
  NlamG_of_seenBarC W Ch hPr u w
    ((seenC_or_seenBarC hX hPr u w (by rw [← hw]; exact natCast_prW_mem w)).resolve_left h)

theorem iface_f_pos (hX : X.Ok) : 0 < X.f := by
  rw [Fields.f, hX.card_Tau]
  exact Module.finrank_pos

theorem iface_T_big {a : ℝ} (hS : Sizes Pr W a) (u : Pr.Word) : 4 * X.f ≤ Pr.T u := by
  have h1 := hS.T_big u
  have h2 : 2 ≤ R.N R.m := by
    have := R.m_add_three_le_k
    unfold Ranks.N
    omega
  have h3 : 2 * X.f * 2 ≤ 2 * X.f * R.N R.m := Nat.mul_le_mul_left _ h2
  omega

theorem iface_T_gt (hX : X.Ok) {a : ℝ} (hS : Sizes Pr W a) (u : Pr.Word) : 2 < Pr.T u := by
  have h1 := iface_T_big hS u
  have h2 := iface_f_pos hX
  omega

theorem lambdaConstant_nonneg (h : ∀ u, ∀ τ ∈ W.tops, (0 : ℝ) ≤ (W.aTop u τ : ℝ)) (u : Pr.Word) : 0 ≤ lambdaConstant W u := by
  unfold lambdaConstant
  refine mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun τ hτ => ?_)
  have h1 : (0 : ℝ) ≤ (W.aTop u τ : ℝ) := h u τ hτ
  have h2 : (1 : ℝ) ≤ (R.k : ℝ) := by
    have := R.m_add_three_le_k
    exact_mod_cast (show 1 ≤ R.k by omega)
  have h3 : (0 : ℝ) ≤ (W.aTop u τ : ℝ) / (R.k : ℝ) := div_nonneg h1 (by linarith)
  have h4 : (0 : ℝ) ≤ (WtauC W u τ : ℝ) := Nat.cast_nonneg _
  linarith

variable (W Ch) in

def colIface (hPr : Pr.Ok) (hS : Sizes Pr W A.num.sc.a) (hA : ColArgOk W Ch A) (hO : ColOpen W Ch A) :
    ColIface X.K Pr.Word where
  toColObj := colObj W Ch hX A
  cplx := hX.cplxK
  f_pos := iface_f_pos hX
  T_prime := hPr.T_prime
  T_big := iface_T_big hS
  Mf_good := Mu0H_good W Ch hX
  M_good := MramH_good W Ch hX
  incl_inj := ramInclH_injective W Ch hX
  incl_norm := ramInclH_norm W Ch hX
  M_L := MramH_L W Ch hX
  Vr_iso := VrC_isometry W Ch hX
  Vr_fcoord := VrC_fcoord W Ch hX
  rank_full u := by
    show (Fintype.card (Mu0H W Ch hX u).ι : ℝ) = dstarC W Ch u * ((Pr.T u : ℝ) ^ R.k - 1) ^ X.f
    rw [card_Mu0H]
    exact finrank_MfV_eq W Ch hX hPr (hS.g_big 0) u
  dstar_pos := dstarC_pos W Ch hX
  rank_ram u := card_MramH_eq W Ch hX hPr (hS.g_big 0) u (iface_T_gt hX hS u)
  rank_pos u := card_MramH_pos W Ch hX hPr (hS.g_big 0) u (iface_T_gt hX hS u)
  slope_ram u := MramH_mu W Ch hX hPr (hS.g_big 0) u (iface_T_gt hX hS u)
  slopeMax_ram u := MramH_muMax_le W Ch hX hPr (hS.g_big 0) u (iface_T_gt hX hS u)
  Nlam_le := hO.nlam_le
  Nlam_bar u w hw h := congrArg (atW w) (NlamG_of_not_seenC hX hPr u w hw h)
  Nlam_len u w h := by
    show ((lenUW w (MramL W Ch u) (NlamG W Ch u w) : ℚ) : ℝ) ≤ (Fintype.card (Mu0H W Ch hX u).ι : ℝ) * lambdaConstant W u
    rw [card_Mu0H]
    exact hO.nlam_len u w h
  lamT_nonneg := lambdaConstant_nonneg fun u τ hτ =>
    le_trans (le_of_lt (mul_pos (by linarith [A.num.sc.one_lt_alt]) (Real.exp_pos _))) ((hO.wtWinZ u).top τ hτ).1
  Nu_fg u := (NuC_isLattice hX hPr (A.Sv u) (fun w h => NlamG_isLattice hX u w (hO.tum_inj u w h)) (hA.np_lat u)).fg
  Nu_comm u := by
    show ∃ c : 𝓞 X.K, c ≠ 0 ∧ ∀ y ∈ MramL W Ch u, c • y ∈ NuC (A.Sv u)
    have : Module.Finite X.K (MramV W Ch u) := Module.Finite.of_basis (MramH W Ch hX u).b
    exact exists_smul_le_of_lattice (iface_MramL_isLattice hX u).fg
      (NuC_isLattice hX hPr (A.Sv u) (fun w h => NlamG_isLattice hX u w (hO.tum_inj u w h)) (hA.np_lat u))
  Nu_atT u w h := localization_at_T_eq hX hPr (A.Sv u) (fun w h => NlamG_isLattice hX u w (hO.tum_inj u w h)) (hA.np_lat u) w h
  Nu_off u w h := atW_NuC_off hX hPr (A.Sv u) (fun w h => NlamG_isLattice hX u w (hO.tum_inj u w h)) (hA.np_lat u) w
    (fun h1 => h (hA.supp_alt u w h1)) (fun h1 => h (hA.supp_served w h1))
  Nu_le_ItM u := NuC_le_ItM hX A hPr u (fun w h => NlamG_isLattice hX u w (hO.tum_inj u w h)) (hA.np_lat u) (hO.nlam_le u)
    (hA.served_alt u) hA.supp_served
  tau_nonneg w := by
    show 0 ≤ A.tau w
    unfold ColArg.tau
    split_ifs
    · exact Nat.cast_nonneg _
    · exact le_refl _
  tau_eq_zero_at_T u w h := by
    show A.tau w = 0
    have h' : prW w = Pr.T u := h
    unfold ColArg.tau
    rw [h', if_neg (hA.served_alt u)]
  supp_alt := hA.supp_alt
  supp_sat := hA.supp_sat
  propZ_low u := ((cZC_spec hO.weightConst_nonneg).2 W Ch hX hPr (hS.g_big 0) u A.num.sc.a A.num.sc.b' (logAvC X A.num) A.num.eta A.num.Sc
    (hO.numbersZ u) (hO.wtWinZ u) (hO.z5a u) (hO.z5b u) (hO.dualSlope u) (hO.z4 u)).1
  propZ_up u := ((cZC_spec hO.weightConst_nonneg).2 W Ch hX hPr (hS.g_big 0) u A.num.sc.a A.num.sc.b' (logAvC X A.num) A.num.eta A.num.Sc
    (hO.numbersZ u) (hO.wtWinZ u) (hO.z5a u) (hO.z5b u) (hO.dualSlope u) (hO.z4 u)).2
  Dstar_pos := DstarC_pos hX hA.dsig_pos
  Xu_pos := XuC_pos W Ch hX hA.dsig_pos
  Xu_pow := XuC_pow W Ch hX hA.dsig_pos
  log_height_lower_bound := hO.log_height_lower_bound
  log_height_upper_bound := hO.log_height_upper_bound
  log_height_variation_bound u u' := by
    have hk : 1 ≤ R.k := by
      have := R.m_add_three_le_k
      omega
    have hD := DstarC_pos (Pr := Pr) (R := R) hX hA.dsig_pos
    have h := variation_col W Ch hX hk u u' (hO.weylDim u) (hO.weylDim u') (DstarC Pr R A.dsig)
      ((R.k : ℝ) * (1 + Real.log (R.k : ℝ)) + 2) hD (hO.vandVar u u')
    show |Real.log (XuC W Ch A.dsig u) - Real.log (XuC W Ch A.dsig u')| ≤ xVarC R
    unfold XuC
    rw [Real.log_rpow (div_pos hD (dstarC_pos W Ch hX u)), Real.log_rpow (div_pos hD (dstarC_pos W Ch hX u'))]
    refine le_trans h (le_of_eq ?_)
    have hk' : (R.k : ℝ) ≠ 0 := by exact_mod_cast (show R.k ≠ 0 by omega)
    unfold xVarC
    field_simp
  Mtil_good := MtildeH_good W Ch hX A.sel _ (rPsymF Ch)

end Conc

section RowSide

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (hX : X.Ok)

structure RowFacts : Prop where
  mtilde_good : ∀ P, (MtildeCSD W Ch sel mu P (mtildeOk W Ch sel mu hX P)).Good 1
  mtilde_rat : ∀ P, (MtildeCSD W Ch sel mu P (mtildeOk W Ch sel mu hX P)).Rat
  mtildeK_good : (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).Good 1
  mtildeK_rat : (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).Rat
  mt_good : ∀ P j, (MtCSD W Ch sel mu P j (mtOk W Ch sel mu hX P j)).Good 1
  mt_rat : ∀ P j, (MtCSD W Ch sel mu P j (mtOk W Ch sel mu hX P j)).Rat
  mtK_good : ∀ j, (MtKCSD W Ch sel mu j (mtKOk W Ch sel mu hX j)).Good 1
  mtK_rat : ∀ j, (MtKCSD W Ch sel mu j (mtKOk W Ch sel mu hX j)).Rat
  reference_action_good : (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).ActGood (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX))
  reference_action_rational : (MtildeKCSD W Ch sel mu (mtildeKOk W Ch sel mu hX)).ActRat (g0Act W Ch sel mu (mtildeKOk W Ch sel mu hX))
  reference_action_good_levels : ∀ j, (MtKCSD W Ch sel mu j (mtKOk W Ch sel mu hX j)).ActGood (unipotentRightActionOnForms W Ch sel mu j (mtKOk W Ch sel mu hX j))
  reference_action_rational_levels : ∀ j, (MtKCSD W Ch sel mu j (mtKOk W Ch sel mu hX j)).ActRat (unipotentRightActionOnForms W Ch sel mu j (mtKOk W Ch sel mu hX j))

  mtildeH_good : ∀ P, (MtildeH W Ch hX sel mu P).Good
  mtH_good : ∀ P j, (MtH W Ch hX sel mu P j).Good

theorem rowFacts : RowFacts W Ch sel mu hX where
  mtilde_good P := MtildeCSD_good W Ch sel mu hX P _
  mtilde_rat P := MtildeCSD_rat W Ch sel mu hX P _
  mtildeK_good := MtildeKCSD_good W Ch sel mu hX _
  mtildeK_rat := MtildeKCSD_rat W Ch sel mu hX _
  mt_good P j := MtCSD_good W Ch sel mu hX P j _
  mt_rat P j := MtCSD_rat W Ch sel mu hX P j _
  mtK_good j := MtKCSD_good W Ch sel mu hX j _
  mtK_rat j := MtKCSD_rat W Ch sel mu hX j _
  reference_action_good := unipotentActionForms_good W Ch sel mu hX _
  reference_action_rational := unipotentActionForms_rational W Ch sel mu hX _
  reference_action_good_levels j := unipotentActionClassSum_good W Ch sel mu hX j _
  reference_action_rational_levels j := unipotentActionClassSum_rational W Ch sel mu hX j _
  mtildeH_good P := MtildeH_good W Ch hX sel mu P
  mtH_good P j := MtH_good W Ch hX sel mu P j

theorem colCSD_rat (u : Pr.Word) (j : ℕ) : (ColCSD W Ch u j (colOk W Ch hX u j)).Rat :=
  (colGSD W Ch u j).toCSDOf_rat _ (colRat W Ch hX u j) _

end RowSide

section Empty

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def colIfaceEmpty (hK : IsTotallyComplex K) (f k m : ℕ) (hf : 0 < f) (Mtil : HLat K) (hM : Mtil.Good) : ColIface K Empty where
  f := f
  k := k
  m := m
  T u := u.elim
  Mf u := u.elim
  M u := u.elim
  incl u := u.elim
  Vr u := u.elim
  dstar u := u.elim
  overPi u := u.elim
  Nlam u := u.elim
  lamT u := u.elim
  Nu u := u.elim
  supp := ∅
  sg u := u.elim
  tau _ := 0
  zLow u := u.elim
  zUp u := u.elim
  Dstar := 1
  Xu u := u.elim
  xLow := 0
  xUp := 0
  xVar := 0
  Mtil := Mtil
  cplx := hK
  f_pos := hf
  T_prime u := u.elim
  T_big u := u.elim
  Mf_good u := u.elim
  M_good u := u.elim
  incl_inj u := u.elim
  incl_norm u := u.elim
  M_L u := u.elim
  Vr_iso u := u.elim
  Vr_fcoord u := u.elim
  rank_full u := u.elim
  dstar_pos u := u.elim
  rank_ram u := u.elim
  rank_pos u := u.elim
  slope_ram u := u.elim
  slopeMax_ram u := u.elim
  Nlam_le u := u.elim
  Nlam_bar u := u.elim
  Nlam_len u := u.elim
  lamT_nonneg u := u.elim
  Nu_fg u := u.elim
  Nu_comm u := u.elim
  Nu_le_ItM u := u.elim
  tau_nonneg _ := le_refl 0
  tau_eq_zero_at_T u := u.elim
  Nu_atT u := u.elim
  Nu_off u := u.elim
  supp_alt u := u.elim
  supp_sat w hw := absurd hw (Finset.notMem_empty w)
  propZ_low u := u.elim
  propZ_up u := u.elim
  Dstar_pos := one_pos
  Xu_pos u := u.elim
  Xu_pow u := u.elim
  log_height_lower_bound u := u.elim
  log_height_upper_bound u := u.elim
  log_height_variation_bound u := u.elim
  Mtil_good := hM

end Empty

end Formalism.L2.Col
