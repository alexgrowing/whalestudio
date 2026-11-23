import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceModelRestrictedTensorFixedHalf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelCompIdempotentSplitTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowColumnProductDataHaveVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesSplitIdempotentSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SubsetVecs

open GlobalTheory.FinPl.PutIn

variable {D : D7} {S T : HSp D} {ι : Type} [DecidableEq ι]

def prodD (a : ι → AE D) (Ψ : ι → WO S T → ℂ) (s : Finset ι) (y : WO S T) : ℂ :=
  if IsHalf (∑ w ∈ s, a w) y then ∏ w ∈ s, Ψ w (a w • y) else 0

theorem sum_mul_zero {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0) {s : Finset ι} {w : ι} (hw : w ∉ s) :
    (∑ v ∈ s, a v) * a w = 0 := by
  rw [Finset.sum_mul]
  exact Finset.sum_eq_zero fun v hv => ho v w fun h => hw (h ▸ hv)

theorem prodD_empty (a : ι → AE D) (Ψ : ι → WO S T → ℂ) (Λ : AddSubgroup (WO S T)) :
    prodD a Ψ ∅ = halfInd 0 Λ := by
  funext y
  unfold prodD halfInd
  rw [Finset.sum_empty, Finset.prod_empty]
  by_cases h : IsHalf (0 : AE D) y
  · rw [if_pos h, if_pos ⟨(GlobalTheory.VecProd.isHalf_zero_iff y).1 h ▸ Λ.zero_mem, h⟩]
  · rw [if_neg h, if_neg fun h' => h h'.2]

theorem prodD_insert {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0) (Ψ : ι → WO S T → ℂ) {s : Finset ι} {w : ι}
    (hw : w ∉ s) : prodD a Ψ (insert w s) = tens (a w) (prodD a Ψ s) (Ψ w) := by
  funext y
  have h0 := sum_mul_zero ho hw
  have hiff : IsHalf (a w + ∑ v ∈ s, a v) y ↔ IsHalf (∑ v ∈ s, a v) (y - a w • y) :=
    GlobalTheory.VecProd.isHalf_add_iff h0 y
  have hp : ∏ v ∈ s, Ψ v (a v • (y - a w • y)) = ∏ v ∈ s, Ψ v (a v • y) :=
    Finset.prod_congr rfl fun v hv => by
      rw [smul_sub, smul_smul, ho v w fun h => hw (h ▸ hv), zero_smul, sub_zero]
  rw [tens_apply]
  unfold prodD
  rw [Finset.sum_insert hw, Finset.prod_insert hw, hp]
  by_cases h : IsHalf (a w + ∑ v ∈ s, a v) y
  · rw [if_pos h, if_pos (hiff.1 h), mul_comm]
  · rw [if_neg h, if_neg fun h' => h (hiff.2 h'), zero_mul]

theorem prodD_congr (a : ι → AE D) {Ψ Ψ' : ι → WO S T → ℂ} {s : Finset ι} (h : ∀ w ∈ s, Ψ w = Ψ' w) :
    prodD a Ψ s = prodD a Ψ' s := by
  funext y
  unfold prodD
  rw [Finset.prod_congr rfl fun w hw => congrFun (h w hw) _]

theorem prodD_sb {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0) (hi : ∀ w, a w * a w = a w)
    {Λ : AddSubgroup (WO S T)} (hΛ : ∀ w, ∀ u ∈ Λ, a w • u ∈ Λ) {Ψ : ι → WO S T → ℂ}
    (hΨ : ∀ w, IsSBHalf (a w) Λ (Ψ w)) (s : Finset ι) : IsSBHalf (∑ w ∈ s, a w) Λ (prodD a Ψ s) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [prodD_empty a Ψ Λ, Finset.sum_empty]
    exact GlobalTheory.isSBHalf_halfInd _ _
  | insert w s hw ih =>
    rw [prodD_insert ho Ψ hw, Finset.sum_insert hw, add_comm]
    exact Factor.isSBHalf_tens (sum_mul_zero ho hw) (hi w) (hΛ w) ih (hΨ w)

theorem prodD_ind {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0) (hi : ∀ w, a w * a w = a w)
    {Λ : AddSubgroup (WO S T)} (hΛ : ∀ w, ∀ u ∈ Λ, a w • u ∈ Λ) (s : Finset ι) :
    prodD a (fun w => halfInd (a w) Λ) s = halfInd (∑ w ∈ s, a w) Λ := by
  induction s using Finset.induction_on with
  | empty => rw [prodD_empty a _ Λ, Finset.sum_empty]
  | insert w s hw ih =>
    rw [prodD_insert ho _ hw, Finset.sum_insert hw, add_comm, ih]
    have h := HalfOff.tens_vac (sum_mul_zero ho hw) (hi w) Λ (hΛ w)
    rwa [one_smul, one_smul] at h

theorem exists_chain [Fintype ι] {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0)
    (hi : ∀ w, a w * a w = a w) (hinf : ∀ w, infPart D (a w) = 0) {Ψ : ι → WO S T → ℂ}
    (hΨ : ∀ w, IsSBHalf (a w) (latO S T ΛS ΛT fun _ => True) (Ψ w)) {f₀ f : WO S T → ℂ} (h₀ : IsThetaFunO ψ S T f₀)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) (∑ w, a w) (latO S T ΛS ΛT fun _ => True) 1 f₀
      (prodD a Ψ Finset.univ) f) :
    ∃ V : Finset ι → WO S T → ℂ, V ∅ = f₀ ∧ V Finset.univ = f ∧ (∀ s, IsThetaFunO ψ S T (V s)) ∧
      ∀ s w, w ∉ s → IsThetaAt ψ (symplO S T) (heisO ψ S T) (a w) (latO S T ΛS ΛT fun _ => True) 1 (V s) (Ψ w)
        (V (insert w s)) := by
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hf
  have hΛ : ∀ w, ∀ u ∈ (latO S T ΛS ΛT fun _ => True), a w • u ∈ (latO S T ΛS ΛT fun _ => True) :=
    fun w u hu => GlobalTheory.CosetRow.smul_mem_latO_idem _ _ (hi w) hu
  let mix : Finset ι → ι → WO S T → ℂ := fun s w =>
    if w ∈ s then Ψ w else halfInd (a w) (latO S T ΛS ΛT fun _ => True)
  have hmix : ∀ s w, IsSBHalf (a w) (latO S T ΛS ΛT fun _ => True) (mix s w) := fun s w => by
    by_cases h : w ∈ s
    · simp only [mix, if_pos h]; exact hΨ w
    · simp only [mix, if_neg h]; exact GlobalTheory.isSBHalf_halfInd _ _
  have hV0 : Tm (prodD a (mix ∅) Finset.univ) = f₀ := by
    rw [prodD_congr a (Ψ' := fun w => halfInd (a w) (latO S T ΛS ΛT fun _ => True))
      (fun w _ => if_neg (Finset.notMem_empty w)), prodD_ind ho hi hΛ]
    have h := hTm.vac
    rwa [one_smul] at h
  have hstep : ∀ s w, w ∉ s → IsThetaAt ψ (symplO S T) (heisO ψ S T) (a w) (latO S T ΛS ΛT fun _ => True) 1
      (Tm (prodD a (mix s) Finset.univ)) (Ψ w) (Tm (prodD a (mix (insert w s)) Finset.univ)) := by
    intro s w hw
    have hne : w ∉ Finset.univ.erase w := Finset.notMem_erase w _
    have hu : (Finset.univ : Finset ι) = insert w (Finset.univ.erase w) :=
      (Finset.insert_erase (Finset.mem_univ w)).symm
    have e1 : prodD a (mix s) Finset.univ = tens (a w) (prodD a (mix s) (Finset.univ.erase w))
        (halfInd (a w) (latO S T ΛS ΛT fun _ => True)) := by
      conv_lhs => rw [hu]
      rw [prodD_insert ho _ hne]
      simp only [mix, if_neg hw]
    have e2 : prodD a (mix (insert w s)) Finset.univ = tens (a w) (prodD a (mix s) (Finset.univ.erase w)) (Ψ w) := by
      conv_lhs => rw [hu]
      rw [prodD_insert ho _ hne, prodD_congr a (Ψ := mix (insert w s)) (Ψ' := mix s) fun v hv => by
        have hvw : v ≠ w := Finset.ne_of_mem_erase hv
        simp only [mix, Finset.mem_insert, hvw, false_or]]
      simp only [mix, if_pos (Finset.mem_insert_self w s)]
    have hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) ((∑ v ∈ Finset.univ.erase w, a v) + a w)
        (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm := by
      rwa [Finset.sum_erase_add _ _ (Finset.mem_univ w)]
    have hM := Factor.isPlaceModel_tensR D ψ S T _ (a w) _ _ _ f₀ Tm (sum_mul_zero ho hne) (hi w) (hΛ w)
      (fun _ _ => Iff.rfl) (prodD_sb ho hi hΛ (hmix s) (Finset.univ.erase w)) hTm'
    rw [e1, e2]
    exact ⟨⟨_, hM⟩, fun T' hT' => GlobalTheory.PlaceVec.placeModel_unique hψ hS hT (hi w) (hinf w) hM hT' (hΨ w)⟩
  refine ⟨fun s => Tm (prodD a (mix s) Finset.univ), hV0, ?_, fun s => ?_, hstep⟩
  · rw [hall Tm hTm]
    exact congrArg Tm (prodD_congr a fun w hw => if_pos hw)
  · induction s using Finset.induction_on with
    | empty => beta_reduce; rw [hV0]; exact h₀
    | insert w s hw ih => exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (hstep s w hw) ih

theorem idemAt_of_single {a : AE D} {w : Pl D.host.E} (h : IsIdemSum a {w}) : Formalism.L2.NTheta.IsIdemAt a w := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  rw [Finset.sum_singleton]
  exact hes w (Finset.mem_singleton_self w)

theorem sum_eq {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {a : P → AE D}
    (ha : ∀ w, IsIdemSum (a w) {w.1}) : ∑ w, a w = e := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [← Finset.sum_coe_sort P es]
  exact Finset.sum_congr rfl fun w _ => by
    rw [GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt (idemAt_of_single (ha w)), GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt (hes w.1 w.2)]

theorem orth {a b : AE D} {v w : Pl D.host.E} (ha : IsIdemSum a {v}) (hb : IsIdemSum b {w}) (h : v ≠ w) : a * b = 0 := by
  have h1 := cpt_of_isIdemAt (idemAt_of_single ha)
  have h2 := cpt_of_isIdemAt (idemAt_of_single hb)
  refine ae_ext ?_ fun Q => ?_
  · rw [map_mul, GlobalTheory.PlaceVec.idemSum_infPart ha, zero_mul, map_zero]
  · rw [map_mul, map_mul, map_zero, map_zero]
    by_cases hQ : Q = v
    · rw [h2.2 Q (hQ ▸ h), mul_zero]
    · rw [h1.2 Q hQ, zero_mul]

theorem map_cpt_smul {a : AE D} {w : Pl D.host.E} (ha : IsIdemSum a {w}) {m n : ℕ} (y : Mx D m n) :
    ((a • y).map fun x => cpt w (toEAf D x)) = y.map fun x => cpt w (toEAf D x) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [map_mul, map_mul, (cpt_of_isIdemAt (idemAt_of_single ha)).1, one_mul]

theorem subset_vectors : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → ∀ (eL : locPl ch.G t → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → ∃ V : Finset (locPl ch.G t) → SchDown ch.G t, V ∅ = (fun j : Fin D.R.m => ch.rm.vT D.R.m j) ∧ V Finset.univ = fd ∧ (∀ S j, IsThetaFunO ch.W.ψ _ _ (V S j)) ∧ ∀ (S : Finset (locPl ch.G t)) (w : locPl ch.G t), w ∉ S → ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) (eL w) (V S j) (fun y => if IsHalf (eL w) y then φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (V (insert w S) j) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t e he φ hφ fd hfd eL heL
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
  have ho : ∀ v w, v ≠ w → eL v * eL w = 0 := fun v w h => orth (heL v) (heL w) fun h' => h (Subtype.ext h')
  have hi : ∀ w, eL w * eL w = eL w := fun w => GlobalTheory.PlaceVec.idemSum_mul_self (heL w)
  have hinf : ∀ w, infPart D (eL w) = 0 := fun w => GlobalTheory.PlaceVec.idemSum_infPart (heL w)
  have hsum := sum_eq he heL
  have key : ∀ j : Fin D.R.m, ∃ V : Finset (locPl ch.G t) → Sch ch.G (.down t D.R.m j), V ∅ = ch.rm.vT D.R.m j ∧
      V Finset.univ = fd j ∧ (∀ S, IsThetaFunO ch.W.ψ _ _ (V S)) ∧
      ∀ (S : Finset (locPl ch.G t)) (w : locPl ch.G t), w ∉ S → IsLocVec ch.W (.mu t D.R.m j) (eL w) (V S) (fun y => if IsHalf (eL w) y then φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (V (insert w S)) := by
    intro j
    have hS : IsSelfDualC (ch.G.pS (.mu t D.R.m j)) (ch.G.latS (.mu t D.R.m j)) :=
      (node_isV ch.G hL (X := .grid D.R.m j) ⟨le_rfl, j.2.le⟩).sd
    have hT : IsSelfDualC (ch.G.pT (.mu t D.R.m j)) (ch.G.latT (.mu t D.R.m j)) :=
      (node_isV ch.G hL (X := .grid D.R.m ((j : ℕ) + 1)) ⟨le_rfl, j.2⟩).sd
    have hβS := ch.S.B.isFrame_β hL (i := D.R.m) (j := (j : ℕ)) le_rfl j.2.le
    have hβT := ch.S.B.isFrame_β hL (i := D.R.m) (j := (j : ℕ) + 1) le_rfl j.2
    have hmem : GlobalTheory.SplitFlip.Edge.theta D.R.m j ∈ GlobalTheory.SplitFlip.oppositePath D.R.m := by
      simp [GlobalTheory.SplitFlip.oppositePath]
    let Ψ : locPl ch.G t → WO (ch.G.pS (.mu t D.R.m j)) (ch.G.pT (.mu t D.R.m j)) → ℂ := fun w y =>
      if IsHalf (eL w) y then φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0
    have hΨ : ∀ w, IsSBHalf (eL w) (latO (ch.G.pS (.mu t D.R.m j)) (ch.G.pT (.mu t D.R.m j))
        (ch.G.latS (.mu t D.R.m j) : Set _) (ch.G.latT (.mu t D.R.m j) : Set _) fun _ => True) (Ψ w) := by
      intro w
      have hin : ∀ v : ({w.1} : Finset (Pl D.host.E)), v.1 ∈ locPl ch.G t := fun v => by
        rw [Finset.mem_singleton.1 v.2]; exact w.2
      have hSB := GlobalTheory.VecsLast.isSBHalf_frames hS hT hβS hβT (heL w) (fun v hv => hAA v (hin ⟨v, hv⟩))
        (fun v => GlobalTheory.VecsLast.coordHom ch.S.B t v.1 (X := (D.R.m, (j : ℕ) + 1)) (Y := (D.R.m, (j : ℕ))) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩)
        (fun v z => GlobalTheory.VecsLast.coordHom_int_iff ch.S.B t v.1 (X := (D.R.m, (j : ℕ) + 1)) (Y := (D.R.m, (j : ℕ))) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ z)
        (fun v => depthAt ch.G v.1) (fun v => φ ⟨v.1, hin v⟩ (.theta D.R.m j))
        (fun v => (GlobalTheory.VecsLast.natDatum_props (hφ ⟨v.1, hin v⟩ _ hmem)).1)
        (fun v => (GlobalTheory.VecsLast.natDatum_props (hφ ⟨v.1, hin v⟩ _ hmem)).2)
      haveI : Subsingleton ({w.1} : Finset (Pl D.host.E)) :=
        ⟨fun a b => Subtype.ext ((Finset.mem_singleton.1 a.2).trans (Finset.mem_singleton.1 b.2).symm)⟩
      convert hSB using 1
      funext y
      rw [Fintype.prod_subsingleton _ ⟨w.1, Finset.mem_singleton_self _⟩]
      rfl
    have hprod : prodD eL Ψ Finset.univ = fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0 := by
      funext y
      unfold prodD
      rw [hsum]
      refine if_congr Iff.rfl (Finset.prod_congr rfl fun w _ => ?_) rfl
      refine (if_pos (Factor.half_of_idem (hi w) y)).trans ?_
      exact congrArg (fun z => φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ z)) (map_cpt_smul (heL w) y)
    obtain ⟨V, h1, h2, h3, h4⟩ := exists_chain ch.W.ψ_std ch.W.θ_is hS hT ho hi hinf hΨ
      (ch.rm.vT_is t D.R.m j le_rfl j.2).2.theta (f := fd j) (by rw [hsum, hprod]; exact (hfd j).2)
    exact ⟨V, h1, h2, h3, fun S w hw => ⟨hΨ w, h4 S w hw⟩⟩
  choose V h1 h2 h3 h4 using key
  exact ⟨fun S j => V j S, funext h1, funext h2, fun S j => h3 j S, fun S w hw j => h4 j S w hw⟩

end GlobalTheory.SubsetVecs

end
