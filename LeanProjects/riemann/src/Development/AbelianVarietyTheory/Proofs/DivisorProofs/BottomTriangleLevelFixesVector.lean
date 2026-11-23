import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegralFundamentalDomainEqSumDoubleCoset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTowerConstantsDifferByFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassSumIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRightOfMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassSignature
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumEqProdSplitPlaceFactors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdemAtUniqueOrth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPlEqCP
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitSumStabLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterUnramifiedMu
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataLines
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.BotFinLevel

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter GlobalTheory.RowVacScalar Formalism.L2.DIV
open Formalism.IndefR.Fin.LevelGroupLemmas.Lat (frG intM)

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

theorem prod_idem {R ι : Type} [CommRing R] [DecidableEq ι] (es : ι → R) (d : R) (s : Finset ι)
    (h : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → es a * es b = 0) :
    ∏ a ∈ s, (es a * d + (1 - es a)) = (∑ a ∈ s, es a) * d + (1 - ∑ a ∈ s, es a) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ih fun x hx y hy => h x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)]
    have h0 : es a * ∑ b ∈ s, es b = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun b hb => h a (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb)
        fun e => ha (e ▸ hb)
    linear_combination (d - 1) ^ 2 * h0

theorem isUnitDet_unique {e : Formalism.L2.Theta.AE D} {k : ℕ} {N : Matrix (Fin k) (Fin k) (Lev.EAf D)} {x y : (Formalism.L2.Theta.AE D)ˣ}
    (hx : IsUnitDet e N x) (hy : IsUnitDet e N y) : x = y :=
  Units.ext (StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.eq_of_parts (hx.1.trans hy.1.symm) (hx.2.1.trans hy.2.1.symm))

theorem ring_mul {R : Type} [CommRing R] {ε a b : R} (h : ε * ε = ε) :
    (1 - ε + ε * a) * (1 - ε + ε * b) = 1 - ε + ε * (a * b) := by
  linear_combination (1 - a - b + a * b) * h

theorem isUnitDet_mul {e : Formalism.L2.Theta.AE D} (he : e * e = e) {k : ℕ} {M N : Matrix (Fin k) (Fin k) (Lev.EAf D)}
    {x y : (Formalism.L2.Theta.AE D)ˣ} (hx : IsUnitDet e M x) (hy : IsUnitDet e N y) : IsUnitDet e (M * N) (x * y) := by
  have hee : toEAf D e * toEAf D e = toEAf D e := by rw [← RingHom.map_mul, he]
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, RingHom.map_mul, hx.1, hy.1, one_mul]
  · rw [Units.val_mul, RingHom.map_mul, hx.2.1, hy.2.1, Matrix.det_mul]
    exact ring_mul hee
  · rw [mul_inv, Units.val_mul, RingHom.map_mul]
    exact mul_mem hx.2.2 hy.2.2

theorem unitChar_mul (ν : (Formalism.L2.Theta.AE D)ˣ →* Circle) {e : Formalism.L2.Theta.AE D} (he : e * e = e) {k : ℕ}
    {K K' : Matrix (Fin k) (Fin k) (Lev.EAf D)} (hK : K' * K = 1) {x x' : (Formalism.L2.Theta.AE D)ˣ} (hx : IsUnitDet e K x)
    (hx' : IsUnitDet e K' x') (N : Matrix (Fin k) (Fin k) (Lev.EAf D)) :
    unitChar ν e (K * N) = (((ν x)⁻¹ : Circle) : ℂ) * unitChar ν e N := by
  unfold unitChar
  by_cases h : ∃ y, IsUnitDet e N y
  · have h' : ∃ y, IsUnitDet e (K * N) y := ⟨_, isUnitDet_mul he hx h.choose_spec⟩
    rw [dif_pos h, dif_pos h', isUnitDet_unique h'.choose_spec (isUnitDet_mul he hx h.choose_spec), map_mul, mul_inv,
      Circle.coe_mul]
  · rw [dif_neg h, dif_neg, mul_zero]
    rintro ⟨y, hy⟩
    have := isUnitDet_mul he hx' hy
    rw [← Matrix.mul_assoc, hK, Matrix.one_mul] at this
    exact h ⟨_, this⟩

theorem rightBlock_mul {κ : Type} [CommRing κ] {k d : ℕ} (a : ℕ) (K : Matrix (Fin k) (Fin k) κ)
    (Y : Matrix (Fin k) (Fin d) κ) : rightBlock a (K * Y) = K * rightBlock a Y := by
  ext i j
  simp only [rightBlock, Matrix.mul_apply]
  split_ifs
  · rfl
  · simp

theorem inId_mul {I : Ideal (𝓞 D.host.E)} {k d : ℕ} {K : Matrix (Fin k) (Fin k) (Lev.EAf D)} (hK : IsIntM K)
    {Y : Matrix (Fin k) (Fin d) (Lev.EAf D)} {j : Fin d} (h : ∀ i, InId I (Y i j)) (i : Fin k) : InId I ((HMul.hMul K Y) i j) := by
  choose h1 h2 using h
  have hm : (HMul.hMul K Y) i j ∈ OO := by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hK i l) (h1 l)
  refine ⟨hm, ?_⟩
  have e : (⟨(HMul.hMul K Y) i j, hm⟩ : OO) = ∑ l, (⟨K i l, hK i l⟩ : OO) * ⟨Y l j, h1 l⟩ := Subtype.ext (by
    rw [AddSubmonoidClass.coe_finset_sum]
    exact Matrix.mul_apply)
  rw [e]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (h2 l)

theorem dualCoord_actO (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (g : Formalism.L2.Theta.GA D S) (y : WO S T) :
    dualCoord S T βS βT (actO S T g 1 y) = HMul.hMul (frG S βS g).1 (dualCoord S T βS βT y) := by
  have h1 : frG T βT 1 = 1 := by
    unfold frG
    rw [map_one, mul_one, inv_mul_cancel]
  unfold dualCoord
  rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_actO, h1, inv_one, Units.val_one, Matrix.mul_one, Matrix.mul_smul]

theorem isIntM_frG {S : HSp D} {β : GL (Fin S.rank) (Lev.EAf D)} {g : Formalism.L2.Theta.GA D S} (hg : Lev.finE S g ∈ St β) :
    IsIntM (frG S β g).1 := by
  obtain ⟨y, hy⟩ := hg
  have e : frG S β g = intGL D.host.F D.host.E _ y := by
    unfold frG
    rw [← hy]
    show β⁻¹ * (β * intGL D.host.F D.host.E _ y * β⁻¹) * β = _
    group
  rw [e]
  exact fun i j => (y.1 i j).2

theorem det_mem {k : ℕ} {N : Matrix (Fin k) (Fin k) (Lev.EAf D)} (hN : IsIntM N) : N.det ∈ OO := by
  rw [Matrix.det_apply]
  exact Subring.sum_mem _ fun σ _ => by
    rw [Units.smul_def]
    exact zsmul_mem (Subring.prod_mem _ fun i _ => hN _ _) _

theorem det_frG (S : HSp D) (β : GL (Fin S.rank) (Lev.EAf D)) (g : Formalism.L2.Theta.GA D S) :
    (frG S β g).1.det = toEAf D (Formalism.L2.Theta.mt S g).det := by
  rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG_coe, Matrix.det_units_conj', RingHom.map_det]
  rfl

theorem isUnitDet_frG {e : Formalism.L2.Theta.AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {S : HSp D}
    {β : GL (Fin S.rank) (Lev.EAf D)} {g : Formalism.L2.Theta.GA D S} (hg : Lev.finE S g ∈ St β) :
    IsUnitDet e (frG S β g).1 (detIdl e S g) := by
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
  have hinv : ((detIdl e S g)⁻¹ : (Formalism.L2.Theta.AE D)ˣ) = detIdl e S g⁻¹ := by
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    have h1 : (Formalism.L2.Theta.mt S g).det * (Formalism.L2.Theta.mt S g⁻¹).det = 1 := by
      rw [← Matrix.det_mul, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.mt_mul_inv, Matrix.det_one]
    rw [Units.val_mul, detIdl_val hee, detIdl_val hee, Units.val_one]
    linear_combination e * h1 + ((Formalism.L2.Theta.mt S g).det * (Formalism.L2.Theta.mt S g⁻¹).det - (Formalism.L2.Theta.mt S g).det -
      (Formalism.L2.Theta.mt S g⁻¹).det + 1) * hee
  refine ⟨?_, ?_, ?_⟩
  · rw [detIdl_val hee, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, hinf, RingHom.map_one, zero_mul, zero_add, sub_zero]
  · rw [detIdl_val hee, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, det_frG, add_comm]
  · rw [hinv, detIdl_val hee, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, ← det_frG S β]
    exact add_mem (mul_mem hE (det_mem (isIntM_frG (by rw [map_inv]; exact inv_mem hg)))) (sub_mem (one_mem _) hE)

theorem stdSnd_actO (ν : (Formalism.L2.Theta.AE D)ˣ →* Circle) {e : Formalism.L2.Theta.AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (I : Ideal (𝓞 D.host.E)) (a : ℕ) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    {g : Formalism.L2.Theta.GA D S} (hg : Lev.finE S g ∈ St βS) (y : WO S T) :
    stdSnd ν e I a S T βS βT (actO S T g 1 y) = (((ν (detIdl e S g))⁻¹ : Circle) : ℂ) * stdSnd ν e I a S T βS βT y := by
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hg' : Lev.finE S g⁻¹ ∈ St βS := by rw [map_inv]; exact inv_mem hg
  have hK : (frG S βS g⁻¹).1 * (frG S βS g).1 = 1 := by
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG_inv, Units.inv_mul]
  have hback : dualCoord S T βS βT y =
      HMul.hMul (frG S βS g⁻¹).1 (HMul.hMul (frG S βS g).1 (dualCoord S T βS βT y)) := by
    rw [← Matrix.mul_assoc, hK, Matrix.one_mul]
  unfold stdSnd
  rw [dualCoord_actO]
  by_cases hc : IsHalf (cA D e) y ∧ IsIntM (dualCoord S T βS βT y) ∧ ∀ i j, j.1 < a → InId I (dualCoord S T βS βT y i j)
  · rw [if_pos hc, if_pos ⟨(GlobalTheory.SchrMove.isHalf_actO_iff g 1 y).2 hc.1,
      Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isIntM_mul (isIntM_frG hg) hc.2.1,
      fun i j hj => inId_mul (isIntM_frG hg) (fun l => hc.2.2 l j hj) i⟩, rightBlock_mul]
    exact unitChar_mul ν hee hK (isUnitDet_frG he hg) (isUnitDet_frG he hg') _
  · rw [if_neg hc, if_neg, mul_zero]
    rintro ⟨h1, h2, h3⟩
    refine hc ⟨(GlobalTheory.SchrMove.isHalf_actO_iff g 1 y).1 h1, ?_, fun i j hj => ?_⟩
    · rw [hback]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isIntM_mul (isIntM_frG hg') h2
    · rw [hback]; exact inId_mul (isIntM_frG hg') (fun l => h3 l j hj) i

theorem keeps_latHat {S : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {β : GL (Fin S.rank) (Lev.EAf D)}
    (hβ : IsFrame β Λ) {g : Formalism.L2.Theta.GA D S} (hg : Lev.finE S g ∈ St β) (y) :
    y ∈ latHat D.host.F D.host.E (Λ : Set (Fin S.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt S g).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (Λ : Set (Fin S.rank → D.host.E)) := by
  rw [GlobalTheory.LevSplit.latHat_iff, GlobalTheory.LevSplit.latHat_iff, GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.mulVec_mem_hatL_iff hβ hg]
  refine iff_of_eq (congrArg (· ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) (funext fun i => ?_))
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rfl

theorem prod_detIdl {e : Formalism.L2.Theta.AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hP : ∀ w ∈ P, Formalism.L2.NTheta.IsIdemAt (idemAt w) w) (S : HSp D) (g : Formalism.L2.Theta.GA D S) :
    ∏ w ∈ P, detIdl (idemAt w) S g = detIdl e S g := by
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  obtain ⟨⟨es, hes, hs⟩, -⟩ := he
  have hs' : e = ∑ w ∈ P, idemAt w := hs.trans (Finset.sum_congr rfl fun w hw =>
    (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ w w (hes w hw) (hP w hw)).1 rfl)
  refine Units.ext ?_
  rw [Units.coe_prod, detIdl_val hee, Finset.prod_congr rfl fun w hw => detIdl_val (hP w hw).1.1 S g, hs']
  exact prod_idem _ _ P fun a ha b hb hab => (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ a b (hP a ha) (hP b hb)).2 hab

theorem detIdl_one (e : Formalism.L2.Theta.AE D) (S : HSp D) : detIdl e S 1 = 1 := by
  by_cases hee : e * e = e
  · refine Units.ext ?_
    rw [detIdl_val hee, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.mt_one, Matrix.det_one, Units.val_one]
    ring
  · rw [detIdl, dif_neg hee]

theorem fix_of_unram {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {α β : T → ((Formalism.L2.Theta.AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S : T → Finset (Pl D.host.E)}
    (hX : X.Is ψ θ α β νH S) (s : T)
    (hu : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (∀ w ∈ S s, w.under (𝓞 D.host.F) ≠ v) →
      CharUnramAt D (α s) v ∧ CharUnramAt D (β s) v)
    {k : Formalism.L2.Theta.GA D A'} (hk : k ∈ Lev.levA A' (St X.rA'.β)) : X.ω' s (k, 1) (X.f' s) = X.f' s := by
  obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
  have hW : IsWeilDatumO ψ A' WW (α s) (α s / β s) (X.ω' s) := hX.weil' s
  have he := hX.idem s
  have hee : X.e s * X.e s = X.e s := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hP : ∀ w ∈ S s, Formalism.L2.NTheta.IsIdemAt (idemAt w) w := fun w hw => by
    obtain ⟨⟨es, hes, -⟩, -⟩ := he
    exact Classical.epsilon_spec (p := fun e : Formalism.L2.Theta.AE D => Formalism.L2.NTheta.IsIdemAt e w) ⟨es w, hes w hw⟩
  have h1 : Lev.finE WW 1 ∈ St X.rW.β := by rw [map_one]; exact one_mem _
  have hv := GlobalTheory.LatStabScalar.om_eq_prod_splitFac hW hX.rigA'.1 hX.rigW.1 (S s) hP (GlobalTheory.LevelPlaces.under_injOn he)
    (fun v hv => ⟨(hu v hv).1, by
      rw [div_eq_mul_inv]
      exact GlobalTheory.SeeSaw.WeilLines.charUnram_mul (hu v hv).1 (GlobalTheory.SeeSaw.WeilLines.charUnram_inv (hu v hv).2)⟩)
    k hk1 1 (one_mem _) (keeps_latHat hX.rigA'.2.1 hk2) (keeps_latHat hX.rigW.2.1 h1) X.vac' hX.isVac'.2.theta hX.isVac'.2.lat
  have hc : (∏ w ∈ S s, ((splitFacO (α s) (α s / β s) (detIdl (idemAt w) A' k) (detIdl (idemAt w) WW 1) : Circle) : ℂ)) =
      ((((α s / β s) (detIdl (X.e s) A' k))⁻¹ : Circle) : ℂ) := by
    rw [← prod_detIdl he hP, map_prod, ← Finset.prod_inv_distrib]
    rw [show ∀ f : Pl D.host.E → Circle, ((∏ w ∈ S s, f w : Circle) : ℂ) = ∏ w ∈ S s, (f w : ℂ) from
      fun f => map_prod Circle.coeHom f (S s)]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [splitFacO, detIdl_one, map_one, mul_one]
  rw [hc] at hv
  have key := GlobalTheory.SchrMove.smul_om_eq D ψ A' WW X.rA'.Λ X.rW.Λ _ _ _ hW hX.rigA'.1 hX.rigW.1 (cA D (X.e s))
    (by rw [← RingHom.map_mul, hee]) (GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum he)) k 1
    (GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D A' WW _ _ _ _ hX.rigA'.1 hX.rigW.1 hX.rigA'.2.1 hX.rigW.2.1 k 1 hk2 h1)
    X.vac' _ (X.f' s) _ _ hX.isVac'.2.theta (hX.snd s) (Circle.coe_ne_zero _) hv
    (stdSnd_actO _ he _ _ A' WW _ _ hk2)
  exact smul_right_injective _ (Circle.coe_ne_zero _) key

theorem charUnram_pow {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)} (h : CharUnramAt D χ v) (n : ℕ) :
    CharUnramAt D (χ ^ n) v := fun x a b c d => by
  rw [MonoidHom.pow_apply, h x a b c d, one_pow]

theorem unram_off {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (n : ℕ) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v) :
    CharUnramAt D (L.mu t (j + 1) * L.eta ^ n) v ∧ CharUnramAt D (G.ch.chi (D.R.m - i) * L.eta ^ n) v := by
  have hS : v ∉ G.pl.S0 := fun h => by
    have hw : G.pl.w v ∈ locPl G t := by
      unfold locPl
      exact Finset.mem_union_left _ (by unfold Places.W0; exact Finset.mem_image_of_mem _ h)
    exact hv _ hw (G.pl.under_w h)
  have hQ : ∀ w ∈ L.Q t, w.under (𝓞 D.host.F) ≠ v := fun w hw => hv w (by
    unfold locPl
    exact Finset.mem_union_right _ hw)
  have hη : CharUnramAt D L.eta v :=
    GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w _ => (GlobalTheory.LFun.unrAt_iff_of_chrEq hL.eta w).2 (L.C.isEta.unr w)
  have h1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  have hχ : CharUnramAt D (G.ch.chi (D.R.m - i)) v :=
    GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw =>
      (GlobalTheory.LFun.unrAt_iff_of_chrEq (G.ch.chi_eq _ h1 h2) w).2 (G.ch.unr _ h1 h2 w (by rwa [hw]))
  have hμ : CharUnramAt D (L.mu t (j + 1)) v := by
    refine GlobalTheory.SeeSaw.WeilLines.charUnram_mul (χ := L.mu0 ((j : ℕ) + 1)) (χ' := L.xi t)
      (GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun P hP => (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 j) P).2 ?_)
      (GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun P hP => (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) P).2 ?_)
    · refine (L.C.isMu0 j).unr P fun k hk => hS ?_
      have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
        rw [← hP]
        change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal
        rw [map_natCast]
        exact hk
      refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
      fin_cases k
      · exact Or.inl hk'
      · exact Or.inr (Or.inl hk')
    · by_contra hn
      rcases (hL.Q_ram t P).1 hn with hq | ⟨P', hq, hc⟩
      · exact hQ P hq hP
      · exact hQ P' hq ((GlobalTheory.BotTripleUnr.under_eq_of_isConjPl hc).trans hP)
  exact ⟨GlobalTheory.SeeSaw.WeilLines.charUnram_mul hμ (charUnram_pow hη n), GlobalTheory.SeeSaw.WeilLines.charUnram_mul hχ (charUnram_pow hη n)⟩

end GlobalTheory.BotFinLevel

theorem GlobalTheory.BotFinLevel.finLevel_fix : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (s : T), ∀ k ∈ Lev.levA A' (Formalism.L2.DIV.St X.rA'.β), X.ω' s (k, 1) (X.f' s) = X.f' s := by
  intro _ _ _ _ _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ _ T Lc μ₀ hμ G => ?_⟩⟩
  intro W _ i j A A' WW X hX s k hk
  exact GlobalTheory.BotFinLevel.fix_of_unram hX.is s (fun v hv => GlobalTheory.BotFinLevel.unram_off G hμ s i j _ hv) hk

end
