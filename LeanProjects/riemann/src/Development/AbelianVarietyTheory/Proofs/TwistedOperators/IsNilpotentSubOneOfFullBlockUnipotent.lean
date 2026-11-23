import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPartStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsLinearlyOnMultiplicityValuesPosDefStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCoefficientSpaceDualDiscreteSeriesModelPosStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplicityMapPrescribedValueDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinrankEqCardMulAndTraceEqZeroOfFreeValuesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOneOfFiniteOrderUnipotentReductionLargePrimeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOfFinOrderOfConjMemSelfDualLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDefiniteSelfDualOfBaseFramePosDefStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FreeMonoidAlgebraOfCharacterVanishesOffOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardMulFinrankSubgroupEigenspaceOfTraceVanishesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenericSeriesSquarefreeLabelsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodProjectorCoeffEqProdAtTwoTypePrimesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelsReadOnProductPrimeFieldGLStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeLevelIdempotentProductAndCentralProductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePrimeLargeAndOneModSixteenQDStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsOfLevelOnObjects
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UpperLeftBlockEqSubmatrixOfRankEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodTupleProjectorIsProjCentral
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamPSizesRecord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteSmoothIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AutomorphicArithmetic.ExponentialBounds.BadShareWin

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefLift GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification Polynomial
open scoped TensorProduct

namespace GlobalTheory.DefFree

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.BadShare in

theorem central_tens2 {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {a : G → ℂ} {b : G' → ℂ}
    (ha : ∀ x, conv a x = conv x a) (hb : ∀ x, conv b x = conv x b) (z : G × G' → ℂ) :
    conv (tens2 a b) z = conv z (tens2 a b) := by
  classical
  have key : ∀ {H : Type} [Group H] [Fintype H] {a : H → ℂ}, (∀ x, conv a x = conv x a) → ∀ u v, a (u * v) = a (v * u) := by
    intro H _ _ a ha u v
    have := congrFun (ha fun y => if y = v⁻¹ then 1 else 0) u
    simp only [conv, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      inv_inv] at this
    rw [← this, Finset.sum_eq_single (u * v)]
    · simp
    · intro y _ hy
      rw [if_neg]
      intro e
      exact hy (by rw [inv_mul_eq_iff_eq_mul] at e; rw [e, inv_mul_cancel_right])
    · simp
  funext x
  simp only [conv]
  refine Fintype.sum_equiv ((Equiv.inv _).trans (Equiv.mulRight x)) _ _ fun y => ?_
  simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulRight, tens2, _root_.mul_inv_rev, inv_inv, Prod.fst_mul,
    Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
  rw [key ha _ x.1, key hb _ x.2, mul_inv_cancel_left, mul_inv_cancel_left, mul_comm]

theorem finrank_multilinear {ι : Type} [Fintype ι] (N : ι → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]
    [∀ i, FiniteDimensional ℂ (N i)] : Module.finrank ℂ (MultilinearMap ℂ N ℂ) = ∏ i, Module.finrank ℂ (N i) := by
  classical
  rw [Module.finrank_eq_card_basis
    (Basis.multilinearMap (fun i => Module.finBasis ℂ (N i)) (Module.Basis.singleton Unit ℂ))]
  simp

theorem isNilpotent_sub_one_of_full_block_unipotent {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (h : r = n) {g : GL (Fin n) κ}
    (hg : g ∈ blockTri (blk2 r)) (hn : IsNilpotent ((upperLeftBlock hr g).val - 1)) : IsNilpotent (g.val - 1) := by
  subst h
  rw [upper_block_val_submatrix hr hg] at hn
  have e : (g : Matrix (Fin r) (Fin r) κ).submatrix (Fin.castLE hr) (Fin.castLE hr) = g := by
    ext i j; rfl
  rwa [e] at hn

variable {D : D7}

theorem eq_one_of_unipotent {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hU : IsDefUnimod D.sp.cm V.gram Λ) (hβ : IsFrame β Λ)
    (hr : L.r = V.rank) (PP : L.Pg) {p : ℕ} (hp : p.Prime) (hc : CharP (kP PP.1) p)
    (hbig : Module.finrank ℚ D.host.E * V.rank + 1 < p) (u : UR D.sp.cm V.gram) (x : UA D.sp.cm V.gram)
    (hu : conjIn D.sp.cm V.gram (x : GL (Fin V.rank) (EAf D)) u ∈ parLev D.sp.cm V.gram β L)
    (hn : IsNilpotent ((rTup β L (conjIn D.sp.cm V.gram (x : GL (Fin V.rank) (EAf D)) u) PP).val - 1)) : u = 1 := by
  have hfin := GlobalTheory.T.isOfFinOrder_of_conj_mem_selfDualLatticeStabilizer _ _ D.sp.cm _ _ Λ β hU hβ u x (parLev_St hu)
  obtain ⟨y, hy⟩ := parLev_St hu
  have hn' := isNilpotent_sub_one_of_full_block_unipotent L.hr hr (blockTri_blkOf_le _ _ (parLev_g hu PP.2)) hn
  rw [← hy, redFn_frGL] at hn'
  refine Subtype.ext (GlobalTheory.T.eq_one_of_finiteOrder_unipotentReduction_largePrime D.host.E (EAf D) (kP PP.1) _ (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) (resS D.host.F PP.1) p V.rank hp hc hbig u
    ((x : GL (Fin V.rank) (EAf D)) * β) y ((UR D.sp.cm V.gram).subtype.isOfFinOrder hfin) ?_ hn')
  rw [conjIn_apply] at hy
  have hy' : β * Formalism.UG.bc _ y * β⁻¹ = _ := hy
  rw [_root_.mul_inv_rev, show β⁻¹ * (x : GL (Fin V.rank) (EAf D))⁻¹ * Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) (u : GL (Fin V.rank) D.host.E) * ((x : GL (Fin V.rank) (EAf D)) * β) =
    β⁻¹ * ((x : GL (Fin V.rank) (EAf D))⁻¹ * Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) (u : GL (Fin V.rank) D.host.E) * x) * β by group, ← hy']
  group

theorem rTup_eq_one_of_fixed {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hU : IsDefUnimod D.sp.cm V.gram Λ) (hβ : IsFrame β Λ)
    (hr : L.r = V.rank) (PP : L.Pg) {p : ℕ} (hp : p.Prime) (hc : CharP (kP PP.1) p)
    (hbig : Module.finrank ℚ D.host.E * V.rank + 1 < p) (x κ : UA D.sp.cm V.gram)
    (hκ : (κ : GL (Fin V.rank) (EAf D)) ∈ parLev D.sp.cm V.gram β L)
    (hn : IsNilpotent ((rTup β L (κ : GL (Fin V.rank) (EAf D)) PP).val - 1))
    (hfix : (Quotient.mk'' (x * κ) : Cl D.sp.cm V.gram (lev D.sp.cm V.gram β (flag1L L))) = Quotient.mk'' x) :
    rTup β L (κ : GL (Fin V.rank) (EAf D)) = 1 := by
  obtain ⟨γ, hγ, k, hk, e⟩ := DoubleCoset.rel_iff.1 (Quotient.exact' hfix.symm)
  obtain ⟨u, hu, hu'⟩ := hγ
  have hk1 : (k : GL (Fin V.rank) (EAf D)) ∈ parLev D.sp.cm V.gram β L := hk.1
  have hk2 : rTup β L (k : GL (Fin V.rank) (EAf D)) = 1 := hk.2
  have e' : (x : GL (Fin V.rank) (EAf D)) * κ = γ * x * k := congrArg Subtype.val e
  have hu'' : Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) u = (γ : GL (Fin V.rank) (EAf D)) := hu'
  have e2 : conjIn D.sp.cm V.gram (x : GL (Fin V.rank) (EAf D)) ⟨u, hu⟩ = (κ : GL (Fin V.rank) (EAf D)) * (k : GL (Fin V.rank) (EAf D))⁻¹ := by
    rw [conjIn_apply, hu'', eq_mul_inv_iff_mul_eq, mul_assoc, mul_assoc, ← mul_assoc (γ : GL (Fin V.rank) (EAf D)), ← e', inv_mul_cancel_left]
  have e3 : rTup β L ((κ : GL (Fin V.rank) (EAf D)) * (k : GL (Fin V.rank) (EAf D))⁻¹) = rTup β L κ := by
    rw [rTup_mul hκ (inv_mem hk1), rTup_inv hk1, hk2, inv_one, mul_one]
  have h1 := eq_one_of_unipotent hU hβ hr PP hp hc hbig ⟨u, hu⟩ x (by rw [e2]; exact mul_mem hκ (inv_mem hk1))
    (by rw [e2, e3]; exact hn)
  rw [← e3, ← e2, h1, map_one, rTup_one]

theorem principal_count {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {β : GL (Fin V.rank) (EAf D)}
    {L : LevDat D.host.E ℂ V.rank} (hθ : IsInfFam θ) (hs : V.SigOK) (hd : V.IsDefinite) (hM : AllPlus M)
    (hχ : ∀ x, levFn β (flag1L L) x = 1) [Finite (Cl D.sp.cm V.gram (lev D.sp.cm V.gram β (flag1L L)))]
    (hΓ : ∀ c : Cl D.sp.cm V.gram (lev D.sp.cm V.gram β (flag1L L)), Gam c = ⊥) :
    FiniteDimensional ℂ (Mult θ M (levS V β (flag1L L)) (levChi V β (flag1L L))) ∧
      Module.finrank ℂ (Mult θ M (levS V β (flag1L L)) (levChi V β (flag1L L))) =
        Nat.card (Cl D.sp.cm V.gram (lev D.sp.cm V.gram β (flag1L L))) * ∏ τ, Module.finrank ℂ (M.H τ) ∧
      ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] MMap M), Function.Injective e →
        LinearMap.range e = Mult θ M (levS V β (flag1L L)) (levChi V β (flag1L L)) → ∀ (A : Module.End ℂ H) (κ : GA D V),
        (∀ x v h, e (A x) v h = e x v (h * κ)) →
        (∀ h, clsA V (lev D.sp.cm V.gram β (flag1L L)) (h * κ) ≠ clsA V (lev D.sp.cm V.gram β (flag1L L)) h) →
        LinearMap.trace ℂ H A = 0 := by
  have hfin := GlobalTheory.DefLift.AllPlus.finite_smooth_irreducible D V S M hM
  haveI : ∀ τ, FiniteDimensional ℂ (M.H τ) := fun τ => (hfin τ).1
  obtain ⟨c, pr, hc, hpr, hsurj⟩ := GlobalTheory.T.exists_coefficientSpace_dual_discreteSeriesModel_posDef D θ V S M hθ hM
  obtain ⟨a1, -, -, -, a5⟩ := GlobalTheory.T.unitaryGroup_adelicClasses_via_finiteAdelicPart D V
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.finrank_eq_card_mul_and_trace_eq_zero_of_free_values_alt (GA D V) _ (MMap M) _ (clsA V (lev D.sp.cm V.gram β (flag1L L))) (evAt M)
    (Mult θ M (levS V β (flag1L L)) (levChi V β (flag1L L)))
    (fun c => by
      obtain ⟨h, -, e⟩ := a1 (rep c)
      exact ⟨h, by rw [clsA, e, mk_rep]⟩)
    (fun T hT => by
      ext v h
      exact congrArg (fun f => f v) (hT h))
    (fun h h' e => by
      obtain ⟨γ, hγ, κ, hκ, k, hk, rfl⟩ := (a5 _ h h').1 e
      obtain ⟨φ, hφ⟩ := GlobalTheory.T.realPoint_acts_linearly_on_multiplicity_values_posDef D θ V S M hθ hM k hk
      refine ⟨φ, fun T hT => ?_⟩
      rw [hφ _ _ T hT]
      congr 1
      ext v
      have hT' := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).1 hT
      rw [evAt_apply, evAt_apply, hT'.lev v κ hκ, (hT'.aut v).left γ hγ, levChi, hχ, Units.val_one, one_mul])
    (GlobalTheory.T.exists_multiplicityMap_prescribed_value_definite D θ V S M c pr β L hθ hs hd hc hpr hsurj hχ hΓ)
  refine ⟨h1, ?_, fun H _ _ e he hr A κ hA hκ => h3 H e he hr A (fun h => h * κ) (fun x h => ?_) hκ⟩
  · rw [h2, finrank_multilinear]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => by rw [(hfin τ).2.1, finrank_top]
  · ext v
    exact hA x v h

section Record

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem posDef_last {i : Fin D.R.m} (hi : (i : ℕ) + 1 = D.R.m) : (Wc D i).IsPosDef := by
  show (D.sp.W ((i : ℕ) + 1)).IsPosDef
  rw [hi]
  exact factWmPosDef D.R D.host.F D.host.E D.sp

theorem rank_weight_component_eq (i : Fin D.R.m) : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2

theorem allPlus_last (h : HidaSetting R F) {i : Fin D.R.m} (hi : (i : ℕ) + 1 = D.R.m) : AllPlus (R.MW i (sg0 D A)) := by
  intro τ a
  rw [h.models.order i τ a, posDef_last hi (tauE D τ)]
  exact decide_eq_true a.2

theorem unimod_last (h : HidaSetting R F) {i : Fin D.R.m} (hi : (i : ℕ) + 1 = D.R.m) :
    IsDefUnimod D.sp.cm (Wc D i).gram (R.ΛW i) ∧ IsFrame (R.βW i) (R.ΛW i) := by
  obtain ⟨c, hc⟩ := h.lev.βW i
  exact ⟨GlobalTheory.T.isDefiniteSelfDual_of_baseFrame_posDef D _ _ _ _ (D.sp.W_sig _) (posDef_last hi) hc, hc.1⟩

theorem levFn_eq_one_chainMember_flags_trivial (i : Fin D.R.m) (x : GL (Fin (Wc D i).rank) (EAf D)) :
    levFn (R.βW i) (flag1L (R.datWp i R.triv)) x = 1 ∧ levFn (R.βW i) (flagL (R.datWp i R.triv)) x = 1 := by
  have h2 : levFn (R.βW i) (flagL (R.datWp i R.triv)) x = 1 := by
    have h1 : ext1 (flagL (R.datWp i R.triv)).P.H (flagL (R.datWp i R.triv)).P.chi
        (rTup (R.βW i) (flagL (R.datWp i R.triv)) x) = 1 := subgroupCharExtension_one_apply _ _
    unfold levFn
    rw [h1, one_mul]
    refine (congrArg₂ (· * ·) ?_ ?_).trans (one_mul 1)
    · exact Finset.prod_eq_one fun _ _ => Finset.prod_empty
    · exact Finset.prod_empty
  exact ⟨(levFn_flag1 x).trans h2, h2⟩

def UnipAt (R : RealDat D A Ks) (g : G0 R.Pg D.R.r) : Prop :=
  ∃ (k : Fin 2) (PP : R.Pg), CharP (kP PP.1) (D.host.g k) ∧ IsNilpotent ((g PP).val - 1)

theorem fixed_last (h : HidaSetting R F) (hbig : ∀ k, Module.finrank ℚ D.host.E * D.R.r + 1 < D.host.g k) {i : Fin D.R.m}
    (hi : (i : ℕ) + 1 = D.R.m) (x κ : UA D.sp.cm (Wc D i).gram)
    (hκ : (κ : GL (Fin (Wc D i).rank) (EAf D)) ∈ parLev D.sp.cm (Wc D i).gram (R.βW i) (R.datWp i R.triv))
    (hn : UnipAt R (rTup (R.βW i) (R.datWp i R.triv) (κ : GL (Fin (Wc D i).rank) (EAf D))))
    (hfix : clsOf R i (x * κ) = clsOf R i x) :
    rTup (R.βW i) (R.datWp i R.triv) (κ : GL (Fin (Wc D i).rank) (EAf D)) = 1 := by
  obtain ⟨k, PP, hc, hn⟩ := hn
  exact rTup_eq_one_of_fixed (L := R.datWp i R.triv) (unimod_last h hi).1 (unimod_last h hi).2 (rank_weight_component_eq i).symm PP
    (D.host.g_prime k) hc (by rw [rank_weight_component_eq]; exact hbig k) x κ hκ hn hfix

theorem unipAt_one (h : HidaSetting R F) : UnipAt R 1 := by
  obtain ⟨Φ, -, -, -, -, h3, -⟩ := GlobalTheory.T.levels_read_on_product_primeFieldGL D G Pl0 T A Ks R F h.grp false
  have := h3 1 (Or.inl fun v => by simp)
  rwa [map_one] at this

theorem unipAt_of_mem (h : HidaSetting R F) (b : Bool) {g : G} (hg : g ∈ (F.lvl b).P) : UnipAt R (R.eG g) := by
  obtain ⟨Φ, L₁, L₂, h1, -, h3, -⟩ := GlobalTheory.T.levels_read_on_product_primeFieldGL D G Pl0 T A Ks R F h.grp b
  exact h3 g (Or.inl fun v => GlobalTheory.BadShare.Basic.isNilpotent_of_isUp (((h1 g).1 hg).1 v).1)

theorem gam_last (h : HidaSetting R F) (hbig : ∀ k, Module.finrank ℚ D.host.E * D.R.r + 1 < D.host.g k) {i : Fin D.R.m}
    (hi : (i : ℕ) + 1 = D.R.m) (c : Cls R i) : Gam c = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
  obtain ⟨k, PP, hc, hn⟩ := unipAt_one h
  have h2 : rTup (R.βW i) (R.datWp i R.triv) (conjIn D.sp.cm (Wc D i).gram (rep c : UA D.sp.cm (Wc D i).gram) u) = 1 := hu.2
  exact eq_one_of_unipotent (L := R.datWp i R.triv) (unimod_last h hi).1 (unimod_last h hi).2 (rank_weight_component_eq i).symm PP
    (D.host.g_prime k) hc (by rw [rank_weight_component_eq]; exact hbig k) u (rep c) hu.1 (by rw [h2]; exact hn)

theorem principal_last (h : HidaSetting R F) (hbig : ∀ k, Module.finrank ℚ D.host.E * D.R.r + 1 < D.host.g k) {i : Fin D.R.m}
    (hi : (i : ℕ) + 1 = D.R.m) : PrincipalCount R i ∧ Module.finrank ℂ (R.HW i (sg0 D A)).H = dK R i ∧
      ∀ g : G, g ≠ 1 → UnipAt R (R.eG g) → LinearMap.trace ℂ _ (R.gW i (sg0 D A) g) = 0 := by
  have hM := allPlus_last h hi
  haveI hfin : Finite (Cls R i) := class_set_finite _ _ D.sp.cm ℂ _ _ _ _ _ (unimod_last h hi).1 (unimod_last h hi).2
  haveI : Finite (Cl D.sp.cm (Wc D i).gram (lev D.sp.cm (Wc D i).gram (R.βW i) (flag1L (R.datWp i R.triv)))) := hfin
  haveI hne : Nonempty (Cls R i) := ⟨clsOf R i 1⟩
  obtain ⟨h1, h2, h3⟩ := principal_count (θ := R.θ) (R.MW i (sg0 D A)) (β := R.βW i) (L := R.datWp i R.triv) h.models.inf
    (D.sp.W_sig _) (fun τ => Or.inl (posDef_last hi τ)) hM (fun x => (levFn_eq_one_chainMember_flags_trivial i x).1) (gam_last h hbig hi)
  have hfd := fun τ => (GlobalTheory.DefLift.AllPlus.finite_smooth_irreducible D _ _ _ hM τ).1
  have hρ : 1 ≤ dimRho R i := by
    refine Finset.prod_pos (f := fun ρ => Module.finrank ℂ ((R.MW i (sg0 D A)).H ρ)) fun τ _ => ?_
    haveI := hfd τ
    haveI := ((R.MW i (sg0 D A)).ds τ).2.1
    exact Module.finrank_pos
  have hK : dK R i = Nat.card (Cls R i) * dimRho R i := h2
  obtain ⟨e1, e2, -⟩ := h.models.HW i (sg0 D A)
  refine ⟨⟨hfin, hne, gam_last h hbig hi, hfd, hρ, h1, hK, ?_⟩, ?_, fun g hg hn => ?_⟩
  · rw [hK]; exact Nat.mul_pos Nat.card_pos hρ
  · rw [dK, ← e2, LinearMap.finrank_range_of_inj e1]
  · have hl := GlobalTheory.GeoActRoad.levelLiftsExist_gridVertexSpaces h.lev i (R.eG g)
    refine h3 _ _ e1 e2 _ hl.choose (fun x v y => ?_) fun y e => hg ?_
    · rw [h.models.gW]
      show actG0 _ _ _ _ _ y = _
      unfold actG0
      rw [dif_pos hl, levChi, (levFn_eq_one_chainMember_flags_trivial i _).2, Units.val_one, inv_one, one_mul]
    · have hk := hl.choose_spec
      have := fixed_last h hbig hi (finU _ y) (finU _ hl.choose) hk.2.1 (by rw [coe_finU, hk.2.2]; exact hn)
        (by rw [← map_mul]; exact e)
      rw [coe_finU, hk.2.2] at this
      exact R.eG.injective (this.trans (map_one _).symm)

theorem sign_at_base_place_eq_embedding (R : RealDat D A Ks) : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0

def chiB (F : Face D A) (b : Bool) : (F.lvl b).P →* ℂˣ := (Units.map (sg0 D A).toMonoidHom).comp (F.lvl b).ψ⁻¹

theorem allAt_eq (h : HidaSetting R F) (b : Bool) (i : Fin D.R.m) :
    allAt R F b i = (eig (R.gW i (sg0 D A)) (F.lvl b).P fun g => ((chiB F b g : ℂˣ) : ℂ)).map (R.HW i (sg0 D A)).e := by
  obtain ⟨e1, e2, -⟩ := h.models.HW i (sg0 D A)
  have key := fun U => GlobalTheory.LevelRowsObj.mem_mult_withP_iff (GlobalTheory.GeoActRoad.levelLiftsExist_gridVertexSpaces h.lev i) R.θ (R.MW i (sg0 D A))
    (levB R F b) U
  have hχ : ∀ (g : (F.lvl b).P) (hg : R.eG g ∈ (levB R F b).H), (levB R F b).chi ⟨R.eG g, hg⟩ = chiB F b g := by
    intro g hg
    show Units.map (sg0 D A).toMonoidHom ((F.lvl b).ψ⁻¹ ⟨R.eG.symm (R.eG g), hg⟩) = Units.map (sg0 D A).toMonoidHom ((F.lvl b).ψ⁻¹ g)
    congr 2
    exact Subtype.ext (R.eG.symm_apply_apply g)
  ext U
  constructor
  · intro hU
    obtain ⟨h1, h2⟩ := (key U).1 hU
    obtain ⟨x, rfl⟩ : U ∈ LinearMap.range (R.HW i (sg0 D A)).e := e2.ge h1
    refine ⟨x, mem_eig.2 fun g => e1 ?_, rfl⟩
    have hg : R.eG g ∈ (levB R F b).H := by
      show R.eG.symm (R.eG g) ∈ (F.lvl b).P
      rw [R.eG.symm_apply_apply]; exact g.2
    rw [h.models.gW, map_smul, ← hχ g hg]
    exact h2 ⟨_, hg⟩
  · rintro ⟨x, hx, rfl⟩
    refine (key _).2 ⟨e2.le (LinearMap.mem_range_self _ x), fun p => ?_⟩
    obtain ⟨p, hp⟩ := p
    obtain ⟨g, rfl⟩ := R.eG.surjective p
    have hg : g ∈ (F.lvl b).P := by
      have : R.eG.symm (R.eG g) ∈ (F.lvl b).P := hp
      rwa [R.eG.symm_apply_apply] at this
    have := congrArg (R.HW i (sg0 D A)).e (mem_eig.1 hx ⟨g, hg⟩)
    rw [h.models.gW, map_smul, ← hχ ⟨g, hg⟩ hp] at this
    exact this

theorem wat_eq (h : HidaSetting R F) (b : Bool) (i : Fin D.R.m) :
    R.Wat i (sg0 D A) (levB R F b) = ((eig (R.gW i (sg0 D A)) (F.lvl b).P fun g => ((chiB F b g : ℂˣ) : ℂ)) ⊓
      LinearMap.ker ((∑ g : G, RealDat.eC (A := A) (sg0 D A) g • R.gW i (sg0 D A) g) - LinearMap.id)).map
        (R.HW i (sg0 D A)).e := by
  obtain ⟨e1, -, -⟩ := h.models.HW i (sg0 D A)
  have key : ∀ x, (R.HW i (sg0 D A)).e ((∑ g : G, RealDat.eC (A := A) (sg0 D A) g • R.gW i (sg0 D A) g) x) =
      postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A)) ((R.HW i (sg0 D A)).e x) := by
    intro x
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h.models.gW i (sg0 D A)]
    ext v y
    simp [postOn, RealDat.eWf, gaL, LinearMap.sum_apply]
    rfl
  have e0 : R.Wat i (sg0 D A) (levB R F b) =
    allAt R F b i ⊓ LinearMap.ker (postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A)) - LinearMap.id) := rfl
  rw [e0, allAt_eq h]
  ext U
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, h2⟩
    refine ⟨x, ⟨hx, e1 ?_⟩, rfl⟩
    rw [LinearMap.sub_apply, map_sub, key, map_zero]
    exact h2
  · rintro ⟨x, ⟨hx, h2⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    have := congrArg (R.HW i (sg0 D A)).e (LinearMap.mem_ker.1 h2)
    rw [LinearMap.sub_apply, map_sub, key, map_zero] at this
    exact this

theorem d0_eq (h : HidaSetting R F) (b : Bool) (i : Fin D.R.m) :
    d0 R F b i = Module.finrank ℂ (eig (R.gW i (sg0 D A)) (F.lvl b).P fun g => ((chiB F b g : ℂˣ) : ℂ)) := by
  rw [d0, allAt_eq h]
  exact (Submodule.equivMapOfInjective _ (h.models.HW i (sg0 D A)).1 _).finrank_eq.symm

theorem dGood_eq (h : HidaSetting R F) (b : Bool) (i : Fin D.R.m) :
    dGood R F b i = Module.finrank ℂ ((eig (R.gW i (sg0 D A)) (F.lvl b).P fun g => ((chiB F b g : ℂˣ) : ℂ)) ⊓
      LinearMap.ker ((∑ g : G, RealDat.eC (A := A) (sg0 D A) g • R.gW i (sg0 D A) g) - LinearMap.id) : Submodule ℂ _) := by
  rw [dGood, wat_eq h]
  exact (Submodule.equivMapOfInjective _ (h.models.HW i (sg0 D A)).1 _).finrank_eq.symm

theorem free_last (h : HidaSetting R F) (hbig : ∀ k, Module.finrank ℚ D.host.E * D.R.r + 1 < D.host.g k) {i : Fin D.R.m}
    (hi : (i : ℕ) + 1 = D.R.m) (b : Bool) : ActsFreely R F b i ∧ FreeCount R F b i := by
  obtain ⟨hP, hdim, htr⟩ := principal_last h hbig hi
  have htr' : ∀ g ∈ (F.lvl b).P, g ≠ 1 → LinearMap.trace ℂ _ (R.gW i (sg0 D A) g) = 0 :=
    fun g hg h1 => htr g h1 (unipAt_of_mem h b hg)
  have h0 : Nat.card (F.lvl b).P * d0 R F b i = dK R i := by
    rw [d0_eq h, ← hdim]
    exact GlobalTheory.T.card_mul_finrank_subgroupEigenspace_of_trace_vanishes G _ _ _ _ htr'
  refine ⟨⟨fun u hu => ?_, fun x κ hκ e => ?_⟩, ?_, h0, ?_⟩
  · obtain ⟨κ, -, h2, h3⟩ := GlobalTheory.GeoActRoad.levelLiftsExist_gridVertexSpaces h.lev i u
    have h3' : rTup (R.βW i) (R.datWp i (levB R F b)) (finE (Wc D i) κ) = u := h3
    exact ⟨finE (Wc D i) κ, ⟨h2, h3'.symm ▸ hu⟩, h3'⟩
  · refine fixed_last h hbig hi x κ hκ.1 ?_ e
    have h1 : R.eG.symm (rTup (R.βW i) (R.datWp i R.triv) (κ : GL (Fin (Wc D i).rank) (EAf D))) ∈ (F.lvl b).P := hκ.2
    have := unipAt_of_mem h b h1
    exact (R.eG.apply_symm_apply _).subst (motive := UnipAt R) this
  · rw [← hdim]
    exact GlobalTheory.T.free_monoidAlgebra_of_character_vanishes_off_one _ _ (repB R F b i) fun g hg => htr' g g.2 fun e => hg (Subtype.ext e)
  · have := hP.2.2.2.2.2.2.2
    rw [← h0] at this
    exact Nat.pos_of_mul_pos_left this

end Record

theorem definiteFree : DefiniteFree := by
  intro D L hP G _ _ Pl0 T A Ks _ _ _ R F h i hi
  have hbig := fun k => (GlobalTheory.T.typePrime_large_and_one_mod_sixteen_q_d D L hP k).1
  exact ⟨(principal_last h hbig hi).1, free_last h hbig hi⟩

open Classical GlobalTheory.BadShare in

theorem definiteGoodShare (hG : GlobalTheory.Published.GreenCuspidal) : DefiniteGoodShare := by
  intro eps heps
  by_cases h1 : eps ≤ 1
  swap
  · exact ⟨0, fun D L _ he => absurd (by have := L.sc.eps_lt; linarith) h1⟩
  obtain ⟨x₀, hx₀⟩ := UpperTheory.Win.badShare_win eps 5 heps h1
  refine ⟨max (max x₀ (Real.exp 209)) 16, fun D L hP he hx hS hE G _ _ Pl0 T A Ks _ _ _ R F h i hi b => ?_⟩
  subst he
  have hnum := GlobalTheory.T.typePrime_large_and_one_mod_sixteen_q_d D L hP
  have hbig := fun k => (hnum k).1
  obtain ⟨hPC, hdim, htr⟩ := principal_last h hbig hi
  have hd0 := (free_last h hbig hi b).2.2.2
  have hsz := GlobalTheory.sizes_record_at L hS 5 le_rfl ((le_max_right _ _).trans hx)
  have hr : 0 < D.R.r := by have := (hsz 0).2.2.2.2.1; omega
  have hτ : ∀ k : Fin 2, ∃ τ : (ZMod (D.host.g k))[X] → GG (D.host.g k) D.R.r → ℂ, IsSeries τ ∧
      ∀ f ∈ sqSet (D.host.g k) D.R.r, ∀ x, (D.ntypes.eSer k f).coeff x = zc (τ f) x := by
    intro k
    obtain ⟨Lb, -, hLb⟩ := hE k
    obtain ⟨τ, h1, h2⟩ := GlobalTheory.T.exists_genericSeries_squarefreeLabels hG.green (D.host.g k) Lb D.R.r
      (le_trans (by norm_num) (hnum k).2.2.2.2.2.2.2.2) hr
    exact ⟨τ, h1, fun f hf x => by rw [hLb]; convert h2 f hf x⟩
  choose τ hτ1 hτ2 using hτ
  obtain ⟨Φ, L₁, L₂, l1, l2, l3, l4⟩ := GlobalTheory.T.levels_read_on_product_primeFieldGL D G Pl0 T A Ks R F h.grp b
  have hez := GlobalTheory.T.coeff_e0_eq_eGood_mul_eGood D τ (fun k f hf x => by convert hτ2 k f hf x)
  set c : GProd D → ℂ := tens2 (eGood (fun _ => τ 0) (D.nd.chiT 0)) (eGood (fun _ => τ 1) (D.nd.chiT 1)) with hc
  have hcΦ : ∀ g, c (Φ g) = RealDat.eC (A := A) (sg0 D A) g := by
    intro g
    let γ : G0g D.nd := fun kv => match kv with
      | ⟨0, v⟩ => (Φ g).1 v
      | ⟨1, v⟩ => (Φ g).2 v
    rw [RealDat.eC, sign_at_base_place_eq_embedding R, l4 g γ (fun _ => rfl) (fun _ => rfl), hez γ]
    rfl
  have p0 := eGood_isProj_central _ _ _ _ (fun _ : D.nd.PlG 0 => τ 0) (D.nd.chiT 0) fun _ => hτ1 0
  have p1 := eGood_isProj_central _ _ _ _ (fun _ : D.nd.PlG 1 => τ 1) (D.nd.chiT 1) fun _ => hτ1 1
  have hcc : conv c c = c := (Basic.isProj_tens2 p0.1 p1.1).1
  have hcz : ∀ a, conv c a = conv a c := central_tens2 p0.2 p1.2
  obtain ⟨r1, r2⟩ := GlobalTheory.T.range_levelIdempotentProduct_and_centralProduct _ _ _ _ _ G _ Φ L₁ L₂ (F.lvl b).P (fun g => ((chiB F b g : ℂˣ) : ℂ)) (R.gW i (sg0 D A)) c l1
    (fun g => by rw [← l2 g, ← sign_at_base_place_eq_embedding R]; rfl) hcc hcz
  haveI : Nontrivial (R.HW i (sg0 D A)).H := Module.finrank_pos_iff.1 (by rw [hdim]; exact hPC.2.2.2.2.2.2.2)
  have hcount : CountAt (M := (R.HW i (sg0 D A)).H) ((R.gW i (sg0 D A)).comp Φ.symm.toMonoidHom) 0 := by
    refine Basic.countAt_of_trace_eq_zero _ fun γ hγ hu => ?_
    obtain ⟨g, rfl⟩ := Φ.surjective γ
    have := htr g (fun e => hγ (by rw [e, map_one])) (l3 g hu)
    simpa using this
  have hx1 := L.sc.one_lt_alt
  have hre : L.sc.x ^ L.sc.eps ≤ (D.R.r : ℝ) := by
    have a1 : L.sc.x ^ L.sc.eps ≤ L.sc.x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have a2 := (hsz 0).2.1
    have a3 : D.R.f ≤ D.R.r := by
      have b1 : D.R.f ≤ D.R.k := D.R.f_le_k
      have := D.R.two_le_m
      unfold Ranks.r; omega
    have a4 : (D.R.f : ℝ) ≤ D.R.r := by exact_mod_cast a3
    rw [Real.rpow_two] at a1
    linarith
  obtain ⟨del, -, hdel, hsh⟩ := hx₀ L.sc.x (((le_max_left _ _).trans (le_max_left _ _)).trans hx) L.sc.ez
    L.sc.ez_le _ _ D.R.r D.R.m D.host.q D.host.d D.R.f
    (D.nd.PlG 0) (D.nd.PlG 1) (D.nd.card_PlG 0) (D.nd.card_PlG 1) (hnum 0).2 (hnum 1).2 (hsz 0).1 (hsz 1).1
    (by rw [Real.rpow_two]; exact (hsz 0).2.1) (hsz 0).2.2.1 (hsz 0).2.2.2.1 hre (hsz 0).2.2.2.2.2.1
    (UpperTheory.Win.fm_div_min_le L hP hS (((le_max_right _ _).trans (le_max_left _ _)).trans hx))
    L₁ L₂ (fun _ => τ 0) (fun _ => τ 1) (fun _ => hτ1 0) (fun _ => hτ1 1) (D.nd.chiT 0) (D.nd.chiT 1) _ _ hcount
  have hsum : ∑ g : G, c (Φ g) • R.gW i (sg0 D A) g = ∑ g : G, RealDat.eC (A := A) (sg0 D A) g • R.gW i (sg0 D A) g :=
    Finset.sum_congr rfl fun g _ => by rw [hcΦ g]
  rw [hsum] at r2
  rw [rk, rk, r1, r2, ← d0_eq h, ← dGood_eq h] at hsh
  have hd0' : (1 : ℝ) ≤ d0 R F b i := by exact_mod_cast hd0
  have hlt : Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) < 1 :=
    Real.exp_lt_one_iff.2 (neg_lt_zero.2 (Real.rpow_pos_of_pos (by linarith) _))
  exact ⟨le_trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith)) hsh, mul_pos (by linarith) (by linarith)⟩

theorem goodVectorsDefinite (hG : GlobalTheory.Published.GreenCuspidal) : GoodVectorsDefinite := ⟨definiteFree, definiteGoodShare hG⟩

end GlobalTheory.DefFree

end
