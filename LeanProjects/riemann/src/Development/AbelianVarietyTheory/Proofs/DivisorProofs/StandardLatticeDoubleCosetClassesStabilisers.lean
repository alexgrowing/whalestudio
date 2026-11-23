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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open scoped TensorProduct
namespace GlobalTheory.BotClassDict

theorem transport {G H : Type} [Group G] [Group H] (π : G →* H) (Γ J : Subgroup G) (Δ K : Subgroup H)
    (hJ : ∀ g, g ∈ J ↔ π g ∈ K) (hmap : ∀ γ ∈ Γ, π γ ∈ Δ) (hsurj : ∀ δ ∈ Δ, ∃ γ ∈ Γ, π γ = δ)
    (hinj : ∀ γ ∈ Γ, ∀ γ' ∈ Γ, π γ = π γ' → γ = γ')
    (gx : DoubleCoset.Quotient (Δ : Set H) (K : Set H) → G) (hgx : ∀ x, π (gx x) = x.out) :
    (∀ g : G, ∃! x, ∃ γ ∈ Γ, ∃ k ∈ J, g = γ * gx x * k) ∧
      ∀ x, {γ : G | γ ∈ Γ ∧ (gx x)⁻¹ * γ * gx x ∈ J}.ncard =
        Nat.card {γ : H // γ ∈ Δ ∧ (x.out)⁻¹ * γ * x.out ∈ K} := by
  refine ⟨fun g => ⟨DoubleCoset.mk Δ K (π g), ?_, ?_⟩, fun x => ?_⟩
  · obtain ⟨δ, k, hδ, hk, e⟩ := DoubleCoset.mk_out_eq_mul Δ K (π g)
    obtain ⟨γ, hγ, rfl⟩ := hsurj δ hδ
    refine ⟨γ⁻¹, inv_mem hγ, (gx (DoubleCoset.mk Δ K (π g)))⁻¹ * γ * g, (hJ _).2 ?_, by group⟩
    rw [map_mul, map_mul, map_inv, hgx, e]
    have : (π γ * π g * k)⁻¹ * π γ * π g = k⁻¹ := by group
    rw [this]
    exact inv_mem hk
  · rintro x ⟨γ, hγ, k, hk, e⟩
    rw [← DoubleCoset.out_eq' _ _ x, DoubleCoset.eq]
    refine ⟨π γ, hmap γ hγ, π k, (hJ k).1 hk, ?_⟩
    rw [e, map_mul, map_mul, hgx]
  · rw [← Nat.card_coe_set_eq]
    refine Nat.card_eq_of_bijective (fun γ => ⟨π γ.1, hmap _ γ.2.1, ?_⟩) ⟨?_, ?_⟩
    · have := (hJ _).1 γ.2.2
      rwa [map_mul, map_mul, map_inv, hgx] at this
    · intro a b hab
      exact Subtype.ext (hinj _ a.2.1 _ b.2.1 (congrArg Subtype.val hab))
    · rintro ⟨δ, hδ, hk⟩
      obtain ⟨γ, hγ, rfl⟩ := hsurj δ hδ
      refine ⟨⟨γ, hγ, (hJ _).2 ?_⟩, rfl⟩
      rwa [map_mul, map_mul, map_inv, hgx]

open GlobalTheory.BotFormula

variable {D : D7}

def finT (D : D7) : AF D.host.F ⊗[D.host.F] D.host.E →+* Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

def finQ (D : D7) : AF D.host.F ⊗[D.host.F] D.host.E →+* Formalism.MainNotions.StandardLatticesGL3.AE D :=
  (toAfE D).symm.toRingHom.comp (finT D)

theorem toAfE_finQ (y : AF D.host.F ⊗[D.host.F] D.host.E) : toAfE D (finQ D y) = finT D y :=
  (toAfE D).apply_symm_apply _

theorem finT_sigR (y : AF D.host.F ⊗[D.host.F] D.host.E) :
    finT D (sigR (AF D.host.F) D.sp.cm.sig y) = sigR (Af D.host.F) D.sp.cm.sig (finT D y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul x a => rfl

theorem finQ_sigR (y : AF D.host.F ⊗[D.host.F] D.host.E) :
    finQ D (sigR (AF D.host.F) D.sp.cm.sig y) = Formalism.MainNotions.StandardLatticesGL3.sgA D (finQ D y) := by
  apply (toAfE D).injective
  rw [toAfE_sgA, toAfE_finQ, toAfE_finQ, finT_sigR]

theorem toFinE_tmul (x : D.host.E) (a : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    toFinE D (x ⊗ₜ[ℚ] a) = algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E a :=
  (GlobalTheory.LFun.toFinAd_tmul a x).trans (mul_comm _ _)

theorem finAdEquiv_toAfE (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (toAfE D y) = toFinE D y :=
  (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).apply_symm_apply _

theorem finQ_inclR (e : D.host.E) : finQ D (inclR (F := D.host.F) (AF D.host.F) e) = inc D e := by
  apply (toAfE D).injective
  apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
  rw [toAfE_finQ, finAdEquiv_toAfE]
  have h1 : toFinE D (inc D e) = algebraMap D.host.E _ e * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E 1 := toFinE_tmul e 1
  have h2 : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finT D (inclR (F := D.host.F) (AF D.host.F) e)) =
      GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E 1 * algebraMap D.host.E _ e := GlobalTheory.LFun.toFinAd_tmul 1 e
  rw [h1, h2, map_one, map_one, one_mul, mul_one]

theorem toAfE_int_iff (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    Lev.swapAE D (toAfE D y) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ y ∈ OhE D := by
  let c := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv
  have h : ∀ x a, ((GlobalTheory.LFun.toFinAd D.host.F D.host.E).comp c.symm.toRingHom) (x ⊗ₜ[D.host.F] a) =
      algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E a :=
    fun x a => (GlobalTheory.LFun.toFinAd_tmul a x).trans (mul_comm _ _)
  have h' : ∀ x a, (toFinE D).toRingHom (x ⊗ₜ[ℚ] a) =
      algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E a := toFinE_tmul
  have e : ((GlobalTheory.LFun.toFinAd D.host.F D.host.E).comp c.symm.toRingHom) (Lev.swapAE D (toAfE D y)) =
      (toFinE D).toRingHom y := by
    change GlobalTheory.LFun.toFinAd D.host.F D.host.E (c.symm (c (toAfE D y))) = _
    rw [c.symm_apply_apply]
    exact finAdEquiv_toAfE y
  constructor
  · intro hy
    have := GlobalTheory.AdeleBaseChange.map_mem_int h hy
    rw [e] at this
    exact GlobalTheory.AdeleBaseChange.mem_int_of_map h' this
  · intro hy
    have := GlobalTheory.AdeleBaseChange.map_mem_int h' hy
    rw [← e] at this
    exact GlobalTheory.AdeleBaseChange.mem_int_of_map h this

theorem finQ_mem (V : HSp D) (hG : V.gram = 1) (g : Formalism.L2.Theta.GA D V) :
    Formalism.UG.bc (finQ D) (matHom V g) ∈ Formalism.MainNotions.StandardLatticesGL3.GA D V.rank := by
  have hg : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (matHom V g).1 * JR (AF D.host.F) V.gram * (matHom V g).1 =
      JR (AF D.host.F) V.gram := g.2
  have hJ : JR (F := D.host.F) (AF D.host.F) V.gram = 1 := by rw [hG, JR, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hJ, mul_one] at hg
  change Formalism.UG.cT _ (Formalism.UG.bc (finQ D) (matHom V g)).1 * _ * _ = _
  rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one]
  exact GlobalTheory.DefU.ClassFin.unitary_map (finQ D) _ (Formalism.MainNotions.StandardLatticesGL3.sgA D) finQ_sigR _ hg

def finStd (V : HSp D) (hG : V.gram = 1) : Formalism.L2.Theta.GA D V →* Formalism.MainNotions.StandardLatticesGL3.GA D V.rank :=
  ((Formalism.UG.bc (finQ D)).comp (matHom V)).codRestrict _ (finQ_mem V hG)

theorem finStd_apply (V : HSp D) (hG : V.gram = 1) (g : Formalism.L2.Theta.GA D V) (i j : Fin V.rank) :
    (finStd V hG g).1.1 i j = finQ D ((matHom V g).1 i j) := rfl

theorem toAfE_finStd (V : HSp D) (hG : V.gram = 1) (g : Formalism.L2.Theta.GA D V) (i j : Fin V.rank) :
    toAfE D ((finStd V hG g).1.1 i j) = (finHom V g).1 i j := toAfE_finQ _

theorem finStd_of_isFinPt (V : HSp D) (hG : V.gram = 1) {g : Formalism.L2.Theta.GA D V} {h : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank}
    (hg : IsFinPt V g h) : finStd V hG g = h := by
  obtain ⟨-, e, he⟩ := hg
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  apply (toFinE D).injective
  rw [← finAdEquiv_toAfE, toAfE_finStd]
  exact he i j

theorem finStd_mem_ratG (V : HSp D) (hG : V.gram = 1) {γ : Formalism.L2.Theta.GA D V} (hγ : γ ∈ GQ V) :
    finStd V hG γ ∈ GlobalTheory.NormSum.ratG D V.rank := by
  obtain ⟨z, -, e⟩ := hγ
  refine (GlobalTheory.NormSum.mem_ratG _).2 ⟨z.1, Matrix.ext fun i j => ?_⟩
  have e' : matHom V γ = Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) z := e.symm
  rw [finStd_apply, e']
  exact finQ_inclR _

theorem finStd_injOn (V : HSp D) (hG : V.gram = 1) {γ γ' : Formalism.L2.Theta.GA D V} (hγ : γ ∈ GQ V) (hγ' : γ' ∈ GQ V)
    (h : finStd V hG γ = finStd V hG γ') : γ = γ' := by
  obtain ⟨z, -, e⟩ := hγ
  obtain ⟨z', -, e'⟩ := hγ'
  have e1 : matHom V γ = Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) z := e.symm
  have e2 : matHom V γ' = Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) z' := e'.symm
  have hz : z = z' := by
    refine Units.ext (Matrix.ext fun i j => GlobalTheory.NormSum.inc_inj D ?_)
    have h1 : (finStd V hG γ).1.1 i j = (finStd V hG γ').1.1 i j := by rw [h]
    rw [finStd_apply, finStd_apply, e1, e2] at h1
    exact (finQ_inclR _).symm.trans (h1.trans (finQ_inclR _))
  exact Subtype.ext (e1.trans (hz ▸ e2.symm))

theorem exists_rat_lift (V : HSp D) (hG : V.gram = 1) {δ : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank} (hδ : δ ∈ GlobalTheory.NormSum.ratG D V.rank) :
    ∃ γ ∈ GQ V, finStd V hG γ = δ := by
  rw [GlobalTheory.NormSum.ratG_eq_ratPts] at hδ
  obtain ⟨u, hu, e⟩ := hδ
  have hu1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u.1 * u.1 = 1 := by
    have hs : (D.sp.cm.sig : D.host.E →+* D.host.E) = ((D.host.conj : D.host.E →ₐ[ℚ] D.host.E) : D.host.E →+* D.host.E) :=
      RingHom.ext fun x => Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D x
    have h2 : Formalism.UG.cT ((D.host.conj : D.host.E →ₐ[ℚ] D.host.E) : D.host.E →+* D.host.E) u.1 * 1 * u.1 = 1 := hu
    rw [hs, ← h2, mul_one]
  have hu2 : u ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
    change Formalism.UG.cT _ u.1 * V.gram * u.1 = V.gram
    rw [hG, mul_one, hu1]
  have hu3 : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) u ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    change Formalism.UG.cT _ (Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) u).1 * JR (F := D.host.F) (AF D.host.F) V.gram * _ =
      JR (F := D.host.F) (AF D.host.F) V.gram
    have hJ : JR (F := D.host.F) (AF D.host.F) V.gram = 1 := by rw [hG, JR, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hJ, mul_one]
    exact GlobalTheory.DefU.ClassFin.unitary_map (inclR (F := D.host.F) (AF D.host.F)) _ (sigR (AF D.host.F) D.sp.cm.sig)
      (fun y => rfl) _ hu1
  refine ⟨⟨_, hu3⟩, ⟨u, hu2, rfl⟩, Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))⟩
  have e' : δ.1 = Formalism.UG.bc (inc D) u := e.symm
  rw [e']
  exact finQ_inclR _

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_range_intGL (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    x ∈ (Formalism.L2.DIV.intGL F E n).range ↔
      ∀ i j, x.1 i j ∈ Formalism.L2.Herm.intAf F E ∧ (x⁻¹).1 i j ∈ Formalism.L2.Herm.intAf F E := by
  constructor
  · rintro ⟨y, rfl⟩ i j
    refine ⟨(y.1 i j).2, ?_⟩
    rw [← map_inv]
    exact ((y⁻¹).1 i j).2
  · intro h
    have hinj : Function.Injective fun M : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) =>
      M.map (Formalism.L2.Herm.intAf F E).subtype := Matrix.map_injective Subtype.val_injective
    let a : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := Matrix.of fun i j => ⟨x.1 i j, (h i j).1⟩
    let b : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := Matrix.of fun i j => ⟨(x⁻¹).1 i j, (h i j).2⟩
    have ha : a.map (Formalism.L2.Herm.intAf F E).subtype = x.1 := rfl
    have hb : b.map (Formalism.L2.Herm.intAf F E).subtype = (x⁻¹).1 := rfl
    have hab : a * b = 1 := by
      apply hinj
      dsimp only
      rw [Matrix.map_mul, ha, hb, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have hba : b * a = 1 := by
      apply hinj
      dsimp only
      rw [Matrix.map_mul, ha, hb, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact ⟨⟨a, b, hab, hba⟩, Units.ext ha⟩

theorem frame_mem_range {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hβ : Formalism.L2.DIV.IsFrame β (Formalism.L2.Col.stdLat E n)) :
    β ∈ (Formalism.L2.DIV.intGL F E n).range := by
  letI : StarRing E := starRingOfComm
  have hm : ∀ z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F,
      z ∈ Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E n) ↔ ∀ i, z i ∈ Formalism.L2.Herm.intAf F E :=
    fun z => Formalism.L2.Col.mem_latS_std z
  have hs : ∀ i j : Fin n, (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) i ∈ Formalism.L2.Herm.intAf F E := by
    intro i j
    by_cases h : i = j
    · subst h
      rw [Pi.single_eq_same]
      exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne h]
      exact Subring.zero_mem _
  refine (mem_range_intGL β).2 fun i j => ⟨?_, ?_⟩
  · have h1 : Matrix.mulVec β.1 (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈
        Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E n) := by
      refine (hβ _).2 fun l => ?_
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      exact hs l j
    have h2 := (hm _).1 h1 i
    rwa [Matrix.mulVec_single_one] at h2
  · have h2 := (hβ _).1 ((hm _).2 fun l => hs l j) i
    rwa [Matrix.mulVec_single_one] at h2

theorem mem_St_iff {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hβ : Formalism.L2.DIV.IsFrame β (Formalism.L2.Col.stdLat E n))
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    x ∈ Formalism.L2.DIV.St β ↔ ∀ i j, x.1 i j ∈ Formalism.L2.Herm.intAf F E ∧ (x⁻¹).1 i j ∈ Formalism.L2.Herm.intAf F E := by
  have hb := frame_mem_range hβ
  rw [← mem_range_intGL]
  constructor
  · rintro ⟨y, rfl⟩
    exact mul_mem (mul_mem hb ⟨y, rfl⟩) (inv_mem hb)
  · intro hx
    obtain ⟨y, hy⟩ := mul_mem (mul_mem (inv_mem hb) hx) hb
    refine ⟨y, ?_⟩
    change β * Formalism.L2.DIV.intGL F E n y * β⁻¹ = x
    rw [hy]
    group

end Frame

theorem mem_level_iff (V : HSp D) (hG : V.gram = 1) {β : GL (Fin V.rank) (Lev.EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β (Formalism.L2.Col.stdLat D.host.E V.rank)) (g : Formalism.L2.Theta.GA D V) :
    g ∈ (Formalism.L2.DIV.St β).comap (Lev.finE V) ↔ finStd V hG g ∈ GlobalTheory.NormSum.intG D V.rank := by
  have key : ∀ (g : Formalism.L2.Theta.GA D V) i j, (Lev.finE V g).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      (finStd V hG g).1.1 i j ∈ OhE D := by
    intro g i j
    rw [← toAfE_int_iff, toAfE_finStd]
    rfl
  rw [Subgroup.mem_comap, mem_St_iff hβ, GlobalTheory.NormSum.mem_intG]
  refine forall_congr' fun i => forall_congr' fun j => and_congr (key g i j) ?_
  rw [← map_inv, ← Subgroup.coe_inv, ← map_inv]
  exact key g⁻¹ i j

theorem classes_and_stabilisers : ∀ {D : D7} (A' : HSp D) (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig A'), r.Is → r.IsStd → ∀ {n : ℕ}, n = A'.rank →
    ∀ gx : GlobalTheory.NormSum.Cls D n (GlobalTheory.NormSum.intG D n) → GA D A', (∀ x, GlobalTheory.BotFormula.IsFinPt A' (gx x) x.out) →
      (∀ g : GA D A', ∃! x, ∃ γ ∈ GQ A', ∃ k ∈ (Formalism.L2.DIV.St r.β).comap (Lev.finE A'), g = γ * gx x * k) ∧
      ∀ x, {γ : GA D A' | γ ∈ GQ A' ∧ (gx x)⁻¹ * γ * gx x ∈ (Formalism.L2.DIV.St r.β).comap (Lev.finE A')}.ncard =
        GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D n) x.out := by
  intro D A' r hr hs n hn gx hgx
  subst hn
  have hΛ : r.Λ = Formalism.L2.Col.stdLat D.host.E A'.rank := by
    ext y
    rw [hs.2.1 y]
    exact ⟨fun h i _ => Submodule.mem_one.2 (h i), fun h i => Submodule.mem_one.1 (h i trivial)⟩
  have hβ : Formalism.L2.DIV.IsFrame r.β (Formalism.L2.Col.stdLat D.host.E A'.rank) := hΛ ▸ hr.2.1
  exact transport (finStd A' hs.1) (GQ A') _ (GlobalTheory.NormSum.ratG D A'.rank) (GlobalTheory.NormSum.intG D A'.rank)
    (mem_level_iff A' hs.1 hβ) (fun γ hγ => finStd_mem_ratG A' hs.1 hγ) (fun δ hδ => exists_rat_lift A' hs.1 hδ)
    (fun γ hγ γ' hγ' h => finStd_injOn A' hs.1 hγ hγ' h) gx (fun x => finStd_of_isFinPt A' hs.1 (hgx x))

end GlobalTheory.BotClassDict
