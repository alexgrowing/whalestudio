import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinEmbStd

variable {D : D7}

theorem eq_of_finHom (V : HSp D) {g g' : GA D V} (hg : g ∈ GfC V) (hg' : g' ∈ GfC V)
    (h : ∀ i j, GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g' : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j)) :
    g = g' := by
  refine GlobalTheory.UnitarySplit.ga_ext V ?_ ?_
  · rw [MonoidHom.mem_ker.1 hg, MonoidHom.mem_ker.1 hg']
  · exact Units.ext (Matrix.ext fun i j => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective (h i j))

theorem toFinE_inc (e : D.host.E) :
    GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D e) = algebraMap D.host.E _ e := by
  change GlobalTheory.LFun.toFinAd ℚ D.host.E (1 ⊗ₜ[ℚ] e) = _
  rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]

theorem finAdEquiv_inclR (e : D.host.E) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (inclR (F := D.host.F) (Af D.host.F) e) = algebraMap D.host.E _ e := by
  change GlobalTheory.LFun.toFinAd D.host.F D.host.E (1 ⊗ₜ[D.host.F] e) = _
  rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]

theorem toFinE_toAfE_symm (y : TensorProduct D.host.F (Af D.host.F) D.host.E) :
    GlobalTheory.BotFormula.toFinE D ((GlobalTheory.BotFormula.toAfE D).symm y) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E y := by
  simp [GlobalTheory.BotFormula.toAfE]

theorem finAdEquiv_finHom_rat (V : HSp D) (γ : GA D V) (u : GL (Fin V.rank) D.host.E)
    (hγ : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) u = matHom V γ) (i j : Fin V.rank) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V γ : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
      algebraMap D.host.E _ ((u : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j) := by
  have : ((finHom V γ : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j =
      inclR (F := D.host.F) (Af D.host.F) ((u : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j) := by
    change (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (((matHom V γ : GL _ _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) = _
    rw [← hγ]
    change (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (inclR (F := D.host.F) (AF D.host.F) ((u : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j)) = _
    simp [inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  rw [this, finAdEquiv_inclR]

theorem exists_std_of_GfC (V : HSp D) (hG : V.gram = 1) (g : GA D V) (hg : g ∈ GfC V) :
    ∃ x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, IsFinPt V g x := by
  let M : Matrix (Fin V.rank) (Fin V.rank) (TensorProduct D.host.F (Af D.host.F) D.host.E) := (finHom V g).val
  have hM : Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) M * M = 1 := by
    have h2 := GlobalTheory.UnitarySplit.finHom_mem V g
    change Formalism.UG.cT _ M * JR (Af D.host.F) V.gram * M = JR (Af D.host.F) V.gram at h2
    rw [hG, JR, Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h2
    exact h2
  have hu : Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) (M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom) *
      M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom = 1 := by
    refine GlobalTheory.DefU.ClassFin.unitary_map _ (sigR (Af D.host.F) D.sp.cm.sig) _ ?_ _ hM
    intro y
    apply (GlobalTheory.BotFormula.toAfE D).injective
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply, GlobalTheory.BotFormula.toAfE_sgA]
  let x0 : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D) := Formalism.UG.bc (GlobalTheory.BotFormula.toAfE D).symm.toRingHom (finHom V g)
  have hx0 : x0 ∈ Formalism.MainNotions.StandardLatticesGL3.GA D V.rank := by
    change Formalism.UG.cT _ (M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom) *
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map _ * (M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom) = _
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one]
    exact hu
  refine ⟨⟨x0, hx0⟩, hg, rfl, fun i j => ?_⟩
  exact (toFinE_toAfE_symm _).symm

theorem exists_GQ_of_rat (V : HSp D) (hG : V.gram = 1) (x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) (hxr : x ∈ ratG D V.rank)
    (g : GA D V) (hg : ∀ i j,
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
        GlobalTheory.BotFormula.toFinE D (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) _) i j)) :
    ∃ γ ∈ GQ V, finHom V γ = finHom V g := by
  rw [GlobalTheory.NormSum.ratG_eq_ratPts] at hxr
  obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hxr)
  let U : Matrix (Fin V.rank) (Fin V.rank) D.host.E := u.val
  have huV : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) U * V.gram * U = V.gram := by
    have h : Formalism.UG.cT (D.host.conj : D.host.E →+* D.host.E) U * 1 * U = 1 := hu
    have hc : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) U = Formalism.UG.cT (D.host.conj : D.host.E →+* D.host.E) U := by
      exact Matrix.ext fun i j => Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D _
    rw [hG, hc]; exact h
  have hcT : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (U.map (inclR (F := D.host.F) (AF D.host.F))) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) U).map (inclR (F := D.host.F) (AF D.host.F)) := by
    ext i j
    simp [Formalism.UG.cT, sigR, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have hmem : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) u ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (U.map (inclR (F := D.host.F) (AF D.host.F))) *
      JR (AF D.host.F) V.gram * U.map (inclR (F := D.host.F) (AF D.host.F)) = JR (AF D.host.F) V.gram
    rw [hcT, JR, ← Matrix.map_mul, ← Matrix.map_mul, huV]
  let γ : GA D V := ⟨Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) u, hmem⟩
  refine ⟨γ, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨u, huV, rfl⟩), ?_⟩
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
  rw [finAdEquiv_finHom_rat V γ u rfl i j, hg i j, ← toFinE_inc]
  congr 1
  rw [← hu']
  rfl

theorem exists_finEmb : ∀ {D : D7} (V : HSp D) (n : ℕ), V.gram = 1 → V.rank = n → ∃ ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V,
    (∀ x, IsFinPt V (ι x) x) ∧ Function.Injective ι ∧ ι.range = GfC V ∧
      ∀ x, (∃ γ ∈ GQ V, finHom V γ = finHom V (ι x)) ↔ x ∈ ratG D n := by
  intro D V n hG hr
  subst hr
  have key : ∀ (g : GA D V) (x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank), IsFinPt V g x ↔ g ∈ GfC V ∧ ∀ i j,
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
        GlobalTheory.BotFormula.toFinE D (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) _) i j) := by
    intro g x
    constructor
    · rintro ⟨h1, e, h2⟩
      exact ⟨h1, fun i j => by simpa using h2 i j⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, rfl, fun i j => by simpa using h2 i j⟩
  choose f hf using fun x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank => GlobalTheory.BotFormula.exists_isFinPt_of_gram_one V hG x rfl
  have uniq : ∀ g x, IsFinPt V g x → g = f x := by
    intro g x hg
    obtain ⟨g1, g2⟩ := (key g x).1 hg
    obtain ⟨f1, f2⟩ := (key _ x).1 (hf x)
    exact eq_of_finHom V g1 f1 fun i j => (g2 i j).trans (f2 i j).symm
  have hfx : ∀ x, ∀ i j, GlobalTheory.LFun.finAdEquiv D.host.F D.host.E
      (((finHom V (f x) : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
        GlobalTheory.BotFormula.toFinE D (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) _) i j) :=
    fun x => ((key _ x).1 (hf x)).2
  let ι : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank →* GA D V :=
    { toFun := f
      map_one' := (uniq 1 1 ((key 1 1).2 ⟨one_mem _, fun i j => by
          simp [Matrix.one_apply, apply_ite]; split_ifs <;> simp_all⟩)).symm
      map_mul' := fun x y => (uniq _ _ ((key _ _).2 ⟨mul_mem ((key _ x).1 (hf x)).1 ((key _ y).1 (hf y)).1, fun i j => by
          simp only [map_mul, Units.val_mul, Subgroup.coe_mul, Matrix.mul_apply, map_sum, hfx]⟩)).symm }
  refine ⟨ι, hf, ?_, ?_, ?_⟩
  · intro x y hxy
    change f x = f y at hxy
    apply Subtype.ext; apply Units.ext; ext i j
    apply (GlobalTheory.BotFormula.toFinE D).injective
    rw [← hfx x, ← hfx y, hxy]
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact ((key _ x).1 (hf x)).1
    · intro g hg
      obtain ⟨x, hx⟩ := exists_std_of_GfC V hG g hg
      exact ⟨x, (uniq g x hx).symm⟩
  · intro x
    constructor
    · rintro ⟨γ, hγ, he⟩
      change finHom V γ = finHom V (f x) at he
      obtain ⟨u, -, hu'⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
      rw [GlobalTheory.NormSum.mem_ratG]
      refine ⟨(u : Matrix (Fin V.rank) (Fin V.rank) D.host.E), ?_⟩
      refine Matrix.ext fun i j => ?_
      apply (GlobalTheory.BotFormula.toFinE D).injective
      rw [Matrix.map_apply, toFinE_inc, ← hfx x, ← he, finAdEquiv_finHom_rat V γ u hu' i j]
    · intro hxr
      exact exists_GQ_of_rat V hG x hxr (f x) (hfx x)

end GlobalTheory.FinEmbStd
