import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondAtOfFirstAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueCharPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralEntriesOfCarriesStandardLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DetIntegralUnitIdeleOfIntegralFinitePartStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharRoot

theorem sigR_sigR (D : D7) (w : Formalism.L2.Theta.AE D) :
    sigR (AF D.host.F) D.sp.cm.sig (sigR (AF D.host.F) D.sp.cm.sig w) = w := by
  have hσ : ∀ z : D.host.E, D.sp.cm.sig (D.sp.cm.sig z) = z := fun z => star_star z
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => simp [sigR, hσ]
  | add p q hp hq => rw [map_add, map_add, hp, hq]

theorem exists_idF_eq_mul_sigR (D : D7) (x : (Formalism.L2.Theta.AE D)ˣ) :
    ∃ t : (AF D.host.F)ˣ, ((idF D t : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = (x : Formalism.L2.Theta.AE D) * sigR (AF D.host.F) D.sp.cm.sig (x : Formalism.L2.Theta.AE D) := by
  have hσ : ∀ z : D.host.E, D.sp.cm.sig (D.sp.cm.sig z) = z := fun z => star_star z
  have htr : ∀ z : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = z + D.sp.cm.sig z := by
    intro z
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add, hσ, add_comm]
  obtain ⟨t, ht⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr
    (x * Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom x) (by
      rw [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_mul, sigR_sigR, mul_comm])
  refine ⟨t, ?_⟩
  convert congrArg Units.val ht using 1
  · rfl
  · rfl

theorem pow_eq_one_of_isDetRoot (D : D7) (V : HSp D) (g : GA D V) (x : (Formalism.L2.Theta.AE D)ˣ) (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (n : ℕ)
    (hn : 0 < n) (hbase : ∀ t, c (idF D t) ^ n = 1) (hcont : Continuous c) (hR : IsDetRoot V g x)
    (d : (Formalism.L2.Theta.AE D)ˣ) (hd : (d : Formalism.L2.Theta.AE D) = (Formalism.L2.Theta.mt V g).det)
    (hfu : Formalism.L2.Pj.FinUnit d) : ∃ N : ℕ, 0 < N ∧ c x ^ N = 1 := by
  obtain ⟨t, ht⟩ := exists_idF_eq_mul_sigR D x
  have hxx : x * x = d * idF D t := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ht, hd]
    unfold IsDetRoot at hR
    unfold Formalism.L2.Theta.mt
    nth_rewrite 1 [hR]
    ring
  obtain ⟨N, -, -, m, hm, hord⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hcont
  refine ⟨2 * (m * n), by positivity, ?_⟩
  rw [pow_mul, sq, ← map_mul, hxx, map_mul, mul_pow, pow_mul, hord _ hfu, one_pow, one_mul, mul_comm m n, pow_mul, hbase t,
    one_pow]

theorem infPart_det_of_mem_GfC : ∀ (D : D7) (V : HSp D) (g : GA D V), g ∈ GfC V →
    infPart D (Formalism.L2.Theta.mt V g).det = 1 := by
  intro D V g hg
  have h : infHom V g = 1 := hg
  have h2 := congrArg (fun z : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => Matrix.det z.1) h
  simp only [Units.val_one, Matrix.det_one] at h2
  rw [← h2]
  unfold infHom Formalism.L2.Theta.mt Formalism.UG.bc
  rw [RingHom.map_det]
  rfl

theorem finUnit_det_of_carries : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V) (k : GL (Fin n) (EF D)),
    g ∈ GfC V → finM V hn g = k.1 →
    Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat D.host.E n) (Formalism.L2.Col.stdLat D.host.E n) →
    ∃ d : (Formalism.L2.Theta.AE D)ˣ, (d : Formalism.L2.Theta.AE D) = (Formalism.L2.Theta.mt V g).det ∧ Formalism.L2.Pj.FinUnit d := by
  intro D V n hn g k hg hk hc
  obtain ⟨h1, h2⟩ := GlobalTheory.T.integral_entries_of_carries_standardLattice D.host.F D.host.E n k hc
  have hu : IsUnit (Formalism.L2.Theta.mt V g).det := by
    unfold Formalism.L2.Theta.mt
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  obtain ⟨f1, f2⟩ := GlobalTheory.T.det_integralUnitIdele_of_integral_finitePart D V n hn g k hk h1 h2 hu.unit hu.unit_spec
  refine ⟨hu.unit, hu.unit_spec, ?_, f1, f2⟩
  rw [hu.unit_spec]
  exact infPart_det_of_mem_GfC D V g hg

end GlobalTheory.CharRoot

theorem GlobalTheory.CharRoot.chr_xr_pow_eq_one : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ j, j < B.R.m → ∀ i, i ≤ B.R.m → ∀ β, ∃ n : ℕ, 0 < n ∧ A.chr (j + 1) (A.xr i β) ^ n = 1 := by
  intro B X I hI hP l Z u a Ch₀ A hA j hj i hi β
  have hc : ChrEq (A.chr (j + 1)) (I.C.mu0 ⟨j, hj⟩ * I.xi a) := hA.chr ⟨j, hj⟩
  obtain ⟨hG, hF, hR⟩ := hA.kA i hi β
  have hb := hA.base i hi β

  obtain ⟨n, hn, hξ⟩ : ∃ n : ℕ, 0 < n ∧ I.xi a ^ n = 1 := by
    have hx := hI.xi_reads a
    have ht : IsOfFinOrder (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) := (I.tup a).2.1.1.1.2
    obtain ⟨n, hn, hpow⟩ := ht.exists_pow_eq_one
    refine ⟨n, hn, ?_⟩
    apply Subtype.ext
    ext y
    have h1 := hx y
    simp only [SubgroupClass.coe_pow, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, OneMemClass.coe_one, MonoidHom.one_apply, Units.val_one]
    rw [h1, ← map_pow, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hpow]
    simp

  have hpow : ∀ k : ℕ, ChrEq (A.chr (j + 1) ^ (k + 1)) ((I.C.mu0 ⟨j, hj⟩ * I.xi a) ^ (k + 1)) := by
    intro k
    induction k with
    | zero => simpa using hc
    | succ k ih =>
      rw [pow_succ (A.chr (j + 1)) (k + 1), pow_succ _ (k + 1)]
      exact GlobalTheory.AdelicLiftCompare.chrEq_mul ih hc
  have hbase : ∀ t, A.chr (j + 1) (idF (I.rec7 l Z) t) ^ n = 1 := by
    intro t
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h1 := hpow k
    rw [mul_pow, hξ, mul_one] at h1
    have h2 := GlobalTheory.GridWeil.triv_base h1 (PsiExist.trivOn_pow (I.C.isMu0 ⟨j, hj⟩).triv (k + 1)) t
    simpa using h2

  have hcar : Formalism.L2.Herm.Carries (A.kb i β) (Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) (Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) := by
    obtain ⟨h1, h2⟩ := hb
    have h := h1.lat
    erw [h2] at h
    exact h
  obtain ⟨d, hd, hfu⟩ := GlobalTheory.CharRoot.finUnit_det_of_carries (I.rec7 l Z) _ _ _ (A.kA i β) (A.kb i β) hG hF hcar
  exact GlobalTheory.CharRoot.pow_eq_one_of_isDetRoot (I.rec7 l Z) _ (A.kA i β) (A.xr i β) (A.chr (j + 1)) n hn hbase hc.1.1 hR d hd hfu
