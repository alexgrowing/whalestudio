import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.MeromorphicOnOfWeak
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SWStdLtK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BaseKnownTheoremsE

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
open GlobalTheory.Cont
namespace PositivityTheory.SiegelWeilFormula.Khead
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n}
def basis2_k {B : Base F E} (h : _root_.UpperTheory.TP.W.GoodK σ B) : Module.Basis (Fin 2) F E :=
  have h2 : Module.finrank F E = 2 := h.cm.2.2.1
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  Module.finBasisOfFinrankEq F E h2
def mkSD_k {B : Base F E} {m : ℕ} {A : Spc F E m} {r s r' s' : ℕ} {χ : Chr F E} {κ : Type} [Fintype κ]
    {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ}
    {om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)} {S : UA σ A.J →* Module.End ℂ ((κ → AF F) → ℂ)}
    {l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} {b : GL (Fin n ⊕ Fin n) E} {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ}
    {μ : Measure (UA σ A.J)} {D : Set (UA σ A.J)} {Φ : (κ → AF F) → ℂ}
    (H : _root_.PositivityTheory.SiegelWeilFormula.Std_k (σ := σ) B A Y r s r' s' χ κ dd om S l b K a μ D Φ) : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ where
  B := B
  m := m
  n := n
  A := A
  Y := Y
  r := r
  s := s
  χ := χ
  κ := κ
  dd := dd
  om := om
  S := S
  l := l
  b := b
  K := K
  a := a
  μ := μ
  D := D
  bs := _root_.PositivityTheory.SiegelWeilFormula.Khead.basis2_k H.good
  ok := ⟨H.good, H.hm, H.hn, H.aniso, H.sign.imp (fun h => ⟨h.1, h.2.skew⟩) (fun h => ⟨h.1, h.2.herm⟩), H.hecke, H.res, H.dbl,
    H.frame, H.stdK, H.hgt, H.haar, H.dom⟩
theorem headOf_k : _root_.PositivityTheory.SiegelWeilFormula.HeadOf_k := by
  intro hBL hSec hStrong hMain F E _ _ _ _ _ σ B m n A Y r s r' s' χ κ _ dd om S l b K a μ D Φ H
  set d := _root_.PositivityTheory.SiegelWeilFormula.Khead.mkSD_k H with hd
  have hK : d.KFin Φ := ⟨H.sch, H.fin⟩
  have hY : Y.IsHerm σ B r' s' ∨ Y.IsSkew σ B r' s' := H.sign.elim (fun h => .inr h.2) (fun h => .inl h.2)
  obtain ⟨Ê, ⟨t, hsum, -⟩, hw⟩ := hBL F E σ B n Y r' s' H.good H.hn hY χ H.hecke m H.res b K a H.frame H.stdK H.hgt
    (s0 m n) (d.sec0 Φ) (hSec F E σ d Φ hK)
  intro x
  have hfl : ∀ z, (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 m n) * d.sec0 Φ y) = flat a (d.sec0 Φ) (s0 m n) z := fun z =>
    funext fun y => by
      simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, flat]
      rw [Real.coe_toNNReal _ (hgt_nonneg d.ok.hgt y)]
      rfl
  have Heisenberg₂ : ∀ z : ℂ, t < z.re → d.eis (d.sec0 Φ) (s0 m n) z x = Ê z x := fun z hz => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.eis]
    rw [hfl z]
    exact (hsum z hz x).tsum_eq
  have hmer := meromorphicOn_of_weak hw x
  have hext : IsExtAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (Ê · x) :=
    ⟨Set.univ, trivial, isRightDomain_univ, hmer, t, fun z hz => (Heisenberg₂ z hz).symm⟩
  have hEA : d.EisAll := fun Φ' hΦ' => hStrong F E σ d ⟨r', s', hY⟩ _ _ (hSec F E σ d Φ' hΦ')
  obtain ⟨H', hext', han, hval⟩ := hMain F E σ d H.hnm hEA Φ hK x
  have hev := hext'.eventuallyEq hext
  have hloc : Function.update (Ê · x) (s0 m n) (d.I Φ x) =ᶠ[𝓝 (s0 m n)] H' := by
    filter_upwards [eventually_nhdsWithin_iff.1 hev] with z hz
    by_cases e : z = s0 m n
    · subst e; rw [Function.update_self]; exact hval.symm
    · rw [Function.update_of_ne e]; exact (hz e).symm
  refine ⟨Function.update (Ê · x) (s0 m n) (d.I Φ x), fun z _ => (hmer z trivial).update _ _, ⟨max t (s0 m n).re, fun z hz => ?_⟩,
    han.congr hloc.symm, Function.update_self _ _ _⟩
  have hz1 : t < z.re := lt_of_le_of_lt (le_max_left _ _) hz
  have hz2 : z ≠ s0 m n := fun e => by subst e; exact lt_irrefl _ (lt_of_le_of_lt (le_max_right _ _) hz)
  rw [Function.update_of_ne hz2]
  exact hsum z hz1 x
end PositivityTheory.SiegelWeilFormula.Khead
end
end
