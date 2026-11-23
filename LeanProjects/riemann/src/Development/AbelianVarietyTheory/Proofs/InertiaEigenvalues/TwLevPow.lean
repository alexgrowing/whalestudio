import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTuplesOfLaws
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOneOfChrEq

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwLevPow

theorem val_pow {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (a : ℕ) (v) :
    (χ ^ a).val v = χ.val v ^ a :=
  GlobalTheory.ConjExt.locK_pow χ a v _

theorem twLev_pow : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    ∀ (χ : Formalism.L2.Host.HChar D.host.E) (xi : (AE D)ˣ →* Circle) (Q : Finset (Pl D.host.E)) (xiR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ),
      GlobalTheory.BigOn.Exp.TwConj.TwLev R χ xi Q xiR → ∀ a b : ℕ, (χ ^ a) ^ b = χ →
      GlobalTheory.BigOn.Exp.TwConj.TwLev R (χ ^ a) (xi ^ a) Q (fun PP => xiR PP ^ a) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC χ xi Q xiR h a b hab

  have hQ0 : ∀ PP, PP ∉ R.Q A.μ0 := fun PP hPP =>
    ((hC.lev.Q_ram A.μ0 PP).2 (Or.inl hPP)) (by rw [hC.lev.xi_base]; intro x _; rfl)
  refine
    { xi := GlobalTheory.ConjExt.chrEq_pow h.xi a
      xi_fin := ?_
      xi_triv := GlobalTheory.ConjExt.trivOn_pow h.xi_triv a
      xi_tame := fun v x h1 h2 => by
        rw [GlobalTheory.ConjExt.loc_pow, h.xi_tame v x h1 h2, one_pow]
      Q_pl := h.Q_pl
      Q_off := h.Q_off
      Q_de := h.Q_de
      Q_ram := fun PP => Iff.trans
        (not_congr ⟨fun hu => hab ▸ GlobalTheory.ConjExt.unrAt_pow hu b, fun hu => GlobalTheory.ConjExt.unrAt_pow hu a⟩) (h.Q_ram PP)
      xiR := fun PP hP c k u h1 h2 => by
        show (xiR PP ^ a) u = (χ ^ a).locK PP k
        rw [GlobalTheory.ConjExt.locK_pow, MonoidHom.pow_apply, h.xiR PP hP c k u h1 h2]
      roots := h.roots
      muVal := ?_
      half := h.half
      guard := h.guard }
  · obtain ⟨n, hn, ho⟩ := h.xi_fin
    refine ⟨n, hn, ?_⟩
    show (χ ^ a) ^ n = 1
    rw [← pow_mul, mul_comm, pow_mul, show χ ^ n = 1 from ho, one_pow]
  · intro i P hP
    obtain ⟨x, hx⟩ := h.muVal i P hP
    have hP0 : Bridge.SplitOff (R.pl P) ((R.Sb : Set (Pl D.host.E)) ∪ (R.Q A.μ0 : Set (Pl D.host.E))) := by
      refine ⟨hP.1, fun hm => ?_, fun Q' hQ' => ?_⟩
      · rcases hm with hm | hm
        · exact hP.2.1 (Or.inl hm)
        · exact hQ0 _ hm
      · rcases hQ' with hQ' | hQ'
        · exact hP.2.2 Q' (Or.inl hQ')
        · exact absurd hQ' (hQ0 _)
    obtain ⟨g, c0R, c0L, ht⟩ := hC.fam.tie
    have hy := hC.fam.muVal i A.μ0 P ((ht.ok A.μ0 P).2 hP0)
    rw [hC.lev.xi_base, mul_one] at hy
    set y : D.what₂.LLˣ := A.muVal i A.μ0 P
    refine ⟨y * (y⁻¹ * x) ^ a, ?_⟩
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mul, map_mul, map_pow, map_mul, Units.val_inv_eq_inv_val,
      map_inv₀, hx, hy, Formalism.L2.Host.HChar.val_mul, Formalism.L2.Host.HChar.val_mul, val_pow]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    rw [inv_mul_cancel_left₀ (Units.ne_zero _)]

end GlobalTheory.TwLevPow
