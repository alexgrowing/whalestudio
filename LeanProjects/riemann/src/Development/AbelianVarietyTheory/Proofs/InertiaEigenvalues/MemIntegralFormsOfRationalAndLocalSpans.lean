import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsLinearIndependentAdelicReadings
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries.SpanInt

variable {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ}

theorem rd_add (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f g : Rul C.d.Xo₂ C.d.c₂) :
    C.rd a (f + g) = C.rd a f + C.rd a g := by
  simp only [Cover.rd, map_add, smul_add]

theorem rd_smul (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (x : C.d.c₂.F) (f : Rul C.d.Xo₂ C.d.c₂) :
    C.rd a (x • f) = C.σ₂ x • C.rd a f := by
  simp only [Cover.rd, LinearMap.map_smulₛₗ, map_smul]
  exact smul_comm _ _ _

theorem rd_zero (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) : C.rd a 0 = 0 := by
  simp only [Cover.rd, map_zero, smul_zero]

theorem vAdd_nonneg {k : Type} [Field k] [NumberField k] (la : HeightOneSpectrum (𝓞 k)) {x : k} (hx0 : x ≠ 0)
    (hx : la.valuation k x ≤ 1) : 0 ≤ vAdd la x := by
  unfold vAdd
  have h2 : (la.valuation k) x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr hx
  rw [WithZero.log_one] at h3
  omega

theorem cuspSec_add (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {f g : Rul C.d.Xo₂ C.d.c₂}
    (hf : f ∈ C.cuspSec a n) (hg : g ∈ C.cuspSec a n) : f + g ∈ C.cuspSec a n :=
  ⟨add_mem hf.1 hg.1, by rw [map_add]; exact add_mem hf.2 hg.2⟩

theorem cuspSec_smul (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : C.d.c₂.F)
    {f : Rul C.d.Xo₂ C.d.c₂} (hf : f ∈ C.cuspSec a n) : x • f ∈ C.cuspSec a n :=
  ⟨Submodule.smul_mem _ x hf.1, by rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hf.2⟩

theorem cuspSec_zero (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : (0 : Rul C.d.Xo₂ C.d.c₂) ∈ C.cuspSec a n :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem exists_of_mem_span_ratForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    {φ : GA D (T.V j σ) → ℂ} (hφ : φ ∈ Submodule.span C.σ₂.range (C.ratForms a n)) :
    ∃ f ∈ C.cuspSec a n, C.rd a f = φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, cuspSec_zero C a n, rd_zero C a⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨g, hg, rfl⟩ := hy
    exact ⟨f + g, cuspSec_add C a n hf hg, rd_add C a f g⟩
  | smul s x _ hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨s, y, rfl⟩ := s
    exact ⟨y • f, cuspSec_smul C a n y hf, by rw [rd_smul]; rfl⟩

theorem exists_of_mem_span_intForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) {φ : GA D (T.V j σ) → ℂ}
    (hφ : φ ∈ Submodule.span (locRing C.σ₂ la) (C.intForms a n {la})) :
    ∃ f ∈ C.cuspSec a n, (∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v f) ∧ C.rd a f = φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, ⟨hf, hv⟩, rfl⟩ := hx
    exact ⟨f, hf, hv la rfl, rfl⟩
  | zero =>
    refine ⟨0, cuspSec_zero C a n, fun v hv => ?_, rd_zero C a⟩
    rw [(isVal_valSet la v hv).zero]
    exact le_top
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, hvf, rfl⟩ := hx
    obtain ⟨g, hg, hvg, rfl⟩ := hy
    exact ⟨f + g, cuspSec_add C a n hf hg,
      fun v hv => (le_min (hvf v hv) (hvg v hv)).trans ((isVal_valSet la v hv).add _ _), rd_add C a f g⟩
  | smul s x _ hx =>
    obtain ⟨f, hf, hvf, rfl⟩ := hx
    obtain ⟨s, y, hy, rfl⟩ := s
    refine ⟨y • f, cuspSec_smul C a n y hf, fun v hv => ?_, by rw [rd_smul]; rfl⟩
    by_cases h0 : y = 0
    · rw [h0, zero_smul, (isVal_valSet la v hv).zero]
      exact le_top
    · rw [(isVal_valSet la v hv).smul y f h0]
      exact add_nonneg (by exact_mod_cast vAdd_nonneg la h0 hy) (hvf v hv)

theorem eq_of_rd_eq (D : D7) (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : Formalism.L2.Pj.InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (C : Cover T j σ) (hC : C.IsUnif) (hcc : CUnit C.cc₂) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (ha : Dom a n) {f g : Rul C.d.Xo₂ C.d.c₂} (hf : f ∈ sec C.d.Xo₂ C.d.c₂ a n) (hg : g ∈ sec C.d.Xo₂ C.d.c₂ a n)
    (h : C.rd a f = C.rd a g) : f = g := by
  by_contra hne
  have hli : LinearIndependent C.d.c₂.F (fun _ : Fin 1 => f - g) :=
    LinearIndependent.of_subsingleton 0 (sub_ne_zero.2 hne)
  have h2 := GlobalTheory.CoverIndep.cover_rd_linearIndependent D T hT j hj σ hσ C hC hcc a n ha 1 (fun _ => f - g)
    (fun _ => sub_mem hf hg) hli
  have h3 : C.rd a (f - g) = 0 := by
    have e := rd_add C a (f - g) g
    rw [sub_add_cancel, h] at e
    calc C.rd a (f - g) = (C.rd a (f - g) + C.rd a g) - C.rd a g := by abel
      _ = 0 := by rw [← e, sub_self]
  exact h2.ne_zero 0 h3

theorem mem_intForms_of_spans : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → CUnit C.cc₂ → ∀ (wa : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom wa n → ∀ (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) (φ : GA D (T.V j σ) → ℂ), φ ∈ Submodule.span C.σ₂.range (C.ratForms wa n) → (∀ la ∈ S, φ ∈ Submodule.span (locRing C.σ₂ la) (C.intForms wa n {la})) → φ ∈ C.intForms wa n S := by
  intro D T hT j hj σ hσ C hC hcc wa n hn S φ hφ hS
  obtain ⟨f, hf, rfl⟩ := exists_of_mem_span_ratForms C wa n hφ
  refine ⟨f, ⟨hf, fun la hla => ?_⟩, rfl⟩
  obtain ⟨g, hg, hvg, hfg⟩ := exists_of_mem_span_intForms C wa n la (hS la hla)
  rw [eq_of_rd_eq D T hT j hj σ hσ C hC hcc wa n hn hf.1 hg.1 hfg.symm]
  exact hvg

end GlobalTheory.LevelSeries.SpanInt
