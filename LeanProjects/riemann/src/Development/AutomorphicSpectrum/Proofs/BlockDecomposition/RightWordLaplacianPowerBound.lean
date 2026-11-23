import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusJointCurve
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevOperatorFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevIntegrationByParts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionNormBound

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.FcSmooth.WordBd

open GlobalTheory.CompanionTheory.CurveJ (sob_comb)
open GlobalTheory.CompanionTheory.SobOpsPf (sob_bs sob_congr sob_smul sob_sum)
open GlobalTheory.CompanionTheory.SecBd (cls_sum cls_congr cls_eq cls_sub)

variable {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem Rw_zero (w : List (Bool × Fin n × Fin n)) : Rw w (0 : Mat n → V) = 0 := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    show Rd (bs p) (Rw w (0 : Mat n → V)) = 0
    rw [ih]
    funext g
    simp [Rd]

theorem sob_zero : Sob μ (0 : Mat n → V) :=
  ⟨contDiffOn_const, fun w => by rw [Rw_zero]; exact MemLp.zero⟩

theorem cls_zero : cls μ (0 : Mat n → V) = 0 := by
  have h : MemLp (fun y : G n => (0 : Mat n → V) y.val) 2 μ := MemLp.zero
  rw [cls_eq μ h]
  exact MemLp.toLp_zero h

theorem cls_mem {f : Mat n → V} (hf : Sob μ f) : cls μ f ∈ Msob μ V :=
  Submodule.subset_span ⟨f, hf, rfl⟩

theorem exists_rep (x : Lp V 2 μ) (hx : x ∈ Msob μ V) : ∃ f : Mat n → V, Sob μ f ∧ cls μ f = x := by
  induction hx using Submodule.span_induction with
  | mem x h => exact h
  | zero => exact ⟨0, sob_zero, cls_zero⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨f', hf', rfl⟩ := hy
    have h := sob_comb 1 hf hf'
    refine ⟨_, h.1, ?_⟩
    simpa [Rw] using h.2 []
  | smul a x _ hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    have h := sob_comb a hf (sob_zero (μ := μ) (V := V))
    refine ⟨_, h.1, ?_⟩
    simpa [Rw, cls_zero] using h.2 []

def rp (x : Msob μ V) : Mat n → V := Classical.choose (exists_rep x.1 x.2)

theorem rp_sob (x : Msob μ V) : Sob μ (rp x) := (Classical.choose_spec (exists_rep x.1 x.2)).1

theorem rp_cls (x : Msob μ V) : cls μ (rp x) = x := (Classical.choose_spec (exists_rep x.1 x.2)).2

def Uniq (μ : Measure (G n)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] : Prop :=
  ∀ f f' : Mat n → V, Sob μ f → Sob μ f' → cls μ f = cls μ f' → ∀ g ∈ GLs n, f g = f' g

def Xf (p : Bool × Fin n × Fin n) (x : Msob μ V) : Msob μ V :=
  ⟨cls μ (Rd (bs p) (rp x)), cls_mem (sob_bs p (rp_sob x))⟩

theorem Xf_cls (hu : Uniq μ V) (p : Bool × Fin n × Fin n) {f : Mat n → V} (hf : Sob μ f) (x : Msob μ V)
    (hx : (x : Lp V 2 μ) = cls μ f) : (Xf p x : Lp V 2 μ) = cls μ (Rd (bs p) f) := by
  have e : Set.EqOn (rp x) f (GLs n) := fun g hg =>
    hu _ _ (rp_sob x) hf ((rp_cls x).trans hx) g hg
  exact cls_congr μ ((sob_bs p (rp_sob x)).2 [])
    fun g hg => GlobalTheory.CompanionTheory.RCalc.Rd_congr (bs p) e hg

theorem Xf_comb (hu : Uniq μ V) (p : Bool × Fin n × Fin n) (a : ℂ) (x y : Msob μ V) :
    Xf p (a • x + y) = a • Xf p x + Xf p y := by
  have h := sob_comb a (rp_sob x) (rp_sob y)
  apply Subtype.ext
  have e : ((a • x + y : Msob μ V) : Lp V 2 μ) = cls μ (fun z => a • rp x z + rp y z) := by
    have := h.2 []
    simp only [Rw, id] at this
    rw [this, rp_cls, rp_cls]
    rfl
  rw [Xf_cls hu p h.1 _ e]
  exact h.2 [p]

def X (hu : Uniq μ V) (p : Bool × Fin n × Fin n) : Module.End ℂ (Msob μ V) where
  toFun := Xf p
  map_add' x y := by simpa using Xf_comb hu p 1 x y
  map_smul' a x := by
    have h0 : Xf p (0 : Msob μ V) = 0 := by simpa using Xf_comb hu p 1 0 0
    simpa [h0] using Xf_comb hu p a x 0

theorem X_cls (hu : Uniq μ V) (p : Bool × Fin n × Fin n) {f : Mat n → V} (hf : Sob μ f) :
    (X hu p ⟨cls μ f, cls_mem hf⟩ : Msob μ V) = ⟨cls μ (Rd (bs p) f), cls_mem (sob_bs p hf)⟩ :=
  Subtype.ext (Xf_cls hu p hf _ rfl)

theorem X_skew (hu : Uniq μ V) (hI : ∀ f f' : Mat n → V, Sob μ f → Sob μ f' → ∀ Y : Mat n,
      ⟪cls μ (Rd Y f), cls μ f'⟫_ℂ = -⟪cls μ f, cls μ (Rd Y f')⟫_ℂ)
    (p : Bool × Fin n × Fin n) (u v : Msob μ V) : ⟪X hu p u, v⟫_ℂ = -⟪u, X hu p v⟫_ℂ := by
  obtain ⟨f, hf, hfu⟩ := exists_rep u.1 u.2
  obtain ⟨f', hf', hfv⟩ := exists_rep v.1 v.2
  have eu : u = ⟨cls μ f, cls_mem hf⟩ := Subtype.ext hfu.symm
  have ev : v = ⟨cls μ f', cls_mem hf'⟩ := Subtype.ext hfv.symm
  rw [eu, ev, X_cls hu p hf, X_cls hu p hf']
  exact hI f f' hf hf' (bs p)

theorem memS {f : Mat n → V} (hf : Sob μ f) : MemLp (fun y : G n => f y.val) 2 μ := hf.2 []

theorem cls_smul (a : ℂ) {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) :
    cls μ (fun g => a • f g) = a • cls μ f := by
  rw [cls_eq μ h, cls_eq μ (f := fun g => a • f g) (h.const_smul a)]
  exact MemLp.toLp_const_smul a h

theorem X_bracket (hu : Uniq μ V)
    (hB : ∀ f : Mat n → V, Sob μ f → ∀ Y Z, ∀ g ∈ GLs n,
      Rd Y (Rd Z f) g - Rd Z (Rd Y f) g = Rd (Y * Z - Z * Y) f g)
    (i j : Bool × Fin n × Fin n) (c : Bool × Fin n × Fin n → ℝ)
    (hc : bs i * bs j - bs j * bs i = ∑ k, c k • bs k) :
    X hu i * X hu j - X hu j * X hu i = ∑ k, (c k : ℂ) • X hu k := by
  refine LinearMap.ext fun u => ?_
  obtain ⟨f, hf, hfu⟩ := exists_rep u.1 u.2
  have eu : u = ⟨cls μ f, cls_mem hf⟩ := Subtype.ext hfu.symm
  rw [eu]
  apply Subtype.ext
  have hm : ∀ k, MemLp (fun y : G n => (c k : ℂ) • Rd (bs k) f y.val) 2 μ := fun k =>
    ((sob_bs k hf).2 []).const_smul _
  have h1 := cls_sum μ Finset.univ (fun k g => (c k : ℂ) • Rd (bs k) f g) fun k _ => hm k
  have hij : ∀ a b, ((X hu a * X hu b) ⟨cls μ f, cls_mem hf⟩ : Msob μ V).1 =
      cls μ (Rd (bs a) (Rd (bs b) f)) := fun a b => by
    rw [Module.End.mul_apply, X_cls hu b hf, X_cls hu a (sob_bs b hf)]
  have hs : ∀ k, (((c k : ℂ) • X hu k) ⟨cls μ f, cls_mem hf⟩ : Msob μ V).1 =
      cls μ (fun g => (c k : ℂ) • Rd (bs k) f g) := fun k => by
    rw [LinearMap.smul_apply, X_cls hu k hf, cls_smul _ (memS (sob_bs k hf))]
    rfl
  rw [LinearMap.sub_apply, Submodule.coe_sub, hij, hij, LinearMap.sum_apply, Submodule.coe_sum]
  simp only [hs]
  rw [← h1.2, ← cls_sub μ (memS (sob_bs i (sob_bs j hf))) (memS (sob_bs j (sob_bs i hf)))]
  refine cls_congr μ ((memS (sob_bs i (sob_bs j hf))).sub (memS (sob_bs j (sob_bs i hf)))) fun g hg => ?_
  rw [hB f hf _ _ g hg, GlobalTheory.CompanionTheory.FcCalc.Ibp.Rd_expand f hc g]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (Complex.coe_smul _ _).symm

theorem word_apply (hu : Uniq μ V) (w : List (Bool × Fin n × Fin n)) {f : Mat n → V} (hf : Sob μ f) :
    (((w.map (X hu)).prod ⟨cls μ f, cls_mem hf⟩ : Msob μ V) : Lp V 2 μ) = cls μ (Rw w f) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    have hw := GlobalTheory.CompanionTheory.SobOpsPf.sob_Rw w hf
    have e : (w.map (X hu)).prod ⟨cls μ f, cls_mem hf⟩ = ⟨cls μ (Rw w f), cls_mem hw⟩ := Subtype.ext ih
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, e, X_cls hu p hw]
    rfl

theorem sob_Lap {f : Mat n → V} (hf : Sob μ f) : Sob μ (Lap f) := by
  refine sob_congr (sob_smul (-1 : ℂ) (sob_sum Finset.univ hf fun p => sob_bs p (sob_bs p hf))) fun g _ => ?_
  simp [Lap]

theorem lap_apply (hu : Uniq μ V) {f : Mat n → V} (hf : Sob μ f) :
    (-∑ i, X hu i * X hu i) ⟨cls μ f, cls_mem hf⟩ = (⟨cls μ (Lap f), cls_mem (sob_Lap hf)⟩ : Msob μ V) := by
  apply Subtype.ext
  have hm : ∀ p, MemLp (fun y : G n => Rd (bs p) (Rd (bs p) f) y.val) 2 μ := fun p =>
    (sob_bs p (sob_bs p hf)).2 []
  have h1 := cls_sum μ Finset.univ (fun p g => Rd (bs p) (Rd (bs p) f) g) fun p _ => hm p
  have e : cls μ (Lap f) = -∑ p, cls μ (Rd (bs p) (Rd (bs p) f)) := by
    have e1 : Lap f = fun g => (-1 : ℂ) • ∑ p, Rd (bs p) (Rd (bs p) f) g := by
      funext g; simp [Lap]
    rw [e1, cls_smul _ h1.1, h1.2]
    simp
  show ((-∑ i, X hu i * X hu i) ⟨cls μ f, cls_mem hf⟩ : Msob μ V).1 = cls μ (Lap f)
  rw [e, LinearMap.neg_apply, LinearMap.sum_apply, Submodule.coe_neg, Submodule.coe_sum]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Module.End.mul_apply, X_cls hu p hf, X_cls hu p (sob_bs p hf)]

theorem sob_Lap_iter (j : ℕ) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Lap^[j] f) := by
  induction j generalizing f with
  | zero => exact hf
  | succ j ih => exact ih (sob_Lap hf)

theorem pow_apply (hu : Uniq μ V) (j : ℕ) {f : Mat n → V} (hf : Sob μ f) :
    (((-∑ i, X hu i * X hu i) ^ j) ⟨cls μ f, cls_mem hf⟩ : Msob μ V).1 = cls μ (Lap^[j] f) := by
  induction j generalizing f with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, lap_apply hu hf, ih (sob_Lap hf)]
    rfl

theorem word_bound : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V],
    LgFacts → Unimod → RCalc → AlgEst → ClsFacts → IbpSob →
    ∀ w : List (Bool × Fin n × Fin n), ∃ C : ℝ, ∀ f : Mat n → V, Sob μ f →
      ‖cls μ (Rw w f)‖ ≤ C * ∑ j ∈ range (w.length + 1), ‖cls μ (GlobalTheory.CompanionTheory.FcSmooth.Lap^[j] f)‖ := by
  intro n _ _ μ _ V _ _ _ hL hU hR hA hC hI w
  have hu : Uniq μ V := fun f f' hf hf' e g hg =>
    (hC n μ V hU).1 f f' hf.1.continuousOn hf'.1.continuousOn (hf.2 []) (hf'.2 []) e g hg
  choose c hc using fun ij : (Bool × Fin n × Fin n) × (Bool × Fin n × Fin n) =>
    GlobalTheory.CompanionTheory.FcCalc.Ibp.exists_coeff (bs ij.1 * bs ij.2 - bs ij.2 * bs ij.1)
  obtain ⟨C, hCb⟩ := hA (Msob μ V) (Bool × Fin n × Fin n) (X hu) (fun i j k => c (i, j) k)
    (X_skew hu fun f f' hf hf' Y => hI n μ V hL hU hR f f' hf hf' Y)
    (fun i j => X_bracket hu (fun f hf Y Z g hg => ((hR n).1 V f hf.1).2.1 Y Z g hg) i j _ (hc (i, j))) w
  refine ⟨C, fun f hf => ?_⟩
  have h := hCb ⟨cls μ f, cls_mem hf⟩
  have e1 : ‖cls μ (Rw w f)‖ = ‖(w.map (X hu)).prod ⟨cls μ f, cls_mem hf⟩‖ := by
    rw [← word_apply hu w hf]; rfl
  rw [e1]
  refine h.trans_eq ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_apply hu j hf]
  rfl

end GlobalTheory.CompanionTheory.FcSmooth.WordBd
