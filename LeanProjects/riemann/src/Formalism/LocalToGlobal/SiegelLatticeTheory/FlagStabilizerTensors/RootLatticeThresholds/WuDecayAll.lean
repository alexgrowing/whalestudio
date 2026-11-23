import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WuDecayPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne
import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.TensInt
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.QuotRaw
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LintegralFinProd

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.WuDecay
open scoped InnerProductSpace ENNReal NNReal
open Matrix

set_option linter.unusedVariables false

namespace Formalism.L2.SG.Pf

def WuDecayOfGap : Prop :=
  ∀ D : D7, Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ X : HidaSetting D,
    WuDecay X ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I)

end Formalism.L2.SG.Pf

namespace Formalism.L2.SG.Pf.WuDec

open Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.WuDecayPf

theorem r_odd (D : D7) : Odd D.R.r := by
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have := D.R.two_le_m
  refine ⟨a + b - 1, ?_⟩
  simp only [Ranks.r]; omega

theorem dimS (D : D7) : 2 * D.R.rS + D.R.k + 1 = D.R.r := dimS_eq D.R

theorem gapBig_of_gapHyp (D : D7) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (τ : D.what₂.Tau) :
    Formalism.MainNotions.CayleySignature.GapBig D.R.k D.R.rS (Formalism.MainNotions.b48 D τ) := by
  obtain ⟨hr, hgap⟩ := hG
  have hdim := dimS D
  have hm := Formalism.MainNotions.two_rS_add_two D
  have hk := D.R.m_add_three_le_k
  refine ⟨D.R.r + 6, ?_, ?_, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := r_odd D
    exact ⟨c + 3, by omega⟩
  · simp only [Formalism.MainNotions.CayleySignature.rk48]; omega
  · simp only [Formalism.MainNotions.CayleySignature.rk48]; omega
  · intro j hj
    have hN : (6 : ℝ) ≤ (D.R.r : ℝ) := by exact_mod_cast (by omega : 6 ≤ D.R.r)
    have hmN : ((2 * D.R.rS + 2 : ℕ) : ℝ) ≤ (D.R.r : ℝ) := by exact_mod_cast (by omega : 2 * D.R.rS + 2 ≤ D.R.r)
    have key := Formalism.MainNotions.numNV (D.R.r : ℝ) ((2 * D.R.rS + 2 : ℕ) : ℝ) ((D.R.r + 6 : ℕ) : ℝ) hN hmN (by positivity)
      (by push_cast; ring)
    have hrk : Formalism.MainNotions.CayleySignature.rk48 D.R.k D.R.rS = D.R.r := by simp only [Formalism.MainNotions.CayleySignature.rk48]; omega
    have hcast : (((Formalism.MainNotions.CayleySignature.rk48 D.R.k D.R.rS + (2 * D.R.rS + 2) * (D.R.r + 6) : ℕ)) : ℝ) =
        (D.R.r : ℝ) + ((2 * D.R.rS + 2 : ℕ) : ℝ) * ((D.R.r + 6 : ℕ) : ℝ) := by
      rw [hrk]; push_cast; ring
    rw [hcast]
    have hj' : (Fin.cast hm j).1 + 1 < D.R.m := by simp; omega
    have hg := hgap τ (Fin.cast hm j) hj'
    have hgR : (16 : ℝ) * (D.R.r : ℝ) ^ 19 ≤ Formalism.MainNotions.b48 D τ ⟨j.val + 1, hj⟩ - Formalism.MainNotions.b48 D τ j := by
      have : Formalism.MainNotions.b48 D τ ⟨j.val + 1, hj⟩ - Formalism.MainNotions.b48 D τ j =
          (((D.hc τ).b ⟨(Fin.cast hm j).1 + 1, hj'⟩ - (D.hc τ).b (Fin.cast hm j) : ℚ) : ℝ) := by
        simp only [Formalism.MainNotions.b48]; push_cast; rfl
      rw [this]
      exact_mod_cast hg
    have hpos : (0 : ℝ) < (D.R.r : ℝ) ^ 19 := by positivity
    push_cast at key ⊢
    linarith

theorem coefW_cast (hC : CoefWeightedLoc) {k r : ℕ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ}
    (hl : Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.CayleySignature.lam48 k r v b)) (hg : Formalism.MainNotions.CayleySignature.GapBig k r b) {n : ℕ}
    (h : n = 2 * r + k + 1) (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (hε : ∀ i, ε i = Formalism.MainNotions.CayleySignature.eps48 k r (Fin.cast h i))
    (hlam : ∀ i, lam i = Formalism.MainNotions.CayleySignature.lam48 k r v b (Fin.cast h i))
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hds : IsDS ε lam σ) (w : H) (hw : IsLowUnit ε lam σ w) :
    ∫⁻ g, ‖⟪w, σ (uMat g) w⟫_ℂ‖ₑ *
        ENNReal.ofReal (opn (uMat g) ^ (4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt (2 * ((r + 1 : ℕ) : ℝ))))
      ∂(Formalism.REAL.muG ε) < ⊤ := by
  subst h
  have he : ε = Formalism.MainNotions.CayleySignature.eps48 k r := funext fun i => by rw [hε i]; rfl
  have hl' : lam = Formalism.MainNotions.CayleySignature.lam48 k r v b := funext fun i => by rw [hlam i]; rfl
  subst he hl'
  exact hC k r v b hl hg H σ hds w hw

variable {D : D7} (X : HidaSetting D)

theorem hdim : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := X.n_eq.trans (dimS D).symm

theorem eps_cast (v : InfinitePlace X.B.I.F) (i : Fin X.B.I.n) :
    X.B.I.ε v i = Formalism.MainNotions.CayleySignature.eps48 D.R.k D.R.rS (Fin.cast (hdim X) i) := by
  rw [X.eps_eq, Formalism.MainNotions.epsilon_signature_eq]
  simp only [epsSH]
  congr 1

theorem lam_cast (v : InfinitePlace X.B.I.F) (i : Fin X.B.I.n) :
    X.B.lam v i = Formalism.MainNotions.CayleySignature.lam48 D.R.k D.R.rS (Formalism.MainNotions.v48 D (X.pl v)) (Formalism.MainNotions.b48 D (X.pl v))
      (Fin.cast (hdim X) i) := by
  rw [X.lam_eq, Formalism.MainNotions.lambda_highest_weight_eq]
  simp only [lamSH]
  congr 1

theorem qAt_le (v : InfinitePlace X.B.I.F) : X.B.I.qAt v ≤ D.R.rS + 1 := by
  have he : ∀ a, X.B.I.ε v a = epsS D.R (Fin.cast X.n_eq a) := X.eps_eq v
  simp only [AutInst.qAt, he]
  rw [card_cast X.n_eq (fun a => epsS D.R a = false)]
  exact card_epsS_false

theorem first_count_le_log : N1 X ≤ 4 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt (2 * ((D.R.rS + 1 : ℕ) : ℝ)) := by
  unfold N1
  rw [hdim X]
  have hs : (Finset.univ.sup fun v => X.B.I.qAt v) ≤ D.R.rS + 1 := Finset.sup_le fun v _ => qAt_le X v
  have hs' : ((Finset.univ.sup fun v => X.B.I.qAt v : ℕ) : ℝ) ≤ ((D.R.rS + 1 : ℕ) : ℝ) := by exact_mod_cast hs
  gcongr

theorem coefWeighted_of_gap (hC : CoefWeightedLoc) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) :
    CoefWeighted X := by
  intro v
  have hl : Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.CayleySignature.lam48 D.R.k D.R.rS (Formalism.MainNotions.v48 D (X.pl v)) (Formalism.MainNotions.b48 D (X.pl v))) := by
    rw [Formalism.MainNotions.lambda_highest_weight_eq]; exact Formalism.MainNotions.S.Inh.obj_isHCParam_lamSH D.R (D.hc (X.pl v))
  have key := coefW_cast hC hl (gapBig_of_gapHyp D hG (X.pl v)) (hdim X) (X.B.I.ε v) (X.B.lam v)
    (eps_cast X v) (lam_cast X v) (X.B.σ v) (X.ds v) (X.B.w v) (X.low v)
  have hn : 0 < X.B.I.n := by rw [hdim X]; omega
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) key
  show ‖coefV X v g‖ₑ * _ ≤ _
  gcongr
  all_goals first | exact one_le_opn hn g | exact first_count_le_log X

theorem phInt_of_gap (hC : CoefWeightedLoc) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) :
    Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) :=
  phInt_of_weighted X (coefWeighted_of_gap X hC hG)

section InSGroup

variable {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ)

theorem spanLt_mono {a b : ℕ} (h : a ≤ b) : spanLt e a ≤ spanLt e b :=
  Submodule.span_mono (Set.image_mono fun c (hc : c.1 < a) => lt_of_lt_of_le hc h)

theorem mem_spanLt {a : ℕ} (c : Fin r) (hc : c.1 < a) : e c ∈ spanLt e a :=
  Submodule.subset_span ⟨c, hc, rfl⟩

theorem mulVec_mul_sub (g h : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    (g * h - 1) *ᵥ x = g *ᵥ ((h - 1) *ᵥ x) + (g - 1) *ᵥ x := by
  simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.one_mulVec, Matrix.mul_one]
  abel

variable {e z}

theorem inS_maps {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (a : ℕ) :
    ∀ x ∈ spanLt e a, g *ᵥ x ∈ spanLt e a := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    have h1 : g *ᵥ e c = e c + (g - 1) *ᵥ e c := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [h1]
    exact Submodule.add_mem _ (mem_spanLt e c hc) (spanLt_mono e (le_of_lt hc) (hg.1 c))
  | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hx

theorem inS_mul {g h : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (hh : InS e z h) : InS e z (g * h) := by
  refine ⟨fun a => ?_, ?_⟩
  · rw [mulVec_mul_sub]
    exact Submodule.add_mem _ (inS_maps hg a.1 _ (hh.1 a)) (hg.1 a)
  · rw [mulVec_mul_sub]
    exact Submodule.add_mem _ (inS_maps hg r _ hh.2) hg.2

theorem inS_one : InS e z (1 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨fun a => by simp, by simp⟩

theorem inS_inv_maps {g B : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (hBg : B * g = 1) (hgB : g * B = 1) (a : ℕ) :
    ∀ y ∈ spanLt e a, B *ᵥ y ∈ spanLt e a := by
  intro y hy
  let f : spanLt e a →ₗ[ℂ] spanLt e a := (Matrix.mulVecLin g).restrict (fun x hx => inS_maps hg a x hx)
  have hinj : Function.Injective f := by
    intro x1 x2 h12
    have h' : g *ᵥ (x1 : Fin n → ℂ) = g *ᵥ (x2 : Fin n → ℂ) := congrArg Subtype.val h12
    have h'' := congrArg (fun t => B *ᵥ t) h'
    simp only [Matrix.mulVec_mulVec, hBg, Matrix.one_mulVec] at h''
    exact Subtype.ext h''
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨y, hy⟩
  have hx' : g *ᵥ (x : Fin n → ℂ) = y := congrArg Subtype.val hx
  rw [← hx', Matrix.mulVec_mulVec, hBg, Matrix.one_mulVec]
  exact x.2

theorem inS_inv {g B : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (hBg : B * g = 1) (hgB : g * B = 1) :
    InS e z B := by
  have key : ∀ x, (B - 1) *ᵥ x = -(B *ᵥ ((g - 1) *ᵥ x)) := by
    intro x
    simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hBg, Matrix.one_mulVec, Matrix.mul_one]
    abel
  refine ⟨fun a => ?_, ?_⟩
  · rw [key]; exact Submodule.neg_mem _ (inS_inv_maps hg hBg hgB a.1 _ (hg.1 a))
  · rw [key]; exact Submodule.neg_mem _ (inS_inv_maps hg hBg hgB r _ hg.2)

end InSGroup

section Loc

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def Sloc (v : InfinitePlace X.B.I.F) : Set (Formalism.REAL.UJ (X.B.I.ε v)) :=
  {s | InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat s)}

def Nloc (v : InfinitePlace X.B.I.F) : Set (Formalism.REAL.UJ (X.B.I.ε v)) :=
  {s | InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat s)}

def Hloc (v : InfinitePlace X.B.I.F) : Set (Formalism.REAL.UJ (X.B.I.ε v)) :=
  {s | ∀ y ∈ Set.range X.eR ∪ Set.range X.fR ∪ {X.zR u}, uMat s *ᵥ rv X.B.I v y = rv X.B.I v y}

def nuLocX (v : InfinitePlace X.B.I.F) (x : Formalism.REAL.UJ (X.B.I.ε v)) : ℝ :=
  ⨅ t : Sloc X u v, opn (uMat ((t : Formalism.REAL.UJ (X.B.I.ε v)) * x))

theorem one_mem_Sloc (v : InfinitePlace X.B.I.F) : (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ Sloc X u v := inS_one

theorem mul_mem_Sloc (v : InfinitePlace X.B.I.F) {s t : Formalism.REAL.UJ (X.B.I.ε v)} (hs : s ∈ Sloc X u v)
    (ht : t ∈ Sloc X u v) : s * t ∈ Sloc X u v := by
  show InS _ _ (uMat (s * t))
  rw [uMat_mul']; exact inS_mul hs ht

theorem uMat_inv_mul {m : ℕ} {ε : Fin m → Bool} (s : Formalism.REAL.UJ ε) : uMat s⁻¹ * uMat s = 1 := by
  rw [← uMat_mul', inv_mul_cancel]; rfl

theorem uMat_mul_inv {m : ℕ} {ε : Fin m → Bool} (s : Formalism.REAL.UJ ε) : uMat s * uMat s⁻¹ = 1 := by
  rw [← uMat_mul', mul_inv_cancel]; rfl

theorem inv_mem_Sloc (v : InfinitePlace X.B.I.F) {s : Formalism.REAL.UJ (X.B.I.ε v)} (hs : s ∈ Sloc X u v) :
    s⁻¹ ∈ Sloc X u v :=
  inS_inv hs (uMat_inv_mul s) (uMat_mul_inv s)

theorem nuLocX_nonneg (v : InfinitePlace X.B.I.F) (x : Formalism.REAL.UJ (X.B.I.ε v)) : 0 ≤ nuLocX X u v x :=
  Real.iInf_nonneg fun _ => opn_nonneg _

theorem bdd_nuLocX (v : InfinitePlace X.B.I.F) (x : Formalism.REAL.UJ (X.B.I.ε v)) :
    BddBelow (Set.range fun t : Sloc X u v => opn (uMat ((t : Formalism.REAL.UJ (X.B.I.ε v)) * x))) :=
  ⟨0, by rintro _ ⟨t, rfl⟩; exact opn_nonneg _⟩

theorem nuLocX_le (v : InfinitePlace X.B.I.F) (x t : Formalism.REAL.UJ (X.B.I.ε v)) (ht : t ∈ Sloc X u v) :
    nuLocX X u v x ≤ opn (uMat (t * x)) :=
  ciInf_le (bdd_nuLocX X u v x) (⟨t, ht⟩ : Sloc X u v)

theorem nuLocX_inv (v : InfinitePlace X.B.I.F) {s : Formalism.REAL.UJ (X.B.I.ε v)} (hs : s ∈ Sloc X u v)
    (x : Formalism.REAL.UJ (X.B.I.ε v)) : nuLocX X u v (s * x) = nuLocX X u v x := by
  have : Nonempty (Sloc X u v) := ⟨⟨1, one_mem_Sloc X u v⟩⟩
  apply le_antisymm
  · refine le_ciInf fun t => ?_
    have := nuLocX_le X u v (s * x) ((t : Formalism.REAL.UJ (X.B.I.ε v)) * s⁻¹)
      (mul_mem_Sloc X u v t.2 (inv_mem_Sloc X u v hs))
    simpa [mul_assoc] using this
  · refine le_ciInf fun t => ?_
    have := nuLocX_le X u v x ((t : Formalism.REAL.UJ (X.B.I.ε v)) * s) (mul_mem_Sloc X u v t.2 hs)
    simpa [mul_assoc] using this

end Loc

section Glob

open Classical

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem continuous_opn_mul {m : ℕ} {ε : Fin m → Bool} (x : Formalism.REAL.UJ ε) :
    Continuous fun t : Formalism.REAL.UJ ε => opn (uMat (t * x)) :=
  opn_continuous.comp (continuous_uMat.comp (continuous_id.mul continuous_const))

theorem continuous_opn_mul' {m : ℕ} {ε : Fin m → Bool} (t : Formalism.REAL.UJ ε) :
    Continuous fun x : Formalism.REAL.UJ ε => opn (uMat (t * x)) :=
  opn_continuous.comp (continuous_uMat.comp (continuous_const.mul continuous_id))

theorem measurable_nuLocX (v : InfinitePlace X.B.I.F) : Measurable (nuLocX X u v) := by
  obtain ⟨Dd, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Sloc X u v)
  have : Countable Dd := hDc.to_subtype
  have : Nonempty (Sloc X u v) := ⟨⟨1, one_mem_Sloc X u v⟩⟩
  have hne : Nonempty Dd := hDd.nonempty.to_subtype
  have heq : nuLocX X u v = fun x => ⨅ t : Dd, opn (uMat (((t : Sloc X u v) : Formalism.REAL.UJ (X.B.I.ε v)) * x)) := by
    funext x
    have hbd : BddBelow (Set.range fun t : Dd => opn (uMat (((t : Sloc X u v) : Formalism.REAL.UJ (X.B.I.ε v)) * x))) :=
      ⟨0, by rintro _ ⟨t, rfl⟩; exact opn_nonneg _⟩
    apply le_antisymm
    · exact le_ciInf fun t => nuLocX_le X u v x _ (t : Sloc X u v).2
    · refine le_ciInf fun t => ?_
      have hc : Continuous fun t : Sloc X u v => opn (uMat ((t : Formalism.REAL.UJ (X.B.I.ε v)) * x)) :=
        (continuous_opn_mul x).comp continuous_subtype_val
      have hcl : IsClosed {t : Sloc X u v | (⨅ s : Dd, opn (uMat (((s : Sloc X u v) : Formalism.REAL.UJ (X.B.I.ε v)) * x))) ≤
          opn (uMat ((t : Formalism.REAL.UJ (X.B.I.ε v)) * x))} := isClosed_le continuous_const hc
      have hsub : Dd ⊆ {t : Sloc X u v | (⨅ s : Dd, opn (uMat (((s : Sloc X u v) : Formalism.REAL.UJ (X.B.I.ε v)) * x))) ≤
          opn (uMat ((t : Formalism.REAL.UJ (X.B.I.ε v)) * x))} := fun t ht => ciInf_le hbd ⟨t, ht⟩
      have h2 := hcl.closure_subset_iff.2 hsub
      rw [hDd.closure_eq] at h2
      exact h2 (Set.mem_univ t)
  rw [heq]
  exact Measurable.iInf fun t => (continuous_opn_mul' _).measurable

theorem nuInf_le_prod (x : X.B.I.Ginf) : nuInf X u x ≤ ∏ v, nuLocX X u v (x v) := by
  have key : ∀ δ : ℝ, 0 < δ → nuInf X u x ≤ ∏ v, (nuLocX X u v (x v) + δ) := by
    intro δ hδ
    have : ∀ v, ∃ t : Sloc X u v, opn (uMat ((t : Formalism.REAL.UJ (X.B.I.ε v)) * x v)) < nuLocX X u v (x v) + δ := by
      intro v
      have : Nonempty (Sloc X u v) := ⟨⟨1, one_mem_Sloc X u v⟩⟩
      exact exists_lt_of_ciInf_lt (lt_add_of_pos_right _ hδ)
    choose t ht using this
    have hmem : (fun v => (t v : Formalism.REAL.UJ (X.B.I.ε v))) ∈ X.SinfU u := fun v => (t v).2
    calc nuInf X u x ≤ normInf X ((fun v => (t v : Formalism.REAL.UJ (X.B.I.ε v))) * x) := nuInf_le X u x _ hmem
      _ = ∏ v, opn (uMat ((t v : Formalism.REAL.UJ (X.B.I.ε v)) * x v)) := rfl
      _ ≤ ∏ v, (nuLocX X u v (x v) + δ) :=
          Finset.prod_le_prod (fun v _ => opn_nonneg _) (fun v _ => (ht v).le)
  have hc : Continuous fun δ : ℝ => ∏ v, (nuLocX X u v (x v) + δ) :=
    continuous_finsetProd _ fun v _ => continuous_const.add continuous_id
  have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simp only [add_zero] at ht
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ hδ => key δ hδ)

theorem norm_psiR {m r : ℕ} (ε : Fin m → Bool) (gg : ℕ) (e f : Fin r → Fin m → ℂ) (z : Fin m → ℂ)
    (g : Matrix (Fin m) (Fin m) ℂ) : ‖psiR ε gg e f z g‖ = 1 := by
  unfold psiR
  set c := rootCoord ε e f z g
  have hq : (∑ a, (c a + star (c a))) / (gg : ℂ) = (((∑ a, 2 * (c a).re) / gg : ℝ) : ℂ) := by
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show star (c a) = (starRingEnd ℂ) (c a) from rfl, Complex.add_conj]
    push_cast; ring
  rw [hq]
  have : 2 * (Real.pi : ℂ) * Complex.I * (((∑ a, 2 * (c a).re) / gg : ℝ) : ℂ) =
      ((2 * Real.pi * ((∑ a, 2 * (c a).re) / gg) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem norm_psiInf (s : X.B.I.Ginf) : ‖X.psiInfU u s‖ = 1 := by
  unfold HidaSetting.psiInfU psiInf
  rw [norm_prod]
  exact Finset.prod_eq_one fun v _ => norm_psiR _ _ _ _ _ _

theorem norm_Wu (x : X.B.I.Ginf) : ‖X.Wu u x‖ = ∏ v, ‖X.Wloc u v (x v)‖ := by
  rw [X.Wu_tens]; exact norm_tens (X.tensU_inner u) _

theorem norm_Wu_inv (s : X.B.I.Ginf) (hs : s ∈ X.SinfU u) (x : X.B.I.Ginf) : ‖X.Wu u (s * x)‖ = ‖X.Wu u x‖ := by
  rw [(X.Wu_spec u).1 s hs x, norm_smul]
  have h1 : ‖psiInf X.B.I X.B.g (fun a => crdOf X.B.I X.ιE X.bas (X.eX a))
      (fun a => crdOf X.B.I X.ιE X.bas (X.fY a)) (crdOf X.B.I X.ιE X.bas (X.zu u)) s‖ = 1 := norm_psiInf X u s
  rw [h1, one_mul]
  have h2 := (X.piU_rep u).2.2.1 s hs (X.Wu u x) (X.Wu u x)
  have h3 : ‖X.piU u s (X.Wu u x)‖ ^ 2 = ‖X.Wu u x‖ ^ 2 := by
    have := congrArg RCLike.re h2
    rwa [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at this
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3

theorem exists_Wu_ne : ∃ x, X.Wu u x ≠ 0 := by
  by_contra h
  push Not at h
  have h1 := ((X.Wu_spec u).2.2.2.2)
  simp only [h, enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, lintegral_zero] at h1
  exact zero_ne_one h1

def single (v : InfinitePlace X.B.I.F) (s : Formalism.REAL.UJ (X.B.I.ε v)) : X.B.I.Ginf :=
  Function.update (1 : X.B.I.Ginf) v s

theorem single_mem (v : InfinitePlace X.B.I.F) {s : Formalism.REAL.UJ (X.B.I.ε v)} (hs : s ∈ Sloc X u v) :
    single X v s ∈ X.SinfU u := by
  intro w
  by_cases h : w = v
  · subst h; simp only [single, Function.update_self]; exact hs
  · simp only [single, Function.update_of_ne h]; exact one_mem_Sloc X u w

theorem norm_Wloc_inv (v : InfinitePlace X.B.I.F) {s : Formalism.REAL.UJ (X.B.I.ε v)} (hs : s ∈ Sloc X u v)
    (y : Formalism.REAL.UJ (X.B.I.ε v)) : ‖X.Wloc u v (s * y)‖ = ‖X.Wloc u v y‖ := by
  obtain ⟨x0, hx0⟩ := exists_Wu_ne X u
  have hne : ∀ w, ‖X.Wloc u w (x0 w)‖ ≠ 0 := by
    have : ∏ w, ‖X.Wloc u w (x0 w)‖ ≠ 0 := by rw [← norm_Wu]; exact norm_ne_zero_iff.2 hx0
    exact fun w => (Finset.prod_ne_zero_iff.1 this) w (Finset.mem_univ w)
  set xx : X.B.I.Ginf := Function.update x0 v y
  have hkey := norm_Wu_inv X u (single X v s) (single_mem X u v hs) xx
  rw [norm_Wu, norm_Wu] at hkey
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v), ← Finset.mul_prod_erase _ _ (Finset.mem_univ v)] at hkey
  have hP : ∏ w ∈ Finset.univ.erase v, ‖X.Wloc u w ((single X v s * xx) w)‖ =
      ∏ w ∈ Finset.univ.erase v, ‖X.Wloc u w (xx w)‖ := by
    refine Finset.prod_congr rfl fun w hw => ?_
    have hwv : w ≠ v := Finset.ne_of_mem_erase hw
    simp only [Pi.mul_apply, single, Function.update_of_ne hwv, Pi.one_apply, one_mul]
  have hP2 : ∏ w ∈ Finset.univ.erase v, ‖X.Wloc u w (xx w)‖ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun w hw => ?_
    have hwv : w ≠ v := Finset.ne_of_mem_erase hw
    simp only [xx, Function.update_of_ne hwv]; exact hne w
  rw [hP] at hkey
  have hv1 : (single X v s * xx) v = s * y := by simp [single, xx]
  have hv2 : xx v = y := by simp [xx]
  rw [hv1, hv2] at hkey
  exact mul_right_cancel₀ hP2 hkey

end Glob

section Steps

open Classical

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def NHloc (v : InfinitePlace X.B.I.F) : Set (Formalism.REAL.UJ (X.B.I.ε v)) :=
  {s | ∃ m ∈ Nloc X u v, ∃ h ∈ Hloc X u v, s = m * h}

def QuotWit (μS νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (C : ℝ≥0∞) : Prop :=
  C ≠ 0 ∧ C ≠ ⊤ ∧
    (∀ v, (SigmaFinite (μS v) ∧ μS v ≠ 0 ∧ μS v (NHloc X u v)ᶜ = 0 ∧
        ∀ s ∈ NHloc X u v, (μS v).map (fun x => s * x) = μS v) ∧
      ∀ F : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable F →
        ∫⁻ x, F x ∂(Formalism.REAL.muG (X.B.I.ε v)) = ∫⁻ x, (∫⁻ s, F (s * x) ∂(μS v)) ∂(νl v)) ∧
    ∀ F : ∀ v, Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, (∀ v, Measurable (F v)) →
      (∀ v, ∀ m ∈ Nloc X u v, ∀ h ∈ Hloc X u v, ∀ x, F v (m * h * x) = F v x) →
      ∫⁻ x, ∏ v, F v (x v) ∂(X.nuQ u) = C * ∏ v, ∫⁻ y, F v y ∂(νl v)

def QuotProdX : Prop := ∃ μS νl C, QuotWit X u μS νl C

def LocDecayX (νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  ∀ v, (∫⁻ x, ‖X.Wloc u v x‖ₑ * ENNReal.ofReal (nuLocX X u v x ^ N1 X) ∂(νl v) < ⊤) ∧
    ∃ (α : Formalism.REAL.UJ (X.B.I.ε v) → ℂ) (Ω : Set (Formalism.REAL.UJ (X.B.I.ε v))) (a : ℝ), IsCompact Ω ∧ 1 ∈ Ω ∧
      Measurable α ∧ (∀ y, α y ≠ 0 → y ∈ Ω) ∧ (∀ y, ‖α y‖ ≤ a) ∧
      ∀ x, Integrable (fun g => α g • X.Wloc u v (x * g)) (Formalism.REAL.muG (X.B.I.ε v)) ∧
        ∫ g, α g • X.Wloc u v (x * g) ∂(Formalism.REAL.muG (X.B.I.ε v)) = X.Wloc u v x

end Steps

def QuotAll : Prop := ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), QuotProdX X u

def LocDecayStep : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (u : D.what₂.Word)
    (μS νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (C : ℝ≥0∞), QuotWit X u μS νl C → LocDecayX X u νl

section Assembly

open Classical

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem Nloc_sub (v : InfinitePlace X.B.I.F) {m : Formalism.REAL.UJ (X.B.I.ε v)} (hm : m ∈ Nloc X u v) :
    m ∈ Sloc X u v := hm.1

theorem Hloc_sub (v : InfinitePlace X.B.I.F) {h : Formalism.REAL.UJ (X.B.I.ε v)} (hh : h ∈ Hloc X u v) :
    h ∈ Sloc X u v := by
  refine ⟨fun a => ?_, ?_⟩
  · have : uMat h *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) := hh _ (Or.inl (Or.inl ⟨a, rfl⟩))
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, this, sub_self]; exact Submodule.zero_mem _
  · have : uMat h *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u) := hh _ (Or.inr rfl)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, this, sub_self]; exact Submodule.zero_mem _

def Fw (v : InfinitePlace X.B.I.F) (y : Formalism.REAL.UJ (X.B.I.ε v)) : ℝ≥0∞ :=
  ‖X.Wloc u v y‖ₑ * ENNReal.ofReal (nuLocX X u v y ^ N1 X)

theorem measurable_Fw (v : InfinitePlace X.B.I.F) : Measurable (Fw X u v) :=
  (X.Wloc_cont u v).enorm.measurable.mul ((measurable_nuLocX X u v).pow_const _).ennreal_ofReal

theorem Fw_inv (v : InfinitePlace X.B.I.F) (m : Formalism.REAL.UJ (X.B.I.ε v)) (hm : m ∈ Nloc X u v)
    (h : Formalism.REAL.UJ (X.B.I.ε v)) (hh : h ∈ Hloc X u v) (x : Formalism.REAL.UJ (X.B.I.ε v)) :
    Fw X u v (m * h * x) = Fw X u v x := by
  have hs : m * h ∈ Sloc X u v := mul_mem_Sloc X u v (Nloc_sub X u v hm) (Hloc_sub X u v hh)
  unfold Fw
  rw [← enorm_norm (X.Wloc u v (m * h * x)), norm_Wloc_inv X u v hs, enorm_norm, nuLocX_inv X u v hs]

theorem wuWeighted_of_loc {μS νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))} {C : ℝ≥0∞}
    (hQ : QuotWit X u μS νl C) (hL : LocDecayX X u νl) : WuWeighted X u := by
  obtain ⟨_, hCt, _, hprod⟩ := hQ
  have hpt : ∀ x : X.B.I.Ginf, ‖X.Wu u x‖ₑ * ENNReal.ofReal (nuInf X u x ^ N1 X) ≤ ∏ v, Fw X u v (x v) := by
    intro x
    have e1 : ‖X.Wu u x‖ₑ = ∏ v, ‖X.Wloc u v (x v)‖ₑ := by
      rw [← ofReal_norm, norm_Wu, ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
      simp only [ofReal_norm]
    have e2 : ENNReal.ofReal (nuInf X u x ^ N1 X) ≤ ∏ v, ENNReal.ofReal (nuLocX X u v (x v) ^ N1 X) := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun v _ => Real.rpow_nonneg (nuLocX_nonneg X u v _) _),
        Real.finsetProd_rpow _ _ (fun v _ => nuLocX_nonneg X u v _)]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (nuInf_nonneg X u x) (nuInf_le_prod X u x) (weight_exponent_nonneg X))
    calc ‖X.Wu u x‖ₑ * ENNReal.ofReal (nuInf X u x ^ N1 X)
        ≤ (∏ v, ‖X.Wloc u v (x v)‖ₑ) * ∏ v, ENNReal.ofReal (nuLocX X u v (x v) ^ N1 X) := by
          rw [e1]; gcongr
      _ = ∏ v, Fw X u v (x v) := by rw [← Finset.prod_mul_distrib]; rfl
  unfold WuWeighted
  calc ∫⁻ x, ‖X.Wu u x‖ₑ * ENNReal.ofReal (nuInf X u x ^ N1 X) ∂(X.nuQ u)
      ≤ ∫⁻ x, ∏ v, Fw X u v (x v) ∂(X.nuQ u) := lintegral_mono hpt
    _ = C * ∏ v, ∫⁻ y, Fw X u v y ∂(νl v) :=
        hprod _ (fun v => measurable_Fw X u v) (fun v m hm h hh x => Fw_inv X u v m hm h hh x)
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hCt)
        (ENNReal.prod_lt_top fun v _ => (hL v).1)

theorem wuReprod_of_loc {νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))} (hL : LocDecayX X u νl) : WuReprod X u := by
  choose α Ω a hΩc h1 hαm hαs hαb hαr using fun v => (hL v).2
  refine ⟨fun z => ∏ v, α v (z v), Set.univ.pi Ω, ∏ v, (a v).toNNReal, isCompact_univ_pi hΩc,
    fun v _ => h1 v, Finset.measurable_prod _ fun v _ => (hαm v).comp (measurable_pi_apply v), ?_, ?_, ?_⟩
  · intro z hz v _
    exact hαs v (z v) ((Finset.prod_ne_zero_iff.1 hz) v (Finset.mem_univ v))
  · intro z
    rw [norm_prod, NNReal.coe_prod]
    exact Finset.prod_le_prod (fun v _ => norm_nonneg _)
      (fun v _ => (hαb v (z v)).trans (Real.le_coe_toNNReal _))
  · intro x
    have hT := integrable_and_integral_pi_apply (InfinitePlace X.B.I.F) (fun v => Formalism.REAL.UJ (X.B.I.ε v))
      (fun v => Formalism.REAL.muG (X.B.I.ε v)) (X.Vloc u) (X.Vpi u) (X.tensU u) (X.tensU_inner u) (X.tensU_span u)
      (fun v g => α v g • X.Wloc u v (x v * g)) (fun v => (hαr v (x v)).1)
    have heq : (fun z : X.B.I.Ginf => (∏ v, α v (z v)) • X.Wu u (x * z)) =
        fun z => X.tensU u (fun v => α v (z v) • X.Wloc u v (x v * z v)) := by
      funext z
      rw [tens_smul (X.tensU_inner u), X.Wu_tens]
      rfl
    refine ⟨?_, ?_⟩
    · rw [heq]; exact hT.1
    · rw [heq]
      show ∫ z, X.tensU u (fun v => α v (z v) • X.Wloc u v (x v * z v))
          ∂(Measure.pi fun v => Formalism.REAL.muG (X.B.I.ε v)) = X.Wu u x
      rw [hT.2, X.Wu_tens]
      congr 1
      funext v
      exact (hαr v (x v)).2

end Assembly

section LocalL2Isometry

open Classical

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem enorm_Wu (x : X.B.I.Ginf) : ‖X.Wu u x‖ₑ = ∏ v, ‖X.Wloc u v (x v)‖ₑ := by
  rw [← ofReal_norm, norm_Wu, ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
  simp only [ofReal_norm]

theorem localRepresentationL2 {μS νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))} {C : ℝ≥0∞} (hQ : QuotWit X u μS νl C)
    (v : InfinitePlace X.B.I.F) :
    ∫⁻ y, ‖X.Wloc u v y‖ₑ ^ 2 ∂(νl v) ≠ 0 ∧ ∫⁻ y, ‖X.Wloc u v y‖ₑ ^ 2 ∂(νl v) ≠ ⊤ := by
  obtain ⟨hC0, hCt, _, hprod⟩ := hQ
  have hinv : ∀ w, ∀ m ∈ Nloc X u w, ∀ h ∈ Hloc X u w, ∀ x,
      ‖X.Wloc u w (m * h * x)‖ₑ ^ 2 = ‖X.Wloc u w x‖ₑ ^ 2 := by
    intro w m hm h hh x
    have hs : m * h ∈ Sloc X u w := mul_mem_Sloc X u w (Nloc_sub X u w hm) (Hloc_sub X u w hh)
    rw [← enorm_norm (X.Wloc u w (m * h * x)), norm_Wloc_inv X u w hs, enorm_norm]
  have h1 := hprod (fun w y => ‖X.Wloc u w y‖ₑ ^ 2) (fun w => ((X.Wloc_cont u w).enorm.measurable.pow_const 2))
    hinv
  have h2 : ∫⁻ x, ∏ w, ‖X.Wloc u w (x w)‖ₑ ^ 2 ∂(X.nuQ u) = 1 := by
    rw [← (X.Wu_spec u).2.2.2.2]
    refine lintegral_congr fun x => ?_
    rw [enorm_Wu, Finset.prod_pow]
  rw [h2] at h1
  set P := ∏ w, ∫⁻ y, ‖X.Wloc u w y‖ₑ ^ 2 ∂(νl w) with hPdef
  have hP0 : P ≠ 0 := by
    intro h; rw [h, mul_zero] at h1; exact zero_ne_one h1.symm
  have hPt : P ≠ ⊤ := by
    intro h; rw [h, ENNReal.mul_top hC0] at h1; exact ENNReal.top_ne_one h1.symm
  have hne : ∀ w, ∫⁻ y, ‖X.Wloc u w y‖ₑ ^ 2 ∂(νl w) ≠ 0 := fun w =>
    (Finset.prod_ne_zero_iff.1 hP0) w (Finset.mem_univ w)
  refine ⟨hne v, fun htop => hPt ?_⟩
  rw [hPdef, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v), htop]
  exact ENNReal.top_mul (Finset.prod_ne_zero_iff.2 fun w _ => hne w)

end LocalL2Isometry

section LocEq

open Classical

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def psiV (v : InfinitePlace X.B.I.F) (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) : ℂ :=
  psiR (X.B.I.ε v) X.B.g (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) g

theorem uMat_one' {m : ℕ} {ε : Fin m → Bool} : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

theorem rootCoord_one (v : InfinitePlace X.B.I.F) (a : Fin D.R.rS) :
    rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) 1 a
      = 0 := by
  unfold rootCoord nxt
  rw [Matrix.one_mulVec]
  split_ifs with h
  · show hJ _ (rv X.B.I v (X.crd (X.fY a))) (rv X.B.I v (X.crd (X.eX ⟨a.1 + 1, h⟩))) = 0
    rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, Formalism.L2.SG.PoincareInHH.Cut.hT_f_e, if_neg, map_zero]
    intro hc
    have := congrArg Fin.val hc
    simp at this
  · show hJ _ (rv X.B.I v (X.crd (X.fY a))) (rv X.B.I v (X.crd (X.zu u))) = 0
    rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, (X.zu_orth u a).2, map_zero]

theorem psiV_one (v : InfinitePlace X.B.I.F) : psiV X u v 1 = 1 := by
  unfold psiV psiR
  simp [rootCoord_one X u v]

theorem single_mul (v : InfinitePlace X.B.I.F) (s t : Formalism.REAL.UJ (X.B.I.ε v)) :
    single X v (s * t) = single X v s * single X v t := by
  funext w
  by_cases h : w = v
  · subst h; simp [single]
  · simp [single, Function.update_of_ne h]

theorem single_mem_N (v : InfinitePlace X.B.I.F) {m : Formalism.REAL.UJ (X.B.I.ε v)} (hm : m ∈ Nloc X u v) :
    single X v m ∈ X.NinfU u := by
  intro w
  by_cases h : w = v
  · subst h; simp only [single, Function.update_self]; exact hm
  · simp only [single, Function.update_of_ne h, Pi.one_apply]
    refine ⟨inS_one, fun y _ => ?_⟩
    rw [uMat_one', sub_self, Matrix.zero_mulVec]; exact Submodule.zero_mem _

theorem single_mem_H (v : InfinitePlace X.B.I.F) {h : Formalism.REAL.UJ (X.B.I.ε v)} (hh : h ∈ Hloc X u v) :
    single X v h ∈ Hset X.B.I (Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.eX a)) ∪
      Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.fY a)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) := by
  intro w y hy
  by_cases hw : w = v
  · subst hw; simp only [single, Function.update_self]; exact hh y hy
  · simp only [single, Function.update_of_ne hw, Pi.one_apply, uMat_one', Matrix.one_mulVec]

theorem matW_single_ne (v w : InfinitePlace X.B.I.F) (hw : w ≠ v) (h : Formalism.REAL.UJ (X.B.I.ε v)) :
    matW X.B.I (X.wfr u w) w (single X v h) = 1 := by
  funext a b
  simp only [matW, single, Function.update_of_ne hw, Pi.one_apply, uMat_one', Matrix.one_mulVec, X.wfr_on,
    Matrix.one_apply]

theorem locEquiv (v : InfinitePlace X.B.I.F) (m : Formalism.REAL.UJ (X.B.I.ε v)) (hm : m ∈ Nloc X u v)
    (h : Formalism.REAL.UJ (X.B.I.ε v)) (hh : h ∈ Hloc X u v) (x : Formalism.REAL.UJ (X.B.I.ε v)) :
    X.Wloc u v (m * h * x) =
      psiV X u v (uMat (m * h)) • X.piLoc u v (matW X.B.I (X.wfr u v) v (single X v h)) (X.Wloc u v x) := by
  obtain ⟨x0, hx0⟩ := exists_Wu_ne X u
  have hne : ∀ w, X.Wloc u w (x0 w) ≠ 0 := by
    have : ∏ w, ‖X.Wloc u w (x0 w)‖ ≠ 0 := by rw [← norm_Wu]; exact norm_ne_zero_iff.2 hx0
    exact fun w => norm_ne_zero_iff.1 ((Finset.prod_ne_zero_iff.1 this) w (Finset.mem_univ w))
  set xx : X.B.I.Ginf := Function.update x0 v x with hxx
  set ξ0 : ∀ w, X.Vloc u w := fun w => X.Wloc u w (x0 w) with hξ0
  have hmS : m ∈ Sloc X u v := Nloc_sub X u v hm
  have hhS : h ∈ Sloc X u v := Hloc_sub X u v hh
  have hS : single X v (m * h) ∈ X.SinfU u := single_mem X u v (mul_mem_Sloc X u v hmS hhS)
  have hg := (X.Wu_spec u).1 (single X v (m * h)) hS xx
  have hpi : X.piU u (single X v (m * h)) = X.piU u (single X v h) := by
    rw [single_mul, (X.piU_rep u).2.1 _ (single_mem X u v hmS) _ (single_mem X u v hhS),
      (X.piU_rep u).2.2.2.1 _ (single_mem_N X u v hm), one_mul]
  have hpsi : psiInf X.B.I X.B.g (fun a => crdOf X.B.I X.ιE X.bas (X.eX a))
      (fun a => crdOf X.B.I X.ιE X.bas (X.fY a)) (crdOf X.B.I X.ιE X.bas (X.zu u)) (single X v (m * h)) =
      psiV X u v (uMat (m * h)) := by
    unfold psiInf
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
    have h1 : ∏ w ∈ Finset.univ.erase v, psiR (X.B.I.ε w) X.B.g (fun a => rv X.B.I w (X.eR a))
        (fun a => rv X.B.I w (X.fR a)) (rv X.B.I w (X.zR u)) (uMat (single X v (m * h) w)) = 1 := by
      refine Finset.prod_eq_one fun w hw => ?_
      simp only [single, Function.update_of_ne (Finset.ne_of_mem_erase hw), Pi.one_apply]
      exact psiV_one X u w
    rw [show (fun a => crdOf X.B.I X.ιE X.bas (X.eX a)) = X.eR from rfl,
      show (fun a => crdOf X.B.I X.ιE X.bas (X.fY a)) = X.fR from rfl,
      show crdOf X.B.I X.ιE X.bas (X.zu u) = X.zR u from rfl]
    rw [h1, mul_one]
    simp only [single, Function.update_self]
    rfl
  rw [hpi, hpsi, X.Wu_tens, X.Wu_tens, X.tensU_equiv u _ (single_mem_H X u v hh)] at hg
  have hL : (fun w => X.Wloc u w ((single X v (m * h) * xx) w)) =
      Function.update ξ0 v (X.Wloc u v (m * h * x)) := by
    funext w
    by_cases hw : w = v
    · subst hw; simp [single, hxx]
    · simp [single, hxx, hξ0, Function.update_of_ne hw]
  have hR : (fun w => X.piLoc u w (matW X.B.I (X.wfr u w) w (single X v h)) (X.Wloc u w (xx w))) =
      Function.update ξ0 v (X.piLoc u v (matW X.B.I (X.wfr u v) v (single X v h)) (X.Wloc u v x)) := by
    funext w
    by_cases hw : w = v
    · subst hw; simp [hxx]
    · rw [Function.update_of_ne hw, matW_single_ne X u v w hw, (X.piLoc_type u w).2.2.1.1.1]
      simp [hxx, hξ0, Function.update_of_ne hw]
  rw [hL, hR] at hg
  set a := X.piLoc u v (matW X.B.I (X.wfr u v) v (single X v h)) (X.Wloc u v x)
  have hsm : psiV X u v (uMat (m * h)) • X.tensU u (Function.update ξ0 v a) =
      X.tensU u (Function.update ξ0 v (psiV X u v (uMat (m * h)) • a)) := by
    have := tens_smul (X.tensU_inner u) (Function.update (fun _ => (1 : ℂ)) v (psiV X u v (uMat (m * h))))
      (Function.update ξ0 v a)
    rw [Finset.prod_update_of_mem (Finset.mem_univ v), Finset.prod_const_one, mul_one] at this
    rw [← this]
    congr 1
    funext w
    by_cases hw : w = v
    · subst hw; simp
    · simp [Function.update_of_ne hw]
  rw [hsm] at hg
  exact tens_update_inj (X.tensU_inner u) ξ0 v (fun w _ => hne w) _ _ hg

end LocEq

section LocCut

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def LocReprodW (v : InfinitePlace X.B.I.F) (W : Formalism.REAL.UJ (X.B.I.ε v) → X.Vloc u v) : Prop :=
  ∀ x, Integrable (fun g => Formalism.L2.SG.ProjRows.phLoc (X.B.σ v) (X.B.w v) (X.dv v) g • W (x * g))
      (Formalism.REAL.muG (X.B.I.ε v)) ∧
    ∫ g, Formalism.L2.SG.ProjRows.phLoc (X.B.σ v) (X.B.w v) (X.dv v) g • W (x * g) ∂(Formalism.REAL.muG (X.B.I.ε v)) = W x

def LocEquivW (v : InfinitePlace X.B.I.F) (W : Formalism.REAL.UJ (X.B.I.ε v) → X.Vloc u v) : Prop :=
  ∀ m ∈ Nloc X u v, ∀ h ∈ Hloc X u v, ∀ x,
    W (m * h * x) = psiV X u v (uMat (m * h)) • X.piLoc u v (matW X.B.I (X.wfr u v) v (single X v h)) (W x)

def LocConcl (v : InfinitePlace X.B.I.F) (νv : Measure (Formalism.REAL.UJ (X.B.I.ε v))) (W : Formalism.REAL.UJ (X.B.I.ε v) → X.Vloc u v) : Prop :=
  (∫⁻ x, ‖W x‖ₑ * ENNReal.ofReal (nuLocX X u v x ^ N1 X) ∂νv < ⊤) ∧
    ∃ (α : Formalism.REAL.UJ (X.B.I.ε v) → ℂ) (Ω : Set (Formalism.REAL.UJ (X.B.I.ε v))) (a : ℝ), IsCompact Ω ∧ 1 ∈ Ω ∧
      Measurable α ∧ (∀ y, α y ≠ 0 → y ∈ Ω) ∧ (∀ y, ‖α y‖ ≤ a) ∧
      ∀ x, Integrable (fun g => α g • W (x * g)) (Formalism.REAL.muG (X.B.I.ε v)) ∧
        ∫ g, α g • W (x * g) ∂(Formalism.REAL.muG (X.B.I.ε v)) = W x

end LocCut

def LocReprodStep : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (u : D.what₂.Word)
    (μS νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (C : ℝ≥0∞), QuotWit X u μS νl C →
      ∀ v, LocReprodW X u v (X.Wloc u v)

def LocUniqStep : Prop :=
  BesselNVGap → CoefWeightedLoc → WlocExists → Formalism.L2.SG.LocWSOf.BesselOfW → Formalism.L2.SG.LitS.BesselMultOne →
    ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (u : D.what₂.Word)
      (μS νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (C : ℝ≥0∞), QuotWit X u μS νl C →
      ∀ v (W : Formalism.REAL.UJ (X.B.I.ε v) → X.Vloc u v), Continuous W → LocEquivW X u v W → LocReprodW X u v W →
        ∫⁻ y, ‖W y‖ₑ ^ 2 ∂(νl v) ≠ 0 → ∫⁻ y, ‖W y‖ₑ ^ 2 ∂(νl v) ≠ ⊤ → LocConcl X u v (νl v) W

theorem locDecayStep_of (hB : BesselNVGap) (hC : CoefWeightedLoc) (hW : WlocExists)
    (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : Formalism.L2.SG.LitS.BesselMultOne)
    (hR : LocReprodStep) (hU : LocUniqStep) : LocDecayStep := by
  intro D hG X u μS νl C hQ v
  exact hU hB hC hW hBW hM1 D hG X u μS νl C hQ v (X.Wloc u v) (X.Wloc_cont u v)
    (fun m hm h hh x => locEquiv X u v m hm h hh x) (hR D hG X u μS νl C hQ v)
    (localRepresentationL2 X u hQ v).1 (localRepresentationL2 X u hQ v).2

theorem wuDecayOfGap_of_steps (hC : CoefWeightedLoc) (hQ : QuotAll) (hL : LocDecayStep) :
    Formalism.L2.SG.Pf.WuDecayOfGap := by
  intro D hG X
  refine ⟨fun u => ?_, phInt_of_gap X hC hG⟩
  obtain ⟨μS, νl, C, hW⟩ := hQ D X u
  have hLx := hL D hG X u μS νl C hW
  exact ⟨wuReprod_of_loc X u hLx, wuWeighted_of_loc X u hW hLx⟩

section QuotInst

open Formalism.L2.SG.Pf.WFL

theorem locHN_cast (hHN : LocHNProps) {k r n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool)
    (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (wf : Fin k → Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0) (hzw : ∀ a, hJ ε z (wf a) = 0) :
    IsClosed {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)} ∧
    IsCompact {g : Formalism.REAL.UJ ε | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ f a = f a) ∧ uMat g *ᵥ z = z} ∧
    ((1 : Formalism.REAL.UJ ε) ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)} ∧
      (∀ a ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}, ∀ b ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)},
        a * b ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}) ∧
      ∀ a ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}, a⁻¹ ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}) ∧
    (∀ h : Formalism.REAL.UJ ε, ((∀ a, uMat h *ᵥ e a = e a) ∧ (∀ a, uMat h *ᵥ f a = f a) ∧ uMat h *ᵥ z = z) →
      ∀ m : Formalism.REAL.UJ ε, InN ε e z (uMat m) → InN ε e z (uMat (h * m * h⁻¹))) := by
  subst hn
  have hc : (((Real.sqrt T)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : (Real.sqrt T)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hT).ne'
    exact_mod_cast this
  exact hHN k r ε e f wf (z0v T z) z _ (isFrameJ_of e f z wf hT hee hff hef hez hfz hzz hww hew hfw hzw) hc rfl

theorem nUnimod_cast (hNU : NUnimodLoc) {k r n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool)
    (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (wf : Fin k → Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0) (hzw : ∀ a, hJ ε z (wf a) = 0) :
    ∀ μ : Measure (Formalism.REAL.UJ ε), SigmaFinite μ → μ ≠ 0 → μ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}ᶜ = 0 →
      (∀ s ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}, μ.map (fun x => s * x) = μ) →
      ∀ s ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}, μ.map (fun x => x * s) = μ := by
  subst hn
  have hc : (((Real.sqrt T)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : (Real.sqrt T)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hT).ne'
    exact_mod_cast this
  exact hNU k r ε e f wf (z0v T z) z _ (isFrameJ_of e f z wf hT hee hff hef hez hfz hzz hww hew hfw hzw) hc rfl

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem Hloc_eq (v : InfinitePlace X.B.I.F) : Hloc X u v =
    {g : Formalism.REAL.UJ (X.B.I.ε v) | (∀ a, uMat g *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a)) ∧
      (∀ a, uMat g *ᵥ rv X.B.I v (X.fR a) = rv X.B.I v (X.fR a)) ∧
      uMat g *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u)} := by
  ext g
  constructor
  · intro hg
    exact ⟨fun a => hg _ (Or.inl (Or.inl ⟨a, rfl⟩)), fun a => hg _ (Or.inl (Or.inr ⟨a, rfl⟩)), hg _ (Or.inr rfl)⟩
  · rintro ⟨h1, h2, h3⟩ y hy
    rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hy
    · exact h1 a
    · exact h2 a
    · rw [Set.mem_singleton_iff] at hy; subst hy; exact h3

theorem quotProdX_of (hQK : QuotProdK) (hHN : LocHNProps) (hNU : NUnimodLoc) : QuotProdX X u := by
  have hT : (0 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
  have R := fun v => (Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v)
  have hee : ∀ v a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun v a b => by
    have := R v (X.eX a) (X.eX b); rw [X.ee, map_zero] at this; exact this
  have hff : ∀ v a b, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.fR b)) = 0 := fun v a b => by
    have := R v (X.fY a) (X.fY b); rw [X.ff, map_zero] at this; exact this
  have hef : ∀ v a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.fR b)) = if a = b then 1 else 0 :=
    fun v a b => by
      have := R v (X.eX a) (X.fY b); rw [X.ef] at this; rw [show X.eR a = X.crd (X.eX a) from rfl,
        show X.fR b = X.crd (X.fY b) from rfl, this]; split_ifs <;> simp
  have hez : ∀ v a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) = 0 := fun v a => by
    have := R v (X.eX a) (X.zu u); rw [(X.zu_orth u a).1, map_zero] at this; exact this
  have hfz : ∀ v a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0 := fun v a => by
    have := R v (X.fY a) (X.zu u); rw [(X.zu_orth u a).2, map_zero] at this; exact this
  have hzz : ∀ v, hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) = -(((D.mem u).A.T : ℝ) : ℂ) :=
    fun v => by
      have := R v (X.zu u) (X.zu u); rw [X.zu_norm, map_neg, map_natCast] at this
      rw [show X.zR u = X.crd (X.zu u) from rfl, this]; push_cast; rfl
  have hww := fun v => X.wfr_on u v
  have hew : ∀ v c a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR c)) (X.wfr u v a) = 0 := fun v c a => ((X.wfr_perp u v a).1 c).1
  have hfw : ∀ v c a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR c)) (X.wfr u v a) = 0 := fun v c a => ((X.wfr_perp u v a).1 c).2
  have hzw : ∀ v a, hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (X.wfr u v a) = 0 := fun v a => (X.wfr_perp u v a).2
  have hP := fun v => locHN_cast hHN (hdim X) (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
    (rv X.B.I v (X.zR u)) (X.wfr u v) hT (hee v) (hff v) (hef v) (hez v) (hfz v) (hzz v) (hww v) (hew v) (hfw v) (hzw v)
  have hU := fun v => nUnimod_cast hNU (hdim X) (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a))
    (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) (X.wfr u v) hT (hee v) (hff v) (hef v) (hez v) (hfz v)
    (hzz v) (hww v) (hew v) (hfw v) (hzw v)
  have hpiN : Set.pi Set.univ (Nloc X u) = X.NinfU u := by ext s; simp [Set.mem_pi, Nloc, HidaSetting.NinfU, Ninf]
  have hpiH : Set.pi Set.univ (Hloc X u) = Hset X.B.I (Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.eX a)) ∪
      Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.fY a)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) := by
    ext s; simp only [Set.mem_pi, Set.mem_univ, true_implies]; rfl
  have hN := X.muN_haar u
  have hH := X.muH_haar u
  obtain ⟨h1, h2, h3, h4⟩ := hN
  obtain ⟨k1, k2, k3, k4⟩ := hH
  obtain ⟨μS, νl, C, hC0, hCt, hloc, hK⟩ := hQK (InfinitePlace X.B.I.F) (fun _ => X.B.I.n) X.B.I.ε (Nloc X u) (Hloc X u)
    (fun v => (hP v).1) (fun v => by rw [Hloc_eq]; exact (hP v).2.1) (fun v => (hP v).2.2.1)
    (fun v => by
      rw [Hloc_eq]
      exact ⟨fix_one, fun a ha b hb => fix_mul ha hb, fun a ha => fix_inv ha⟩)
    (fun v h hh m hm => (hP v).2.2.2 h (by rw [Hloc_eq] at hh; exact hh) m hm)
    (fun v μ a1 a2 a3 a4 => hU v μ a1 a2 a3 a4)
    (X.muN u) (X.muH u) (X.nuQ u)
    ⟨h1, h2, by rw [hpiN]; exact h3, by rw [hpiN]; exact h4⟩
    ⟨k1, k2, by rw [hpiH]; exact k3, by rw [hpiH]; exact k4⟩ (X.nuQ_weil u)
  exact ⟨μS, νl, C, hC0, hCt, hloc, hK⟩

theorem quotAll_of (hQK : QuotProdK) (hHN : LocHNProps) (hNU : NUnimodLoc) : QuotAll :=
  fun _ X u => quotProdX_of X u hQK hHN hNU

end QuotInst

section Tens2

variable {ι : Type} [Fintype ι] {V : ι → Type} [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
  {Vπ : Type} [NormedAddCommGroup Vπ] [InnerProductSpace ℂ Vπ] {tens : (∀ v, V v) → Vπ}

theorem inner_tens_update2 [DecidableEq ι] (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (p q : ∀ v, V v)
    (v : ι) (a b : V v) :
    ⟪tens (Function.update p v a), tens (Function.update q v b)⟫_ℂ =
      ⟪a, b⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪p w, q w⟫_ℂ := by
  rw [hi, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v), Function.update_self, Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw), Function.update_of_ne (Finset.ne_of_mem_erase hw)]

end Tens2

section Scalar

open Classical

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

abbrev Pv (v : InfinitePlace X.B.I.F) : Formalism.REAL.UJ (X.B.I.ε v) → ℂ :=
  Formalism.L2.SG.ProjRows.phLoc (X.B.σ v) (X.B.w v) (X.dv v)

theorem ph_eq_prod (y : X.B.I.Ginf) : X.ph y = ∏ v, Pv X v (y v) := by
  simp only [HidaSetting.ph, Formalism.L2.SG.ProjRows.phInf, Formalism.L2.SG.ProjRows.mInf, Pv, Formalism.L2.SG.ProjRows.phLoc]
  rw [Finset.prod_mul_distrib, Complex.ofReal_prod]
  congr 1
  exact map_prod (starRingEnd ℂ) _ _

theorem continuous_Pv (v : InfinitePlace X.B.I.F) : Continuous (Pv X v) := by
  have hc := (X.ds v).2.2.1.2.2 (X.B.w v)
  have h2 : Continuous fun g : Formalism.REAL.UJ (X.B.I.ε v) => X.B.σ v (uMat g) (X.B.w v) :=
    hc.comp_continuous Formalism.L2.SG.WuDecayPf.continuous_uMat (fun g => g.2)
  exact continuous_const.mul (continuous_star.comp (continuous_const.inner h2))

def Gl (x : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) (t : Formalism.REAL.UJ (X.B.I.ε v)) : X.Vloc u v :=
  Pv X v t • X.Wloc u v (x v * t)

theorem continuous_Gl (x : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) : Continuous (Gl X u x v) :=
  (continuous_Pv X v).smul ((X.Wloc_cont u v).comp (continuous_const.mul continuous_id))

theorem integrand_eq (x y : X.B.I.Ginf) : X.ph y • X.Wu u (x * y) = X.tensU u (fun w => Gl X u x w (y w)) := by
  rw [ph_eq_prod, X.Wu_tens, ← tens_smul (X.tensU_inner u)]
  rfl

theorem lint_prod (x : X.B.I.Ginf) :
    ∫⁻ y, ‖X.ph y • X.Wu u (x * y)‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
      ∏ w, ∫⁻ t, ‖Gl X u x w t‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε w)) := by
  have h1 : ∀ y, ‖X.ph y • X.Wu u (x * y)‖ₑ = ∏ w, ‖Gl X u x w (y w)‖ₑ := by
    intro y
    rw [integrand_eq, ← ofReal_norm, norm_tens (X.tensU_inner u),
      ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
    simp only [ofReal_norm]
  simp only [h1]
  exact Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.lintegral_pi_prod _ _ fun w => (continuous_Gl X u x w).enorm.measurable

theorem lint_prod_lt (x : X.B.I.Ginf) : ∏ w, ∫⁻ t, ‖Gl X u x w t‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε w)) < ⊤ := by
  rw [← lint_prod]; exact ((X.Wu_spec u).2.1 x).1.2

theorem lint_ne_zero {x : X.B.I.Ginf} (hx : X.Wu u x ≠ 0) (w : InfinitePlace X.B.I.F) :
    ∫⁻ t, ‖Gl X u x w t‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε w)) ≠ 0 := by
  intro h0
  have hP : ∏ w, ∫⁻ t, ‖Gl X u x w t‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε w)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ w) h0
  rw [← lint_prod] at hP
  have hae : (fun y => X.ph y • X.Wu u (x * y)) =ᵐ[Formalism.L2.SG.ProjRows.muInf X.B.I] 0 := by
    have hm : AEMeasurable (fun y => ‖X.ph y • X.Wu u (x * y)‖ₑ) (Formalism.L2.SG.ProjRows.muInf X.B.I) :=
      ((X.Wu_spec u).2.1 x).1.1.enorm
    have := (lintegral_eq_zero_iff' hm).1 hP
    filter_upwards [this] with y hy
    simpa using hy
  have h2 : ∫ y, X.ph y • X.Wu u (x * y) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = X.Wu u x := ((X.Wu_spec u).2.1 x).2
  rw [integral_congr_ae hae] at h2
  simp only [Pi.zero_apply, integral_zero] at h2
  exact hx h2.symm

theorem locReprod_scalar (v : InfinitePlace X.B.I.F) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ xv : Formalism.REAL.UJ (X.B.I.ε v),
      Integrable (fun g => Pv X v g • X.Wloc u v (xv * g)) (Formalism.REAL.muG (X.B.I.ε v)) ∧
      ∫ g, Pv X v g • X.Wloc u v (xv * g) ∂(Formalism.REAL.muG (X.B.I.ε v)) = c • X.Wloc u v xv := by
  obtain ⟨x0, hx0⟩ := exists_Wu_ne X u
  have hne : ∀ w, X.Wloc u w (x0 w) ≠ 0 := by
    have : ∏ w, ‖X.Wloc u w (x0 w)‖ ≠ 0 := by rw [← norm_Wu]; exact norm_ne_zero_iff.2 hx0
    exact fun w => norm_ne_zero_iff.1 ((Finset.prod_ne_zero_iff.1 this) w (Finset.mem_univ w))

  set I : ∀ w, ℝ≥0∞ := fun w => ∫⁻ t, ‖Gl X u x0 w t‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε w)) with hIdef
  have hI0 : ∀ w, I w ≠ 0 := lint_ne_zero X u hx0
  have hIt : ∀ w, I w ≠ ⊤ := by
    intro w htop
    have h := lint_prod_lt X u x0
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)] at h
    have : I w * ∏ w' ∈ Finset.univ.erase w, I w' = ⊤ := by
      rw [htop]; exact ENNReal.top_mul (Finset.prod_ne_zero_iff.2 fun w' _ => hI0 w')
    exact (lt_irrefl _ (this ▸ h))
  have hint0 : ∀ w, Integrable (Gl X u x0 w) (Formalism.REAL.muG (X.B.I.ε w)) := fun w =>
    ⟨(continuous_Gl X u x0 w).aestronglyMeasurable, lt_top_iff_ne_top.2 (hIt w)⟩

  have hintv : ∀ xv : Formalism.REAL.UJ (X.B.I.ε v),
      Integrable (Gl X u (Function.update x0 v xv) v) (Formalism.REAL.muG (X.B.I.ε v)) := by
    intro xv
    refine ⟨(continuous_Gl X u _ v).aestronglyMeasurable, lt_top_iff_ne_top.2 fun htop => ?_⟩
    have h := lint_prod_lt X u (Function.update x0 v xv)
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v)] at h
    have hrest : ∏ w ∈ Finset.univ.erase v, ∫⁻ t, ‖Gl X u (Function.update x0 v xv) w t‖ₑ
        ∂(Formalism.REAL.muG (X.B.I.ε w)) = ∏ w ∈ Finset.univ.erase v, I w := by
      refine Finset.prod_congr rfl fun w hw => ?_
      simp only [hIdef, Gl, Function.update_of_ne (Finset.ne_of_mem_erase hw)]
    rw [hrest] at h
    have : (∫⁻ t, ‖Gl X u (Function.update x0 v xv) v t‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε v))) *
        ∏ w ∈ Finset.univ.erase v, I w = ⊤ := by
      rw [htop]; exact ENNReal.top_mul (Finset.prod_ne_zero_iff.2 fun w' _ => hI0 w')
    exact (lt_irrefl _ (this ▸ h))
  have hGv : ∀ xv : Formalism.REAL.UJ (X.B.I.ε v), Gl X u (Function.update x0 v xv) v =
      fun g => Pv X v g • X.Wloc u v (xv * g) := by
    intro xv; funext g; simp [Gl]

  set L0 : ∀ w, X.Vloc u w := fun w => ∫ t, Gl X u x0 w t ∂(Formalism.REAL.muG (X.B.I.ε w)) with hL0
  set W0 : ∀ w, X.Vloc u w := fun w => X.Wloc u w (x0 w) with hW0
  have key : ∀ xv : Formalism.REAL.UJ (X.B.I.ε v),
      X.tensU u (Function.update L0 v (∫ g, Pv X v g • X.Wloc u v (xv * g) ∂(Formalism.REAL.muG (X.B.I.ε v)))) =
        X.tensU u (Function.update W0 v (X.Wloc u v xv)) := by
    intro xv
    set xx := Function.update x0 v xv
    have hG : ∀ w, Integrable (Gl X u xx w) (Formalism.REAL.muG (X.B.I.ε w)) := by
      intro w
      by_cases hw : w = v
      · subst hw; exact hintv xv
      · have : Gl X u xx w = Gl X u x0 w := by funext t; simp [Gl, xx, Function.update_of_ne hw]
        rw [this]; exact hint0 w
    have hT := integrable_and_integral_pi_apply (InfinitePlace X.B.I.F) (fun w => Formalism.REAL.UJ (X.B.I.ε w))
      (fun w => Formalism.REAL.muG (X.B.I.ε w)) (X.Vloc u) (X.Vpi u) (X.tensU u) (X.tensU_inner u) (X.tensU_span u)
      (Gl X u xx) hG
    have hglob : ∫ y, X.ph y • X.Wu u (xx * y) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = X.Wu u xx :=
      ((X.Wu_spec u).2.1 xx).2
    have hfun : (fun y : X.B.I.Ginf => X.ph y • X.Wu u (xx * y)) = fun y => X.tensU u (fun w => Gl X u xx w (y w)) := by
      funext y; exact integrand_eq X u xx y
    rw [hfun, hT.2, X.Wu_tens] at hglob
    have e1 : (fun w => ∫ t, Gl X u xx w t ∂(Formalism.REAL.muG (X.B.I.ε w))) =
        Function.update L0 v (∫ g, Pv X v g • X.Wloc u v (xv * g) ∂(Formalism.REAL.muG (X.B.I.ε v))) := by
      funext w
      by_cases hw : w = v
      · subst hw; simp only [Function.update_self]; rw [hGv]
      · simp only [Function.update_of_ne hw, hL0]
        congr 1; funext t; simp [Gl, xx, Function.update_of_ne hw]
    have e2 : (fun w => X.Wloc u w (xx w)) = Function.update W0 v (X.Wloc u v xv) := by
      funext w
      by_cases hw : w = v
      · subst hw; simp [xx]
      · simp [xx, hW0, Function.update_of_ne hw]
    rw [e1, e2] at hglob
    exact hglob

  set A : ℂ := ∏ w ∈ Finset.univ.erase v, ⟪W0 w, L0 w⟫_ℂ with hA
  set Bc : ℂ := ∏ w ∈ Finset.univ.erase v, ⟪W0 w, W0 w⟫_ℂ with hBc
  have hBc0 : Bc ≠ 0 := Finset.prod_ne_zero_iff.2 fun w _ => inner_self_ne_zero.2 (hne w)
  have hlin : ∀ xv : Formalism.REAL.UJ (X.B.I.ε v),
      A • (∫ g, Pv X v g • X.Wloc u v (xv * g) ∂(Formalism.REAL.muG (X.B.I.ε v))) = Bc • X.Wloc u v xv := by
    intro xv
    refine ext_inner_left ℂ fun ξ => ?_
    have h1 := congrArg (fun t => ⟪X.tensU u (Function.update W0 v ξ), t⟫_ℂ) (key xv)
    simp only [inner_tens_update2 (X.tensU_inner u)] at h1
    rw [inner_smul_right, inner_smul_right]
    rw [hA, hBc]
    linear_combination h1
  have hA0 : A ≠ 0 := by
    intro h0
    have := hlin (x0 v)
    rw [h0, zero_smul] at this
    exact hne v ((smul_eq_zero.1 this.symm).resolve_left hBc0)
  refine ⟨Bc / A, div_ne_zero hBc0 hA0, fun xv => ⟨by rw [← hGv]; exact hintv xv, ?_⟩⟩
  have h3 := hlin xv
  calc ∫ g, Pv X v g • X.Wloc u v (xv * g) ∂(Formalism.REAL.muG (X.B.I.ε v))
      = A⁻¹ • (A • ∫ g, Pv X v g • X.Wloc u v (xv * g) ∂(Formalism.REAL.muG (X.B.I.ε v))) := by
        rw [smul_smul, inv_mul_cancel₀ hA0, one_smul]
    _ = (Bc / A) • X.Wloc u v xv := by rw [h3, smul_smul, div_eq_inv_mul]

end Scalar

def LocScalarStep : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (u : D.what₂.Word)
    (μS νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (C : ℝ≥0∞), QuotWit X u μS νl C →
      ∀ (v : InfinitePlace X.B.I.F) (c : ℂ), c ≠ 0 →
        (∀ xv : Formalism.REAL.UJ (X.B.I.ε v),
          Integrable (fun g => Pv X v g • X.Wloc u v (xv * g)) (Formalism.REAL.muG (X.B.I.ε v)) ∧
          ∫ g, Pv X v g • X.Wloc u v (xv * g) ∂(Formalism.REAL.muG (X.B.I.ε v)) = c • X.Wloc u v xv) → c = 1

theorem locReprodStep_of (hS : LocScalarStep) : LocReprodStep := by
  intro D hG X u μS νl C hQ v
  obtain ⟨c, hc0, hc⟩ := locReprod_scalar X u v
  have h1 : c = 1 := hS D hG X u μS νl C hQ v c hc0 hc
  intro xv
  refine ⟨(hc xv).1, ?_⟩
  rw [(hc xv).2, h1, one_smul]

theorem wuDecay_of_gap_steps (hB : BesselNVGap) (hC : CoefWeightedLoc) (hW : WlocExists)
    (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : Formalism.L2.SG.LitS.BesselMultOne)
    (hQ : QuotAll) (hR : LocReprodStep) (hU : LocUniqStep) : Formalism.L2.SG.Pf.WuDecayOfGap :=
  wuDecayOfGap_of_steps hC hQ (locDecayStep_of hB hC hW hBW hM1 hR hU)

theorem wuDecay_of_gap (hB : BesselNVGap) (hC : CoefWeightedLoc) (hW : WlocExists)
    (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : Formalism.L2.SG.LitS.BesselMultOne)
    (hQK : Formalism.L2.SG.Pf.WFL.QuotProdK) (hHN : Formalism.L2.SG.Pf.WFL.LocHNProps) (hNU : Formalism.L2.SG.Pf.WFL.NUnimodLoc)
    (hR : LocReprodStep) (hU : LocUniqStep) : Formalism.L2.SG.Pf.WuDecayOfGap :=
  wuDecay_of_gap_steps hB hC hW hBW hM1 (quotAll_of hQK hHN hNU) hR hU

end Formalism.L2.SG.Pf.WuDec

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.Pf.WuDec

theorem wuDecay_of_gap (hB : BesselNVGap) (hC : CoefWeightedLoc) (hW : WlocExists)
    (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : Formalism.L2.SG.LitS.BesselMultOne)
    (hQK : Formalism.L2.SG.Pf.WFL.QuotProdK) (hHN : Formalism.L2.SG.Pf.WFL.LocHNProps) (hNU : Formalism.L2.SG.Pf.WFL.NUnimodLoc)
    (hS : LocScalarStep) (hU : LocUniqStep) : WuDecayOfGap :=
  WuDec.wuDecay_of_gap_steps hB hC hW hBW hM1 (quotAll_of hQK hHN hNU)
    (locReprodStep_of hS) hU

end Formalism.L2.SG.Pf
