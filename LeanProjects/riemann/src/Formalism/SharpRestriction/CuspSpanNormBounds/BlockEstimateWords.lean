import Formalism.SharpRestriction.CuspSpanNormBounds.RadialGaugeOfGaugeIdentitySlices
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateTheorem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PoissonSummationDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PsdFormConjRewrite
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualCovolumeChangeOfVariables

section PartDefs

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Defs

variable {D : D7} {k0 : ℕ} (G : GramWordSpace.GramMap k0 D.R.rS) (X : GramWordSpace.Dat D k0)
  (a : ℕ → ℕ → D.what₂.Tau → ℂ) (cb : ℕ → ℕ → ℝ) (c0 : ℝ) (χ : ℝ → ℝ)

def tau (i s : ℕ) (t : D.host.E) : D.what₂.Tau → ℂ := fun v => a i s v * plEmb D v t

def lbF (v : D.what₂.Tau) : ℕ → TA.Pt D.host.E → List (ℂ × ℕ)
  | _, [] => []
  | o, (s, t) :: bs => (a (o + 1) s v * plEmb D v t, s) :: lbF v (o + s) bs

def wB (v : D.what₂.Tau) (o s : ℕ) (τ : ℂ) : ℝ := if X.okT v o s τ then X.wt v o s τ else 0

def wF (v : D.what₂.Tau) : ℕ → TA.Pt D.host.E → ℝ
  | _, [] => 1
  | o, (s, t) :: bs => wB X v o s (a (o + 1) s v * plEmb D v t) * wF v (o + s) bs

def nF : ℕ → TA.Pt D.host.E → ℝ
  | _, [] => 1
  | o, (s, _) :: bs => Real.sqrt (cb (o + 1) s) * nF (o + s) bs

def sc (p : TA.Pt D.host.E) : ℝ := nF (D := D) cb 0 p * ∏ v, wF X a v 0 p

theorem lbF_ok (ha : ∀ i s v, a i s v ≠ 0) (v : D.what₂.Tau) (p : TA.Pt D.host.E) :
    ∀ o, (∀ b ∈ p, 1 ≤ b.1 ∧ b.2 ≠ 0) → (∀ b ∈ lbF a v o p, b.1 ≠ 0 ∧ 1 ≤ b.2) ∧
      ((lbF a v o p).map Prod.snd).sum = TA.lvl p := by
  induction p with
  | nil => intro o _; simp [lbF, TA.lvl]
  | cons b bs ih =>
    intro o h
    obtain ⟨s, t⟩ := b
    have hb := h (s, t) (by simp)
    obtain ⟨i1, i2⟩ := ih (o + s) (fun b hb => h b (by simp [hb]))
    refine ⟨fun c hc => ?_, ?_⟩
    · simp only [lbF, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact ⟨mul_ne_zero (ha _ _ _) ((map_ne_zero (plEmb D v)).2 hb.2), hb.1⟩
      · exact i1 c hc
    · simp only [lbF, List.map_cons, List.sum_cons, i2, TA.lvl]

def lpt (ha : ∀ i s v, a i s v ≠ 0) (j : ℕ) (p : TA.Pt D.host.E) : GramWordSpace.Head D j := fun v =>
  if h : TA.IsPt j p then ⟨lbF a v 0 p, (lbF_ok a ha v p 0 h.2).1, by rw [(lbF_ok a ha v p 0 h.2).2]; exact h.1⟩
  else dflt j

def Gk (ha : ∀ i s v, a i s v ≠ 0) (eps : ℝ) (w : GramWordSpace.GWord D) (j : ℕ) (p p' : TA.Pt D.host.E) : ℂ :=
  ((c0 * (sc X a cb p * sc X a cb p') : ℝ) : ℂ) *
    (∏ v, GramWordSpace.gram G X v j (w v) (X.Fv χ eps v) (lpt a ha j p v) (lpt a ha j p' v)) / (X.brk w : ℂ)

def GkLim (p p' : TA.Pt D.host.E) : ℂ :=
  ((c0 * (sc X a cb p * sc X a cb p') : ℝ) : ℂ) *
    ∏ v, hsInner (G.V (X.B v) (X.f v) (lbF a v 0 p)) (G.V (X.B v) (X.f v) (lbF a v 0 p'))

def w00 : GramWordSpace.GWord D := fun _ => []

def glen (w : GramWordSpace.GWord D) : ℕ := Finset.univ.sup fun v => (w v).length

def embA (i s : ℕ) : D.host.E →+ (D.what₂.Tau → ℂ) where
  toFun := tau a i s
  map_zero' := by funext v; simp [tau]
  map_add' := fun x y => by funext v; simp [tau, mul_add]

def laC (L : LatticeDataWithDual D) (i s : ℕ) : AddSubgroup (D.what₂.Tau → ℂ) := (L.La i s).toAddSubgroup.map (embA a i s)

def sgm (δ : D.host.E) (i s : ℕ) (l : D.host.E) : D.what₂.Tau → ℂ :=
  fun v => 2 * (Real.pi : ℂ) * Complex.I * plEmb D v (l / δ) / a i s v

def aDual (δ : D.host.E) (i s : ℕ) : D.what₂.Tau → ℂ :=
  fun v => 2 * (Real.pi : ℂ) * Complex.I / (plEmb D v δ * a i s v)

end Defs

end Formalism.MainNotions.BlockEstimateWords

end

end PartDefs

section PartDefs2

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

structure Mod (D : D7) {k0 : ℕ} (X : GramWordSpace.Dat D k0) (a : ℕ → ℕ → D.what₂.Tau → ℂ) (cb : ℕ → ℕ → ℝ) (c0 : ℝ)
    (Ks : ℕ) (E₀ Eg E₁ E₂ E₃ C C4 T T' : ℝ) (δ : D.host.E) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D)
    (κL : ℕ → ℕ → ℝ) : Prop where
  std : X.Std Ks E₀ Eg
  δ_ne : δ ≠ 0
  a_ne : ∀ i s v, a i s v ≠ 0
  cb_pos : ∀ i s, 0 < cb i s
  lowerConstantNonneg : 0 ≤ c0
  brk_pos : ∀ w, X.admitted w → 0 < X.brk w
  xi_nn : ∀ i v, 0 ≤ X.xi E₁ E₂ Ks i v
  blockSizeNonneg : ∀ j0 s v, 0 ≤ GramWordSpace.blockLiftThreshold X E₁ E₂ Ks j0 s v
  thr1 : ∀ i v, 1 ≤ i → i ≤ D.R.rS + 1 →
    X.xi E₁ E₂ Ks i v * ‖a i 1 v‖ ≤ kaV D δ v * szX D C C (Nlet D Ks) T T' δ x i v
  thr3 : ∀ i s v, 1 ≤ s → s ≤ i → i ≤ D.R.rS + 1 → ¬ (i = D.R.rS + 1 ∧ s = 1) →
    GramWordSpace.blockLiftThreshold X E₁ E₂ Ks (i - s) s v * ‖a (i - s + 1) s v‖ ≤ thr3 D C C (Nlet D Ks) T T' δ x i s v
  lat : ∀ b s, IsBlockSL2Embedding D b s → GramWordSpace.IsLat D (laC a L b s) (κL b s)
  dual : ∀ b s, IsBlockSL2Embedding D b s → ∀ σ ∈ GramWordSpace.dualS D (laC a L b s), ∃ l ∈ dualPsi D δ (L.La b s), σ = sgm a δ b s l
  dualV : ∀ b s, IsBlockSL2Embedding D b s → dualPsi D δ (L.La b s) ⊆ (L.aaV b s : Set D.host.E)
  cb1 : ∀ i, 1 ≤ i → i ≤ D.R.rS + 1 → cb i 1 = κL i 1
  blockProductBound : ∀ b s, 2 ≤ s → IsBlockSL2Embedding D b s →
    ∏ v, X.abelian₂ E₁ E₂ Ks s b v ≤ Real.sqrt (GramWordSpace.scNorm D (aDual a δ b s) (L.aaV b s))
  blockSL2Embedding_bound : ∀ b s, 2 ≤ s → IsBlockSL2Embedding D b s →
    cb b s / κL b s * (E₃ ^ (D.R.f * s) * ∏ s' ∈ Finset.Ico 1 s, ∏ v, X.LamG E₁ E₂ Ks s' b v ^ 2) ≤
      bdB D C C (Nlet D Ks) T T' δ x L C4 (b + s - 1) s

def PoissonPi (D : D7) : Prop :=
  ∀ (La : AddSubgroup (D.what₂.Tau → ℂ)) (κ : ℝ), GramWordSpace.IsLat D La κ →
    ∀ (φ : (D.what₂.Tau → ℂ) → ℝ) (Cφ : ℝ), Continuous φ → (∀ t, |φ t| ≤ Cφ * ∏ v, ((1 + ‖t v‖) ^ 3)⁻¹) → (∀ t, 0 ≤ φ t) →
    ∀ (t₀ : D.what₂.Tau → ℂ) (B : ℝ),
      (∀ S : Finset (D.what₂.Tau → ℂ), (∀ σ ∈ S, σ ∈ GramWordSpace.dualS D La ∧ σ ≠ 0) →
        ∑ σ ∈ S, ‖∫ t, ((φ t : ℝ) : ℂ) * ∏ v, TopsChoicePartA.fsC (σ v) (t v)‖ ≤ B) →
      ∀ S : Finset (D.what₂.Tau → ℂ), (∀ z ∈ S, z ∈ La) →
        κ * ∑ z ∈ S, φ (t₀ + z) ≤ ‖∫ t, ((φ t : ℝ) : ℂ)‖ + B

section Iface

variable {D : D7} {k0 : ℕ} (G : GramWordSpace.GramMap k0 D.R.rS) (X : GramWordSpace.Dat D k0)
  (a : ℕ → ℕ → D.what₂.Tau → ℂ) (cb : ℕ → ℕ → ℝ) (c0 : ℝ) (χ : ℝ → ℝ)

def WOK (Ks : ℕ) (w : GramWordSpace.GWord D) : Prop := X.admitted w ∧ GramWordSpace.Len (GramWordSpace.NN D Ks) w

def hdS (ha : ∀ i s v, a i s v ≠ 0) (j0 : ℕ) (Hd : Finset (TA.Pt D.host.E)) : Hd → GramWordSpace.Head D j0 :=
  fun h => lpt a ha j0 h.1

def kapS (Hd : Finset (TA.Pt D.host.E)) (kap : TA.Pt D.host.E → TA.Pt D.host.E → ℂ) : Hd → Hd → ℂ :=
  fun x y => kap y.1 x.1 * ((c0 * (sc X a cb x.1 * sc X a cb y.1) : ℝ) : ℂ)

def GramId (ha : ∀ i s v, a i s v ≠ 0) (Ks : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ : ℝ → GramWordSpace.GWord D → TA.Pt D.host.E → H) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∀ w, WOK X Ks w → ∀ j, j ≤ D.R.rS + 1 → ∀ p p', TA.IsPt j p → TA.IsPt j p' →
    ⟪Φ eps w p, Φ eps w p'⟫_ℂ = Gk G X a cb c0 χ ha eps w j p' p

def trS (ha : ∀ i s v, a i s v ≠ 0) (δ : D.host.E) (eps : ℝ) (i : ℕ) (w : GramWordSpace.GWord D) (Hd : Finset (TA.Pt D.host.E))
    (kap : TA.Pt D.host.E → TA.Pt D.host.E → ℂ) (l : D.host.E) : ℂ :=
  GramWordSpace.Ntr G X (i - 1) w χ eps (hdS a ha (i - 1) Hd) (kapS X a cb c0 Hd kap) (sgm a δ i 1 l)

def pat1S (δ : D.host.E) (E₁ E₂ : ℝ) (Ks : ℕ) (i : ℕ) (l : D.host.E) : Set D.what₂.Tau :=
  {v | X.xi E₁ E₂ Ks i v < ‖sgm a δ i 1 l v‖}

end Iface

end Formalism.MainNotions.BlockEstimateWords

end

end PartDefs2

section PartE0

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Append

variable {D : D7} {k0 : ℕ} (X : GramWordSpace.Dat D k0) (a : ℕ → ℕ → D.what₂.Tau → ℂ) (cb : ℕ → ℕ → ℝ)

theorem lbF_append (v : D.what₂.Tau) (h : TA.Pt D.host.E) (s : ℕ) (t : D.host.E) :
    ∀ o, lbF a v o (h ++ [(s, t)]) = lbF a v o h ++ [(a (o + TA.lvl h + 1) s v * plEmb D v t, s)] := by
  induction h with
  | nil => intro o; simp [lbF, TA.lvl]
  | cons b bs ih =>
    intro o
    obtain ⟨s', t'⟩ := b
    have e : o + TA.lvl ((s', t') :: bs) = o + s' + TA.lvl bs := by simp [TA.lvl]; ring
    simp only [List.cons_append, lbF, ih (o + s'), e]

theorem wF_append (v : D.what₂.Tau) (h : TA.Pt D.host.E) (s : ℕ) (t : D.host.E) :
    ∀ o, wF X a v o (h ++ [(s, t)]) =
      wF X a v o h * wB X v (o + TA.lvl h) s (a (o + TA.lvl h + 1) s v * plEmb D v t) := by
  induction h with
  | nil => intro o; simp [wF, TA.lvl]
  | cons b bs ih =>
    intro o
    obtain ⟨s', t'⟩ := b
    have e : o + TA.lvl ((s', t') :: bs) = o + s' + TA.lvl bs := by simp [TA.lvl]; ring
    simp only [List.cons_append, wF, ih (o + s'), e, mul_assoc]

theorem nF_append (h : TA.Pt D.host.E) (s : ℕ) (t : D.host.E) :
    ∀ o, nF (D := D) cb o (h ++ [(s, t)]) = nF (D := D) cb o h * Real.sqrt (cb (o + TA.lvl h + 1) s) := by
  induction h with
  | nil => intro o; simp [nF, TA.lvl]
  | cons b bs ih =>
    intro o
    obtain ⟨s', t'⟩ := b
    have e : o + TA.lvl ((s', t') :: bs) = o + s' + TA.lvl bs := by simp [TA.lvl]; ring
    simp only [List.cons_append, nF, ih (o + s'), e, mul_assoc]

theorem sc_ext {j0 : ℕ} {h : TA.Pt D.host.E} (hh : TA.IsPt j0 h) (s : ℕ) (t : D.host.E) :
    sc X a cb (TA.ext h s t) =
      sc X a cb h * (Real.sqrt (cb (j0 + 1) s) * ∏ v, wB X v j0 s (tau a (j0 + 1) s t v)) := by
  have hl : TA.lvl h = j0 := hh.1
  unfold sc TA.ext
  rw [nF_append]
  simp only [wF_append, zero_add, hl, Finset.prod_mul_distrib, tau]
  ring

theorem tau_ne (ha : ∀ i s v, a i s v ≠ 0) (i s : ℕ) {t : D.host.E} (ht : t ≠ 0) (v : D.what₂.Tau) :
    tau a i s t v ≠ 0 := mul_ne_zero (ha _ _ _) ((map_ne_zero (plEmb D v)).2 ht)

theorem lpt_val (ha : ∀ i s v, a i s v ≠ 0) {j : ℕ} {p : TA.Pt D.host.E} (h : TA.IsPt j p) (v : D.what₂.Tau) :
    (lpt a ha j p v).1 = lbF a v 0 p := by
  simp [lpt, h]

theorem lpt_ext (ha : ∀ i s v, a i s v ≠ 0) {j0 s : ℕ} {h : TA.Pt D.host.E} (hh : TA.IsPt j0 h) (hs : 1 ≤ s)
    {t : D.host.E} (ht : t ≠ 0) (v : D.what₂.Tau) :
    lpt a ha (j0 + s) (TA.ext h s t) v =
      GramWordSpace.snoc (lpt a ha j0 h v) (tau a (j0 + 1) s t v) (tau_ne a ha _ _ ht v) s hs := by
  have h2 : TA.IsPt (j0 + s) (TA.ext h s t) := isPt_ext hh hs ht
  apply Subtype.ext
  have hl : TA.lvl h = j0 := hh.1
  rw [lpt_val a ha h2]
  show _ = (lpt a ha j0 h v).1 ++ [(tau a (j0 + 1) s t v, s)]
  rw [lpt_val a ha hh]
  simp only [TA.ext, lbF_append, zero_add, hl, tau]

end Append

theorem sum_sub {α : Type} (P : Finset α) (F : α → α → ℂ) :
    (∑ h : P, ∑ h' : P, F h.1 h'.1) = ∑ h ∈ P, ∑ h' ∈ P, F h h' := by
  rw [← Finset.sum_coe_sort P (fun h => ∑ h' ∈ P, F h h')]
  exact Finset.sum_congr rfl fun h _ => Finset.sum_coe_sort P (fun h' => F h.1 h')

section E0

variable {D : D7} {k0 : ℕ} {G : GramWordSpace.GramMap k0 D.R.rS} {X : GramWordSpace.Dat D k0}
  {a : ℕ → ℕ → D.what₂.Tau → ℂ} {cb : ℕ → ℕ → ℝ} {c0 : ℝ} {χ : ℝ → ℝ} {ha : ∀ i s v, a i s v ≠ 0} {Ks : ℕ}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Φ : ℝ → GramWordSpace.GWord D → TA.Pt D.host.E → H}

theorem gram_eq_base_norm_form (hΦ : GramId G X a cb c0 χ ha Ks Φ) {eps : ℝ} (he : 0 < eps) {w : GramWordSpace.GWord D} (hw : WOK X Ks w)
    {j0 : ℕ} (hj : j0 ≤ D.R.rS + 1) (Hd : Finset (TA.Pt D.host.E)) (hHd : ∀ h ∈ Hd, TA.IsPt j0 h)
    (kap : TA.Pt D.host.E → TA.Pt D.host.E → ℂ) :
    TA.gram kap (Φ eps w) Hd = GramWordSpace.N0 G X j0 w χ eps (hdS a ha j0 Hd) (kapS X a cb c0 Hd kap) := by
  unfold TA.gram GramWordSpace.N0
  have e := sum_sub Hd (fun h h' => kap h' h * ((c0 * (sc X a cb h * sc X a cb h') : ℝ) : ℂ) *
    ∏ v, GramWordSpace.gram G X v j0 (w v) (X.Fv χ eps v) (lpt a ha j0 h v) (lpt a ha j0 h' v))
  have e2 : (∑ h : Hd, ∑ h' : Hd, kapS X a cb c0 Hd kap h h' *
      ∏ v, GramWordSpace.gram G X v j0 (w v) (X.Fv χ eps v) (hdS a ha j0 Hd h v) (hdS a ha j0 Hd h' v)) =
      ∑ h ∈ Hd, ∑ h' ∈ Hd, kap h' h * ((c0 * (sc X a cb h * sc X a cb h') : ℝ) : ℂ) *
        ∏ v, GramWordSpace.gram G X v j0 (w v) (X.Fv χ eps v) (lpt a ha j0 h v) (lpt a ha j0 h' v) := e
  rw [e2, Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun p' hp' => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [hΦ eps he w hw j0 hj p p' (hHd p hp) (hHd p' hp')]
  unfold Gk
  ring

theorem wB_gram (v : D.what₂.Tau) {j0 s : ℕ} (hs : 1 ≤ s) (w : TopsChoicePartA.Word) (F : GramWordSpace.GFn (X.B v)) (h h' : Point ℂ j0)
    {τ τ' : ℂ} (hτ : τ ≠ 0) (hτ' : τ' ≠ 0) :
    ((wB X v j0 s τ * wB X v j0 s τ' : ℝ) : ℂ) *
        GramWordSpace.gram G X v (j0 + s) w F (GramWordSpace.snoc h τ hτ s hs) (GramWordSpace.snoc h' τ' hτ' s hs) =
      ((X.wt v j0 s τ * X.wt v j0 s τ' : ℝ) : ℂ) * GramWordSpace.gramS G X v j0 s w F h h' τ τ' := by
  unfold GramWordSpace.gramS wB
  by_cases h1 : X.okT v j0 s τ
  · by_cases h2 : X.okT v j0 s τ'
    · rw [dif_pos ⟨hs, h1, h2⟩, if_pos h1, if_pos h2]
    · rw [dif_neg (fun H => h2 H.2.2), if_neg h2]; simp
  · rw [dif_neg (fun H => h1 H.2.1), if_neg h1]; simp

theorem Nst_eq_Ns (hΦ : GramId G X a cb c0 χ ha Ks Φ) (hcb : ∀ i s, 0 ≤ cb i s) {eps : ℝ} (he : 0 < eps)
    {w : GramWordSpace.GWord D} (hw : WOK X Ks w) {j0 s : ℕ} (hs : 1 ≤ s) (hjs : j0 + s ≤ D.R.rS + 1)
    (Hd : Finset (TA.Pt D.host.E)) (hHd : ∀ h ∈ Hd, TA.IsPt j0 h)
    (kap : TA.Pt D.host.E → TA.Pt D.host.E → ℂ) {t t' : D.host.E} (ht : t ≠ 0) (ht' : t' ≠ 0) :
    TA.Nst (Φ eps w) Hd kap s t t' = ((cb (j0 + 1) s : ℝ) : ℂ) *
      GramWordSpace.Ns G X j0 s w χ eps (hdS a ha j0 Hd) (kapS X a cb c0 Hd kap) (tau a (j0 + 1) s t') (tau a (j0 + 1) s t) := by
  unfold TA.Nst GramWordSpace.Ns
  have e2 : (∑ h : Hd, ∑ h' : Hd, kapS X a cb c0 Hd kap h h' *
      ∏ v, GramWordSpace.gramS G X v j0 s (w v) (X.Fv χ eps v) (hdS a ha j0 Hd h v) (hdS a ha j0 Hd h' v)
        (tau a (j0 + 1) s t' v) (tau a (j0 + 1) s t v)) =
      ∑ h ∈ Hd, ∑ h' ∈ Hd, kap h' h * ((c0 * (sc X a cb h * sc X a cb h') : ℝ) : ℂ) *
        ∏ v, GramWordSpace.gramS G X v j0 s (w v) (X.Fv χ eps v) (lpt a ha j0 h v) (lpt a ha j0 h' v)
          (tau a (j0 + 1) s t' v) (tau a (j0 + 1) s t v) :=
    sum_sub Hd (fun h h' => kap h' h * ((c0 * (sc X a cb h * sc X a cb h') : ℝ) : ℂ) *
        ∏ v, GramWordSpace.gramS G X v j0 s (w v) (X.Fv χ eps v) (lpt a ha j0 h v) (lpt a ha j0 h' v)
          (tau a (j0 + 1) s t' v) (tau a (j0 + 1) s t v))
  rw [e2, Finset.sum_comm, Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p' hp' => ?_
  rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [hΦ eps he w hw (j0 + s) hjs _ _ (isPt_ext (hHd p hp) hs ht) (isPt_ext (hHd p' hp') hs ht')]
  unfold Gk
  rw [sc_ext X a cb (hHd p hp), sc_ext X a cb (hHd p' hp')]
  have hkey : (((∏ v, wB X v j0 s (tau a (j0 + 1) s t' v)) * ∏ v, wB X v j0 s (tau a (j0 + 1) s t v) : ℝ) : ℂ) *
      (∏ v, GramWordSpace.gram G X v (j0 + s) (w v) (X.Fv χ eps v) (lpt a ha (j0 + s) (TA.ext p' s t') v)
        (lpt a ha (j0 + s) (TA.ext p s t) v)) =
      ((∏ v, X.wt v j0 s (tau a (j0 + 1) s t' v) * X.wt v j0 s (tau a (j0 + 1) s t v) : ℝ) : ℂ) *
      ∏ v, GramWordSpace.gramS G X v j0 s (w v) (X.Fv χ eps v) (lpt a ha j0 p' v) (lpt a ha j0 p v)
          (tau a (j0 + 1) s t' v) (tau a (j0 + 1) s t v) := by
    rw [← Finset.prod_mul_distrib, Complex.ofReal_prod, Complex.ofReal_prod, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [lpt_ext a ha (hHd p' hp') hs ht' v, lpt_ext a ha (hHd p hp) hs ht v]
    exact wB_gram v hs (w v) _ _ _ _ _
  have hq : ((Real.sqrt (cb (j0 + 1) s) : ℝ) : ℂ) * ((Real.sqrt (cb (j0 + 1) s) : ℝ) : ℂ) = ((cb (j0 + 1) s : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hcb _ _)]
  push_cast at hkey ⊢
  simp only [div_eq_mul_inv]
  linear_combination (kap p p' * (c0 : ℂ) * (sc X a cb p' : ℂ) * (sc X a cb p : ℂ) * ((X.brk w : ℝ) : ℂ)⁻¹ *
      ((cb (j0 + 1) s : ℝ) : ℂ)) * hkey +
    (kap p p' * (c0 : ℂ) * (sc X a cb p' : ℂ) * (sc X a cb p : ℂ) * ((X.brk w : ℝ) : ℂ)⁻¹ *
      ((∏ v, ((wB X v j0 s (tau a (j0 + 1) s t' v) : ℝ) : ℂ)) * ∏ v, ((wB X v j0 s (tau a (j0 + 1) s t v) : ℝ) : ℂ)) *
      (∏ v, GramWordSpace.gram G X v (j0 + s) (w v) (X.Fv χ eps v) (lpt a ha (j0 + s) (TA.ext p' s t') v)
        (lpt a ha (j0 + s) (TA.ext p s t) v))) * hq

theorem kapS_psdk (hc0 : 0 ≤ c0) (Hd : Finset (TA.Pt D.host.E)) (kap : TA.Pt D.host.E → TA.Pt D.host.E → ℂ)
    (h : TA.PSDOn Hd kap) : PSDK (kapS X a cb c0 Hd kap) := by
  have h1 : TB.PSDOn Hd kap := ((Formalism.FourierDecayAlt.P.psd_agree _ Hd kap).1).2 h
  have h2 : PSDK (fun x y : Hd => kap x.1 y.1) := (psdk_iff _).2 h1
  have h3 : PSDK (fun x y : Hd => ((sc X a cb x.1 : ℝ) : ℂ) * conj ((sc X a cb y.1 : ℝ) : ℂ)) :=
    PSDK.rankOne (fun x : Hd => ((sc X a cb x.1 : ℝ) : ℂ))
  have h4 := PSDK.smul (PSDK.mul (PSDK.transpose h2) h3) hc0
  have e : kapS X a cb c0 Hd kap = fun p q : Hd => (c0 : ℂ) * (kap q.1 p.1 *
      (((sc X a cb p.1 : ℝ) : ℂ) * conj ((sc X a cb q.1 : ℝ) : ℂ))) := by
    funext p q
    unfold kapS
    rw [Complex.conj_ofReal]
    push_cast
    ring
  rw [e]
  exact h4

theorem gram_re_nonneg {E : Type} (V : TA.Pt E → H) (P : Finset (TA.Pt E)) (k : TA.Pt E → TA.Pt E → ℂ)
    (h : TA.PSDOn P k) : 0 ≤ (TA.gram k V P).re := Formalism.FourierDecayAlt.P.GramConjugationNorm.gram_re_nonneg k V P h

theorem Nst_re_nonneg {E : Type} (V : TA.Pt E → H) (Hd : Finset (TA.Pt E)) (k : TA.Pt E → TA.Pt E → ℂ)
    (h : TA.PSDOn Hd k) (s : ℕ) (t : E) : 0 ≤ (TA.Nst V Hd k s t t).re :=
  Formalism.FourierDecayAlt.P.TA2.gram_nonneg Hd k (fun h => V (TA.ext h s t)) h

end E0

end Formalism.MainNotions.BlockEstimateWords

end

end PartE0

section PartP72

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Small

variable {D : D7} {k0 : ℕ}

theorem len_of_glen {Ks : ℕ} {w : GramWordSpace.GWord D} {m : ℕ} (h : glen w + m ≤ GramWordSpace.NN D Ks) :
    GramWordSpace.Len (GramWordSpace.NN D Ks - m) w := by
  intro v
  have : (w v).length ≤ glen w := Finset.le_sup (f := fun v => (w v).length) (Finset.mem_univ v)
  omega

theorem wok_ext {X : GramWordSpace.Dat D k0} {Ks : ℕ} {w w' : GramWordSpace.GWord D} {m : ℕ} {A : Set D.what₂.Tau}
    (hw : glen w + m ≤ GramWordSpace.NN D Ks) (he : GramWordSpace.ExtAt m A w w') (hA : X.admitted w') : WOK X Ks w' := by
  refine ⟨hA, fun v => ?_⟩
  obtain ⟨l, hl, -, e⟩ := he v
  have : (w v).length ≤ glen w := Finset.le_sup (f := fun v => (w v).length) (Finset.mem_univ v)
  rw [e, List.length_append]
  omega

theorem kaV_pos {δ : D.host.E} (hδ : δ ≠ 0) (v : D.what₂.Tau) : 0 < kaV D δ v :=
  div_pos (by positivity) (norm_pos_iff.2 ((map_ne_zero (plEmb D v)).2 hδ))

theorem norm_sgm (a : ℕ → ℕ → D.what₂.Tau → ℂ) (δ : D.host.E) (i s : ℕ) (l : D.host.E) (v : D.what₂.Tau) :
    ‖sgm a δ i s l v‖ = kaV D δ v * ‖plEmb D v l‖ / ‖a i s v‖ := by
  unfold sgm kaV
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [map_div₀, norm_div, norm_mul, norm_mul, norm_mul, norm_div, h2, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  ring

theorem minFac_nonneg {x y : ℝ} (K : ℕ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ minFac x y K := by
  unfold minFac
  split_ifs
  · norm_num
  · exact le_min zero_le_one (pow_nonneg (div_nonneg hx hy) K)

theorem minFac_scale {x x' k y α : ℝ} (K : ℕ) (hx : 0 ≤ x) (hk : 0 < k) (hy : 0 < y) (hα : 0 < α)
    (h : x * α ≤ k * x') : minFac x (k * y / α) K ≤ minFac x' y K := by
  unfold minFac
  have hky : k * y / α ≠ 0 := (div_pos (mul_pos hk hy) hα).ne'
  rw [if_neg hky, if_neg hy.ne']
  refine min_le_min le_rfl (pow_le_pow_left₀ (div_nonneg hx (div_pos (mul_pos hk hy) hα).le) ?_ K)
  have e : x / (k * y / α) = x * α / k / y := by field_simp
  rw [e]
  refine div_le_div_of_nonneg_right ?_ hy.le
  rw [div_le_iff₀ hk]
  linarith

theorem sgm_zero (a : ℕ → ℕ → D.what₂.Tau → ℂ) (δ : D.host.E) (i s : ℕ) : sgm a δ i s 0 = 0 := by
  funext v; simp [sgm]

end Small

section P72

variable {D : D7} {k0 : ℕ} {G : GramWordSpace.GramMap k0 D.R.rS} {X : GramWordSpace.Dat D k0}
  {a : ℕ → ℕ → D.what₂.Tau → ℂ} {cb : ℕ → ℕ → ℝ} {c0 : ℝ} {χ : ℝ → ℝ} {Ks : ℕ}
  {E₀ Eg E₁ E₂ E₃ C C4 T T' : ℝ} {δ : D.host.E} {x : D.what₂.Tau → LocalDataRealPlace D} {L : LatticeDataWithDual D} {κL : ℕ → ℕ → ℝ}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Φ : ℝ → GramWordSpace.GWord D → TA.Pt D.host.E → H}

theorem first_profile_le (hM : Mod D X a cb c0 Ks E₀ Eg E₁ E₂ E₃ C C4 T T' δ x L κL) {i : ℕ} (hi1 : 1 ≤ i)
    (hi : i ≤ D.R.rS + 1) {l : D.host.E} (hl : l ≠ 0) :
    (∏ v, minFac (X.xi E₁ E₂ Ks i v) ‖sgm a δ i 1 l v‖ Ks) ≤ prof1 D C C (Nlet D Ks) T T' δ x Ks i l := by
  unfold prof1
  refine Finset.prod_le_prod (fun v _ => minFac_nonneg _ (hM.xi_nn i v) (norm_nonneg _)) fun v _ => ?_
  rw [norm_sgm]
  exact minFac_scale Ks (hM.xi_nn i v) (kaV_pos hM.δ_ne v) (norm_pos_iff.2 ((map_ne_zero (plEmb D v)).2 hl))
    (norm_pos_iff.2 (hM.a_ne i 1 v)) (hM.thr1 i v hi1 hi)

theorem word_extension_prob_single (hM : Mod D X a cb c0 Ks E₀ Eg E₁ E₂ E₃ C C4 T T' δ x L κL) (hχ : IsCutoff χ)
    (h72 : GramWordSpace.SingleLevelGramEstimate D G Ks E₀ Eg E₁ E₂) (hΦ : GramId G X a cb c0 χ hM.a_ne Ks Φ)
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ D.R.rS + 1) {w : GramWordSpace.GWord D} (hw : WOK X Ks w)
    (hlen : glen w + Ks ≤ GramWordSpace.NN D Ks) :
    ∃ θ : Set D.what₂.Tau → (GramWordSpace.GWord D →₀ ℝ),
      (∀ A, GramWordSpace.IsProb (θ A) ∧ ∀ w' ∈ (θ A).support, GramWordSpace.ExtAt Ks A w w' ∧ X.admitted w') ∧
      ∀ eps : ℝ, 0 < eps → ∀ (Hd : Finset (TA.Pt D.host.E)) (kap : TA.Pt D.host.E → TA.Pt D.host.E → ℂ),
        (∀ h ∈ Hd, TA.IsPt (i - 1) h) → TA.PSDOn Hd kap →
        trS G X a cb c0 χ hM.a_ne δ eps i w Hd kap 0 = TA.gram kap (Φ eps w) Hd ∧
        ∀ l ∈ taLv D δ L i, l ≠ 0 →
          ‖trS G X a cb c0 χ hM.a_ne δ eps i w Hd kap l‖ ≤ prof1 D C C (Nlet D Ks) T T' δ x Ks i l *
            (θ (pat1S X a δ E₁ E₂ Ks i l)).sum (fun w' c => c * (TA.gram kap (Φ eps w') Hd).re) := by
  have hj0 : i - 1 ≤ D.R.rS := by omega
  have hi' : i - 1 + 1 = i := by omega
  obtain ⟨hpart, θ, hθ, hB⟩ := h72 X hM.std (i - 1) hj0 w hw.1 (len_of_glen hlen)
  refine ⟨θ, hθ, fun eps he Hd kap hHd hk => ?_⟩
  have hκ := kapS_psdk (X := X) (a := a) (cb := cb) hM.lowerConstantNonneg Hd kap hk
  have hN0 : ∀ w' ∈ (θ (pat1S X a δ E₁ E₂ Ks i 0)).support, True := fun _ _ => trivial
  clear hN0
  refine ⟨?_, fun l _ hl => ?_⟩
  · unfold trS
    rw [sgm_zero, (hpart χ hχ eps he Hd (hdS a hM.a_ne (i - 1) Hd) (kapS X a cb c0 Hd kap) hκ).2]
    exact (gram_eq_base_norm_form hΦ he hw (by omega) Hd hHd kap).symm
  · have h1 := hB χ hχ eps he Hd (hdS a hM.a_ne (i - 1) Hd) (kapS X a cb c0 Hd kap) hκ (sgm a δ i 1 l)
    rw [hi'] at h1
    have hset : {v | X.xi E₁ E₂ Ks i v < ‖sgm a δ i 1 l v‖} = pat1S X a δ E₁ E₂ Ks i l := rfl
    rw [hset] at h1
    have hsum : (θ (pat1S X a δ E₁ E₂ Ks i l)).sum
        (fun w' c => c * (GramWordSpace.N0 G X (i - 1) w' χ eps (hdS a hM.a_ne (i - 1) Hd) (kapS X a cb c0 Hd kap)).re) =
        (θ (pat1S X a δ E₁ E₂ Ks i l)).sum (fun w' c => c * (TA.gram kap (Φ eps w') Hd).re) := by
      refine Finsupp.sum_congr fun w' hw' => ?_
      obtain ⟨hext, hadm⟩ := (hθ _).2 w' hw'
      rw [gram_eq_base_norm_form hΦ he (wok_ext hlen hext hadm) (by omega) Hd hHd kap]
    rw [hsum] at h1
    have hS : 0 ≤ (θ (pat1S X a δ E₁ E₂ Ks i l)).sum (fun w' c => c * (TA.gram kap (Φ eps w') Hd).re) :=
      Finset.sum_nonneg fun w' _ => mul_nonneg ((hθ _).1.1 w') (gram_re_nonneg _ Hd kap hk)
    exact le_trans h1 (mul_le_mul_of_nonneg_right (first_profile_le hM hi1 hi hl) hS)

end P72

end Formalism.MainNotions.BlockEstimateWords

end

end PartP72

section PartP74

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section P74

variable {D : D7} {k0 : ℕ} {G : GramWordSpace.GramMap k0 D.R.rS} {X : GramWordSpace.Dat D k0}
  {a : ℕ → ℕ → D.what₂.Tau → ℂ} {cb : ℕ → ℕ → ℝ} {c0 : ℝ} {χ : ℝ → ℝ} {Ks : ℕ}
  {E₀ Eg E₁ E₂ E₃ C C4 T T' : ℝ} {δ : D.host.E} {x : D.what₂.Tau → LocalDataRealPlace D} {L : LatticeDataWithDual D} {κL : ℕ → ℕ → ℝ}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Φ : ℝ → GramWordSpace.GWord D → TA.Pt D.host.E → H}

theorem tau_nonempty (D : D7) : Nonempty D.what₂.Tau :=
  Fintype.card_pos_iff.1 (by rw [D.what₂.card_Tau]; exact f_pos D)

theorem embA_inj (a : ℕ → ℕ → D.what₂.Tau → ℂ) {i s : ℕ} (hne : ∀ v, a i s v ≠ 0) :
    Function.Injective (embA a i s) := by
  intro t t' h
  obtain ⟨v⟩ := tau_nonempty D
  have h1 : a i s v * plEmb D v t = a i s v * plEmb D v t' := congrFun h v
  exact (plEmb D v).injective (mul_left_cancel₀ (hne v) h1)

theorem Ns_zero (G : GramWordSpace.GramMap k0 D.R.rS) (X : GramWordSpace.Dat D k0) (j0 s : ℕ) (w : GramWordSpace.GWord D) (χ : ℝ → ℝ) (eps : ℝ)
    {Hd : Type} [Fintype Hd] (hd : Hd → GramWordSpace.Head D j0) (κ : Hd → Hd → ℂ) :
    GramWordSpace.Ns G X j0 s w χ eps hd κ 0 0 = 0 := by
  obtain ⟨v0⟩ := tau_nonempty D
  have hg : ∀ h h' : Hd, ∏ v, GramWordSpace.gramS G X v j0 s (w v) (X.Fv χ eps v) (hd h v) (hd h' v) (0 : ℂ) (0 : ℂ) = 0 := by
    intro h h'
    refine Finset.prod_eq_zero (Finset.mem_univ v0) ?_
    unfold GramWordSpace.gramS
    rw [dif_neg]
    rintro ⟨_, ⟨h0, _⟩, _⟩
    exact h0 rfl
  simp only [GramWordSpace.Ns, Pi.zero_apply, hg, mul_zero, Finset.sum_const_zero, zero_div]

theorem block_word_extension_prob (hM : Mod D X a cb c0 Ks E₀ Eg E₁ E₂ E₃ C C4 T T' δ x L κL) (hχ : IsCutoff χ)
    (h74 : GramWordSpace.LargeBlockLiftEstimate D G Ks E₀ Eg E₁ E₂ E₃) (hΦ : GramId G X a cb c0 χ hM.a_ne Ks Φ)
    {i s : ℕ} (hs : 2 ≤ s) (hsi : s ≤ i) (hi : i ≤ D.R.rS + 1)
    {w : GramWordSpace.GWord D} (hw : WOK X Ks w) (hlen : glen w + (s + 1) * Ks ≤ GramWordSpace.NN D Ks) :
    ∃ θ : GramWordSpace.GWord D →₀ ℝ, GramWordSpace.IsProb θ ∧
      (∀ w' ∈ θ.support, GramWordSpace.ExtAt ((s + 1) * Ks) Set.univ w w' ∧ X.admitted w') ∧
      ∀ eps : ℝ, 0 < eps → ∀ (Hd : Finset (TA.Pt D.host.E)) (kap : TA.Pt D.host.E → TA.Pt D.host.E → ℂ),
        (∀ h ∈ Hd, TA.IsPt (i - s) h) → TA.PSDOn Hd kap →
        ∀ (t0 : D.host.E) (Ts : Finset D.host.E), (∀ t ∈ Ts, t ≠ 0 ∧ t - t0 ∈ (L.La (i - s + 1) s).toAddSubgroup) →
          ∑ t ∈ Ts, (TA.Nst (Φ eps w) Hd kap s t t).re ≤ bdB D C C (Nlet D Ks) T T' δ x L C4 i s *
            θ.sum (fun w' c => c * (TA.gram kap (Φ eps w') Hd).re) := by
  have hjs : i - s + s ≤ D.R.rS + 1 := by omega
  have hs1 : 1 ≤ s := by omega
  have hblk : IsBlockSL2Embedding D (i - s + 1) s := ⟨by omega, hs1, by omega⟩
  have hcb : ∀ i s, 0 ≤ cb i s := fun i s => (hM.cb_pos i s).le
  have ha' : ∀ v, aDual a δ (i - s + 1) s v ≠ 0 := fun v => by
    unfold aDual
    exact div_ne_zero (by simp [Real.pi_ne_zero]) (mul_ne_zero ((map_ne_zero (plEmb D v)).2 hM.δ_ne) (hM.a_ne _ _ _))
  have hdual : GramWordSpace.dualS D (laC a L (i - s + 1) s) ⊆ GramWordSpace.scId D (aDual a δ (i - s + 1) s) (L.aaV (i - s + 1) s) := by
    intro σ hσ
    obtain ⟨l, hl, rfl⟩ := hM.dual _ _ hblk σ hσ
    refine ⟨l, hM.dualV _ _ hblk hl, fun v => ?_⟩
    unfold sgm aDual
    rw [map_div₀]
    ring
  obtain ⟨θ, hP, hsupp, hB⟩ := h74 X hM.std (i - s) s hs hjs w hw.1 (len_of_glen hlen) (L.aaV (i - s + 1) s)
    (aDual a δ (i - s + 1) s) ha' (hM.blockProductBound _ s hs hblk)
  refine ⟨θ, hP, hsupp, fun eps he Hd kap hHd hk t0 Ts hTs => ?_⟩
  have hκ := kapS_psdk (X := X) (a := a) (cb := cb) hM.lowerConstantNonneg Hd kap hk
  have hlat := hM.lat _ _ hblk
  obtain ⟨sv, hsum, hle⟩ := hB (laC a L (i - s + 1) s) (κL (i - s + 1) s) hlat hdual χ hχ eps he Hd
    (hdS a hM.a_ne (i - s) Hd) (kapS X a cb c0 Hd kap) hκ (tau a (i - s + 1) s t0)
  set f : (D.what₂.Tau → ℂ) → ℂ := fun z =>
    GramWordSpace.Ns G X (i - s) s w χ eps (hdS a hM.a_ne (i - s) Hd) (kapS X a cb c0 Hd kap) z z with hf
  have hre : HasSum (fun z : laC a L (i - s + 1) s => (f (tau a (i - s + 1) s t0 + z)).re) sv := by
    simpa using (Complex.reCLM.hasSum hsum)
  have hcb0 : 0 < cb (i - s + 1) s := hM.cb_pos _ _

  have hval : ∀ t : D.host.E, t ≠ 0 →
      (TA.Nst (Φ eps w) Hd kap s t t).re = cb (i - s + 1) s * (f (tau a (i - s + 1) s t)).re := by
    intro t ht
    rw [Nst_eq_Ns hΦ hcb he hw hs1 hjs Hd hHd kap ht ht, Complex.re_ofReal_mul]
  have hnn : ∀ z : laC a L (i - s + 1) s, 0 ≤ (f (tau a (i - s + 1) s t0 + z)).re := by
    intro z
    obtain ⟨l, -, hz⟩ := AddSubgroup.mem_map.1 z.2
    have e : tau a (i - s + 1) s t0 + (z : D.what₂.Tau → ℂ) = tau a (i - s + 1) s (t0 + l) := by
      rw [← hz]; funext v; simp [embA, tau, mul_add]
    rw [e]
    by_cases h0 : t0 + l = 0
    · have e0 : tau a (i - s + 1) s (t0 + l) = 0 := by rw [h0]; funext v; simp [tau]
      rw [e0, hf]
      simp only [Ns_zero, Complex.zero_re, le_refl]
    · have h1 := Nst_re_nonneg (Φ eps w) Hd kap hk s (t0 + l)
      rw [hval _ h0] at h1
      exact nonneg_of_mul_nonneg_right (by linarith) hcb0

  let ψ : D.host.E → laC a L (i - s + 1) s := fun t =>
    if h : t - t0 ∈ (L.La (i - s + 1) s).toAddSubgroup then ⟨embA a (i - s + 1) s (t - t0), ⟨t - t0, h, rfl⟩⟩ else 0
  have hψ : ∀ t ∈ Ts, tau a (i - s + 1) s t0 + (ψ t : D.what₂.Tau → ℂ) = tau a (i - s + 1) s t := by
    intro t ht
    simp only [ψ, dif_pos (hTs t ht).2]
    funext v; simp [embA, tau, mul_sub]
  have hinj : ∀ t ∈ Ts, ∀ t' ∈ Ts, ψ t = ψ t' → t = t' := by
    intro t ht t' ht' e
    simp only [ψ, dif_pos (hTs t ht).2, dif_pos (hTs t' ht').2] at e
    have e' : embA a (i - s + 1) s (t - t0) = embA a (i - s + 1) s (t' - t0) := congrArg Subtype.val e
    exact sub_left_injective (embA_inj a (hM.a_ne (i - s + 1) s) e')
  have hpart : ∑ t ∈ Ts, (f (tau a (i - s + 1) s t)).re ≤ sv := by
    have e1 : ∑ t ∈ Ts, (f (tau a (i - s + 1) s t)).re =
        ∑ z ∈ Ts.image ψ, (f (tau a (i - s + 1) s t0 + z)).re := by
      rw [Finset.sum_image hinj]
      exact Finset.sum_congr rfl fun t ht => by rw [hψ t ht]
    rw [e1]
    exact sum_le_hasSum _ (fun z _ => hnn z) hre
  have hlhs : ∑ t ∈ Ts, (TA.Nst (Φ eps w) Hd kap s t t).re = cb (i - s + 1) s * ∑ t ∈ Ts, (f (tau a (i - s + 1) s t)).re := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t ht => hval t (hTs t ht).1

  have hθsum : θ.sum (fun w' c => c * (GramWordSpace.N0 G X (i - s) w' χ eps (hdS a hM.a_ne (i - s) Hd) (kapS X a cb c0 Hd kap)).re) =
      θ.sum (fun w' c => c * (TA.gram kap (Φ eps w') Hd).re) := by
    refine Finsupp.sum_congr fun w' hw' => ?_
    obtain ⟨hext, hadm⟩ := hsupp w' hw'
    rw [gram_eq_base_norm_form hΦ he (wok_ext hlen hext hadm) (by omega) Hd hHd kap]
  rw [hθsum] at hle
  have hS : 0 ≤ θ.sum (fun w' c => c * (TA.gram kap (Φ eps w') Hd).re) :=
    Finset.sum_nonneg fun w' _ => mul_nonneg (hP.1 w') (gram_re_nonneg _ Hd kap hk)
  have hκ0 : 0 < κL (i - s + 1) s := hlat.1
  have hbd := hM.blockSL2Embedding_bound _ s hs hblk
  have hidx : i - s + 1 + s - 1 = i := by omega
  rw [hidx] at hbd
  rw [hlhs]
  have h2 : cb (i - s + 1) s * sv ≤ cb (i - s + 1) s / κL (i - s + 1) s *
      (E₃ ^ (D.R.f * s) * (∏ s' ∈ Finset.Ico 1 s, ∏ v, X.LamG E₁ E₂ Ks s' (i - s + 1) v ^ 2) *
        θ.sum (fun w' c => c * (TA.gram kap (Φ eps w') Hd).re)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hκ0]
    nlinarith [hle, hcb0]
  calc cb (i - s + 1) s * ∑ t ∈ Ts, (f (tau a (i - s + 1) s t)).re ≤ cb (i - s + 1) s * sv :=
        mul_le_mul_of_nonneg_left hpart hcb0.le
    _ ≤ _ := h2
    _ = cb (i - s + 1) s / κL (i - s + 1) s *
          (E₃ ^ (D.R.f * s) * ∏ s' ∈ Finset.Ico 1 s, ∏ v, X.LamG E₁ E₂ Ks s' (i - s + 1) v ^ 2) *
        θ.sum (fun w' c => c * (TA.gram kap (Φ eps w') Hd).re) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbd hS

end P74

end Formalism.MainNotions.BlockEstimateWords

end

end PartP74

section PartP73

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Psd

theorem sum_over_fibers {β γ : Type} (P : Finset β) (Q : Finset γ) (e : γ → β) (hm : ∀ x ∈ Q, e x ∈ P) (F : β → ℂ)
    (b : γ → ℂ) : ∑ u ∈ P, F u * (∑ x ∈ Q, if e x = u then b x else 0) = ∑ x ∈ Q, F (e x) * b x := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, if_pos (hm x hx)]

theorem hermitian_form_pullback_fiber {β γ : Type} (P : Finset β) (Q : Finset γ) (e : γ → β) (hm : ∀ x ∈ Q, e x ∈ P)
    (k : β → β → ℂ) (b : γ → ℂ) :
    ∑ u ∈ P, ∑ u' ∈ P, conj (∑ x ∈ Q, if e x = u then b x else 0) * k u u' * (∑ y ∈ Q, if e y = u' then b y else 0) =
      ∑ x ∈ Q, ∑ y ∈ Q, conj (b x) * k (e x) (e y) * b y := by
  have h1 : ∀ u, ∑ u' ∈ P, conj (∑ x ∈ Q, if e x = u then b x else 0) * k u u' *
      (∑ y ∈ Q, if e y = u' then b y else 0) =
      (∑ y ∈ Q, k u (e y) * b y) * (∑ x ∈ Q, if e x = u then conj (b x) else 0) := by
    intro u
    rw [← sum_over_fibers P Q e hm (k u) b, mul_comm, Finset.mul_sum]
    have h2 : conj (∑ x ∈ Q, if e x = u then b x else 0) = ∑ x ∈ Q, if e x = u then conj (b x) else 0 := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> simp
    rw [h2]
    refine Finset.sum_congr rfl fun u' _ => ?_
    ring
  rw [Finset.sum_congr rfl fun u _ => h1 u, sum_over_fibers P Q e hm (fun u => ∑ y ∈ Q, k u (e y) * b y) (fun x => conj (b x))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

theorem hermitian_quadratic_form_real {β : Type} (P : Finset β) (k : β → β → ℂ) (hk : ∀ x ∈ P, ∀ y ∈ P, k y x = conj (k x y))
    (b : β → ℂ) : (∑ x ∈ P, ∑ y ∈ P, conj (b x) * k x y * b y).im = 0 := by
  apply Complex.conj_eq_iff_im.1
  rw [map_sum]
  simp_rw [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => ?_
  rw [hk x hx y hy]
  simp only [map_mul, Complex.conj_conj]
  ring

theorem psd_on_comap {β γ : Type} (P : Finset β) (k : β → β → ℂ) (h : TA.PSDOn P k) (Q : Finset γ) (e : γ → β)
    (hm : ∀ x ∈ Q, e x ∈ P) : TA.PSDOn Q (fun x y => k (e x) (e y)) := by
  refine ⟨fun x hx y hy => h.1 _ (hm x hx) _ (hm y hy), fun b => ?_⟩
  rw [← hermitian_form_pullback_fiber P Q e hm k b]
  exact h.2 _

theorem psd_kernel_weighted_pullback {α β : Type} (P : Finset β) (k : β → β → ℂ) (h : TA.PSDOn P k) (ψ : α → β) (W : α → ℂ)
    (hW : ∀ z, ψ z ∉ P → W z = 0) : PSDK (fun z z' => W z * conj (W z') * k (ψ z') (ψ z)) := by
  intro X c
  set Q := X.filter (fun z => ψ z ∈ P) with hQdef
  have hQ := psd_on_comap P k h Q ψ (fun x hx => (Finset.mem_filter.1 hx).2)
  set b : α → ℂ := fun z => W z * conj (c z) with hb
  have hb0 : ∀ z, ψ z ∉ P → b z = 0 := fun z hz => by rw [hb]; simp only; rw [hW z hz, zero_mul]
  have e1 : ∀ f : α → ℂ, (∀ z, ψ z ∉ P → f z = 0) → ∑ x ∈ Q, f x = ∑ x ∈ X, f x := fun f hf => by
    rw [hQdef, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with hx
    · rfl
    · exact (hf x hx).symm
  have key : ∑ p ∈ X, ∑ q ∈ X, star (c p) * (W p * conj (W q) * k (ψ q) (ψ p)) * c q =
      ∑ x ∈ Q, ∑ y ∈ Q, conj (b x) * k (ψ x) (ψ y) * b y := by
    rw [e1 (fun x => ∑ y ∈ Q, conj (b x) * k (ψ x) (ψ y) * b y) (fun z hz => by
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [hb0 z hz]; simp)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [e1 (fun y => conj (b x) * k (ψ x) (ψ y) * b y) (fun z hz => by rw [hb0 z hz, mul_zero])]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [hb, map_mul, Complex.conj_conj, Complex.star_def]
    ring
  rw [key]
  refine Complex.le_def.2 ⟨?_, ?_⟩
  · simpa using hQ.2 b
  · simpa using (hermitian_quadratic_form_real Q (fun x y => k (ψ x) (ψ y)) hQ.1 b).symm

end Psd

section Lift

theorem block_tau_injective {D : D7} (a : ℕ → ℕ → D.what₂.Tau → ℂ) (ha : ∀ i s v, a i s v ≠ 0) (i s : ℕ) :
    Function.Injective (tau (D := D) a i s) := by
  intro u u' h
  have hne : Nonempty D.what₂.Tau := by
    apply Fintype.card_pos_iff.1
    rw [D.what₂.card_Tau]
    exact f_pos D
  obtain ⟨v⟩ := hne
  have h1 := congrFun h v
  simp only [tau] at h1
  exact (plEmb D v).injective (mul_left_cancel₀ (ha i s v) h1)

theorem admissible_word_pair {D : D7} {k0 : ℕ} {X : GramWordSpace.Dat D k0} {Ks j0 s : ℕ} {w : GramWordSpace.GWord D}
    {p : D.what₂.Tau → Option Bool} {q : GramWordSpace.GWord D × GramWordSpace.GWord D} (hlen : glen w + Ks ≤ GramWordSpace.NN D Ks)
    (hq : GramWordSpace.ChargedPairs Ks j0 s w p q) (h1 : X.admitted q.1) (h2 : X.admitted q.2) : WOK X Ks q.1 ∧ WOK X Ks q.2 := by
  have hwv : ∀ v, (w v).length ≤ glen w := fun v =>
    Finset.le_sup (f := fun v => (w v).length) (Finset.mem_univ v)
  unfold GramWordSpace.ChargedPairs at hq
  split_ifs at hq
  · refine ⟨⟨h1, fun v => ?_⟩, ⟨h2, fun v => ?_⟩⟩
    · obtain ⟨l, hl, -, -, e1, -⟩ := hq v
      have := hwv v
      rw [e1, List.length_append]
      omega
    · obtain ⟨l, hl, -, -, -, e2⟩ := hq v
      have := hwv v
      rw [e2, List.length_append, GramWordSpace.dualL, List.length_map]
      omega
  · refine ⟨⟨h1, fun v => ?_⟩, ⟨h2, fun v => ?_⟩⟩
    · obtain ⟨l, hl, -, -, e1⟩ := hq.1 v
      have := hwv v
      rw [e1, List.length_append]
      omega
    · obtain ⟨l, hl, -, -, e2⟩ := hq.2 v
      have := hwv v
      rw [e2, List.length_append]
      omega

theorem min_factor_nonneg {x y : ℝ} (K : ℕ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ minFac x y K := by
  unfold minFac
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (pow_nonneg (div_nonneg hx hy) K)

theorem min_factor_mono {x x' y A : ℝ} (K : ℕ) (hx : 0 ≤ x) (hA : 0 < A) (hy : 0 < y) (h : x * A ≤ x') :
    minFac x (y / A) K ≤ minFac x' y K := by
  unfold minFac
  rw [if_neg (div_pos hy hA).ne', if_neg hy.ne']
  refine min_le_min le_rfl (pow_le_pow_left₀ (div_nonneg hx (div_pos hy hA).le) ?_ K)
  rw [div_div_eq_mul_div]
  exact div_le_div_of_nonneg_right h hy.le

theorem weighted_sum_final_bound {ι Q : Type} [Fintype ι] (θ : ι → (Q →₀ ℝ)) (hθ : ∀ p q, 0 ≤ θ p q) (A B : Q → ℝ)
    (c Pm Pf N : ℝ) (p : ι) (hc : 0 ≤ c) (hPm : 0 ≤ Pm) (hP : Pm ≤ Pf) (hB : ∀ q, 0 ≤ B q)
    (hAB : ∀ q ∈ (θ p).support, B q = c * A q) (hb : N ≤ Pm * (θ p).sum (fun q x => x * A q)) :
    c * N ≤ Pf * ∑ p', (θ p').sum (fun q x => x * B q) := by
  have h1 : (θ p).sum (fun q x => x * B q) = c * (θ p).sum (fun q x => x * A q) := by
    unfold Finsupp.sum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    show (θ p) q * B q = c * ((θ p) q * A q)
    rw [hAB q hq]
    ring
  have hnn : ∀ p', 0 ≤ (θ p').sum (fun q x => x * B q) := fun p' => by
    unfold Finsupp.sum
    exact Finset.sum_nonneg fun q _ => mul_nonneg (hθ p' q) (hB q)
  calc c * N ≤ c * (Pm * (θ p).sum (fun q x => x * A q)) := mul_le_mul_of_nonneg_left hb hc
    _ = Pm * (θ p).sum (fun q x => x * B q) := by rw [h1]; ring
    _ ≤ Pf * (θ p).sum (fun q x => x * B q) := mul_le_mul_of_nonneg_right hP (hnn p)
    _ ≤ Pf * ∑ p', (θ p').sum (fun q x => x * B q) :=
        mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun p' => (θ p').sum (fun q x => x * B q)) (fun p' _ => hnn p')
            (Finset.mem_univ p)) (le_trans hPm hP)

variable {D : D7} {k0 : ℕ} {G : GramWordSpace.GramMap k0 D.R.rS} {X : GramWordSpace.Dat D k0}
  {a : ℕ → ℕ → D.what₂.Tau → ℂ} {cb : ℕ → ℕ → ℝ} {c0 : ℝ} {χ : ℝ → ℝ} {Ks : ℕ}
  {E₀ Eg E₁ E₂ E₃ C C4 T T' : ℝ} {δ : D.host.E} {x : D.what₂.Tau → LocalDataRealPlace D} {L : LatticeDataWithDual D} {κL : ℕ → ℕ → ℝ}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Φ : ℝ → GramWordSpace.GWord D → TA.Pt D.host.E → H}

theorem product_min_factor_profile (hM : Mod D X a cb c0 Ks E₀ Eg E₁ E₂ E₃ C C4 T T' δ x L κL)
    {i s : ℕ} (hs : 1 ≤ s) (hsi : s ≤ i) (hi : i ≤ D.R.rS + 1) (hns : ¬ (i = D.R.rS + 1 ∧ s = 1))
    {t t' : D.host.E} (ht : t ≠ 0) (ht' : t' ≠ 0) (htt : t ≠ t') :
    0 ≤ ∏ v, minFac (GramWordSpace.blockLiftThreshold X E₁ E₂ Ks (i - s) s v)
        ‖GramWordSpace.oDiff (tau a (i - s + 1) s t') (tau a (i - s + 1) s t) v‖ Ks ∧
    ∏ v, minFac (GramWordSpace.blockLiftThreshold X E₁ E₂ Ks (i - s) s v)
        ‖GramWordSpace.oDiff (tau a (i - s + 1) s t') (tau a (i - s + 1) s t) v‖ Ks ≤
      prof3 D C C (Nlet D Ks) T T' δ x Ks i s (1 / t - 1 / t') := by
  refine ⟨Finset.prod_nonneg fun v _ => min_factor_nonneg Ks (hM.blockSizeNonneg _ _ _) (norm_nonneg _), ?_⟩
  unfold prof3
  refine Finset.prod_le_prod (fun v _ => min_factor_nonneg Ks (hM.blockSizeNonneg _ _ _) (norm_nonneg _)) fun v _ => ?_
  have hav := hM.a_ne (i - s + 1) s v
  have h1 : plEmb D v t ≠ 0 := (map_ne_zero (plEmb D v)).2 ht
  have h2 : plEmb D v t' ≠ 0 := (map_ne_zero (plEmb D v)).2 ht'
  have ho : (1 / t - 1 / t' : D.host.E) ≠ 0 := by
    refine sub_ne_zero.2 fun h => htt ?_
    simpa [one_div] using h
  have e : GramWordSpace.oDiff (tau a (i - s + 1) s t') (tau a (i - s + 1) s t) v =
      -(plEmb D v (1 / t - 1 / t')) / a (i - s + 1) s v := by
    simp only [GramWordSpace.oDiff, tau, map_sub, map_div₀, map_one]
    field_simp
    ring
  rw [e, norm_div, norm_neg]
  exact min_factor_mono Ks (hM.blockSizeNonneg _ _ _) (norm_pos_iff.2 hav)
    (norm_pos_iff.2 ((map_ne_zero (plEmb D v)).2 ho)) (hM.thr3 i s v hs hsi hi hns)

theorem word_pair_extension_prob (hM : Mod D X a cb c0 Ks E₀ Eg E₁ E₂ E₃ C C4 T T' δ x L κL) (hχ : IsCutoff χ)
    (h73 : GramWordSpace.BlockLiftEstimate D G Ks E₀ Eg E₁ E₂) (hΦ : GramId G X a cb c0 χ hM.a_ne Ks Φ)
    {i s : ℕ} (hs : 1 ≤ s) (hsi : s ≤ i) (hi : i ≤ D.R.rS + 1) (hns : ¬ (i = D.R.rS + 1 ∧ s = 1))
    {w : GramWordSpace.GWord D} (hw : WOK X Ks w) (hlen : glen w + Ks ≤ GramWordSpace.NN D Ks) :
    ∃ θ : (D.what₂.Tau → Option Bool) → (GramWordSpace.GWord D × GramWordSpace.GWord D →₀ ℝ),
      (∀ p, GramWordSpace.IsProb (θ p) ∧ ∀ q ∈ (θ p).support, GramWordSpace.ChargedPairs Ks (i - s) s w p q ∧ X.admitted q.1 ∧ X.admitted q.2) ∧
      ∀ eps : ℝ, 0 < eps → ∀ (Hd : Finset (TA.Pt D.host.E)) (kp : TA.Pt D.host.E → TA.Pt D.host.E → ℂ)
        (Ts : Finset D.host.E), (∀ h ∈ Hd, TA.IsPt (i - s) h) → (∀ t ∈ Ts, t ≠ 0) →
        TA.PSDOn ((Hd ×ˢ Ts).image fun y => TA.ext y.1 s y.2) kp →
        ∀ t ∈ Ts, ∀ t' ∈ Ts, t ≠ t' →
          ‖TA.Nst (Φ eps w) Hd (TA.offK kp s t t') s t t'‖ ≤
            prof3 D C C (Nlet D Ks) T T' δ x Ks i s (1 / t - 1 / t') *
              ∑ p : D.what₂.Tau → Option Bool, (θ p).sum (fun q c => c *
                (((TA.Nst (Φ eps q.2) Hd (TA.offK kp s t t) s t t).re +
                  (TA.Nst (Φ eps q.1) Hd (TA.offK kp s t' t') s t' t').re) / 2)) := by
  have hcond : (i - s) + s ≤ D.R.rS ∨ (2 ≤ s ∧ (i - s) + s = D.R.rS + 1) := by
    rw [Nat.sub_add_cancel hsi]
    by_cases h : i ≤ D.R.rS
    · exact Or.inl h
    · have hi' : i = D.R.rS + 1 := by omega
      refine Or.inr ⟨?_, hi'⟩
      by_contra h2
      exact hns ⟨hi', by omega⟩
  have hLen : GramWordSpace.Len (GramWordSpace.NN D Ks - Ks) w := fun v => by
    have : (w v).length ≤ glen w := Finset.le_sup (f := fun v => (w v).length) (Finset.mem_univ v)
    omega
  have hcbnn : ∀ i s, 0 ≤ cb i s := fun i s => (hM.cb_pos i s).le
  have hjs : (i - s) + s ≤ D.R.rS + 1 := by omega
  obtain ⟨θ, hθ, hmain⟩ := h73 X hM.std (i - s) s hs hcond w hw.1 hLen
  refine ⟨θ, hθ, ?_⟩
  intro eps he Hd kp Ts hHd hTs hkp t ht t' ht' htt
  set P : Finset (TA.Pt D.host.E) := (Hd ×ˢ Ts).image fun y => TA.ext y.1 s y.2 with hPdef
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Hd × (D.what₂.Tau → ℂ) → TA.Pt D.host.E,
      ∀ (y : Hd) (u : D.host.E), u ∈ Ts → ψ (y, tau a (i - s + 1) s u) = TA.ext y.1 s u := by
    refine ⟨fun z => if h : ∃ u ∈ Ts, tau a (i - s + 1) s u = z.2 then TA.ext z.1.1 s h.choose else [], ?_⟩
    intro y u hu
    have hex : ∃ u' ∈ Ts, tau a (i - s + 1) s u' = tau a (i - s + 1) s u := ⟨u, hu, rfl⟩
    simp only
    rw [dif_pos hex, block_tau_injective a hM.a_ne _ _ hex.choose_spec.2]
  have hψP : ∀ (y : Hd) (u : D.host.E), u ∈ Ts → ψ (y, tau a (i - s + 1) s u) ∈ P := fun y u hu => by
    rw [hψ y u hu]
    exact Finset.mem_image.2 ⟨(y.1, u), Finset.mem_product.2 ⟨y.2, hu⟩, rfl⟩
  obtain ⟨W, hW0, hW1⟩ : ∃ W : Hd × (D.what₂.Tau → ℂ) → ℂ, (∀ z, ψ z ∉ P → W z = 0) ∧
      ∀ (y : Hd) (τ : D.what₂.Tau → ℂ), ψ (y, τ) ∈ P → W (y, τ) = ((Real.sqrt c0 * sc X a cb y.1 : ℝ) : ℂ) :=
    ⟨fun z => if ψ z ∈ P then ((Real.sqrt c0 * sc X a cb z.1.1 : ℝ) : ℂ) else 0, fun z hz => if_neg hz,
      fun y τ hz => if_pos hz⟩
  obtain ⟨K, hKdef⟩ : ∃ K : Hd × (D.what₂.Tau → ℂ) → Hd × (D.what₂.Tau → ℂ) → ℂ,
      K = fun z z' => W z * conj (W z') * kp (ψ z') (ψ z) := ⟨_, rfl⟩
  have hK : PSDK K := by
    rw [hKdef]
    exact psd_kernel_weighted_pullback P kp hkp ψ W hW0
  have hKv : ∀ u ∈ Ts, ∀ u' ∈ Ts, (fun h h' : Hd => K (h, tau a (i - s + 1) s u) (h', tau a (i - s + 1) s u')) =
      kapS X a cb c0 Hd (TA.offK kp s u' u) := by
    intro u hu u' hu'
    funext y y'
    rw [hKdef]
    simp only
    rw [hW1 y _ (hψP y u hu), hW1 y' _ (hψP y' u' hu'), hψ y u hu, hψ y' u' hu', Complex.conj_ofReal]
    have e : ((c0 * (sc X a cb y.1 * sc X a cb y'.1) : ℝ) : ℂ) =
        ((Real.sqrt c0 * sc X a cb y.1 : ℝ) : ℂ) * ((Real.sqrt c0 * sc X a cb y'.1 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      have h := Real.mul_self_sqrt hM.lowerConstantNonneg
      calc c0 * (sc X a cb y.1 * sc X a cb y'.1)
          = (Real.sqrt c0 * Real.sqrt c0) * (sc X a cb y.1 * sc X a cb y'.1) := by rw [h]
        _ = _ := by ring
    simp only [kapS, TA.offK]
    rw [e]
    ring
  have htv : ∀ u, u ≠ 0 → ∀ v, tau a (i - s + 1) s u v ≠ 0 := fun u hu v =>
    mul_ne_zero (hM.a_ne _ _ _) ((map_ne_zero (plEmb D v)).2 hu)
  obtain ⟨p, -, hb⟩ := hmain χ hχ eps he Hd (hdS a hM.a_ne (i - s) Hd) K hK (tau a (i - s + 1) s t')
    (tau a (i - s + 1) s t) (htv t' (hTs t' ht')) (htv t (hTs t ht))
  rw [hKv t' ht' t ht, hKv t' ht' t' ht', hKv t ht t ht] at hb
  have hoff : ∀ u ∈ Ts, TA.PSDOn Hd (TA.offK kp s u u) := fun u hu =>
    psd_on_comap P kp hkp Hd (fun h => TA.ext h s u)
      (fun y hy => Finset.mem_image.2 ⟨(y, u), Finset.mem_product.2 ⟨hy, hu⟩, rfl⟩)
  have n0 := Nst_eq_Ns hΦ hcbnn he hw hs hjs Hd hHd (TA.offK kp s t t') (hTs t ht) (hTs t' ht')
  rw [n0, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hcbnn _ _)]
  obtain ⟨hPm, hP⟩ := product_min_factor_profile hM hs hsi hi hns (hTs t ht) (hTs t' ht') htt
  refine weighted_sum_final_bound θ (fun p q => (hθ p).1.1 q) _ _ _ _ _ _ p (hcbnn _ _) hPm hP ?_ ?_ hb
  · intro q
    exact div_nonneg (add_nonneg (Nst_re_nonneg _ Hd _ (hoff t ht) s t) (Nst_re_nonneg _ Hd _ (hoff t' ht') s t'))
      two_pos.le
  · intro q hq
    obtain ⟨hq1, hq2, hq3⟩ := (hθ p).2 q hq
    obtain ⟨w1, w2⟩ := admissible_word_pair hlen hq1 hq2 hq3
    rw [Nst_eq_Ns hΦ hcbnn he w2 hs hjs Hd hHd _ (hTs t ht) (hTs t ht),
      Nst_eq_Ns hΦ hcbnn he w1 hs hjs Hd hHd _ (hTs t' ht') (hTs t' ht'), Complex.re_ofReal_mul,
      Complex.re_ofReal_mul]
    ring

end Lift

end Formalism.MainNotions.BlockEstimateWords

end

end PartP73

section PartPPo0

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Pos

variable {D : D7} {k0 : ℕ} {G : GramWordSpace.GramMap k0 D.R.rS} {X : GramWordSpace.Dat D k0} {χ : ℝ → ℝ} {Ks : ℕ} {E₀ Eg : ℝ}

theorem gram_psdk (hstd : X.Std Ks E₀ Eg) (hχ : IsCutoff χ) (hTop : GramWordSpace.TopPos D G Ks E₀ Eg)
    (hLow : GramWordSpace.LowPos D k0 Ks E₀ Eg) {eps : ℝ} (he : 0 < eps) (v : D.what₂.Tau) (j : ℕ) (w : TopsChoicePartA.Word)
    (hadm : TopsChoicePartA.Admissible (X.I v) w) (hl : w.length ≤ GramWordSpace.NN D Ks) :
    PSDK (fun p p' : Point ℂ j => GramWordSpace.gram G X v j w (X.Fv χ eps v) p p') := by
  unfold GramWordSpace.gram
  by_cases hj : j ≤ D.R.rS
  · simp only [dif_pos hj]
    exact hLow X hstd v j hj w hadm hl χ hχ eps he
  · simp only [dif_neg hj]
    exact PSDK.comap (hTop X hstd v w hadm hl χ hχ eps he) (fun p : Point ℂ j => p.1)

theorem gramS_psdk (hstd : X.Std Ks E₀ Eg) (hχ : IsCutoff χ) (hTop : GramWordSpace.TopPos D G Ks E₀ Eg)
    (hLow : GramWordSpace.LowPos D k0 Ks E₀ Eg) {eps : ℝ} (he : 0 < eps) (v : D.what₂.Tau) (j0 s : ℕ) (w : TopsChoicePartA.Word)
    (hadm : TopsChoicePartA.Admissible (X.I v) w) (hl : w.length ≤ GramWordSpace.NN D Ks) (t : ℂ) :
    PSDK (fun h h' : Point ℂ j0 => GramWordSpace.gramS G X v j0 s w (X.Fv χ eps v) h h' t t) := by
  unfold GramWordSpace.gramS
  by_cases H : 1 ≤ s ∧ X.okT v j0 s t ∧ X.okT v j0 s t
  · simp only [dif_pos H]
    exact PSDK.comap (gram_psdk hstd hχ hTop hLow he v (j0 + s) w hadm hl) (fun h : Point ℂ j0 => GramWordSpace.snoc h t H.2.1.1 s H.1)
  · simp only [dif_neg H]
    intro Y b
    simp

theorem Ns_diag_nonneg (hstd : X.Std Ks E₀ Eg) (hχ : IsCutoff χ) (hTop : GramWordSpace.TopPos D G Ks E₀ Eg)
    (hLow : GramWordSpace.LowPos D k0 Ks E₀ Eg) {eps : ℝ} (he : 0 < eps) (j0 s : ℕ) {w : GramWordSpace.GWord D} (hw : WOK X Ks w)
    (hb : 0 ≤ X.brk w) {Hd : Type} [Fintype Hd] (hd : Hd → GramWordSpace.Head D j0) (κ : Hd → Hd → ℂ) (hκ : PSDK κ)
    (t : D.what₂.Tau → ℂ) : 0 ≤ GramWordSpace.Ns G X j0 s w χ eps hd κ t t := by
  unfold GramWordSpace.Ns
  have h1 : PSDK (fun h h' : Hd => ∏ v, GramWordSpace.gramS G X v j0 s (w v) (X.Fv χ eps v) (hd h v) (hd h' v) (t v) (t v)) :=
    PSDK.prod Finset.univ fun v _ =>
      PSDK.comap (gramS_psdk hstd hχ hTop hLow he v j0 s (w v) (hw.1 v) (hw.2 v) (t v)) (fun h : Hd => hd h v)
  have h2 := PSDK.mul hκ h1 Finset.univ (fun _ => 1)
  simp only [star_one, one_mul, mul_one] at h2
  have h3 : (0 : ℝ) ≤ ∏ v, X.wt v j0 s (t v) * X.wt v j0 s (t v) := Finset.prod_nonneg fun v _ => mul_self_nonneg _
  obtain ⟨hre, him⟩ := Complex.le_def.1 h2
  set S : ℂ := ∑ h, ∑ h', κ h h' * ∏ v, GramWordSpace.gramS G X v j0 s (w v) (X.Fv χ eps v) (hd h v) (hd h' v) (t v) (t v) with hS
  have hSr : S = ((S.re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using him.symm)
  rw [hSr, ← Complex.ofReal_mul, ← Complex.ofReal_div]
  exact Complex.zero_le_real.2 (div_nonneg (mul_nonneg h3 (by simpa using hre)) hb)

end Pos

end Formalism.MainNotions.BlockEstimateWords

end

end PartPPo0

section PartPPo

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Main

variable {D : D7} {k0 : ℕ} {G : GramWordSpace.GramMap k0 D.R.rS} {X : GramWordSpace.Dat D k0}
  {a : ℕ → ℕ → D.what₂.Tau → ℂ} {cb : ℕ → ℕ → ℝ} {c0 : ℝ} {χ : ℝ → ℝ} {Ks : ℕ}
  {E₀ Eg E₁ E₂ E₃ C C4 T T' : ℝ} {δ : D.host.E} {x : D.what₂.Tau → LocalDataRealPlace D} {L : LatticeDataWithDual D} {κL : ℕ → ℕ → ℝ}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Φ : ℝ → GramWordSpace.GWord D → TA.Pt D.host.E → H}

theorem ae_ne_zero (D : D7) : ∀ᵐ t : D.what₂.Tau → ℂ, ∀ v, t v ≠ 0 := by
  refine ae_all_iff.2 fun v => ?_
  rw [ae_iff]
  simp only [not_not]
  rw [volume_pi]
  exact Measure.pi_hyperplane _ v 0

theorem dense_ne_zero (D : D7) : Dense {t : D.what₂.Tau → ℂ | ∀ v, t v ≠ 0} := by
  have h : {t : D.what₂.Tau → ℂ | ∀ v, t v ≠ 0} = Set.pi Set.univ (fun _ => ({0}ᶜ : Set ℂ)) := by
    ext t; simp [Set.mem_pi]
  rw [h]
  exact dense_pi Set.univ (fun v _ => dense_compl_singleton 0)

theorem sgm_zero_ppo (a : ℕ → ℕ → D.what₂.Tau → ℂ) (δ : D.host.E) (i s : ℕ) : sgm a δ i s 0 = 0 := by
  funext v; simp [sgm]

theorem embA_injective (ha : ∀ i s v, a i s v ≠ 0) (i s : ℕ) : Function.Injective (embA a i s) := by
  intro y z h
  obtain ⟨v⟩ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by rw [D.what₂.card_Tau]; exact f_pos D)
  have h1 : a i s v * plEmb D v y = a i s v * plEmb D v z := congrFun h v
  exact (plEmb D v).injective (mul_left_cancel₀ (ha i s v) h1)

theorem poisson_core (hstd : X.Std Ks E₀ Eg) (hχ : IsCutoff χ) (hP : PoissonPi D)
    (h72 : GramWordSpace.SingleLevelGramEstimate D G Ks E₀ Eg E₁ E₂) (hTop : GramWordSpace.TopPos D G Ks E₀ Eg) (hLow : GramWordSpace.LowPos D k0 Ks E₀ Eg)
    {j0 : ℕ} (hj0 : j0 ≤ D.R.rS) {w : GramWordSpace.GWord D} (hw : WOK X Ks w) (hb : 0 ≤ X.brk w)
    (hLen : GramWordSpace.Len (GramWordSpace.NN D Ks - Ks) w) {eps : ℝ} (he : 0 < eps)
    {HdT : Type} [Fintype HdT] (hd : HdT → GramWordSpace.Head D j0) (κ : HdT → HdT → ℂ) (hκ : PSDK κ)
    (La : AddSubgroup (D.what₂.Tau → ℂ)) (κl : ℝ) (hLa : GramWordSpace.IsLat D La κl) (t₀ : D.what₂.Tau → ℂ) (B : ℝ)
    (hB : ∀ S : Finset (D.what₂.Tau → ℂ), (∀ σ ∈ S, σ ∈ GramWordSpace.dualS D La ∧ σ ≠ 0) →
      ∑ σ ∈ S, ‖GramWordSpace.Ntr G X j0 w χ eps hd κ σ‖ ≤ B)
    (S : Finset (D.what₂.Tau → ℂ)) (hS : ∀ z ∈ S, z ∈ La) (hne : ∀ z ∈ S, ∀ v, (t₀ + z) v ≠ 0) :
    κl * ∑ z ∈ S, (GramWordSpace.Ns G X j0 1 w χ eps hd κ (t₀ + z) (t₀ + z)).re ≤ ‖GramWordSpace.Ntr G X j0 w χ eps hd κ 0‖ + B := by
  obtain ⟨hp1, -⟩ := h72 X hstd j0 hj0 w hw.1 hLen
  obtain ⟨⟨φ, hφc, hφe, Cc, hφb⟩, -⟩ := hp1 χ hχ eps he HdT hd κ hκ
  have hpos : ∀ t, 0 ≤ GramWordSpace.Ns G X j0 1 w χ eps hd κ t t := fun t =>
    Ns_diag_nonneg hstd hχ hTop hLow he j0 1 hw hb hd κ hκ t
  have hψe : ∀ t, (∀ v, t v ≠ 0) → (((φ t).re : ℝ) : ℂ) = GramWordSpace.Ns G X j0 1 w χ eps hd κ t t := fun t ht => by
    rw [hφe t ht]
    exact Complex.ext (by simp) (by simpa using (Complex.le_def.1 (hpos t)).2)
  have hψc : Continuous fun t => (φ t).re := Complex.continuous_re.comp hφc
  have hψnn : ∀ t, 0 ≤ (φ t).re := by
    have hcl : IsClosed {t | 0 ≤ (φ t).re} := isClosed_le continuous_const hψc
    have hsub : {t : D.what₂.Tau → ℂ | ∀ v, t v ≠ 0} ⊆ {t | 0 ≤ (φ t).re} := fun t ht => by
      show 0 ≤ (φ t).re
      rw [hφe t ht]
      simpa using (Complex.le_def.1 (hpos t)).1
    intro t
    exact (hcl.closure_subset_iff.2 hsub) (dense_ne_zero D t)
  have htr : ∀ σ : D.what₂.Tau → ℂ, ∫ t, (((φ t).re : ℝ) : ℂ) * ∏ v, TopsChoicePartA.fsC (σ v) (t v) =
      GramWordSpace.Ntr G X j0 w χ eps hd κ σ := fun σ => by
    unfold GramWordSpace.Ntr
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero D] with t ht
    rw [hψe t ht]
  have hK3 : 3 ≤ Ks := by have := hstd.1; omega
  have hdec : ∀ t, |(φ t).re| ≤ |Cc| * ∏ v, ((1 + ‖t v‖) ^ 3)⁻¹ := fun t => by
    have h1 : |(φ t).re| ≤ ‖φ t‖ := Complex.abs_re_le_norm _
    have h2 : (∏ v, (1 + ‖t v‖) ^ (-(3 : ℝ))) ≤ ∏ v, ((1 + ‖t v‖) ^ 3)⁻¹ := by
      refine Finset.prod_le_prod (fun v _ => Real.rpow_nonneg (by positivity) _) fun v _ => ?_
      have hx : (1 : ℝ) ≤ 1 + ‖t v‖ := by linarith [norm_nonneg (t v)]
      have h33 : (1 + ‖t v‖) ^ (3 : ℝ) = (1 + ‖t v‖) ^ 3 := by exact_mod_cast Real.rpow_natCast (1 + ‖t v‖) 3
      rw [Real.rpow_neg (by positivity), h33]
    have h3 : (0 : ℝ) ≤ ∏ v, (1 + ‖t v‖) ^ (-(3 : ℝ)) :=
      Finset.prod_nonneg fun v _ => Real.rpow_nonneg (by positivity) _
    calc |(φ t).re| ≤ ‖φ t‖ := h1
      _ ≤ Cc * ∏ v, (1 + ‖t v‖) ^ (-(3 : ℝ)) := hφb t
      _ ≤ |Cc| * ∏ v, (1 + ‖t v‖) ^ (-(3 : ℝ)) := mul_le_mul_of_nonneg_right (le_abs_self _) h3
      _ ≤ |Cc| * ∏ v, ((1 + ‖t v‖) ^ 3)⁻¹ := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have key := hP La κl hLa (fun t => (φ t).re) |Cc| hψc hdec hψnn t₀ B
    (fun S' hS' => by simp only [htr]; exact hB S' hS') S hS
  beta_reduce at key
  have h0 : ∫ t, (((φ t).re : ℝ) : ℂ) = GramWordSpace.Ntr G X j0 w χ eps hd κ 0 := by
    rw [← htr 0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp [TopsChoicePartA.fsC]
  rw [h0] at key
  refine le_of_eq_of_le ?_ key
  congr 1
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [hφe _ (hne z hz)]

theorem poisson_preparation (hM : Mod D X a cb c0 Ks E₀ Eg E₁ E₂ E₃ C C4 T T' δ x L κL) (hχ : IsCutoff χ) (hP : PoissonPi D)
    (h72 : GramWordSpace.SingleLevelGramEstimate D G Ks E₀ Eg E₁ E₂) (hTop : GramWordSpace.TopPos D G Ks E₀ Eg) (hLow : GramWordSpace.LowPos D k0 Ks E₀ Eg)
    (hΦ : GramId G X a cb c0 χ hM.a_ne Ks Φ)
    {j0 : ℕ} (hj0 : j0 ≤ D.R.rS) {w : GramWordSpace.GWord D} (hw : WOK X Ks w)
    (hlen : glen w + Ks ≤ GramWordSpace.NN D Ks) {eps : ℝ} (he : 0 < eps)
    (Hd : Finset (TA.Pt D.host.E)) (kap : TA.Pt D.host.E → TA.Pt D.host.E → ℂ)
    (hHd : ∀ h ∈ Hd, TA.IsPt j0 h) (hk : TA.PSDOn Hd kap) (t0 : D.host.E) (Ts : Finset D.host.E)
    (hT : ∀ t ∈ Ts, t ≠ 0 ∧ t - t0 ∈ (L.La (j0 + 1) 1).toAddSubgroup) (B : ℝ)
    (hB : ∀ Ls : Finset D.host.E, (∀ l ∈ Ls, l ∈ taLv D δ L (j0 + 1) ∧ l ≠ 0) →
      ∑ l ∈ Ls, ‖GramWordSpace.Ntr G X j0 w χ eps (hdS a hM.a_ne j0 Hd) (kapS X a cb c0 Hd kap) (sgm a δ (j0 + 1) 1 l)‖ ≤ B) :
    ∑ t ∈ Ts, (TA.Nst (Φ eps w) Hd kap 1 t t).re ≤
      ‖GramWordSpace.Ntr G X j0 w χ eps (hdS a hM.a_ne j0 Hd) (kapS X a cb c0 Hd kap) (sgm a δ (j0 + 1) 1 0)‖ + B := by
  have hLen : GramWordSpace.Len (GramWordSpace.NN D Ks - Ks) w := fun v => by
    have h1 : (w v).length ≤ glen w := Finset.le_sup (f := fun v => (w v).length) (Finset.mem_univ v)
    omega
  have hκ : PSDK (kapS X a cb c0 Hd kap) := kapS_psdk hM.lowerConstantNonneg Hd kap hk
  have hblk : IsBlockSL2Embedding D (j0 + 1) 1 := ⟨by omega, le_rfl, by omega⟩
  have hB' : ∀ S : Finset (D.what₂.Tau → ℂ), (∀ σ ∈ S, σ ∈ GramWordSpace.dualS D (laC a L (j0 + 1) 1) ∧ σ ≠ 0) →
      ∑ σ ∈ S, ‖GramWordSpace.Ntr G X j0 w χ eps (hdS a hM.a_ne j0 Hd) (kapS X a cb c0 Hd kap) σ‖ ≤ B := by
    intro S hS
    have hex : ∀ σ ∈ S, ∃ l ∈ dualPsi D δ (L.La (j0 + 1) 1), σ = sgm a δ (j0 + 1) 1 l := fun σ hσ =>
      hM.dual _ _ hblk σ (hS σ hσ).1
    choose! lf hlf1 hlf2 using hex
    have hinj : Set.InjOn lf (S : Set (D.what₂.Tau → ℂ)) := fun σ hσ σ' hσ' e =>
      (hlf2 σ hσ).trans ((congrArg (sgm a δ (j0 + 1) 1) e).trans (hlf2 σ' hσ').symm)
    have h1 := hB (S.image lf) (fun l hl => by
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hl
      refine ⟨(show lf σ ∈ taLv D δ L (j0 + 1) from hlf1 σ hσ), fun h0 => (hS σ hσ).2 ?_⟩
      rw [hlf2 σ hσ, h0]
      exact sgm_zero_ppo a δ (j0 + 1) 1)
    rw [Finset.sum_image hinj] at h1
    refine le_of_eq_of_le (Finset.sum_congr rfl fun σ hσ => ?_) h1
    rw [← hlf2 σ hσ]
  have hS : ∀ z ∈ Ts.image (fun t => embA a (j0 + 1) 1 (t - t0)), z ∈ laC a L (j0 + 1) 1 := fun z hz => by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hz
    show embA a (j0 + 1) 1 (t - t0) ∈ (L.La (j0 + 1) 1).toAddSubgroup.map (embA a (j0 + 1) 1)
    exact AddSubgroup.mem_map.2 ⟨t - t0, (hT t ht).2, rfl⟩
  have hadd : ∀ t, tau a (j0 + 1) 1 t0 + embA a (j0 + 1) 1 (t - t0) = tau a (j0 + 1) 1 t := fun t => by
    have h1 : embA a (j0 + 1) 1 t0 + embA a (j0 + 1) 1 (t - t0) = embA a (j0 + 1) 1 t := by
      rw [← map_add, add_sub_cancel]
    exact h1
  have hne : ∀ z ∈ Ts.image (fun t => embA a (j0 + 1) 1 (t - t0)), ∀ v, (tau a (j0 + 1) 1 t0 + z) v ≠ 0 := fun z hz v => by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hz
    rw [hadd t]
    exact mul_ne_zero (hM.a_ne _ _ _) ((map_ne_zero (plEmb D v)).2 (hT t ht).1)
  have hcore := poisson_core hM.std hχ hP h72 hTop hLow hj0 hw (hM.brk_pos w hw.1).le hLen he
    (hdS a hM.a_ne j0 Hd) (kapS X a cb c0 Hd kap) hκ (laC a L (j0 + 1) 1) (κL (j0 + 1) 1) (hM.lat _ _ hblk)
    (tau a (j0 + 1) 1 t0) B hB' (Ts.image fun t => embA a (j0 + 1) 1 (t - t0)) hS hne
  rw [sgm_zero_ppo]
  refine le_of_eq_of_le ?_ hcore
  rw [Finset.sum_image (fun t _ t' _ e => sub_left_inj.1 (embA_injective hM.a_ne _ _ e)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [hadd t, Nst_eq_Ns hΦ (fun i s => (hM.cb_pos i s).le) he hw le_rfl (by omega) Hd hHd kap (hT t ht).1 (hT t ht).1,
    Complex.re_ofReal_mul, hM.cb1 (j0 + 1) (by omega) (by omega)]

theorem prePoisson (hM : Mod D X a cb c0 Ks E₀ Eg E₁ E₂ E₃ C C4 T T' δ x L κL) (hχ : IsCutoff χ) (hP : PoissonPi D)
    (h72 : GramWordSpace.SingleLevelGramEstimate D G Ks E₀ Eg E₁ E₂) (hTop : GramWordSpace.TopPos D G Ks E₀ Eg) (hLow : GramWordSpace.LowPos D k0 Ks E₀ Eg)
    (hΦ : GramId G X a cb c0 χ hM.a_ne Ks Φ)
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ D.R.rS + 1) {w : GramWordSpace.GWord D} (hw : WOK X Ks w)
    (hlen : glen w + Ks ≤ GramWordSpace.NN D Ks) {eps : ℝ} (he : 0 < eps)
    (Hd : Finset (TA.Pt D.host.E)) (kap : TA.Pt D.host.E → TA.Pt D.host.E → ℂ)
    (hHd : ∀ h ∈ Hd, TA.IsPt (i - 1) h) (hk : TA.PSDOn Hd kap) (t0 : D.host.E) (Ts : Finset D.host.E)
    (hT : ∀ t ∈ Ts, t ≠ 0 ∧ t - t0 ∈ (L.La i 1).toAddSubgroup) (B : ℝ)
    (hB : ∀ Ls : Finset D.host.E, (∀ l ∈ Ls, l ∈ taLv D δ L i ∧ l ≠ 0) →
      ∑ l ∈ Ls, ‖trS G X a cb c0 χ hM.a_ne δ eps i w Hd kap l‖ ≤ B) :
    ∑ t ∈ Ts, (TA.Nst (Φ eps w) Hd kap 1 t t).re ≤ ‖trS G X a cb c0 χ hM.a_ne δ eps i w Hd kap 0‖ + B := by
  obtain ⟨j0, rfl⟩ : ∃ j0, i = j0 + 1 := ⟨i - 1, by omega⟩
  exact poisson_preparation hM hχ hP h72 hTop hLow hΦ (by omega) hw hlen he Hd kap hHd hk t0 Ts hT B hB

end Main

end Formalism.MainNotions.BlockEstimateWords

end

end PartPPo

section PartVec

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

theorem psdk_blockDiag {α β : Type*} (c : α → β) (k : α → α → ℂ)
    (h : ∀ b, ∃ g : α → α → ℂ, PSDK g ∧ ∀ x y, c x = b → c y = b → k x y = g x y) :
    PSDK (fun x y => if c x = c y then k x y else 0) := by
  choose g hg hk using h
  intro Y a
  have key : ∀ p ∈ Y, ∀ q ∈ Y, star (a p) * (if c p = c q then k p q else 0) * a q =
      ∑ b ∈ Y.image c, star (a p * (if c p = b then 1 else 0)) * g b p q * (a q * (if c q = b then 1 else 0)) := by
    intro p hp q _
    rw [Finset.sum_eq_single (c p)]
    · by_cases hpq : c p = c q
      · rw [if_pos hpq, if_pos rfl, if_pos hpq.symm, hk (c p) p q rfl hpq.symm]
        simp
      · rw [if_neg hpq, if_pos rfl, if_neg (fun e => hpq e.symm)]
        simp
    · intro b _ hb
      rw [if_neg (fun e => hb e.symm)]
      simp
    · intro hn
      exact absurd (Finset.mem_image_of_mem c hp) hn
  have e : ∑ p ∈ Y, ∑ q ∈ Y, star (a p) * (if c p = c q then k p q else 0) * a q =
      ∑ b ∈ Y.image c, ∑ p ∈ Y, ∑ q ∈ Y,
        star (a p * (if c p = b then 1 else 0)) * g b p q * (a q * (if c q = b then 1 else 0)) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun p hp => key p hp q hq]
    rw [Finset.sum_congr rfl fun q _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
  rw [e]
  exact Finset.sum_nonneg fun b _ => hg b Y (fun p => a p * (if c p = b then 1 else 0))

theorem exists_gram_two {α₁ α₂ : Type} {P : α₁ → α₁ → ℂ} {K : α₂ → α₂ → ℂ} (hP : PSDK P) (hK : PSDK K)
    (d₁ : α₁) (d₂ : α₂) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (V₁ : α₁ → H) (V₂ : α₂ → H),
      (∀ p q, ⟪V₁ p, V₁ q⟫_ℂ = P q p) ∧ (∀ p q, ⟪V₂ p, V₂ q⟫_ℂ = K q p) := by
  let pr1 : α₁ ⊕ α₂ → α₁ := Sum.elim id (fun _ => d₁)
  let pr2 : α₁ ⊕ α₂ → α₂ := Sum.elim (fun _ => d₂) id
  let k : α₁ ⊕ α₂ → α₁ ⊕ α₂ → ℂ := fun x y => if x.isLeft = true then P (pr1 x) (pr1 y) else K (pr2 x) (pr2 y)
  have hk := psdk_blockDiag (fun x : α₁ ⊕ α₂ => x.isLeft) k (by
    intro b
    cases b with
    | true => exact ⟨fun x y => P (pr1 x) (pr1 y), PSDK.comap hP pr1, fun x y hx _ => by simp only [k, hx, if_true]⟩
    | false =>
      refine ⟨fun x y => K (pr2 x) (pr2 y), PSDK.comap hK pr2, fun x y hx _ => ?_⟩
      simp only [k, hx]
      simp)
  obtain ⟨H, i1, i2, i3, V, hV⟩ := exists_gram_transpose hk
  refine ⟨H, i1, i2, i3, fun p => V (Sum.inl p), fun p => V (Sum.inr p), fun p q => ?_, fun p q => ?_⟩
  · rw [hV]; simp [k, pr1]
  · rw [hV]; simp [k, pr2]

section Vec

variable {D : D7} {k0 : ℕ} (G : GramWordSpace.GramMap k0 D.R.rS) (X : GramWordSpace.Dat D k0)
  (a : ℕ → ℕ → D.what₂.Tau → ℂ) (cb : ℕ → ℕ → ℝ) (c0 : ℝ) (χ : ℝ → ℝ)

theorem brk_nonneg (w : GramWordSpace.GWord D) : 0 ≤ X.brk w := by
  unfold GramWordSpace.Dat.brk
  refine Finset.prod_nonneg fun v _ => ?_
  unfold brkW
  refine List.prod_nonneg fun x hx => ?_
  obtain ⟨Y, _, rfl⟩ := List.mem_map.1 hx
  exact norm_nonneg _

theorem lpt_val_vec (ha : ∀ i s v, a i s v ≠ 0) {j : ℕ} {p : TA.Pt D.host.E} (hp : TA.IsPt j p) (v : D.what₂.Tau) :
    (lpt a ha j p v).1 = lbF a v 0 p := by
  have h : lpt a ha j p v = ⟨lbF a v 0 p, (lbF_ok a ha v p 0 hp.2).1,
      by rw [(lbF_ok a ha v p 0 hp.2).2]; exact hp.1⟩ := dif_pos hp
  rw [h]

theorem gram_psdk_vec {Ks : ℕ} {E₀ Eg : ℝ} (hstd : X.Std Ks E₀ Eg) (hχ : IsCutoff χ) (hTop : GramWordSpace.TopPos D G Ks E₀ Eg)
    (hLow : GramWordSpace.LowPos D k0 Ks E₀ Eg) {eps : ℝ} (he : 0 < eps) {w : GramWordSpace.GWord D} (hw : WOK X Ks w)
    (v : D.what₂.Tau) (j : ℕ) :
    PSDK (fun p p' : Point ℂ j => GramWordSpace.gram G X v j (w v) (X.Fv χ eps v) p p') := by
  by_cases hj : j ≤ D.R.rS
  · have h := hLow X hstd v j hj (w v) (hw.1 v) (hw.2 v) χ hχ eps he
    have e : (fun p p' : Point ℂ j => GramWordSpace.gram G X v j (w v) (X.Fv χ eps v) p p') =
        fun p p' => X.gramLow v j hj (w v) (X.Fv χ eps v) p p' := by
      funext p p'; simp only [GramWordSpace.gram, dif_pos hj]
    rw [e]; exact h
  · have h := hTop X hstd v (w v) (hw.1 v) (hw.2 v) χ hχ eps he
    have e : (fun p p' : Point ℂ j => GramWordSpace.gram G X v j (w v) (X.Fv χ eps v) p p') =
        fun p p' => G.top (X.B v) (X.I v) (w v) (X.Fv χ eps v) p.1 p'.1 := by
      funext p p'; simp only [GramWordSpace.gram, dif_neg hj]
    rw [e]; exact PSDK.comap h (fun p : Point ℂ j => p.1)

theorem Gk_psdk (ha : ∀ i s v, a i s v ≠ 0) {Ks : ℕ} {E₀ Eg : ℝ} (hstd : X.Std Ks E₀ Eg) (hc0 : 0 ≤ c0) (hχ : IsCutoff χ)
    (hTop : GramWordSpace.TopPos D G Ks E₀ Eg) (hLow : GramWordSpace.LowPos D k0 Ks E₀ Eg) {eps : ℝ} (he : 0 < eps)
    {w : GramWordSpace.GWord D} (hw : WOK X Ks w) (j : ℕ) :
    PSDK (fun p p' : TA.Pt D.host.E => Gk G X a cb c0 χ ha eps w j p p') := by
  have h1 : PSDK (fun p q : TA.Pt D.host.E => ((sc X a cb p : ℝ) : ℂ) * conj ((sc X a cb q : ℝ) : ℂ)) :=
    PSDK.rankOne (fun p => ((sc X a cb p : ℝ) : ℂ))
  have h2 := PSDK.prod (α := TA.Pt D.host.E) Finset.univ
    (K := fun v p q => GramWordSpace.gram G X v j (w v) (X.Fv χ eps v) (lpt a ha j p v) (lpt a ha j q v))
    fun v _ => PSDK.comap (gram_psdk_vec G X χ hstd hχ hTop hLow he hw v j) (fun p => lpt a ha j p v)
  have h3 := PSDK.smul (PSDK.mul h1 h2) (div_nonneg hc0 (brk_nonneg X w))
  have e : (fun p p' : TA.Pt D.host.E => Gk G X a cb c0 χ ha eps w j p p') =
      fun p q => ((c0 / X.brk w : ℝ) : ℂ) * (((sc X a cb p : ℝ) : ℂ) * conj ((sc X a cb q : ℝ) : ℂ) *
        ∏ v ∈ Finset.univ, GramWordSpace.gram G X v j (w v) (X.Fv χ eps v) (lpt a ha j p v) (lpt a ha j q v)) := by
    funext p q
    unfold Gk
    rw [Complex.conj_ofReal]
    push_cast
    ring
  rw [e]; exact h3

theorem Gk_top (ha : ∀ i s v, a i s v ≠ 0) (eps : ℝ) {p p' : TA.Pt D.host.E} (hp : TA.IsPt (D.R.rS + 1) p)
    (hp' : TA.IsPt (D.R.rS + 1) p') :
    Gk G X a cb c0 χ ha eps w00 (D.R.rS + 1) p p' = ((c0 * (sc X a cb p * sc X a cb p') : ℝ) : ℂ) *
      ∏ v, hsInner (G.V (X.B v) (X.Fv χ eps v) (lbF a v 0 p)) (G.V (X.B v) (X.Fv χ eps v) (lbF a v 0 p')) := by
  have hb : X.brk w00 = 1 := by simp [GramWordSpace.Dat.brk, w00, brkW]
  have hg : ∀ v, GramWordSpace.gram G X v (D.R.rS + 1) (w00 v) (X.Fv χ eps v) (lpt a ha (D.R.rS + 1) p v)
      (lpt a ha (D.R.rS + 1) p' v) =
      hsInner (G.V (X.B v) (X.Fv χ eps v) (lbF a v 0 p)) (G.V (X.B v) (X.Fv χ eps v) (lbF a v 0 p')) := by
    intro v
    have hn : ¬ D.R.rS + 1 ≤ D.R.rS := by omega
    simp only [GramWordSpace.gram, dif_neg hn]
    rw [lpt_val_vec a ha hp, lpt_val_vec a ha hp']
    exact G.top_nil _ _ _ _ _
  unfold Gk
  rw [hb, Finset.prod_congr rfl fun v _ => hg v]
  simp

theorem Gk_zero (ha : ∀ i s v, a i s v ≠ 0) (eps : ℝ) (w : GramWordSpace.GWord D) :
    Gk G X a cb c0 χ ha eps w 0 [] [] = (c0 : ℂ) * X.energy w χ eps / (X.brk w : ℂ) := by
  have hp : TA.IsPt (E := D.host.E) 0 [] := ⟨by simp [TA.lvl], fun b hb => by simp at hb⟩
  have hs : sc X a cb ([] : TA.Pt D.host.E) = 1 := by simp [sc, nF, wF]
  have hl : ∀ v, lpt a ha 0 [] v = GramWordSpace.pt0 := fun v => Subtype.ext (by rw [lpt_val_vec a ha hp]; rfl)
  unfold Gk GramWordSpace.Dat.energy
  rw [hs]
  simp only [hl, GramWordSpace.gram, dif_pos (Nat.zero_le D.R.rS), mul_one]

def vkCl (x : ℝ × GramWordSpace.GWord D × TA.Pt D.host.E) : ℝ × GramWordSpace.GWord D × ℕ := (x.1, x.2.1, TA.lvl x.2.2)

def vkK (ha : ∀ i s v, a i s v ≠ 0) (Ks : ℕ) (x y : ℝ × GramWordSpace.GWord D × TA.Pt D.host.E) : ℂ :=
  if 0 < x.1 ∧ WOK X Ks x.2.1 then Gk G X a cb c0 χ ha x.1 x.2.1 (TA.lvl x.2.2) x.2.2 y.2.2 else 0

def vkSf (p : TA.Pt D.host.E) : ℂ := ((Real.sqrt c0 * sc X a cb p : ℝ) : ℂ)

theorem vkSf_mul (hc0 : 0 ≤ c0) (p p' : TA.Pt D.host.E) :
    conj (vkSf X a cb c0 p) * vkSf X a cb c0 p' = ((c0 * (sc X a cb p' * sc X a cb p) : ℝ) : ℂ) := by
  unfold vkSf
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul]
  congr 1
  calc Real.sqrt c0 * sc X a cb p * (Real.sqrt c0 * sc X a cb p')
      = (Real.sqrt c0 * Real.sqrt c0) * (sc X a cb p' * sc X a cb p) := by ring
    _ = c0 * (sc X a cb p' * sc X a cb p) := by rw [Real.mul_self_sqrt hc0]

theorem exists_vectors (ha : ∀ i s v, a i s v ≠ 0) (Ks : ℕ) (E₀ Eg : ℝ) (hstd : X.Std Ks E₀ Eg) (hc0 : 0 ≤ c0)
    (hχ : IsCutoff χ) (hTop : GramWordSpace.TopPos D G Ks E₀ Eg) (hLow : GramWordSpace.LowPos D k0 Ks E₀ Eg) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (Φ : ℝ → GramWordSpace.GWord D → TA.Pt D.host.E → H) (Wv : TA.Pt D.host.E → H),
      GramId G X a cb c0 χ ha Ks Φ ∧ (∀ p p', ⟪Wv p, Wv p'⟫_ℂ = GkLim G X a cb c0 p' p) ∧
      ∀ eps p, TA.IsPt (D.R.rS + 1) p →
        (∀ v, G.V (X.B v) (X.Fv χ eps v) (lbF a v 0 p) = G.V (X.B v) (X.f v) (lbF a v 0 p)) → Φ eps w00 p = Wv p := by
  have hP := PSDK.prod (α := ∀ v, (X.B v).Wq →L[ℂ] (X.B v).Wp) Finset.univ
    (K := fun v t t' => hsInner (t v) (t' v))
    fun v _ => PSDK.comap ta_psdk_hsInner (fun t : (∀ v, (X.B v).Wq →L[ℂ] (X.B v).Wp) => t v)
  have hK := psdk_blockDiag (vkCl (D := D)) (vkK G X a cb c0 χ ha Ks) (by
    intro b
    by_cases hb : 0 < b.1 ∧ WOK X Ks b.2.1
    · refine ⟨fun x y => Gk G X a cb c0 χ ha b.1 b.2.1 b.2.2 x.2.2 y.2.2,
        PSDK.comap (Gk_psdk G X a cb c0 χ ha hstd hc0 hχ hTop hLow hb.1 hb.2 b.2.2)
          (fun x : ℝ × GramWordSpace.GWord D × TA.Pt D.host.E => x.2.2), fun x y hx _ => ?_⟩
      subst hx
      exact if_pos hb
    · refine ⟨fun _ _ => 0, fun Y c => by simp, fun x y hx _ => ?_⟩
      subst hx
      exact if_neg hb)
  obtain ⟨H, i1, i2, i3, V₁, V₂, h1, h2⟩ := exists_gram_two hP hK (fun _ => 0) ((0 : ℝ), w00, [])
  refine ⟨H, i1, i2, i3,
    fun eps w p => if w = w00 ∧ TA.lvl p = D.R.rS + 1 then
      vkSf X a cb c0 p • V₁ (fun v => G.V (X.B v) (X.Fv χ eps v) (lbF a v 0 p)) else V₂ (eps, w, p),
    fun p => vkSf X a cb c0 p • V₁ (fun v => G.V (X.B v) (X.f v) (lbF a v 0 p)), ?_, ?_, ?_⟩
  · intro eps he w hw j _ p p' hp hp'
    by_cases hc : w = w00 ∧ j = D.R.rS + 1
    · obtain ⟨rfl, rfl⟩ := hc
      simp only []
      rw [if_pos ⟨trivial, hp.1⟩, if_pos ⟨trivial, hp'.1⟩, inner_smul_left, inner_smul_right, h1, ← mul_assoc,
        vkSf_mul X a cb c0 hc0, Gk_top G X a cb c0 χ ha eps hp' hp]
    · have n1 : ¬ (w = w00 ∧ TA.lvl p = D.R.rS + 1) := fun h => hc ⟨h.1, hp.1 ▸ h.2⟩
      have n2 : ¬ (w = w00 ∧ TA.lvl p' = D.R.rS + 1) := fun h => hc ⟨h.1, hp'.1 ▸ h.2⟩
      simp only []
      rw [if_neg n1, if_neg n2, h2]
      have hcl : vkCl (D := D) (eps, w, p') = vkCl (eps, w, p) := by simp only [vkCl, hp.1, hp'.1]
      rw [if_pos hcl]
      have hk : vkK G X a cb c0 χ ha Ks (eps, w, p') (eps, w, p) =
          Gk G X a cb c0 χ ha eps w (TA.lvl p') p' p := if_pos ⟨he, hw⟩
      rw [hk, hp'.1]
  · intro p p'
    rw [inner_smul_left, inner_smul_right, h1, ← mul_assoc, vkSf_mul X a cb c0 hc0]
    rfl
  · intro eps p hp hv
    simp only []
    rw [if_pos ⟨trivial, hp.1⟩, funext hv]

theorem energy_tendsto (ha : ∀ i s v, a i s v ≠ 0) (Ks : ℕ) (E₀ Eg : ℝ) (hstd : X.Std Ks E₀ Eg) (hχ : IsCutoff χ)
    (hE : GramWordSpace.E D k0 Ks E₀ Eg) (hbrk : ∀ w, X.admitted w → 0 < X.brk w)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Φ : ℝ → GramWordSpace.GWord D → TA.Pt D.host.E → H}
    (hΦ : GramId G X a cb c0 χ ha Ks Φ) {w : GramWordSpace.GWord D} (hw : WOK X Ks w) :
    Tendsto (fun eps => ‖Φ eps w []‖ ^ 2) (𝓝[>] 0) (𝓝 (c0 * X.jn2.re)) := by
  have hp : TA.IsPt (E := D.host.E) 0 [] := ⟨by simp [TA.lvl], fun b hb => by simp at hb⟩
  have h1 : ∀ eps : ℝ, 0 < eps → ‖Φ eps w []‖ ^ 2 = ((c0 : ℂ) * X.energy w χ eps / (X.brk w : ℂ)).re := by
    intro eps he
    have h := hΦ eps he w hw 0 (Nat.zero_le _) [] [] hp hp
    rw [Gk_zero] at h
    have h' := inner_self_eq_norm_sq (𝕜 := ℂ) (Φ eps w [])
    rw [h] at h'
    exact h'.symm
  have h2 := hE X hstd χ hχ w hw.1 hw.2
  have h3 : Tendsto (fun eps => ((c0 : ℂ) * X.energy w χ eps / (X.brk w : ℂ)).re) (𝓝[>] 0)
      (𝓝 (((c0 : ℂ) * ((X.brk w : ℂ) * X.jn2) / (X.brk w : ℂ)).re)) :=
    (Complex.continuous_re.tendsto _).comp ((h2.const_mul _).div_const _)
  have h4 : ((c0 : ℂ) * ((X.brk w : ℂ) * X.jn2) / (X.brk w : ℂ)).re = c0 * X.jn2.re := by
    have hb : (X.brk w : ℂ) ≠ 0 := by exact_mod_cast (hbrk w hw.1).ne'
    rw [show (c0 : ℂ) * ((X.brk w : ℂ) * X.jn2) / (X.brk w : ℂ) = (c0 : ℂ) * X.jn2 by field_simp,
      Complex.re_ofReal_mul]
  rw [h4] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with eps he
  exact (h1 eps he).symm

end Vec

end Formalism.MainNotions.BlockEstimateWords

end

end PartVec

section PartClosed

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

theorem exists_closed {W : Type} (child : W → Finset W) (μ : W → ℕ) (M : ℕ) (P : W → Prop)
    (hgrow : ∀ w, ∀ w' ∈ child w, w' = w ∨ μ w < μ w') (hbd : ∀ w, ∀ w' ∈ child w, μ w' ≤ M)
    (hP : ∀ w, P w → ∀ w' ∈ child w, P w') (w0 : W) (h0 : P w0) :
    ∃ S : Finset W, w0 ∈ S ∧ (∀ w ∈ S, P w) ∧ ∀ w ∈ S, child w ⊆ S := by
  let stage : ℕ → Finset W := fun n => Nat.rec {w0} (fun _ S => S ∪ S.biUnion child) n
  have hs0 : stage 0 = {w0} := rfl
  have hss : ∀ n, stage (n + 1) = stage n ∪ (stage n).biUnion child := fun n => rfl
  have hnew : ∀ n, ∀ w ∈ stage (n + 1), w ∉ stage n → ∃ u ∈ stage n, w ∈ child u := by
    intro n w hw hn
    rw [hss, Finset.mem_union] at hw
    rcases hw with hw | hw
    · exact absurd hw hn
    · exact Finset.mem_biUnion.1 hw
  have hA : ∀ n, ∀ w ∈ stage (n + 1), w ∉ stage n → n + 1 ≤ μ w := by
    intro n
    induction n with
    | zero =>
      intro w hw hn
      obtain ⟨u, hu, hwu⟩ := hnew 0 w hw hn
      rcases hgrow u w hwu with h | h
      · exact absurd (h ▸ hu) hn
      · omega
    | succ n ih =>
      intro w hw hn
      obtain ⟨u, hu, hwu⟩ := hnew (n + 1) w hw hn
      have hun : u ∉ stage n := by
        intro hun
        apply hn
        rw [hss, Finset.mem_union]
        exact Or.inr (Finset.mem_biUnion.2 ⟨u, hun, hwu⟩)
      have h1 := ih u hu hun
      rcases hgrow u w hwu with h | h
      · exact absurd (h ▸ hu) hn
      · omega
  have hPs : ∀ n, ∀ w ∈ stage n, P w := by
    intro n
    induction n with
    | zero => intro w hw; rw [hs0, Finset.mem_singleton] at hw; exact hw ▸ h0
    | succ n ih =>
      intro w hw
      rw [hss, Finset.mem_union] at hw
      rcases hw with hw | hw
      · exact ih w hw
      · obtain ⟨u, hu, hwu⟩ := Finset.mem_biUnion.1 hw
        exact hP u (ih u hu) w hwu
  have hw0 : ∀ n, w0 ∈ stage n := by
    intro n
    induction n with
    | zero => rw [hs0]; exact Finset.mem_singleton_self _
    | succ n ih => rw [hss]; exact Finset.mem_union_left _ ih
  refine ⟨stage M, hw0 M, hPs M, fun w hw w' hw' => ?_⟩
  by_contra hn
  have h1 : w' ∈ stage (M + 1) := by
    rw [hss, Finset.mem_union]
    exact Or.inr (Finset.mem_biUnion.2 ⟨w, hw, hw'⟩)
  have h2 := hA M w' h1 hn
  have h3 := hbd w w' hw'
  omega

end Formalism.MainNotions.BlockEstimateWords

end

end PartClosed

section PartR0

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Sums

variable {W : Type}

theorem fsum_coe (S : Finset W) (θ : W →₀ ℝ) (hθ : θ.support ⊆ S) (g : W → ℝ) :
    θ.sum (fun w c => c * g w) = ∑ w : S, θ w.1 * g w.1 := by
  rw [Finsupp.sum, Finset.sum_coe_sort S (fun w => θ w * g w)]
  refine Finset.sum_subset hθ fun w _ hw => ?_
  rw [Finsupp.notMem_support_iff.1 hw, zero_mul]

theorem fsum_one_coe (S : Finset W) (θ : W →₀ ℝ) (hθ : θ.support ⊆ S) :
    θ.sum (fun _ c => c) = ∑ w : S, θ w.1 := by
  have := fsum_coe S θ hθ (fun _ => 1)
  simpa using this

theorem fsum_pair_coe (S : Finset W) (θ : W × W →₀ ℝ) (hθ : ∀ q ∈ θ.support, q.1 ∈ S ∧ q.2 ∈ S) (g : W × W → ℝ) :
    θ.sum (fun q c => c * g q) = ∑ y : S × S, θ (y.2.1, y.1.1) * g (y.2.1, y.1.1) := by
  have h1 : θ.support ⊆ S ×ˢ S := fun q hq => Finset.mem_product.2 (hθ q hq)
  have h2 : θ.sum (fun q c => c * g q) = ∑ q ∈ S ×ˢ S, θ q * g q := by
    rw [Finsupp.sum]
    refine Finset.sum_subset h1 fun w _ hw => ?_
    rw [Finsupp.notMem_support_iff.1 hw, zero_mul]
  rw [h2, Finset.sum_product, Fintype.sum_prod_type, Finset.sum_comm' (t' := S) (s' := fun _ => S) (by simp [and_comm])]
  rw [← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun y1 _ => ?_
  rw [← Finset.sum_coe_sort S]

end Sums

section Words

variable {D : D7}

def ExtK (K : ℕ) (w w' : GramWordSpace.GWord D) : Prop := ∀ v, ∃ l : TopsChoicePartA.Word, l.length ≤ K ∧ w' v = l ++ w v

def gtot (w : GramWordSpace.GWord D) : ℕ := ∑ v, (w v).length

theorem le_glen (w : GramWordSpace.GWord D) (v : D.what₂.Tau) : (w v).length ≤ glen w :=
  Finset.le_sup (f := fun v => (w v).length) (Finset.mem_univ v)

theorem glen_le {w : GramWordSpace.GWord D} {B : ℕ} (h : ∀ v, (w v).length ≤ B) : glen w ≤ B :=
  Finset.sup_le fun v _ => h v

theorem ExtK.glen_le {K : ℕ} {w w' : GramWordSpace.GWord D} (h : ExtK K w w') : glen w' ≤ glen w + K := by
  refine Formalism.MainNotions.BlockEstimateWords.glen_le fun v => ?_
  obtain ⟨l, hl, e⟩ := h v
  rw [e, List.length_append]
  have := le_glen w v
  omega

theorem ExtK.grow {K : ℕ} {w w' : GramWordSpace.GWord D} (h : ExtK K w w') : w' = w ∨ gtot w < gtot w' := by
  by_cases h0 : ∀ v, (w' v).length ≤ (w v).length
  · left
    funext v
    obtain ⟨l, _, e⟩ := h v
    have := h0 v
    rw [e, List.length_append] at this
    have hl : l = [] := List.length_eq_zero_iff.1 (by omega)
    rw [e, hl, List.nil_append]
  · right
    push_neg at h0
    obtain ⟨v0, hv0⟩ := h0
    refine Finset.sum_lt_sum (fun v _ => ?_) ⟨v0, Finset.mem_univ _, hv0⟩
    obtain ⟨l, _, e⟩ := h v
    rw [e, List.length_append]
    omega

theorem gtot_le {w : GramWordSpace.GWord D} {B : ℕ} (h : GramWordSpace.Len B w) : gtot w ≤ Fintype.card D.what₂.Tau * B := by
  unfold gtot
  calc ∑ v, (w v).length ≤ ∑ _v : D.what₂.Tau, B := Finset.sum_le_sum fun v _ => h v
    _ = Fintype.card D.what₂.Tau * B := by simp

theorem ExtK.len {K B : ℕ} {w w' : GramWordSpace.GWord D} (h : ExtK K w w') (hB : glen w + K ≤ B) : GramWordSpace.Len B w' := fun v =>
  le_trans (le_glen w' v) (le_trans h.glen_le hB)

theorem extK_of_extAt {K : ℕ} {A : Set D.what₂.Tau} {w w' : GramWordSpace.GWord D} (h : GramWordSpace.ExtAt K A w w') : ExtK K w w' :=
  fun v => by
    obtain ⟨l, h1, _, h3⟩ := h v
    exact ⟨l, h1, h3⟩

theorem extension_of_word_pair {K j0 s : ℕ} {w : GramWordSpace.GWord D} {p : D.what₂.Tau → Option Bool}
    {q : GramWordSpace.GWord D × GramWordSpace.GWord D} (h : GramWordSpace.ChargedPairs K j0 s w p q) : ExtK K w q.1 ∧ ExtK K w q.2 := by
  unfold GramWordSpace.ChargedPairs at h
  split_ifs at h
  · refine ⟨fun v => ?_, fun v => ?_⟩
    · obtain ⟨l, h1, _, _, h4, _⟩ := h v
      exact ⟨l, h1, h4⟩
    · obtain ⟨l, h1, _, _, _, h5⟩ := h v
      exact ⟨GramWordSpace.dualL l, by simpa [GramWordSpace.dualL] using h1, h5⟩
  · refine ⟨fun v => ?_, fun v => ?_⟩
    · obtain ⟨l, h1, _, _, h4⟩ := h.1 v
      exact ⟨l, h1, h4⟩
    · obtain ⟨l, h1, _, _, h4⟩ := h.2 v
      exact ⟨l, h1, h4⟩

theorem empty_word_length_zero : glen (w00 : GramWordSpace.GWord D) = 0 := by
  refine Nat.le_zero.1 (Formalism.MainNotions.BlockEstimateWords.glen_le fun v => ?_)
  simp [w00]

theorem admissible_empty_word {k0 : ℕ} (X : GramWordSpace.Dat D k0) (Ks : ℕ) : WOK X Ks w00 := by
  refine ⟨fun v => ⟨fun l hl => ?_, ?_⟩, fun v => ?_⟩
  · simp [w00] at hl
  · simp [w00]
  · simp [w00]

end Words

theorem exists_many {E : Type} [Field E] [CharZero E] (A : AddSubgroup E) {l0 : E} (h0 : l0 ∈ A) (hne : l0 ≠ 0) (n : ℕ) :
    ∃ Ls : Finset E, (∀ l ∈ Ls, l ∈ A ∧ l ≠ 0) ∧ Ls.card = n := by
  have hinj : Function.Injective (fun k : ℕ => (k + 1) • l0) := by
    intro x y hxy
    simp only [nsmul_eq_mul] at hxy
    have := mul_right_cancel₀ hne hxy
    have h2 : ((x + 1 : ℕ) : E) = ((y + 1 : ℕ) : E) := this
    have h3 := Nat.cast_injective h2
    omega
  refine ⟨(Finset.range n).image (fun k : ℕ => (k + 1) • l0), fun l hl => ?_, ?_⟩
  · obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hl
    refine ⟨A.nsmul_mem h0 _, ?_⟩
    rw [nsmul_eq_mul]
    exact mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero k) hne
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_range]

end Formalism.MainNotions.BlockEstimateWords

end

end PartR0

section PartR0b

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Prob

variable {D : D7}

theorem isProb_of (S : Finset (GramWordSpace.GWord D)) (θ : GramWordSpace.GWord D →₀ ℝ) (hθ : GramWordSpace.IsProb θ) (hsub : θ.support ⊆ S) (B : ℕ)
    (hB : ∀ w' ∈ θ.support, glen w' ≤ B) : TA.IsProb (fun w : S => glen w.1) B (fun w : S => θ w.1) :=
  ⟨fun w => hθ.1 w.1, by rw [← fsum_one_coe S θ hsub]; exact hθ.2,
    fun w hw => hB w.1 (Finsupp.mem_support_iff.2 hw)⟩

theorem card_pat : (Fintype.card (D.what₂.Tau → Option Bool) : ℝ) = (3 : ℝ) ^ D.R.f := by
  rw [Fintype.card_fun, D.what₂.card_Tau]
  simp

theorem isProb2_of (S : Finset (GramWordSpace.GWord D))
    (θ : (D.what₂.Tau → Option Bool) → (GramWordSpace.GWord D × GramWordSpace.GWord D →₀ ℝ)) (hθ : ∀ p, GramWordSpace.IsProb (θ p))
    (hsub : ∀ p, ∀ q ∈ (θ p).support, q.1 ∈ S ∧ q.2 ∈ S) (B : ℕ)
    (hB : ∀ p, ∀ q ∈ (θ p).support, glen q.1 ≤ B ∧ glen q.2 ≤ B) :
    TA.IsProb2 (fun w : S => glen w.1) B
      (fun y : S × S => ((3 : ℝ) ^ D.R.f)⁻¹ * ∑ p, θ p (y.2.1, y.1.1)) := by
  refine ⟨fun y => mul_nonneg (inv_nonneg.2 (by positivity)) (Finset.sum_nonneg fun p _ => (hθ p).1 _), ?_, ?_⟩
  · rw [← Finset.mul_sum, Finset.sum_comm]
    have h1 : ∀ p, ∑ y : S × S, θ p (y.2.1, y.1.1) = 1 := by
      intro p
      have h2 := fsum_pair_coe S (θ p) (hsub p) (fun _ => 1)
      simp only [mul_one] at h2
      rw [← h2]
      exact (hθ p).2
    rw [Finset.sum_congr rfl fun p _ => h1 p]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [card_pat]
    exact inv_mul_cancel₀ (by positivity)
  · intro y hy
    have h1 : ∑ p, θ p (y.2.1, y.1.1) ≠ 0 := fun h => hy (by show ((3 : ℝ) ^ D.R.f)⁻¹ * _ = 0; rw [h, mul_zero])
    obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    have h2 := hB p (y.2.1, y.1.1) (Finsupp.mem_support_iff.2 hp)
    exact ⟨h2.2, h2.1⟩

theorem mean_sum {P Y : Type} [Fintype P] [Fintype Y] (c A : ℝ) (hc : c ≠ 0) (θ : P → Y → ℝ) (g : Y → ℝ) :
    A * ∑ p, ∑ y, θ p y * g y = (c * A) * ∑ y, (c⁻¹ * ∑ p, θ p y) * g y := by
  rw [Finset.sum_comm]
  have h : ∀ y, (c⁻¹ * ∑ p, θ p y) * g y = c⁻¹ * ∑ p, θ p y * g y := by
    intro y
    rw [mul_assoc, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun y _ => h y, ← Finset.mul_sum]
  field_simp

end Prob

section WordSet

variable {D : D7} {k0 : ℕ} (X : GramWordSpace.Dat D k0) (Ks : ℕ)

theorem exists_wordset (θ72 : ℕ → GramWordSpace.GWord D → Set D.what₂.Tau → (GramWordSpace.GWord D →₀ ℝ))
    (θ73 : ℕ → ℕ → GramWordSpace.GWord D → (D.what₂.Tau → Option Bool) → (GramWordSpace.GWord D × GramWordSpace.GWord D →₀ ℝ))
    (θ74 : ℕ → ℕ → GramWordSpace.GWord D → (GramWordSpace.GWord D →₀ ℝ))
    (h72 : ∀ i w, 1 ≤ i → i ≤ D.R.rS + 1 → WOK X Ks w → glen w + Ks ≤ GramWordSpace.NN D Ks →
      ∀ A, ∀ w' ∈ (θ72 i w A).support, ExtK Ks w w' ∧ X.admitted w')
    (h73 : ∀ i s w, 1 ≤ s → s ≤ i → i ≤ D.R.rS + 1 → ¬ (i = D.R.rS + 1 ∧ s = 1) → WOK X Ks w →
      glen w + Ks ≤ GramWordSpace.NN D Ks → ∀ p, ∀ q ∈ (θ73 i s w p).support,
        (ExtK Ks w q.1 ∧ X.admitted q.1) ∧ (ExtK Ks w q.2 ∧ X.admitted q.2))
    (h74 : ∀ i s w, 2 ≤ s → s ≤ i → i ≤ D.R.rS + 1 → WOK X Ks w → glen w + (s + 1) * Ks ≤ GramWordSpace.NN D Ks →
      ∀ w' ∈ (θ74 i s w).support, ExtK ((s + 1) * Ks) w w' ∧ X.admitted w') :
    ∃ S : Finset (GramWordSpace.GWord D), w00 ∈ S ∧ (∀ w ∈ S, WOK X Ks w) ∧
      (∀ w ∈ S, ∀ i, 1 ≤ i → i ≤ D.R.rS + 1 → glen w + Ks ≤ GramWordSpace.NN D Ks → ∀ A, (θ72 i w A).support ⊆ S) ∧
      (∀ w ∈ S, ∀ i s, 1 ≤ s → s ≤ i → i ≤ D.R.rS + 1 → ¬ (i = D.R.rS + 1 ∧ s = 1) →
        glen w + Ks ≤ GramWordSpace.NN D Ks → ∀ p, ∀ q ∈ (θ73 i s w p).support, q.1 ∈ S ∧ q.2 ∈ S) ∧
      (∀ w ∈ S, ∀ i s, 2 ≤ s → s ≤ i → i ≤ D.R.rS + 1 → glen w + (s + 1) * Ks ≤ GramWordSpace.NN D Ks →
        (θ74 i s w).support ⊆ S) := by
  let Good : GramWordSpace.GWord D → GramWordSpace.GWord D → Prop := fun w w' =>
    ∃ K, ExtK K w w' ∧ glen w + K ≤ GramWordSpace.NN D Ks ∧ X.admitted w'
  let U : GramWordSpace.GWord D → Finset (GramWordSpace.GWord D) := fun w =>
    (Finset.range (D.R.rS + 2)).biUnion fun i =>
      ((Finset.univ : Finset (Set D.what₂.Tau)).biUnion fun A => (θ72 i w A).support) ∪
      (Finset.range (D.R.rS + 2)).biUnion fun s =>
        ((Finset.univ : Finset (D.what₂.Tau → Option Bool)).biUnion fun p =>
          (θ73 i s w p).support.image Prod.fst ∪ (θ73 i s w p).support.image Prod.snd) ∪ (θ74 i s w).support
  have m72 : ∀ w i A w', i ≤ D.R.rS + 1 → w' ∈ (θ72 i w A).support → w' ∈ U w := fun w i A w' hi h =>
    Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 (by omega),
      Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨A, Finset.mem_univ _, h⟩)⟩
  have m73a : ∀ w i s p q, i ≤ D.R.rS + 1 → s ≤ D.R.rS + 1 → q ∈ (θ73 i s w p).support → q.1 ∈ U w :=
    fun w i s p q hi hs h =>
    Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 (by omega),
      Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨s, Finset.mem_range.2 (by omega),
        Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨p, Finset.mem_univ _,
          Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst h)⟩)⟩)⟩
  have m73b : ∀ w i s p q, i ≤ D.R.rS + 1 → s ≤ D.R.rS + 1 → q ∈ (θ73 i s w p).support → q.2 ∈ U w :=
    fun w i s p q hi hs h =>
    Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 (by omega),
      Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨s, Finset.mem_range.2 (by omega),
        Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨p, Finset.mem_univ _,
          Finset.mem_union_right _ (Finset.mem_image_of_mem Prod.snd h)⟩)⟩)⟩
  have m74 : ∀ w i s w', i ≤ D.R.rS + 1 → s ≤ D.R.rS + 1 → w' ∈ (θ74 i s w).support → w' ∈ U w :=
    fun w i s w' hi hs h =>
    Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 (by omega),
      Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨s, Finset.mem_range.2 (by omega),
        Finset.mem_union_right _ h⟩)⟩
  obtain ⟨S, hS0, hSP, hSc⟩ := exists_closed (fun w => (U w).filter (Good w)) gtot
    (Fintype.card D.what₂.Tau * GramWordSpace.NN D Ks) (WOK X Ks)
    (fun w w' hw' => by
      obtain ⟨K, hK, _, _⟩ := (Finset.mem_filter.1 hw').2
      exact hK.grow)
    (fun w w' hw' => by
      obtain ⟨K, hK, hB, _⟩ := (Finset.mem_filter.1 hw').2
      exact gtot_le (hK.len hB))
    (fun w _ w' hw' => by
      obtain ⟨K, hK, hB, hA⟩ := (Finset.mem_filter.1 hw').2
      exact ⟨hA, hK.len hB⟩)
    w00 (admissible_empty_word X Ks)
  refine ⟨S, hS0, hSP, ?_, ?_, ?_⟩
  · intro w hw i hi1 hi2 hb A w' hw'
    obtain ⟨e1, e2⟩ := h72 i w hi1 hi2 (hSP w hw) hb A w' hw'
    exact hSc w hw (Finset.mem_filter.2 ⟨m72 w i A w' hi2 hw', Ks, e1, hb, e2⟩)
  · intro w hw i s hs1 hs2 hi2 hns hb p q hq
    obtain ⟨⟨e1, e2⟩, ⟨e3, e4⟩⟩ := h73 i s w hs1 hs2 hi2 hns (hSP w hw) hb p q hq
    exact ⟨hSc w hw (Finset.mem_filter.2 ⟨m73a w i s p q hi2 (by omega) hq, Ks, e1, hb, e2⟩),
      hSc w hw (Finset.mem_filter.2 ⟨m73b w i s p q hi2 (by omega) hq, Ks, e3, hb, e4⟩)⟩
  · intro w hw i s hs1 hs2 hi2 hb w' hw'
    obtain ⟨e1, e2⟩ := h74 i s w hs1 hs2 hi2 (hSP w hw) hb w' hw'
    exact hSc w hw (Finset.mem_filter.2 ⟨m74 w i s w' hi2 (by omega) hw', (s + 1) * Ks, e1, hb, e2⟩)

end WordSet

end Formalism.MainNotions.BlockEstimateWords

end

end PartR0b

section PartR1

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

theorem lift_point_value {D : D7} {a : ℕ → ℕ → D.what₂.Tau → ℂ} (ha : ∀ i s v, a i s v ≠ 0) {j : ℕ} {p : TA.Pt D.host.E}
    (h : TA.IsPt j p) (v : D.what₂.Tau) : (lpt a ha j p v).1 = lbF a v 0 p := by
  have e : lpt a ha j p v = ⟨lbF a v 0 p, (lbF_ok a ha v p 0 h.2).1, by rw [(lbF_ok a ha v p 0 h.2).2]; exact h.1⟩ := by
    unfold lpt; exact dif_pos h
  rw [e]

theorem levelEst_of_model {D : D7} {k0 : ℕ} {G : GramWordSpace.GramMap k0 D.R.rS} {X : GramWordSpace.Dat D k0}
    {a : ℕ → ℕ → D.what₂.Tau → ℂ} {cb : ℕ → ℕ → ℝ} {c0 : ℝ} {χ : ℝ → ℝ} {Ks : ℕ}
    {E₀ Eg E₁ E₂ E₃ C C4 T T' : ℝ} {δ : D.host.E} {x : D.what₂.Tau → LocalDataRealPlace D} {L : LatticeDataWithDual D} {κL : ℕ → ℕ → ℝ}
    (hM : Mod D X a cb c0 Ks E₀ Eg E₁ E₂ E₃ C C4 T T' δ x L κL) (hLat : LatAx D δ L) (hχ : IsCutoff χ) (hP : PoissonPi D)
    (h72 : GramWordSpace.SingleLevelGramEstimate D G Ks E₀ Eg E₁ E₂) (h73 : GramWordSpace.BlockLiftEstimate D G Ks E₀ Eg E₁ E₂) (h74 : GramWordSpace.LargeBlockLiftEstimate D G Ks E₀ Eg E₁ E₂ E₃)
    (hE : GramWordSpace.E D k0 Ks E₀ Eg) (hTop : GramWordSpace.TopPos D G Ks E₀ Eg) (hLow : GramWordSpace.LowPos D k0 Ks E₀ Eg) (Kd : KernelData D)
    (hcut : ∀ v (γ : Point ℂ (D.R.rS + 1)), ∀ᶠ eps in 𝓝[>] (0 : ℝ),
      G.V (X.B v) (X.Fv χ eps v) γ.1 = G.V (X.B v) (X.f v) γ.1) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (Wv : TA.Pt D.host.E → H), (∀ p p', ⟪Wv p, Wv p'⟫_ℂ = GkLim G X a cb c0 p' p) ∧
      ∃ (Wd : Type) (_ : Fintype Wd) (len : Wd → ℕ) (Φ : ℝ → Wd → TA.Pt D.host.E → H)
        (tr : ℝ → ℕ → Wd → Finset (TA.Pt D.host.E) → (TA.Pt D.host.E → TA.Pt D.host.E → ℂ) → D.host.E → ℂ) (w0 : Wd),
        (∀ eps : ℝ, 0 < eps → ∀ i ∈ Icc 1 (D.R.rS + 1),
          TA.LevelEst len Ks (taData D L Kd (taLv D δ L)) (Φ eps) (tr eps i) (pat1S X a δ E₁ E₂ Ks i)
            (fun _ _ _ => ()) (prof1 D C C (Nlet D Ks) T T' δ x Ks i)
            (fun s l => (3 : ℝ) ^ D.R.f * prof3 D C C (Nlet D Ks) T T' δ x Ks i s l)
            (bdB D C C (Nlet D Ks) T T' δ x L C4 i) i) ∧
        (∀ w, len w ≤ 4 * Ks * (D.R.rS + 1) → Tendsto (fun eps => ‖Φ eps w []‖ ^ 2) (𝓝[>] 0) (𝓝 (c0 * X.jn2.re))) ∧
        len w0 = 0 ∧
        ∀ p, TA.IsPt (D.R.rS + 1) p → ∀ᶠ eps in 𝓝[>] (0 : ℝ), Φ eps w0 p = Wv p := by
  obtain ⟨H, i1, i2, i3, Φ, Wv, hΦ, hW, hcutΦ⟩ :=
    exists_vectors G X a cb c0 χ hM.a_ne Ks E₀ Eg hM.std hM.lowerConstantNonneg hχ hTop hLow
  refine ⟨H, i1, i2, i3, Wv, hW, ?_⟩
  have p72 := fun (i : ℕ) (w : GramWordSpace.GWord D) (h1 : 1 ≤ i) (h2 : i ≤ D.R.rS + 1) (h3 : WOK X Ks w)
    (h4 : glen w + Ks ≤ GramWordSpace.NN D Ks) => word_extension_prob_single hM hχ h72 hΦ h1 h2 h3 h4
  choose! θ72 hθ72a hθ72b using p72
  have p73 := fun (i s : ℕ) (w : GramWordSpace.GWord D) (h1 : 1 ≤ s) (h2 : s ≤ i) (h3 : i ≤ D.R.rS + 1)
    (h4 : ¬ (i = D.R.rS + 1 ∧ s = 1)) (h5 : WOK X Ks w) (h6 : glen w + Ks ≤ GramWordSpace.NN D Ks) =>
    word_pair_extension_prob hM hχ h73 hΦ h1 h2 h3 h4 h5 h6
  choose! θ73 hθ73a hθ73b using p73
  have p74 := fun (i s : ℕ) (w : GramWordSpace.GWord D) (h1 : 2 ≤ s) (h2 : s ≤ i) (h3 : i ≤ D.R.rS + 1) (h5 : WOK X Ks w)
    (h6 : glen w + (s + 1) * Ks ≤ GramWordSpace.NN D Ks) => block_word_extension_prob hM hχ h74 hΦ h1 h2 h3 h5 h6
  choose! θ74 hθ74a hθ74b hθ74c using p74
  obtain ⟨S, hS0, hSP, hS72, hS73, hS74⟩ := exists_wordset X Ks θ72 θ73 θ74
    (fun i w h1 h2 h3 h4 A w' hw' =>
      ⟨extK_of_extAt ((hθ72a i w h1 h2 h3 h4 A).2 w' hw').1, ((hθ72a i w h1 h2 h3 h4 A).2 w' hw').2⟩)
    (fun i s w h1 h2 h3 h4 h5 h6 p q hq =>
      ⟨⟨(extension_of_word_pair ((hθ73a i s w h1 h2 h3 h4 h5 h6 p).2 q hq).1).1, ((hθ73a i s w h1 h2 h3 h4 h5 h6 p).2 q hq).2.1⟩,
        ⟨(extension_of_word_pair ((hθ73a i s w h1 h2 h3 h4 h5 h6 p).2 q hq).1).2, ((hθ73a i s w h1 h2 h3 h4 h5 h6 p).2 q hq).2.2⟩⟩)
    (fun i s w h1 h2 h3 h5 h6 w' hw' =>
      ⟨extK_of_extAt ((hθ74b i s w h1 h2 h3 h5 h6) w' hw').1, ((hθ74b i s w h1 h2 h3 h5 h6) w' hw').2⟩)
  refine ⟨S, inferInstance, fun w => glen w.1, fun eps w => Φ eps w.1,
    fun eps i w Hd kap l => if glen w.1 + Ks ≤ GramWordSpace.NN D Ks then trS G X a cb c0 χ hM.a_ne δ eps i w.1 Hd kap l else 1,
    ⟨w00, hS0⟩, ?_, ?_, empty_word_length_zero, ?_⟩
  · intro eps he i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
    unfold TA.LevelEst
    refine ⟨?_, ?_, ?_, ?_⟩
    ·
      intro w Hd kap hHd hk t0 Ts hT B hB
      by_cases hb : glen w.1 + Ks ≤ GramWordSpace.NN D Ks
      · simp only [if_pos hb] at hB ⊢
        refine prePoisson hM hχ hP h72 hTop hLow hΦ hi1 hi2 (hSP w.1 w.2) hb he Hd kap hHd hk t0 Ts ?_ B hB
        intro t ht
        have h1 := hT t ht
        have e : (taData D L Kd (taLv D δ L)).La i 1 = (L.La i 1).toAddSubgroup := by
          show (L.La (i - 1 + 1) 1).toAddSubgroup = _
          rw [Nat.sub_add_cancel hi1]
        rw [e] at h1
        exact h1
      · exfalso
        simp only [if_neg hb] at hB
        obtain ⟨l0, hl0, hne⟩ := ta_dual_ne D δ hM.δ_ne (L.La i 1) ((hLat.2 i 1 ⟨hi1, le_rfl, by omega⟩).2.1.1)
        have hl0' : l0 ∈ taLv D δ L i := hl0
        obtain ⟨n, hn⟩ := exists_nat_gt B
        obtain ⟨Ls, hLs, hcard⟩ := exists_many (taLv D δ L i) hl0' hne n
        have h1 := hB Ls hLs
        simp only [norm_one, Finset.sum_const, hcard, nsmul_eq_mul, mul_one] at h1
        linarith
    ·
      intro w hlen
      have hb : glen w.1 + Ks ≤ GramWordSpace.NN D Ks := hlen
      have hA := hθ72a i w.1 hi1 hi2 (hSP w.1 w.2) hb
      have hBd := hθ72b i w.1 hi1 hi2 (hSP w.1 w.2) hb eps he
      refine ⟨fun A w' => θ72 i w.1 A w'.1, fun A => isProb_of S _ (hA A).1 (hS72 w.1 w.2 i hi1 hi2 hb A) _
        (fun w' hw' => (extK_of_extAt ((hA A).2 w' hw').1).glen_le), ?_⟩
      intro Hd kap hHd hk
      obtain ⟨e0, e1⟩ := hBd Hd kap hHd hk
      simp only [if_pos hb]
      refine ⟨e0, fun l hl hl0 => ?_⟩
      have h1 := e1 l hl hl0
      rw [fsum_coe S _ (hS72 w.1 w.2 i hi1 hi2 hb _)] at h1
      exact h1
    ·
      intro s hs hns w hlen
      obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.1 hs
      have hns' : ¬ (i = D.R.rS + 1 ∧ s = 1) := hns
      have hb : glen w.1 + Ks ≤ GramWordSpace.NN D Ks := hlen
      have hA := hθ73a i s w.1 hs1 hs2 hi2 hns' (hSP _ w.2) hb
      have hBd := hθ73b i s w.1 hs1 hs2 hi2 hns' (hSP _ w.2) hb eps he
      have hsub := hS73 w.1 w.2 i s hs1 hs2 hi2 hns' hb
      refine ⟨fun _ y => ((3 : ℝ) ^ D.R.f)⁻¹ * ∑ p, θ73 i s w.1 p (y.2.1, y.1.1),
        fun _ => isProb2_of S _ (fun p => (hA p).1) hsub _ (fun p q hq =>
          ⟨(extension_of_word_pair ((hA p).2 q hq).1).1.glen_le, (extension_of_word_pair ((hA p).2 q hq).1).2.glen_le⟩), ?_⟩
      intro Hd kp Ts hHd hTs hk t ht t' ht' htt
      have h0 := hBd Hd kp Ts hHd hTs hk t ht t' ht' htt
      refine le_of_le_of_eq h0 ?_
      rw [Finset.sum_congr rfl fun p _ => fsum_pair_coe S (θ73 i s w.1 p) (hsub p) _]
      exact mean_sum _ _ (by positivity) _ _
    ·
      intro s hs w hlen
      obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.1 hs
      have hb : glen w.1 + (s + 1) * Ks ≤ GramWordSpace.NN D Ks := hlen
      have hw := hSP w.1 w.2
      have hsub := hS74 w.1 w.2 i s hs1 hs2 hi2 hb
      refine ⟨fun w' => θ74 i s w.1 w'.1, isProb_of S _ (hθ74a i s w.1 hs1 hs2 hi2 hw hb) hsub _
        (fun w' hw' => (extK_of_extAt ((hθ74b i s w.1 hs1 hs2 hi2 hw hb) w' hw').1).glen_le), ?_⟩
      intro Hd kap hHd hk t0 Ts hT
      have h0 := hθ74c i s w.1 hs1 hs2 hi2 hw hb eps he Hd kap hHd hk t0 Ts hT
      rw [fsum_coe S _ hsub] at h0
      exact h0
  · intro w _
    exact energy_tendsto G X a cb c0 χ hM.a_ne Ks E₀ Eg hM.std hχ hE hM.brk_pos hΦ (hSP w.1 w.2)
  · intro p hp
    have h := Filter.eventually_all.2 (fun v => hcut v (lpt a hM.a_ne (D.R.rS + 1) p v))
    refine h.mono fun eps he => hcutΦ eps p hp fun v => ?_
    have e := he v
    rw [lift_point_value hM.a_ne hp v] at e
    exact e

end Formalism.MainNotions.BlockEstimateWords

end

end PartR1

section PartU

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

theorem levelSizes_unit {E : Type} [Field E] (Dt : TA.Data E) (Pat3 : Type) [Fintype Pat3] (c1 : E → ℝ) (c3 : ℕ → E → ℝ)
    (ep1 : ℝ) (ep3 bd4 : ℕ → ℝ) (ep a : ℝ) (i : ℕ) (h : TA.LevelSizes Dt Pat3 c1 c3 ep1 ep3 bd4 ep a i) :
    TA.LevelSizes Dt Unit c1 (fun s l => (Fintype.card Pat3 : ℝ) * c3 s l) ep1
      (fun s => (Fintype.card Pat3 : ℝ) * ep3 s) bd4 ep a i := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hc : (0 : ℝ) ≤ (Fintype.card Pat3 : ℝ) := Nat.cast_nonneg _
  refine ⟨h1, fun s hs hn => ⟨fun x => mul_nonneg hc ((h2 s hs hn).1 x), fun S hS => ?_⟩, mul_nonneg hc h3, ?_,
    fun s hs => ⟨(h5 s hs).1, ?_⟩⟩
  · rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left ((h2 s hs hn).2 S hS) hc
  · simpa [Fintype.card_unit] using h4
  · simpa [Fintype.card_unit] using (h5 s hs).2

theorem card3 (D : D7) (inst : Fintype (D.what₂.Tau → Option Bool)) :
    ((@Fintype.card _ inst : ℕ) : ℝ) = (3 : ℝ) ^ D.R.f := by
  have h : @Fintype.card _ inst = 3 ^ D.R.f := by
    have h2 : Fintype.card (Option Bool) = 3 := by simp
    rw [Subsingleton.elim inst Pi.instFintype, Fintype.card_fun, D.what₂.card_Tau, h2]
  rw [h]; push_cast; ring

theorem rowSums_of_levelEstU (K : ℕ) (hK : 4 ≤ K) (C4 : ℝ) (hC4 : 1 ≤ C4) :
    ∃ C0 C' C : ℝ, 1 ≤ C0 ∧
    ∀ (D : D7) (C1 C2 N T T' : ℝ) (δ : D.host.E) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) (Kd : KernelData D)
      (Lv : ℕ → AddSubgroup D.host.E), ArithAxF D L Kd → SzOK D C1 C2 N T T' δ x L Lv →
      C' ≤ ThS D C1 C2 N T T' δ x L → (D.R.rS : ℝ) * (C0 / ThS D C1 C2 N T T' δ x L) ^ D.R.f ≤ 1 →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Wd : Type) [Fintype Wd] (len : Wd → ℕ)
        (Pat1 : Type) (pat1 : ℕ → D.host.E → Pat1)
        (Φ : ℝ → Wd → TA.Pt D.host.E → H)
        (tr : ℝ → ℕ → Wd → Finset (TA.Pt D.host.E) → (TA.Pt D.host.E → TA.Pt D.host.E → ℂ) → D.host.E → ℂ)
        (w0 : Wd) (jn : ℝ) (ι : Type) (c : ι → Point D.host.E (D.R.rS + 1) → ℂ) (Wv : Point D.host.E (D.R.rS + 1) → H),
        (∀ eps : ℝ, 0 < eps → ∀ i ∈ Icc 1 (D.R.rS + 1),
          TA.LevelEst len K (taData D L Kd Lv) (Φ eps) (tr eps i) (pat1 i) (fun _ _ _ => ()) (prof1 D C1 C2 N T T' δ x K i)
            (fun s l => (3 : ℝ) ^ D.R.f * prof3 D C1 C2 N T T' δ x K i s l) (bdB D C1 C2 N T T' δ x L C4 i) i) →
        (∀ w, len w ≤ 4 * K * (D.R.rS + 1) → Tendsto (fun eps => ‖Φ eps w []‖ ^ 2) (𝓝[>] 0) (𝓝 jn)) →
        len w0 = 0 →
        (∀ p, TA.IsPt (D.R.rS + 1) p → ∀ᶠ eps in 𝓝[>] (0 : ℝ), Φ eps w0 p = Wv (ph (D.R.rS + 1) p)) →
        (∀ R : Finset ι, KLE (fun p p' => ∑ ρ ∈ R, c ρ p * star (c ρ p')) (Kd.K (D.R.rS + 1))) →
        (∀ ρ, Summable fun h => ‖c ρ h‖ * ‖Wv h‖) →
        ∀ R : Finset ι, ∑ ρ ∈ R, ‖∑' h, c ρ h • Wv h‖ ^ 2 ≤
          (1 + C * ((D.R.rS : ℝ) + 1) * (C0 / ThS D C1 C2 N T T' δ x L) ^ D.R.f) *
            (∏ i ∈ Icc 1 (D.R.rS + 1), (1 + Kd.e i)) * jn := by
  obtain ⟨C0, hC01, hSz⟩ := levelSizes_of_ThS K hK C4 hC4
  obtain ⟨C', C, hTA⟩ := ta_reductionAfter C0 hC01
  refine ⟨C0, max C' (max C0 5), C, hC01, ?_⟩
  intro D C1 C2 N T T' δ x L Kd Lv hAx hOK hΘ hr H _ _ _ Wd _ len Pat1 pat1 Φ tr w0 jn ι c Wv hEst hE hw0 hcut hrow hsum R
  have hΘ1 : C' ≤ ThS D C1 C2 N T T' δ x L := le_trans (le_max_left _ _) hΘ
  have hΘ2 : C0 ≤ ThS D C1 C2 N T T' δ x L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hΘ
  have hΘ3 : 4 < ThS D C1 C2 N T T' δ x L :=
    lt_of_lt_of_le (by norm_num) (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hΘ)
  obtain ⟨ep1, ep3, hLS0⟩ := hSz D C1 C2 N T T' δ x L (taKer0 D Kd.e) Lv (ta_arith0 D L Kd.e hAx.2.2.1) hOK hΘ2 hΘ3
  have hLS : ∀ i ∈ Icc 1 (D.R.rS + 1),
      TA.LevelSizes (taData D L Kd Lv) (D.what₂.Tau → Option Bool) (prof1 D C1 C2 N T T' δ x K i)
        (prof3 D C1 C2 N T T' δ x K i) ep1 (fun _ => ep3) (bdB D C1 C2 N T T' δ x L C4 i)
        ((C0 * ThS D C1 C2 N T T' δ x L ^ (-((K : ℝ) - 5 / 2))) ^ D.R.f)
        ((C0 / ThS D C1 C2 N T T' δ x L) ^ D.R.f) i := fun i hi => hLS0 i hi
  have hLSU : ∀ i ∈ Icc 1 (D.R.rS + 1),
      TA.LevelSizes (taData D L Kd Lv) Unit (prof1 D C1 C2 N T T' δ x K i)
        (fun s l => (3 : ℝ) ^ D.R.f * prof3 D C1 C2 N T T' δ x K i s l) ep1 (fun _ => (3 : ℝ) ^ D.R.f * ep3)
        (bdB D C1 C2 N T T' δ x L C4 i)
        ((C0 * ThS D C1 C2 N T T' δ x L ^ (-((K : ℝ) - 5 / 2))) ^ D.R.f)
        ((C0 / ThS D C1 C2 N T T' δ x L) ^ D.R.f) i := fun i hi => by
    have h := levelSizes_unit _ _ _ _ _ _ _ _ _ _ (hLS i hi)
    rw [card3 D] at h
    exact h
  have key := hTA D.host.E H Wd len K D.R.f (ThS D C1 C2 N T T' δ x L) (taData D L Kd Lv) Pat1 Unit
    pat1 (fun _ _ _ _ => ()) (prof1 D C1 C2 N T T' δ x K)
    (fun i s l => (3 : ℝ) ^ D.R.f * prof3 D C1 C2 N T T' δ x K i s l) (fun _ => ep1) (fun _ _ => (3 : ℝ) ^ D.R.f * ep3)
    (bdB D C1 C2 N T T' δ x L C4) Φ tr w0 (fun p => Wv (ph (D.R.rS + 1) p)) jn ι (fun ρ p => c ρ (ph (D.R.rS + 1) p))
    hK (f_pos D) hΘ1 hr (axK_of_ArithAxF Lv hAx) (arithmetic_axiom_of_family Lv hAx) (domAfterA_of_ArithAxF Lv hAx) (axE_of_ArithAxF Lv hAx)
    hLSU hEst hE hw0 hcut (fun P R hP => rows_of_KLE Lv c hrow P R hP)
    (fun ρ => ((ptEquiv (E := D.host.E) (D.R.rS + 1)).summable_iff (f := fun h => ‖c ρ h‖ * ‖Wv h‖)).2 (hsum ρ)) R
  refine le_of_eq_of_le ?_ key
  refine Finset.sum_congr rfl fun ρ _ => ?_
  congr 2
  exact ((ptEquiv (E := D.host.E) (D.R.rS + 1)).tsum_eq (fun h => c ρ h • Wv h)).symm

theorem sRowForm_of_levelEstU (K : ℕ) (hK : 4 ≤ K) (C4 : ℝ) (hC4 : 1 ≤ C4) :
    ∃ C0 C' C : ℝ, 1 ≤ C0 ∧
    ∀ (D : D7) (C1 C2 N T T' : ℝ) (δ : D.host.E) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) (Kd : KernelData D)
      (Lv : ℕ → AddSubgroup D.host.E), ArithAxF D L Kd → SzOK D C1 C2 N T T' δ x L Lv →
      C' ≤ ThS D C1 C2 N T T' δ x L → (D.R.rS : ℝ) * (C0 / ThS D C1 C2 N T T' δ x L) ^ D.R.f ≤ 1 →
      ∀ (HSv : D.what₂.Tau → Type) (ip : ∀ v, HSv v → HSv v → ℂ), (∀ v, PSDK (ip v)) →
      ∀ (n : Point D.host.E (D.R.rS + 1) → ℝ) (ι : Type) (c : ι → Point D.host.E (D.R.rS + 1) → ℂ)
        (V : ∀ v, Point D.host.E (D.R.rS + 1) → HSv v), RowsAx HSv ip (Kd.K (D.R.rS + 1)) n c V →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Wv : Point D.host.E (D.R.rS + 1) → H),
        (∀ p q, ⟪Wv p, Wv q⟫_ℂ = ((Real.sqrt (n q) : ℝ) : ℂ) * ((Real.sqrt (n p) : ℝ) : ℂ) * ∏ v, ip v (V v q) (V v p)) →
      ∀ (Wd : Type) [Fintype Wd] (len : Wd → ℕ)
        (Pat1 : Type) (pat1 : ℕ → D.host.E → Pat1)
        (Φ : ℝ → Wd → TA.Pt D.host.E → H)
        (tr : ℝ → ℕ → Wd → Finset (TA.Pt D.host.E) → (TA.Pt D.host.E → TA.Pt D.host.E → ℂ) → D.host.E → ℂ)
        (w0 : Wd) (jn : ℝ),
        (∀ eps : ℝ, 0 < eps → ∀ i ∈ Icc 1 (D.R.rS + 1),
          TA.LevelEst len K (taData D L Kd Lv) (Φ eps) (tr eps i) (pat1 i) (fun _ _ _ => ()) (prof1 D C1 C2 N T T' δ x K i)
            (fun s l => (3 : ℝ) ^ D.R.f * prof3 D C1 C2 N T T' δ x K i s l) (bdB D C1 C2 N T T' δ x L C4 i) i) →
        (∀ w, len w ≤ 4 * K * (D.R.rS + 1) → Tendsto (fun eps => ‖Φ eps w []‖ ^ 2) (𝓝[>] 0) (𝓝 jn)) →
        len w0 = 0 →
        (∀ p, TA.IsPt (D.R.rS + 1) p → ∀ᶠ eps in 𝓝[>] (0 : ℝ), Φ eps w0 p = Wv (ph (D.R.rS + 1) p)) →
        SRowForm HSv ip n c V ≤ ENNReal.ofReal
          ((1 + C * ((D.R.rS : ℝ) + 1) * (C0 / ThS D C1 C2 N T T' δ x L) ^ D.R.f) *
            (∏ i ∈ Icc 1 (D.R.rS + 1), (1 + Kd.e i)) * jn) := by
  obtain ⟨C0, C', C, hC01, h⟩ := rowSums_of_levelEstU K hK C4 hC4
  refine ⟨C0, C', C, hC01, ?_⟩
  intro D C1 C2 N T T' δ x L Kd Lv hAx hOK hΘ hr HSv ip hip n ι c V hRows H _ _ _ Wv hW Wd _ len Pat1 pat1 Φ tr w0 jn
    hEst hE hw0 hcut
  refine sRowForm_le ip hip n c V Wv hW hRows.2 _ ?_
  refine h D C1 C2 N T T' δ x L Kd Lv hAx hOK hΘ hr H Wd len Pat1 pat1 Φ tr w0 jn ι c Wv hEst hE hw0 hcut hRows.1 ?_
  intro ρ
  refine (hRows.2 ρ).congr fun p => ?_
  rw [norm_places ip hip n V Wv hW p, mul_assoc]

end Formalism.MainNotions.BlockEstimateWords

end

end PartU

section PartPoPi

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Span

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem pp_norm_le_of_orth {d u : V} (h : ⟪d, u⟫_ℝ = 0) (c : ℝ) : ‖d‖ ≤ ‖d - c • u‖ := by
  have h1 : ‖d - c • u‖ ^ 2 = ‖d‖ ^ 2 + ‖c • u‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, h]; ring
  have h2 : ‖d‖ ^ 2 ≤ ‖d - c • u‖ ^ 2 := by rw [h1]; nlinarith [sq_nonneg ‖c • u‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

theorem pp_span_top (Λ : Submodule ℤ V) [DiscreteTopology Λ] [Countable Λ] (F : Set V)
    (hF : IsAddFundamentalDomain Λ F volume) (hfin : volume F ≠ ⊤) : Submodule.span ℝ (Λ : Set V) = ⊤ := by
  by_contra hne
  set W : Submodule ℝ V := Submodule.span ℝ (Λ : Set V) with hW
  have hWo : Wᗮ ≠ ⊥ := fun h => hne (Submodule.orthogonal_eq_bot_iff.1 h)
  obtain ⟨u0, hu0, hu0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWo

  obtain ⟨r, hr, hsep⟩ : ∃ r : ℝ, 0 < r ∧ ∀ l : Λ, ‖(l : V)‖ < r → l = 0 := by
    have ho : IsOpen ({0} : Set Λ) := isOpen_discrete _
    obtain ⟨e, he, hb⟩ := Metric.isOpen_iff.1 ho 0 rfl
    refine ⟨e, he, fun l hl => ?_⟩
    have : l ∈ Metric.ball (0 : Λ) e := by
      rw [Metric.mem_ball, dist_zero_right]; exact hl
    exact hb this
  set u : V := (r / ‖u0‖) • u0 with hu
  have hun : ‖u‖ = r := by
    rw [hu, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr (norm_pos_iff.2 hu0ne)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 hu0ne)]
  have huW : ∀ d ∈ W, ⟪d, u⟫_ℝ = 0 := fun d hd => by
    rw [hu, inner_smul_right, (Submodule.mem_orthogonal W u0).1 hu0 d hd, mul_zero]
  have hc : volume (Metric.ball (0 : V) (r / 2)) ≠ 0 := (Metric.measure_ball_pos volume 0 (by positivity)).ne'
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hc hfin
  set s : Set V := ⋃ n ∈ Finset.range N, Metric.ball ((n : ℝ) • u) (r / 2) with hs
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range N)) (fun n : ℕ => Metric.ball ((n : ℝ) • u) (r / 2)) := by
    intro n _ m _ hnm
    refine Metric.ball_disjoint_ball ?_
    rw [dist_eq_norm, ← sub_smul, norm_smul, hun, Real.norm_eq_abs]
    have h1 : (1 : ℝ) ≤ |(n : ℝ) - (m : ℝ)| := by
      have h2 : (n : ℤ) - (m : ℤ) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hnm)
      have h3 := Int.one_le_abs h2
      have h4 : ((1 : ℤ) : ℝ) ≤ ((|(n : ℤ) - (m : ℤ)| : ℤ) : ℝ) := by exact_mod_cast h3
      simpa using h4
    nlinarith
  have hvol : volume s = N * volume (Metric.ball (0 : V) (r / 2)) := by
    rw [hs, measure_biUnion_finset hdisj (fun _ _ => Metric.isOpen_ball.measurableSet)]
    simp [Measure.addHaar_ball_center]
  have hms : NullMeasurableSet s volume :=
    (Finset.measurableSet_biUnion _ fun _ _ => Metric.isOpen_ball.measurableSet).nullMeasurableSet
  have : MeasurableVAdd Λ V := (inferInstance : MeasurableVAdd Λ.toAddSubgroup V)
  have : VAddInvariantMeasure Λ V volume := (inferInstance : VAddInvariantMeasure Λ.toAddSubgroup V volume)
  obtain ⟨x, y, hxy, hnd⟩ := exists_pair_mem_lattice_not_disjoint_vadd hF hms (by rw [hvol]; exact hN)
  obtain ⟨z, ⟨p, hp, hpz⟩, q, hq, hqz⟩ := Set.not_disjoint_iff.1 hnd
  simp only [hs, Set.mem_iUnion, Metric.mem_ball, dist_eq_norm, exists_prop] at hp hq
  obtain ⟨n, -, hp⟩ := hp
  obtain ⟨m, -, hq⟩ := hq
  apply hxy
  have hz : (x : V) + p = (y : V) + q := by
    have e1 : (x : V) + p = z := hpz
    have e2 : (y : V) + q = z := hqz
    rw [e1, e2]
  have hd : ((x - y : Λ) : V) - ((m : ℝ) - (n : ℝ)) • u = (q - (m : ℝ) • u) - (p - (n : ℝ) • u) := by
    have : ((x - y : Λ) : V) = q - p := by
      rw [Submodule.coe_sub]
      exact sub_eq_sub_iff_add_eq_add.2 (by rw [hz, add_comm])
    rw [this, sub_smul]; abel
  have hmem : ((x - y : Λ) : V) ∈ W := Submodule.subset_span (x - y).2
  have h1 := pp_norm_le_of_orth (huW _ hmem) ((m : ℝ) - (n : ℝ))
  have h2 : ‖((x - y : Λ) : V) - ((m : ℝ) - (n : ℝ)) • u‖ < r := by
    rw [hd]
    calc _ ≤ ‖q - (m : ℝ) • u‖ + ‖p - (n : ℝ) • u‖ := norm_sub_le _ _
      _ < r := by linarith
  exact sub_eq_zero.1 (hsep _ (lt_of_le_of_lt h1 h2))

end Span

section Maps

open scoped FourierTransform

variable {ι : Type} [Fintype ι]

abbrev VV (ι : Type) [Fintype ι] := EuclideanSpace ℝ (ι ⊕ ι)

def piL (k : ι) : VV ι →ₗ[ℝ] ℂ where
  toFun y := ⟨y (Sum.inl k), y (Sum.inr k)⟩
  map_add' a b := by apply Complex.ext <;> simp
  map_smul' c a := by apply Complex.ext <;> simp

def piC (k : ι) : VV ι →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (piL k)

theorem piC_apply (k : ι) (y : VV ι) : piC k y = ⟨y (Sum.inl k), y (Sum.inr k)⟩ := rfl

def cplx (y : VV ι) : ι → ℂ := fun k => piC k y

theorem cplx_add (a b : VV ι) : cplx (a + b) = cplx a + cplx b := by funext k; exact map_add (piC k) a b

theorem cplx_zero : cplx (0 : VV ι) = 0 := by funext k; exact map_zero (piC k)

theorem cplx_zsmul (n : ℤ) (a : VV ι) : cplx (n • a) = n • cplx a := by funext k; exact map_zsmul (piC k) n a

theorem cplx_reals (t : ι → ℂ) : cplx (Gm.reals t) = t := by
  funext k
  simp only [cplx, piC_apply]
  apply Complex.ext <;> simp [Gm.reals]

theorem reals_cplx (y : VV ι) : Gm.reals (cplx y) = y := by
  ext k
  rcases k with k | k <;> simp [Gm.reals, cplx, piC_apply]

theorem continuous_cplx : Continuous (cplx : VV ι → ι → ℂ) := continuous_pi fun k => (piC k).continuous

def realsME : (ι → ℂ) ≃ᵐ VV ι where
  toEquiv := ⟨Gm.reals, cplx, cplx_reals, reals_cplx⟩
  measurable_toFun := Gm.mp_reals.measurable
  measurable_invFun := continuous_cplx.measurable

theorem mp_cplx : MeasurePreserving (cplx : VV ι → ι → ℂ) volume volume :=
  MeasurePreserving.symm realsME (show MeasurePreserving (realsME (ι := ι)) volume volume from Gm.mp_reals)

theorem me_reals : MeasurableEmbedding (Gm.reals : (ι → ℂ) → VV ι) := (realsME (ι := ι)).measurableEmbedding

def realsA : (ι → ℂ) →+ VV ι where
  toFun := Gm.reals
  map_zero' := by ext k; rcases k with k | k <;> simp [Gm.reals]
  map_add' a b := by ext k; rcases k with k | k <;> simp [Gm.reals]

theorem inner_reals (t m : ι → ℂ) :
    ⟪Gm.reals t, Gm.reals m⟫_ℝ = ∑ k, ((t k).re * (m k).re + (t k).im * (m k).im) := by
  rw [PiLp.inner_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Gm.reals, mul_comm]

def jmap (σ : ι → ℂ) : ι → ℂ := fun v => ⟨-(σ v).im / Real.pi, -(σ v).re / Real.pi⟩

def dmapA : (ι → ℂ) →+ VV ι where
  toFun σ := Gm.reals (jmap σ)
  map_zero' := by ext k; rcases k with k | k <;> simp [Gm.reals, jmap]
  map_add' a b := by
    ext k
    rcases k with k | k
    · simp only [Gm.reals, jmap, PiLp.add_apply, Sum.elim_inl, Pi.add_apply, Complex.add_im]; ring
    · simp only [Gm.reals, jmap, PiLp.add_apply, Sum.elim_inr, Pi.add_apply, Complex.add_re]; ring

theorem pp_char (σ t : ι → ℂ) :
    Complex.exp (((-2 * Real.pi * ⟪Gm.reals t, Gm.reals (jmap σ)⟫_ℝ : ℝ) : ℂ) * Complex.I) =
      ∏ v, TopsChoicePartA.fsC (σ v) (t v) := by
  have h : ∀ v, σ v * t v - star (σ v) * star (t v) = ((2 * (σ v * t v).im : ℝ) : ℂ) * Complex.I := fun v => by
    rw [← star_mul', Complex.star_def, Complex.sub_conj]
  have hpi := Real.pi_ne_zero
  have hAB : -2 * Real.pi * ⟪Gm.reals t, Gm.reals (jmap σ)⟫_ℝ = ∑ v, 2 * (σ v * t v).im := by
    rw [inner_reals, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [jmap, Complex.mul_im]
    field_simp
    ring
  simp only [TopsChoicePartA.fsC, h]
  rw [← Complex.exp_sum, ← Finset.sum_mul, ← Complex.ofReal_sum, hAB]

theorem pp_fourier (φ : (ι → ℂ) → ℝ) (σ : ι → ℂ) :
    (𝓕 (fun y : VV ι => ((φ (cplx y) : ℝ) : ℂ)) : VV ι → ℂ) (Gm.reals (jmap σ)) =
      ∫ t, ((φ t : ℝ) : ℂ) * ∏ v, TopsChoicePartA.fsC (σ v) (t v) := by
  have h := Gm.mp_reals.integral_comp (me_reals (ι := ι)) (fun y : VV ι =>
    Complex.exp (((-2 * Real.pi * ⟪y, Gm.reals (jmap σ)⟫_ℝ : ℝ) : ℂ) * Complex.I) • ((φ (cplx y) : ℝ) : ℂ))
  rw [Real.fourier_eq', ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [cplx_reals, pp_char, smul_eq_mul]
  ring

def LamV (La : AddSubgroup (ι → ℂ)) : Submodule ℤ (VV ι) where
  carrier := {y | cplx y ∈ La}
  add_mem' := by
    intro a b ha hb
    show cplx (a + b) ∈ La
    rw [cplx_add]; exact La.add_mem ha hb
  zero_mem' := by
    show cplx (0 : VV ι) ∈ La
    rw [cplx_zero]; exact La.zero_mem
  smul_mem' := by
    intro n y hy
    show cplx (n • y) ∈ La
    rw [cplx_zsmul]; exact La.zsmul_mem hy n

theorem reals_mem_LamV {La : AddSubgroup (ι → ℂ)} {t : ι → ℂ} (ht : t ∈ La) : Gm.reals t ∈ LamV La := by
  show cplx (Gm.reals t) ∈ La
  rw [cplx_reals]; exact ht

theorem cplx_injective : Function.Injective (cplx : VV ι → ι → ℂ) := fun a b h => by
  rw [← reals_cplx a, ← reals_cplx b, h]

theorem LamV_discrete (La : AddSubgroup (ι → ℂ)) [DiscreteTopology La] : DiscreteTopology (LamV La) :=
  DiscreteTopology.of_continuous_injective (β := La) (f := fun y : LamV La => (⟨cplx y.1, y.2⟩ : La))
    (Continuous.subtype_mk (continuous_cplx.comp continuous_subtype_val) _)
    (fun a b h => Subtype.ext (cplx_injective (congrArg Subtype.val h)))

theorem LamV_fund {La : AddSubgroup (ι → ℂ)} {U : Set (ι → ℂ)} (hU : IsAddFundamentalDomain La U volume) :
    IsAddFundamentalDomain (LamV La) (cplx ⁻¹' U) volume := by
  refine hU.preimage_of_equiv (f := cplx) mp_cplx.quasiMeasurePreserving
    (e := fun g : La => (⟨Gm.reals g.1, reals_mem_LamV g.2⟩ : LamV La)) ⟨?_, ?_⟩ ?_
  · intro a b h
    have h1 : Gm.reals a.1 = Gm.reals b.1 := congrArg Subtype.val h
    apply Subtype.ext
    rw [← cplx_reals a.1, ← cplx_reals b.1, h1]
  · intro y
    exact ⟨⟨cplx y.1, y.2⟩, Subtype.ext (reals_cplx y.1)⟩
  · intro g y
    show cplx (Gm.reals g.1 + y) = g.1 + cplx y
    rw [cplx_add, cplx_reals]

theorem pp_dual_mem (La : AddSubgroup (ι → ℂ)) (σ : ι → ℂ) (h : Gm.reals (jmap σ) ∈ Formalism.H.dual (LamV La)) :
    ∀ t ∈ La, ∏ v, TopsChoicePartA.fsC (σ v) (t v) = 1 := by
  intro t ht
  obtain ⟨n, hn⟩ := Submodule.mem_one.1 (h (Gm.reals t) (reals_mem_LamV ht))
  have hn2 : ⟪Gm.reals t, Gm.reals (jmap σ)⟫_ℝ = (n : ℝ) := by
    rw [real_inner_comm]
    simpa using hn.symm
  rw [← pp_char, hn2, Complex.exp_eq_one_iff]
  exact ⟨-n, by push_cast; ring⟩

theorem pp_dual_surj (μ : VV ι) : ∃ σ : ι → ℂ, Gm.reals (jmap σ) = μ := by
  refine ⟨fun v => ⟨-Real.pi * (cplx μ v).im, -Real.pi * (cplx μ v).re⟩, ?_⟩
  have hpi := Real.pi_ne_zero
  have : jmap (fun v => (⟨-Real.pi * (cplx μ v).im, -Real.pi * (cplx μ v).re⟩ : ℂ)) = cplx μ := by
    funext v
    apply Complex.ext
    · simp only [jmap]; field_simp
    · simp only [jmap]; field_simp
  rw [this, reals_cplx]

end Maps

section Main

open scoped FourierTransform

variable {ι : Type} [Fintype ι]

theorem poisson_gen (La : AddSubgroup (ι → ℂ)) (κ : ℝ) (hκ : 0 < κ) [DiscreteTopology La] (U : Set (ι → ℂ))
    (hU : IsAddFundamentalDomain La U volume) (hvol : volume U = ENNReal.ofReal κ)
    (φ : (ι → ℂ) → ℝ) (Cφ : ℝ) (hc : Continuous φ) (hdec : ∀ t, |φ t| ≤ Cφ * ∏ v, ((1 + ‖t v‖) ^ 3)⁻¹)
    (hpos : ∀ t, 0 ≤ φ t) (t₀ : ι → ℂ) (B : ℝ)
    (hB : ∀ S : Finset (ι → ℂ), (∀ σ ∈ S, (∀ t ∈ La, ∏ v, TopsChoicePartA.fsC (σ v) (t v) = 1) ∧ σ ≠ 0) →
      ∑ σ ∈ S, ‖∫ t, ((φ t : ℝ) : ℂ) * ∏ v, TopsChoicePartA.fsC (σ v) (t v)‖ ≤ B)
    (S : Finset (ι → ℂ)) (hS : ∀ z ∈ S, z ∈ La) :
    κ * ∑ z ∈ S, φ (t₀ + z) ≤ ‖∫ t, ((φ t : ℝ) : ℂ)‖ + B := by
  have : DiscreteTopology (LamV La) := LamV_discrete La
  have : Countable (LamV La) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hfd := LamV_fund hU
  have hvolV : volume (cplx ⁻¹' U : Set (VV ι)) = ENNReal.ofReal κ := by
    rw [mp_cplx.measure_preimage hU.nullMeasurableSet, hvol]
  have : IsZLattice ℝ (LamV La) := ⟨pp_span_top (LamV La) _ hfd (by rw [hvolV]; exact ENNReal.ofReal_ne_top)⟩
  have hcov : ZLattice.covolume (LamV La) = κ := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain (LamV La) volume hfd, measureReal_def, hvolV,
      ENNReal.toReal_ofReal hκ.le]
  set A : (ι → ℂ) → ℂ := fun σ => ∫ t, ((φ t : ℝ) : ℂ) * ∏ v, TopsChoicePartA.fsC (σ v) (t v) with hA
  have hnorm : ∀ σ, ‖((κ : ℝ) : ℂ)⁻¹ * A σ‖ = κ⁻¹ * ‖A σ‖ := fun σ => by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hκ.le]
  have key := Formalism.FourierDecayAlt.P.poisson_joint Formalism.FourierDecayAlt.P.poisson_summation_level_statement (VV ι) ι piC
    ⟨cplx_injective, fun t => ⟨Gm.reals t, cplx_reals t⟩⟩ (LamV La) (ι → ℂ) realsA dmapA La
    ((Formalism.H.dual (LamV La)).toAddSubgroup.comap dmapA) (fun y => φ (cplx y)) Cφ (fun σ => ((κ : ℝ) : ℂ)⁻¹ * A σ)
    (fun a b h => by
      have h1 : Gm.reals a = Gm.reals b := h
      rw [← cplx_reals a, ← cplx_reals b, h1])
    (fun t ht => reals_mem_LamV ht) (map_zero dmapA)
    (fun μ hμ => by
      obtain ⟨σ, hσ⟩ := pp_dual_surj μ
      refine ⟨σ, ?_, hσ⟩
      show Gm.reals (jmap σ) ∈ Formalism.H.dual (LamV La)
      rw [hσ]; exact hμ)
    (hc.comp continuous_cplx) (fun c => hdec (cplx c)) (fun c => hpos (cplx c))
    (fun l => by
      rw [hcov]
      show _ = _ * (𝓕 (fun y : VV ι => ((φ (cplx y) : ℝ) : ℂ)) : VV ι → ℂ) (Gm.reals (jmap l))
      rw [pp_fourier])
    t₀ (κ⁻¹ * B)
    (fun Ls hLs => by
      simp only [hnorm]
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (hB Ls fun σ hσ => ⟨pp_dual_mem La σ (hLs σ hσ).1, (hLs σ hσ).2⟩)
        (inv_nonneg.2 hκ.le))
    (S.image fun z => t₀ + z)
    (fun t ht => by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 ht
      rw [add_sub_cancel_left]; exact hS z hz)
  rw [Finset.sum_image (fun x _ y _ h => add_left_cancel h), hnorm] at key
  have hA0 : A 0 = ∫ t, ((φ t : ℝ) : ℂ) := by simp [hA, TopsChoicePartA.fsC]
  rw [hA0] at key
  have key2 : ∑ z ∈ S, φ (t₀ + z) ≤ κ⁻¹ * ‖∫ t, ((φ t : ℝ) : ℂ)‖ + κ⁻¹ * B := by
    refine le_of_eq_of_le (Finset.sum_congr rfl fun z _ => ?_) key
    show φ (t₀ + z) = φ (cplx (Gm.reals (t₀ + z)))
    rw [cplx_reals]
  calc κ * ∑ z ∈ S, φ (t₀ + z) ≤ κ * (κ⁻¹ * ‖∫ t, ((φ t : ℝ) : ℂ)‖ + κ⁻¹ * B) :=
        mul_le_mul_of_nonneg_left key2 hκ.le
    _ = ‖∫ t, ((φ t : ℝ) : ℂ)‖ + B := by field_simp

end Main

theorem poissonPi (D : D7) : PoissonPi D := by
  intro La κ hL φ Cφ h1 h2 h3 t₀ B hB S hS
  obtain ⟨hκ, hd, U, hU, hvol⟩ := hL
  exact poisson_gen La κ hκ U hU hvol φ Cφ h1 h2 h3 t₀ B hB S hS

end Formalism.MainNotions.BlockEstimateWords

end

end PartPoPi

section PartLat1

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

open NumberField

theorem trace_places {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (a : K) :
    ((Algebra.trace ℚ K a : ℚ) : ℝ) = ∑ v : InfinitePlace K, 2 * (v.embedding a).re := by
  classical
  have h := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := a)
  rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => φ a)
      (fun σ => σ a) (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun φ => φ a)] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  have hq : (algebraMap ℚ ℂ (Algebra.trace ℚ K a)).re = ((Algebra.trace ℚ K a : ℚ) : ℝ) := by
    simp
  rw [hq] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Complex.re_sum]
  have hfib : ∀ φ ∈ (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w),
      (φ a).re = (w.embedding a).re := by
    intro φ hφ
    have hm := (Finset.mem_filter.mp hφ).2
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff] at hm
    rcases hm with rfl | hc
    · rfl
    · rw [← hc, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    (IsTotallyComplex.isComplex w).mult_eq_two]
  simp

theorem trace_tau (D : D7) (x : D.host.E) :
    ((Algebra.trace ℚ D.host.E x : ℚ) : ℝ) = ∑ v, 2 * (plEmb D v x).re := by
  have := host_totallyComplex D
  rw [trace_places x]
  refine (Fintype.sum_bijective (plOf D) (plOf_bijective D) _ _ fun v => ?_).symm
  rcases InfinitePlace.embedding_mk_eq (plEmb D v) with h | h
  · show _ = 2 * ((InfinitePlace.mk (plEmb D v)).embedding x).re
    rw [h]
  · show _ = 2 * ((InfinitePlace.mk (plEmb D v)).embedding x).re
    rw [h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]

theorem plEmb_ne_conj (D : D7) (v w : D.what₂.Tau) : plEmb D v ≠ ComplexEmbedding.conjugate (plEmb D w) := by
  have := host_totallyComplex D
  intro h
  have h1 : plOf D v = plOf D w := by
    unfold plOf
    rw [h, InfinitePlace.mk_conjugate_eq]
  have h2 := (plOf_bijective D).1 h1
  subst h2
  have h3 : ComplexEmbedding.IsReal (plEmb D v) := ComplexEmbedding.isReal_iff.2 h.symm
  exact (InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex (InfinitePlace.mk (plEmb D v)))) h3

theorem emb_indep (D : D7) (c : D.what₂.Tau → ℂ) (h : ∀ t : D.host.E, ∑ v, (c v * plEmb D v t).im = 0) :
    ∀ v, c v = 0 := by
  classical
  let g : D.what₂.Tau ⊕ D.what₂.Tau → (D.host.E →* ℂ) :=
    Sum.elim (fun v => (plEmb D v).toMonoidHom) (fun v => (ComplexEmbedding.conjugate (plEmb D v)).toMonoidHom)
  have e1 : ∀ v t, g (Sum.inl v) t = plEmb D v t := fun v t => rfl
  have e2 : ∀ v t, g (Sum.inr v) t = conj (plEmb D v t) := fun v t => rfl
  have hg : Function.Injective g := by
    intro i j hij
    have hv : ∀ t, g i t = g j t := fun t => by rw [hij]
    rcases i with v | v <;> rcases j with w | w
    · have : plEmb D v = plEmb D w := RingHom.ext fun t => by rw [← e1, ← e1]; exact hv t
      rw [plEmb_injective D this]
    · exfalso
      refine plEmb_ne_conj D v w (RingHom.ext fun t => ?_)
      rw [ComplexEmbedding.conjugate_coe_eq, ← e1, ← e2]; exact hv t
    · exfalso
      refine plEmb_ne_conj D w v (RingHom.ext fun t => ?_)
      rw [ComplexEmbedding.conjugate_coe_eq, ← e1, ← e2]; exact (hv t).symm
    · have : plEmb D v = plEmb D w := RingHom.ext fun t => by
        have := hv t
        rw [e2, e2] at this
        exact (starRingEnd ℂ).injective this
      rw [plEmb_injective D this]
  have hli := (linearIndependent_monoidHom D.host.E ℂ).comp g hg
  rw [Fintype.linearIndependent_iff] at hli
  have key := hli (Sum.elim c (fun v => - conj (c v))) ?_
  · intro v; exact key (Sum.inl v)
  · funext t
    rw [Finset.sum_apply, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, Function.comp_apply, Pi.zero_apply, e1, e2]
    have hz : ∀ v, c v * plEmb D v t + -(conj (c v)) * conj (plEmb D v t) =
        ((2 * (c v * plEmb D v t).im : ℝ) : ℂ) * Complex.I := fun v => by
      rw [← Complex.sub_conj, map_mul]; ring
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun v _ => hz v), ← Finset.sum_mul, ← Complex.ofReal_sum,
      ← Finset.mul_sum, h t]
    simp

theorem dual_int {ι : Type} [Fintype ι] (σ t : ι → ℂ) (h : ∏ v, TopsChoicePartA.fsC (σ v) (t v) = 1) :
    ∃ n : ℤ, ∑ v, (σ v * t v).im = n * Real.pi := by
  have h1 : ∀ v, TopsChoicePartA.fsC (σ v) (t v) = Complex.exp (((2 * (σ v * t v).im : ℝ) : ℂ) * Complex.I) := fun v => by
    unfold TopsChoicePartA.fsC
    rw [← Complex.sub_conj, map_mul]
    rfl
  rw [Finset.prod_congr rfl (fun v _ => h1 v), ← Complex.exp_sum, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← Finset.mul_sum] at hn
  have h3 : ((2 * ∑ v, (σ v * t v).im : ℝ) : ℂ) * Complex.I = ((n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    rw [hn]; push_cast; ring
  have h4 := mul_right_cancel₀ Complex.I_ne_zero h3
  have h5 : 2 * ∑ v, (σ v * t v).im = n * (2 * Real.pi) := by exact_mod_cast h4
  linarith

theorem dual_of_full {D : D7} (a : ℕ → ℕ → D.what₂.Tau → ℂ) {δ : D.host.E} {L : LatticeDataWithDual D} (hδ : δ ≠ 0) {b s : ℕ}
    (hfull : FullLat D (L.La b s)) (ha : ∀ v, a b s v ≠ 0) :
    ∀ σ ∈ GramWordSpace.dualS D (laC a L b s), ∃ l ∈ dualPsi D δ (L.La b s), σ = sgm a δ b s l := by
  classical
  intro σ hσ
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hπc : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hint : ∀ t ∈ L.La b s, ∃ n : ℤ, ∑ v, (σ v * (a b s v * plEmb D v t)).im = n * Real.pi := fun t ht =>
    dual_int σ (tau a b s t) (hσ (tau a b s t) (AddSubgroup.mem_map.2 ⟨t, ht, rfl⟩))
  let φ0 : D.host.E →+ ℝ :=
    { toFun := fun t => (∑ v, (σ v * (a b s v * plEmb D v t)).im) / Real.pi
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [map_add, mul_add, Complex.add_im, Finset.sum_add_distrib, add_div] }
  let φ : D.host.E →ₗ[ℚ] ℝ := φ0.toRatLinearMap
  have hφ : ∀ t, φ t = (∑ v, (σ v * (a b s v * plEmb D v t)).im) / Real.pi := fun t => rfl
  have hrat : ∀ t : D.host.E, ∃ q : ℚ, φ t = q := by
    intro t
    have ht : t ∈ Submodule.span ℚ (L.La b s : Set D.host.E) := by rw [hfull.2]; trivial
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, hn⟩ := hint x hx
      exact ⟨(n : ℚ), by rw [hφ, hn, mul_div_assoc, div_self hπ, mul_one]; simp⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨p, hp⟩ := hx
      obtain ⟨q, hq⟩ := hy
      exact ⟨p + q, by rw [map_add, hp, hq]; push_cast; ring⟩
    | smul r x _ hx =>
      obtain ⟨p, hp⟩ := hx
      exact ⟨r * p, by rw [map_smul, hp, Rat.smul_def]; push_cast; ring⟩
  let bs := Module.finBasis ℚ D.host.E
  choose q hq using fun i => hrat (bs i)
  have hB : (Algebra.traceForm ℚ D.host.E).Nondegenerate := traceForm_nondegenerate ℚ D.host.E
  let m : D.host.E := ∑ i, q i • (Algebra.traceForm ℚ D.host.E).dualBasis hB bs i
  have hm : ∀ j, Algebra.trace ℚ D.host.E (m * bs j) = q j := by
    intro j
    rw [← Algebra.traceForm_apply]
    simp only [m, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.BilinForm.apply_dualBasis_left, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  let Φ2 : D.host.E →ₗ[ℚ] ℝ := (Algebra.linearMap ℚ ℝ).comp ((Algebra.traceForm ℚ D.host.E) m)
  have hΦ2 : ∀ t, Φ2 t = ((Algebra.trace ℚ D.host.E (m * t) : ℚ) : ℝ) := fun t => by
    simp only [Φ2, LinearMap.comp_apply, Algebra.linearMap_apply, eq_ratCast, Algebra.traceForm_apply]
  have heq : φ = Φ2 := bs.ext fun i => by rw [hq i, hΦ2, hm]
  have hall : ∀ t, (∑ v, (σ v * (a b s v * plEmb D v t)).im) / Real.pi = ∑ v, 2 * (plEmb D v (m * t)).re := fun t => by
    rw [← hφ, heq, hΦ2, trace_tau]
  have hc : ∀ v, σ v * a b s v / (Real.pi : ℂ) - 2 * Complex.I * plEmb D v m = 0 := by
    apply emb_indep D
    intro t
    have h2 : ∀ v, ((σ v * a b s v / (Real.pi : ℂ) - 2 * Complex.I * plEmb D v m) * plEmb D v t).im =
        (σ v * (a b s v * plEmb D v t)).im / Real.pi - 2 * (plEmb D v (m * t)).re := by
      intro v
      have e : (σ v * a b s v / (Real.pi : ℂ) - 2 * Complex.I * plEmb D v m) * plEmb D v t =
          (σ v * (a b s v * plEmb D v t)) / (Real.pi : ℂ) - Complex.I * (((2 : ℝ) : ℂ) * plEmb D v (m * t)) := by
        rw [map_mul]; push_cast; ring
      rw [e, Complex.sub_im, Complex.div_ofReal_im, Complex.I_mul_im, Complex.re_ofReal_mul]
    rw [Finset.sum_congr rfl fun v _ => h2 v, Finset.sum_sub_distrib, ← Finset.sum_div, hall t, sub_self]
  refine ⟨m * δ, ?_, ?_⟩
  · intro c hc'
    obtain ⟨n, hn⟩ := hint c hc'
    refine ⟨n, ?_⟩
    have h1 := hall c
    rw [hn, mul_div_assoc, div_self hπ, mul_one, ← trace_tau] at h1
    have h2 : m * δ * c / δ = m * c := by field_simp
    rw [h2]
    have h3 : ((Algebra.trace ℚ D.host.E (m * c) : ℚ) : ℝ) = (((n : ℤ) : ℚ) : ℝ) := by rw [← h1]; simp
    exact_mod_cast h3
  · funext v
    have h3 : σ v * a b s v / (Real.pi : ℂ) = 2 * Complex.I * plEmb D v m := sub_eq_zero.1 (hc v)
    rw [div_eq_iff hπc] at h3
    have h2 : m * δ / δ = m := by field_simp
    unfold sgm
    rw [h2, eq_div_iff (ha v), h3]
    ring

section Scl

variable {ι : Type} [Fintype ι]

def scl (c : ι → ℂ) : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) :=
  LinearMap.pi fun v => (Algebra.lmul ℝ ℂ (c v)) ∘ₗ LinearMap.proj v

theorem scl_apply (c : ι → ℂ) (t : ι → ℂ) (v : ι) : scl c t v = c v * t v := by
  rfl

theorem scl_det (c : ι → ℂ) : LinearMap.det (scl c) = ∏ v, Complex.normSq (c v) := by
  unfold scl
  rw [LinearMap.det_pi]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Algebra.norm_complex_apply, Algebra.norm_apply]

theorem scl_inv_left (c : ι → ℂ) (hc : ∀ v, c v ≠ 0) (t : ι → ℂ) : scl (fun v => (c v)⁻¹) (scl c t) = t := by
  funext v
  rw [scl_apply, scl_apply, ← mul_assoc, inv_mul_cancel₀ (hc v), one_mul]

theorem scl_inv_right (c : ι → ℂ) (hc : ∀ v, c v ≠ 0) (t : ι → ℂ) : scl c (scl (fun v => (c v)⁻¹) t) = t := by
  funext v
  rw [scl_apply, scl_apply, ← mul_assoc, mul_inv_cancel₀ (hc v), one_mul]

theorem scl_qmp (c : ι → ℂ) (hc : ∀ v, c v ≠ 0) :
    Measure.QuasiMeasurePreserving (scl c) (volume : Measure (ι → ℂ)) volume := by
  have hdet : LinearMap.det (scl c) ≠ 0 := by
    rw [scl_det]
    exact Finset.prod_ne_zero_iff.2 fun v _ => fun h0 => hc v (Complex.normSq_eq_zero.1 h0)
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ)) hdet
  refine ⟨(LinearMap.continuous_of_finiteDimensional (scl c)).measurable, ?_⟩
  rw [hmap]
  exact Measure.smul_absolutelyContinuous

theorem fund_scl (c : ι → ℂ) (hc : ∀ v, c v ≠ 0) (Λ : AddSubgroup (ι → ℂ)) (F : Set (ι → ℂ))
    (hF : IsAddFundamentalDomain Λ F volume) :
    IsAddFundamentalDomain (Λ.map (scl c).toAddMonoidHom) (scl c '' F) volume := by
  let f : (ι → ℂ) ≃ (ι → ℂ) :=
    { toFun := scl c
      invFun := scl (fun v => (c v)⁻¹)
      left_inv := scl_inv_left c hc
      right_inv := scl_inv_right c hc }
  have hq : Measure.QuasiMeasurePreserving f.symm (volume : Measure (ι → ℂ)) volume :=
    scl_qmp (fun v => (c v)⁻¹) (fun v => inv_ne_zero (hc v))
  let e : (Λ.map (scl c).toAddMonoidHom) ≃ Λ :=
    { toFun := fun g => ⟨scl (fun v => (c v)⁻¹) g.1, by
        obtain ⟨y, hy, h⟩ := AddSubgroup.mem_map.1 g.2
        rw [← h]
        show scl (fun v => (c v)⁻¹) (scl c y) ∈ Λ
        rw [scl_inv_left c hc]
        exact hy⟩
      invFun := fun g => ⟨scl c g.1, AddSubgroup.mem_map.2 ⟨g.1, g.2, rfl⟩⟩
      left_inv := fun g => Subtype.ext (scl_inv_right c hc g.1)
      right_inv := fun g => Subtype.ext (scl_inv_left c hc g.1) }
  have key := hF.image_of_equiv f hq e (fun g x => by
    show scl c (scl (fun v => (c v)⁻¹) g.1 + x) = g.1 + scl c x
    rw [map_add, scl_inv_right c hc])
  exact key

theorem vol_scl (c : ι → ℂ) (F : Set (ι → ℂ)) :
    volume (scl c '' F) = ENNReal.ofReal (∏ v, ‖c v‖ ^ 2) * volume F := by
  rw [Measure.addHaar_image_linearMap, scl_det]
  congr 2
  rw [abs_of_nonneg (Finset.prod_nonneg fun v _ => Complex.normSq_nonneg _)]
  exact Finset.prod_congr rfl fun v _ => Complex.normSq_eq_norm_sq _

end Scl

theorem one_le_prod_int (D : D7) (y : 𝓞 D.host.E) (hy : y ≠ 0) :
    1 ≤ ∏ v, ‖plEmb D v (y : D.host.E)‖ ^ 2 := by
  have := host_totallyComplex D
  have h1 := InfinitePlace.prod_eq_abs_norm (y : D.host.E)
  have h2 : ∏ w : InfinitePlace D.host.E, w (y : D.host.E) ^ w.mult = ∏ v, ‖plEmb D v (y : D.host.E)‖ ^ 2 := by
    rw [prod_places D]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [(IsTotallyComplex.isComplex (plOf D v)).mult_eq_two, plOf_apply]
  rw [← h2, h1, ← Algebra.coe_norm_int]
  have h3 : Algebra.norm ℤ y ≠ 0 := Algebra.norm_ne_zero_iff.2 hy
  have h4 : (1 : ℤ) ≤ |Algebra.norm ℤ y| := Int.one_le_abs h3
  exact_mod_cast h4

theorem exists_denom (D : D7) (M : Submodule ℤ D.host.E) (hfg : M.FG) :
    ∃ β : 𝓞 D.host.E, β ≠ 0 ∧ ∀ x ∈ M, ∃ y : 𝓞 D.host.E,
      algebraMap (𝓞 D.host.E) D.host.E y = algebraMap (𝓞 D.host.E) D.host.E β * x := by
  classical
  obtain ⟨S, hS⟩ := hfg
  obtain ⟨β, hβ⟩ := IsLocalization.exist_integer_multiples_of_finset (𝓞 D.host.E)⁰ S
  refine ⟨β.1, nonZeroDivisors.ne_zero β.2, fun x hx => ?_⟩
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy⟩ := hβ x hx
    exact ⟨y, by rw [hy, Algebra.smul_def]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    exact ⟨p + q, by rw [map_add, hp, hq, mul_add]⟩
  | smul n x _ hx =>
    obtain ⟨p, hp⟩ := hx
    exact ⟨n • p, by rw [map_zsmul, hp, mul_smul_comm]⟩

theorem discrete_laC {D : D7} (a : ℕ → ℕ → D.what₂.Tau → ℂ) {L : LatticeDataWithDual D} {b s : ℕ} (hfg : (L.La b s).FG)
    (ha : ∀ v, a b s v ≠ 0) : DiscreteTopology (laC a L b s) := by
  classical
  obtain ⟨β, hβ0, hβ⟩ := exists_denom D (L.La b s) hfg
  have hβE : (β : D.host.E) ≠ 0 := by
    intro h0
    exact hβ0 (NumberField.RingOfIntegers.coe_injective (h0.trans (map_zero (algebraMap (𝓞 D.host.E) D.host.E)).symm))
  set Bn : ℝ := ∏ v, ‖plEmb D v (β : D.host.E)‖ ^ 2 with hBn
  have hBn0 : 0 < Bn := Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 ((map_ne_zero (plEmb D v)).2 hβE)) 2
  set A : ℝ := ∏ v, ‖a b s v‖ ^ 2 with hA
  have hA0 : 0 < A := Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 (ha v)) 2
  have hcard : Fintype.card D.what₂.Tau ≠ 0 := by
    rw [D.what₂.card_Tau]; exact (f_pos D).ne'
  apply discreteTopology_of_isOpen_singleton_zero
  rw [Metric.isOpen_singleton_iff]
  have hε0 : 0 < min 1 (A / Bn / 2) := lt_min one_pos (by positivity)
  refine ⟨min 1 (A / Bn / 2), hε0, fun y hy => ?_⟩
  set ε : ℝ := min 1 (A / Bn / 2) with hε
  obtain ⟨t, ht, hty⟩ := AddSubgroup.mem_map.1 y.2
  by_contra hne
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hne
    apply Subtype.ext
    rw [← hty, map_zero]
    rfl
  obtain ⟨z, hz⟩ := hβ t ht
  have hzE : (z : D.host.E) = (β : D.host.E) * t := hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    have h0 : (β : D.host.E) * t = 0 := by rw [← hzE]; rfl
    exact (mul_ne_zero hβE ht0) h0
  have h1 := one_le_prod_int D z hz0
  have h1' : 1 ≤ Bn * ∏ v, ‖plEmb D v t‖ ^ 2 := by
    rw [hBn, ← Finset.prod_mul_distrib]
    refine le_of_le_of_eq h1 (Finset.prod_congr rfl fun v _ => ?_)
    rw [hzE, map_mul, norm_mul, mul_pow]
  have hnorm : ‖(y : D.what₂.Tau → ℂ)‖ < ε := by
    have := hy
    rw [Subtype.dist_eq] at this
    simpa using this
  have h2 : ∀ v, ‖a b s v‖ * ‖plEmb D v t‖ ≤ ε := fun v => by
    have h3 : (y : D.what₂.Tau → ℂ) v = a b s v * plEmb D v t := by rw [← hty]; rfl
    rw [← norm_mul, ← h3]
    exact le_trans (norm_le_pi_norm _ v) hnorm.le
  have h4 : A * ∏ v, ‖plEmb D v t‖ ^ 2 ≤ (ε ^ 2) ^ Fintype.card D.what₂.Tau := by
    rw [hA, ← Finset.prod_mul_distrib, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_le_prod (fun v _ => by positivity) fun v _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (h2 v) 2
  have hε1 : ε ≤ 1 := min_le_left _ _
  have h5 : (ε ^ 2) ^ Fintype.card D.what₂.Tau ≤ ε := by
    refine le_trans (pow_le_of_le_one (by positivity) (by nlinarith) hcard) (by nlinarith)
  have h6 : ε ≤ A / Bn / 2 := min_le_right _ _
  have h7 : A * ∏ v, ‖plEmb D v t‖ ^ 2 ≤ A / Bn / 2 := le_trans h4 (le_trans h5 h6)
  have h8 : Bn * ∏ v, ‖plEmb D v t‖ ^ 2 ≤ 1 / 2 := by
    have h9 : A * (Bn * ∏ v, ‖plEmb D v t‖ ^ 2) ≤ A * (1 / 2) := by
      have : A * (Bn * ∏ v, ‖plEmb D v t‖ ^ 2) = Bn * (A * ∏ v, ‖plEmb D v t‖ ^ 2) := by ring
      rw [this]
      calc Bn * (A * ∏ v, ‖plEmb D v t‖ ^ 2) ≤ Bn * (A / Bn / 2) := mul_le_mul_of_nonneg_left h7 hBn0.le
        _ = A * (1 / 2) := by field_simp
    exact le_of_mul_le_mul_left h9 hA0
  linarith

theorem isLat_of_LatAx {D : D7} (a : ℕ → ℕ → D.what₂.Tau → ℂ) {δ : D.host.E} {L : LatticeDataWithDual D} (hL : LatAx D δ L) {b s : ℕ}
    (hb : IsBlockSL2Embedding D b s) (ha : ∀ v, a b s v ≠ 0) :
    GramWordSpace.IsLat D (laC a L b s) (L.κ * ∏ v, (‖a b s v‖ / L.ρ b s) ^ 2) := by
  obtain ⟨hκ, hall⟩ := hL
  obtain ⟨hρ, hfull, -, ⟨F, -, hF, hvol⟩, -, -⟩ := hall b s hb
  have hρc : ((L.ρ b s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  set c : D.what₂.Tau → ℂ := fun v => a b s v / ((L.ρ b s : ℝ) : ℂ) with hcdef
  have hc : ∀ v, c v ≠ 0 := fun v => div_ne_zero (ha v) hρc
  have hmap : laC a L b s =
      ((L.La b s).toAddSubgroup.map (embInfS D (L.ρ b s))).map (scl c).toAddMonoidHom := by
    rw [AddSubgroup.map_map]
    unfold laC
    congr 1
    refine AddMonoidHom.ext fun t => funext fun v => ?_
    show a b s v * plEmb D v t = scl c (embInfS D (L.ρ b s) t) v
    rw [scl_apply]
    show a b s v * plEmb D v t = a b s v / ((L.ρ b s : ℝ) : ℂ) * (((L.ρ b s : ℝ) : ℂ) * plEmb D v t)
    field_simp
  have hnc : ∀ v, ‖c v‖ = ‖a b s v‖ / L.ρ b s := fun v => by
    rw [hcdef]
    simp only [norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  refine ⟨mul_pos hκ (Finset.prod_pos fun v _ => pow_pos (div_pos (norm_pos_iff.2 (ha v)) hρ) 2),
    discrete_laC a hfull.1 ha, scl c '' F, ?_, ?_⟩
  · rw [hmap]
    exact fund_scl c hc _ F hF
  · rw [vol_scl, hvol, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => by positivity), mul_comm]
    congr 2
    exact Finset.prod_congr rfl fun v _ => by rw [hnc v]

theorem dual_of_LatAx {D : D7} (a : ℕ → ℕ → D.what₂.Tau → ℂ) {δ : D.host.E} {L : LatticeDataWithDual D} (hL : LatAx D δ L) (hδ : δ ≠ 0)
    {b s : ℕ} (hb : IsBlockSL2Embedding D b s) (ha : ∀ v, a b s v ≠ 0) :
    ∀ σ ∈ GramWordSpace.dualS D (laC a L b s), ∃ l ∈ dualPsi D δ (L.La b s), σ = sgm a δ b s l :=
  dual_of_full a hδ (hL.2 b s hb).2.1 ha

end Formalism.MainNotions.BlockEstimateWords

end

end PartLat1

section PartLat2a

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Alg

variable {K : Type} [Field K] [NumberField K]

theorem fg_spanning_submodule_basis (M : Submodule ℤ K) (hfg : M.FG) (hsp : Submodule.span ℚ (M : Set K) = ⊤) :
    ∃ (ι : Type) (_ : Finite ι) (b : Module.Basis ι ℚ K), Submodule.span ℤ (Set.range b) = M := by
  have : Module.Finite ℤ M := Module.Finite.iff_fg.2 hfg
  have : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
  let bM := Module.Free.chooseBasis ℤ M
  let v : Module.Free.ChooseBasisIndex ℤ M → K := fun i => (bM i : K)
  have hli : LinearIndependent ℤ v :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hspan : Submodule.span ℤ (Set.range v) = M := by
    have h1 : Set.range v = M.subtype '' Set.range bM := by
      rw [← Set.range_comp]; rfl
    rw [h1, Submodule.span_image, bM.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hliQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have htop : ⊤ ≤ Submodule.span ℚ (Set.range v) := by
    rw [← hsp]
    refine Submodule.span_le.2 fun x hx => ?_
    have hx' : x ∈ Submodule.span ℤ (Set.range v) := by rw [hspan]; exact hx
    exact Submodule.span_le_restrictScalars ℤ ℚ _ hx'
  refine ⟨_, inferInstance, Module.Basis.mk hliQ htop, ?_⟩
  rw [Module.Basis.coe_mk]
  exact hspan

theorem dual_ideal_subset (M : Submodule ℤ K) (hfg : M.FG) (hsp : Submodule.span ℚ (M : Set K) = ⊤) (δ : K) (hδ : δ ≠ 0)
    (aa : FractionalIdeal (𝓞 K)⁰ K) (haa : aa ≠ 0)
    (hsub : ∀ l : K, (∀ c ∈ M, ∃ z : ℤ, Algebra.trace ℚ K (l * c / δ) = (z : ℚ)) → l ∈ aa)
    (c : K) (hc : c ∈ FractionalIdeal.spanSingleton (𝓞 K)⁰ δ * FractionalIdeal.dual ℤ ℚ aa) : c ∈ M := by
  obtain ⟨ι, _, b, hb⟩ := fg_spanning_submodule_basis M hfg hsp
  obtain ⟨c', hc', rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hc
  have hdd := LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis (R := ℤ) (Algebra.traceForm ℚ K)
    (traceForm_nondegenerate ℚ K) (Algebra.traceForm_isSymm ℚ) b
  rw [hb] at hdd
  rw [← hdd, LinearMap.BilinForm.mem_dualSubmodule]
  intro y hy
  have hl : δ * y ∈ aa := by
    refine hsub _ fun c1 hc1 => ?_
    have h1 := (LinearMap.BilinForm.mem_dualSubmodule _).1 hy c1 hc1
    obtain ⟨z, hz⟩ := Submodule.mem_one.1 h1
    refine ⟨z, ?_⟩
    rw [Algebra.traceForm_apply] at hz
    have e : δ * y * c1 / δ = y * c1 := by field_simp
    rw [e, ← hz]; rfl
  have h2 := (FractionalIdeal.mem_dual haa).1 hc' (δ * y) hl
  obtain ⟨z, hz⟩ := h2
  rw [Algebra.traceForm_apply] at hz
  rw [Submodule.mem_one, Algebra.traceForm_apply]
  refine ⟨z, ?_⟩
  rw [hz]
  congr 1; ring

theorem abs_norm_span_dual (δ : K) (aa : FractionalIdeal (𝓞 K)⁰ K) :
    FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ δ * FractionalIdeal.dual ℤ ℚ aa) =
      |Algebra.norm ℚ δ| * (((NumberField.discr K).natAbs : ℚ))⁻¹ * (FractionalIdeal.absNorm aa)⁻¹ := by
  rw [map_mul, FractionalIdeal.absNorm_span_singleton, FractionalIdeal.dual_eq_mul_inv, map_mul, map_inv₀, mul_assoc]
  congr 2
  have h1 := coeIdeal_differentIdeal ℤ ℚ K (𝓞 K)
  have h2 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) =
      ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [h1, inv_inv]
  rw [h2, map_inv₀, FractionalIdeal.coeIdeal_absNorm, NumberField.absNorm_differentIdeal K (𝓞 K)]

end Alg

end Formalism.MainNotions.BlockEstimateWords

end

end PartLat2a

section PartLat2b

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Geo

open NumberField

variable (D : D7)

instance hostFieldTotallyComplex : NumberField.IsTotallyComplex D.host.E := host_totallyComplex D

theorem place_is_complex (v : D.what₂.Tau) : (plOf D v).IsComplex := NumberField.IsTotallyComplex.isComplex _

def l2Pl : D.what₂.Tau ≃ {w : InfinitePlace D.host.E // w.IsComplex} :=
  Equiv.ofBijective (fun v => ⟨plOf D v, place_is_complex D v⟩) (by
    constructor
    · intro v w h
      exact (plOf_bijective D).1 (congrArg Subtype.val h)
    · intro w
      obtain ⟨v, hv⟩ := (plOf_bijective D).2 w.1
      exact ⟨v, Subtype.ext hv⟩)

instance no_real_places : IsEmpty {w : InfinitePlace D.host.E // w.IsReal} :=
  ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.2 (NumberField.IsTotallyComplex.isComplex w.1)) w.2⟩

def l2cj (v : D.what₂.Tau) : ℂ ≃ₗ[ℝ] ℂ :=
  if (plOf D v).embedding = plEmb D v then LinearEquiv.refl ℝ ℂ else Complex.conjAe.toLinearEquiv

theorem place_conj_apply (v : D.what₂.Tau) (x : D.host.E) : l2cj D v ((plOf D v).embedding x) = plEmb D v x := by
  unfold l2cj
  split_ifs with h
  · rw [h]; rfl
  · rcases InfinitePlace.embedding_mk_eq (plEmb D v) with h' | h'
    · exact absurd h' h
    · have e : (plOf D v).embedding = NumberField.ComplexEmbedding.conjugate (plEmb D v) := h'
      rw [e, NumberField.ComplexEmbedding.conjugate_coe_eq]
      simp

theorem place_conj_measure_preserving (v : D.what₂.Tau) : MeasurePreserving (l2cj D v) volume volume := by
  unfold l2cj
  split_ifs
  · exact MeasurePreserving.id volume
  · have e : ⇑(Complex.conjAe.toLinearEquiv : ℂ ≃ₗ[ℝ] ℂ) = ⇑Complex.conjLIE := by funext z; simp
    rw [e]
    exact Complex.conjLIE.measurePreserving

def l2g0 : mixedEmbedding.mixedSpace D.host.E ≃ₗ[ℝ] (D.what₂.Tau → ℂ) :=
  (LinearEquiv.uniqueProd).trans ((LinearEquiv.funCongrLeft ℝ ℂ (l2Pl D)).trans (LinearEquiv.piCongrRight (l2cj D)))

theorem l2g0_apply (x : mixedEmbedding.mixedSpace D.host.E) (v : D.what₂.Tau) :
    l2g0 D x v = l2cj D v (x.2 (l2Pl D v)) := rfl

theorem l2g0_emb (x : D.host.E) : l2g0 D (mixedEmbedding D.host.E x) = fun v => plEmb D v x := by
  funext v
  rw [l2g0_apply]
  show l2cj D v ((mixedEmbedding D.host.E x).2 ⟨plOf D v, place_is_complex D v⟩) = _
  rw [mixedEmbedding.mixedEmbedding_apply_isComplex]
  exact place_conj_apply D v x

theorem l2g0_mp : MeasurePreserving (l2g0 D) volume volume := by
  have h1 : MeasurePreserving (Prod.snd : mixedEmbedding.mixedSpace D.host.E → ({w : InfinitePlace D.host.E // w.IsComplex} → ℂ))
      volume volume := by
    refine ⟨measurable_snd, ?_⟩
    rw [Measure.volume_eq_prod, Measure.map_snd_prod]
    have h : (volume : Measure ({w : InfinitePlace D.host.E // w.IsReal} → ℝ)) Set.univ = 1 := by
      rw [MeasureTheory.volume_pi, Measure.pi_of_empty]; simp
    rw [h, one_smul]
  have h2 : MeasurePreserving (fun (y : {w : InfinitePlace D.host.E // w.IsComplex} → ℂ) (v : D.what₂.Tau) => y (l2Pl D v))
      volume volume := by
    have := measurePreserving_arrowCongr' (fun _ : {w : InfinitePlace D.host.E // w.IsComplex} => (volume : Measure ℂ))
      (fun _ : D.what₂.Tau => (volume : Measure ℂ)) (l2Pl D).symm (MeasurableEquiv.refl ℂ) (fun _ => MeasurePreserving.id _)
    have e : (fun (y : {w : InfinitePlace D.host.E // w.IsComplex} → ℂ) (v : D.what₂.Tau) => y (l2Pl D v)) =
        ⇑(MeasurableEquiv.arrowCongr' (l2Pl D).symm (MeasurableEquiv.refl ℂ)) := by
      funext y v
      simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr']
    rw [e]
    exact this
  have h3 : MeasurePreserving (fun (t : D.what₂.Tau → ℂ) (v : D.what₂.Tau) => l2cj D v (t v)) volume volume :=
    volume_preserving_pi fun v => place_conj_measure_preserving D v
  exact (h3.comp h2).comp h1

theorem volume_image_isometry (S : Set (mixedEmbedding.mixedSpace D.host.E)) (hS : MeasurableSet (l2g0 D '' S)) :
    volume (l2g0 D '' S) = volume S := by
  rw [← (l2g0_mp D).measure_preimage hS.nullMeasurableSet, (l2g0 D).injective.preimage_image]

end Geo

end Formalism.MainNotions.BlockEstimateWords

end

end PartLat2b

section PartLat2c

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Main

open NumberField
open scoped Pointwise

variable (D : D7)

def l2G (ρ : ℝ) (hρ : ρ ≠ 0) : mixedEmbedding.mixedSpace D.host.E ≃ₗ[ℝ] (D.what₂.Tau → ℂ) :=
  (l2g0 D).trans (LinearEquiv.smulOfNeZero ℝ (D.what₂.Tau → ℂ) ρ hρ)

theorem scaled_embedding_mixed (ρ : ℝ) (hρ : ρ ≠ 0) (x : D.host.E) : l2G D ρ hρ (mixedEmbedding D.host.E x) = embInfS D ρ x := by
  funext v
  have e : l2G D ρ hρ (mixedEmbedding D.host.E x) = ρ • l2g0 D (mixedEmbedding D.host.E x) := rfl
  rw [e, l2g0_emb]
  show ρ • plEmb D v x = ((ρ : ℝ) : ℂ) * plEmb D v x
  rw [Complex.real_smul]

def l2b (J : (FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)ˣ) (ρ : ℝ) (hρ : ρ ≠ 0) :=
  (mixedEmbedding.fractionalIdealLatticeBasis D.host.E J).map (l2G D ρ hρ)

theorem scaled_lattice_basis_mem (J : (FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)ˣ) (ρ : ℝ) (hρ : ρ ≠ 0) (i) :
    ∃ y ∈ (J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), l2b D J ρ hρ i = embInfS D ρ y := by
  refine ⟨basisOfFractionalIdeal D.host.E J i, ?_, ?_⟩
  · rw [basisOfFractionalIdeal_apply]
    exact (fractionalIdealBasis D.host.E (J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) i).2
  · rw [l2b, Module.Basis.map_apply, mixedEmbedding.fractionalIdealLatticeBasis_apply, scaled_embedding_mixed]

theorem finrank_places_complex_alt : Module.finrank ℝ (D.what₂.Tau → ℂ) = 2 * D.R.f := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, D.what₂.card_Tau]
  ring

theorem scaled_lattice_fundamental_volume (J : (FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)ˣ) (ρ : ℝ) (hρ : 0 < ρ) :
    volume (ZSpan.fundamentalDomain (l2b D J ρ hρ.ne')) = ENNReal.ofReal (ρ ^ (2 * D.R.f)) *
      volume (ZSpan.fundamentalDomain (mixedEmbedding.fractionalIdealLatticeBasis D.host.E J)) := by
  set b0 := mixedEmbedding.fractionalIdealLatticeBasis D.host.E J
  rw [l2b, ← ZSpan.map_fundamentalDomain]
  have e : ⇑(l2G D ρ hρ.ne') '' ZSpan.fundamentalDomain b0 = ρ • (⇑(l2g0 D) '' ZSpan.fundamentalDomain b0) := by
    rw [← Set.image_smul, Set.image_image]; rfl
  have hm : MeasurableSet (⇑(l2g0 D) '' ZSpan.fundamentalDomain b0) := by
    rw [ZSpan.map_fundamentalDomain]; exact ZSpan.fundamentalDomain_measurableSet _
  rw [e, Measure.addHaar_smul, volume_image_isometry D _ hm, finrank_places_complex_alt D, abs_of_nonneg (by positivity)]

theorem complex_places_count : InfinitePlace.nrComplexPlaces D.host.E = D.R.f := by
  rw [InfinitePlace.nrComplexPlaces, ← D.what₂.card_Tau]
  exact (Fintype.card_congr (l2Pl D)).symm

theorem abs_norm_eq_prod_place_norms (δ : D.host.E) : (((|Algebra.norm ℚ δ| : ℚ)) : ℝ) = ∏ v, ‖plEmb D v δ‖ ^ 2 := by
  have h := InfinitePlace.prod_eq_abs_norm δ
  rw [prod_places D] at h
  rw [← h]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hm : (plOf D v).mult = 2 := InfinitePlace.mult_isComplex ⟨plOf D v, place_is_complex D v⟩
  rw [hm, plOf_apply]

theorem abs_discriminant_eq_root_pow : |((NumberField.discr D.host.E : ℤ) : ℝ)| = D.host.rdE ^ (2 * D.R.f) := by
  have hfr : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    push_cast
    ring
  have hf : (0 : ℝ) < 2 * (D.R.f : ℝ) := by have := f_pos D; positivity
  unfold Host.rdE
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), hfr]
  push_cast
  rw [one_div, inv_mul_cancel₀ hf.ne', Real.rpow_one]

end Main

end Formalism.MainNotions.BlockEstimateWords

end

end PartLat2c

section PartLat2

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Dens

open NumberField

theorem dualDensity (D : D7) (δ : D.host.E) (L : LatticeDataWithDual D) (hL : LatAx D δ L) (hδ : δ ≠ 0) (hv : 1 ≤ D.host.v)
    {b s : ℕ} (hbs : IsBlockSL2Embedding D b s) :
    L.κ * (∏ v, (kaV D δ v / L.ρ b s) ^ 2) * ((FractionalIdeal.absNorm (L.aaV b s) : ℚ) : ℝ) ≤
      Real.pi ^ (2 * D.R.f) := by
  obtain ⟨hκ, hblk⟩ := hL
  obtain ⟨hρ, hM, -, hcov, hdual, -⟩ := hblk b s hbs
  set ρ := L.ρ b s with hρdef
  by_cases haa : L.aaV b s = 0
  · rw [haa, map_zero]; simp only [Rat.cast_zero, mul_zero]; positivity
  set J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
    FractionalIdeal.spanSingleton _ δ * FractionalIdeal.dual ℤ ℚ (L.aaV b s) with hJdef
  have hJ : J ≠ 0 := mul_ne_zero (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])
    (FractionalIdeal.dual_ne_zero ℤ ℚ haa)
  set JU := Units.mk0 J hJ
  have hJM : ∀ y ∈ J, y ∈ L.La b s := fun y hy =>
    dual_ideal_subset (L.La b s) hM.1 hM.2 δ hδ _ haa (fun l hl => hdual hl) y hy
  obtain ⟨F, hFm, hF, hFv⟩ := hcov
  set b1 := l2b D JU ρ hρ.ne'
  have hfd := ZSpan.isAddFundamentalDomain' b1 volume
  have hsub : Submodule.span ℤ (Set.range b1) ≤ (L.La b s).map (embInfS D ρ).toIntLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨y, hy, e⟩ := scaled_lattice_basis_mem D JU ρ hρ.ne' i
    rw [e]
    exact ⟨y, hJM y hy, rfl⟩
  have hle : ∀ g ∈ (Submodule.span ℤ (Set.range b1)).toAddSubgroup,
      g ∈ (L.La b s).toAddSubgroup.map (embInfS D ρ) := by
    intro g hg
    obtain ⟨y, hy, e⟩ := hsub hg
    exact ⟨y, hy, e⟩
  have hc0 : Countable (Submodule.span ℤ (Set.range b1)) := inferInstance
  have hc : Countable (Submodule.span ℤ (Set.range b1)).toAddSubgroup := hc0
  have hvol : volume F ≤ volume (ZSpan.fundamentalDomain b1) := by
    refine hfd.measure_le_of_pairwise_disjoint hFm.nullMeasurableSet ?_
    intro g g' hgg'
    have hne : (⟨g.1, hle g.1 g.2⟩ : (L.La b s).toAddSubgroup.map (embInfS D ρ)) ≠ ⟨g'.1, hle g'.1 g'.2⟩ := by
      intro h; apply hgg'
      exact Subtype.ext (congrArg (fun z : (L.La b s).toAddSubgroup.map (embInfS D ρ) => (z : D.what₂.Tau → ℂ)) h)
    exact (hF.aedisjoint hne).mono (fun x hx => hx.1) (fun x hx => hx.1)
  rw [hFv, scaled_lattice_fundamental_volume D JU ρ hρ, mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis,
    mixedEmbedding.volume_fundamentalDomain_latticeBasis] at hvol

  set NJ : ℝ := ((FractionalIdeal.absNorm J : ℚ) : ℝ) with hNJ
  set d : ℝ := |((NumberField.discr D.host.E : ℤ) : ℝ)| with hddef
  have hXne : ENNReal.ofReal (ρ ^ (2 * D.R.f)) * (ENNReal.ofReal ((FractionalIdeal.absNorm ((JU : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) : ℚ) : ℝ) *
      (2⁻¹ ^ InfinitePlace.nrComplexPlaces D.host.E * ((NNReal.sqrt ‖NumberField.discr D.host.E‖₊ : NNReal) : ENNReal))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) ENNReal.coe_ne_top))
  have key0 := ENNReal.toReal_mono hXne hvol
  rw [ENNReal.toReal_ofReal hκ.le] at key0
  have hNJ0 : 0 ≤ NJ := by rw [hNJ]; exact_mod_cast FractionalIdeal.absNorm_nonneg J
  have key : L.κ ≤ ρ ^ (2 * D.R.f) * (NJ * ((2 : ℝ)⁻¹ ^ D.R.f * Real.sqrt d)) := by
    convert key0 using 1
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by
        have : (0 : ℚ) ≤ FractionalIdeal.absNorm ((JU : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) :=
          FractionalIdeal.absNorm_nonneg _
        exact_mod_cast this), ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.coe_toReal, complex_places_count D]
    simp [JU, hddef, Int.norm_eq_abs]
    exact Or.inl (Or.inl hNJ)

  set P : ℝ := ∏ v, ‖plEmb D v δ‖ ^ 2 with hPdef
  set NA : ℝ := ((FractionalIdeal.absNorm (L.aaV b s) : ℚ) : ℝ) with hNAdef
  have hδv : ∀ v, 0 < ‖plEmb D v δ‖ := fun v => norm_pos_iff.2 ((map_ne_zero (plEmb D v)).2 hδ)
  have hP : 0 < P := Finset.prod_pos fun v _ => pow_pos (hδv v) 2
  have hNA : 0 < NA := by
    have h1 : (0 : ℚ) ≤ FractionalIdeal.absNorm (L.aaV b s) := FractionalIdeal.absNorm_nonneg _
    have h2 : FractionalIdeal.absNorm (L.aaV b s) ≠ 0 := fun h => haa (FractionalIdeal.absNorm_eq_zero_iff.1 h)
    have h3 : (0 : ℚ) < FractionalIdeal.absNorm (L.aaV b s) := lt_of_le_of_ne h1 (Ne.symm h2)
    rw [hNAdef]; exact_mod_cast h3
  have hr : 0 < D.host.rdE := rdE_pos D
  have hr2 : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have hd : d = D.host.rdE ^ (2 * D.R.f) := abs_discriminant_eq_root_pow D
  have hNJR : NJ = P * d⁻¹ * NA⁻¹ := by
    rw [hNJ, hJdef, abs_norm_span_dual δ (L.aaV b s), Rat.cast_mul, Rat.cast_mul, Rat.cast_inv, Rat.cast_inv, abs_norm_eq_prod_place_norms,
      Rat.cast_natCast, Nat.cast_natAbs, Int.cast_abs]
  have hsq : Real.sqrt d = D.host.rdE ^ D.R.f := by
    rw [hd, pow_mul', Real.sqrt_sq (pow_nonneg hr.le _)]
  have hka : ∏ v, (kaV D δ v / ρ) ^ 2 = ((2 * Real.pi) ^ 2 / ρ ^ 2) ^ D.R.f / P := by
    have e : ∀ v, (kaV D δ v / ρ) ^ 2 = ((2 * Real.pi) ^ 2 / ρ ^ 2) / ‖plEmb D v δ‖ ^ 2 := by
      intro v
      have := hδv v
      unfold kaV
      field_simp
    rw [Finset.prod_congr rfl (fun v _ => e v), Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
      D.what₂.card_Tau]
  rw [hNJR, hsq, hd] at key
  rw [hka]
  calc L.κ * (((2 * Real.pi) ^ 2 / ρ ^ 2) ^ D.R.f / P) * NA
      ≤ (ρ ^ (2 * D.R.f) * (P * (D.host.rdE ^ (2 * D.R.f))⁻¹ * NA⁻¹ * ((2 : ℝ)⁻¹ ^ D.R.f * D.host.rdE ^ D.R.f))) *
          (((2 * Real.pi) ^ 2 / ρ ^ 2) ^ D.R.f / P) * NA := by gcongr
    _ = (Real.pi ^ 2 * (2 / D.host.rdE)) ^ D.R.f := by
      have hρn : ρ ≠ 0 := hρ.ne'
      have hrn : D.host.rdE ≠ 0 := hr.ne'
      have hPn : P ≠ 0 := hP.ne'
      have hNAn : NA ≠ 0 := hNA.ne'
      rw [pow_mul, pow_mul]
      have e : (ρ ^ 2) ^ D.R.f * (P * ((D.host.rdE ^ 2) ^ D.R.f)⁻¹ * NA⁻¹ * ((2 : ℝ)⁻¹ ^ D.R.f * D.host.rdE ^ D.R.f)) *
          (((2 * Real.pi) ^ 2 / ρ ^ 2) ^ D.R.f / P) * NA =
          ((ρ ^ 2) * ((D.host.rdE ^ 2)⁻¹ * ((2 : ℝ)⁻¹ * D.host.rdE)) * ((2 * Real.pi) ^ 2 / ρ ^ 2)) ^ D.R.f := by
        rw [mul_pow, mul_pow, mul_pow, inv_pow]
        field_simp
        rw [← mul_pow, ← mul_pow]
        congr 1
        field_simp
      rw [e]
      congr 1
      field_simp
    _ ≤ (Real.pi ^ 2) ^ D.R.f := by
      have h1 : 2 / D.host.rdE ≤ 1 := by rw [div_le_one hr]; linarith
      have h2 : 0 ≤ 2 / D.host.rdE := by positivity
      exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_right (by positivity) h1) _
    _ = Real.pi ^ (2 * D.R.f) := by rw [pow_mul]

end Dens

end Formalism.MainNotions.BlockEstimateWords

end

end PartLat2

section PartDefs3

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

def sclL (av : ℕ → ℕ → ℂ) : ℕ → List (ℂ × ℕ) → List (ℂ × ℕ)
  | _, [] => []
  | o, (t, s) :: bs => (av (o + 1) s * t, s) :: sclL av (o + s) bs

def okL (r : ℕ) (T T' : ℝ) (o s : ℕ) (t : ℂ) : Prop := t ≠ 0 ∧ (s = 1 → o = r → T * T' < Complex.normSq t)

def wLoc (k r : ℕ) (T T' : ℝ) : ℕ → List (ℂ × ℕ) → ℝ
  | _, [] => 1
  | o, (t, s) :: bs =>
    (if okL r T T' o s t then Real.sqrt (ptWeightFrom k r T T' o [(t, s)]) else 0) * wLoc k r T T' (o + s) bs

def cblk (κ : ℝ) (i s : ℕ) : ℝ := (κ ^ (s * (s - 1)))⁻¹ * ∏ l ∈ Finset.Ico i (i + s), κ ^ (4 * (l - 1))

def ccL (κ : ℝ) : ℕ → List (ℂ × ℕ) → ℝ
  | _, [] => 1
  | o, (_, s) :: bs => Real.sqrt (cblk κ (o + 1) s) * ccL κ (o + s) bs

structure LocFrame (D : D7) {k0 : ℕ} (hk : k0 + 1 = D.R.k) (G : GramWordSpace.GramMap k0 D.R.rS) (B : LocBessel D.R.k D.R.rS)
    (f : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (B.Wq →L[ℂ] B.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) where
  B' : LocBessel (k0 + 1) D.R.rS
  f' : GramWordSpace.GFn B'
  μ' : GramWordSpace.Sec k0
  av : ℕ → ℕ → ℂ
  A : ℝ
  hc : B'.c = cStd
  hε : ∀ i, B'.ε i = B.ε (Fin.cast (by omega) i)
  hlam : ∀ i, B'.lam i = B.lam (Fin.cast (by omega) i)
  hu : ∀ i, B'.u i = B.u (Fin.cast hk i)
  hu' : ∀ i, B'.u' i = B.u' (Fin.cast hk i)
  hT : Tz (k0 + 1) D.R.rS B'.z = (‖B.c‖ / 2) ^ (2 * D.R.rS) * Tz D.R.k D.R.rS B.z
  hT' : Tz (k0 + 1) D.R.rS B'.z' = (‖B.c‖ / 2) ^ (2 * D.R.rS) * Tz D.R.k D.R.rS B.z'
  hsec : IsSection (k0 + 1) D.R.rS B'.z B'.z' μ'
  hf : UnitaryLevelOperators.IsKFinCoefT B'.σ f'
  hav : ∀ i s, ‖av i s‖ = (‖B.c‖ / 2) ^ (2 * i + s - 3)
  hA : 0 < A
  val : ∀ γ γ' : Point ℂ (D.R.rS + 1),
    ((Real.sqrt (ptWeightFrom D.R.k D.R.rS (Tz D.R.k D.R.rS B.z) (Tz D.R.k D.R.rS B.z') 0 γ.1) *
        Real.sqrt (ptWeightFrom D.R.k D.R.rS (Tz D.R.k D.R.rS B.z) (Tz D.R.k D.R.rS B.z') 0 γ'.1) : ℝ) : ℂ) *
      hsInner ((BlockEstimateTheorem.vmOf D hk G).V B f γ.1) ((BlockEstimateTheorem.vmOf D hk G).V B f γ'.1) =
    ((A * (ccL (‖B.c‖ / 2) 0 γ.1 * ccL (‖B.c‖ / 2) 0 γ'.1) *
        (wLoc (k0 + 1) D.R.rS (Tz (k0 + 1) D.R.rS B'.z) (Tz (k0 + 1) D.R.rS B'.z') 0 (sclL av 0 γ.1) *
          wLoc (k0 + 1) D.R.rS (Tz (k0 + 1) D.R.rS B'.z) (Tz (k0 + 1) D.R.rS B'.z') 0 (sclL av 0 γ'.1)) : ℝ) : ℂ) *
      hsInner (G.V B' f' (sclL av 0 γ.1)) (G.V B' f' (sclL av 0 γ'.1))
  energy : ENNReal.ofReal (A * (B'.beta μ' f' f').re) ≤
    ∫⁻ p : (Fin D.R.rS → ℂ) × ℂ, ENNReal.ofReal (bcWeight D.R.k D.R.rS (Tz D.R.k D.R.rS B.z) (Tz D.R.k D.R.rS B.z') p *
      hsNormSq (B.J f (bigCell D.R.k D.R.rS p.1 (μsec p.2))))

def FrameOpen (D : D7) {k0 : ℕ} (hk : k0 + 1 = D.R.k) (G : GramWordSpace.GramMap k0 D.R.rS) : Prop :=
  ∀ (B : LocBessel D.R.k D.R.rS)
    (f : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (B.Wq →L[ℂ] B.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ),
    B.c ≠ 0 → (B.c.re = 0 ∨ B.c.im = 0) → IsKFinCoefH B.σ f → IsSection D.R.k D.R.rS B.z B.z' μsec →
    Nonempty (LocFrame D hk G B f μsec)

def CutOpen (D : D7) {k0 : ℕ} (G : GramWordSpace.GramMap k0 D.R.rS) : Prop :=
  ∀ (B : LocBessel (k0 + 1) D.R.rS) (f : GramWordSpace.GFn B) (χ : ℝ → ℝ), B.c = cStd → IsCutoff χ → UnitaryLevelOperators.IsKFinCoefT B.σ f →
    ∀ γ : Point ℂ (D.R.rS + 1), ∀ᶠ eps in 𝓝[>] (0 : ℝ), G.V B (UnitaryLevelOperators.cutF B.z B.z' χ eps f) γ.1 = G.V B f γ.1

def RadOpen (k0 r : ℕ) : Prop :=
  ∀ (L : LocBessel (k0 + 1) r) (μsec : GramWordSpace.Sec k0), IsSection (k0 + 1) r L.z L.z' μsec →
    ∀ (j : ℕ) (hj : j ≤ r), ∃ R, GramWordSpace.IsRadQQd (GramWordSpace.lev L μsec j hj) R

def DualDensity (D : D7) (δ : D.host.E) (L : LatticeDataWithDual D) : Prop :=
  ∀ b s, IsBlockSL2Embedding D b s →
    L.κ * (∏ v, (kaV D δ v / L.ρ b s) ^ 2) * ((FractionalIdeal.absNorm (L.aaV b s) : ℚ) : ℝ) ≤ Real.pi ^ (2 * D.R.f)

def LatOpen (D : D7) (δ : D.host.E) (L : LatticeDataWithDual D) : Prop :=
  ∀ (a : ℕ → ℕ → D.what₂.Tau → ℂ) (b s : ℕ), IsBlockSL2Embedding D b s → (∀ v, a b s v ≠ 0) →
    GramWordSpace.IsLat D (laC a L b s) (L.κ * ∏ v, (‖a b s v‖ / L.ρ b s) ^ 2) ∧
    ∀ σ ∈ GramWordSpace.dualS D (laC a L b s), ∃ l ∈ dualPsi D δ (L.La b s), σ = sgm a δ b s l

section Glob

variable {D : D7} (L : LatticeDataWithDual D) (kap : D.what₂.Tau → ℝ) (av : D.what₂.Tau → ℕ → ℕ → ℂ) (Aa : D.what₂.Tau → ℝ)

def aG : ℕ → ℕ → D.what₂.Tau → ℂ := fun i s v => av v i s * (((if L.ρ i s = 0 then 1 else L.ρ i s : ℝ) : ℝ) : ℂ)

def cbG : ℕ → ℕ → ℝ := fun i s => L.κ ^ s * ∏ v, cblk (kap v) i s

def c0G : ℝ := (∏ v, Aa v) / L.κ ^ (D.R.rS + 1)

def κLG : ℕ → ℕ → ℝ := fun i s => L.κ * ∏ v, (‖aG L av i s v‖ / L.ρ i s) ^ 2

end Glob

structure XTie {D : D7} {k0 : ℕ} (X : GramWordSpace.Dat D k0) (x : D.what₂.Tau → LocalDataRealPlace D) (T T' : ℝ) (kap : D.what₂.Tau → ℝ) : Prop where
  hT : ∀ v, X.T v = kap v ^ (2 * D.R.rS) * T
  hT' : ∀ v, X.T' v = kap v ^ (2 * D.R.rS) * T'
  lam : ∀ v, (X.loc v).lam = (x v).lam
  u : ∀ v, (X.loc v).u = (x v).u
  u' : ∀ v, (X.loc v).u' = (x v).u'
  a : ∀ v, X.a v = (x v).a
  b : ∀ v, X.b v = (x v).b
  a1 : ∀ v, X.a1 v = (x v).a1
  b1 : ∀ v, X.b1 v = (x v).b1

def mkX {D : D7} {k0 : ℕ} (hk : k0 + 1 = D.R.k) {G : GramWordSpace.GramMap k0 D.R.rS} {B : D.what₂.Tau → LocBessel D.R.k D.R.rS}
    {f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp)}
    {μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (Fr : ∀ v, LocFrame D hk G (B v) (f v) (μsec v)) (x : D.what₂.Tau → LocalDataRealPlace D) (l : D.what₂.Tau → Fin (k0 + 1))
    (R : ∀ v (j : ℕ) (hj : j ≤ D.R.rS), ℂ → Matrix (Fin 2) (Fin 2) (GramWordSpace.lev (Fr v).B' (Fr v).μ' j hj).POp)
    (Th : ∀ v (j : ℕ) (_ : j ≤ D.R.rS) (w : TopsChoicePartA.Word), TopsChoicePartA.AuxiliarySlotStates w.length → GramWordSpace.GFn (Fr v).B' → GramWordSpace.GFn (Fr v).B') :
    GramWordSpace.Dat D k0 where
  hk := hk
  B := fun v => (Fr v).B'
  μsec := fun v => (Fr v).μ'
  l := l
  a := fun v => (x v).a
  b := fun v => (x v).b
  a1 := fun v => (x v).a1
  b1 := fun v => (x v).b1
  f := fun v => (Fr v).f'
  R := R
  Th := Th

end Formalism.MainNotions.BlockEstimateWords

end

end PartDefs3

section PartN1

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

theorem hsInner_self_real {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) :
    hsInner A A = ((hsNormSq A : ℝ) : ℂ) ∧ 0 ≤ hsNormSq A := by
  have h := Complex.le_def.1 (PSDK.diag_real (ta_psdk_hsInner (Wp := Wp) (Wq := Wq)) A)
  refine ⟨?_, h.1⟩
  apply Complex.ext
  · simp [hsNormSq]
  · simp only [Complex.ofReal_im]; exact h.2.symm

theorem bcWeight_nonneg (k r : ℕ) (T T' : ℝ) (p : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' p := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => by positivity) (pow_nonneg (by linarith) _)
  · exact le_rfl

theorem beta_self {k r : ℕ} (L : LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) :
    L.beta μsec F F = (((L.beta μsec F F).re : ℝ) : ℂ) ∧ 0 ≤ (L.beta μsec F F).re := by
  have e : L.beta μsec F F = ((∫ p : (Fin r → ℂ) × ℂ, bcWeight k r (Tz k r L.z) (Tz k r L.z') p *
      hsNormSq (L.J F (bigCell k r p.1 (μsec p.2))) : ℝ) : ℂ) := by
    unfold LocBessel.beta
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only
    rw [(hsInner_self_real _).1]
    push_cast
    rfl
  rw [e]
  refine ⟨by simp, ?_⟩
  rw [Complex.ofReal_re]
  exact integral_nonneg fun p => mul_nonneg (bcWeight_nonneg _ _ _ _ _) (hsInner_self_real _).2

section Fr

variable {D : D7} {k0 : ℕ} (hk : k0 + 1 = D.R.k) {G : GramWordSpace.GramMap k0 D.R.rS} {B : D.what₂.Tau → LocBessel D.R.k D.R.rS}
    {f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp)}
    {μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (Fr : ∀ v, LocFrame D hk G (B v) (f v) (μsec v)) (x : D.what₂.Tau → LocalDataRealPlace D) (l : D.what₂.Tau → Fin (k0 + 1))
    (R : ∀ v (j : ℕ) (hj : j ≤ D.R.rS), ℂ → Matrix (Fin 2) (Fin 2) (GramWordSpace.lev (Fr v).B' (Fr v).μ' j hj).POp)
    (Th : ∀ v (j : ℕ) (_ : j ≤ D.R.rS) (w : TopsChoicePartA.Word), TopsChoicePartA.AuxiliarySlotStates w.length → GramWordSpace.GFn (Fr v).B' → GramWordSpace.GFn (Fr v).B')

theorem energy_of_frames {T T' : ℝ} {δ : D.host.E} {L : LatticeDataWithDual D} (hL : LatAx D δ L)
    (hT : ∀ v, Tz D.R.k D.R.rS (B v).z = T) (hT' : ∀ v, Tz D.R.k D.R.rS (B v).z' = T') :
    ENNReal.ofReal (c0G L (fun v => (Fr v).A) * (mkX hk Fr x l R Th).jn2.re) ≤
      jNorm2One (fun v => (B v).Wq →L[ℂ] (B v).Wp) (fun _ => hsNormSq) D.R.k D.R.rS T T' L.κ
        (fun v p => (B v).J (f v) (bigCell D.R.k D.R.rS p.1 (μsec v p.2))) := by
  have hκ : 0 < L.κ := hL.1
  have hb := fun v => beta_self (Fr v).B' (Fr v).μ' (Fr v).f'
  have hj : (mkX hk Fr x l R Th).jn2 = ((∏ v, ((Fr v).B'.beta (Fr v).μ' (Fr v).f' (Fr v).f').re : ℝ) : ℂ) := by
    unfold GramWordSpace.Dat.jn2
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun v _ => (hb v).1
  rw [hj, Complex.ofReal_re]
  unfold c0G jNorm2One
  have e : (∏ v, (Fr v).A) / L.κ ^ (D.R.rS + 1) * ∏ v, ((Fr v).B'.beta (Fr v).μ' (Fr v).f' (Fr v).f').re =
      (∏ v, (Fr v).A * ((Fr v).B'.beta (Fr v).μ' (Fr v).f' (Fr v).f').re) / L.κ ^ (D.R.rS + 1) := by
    rw [Finset.prod_mul_distrib]; ring
  rw [e, ENNReal.ofReal_div_of_pos (pow_pos hκ _), ENNReal.ofReal_pow hκ.le,
    ENNReal.ofReal_prod_of_nonneg (fun v _ => mul_nonneg (Fr v).hA.le (hb v).2)]
  refine ENNReal.div_le_div_right (Finset.prod_le_prod' fun v _ => ?_) _
  have := (Fr v).energy
  rw [hT v, hT' v] at this
  exact this

theorem xtie_of_frames {T T' : ℝ}
    (hm : ∀ v, LocMatch D T T' (x v) (B v)) :
    XTie (mkX hk Fr x l R Th) x T T' (fun v => ‖(B v).c‖ / 2) := by
  refine ⟨fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  · show Tz (k0 + 1) D.R.rS (Fr v).B'.z = _
    rw [(Fr v).hT, (hm v).2.2.2.1]
  · show Tz (k0 + 1) D.R.rS (Fr v).B'.z' = _
    rw [(Fr v).hT', (hm v).2.2.2.2.1]
  · funext s
    show (Fr v).B'.lam (Fin.cast _ s) = _
    rw [(Fr v).hlam, ← (hm v).1]
    rfl
  · funext s
    show (Fr v).B'.u (Fin.cast _ s) = _
    rw [(Fr v).hu, ← (hm v).2.1]
    rfl
  · funext s
    show (Fr v).B'.u' (Fin.cast _ s) = _
    rw [(Fr v).hu', ← (hm v).2.2.1]
    rfl

end Fr

end Formalism.MainNotions.BlockEstimateWords

end

end PartN1

section PartN2

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

theorem il_cast {k k' n n' : ℕ} (hk : k' = k) (hn : n' = n) (hkn : k ≤ n) (hkn' : k' ≤ n') {u : Fin k → ℝ} {lam : Fin n → ℝ}
    {u' : Fin k' → ℝ} {lam' : Fin n' → ℝ} (hu : ∀ i, u' i = u (Fin.cast hk i)) (hl : ∀ i, lam' i = lam (Fin.cast hn i))
    (h : InterlaceS hkn u lam) : InterlaceS hkn' u' lam' := by
  subst hk; subst hn
  have e1 : u' = u := funext hu
  have e2 : lam' = lam := funext hl
  subst e1; subst e2
  exact h

theorem gap_cast {n n' : ℕ} (hn : n' = n) {ε : Fin n → Bool} {lam : Fin n → ℝ} {ε' : Fin n' → Bool} {lam' : Fin n' → ℝ}
    (he : ∀ i, ε' i = ε (Fin.cast hn i)) (hl : ∀ i, lam' i = lam (Fin.cast hn i)) {h h' : ℝ} (hh : h' ≤ h)
    (H : GapAtLeast ε lam h) : GapAtLeast ε' lam' h' := by
  subst hn
  have e1 : ε' = ε := funext he
  have e2 : lam' = lam := funext hl
  subst e1; subst e2
  exact fun a b hab => le_trans hh (H a b hab)

theorem cut_cast {k k' : ℕ} (hk : k' = k) {u w : Fin k → ℝ} {u' w' : Fin k' → ℝ} (hu : ∀ i, u' i = u (Fin.cast hk i))
    (hw : ∀ i, w' i = w (Fin.cast hk i)) {a b : ℝ} (hab : a ≤ b) (h : IsCutS u w (Set.Icc a b)) :
    IsCutS u' w' (Set.Icc a b) ∧ ∃ l : Fin k', u' l ≠ w' l ∧ min (-u' l) (-w' l) + 2 ≤ a ∧ b ≤ max (-u' l) (-w' l) - 2 := by
  subst hk
  have e1 : u' = u := funext hu
  have e2 : w' = w := funext hw
  subst e1; subst e2
  refine ⟨h, ?_⟩
  obtain ⟨l, a', b', hne, hab', hI, hmin, hmax, hd⟩ := h
  obtain ⟨rfl, rfl⟩ := (Set.Icc_eq_Icc_iff hab).1 hI
  refine ⟨l, hne, ?_, ?_⟩
  · obtain ⟨d1, d2⟩ := hd a (Set.left_mem_Icc.2 hab)
    rcases le_total (-u' l) (-w' l) with hle | hle
    · rw [min_eq_left hle] at hmin ⊢
      rw [abs_of_pos (by linarith)] at d1
      linarith
    · rw [min_eq_right hle] at hmin ⊢
      rw [abs_of_pos (by linarith)] at d2
      linarith
  · obtain ⟨d1, d2⟩ := hd b (Set.right_mem_Icc.2 hab)
    rcases le_total (-u' l) (-w' l) with hle | hle
    · rw [max_eq_right hle] at hmax ⊢
      rw [abs_of_neg (by linarith)] at d2
      linarith
    · rw [max_eq_left hle] at hmax ⊢
      rw [abs_of_neg (by linarith)] at d1
      linarith

theorem NN_cast (D : D7) (Ks : ℕ) : ((GramWordSpace.NN D Ks : ℕ) : ℝ) = Nlet D Ks := by
  unfold GramWordSpace.NN Nlet; push_cast; ring

theorem std_of_frames {D : D7} {k0 : ℕ} (hk : k0 + 1 = D.R.k) {G : GramWordSpace.GramMap k0 D.R.rS} {B : D.what₂.Tau → LocBessel D.R.k D.R.rS}
    {f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp)}
    {μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (Fr : ∀ v, LocFrame D hk G (B v) (f v) (μsec v)) {x : D.what₂.Tau → LocalDataRealPlace D}
    {Ks : ℕ} {E₀ Eg C T T' : ℝ} {δ : D.host.E} {L : LatticeDataWithDual D} {Kd : KernelData D}
    (hH : ThmAHyp D C Ks δ T T' x L Kd B f μsec) (hE₀ : E₀ ≤ C) (hEg : Eg ≤ C)
    (hRad : RadOpen k0 D.R.rS) (hLet : GramWordSpace.LettersExist) :
    ∃ l R Th, (mkX hk Fr x l R Th).Std Ks E₀ Eg := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hH
  have hn : 2 * D.R.rS + (k0 + 1) + 1 = 2 * D.R.rS + D.R.k + 1 := by omega
  have hu : ∀ v i, (Fr v).B'.u i = (x v).u (Fin.cast hk i) := fun v i => by rw [(Fr v).hu, (h7 v).1.2.1]
  have hu' : ∀ v i, (Fr v).B'.u' i = (x v).u' (Fin.cast hk i) := fun v i => by rw [(Fr v).hu', (h7 v).1.2.2.1]
  have hlam : ∀ v i, (Fr v).B'.lam i = (x v).lam (Fin.cast hn i) := fun v i => by rw [(Fr v).hlam, (h7 v).1.1]
  have hε : ∀ v i, (Fr v).B'.ε i = epsSH D.R (Fin.cast hn i) := fun v i => by rw [(Fr v).hε, (h7 v).1.2.2.2.2.2]
  have hab : ∀ v, (x v).a ≤ (x v).b := fun v => by obtain ⟨e1, e2, e3, _⟩ := h12 v; linarith
  have hcut := fun v => cut_cast hk (hu v) (hu' v) (hab v) (h11 v)
  choose l hl using fun v => (hcut v).2
  choose R hR using fun v => hRad (Fr v).B' (Fr v).μ' (Fr v).hsec
  have hStd : ∀ v, (GramWordSpace.levOf (Fr v).B' (Fr v).μ').Std := fun v =>
    ⟨(Fr v).B'.hz.1, (Fr v).B'.hz'.1, (Fr v).B'.hz.2, (Fr v).B'.hz'.2, (Fr v).hsec⟩
  choose Th hTh using fun v => hLet k0 D.R.rS (Fr v).B' (Fr v).μ' (hStd v)
  have hil := fun v => il_cast hk hn (k_le_nS D) (by omega) (hu v) (hlam v) (h8 v).1
  have hil' := fun v => il_cast hk hn (k_le_nS D) (by omega) (hu' v) (hlam v) (h8 v).2
  have hN0 : 0 ≤ Nlet D Ks := by unfold Nlet; positivity
  refine ⟨l, R, Th, h1, fun v => ⟨hε v, (Fr v).hc, (Fr v).hsec, (hcut v).1, ⟨(hl v).1, (hl v).2.1, hab v, (hl v).2.2⟩, ?_,
    Set.Icc_subset_Icc (h12 v).1 (h12 v).2.2.1, (h12 v).2.1, ?_, hil v, hil' v, ?_, ?_, (Fr v).hf, hR v, hTh v⟩⟩
  · refine ⟨fun j => (Fr v).B'.lam ⟨j.val, by omega⟩, fun j => ?_, fun j => ?_⟩
    · exact (hil v).1 j.val (by omega)
    · exact (hil' v).1 j.val (by omega)
  · rw [NN_cast]; exact (h12 v).2.2.2
  · rw [NN_cast]
    refine le_trans (mul_le_mul_of_nonneg_right hE₀ ?_) (h13 v)
    positivity
  · rw [NN_cast]
    refine gap_cast hn (hε v) (hlam v) ?_ (h10 v)
    have : 0 ≤ (D.R.m : ℝ) ^ ((9 : ℝ) / 2) * (Nlet D Ks * (D.R.r : ℝ) ^ 2 + (D.R.r : ℝ) ^ 3) := by positivity
    calc Eg * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) * (Nlet D Ks * (D.R.r : ℝ) ^ 2 + (D.R.r : ℝ) ^ 3)
        = Eg * ((D.R.m : ℝ) ^ ((9 : ℝ) / 2) * (Nlet D Ks * (D.R.r : ℝ) ^ 2 + (D.R.r : ℝ) ^ 3)) := by ring
      _ ≤ C * ((D.R.m : ℝ) ^ ((9 : ℝ) / 2) * (Nlet D Ks * (D.R.r : ℝ) ^ 2 + (D.R.r : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_right hEg this
      _ = _ := by ring

end Formalism.MainNotions.BlockEstimateWords

end

end PartN2

section PartNum0

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

theorem nm_kaV_pos {D : D7} {δ : D.host.E} (hδ : δ ≠ 0) (v : D.what₂.Tau) : 0 < kaV D δ v :=
  div_pos (by positivity) (norm_pos_iff.2 ((map_ne_zero (plEmb D v)).2 hδ))

theorem nm_rho {D : D7} {L : LatticeDataWithDual D} {ϱ : ℝ} (hϱ : IsFrameScale D L ϱ) {b s : ℕ} (hb : IsBlockSL2Embedding D b s) :
    L.ρ b s = ϱ ^ (2 * b + s - 3) * (ϱ ^ (2 * D.R.rS))⁻¹ := by
  rw [hϱ.2 b s hb]
  obtain ⟨h1, h2, _⟩ := hb
  have e : -((((2 * D.R.rS + 3 : ℕ) : ℤ) - 2 * (b : ℤ) - (s : ℤ))) = ((2 * b + s - 3 : ℕ) : ℤ) - ((2 * D.R.rS : ℕ) : ℤ) := by
    omega
  rw [e, zpow_sub₀ hϱ.1.ne', zpow_natCast, zpow_natCast, div_eq_mul_inv]

theorem nm_qPoly {k : ℕ} (c T T' : ℝ) (u u' : Fin k → ℝ) (Y : ℂ) :
    qPoly (c * T) (c * T') u u' Y = ((c ^ 2 : ℝ) : ℂ) * qPoly T T' u u' Y := by
  unfold qPoly; push_cast; ring

theorem nm_beS {n k : ℕ} (r : ℕ) (lam : Fin n → ℝ) (T T' : ℝ) (u u' : Fin k → ℝ) (Y : ℝ) {ka ϱ : ℝ} (hka : 0 < ka) (hϱ : 0 < ϱ) :
    beS 1 r lam ((ka / ϱ) ^ (2 * r) * T) ((ka / ϱ) ^ (2 * r) * T') u u' Y = ϱ ^ (2 * r) * ka * beS ka r lam T T' u u' Y := by
  unfold beS
  have hc : 0 < (ka / ϱ) ^ (2 * r) := pow_pos (div_pos hka hϱ) _
  generalize capP (fun s => (lam s : ℂ)) (Y : ℂ) * capP (fun s => (lam s : ℂ)) ((Y : ℂ) + 1) = A
  rw [nm_qPoly, one_zpow, one_mul]
  generalize qPoly T T' u u' (Y : ℂ) = q
  have e1 : ‖A / ((((ka / ϱ) ^ (2 * r)) ^ 2 : ℝ) * q)‖ = ‖A / q‖ / ((ka / ϱ) ^ (2 * r)) ^ 2 := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _), norm_div, div_mul_eq_div_div_swap]
  rw [e1, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hc.le]
  have e2 : (1 + 2 * (r : ℤ)) = ((1 + 2 * r : ℕ) : ℤ) := by push_cast; ring
  rw [e2, zpow_neg, zpow_natCast, div_pow]
  have h1 := pow_pos hka (2 * r)
  have h2 := pow_pos hϱ (2 * r)
  rw [pow_add, pow_one]
  field_simp

open scoped Pointwise in
theorem nm_supBe {D : D7} {k0 : ℕ} {X : GramWordSpace.Dat D k0} {x : D.what₂.Tau → LocalDataRealPlace D} {T T' : ℝ} {kap : D.what₂.Tau → ℝ}
    (hX : XTie X x T T' kap) {δ : D.host.E} (hδ : δ ≠ 0) {ϱ : ℝ} (hϱ : 0 < ϱ) (hkap : ∀ v, kap v = kaV D δ v / ϱ)
    (v : D.what₂.Tau) (J : Set ℝ) :
    supBe D 1 (X.T v) (X.T' v) (X.loc v) J = ϱ ^ (2 * D.R.rS) * kaV D δ v * supBe D (kaV D δ v) T T' (x v) J := by
  unfold supBe
  rw [hX.lam v, hX.u v, hX.u' v, hX.hT v, hX.hT' v, hkap v]
  have hka := nm_kaV_pos hδ v
  have e : (beS 1 D.R.rS (x v).lam ((kaV D δ v / ϱ) ^ (2 * D.R.rS) * T) ((kaV D δ v / ϱ) ^ (2 * D.R.rS) * T') (x v).u (x v).u') '' J =
      (ϱ ^ (2 * D.R.rS) * kaV D δ v) • ((beS (kaV D δ v) D.R.rS (x v).lam T T' (x v).u (x v).u') '' J) := by
    rw [← Set.image_smul, Set.image_image]
    refine Set.image_congr fun Y _ => ?_
    rw [nm_beS D.R.rS _ T T' _ _ Y hka hϱ, smul_eq_mul]
  rw [e, Real.sSup_smul_of_nonneg (by positivity), smul_eq_mul]

theorem nm_supBe_nonneg (D : D7) (ka T T' : ℝ) (hka : 0 ≤ ka) (x : LocalDataRealPlace D) (J : Set ℝ) : 0 ≤ supBe D ka T T' x J := by
  unfold supBe
  refine Real.sSup_nonneg ?_
  rintro y ⟨Y, _, rfl⟩
  unfold beS
  exact mul_nonneg (zpow_nonneg hka _) (Real.sqrt_nonneg _)

theorem nm_core {E₁ E₂ C S N w ka P : ℝ} (m : ℕ) (hE₁ : 0 ≤ E₁) (hE₁C : E₁ ≤ C) (hE₂ : 0 ≤ E₂) (hE₂C : E₂ ≤ C) (hS : 0 ≤ S)
    (hN : 0 ≤ N) (hw : 0 ≤ w) (hka : 0 < ka) (hP : 0 < P) :
    E₁ * (P * ka * S) * (E₂ * 1 * N / w) ^ m * (ka ^ m * P⁻¹) ≤ ka * (C * S * (C * ka * N / w) ^ m) := by
  have e : E₁ * (P * ka * S) * (E₂ * 1 * N / w) ^ m * (ka ^ m * P⁻¹) = ka * (E₁ * S * (E₂ * ka * N / w) ^ m) := by
    have : (E₂ * ka * N / w) ^ m = (E₂ * 1 * N / w) ^ m * ka ^ m := by rw [← mul_pow]; congr 1; ring
    rw [this]; field_simp
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hka.le
  have h1 : 0 ≤ E₂ * ka * N / w := by positivity
  have h2 : E₂ * ka * N / w ≤ C * ka * N / w := by
    refine div_le_div_of_nonneg_right ?_ hw
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE₂C hka.le) hN
  exact mul_le_mul (mul_le_mul_of_nonneg_right hE₁C hS) (pow_le_pow_left₀ h1 h2 m) (pow_nonneg h1 m)
    (mul_nonneg (le_trans hE₁ hE₁C) hS)

section Num

variable {D : D7} {k0 : ℕ} {X : GramWordSpace.Dat D k0} {Ks : ℕ} {E₀ Eg E₁ E₂ C T T' ϱ : ℝ} {δ : D.host.E}
    {x : D.what₂.Tau → LocalDataRealPlace D} {L : LatticeDataWithDual D} {Kd : KernelData D} {B : D.what₂.Tau → LocBessel D.R.k D.R.rS}
    {f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp)}
    {μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    {kap : D.what₂.Tau → ℝ} {av : D.what₂.Tau → ℕ → ℕ → ℂ}

theorem nm_N_pos (hH : ThmAHyp D C Ks δ T T' x L Kd B f μsec) : 0 < Nlet D Ks := by
  have hK0 : (0 : ℝ) < (Ks : ℝ) := by exact_mod_cast (by have := hH.1; omega : 0 < Ks)
  unfold Nlet; positivity

theorem nm_w_pos (hH : ThmAHyp D C Ks δ T T' x L Kd B f μsec) (hC : 0 < C) (v : D.what₂.Tau) : 0 < (x v).b - (x v).a := by
  have hN := nm_N_pos hH
  exact lt_of_lt_of_le (by positivity) (hH.2.2.2.2.2.2.2.2.2.2.2.2 v)

theorem nm_T_pos (hH : ThmAHyp D C Ks δ T T' x L Kd B f μsec) (v : D.what₂.Tau) : 0 < T ∧ 0 < T' :=
  ⟨(hH.2.2.2.2.2.2.1 v).1.2.2.2.1 ▸ (B v).hz.2, (hH.2.2.2.2.2.2.1 v).1.2.2.2.2.1 ▸ (B v).hz'.2⟩

theorem norm_aG (hL : LatAx D δ L) (hav : ∀ v i s, ‖av v i s‖ = kap v ^ (2 * i + s - 3)) {b s : ℕ} (hb : IsBlockSL2Embedding D b s)
    (v : D.what₂.Tau) : ‖aG L av b s v‖ = kap v ^ (2 * b + s - 3) * L.ρ b s := by
  have hρ := (hL.2 b s hb).1
  unfold aG
  rw [if_neg hρ.ne', norm_mul, hav, Complex.norm_real, Real.norm_of_nonneg hρ.le]

theorem nm_norm_aG (hL : LatAx D δ L) (hϱ : IsFrameScale D L ϱ) (hkap : ∀ v, kap v = kaV D δ v / ϱ)
    (hav : ∀ v i s, ‖av v i s‖ = kap v ^ (2 * i + s - 3)) {b s : ℕ} (hb : IsBlockSL2Embedding D b s) (v : D.what₂.Tau) :
    ‖aG L av b s v‖ = kaV D δ v ^ (2 * b + s - 3) * (ϱ ^ (2 * D.R.rS))⁻¹ := by
  rw [norm_aG hL hav hb, hkap, nm_rho hϱ hb, div_pow]
  have := pow_pos hϱ.1 (2 * b + s - 3)
  field_simp

variable (hH : ThmAHyp D C Ks δ T T' x L Kd B f μsec) (hX : XTie X x T T' kap)
    (hϱ : IsFrameScale D L ϱ) (hkap : ∀ v, kap v = kaV D δ v / ϱ)
    (hav : ∀ v i s, ‖av v i s‖ = kap v ^ (2 * i + s - 3))
    (hE₁ : 0 < E₁) (hE₁C : E₁ ≤ C) (hE₂ : 0 < E₂) (hE₂C : E₂ ≤ C)

include hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C

theorem xi_le {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ D.R.rS + 1) (v : D.what₂.Tau) :
    X.xi E₁ E₂ Ks i v * ‖aG L av i 1 v‖ ≤ kaV D δ v * szX D C C (Nlet D Ks) T T' δ x i v := by
  have hδ : δ ≠ 0 := hH.2.2.1.1
  have hC : 0 < C := lt_of_lt_of_le hE₁ hE₁C
  rw [nm_norm_aG hH.2.2.2.1 hϱ hkap hav ⟨hi1, le_rfl, by omega⟩ v]
  show E₁ * supBe D 1 (X.T v) (X.T' v) (X.loc v) (if i = 1 then Set.Icc (X.a1 v) (X.b1 v) else Set.Icc (X.a v) (X.b v)) *
      (E₂ * 1 * ((GramWordSpace.NN D Ks : ℕ) : ℝ) / (X.b v - X.a v)) ^ (2 * i - 2) * _ ≤
    kaV D δ v * (C * supBe D (kaV D δ v) T T' (x v) (if i = 1 then Set.Icc (x v).a1 (x v).b1 else Set.Icc (x v).a (x v).b) *
      (C * kaV D δ v * Nlet D Ks / ((x v).b - (x v).a)) ^ (2 * i - 2))
  rw [hX.a, hX.b, hX.a1, hX.b1, NN_cast, nm_supBe hX hδ hϱ.1 hkap, (by omega : 2 * i + 1 - 3 = 2 * i - 2)]
  exact nm_core _ hE₁.le hE₁C hE₂.le hE₂C (nm_supBe_nonneg D _ T T' (nm_kaV_pos hδ v).le _ _) (nm_N_pos hH).le
    (nm_w_pos hH hC v).le (nm_kaV_pos hδ v) (pow_pos hϱ.1 _)

theorem lam_le {b s : ℕ} (hb : IsBlockSL2Embedding D b s) (v : D.what₂.Tau) :
    X.abelian₂ E₁ E₂ Ks s b v * ‖aG L av b s v‖ ≤ kaV D δ v * szL D C C (Nlet D Ks) T T' δ x b s v := by
  have hδ : δ ≠ 0 := hH.2.2.1.1
  have hC : 0 < C := lt_of_lt_of_le hE₁ hE₁C
  rw [nm_norm_aG hH.2.2.2.1 hϱ hkap hav hb v]
  show E₁ * supBe D 1 (X.T v) (X.T' v) (X.loc v) (Set.Icc (X.a v) (X.b v)) *
      (E₂ * 1 * ((GramWordSpace.NN D Ks : ℕ) : ℝ) / (X.b v - X.a v)) ^ (2 * (b - 1) + s - 1) * _ ≤
    kaV D δ v * (C * supBe D (kaV D δ v) T T' (x v) (Set.Icc (x v).a (x v).b) *
      (C * kaV D δ v * Nlet D Ks / ((x v).b - (x v).a)) ^ (2 * (b - 1) + s - 1))
  obtain ⟨hb1, hb2, _⟩ := hb
  rw [hX.a, hX.b, NN_cast, nm_supBe hX hδ hϱ.1 hkap, (by omega : 2 * b + s - 3 = 2 * (b - 1) + s - 1)]
  exact nm_core _ hE₁.le hE₁C hE₂.le hE₂C (nm_supBe_nonneg D _ T T' (nm_kaV_pos hδ v).le _ _) (nm_N_pos hH).le
    (nm_w_pos hH hC v).le (nm_kaV_pos hδ v) (pow_pos hϱ.1 _)

theorem lam_next_le {b s : ℕ} (hb : IsBlockSL2Embedding D b (s + 1)) (hs : 1 ≤ s) (v : D.what₂.Tau) :
    X.abelian₂ E₁ E₂ Ks (s + 1) b v * ‖aG L av b s v‖ ≤ szL D C C (Nlet D Ks) T T' δ x b (s + 1) v := by
  have hδ : δ ≠ 0 := hH.2.2.1.1
  have hka := nm_kaV_pos hδ v
  have h := lam_le hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C hb v
  have hb' : IsBlockSL2Embedding D b s := ⟨hb.1, hs, by have := hb.2.2; omega⟩
  have e : ‖aG L av b (s + 1) v‖ = kaV D δ v * ‖aG L av b s v‖ := by
    rw [nm_norm_aG hH.2.2.2.1 hϱ hkap hav hb v, nm_norm_aG hH.2.2.2.1 hϱ hkap hav hb' v,
      (by have := hb.1; omega : 2 * b + (s + 1) - 3 = (2 * b + s - 3) + 1), pow_succ]
    ring
  rw [e] at h
  have h2 : kaV D δ v * (X.abelian₂ E₁ E₂ Ks (s + 1) b v * ‖aG L av b s v‖) ≤ kaV D δ v * szL D C C (Nlet D Ks) T T' δ x b (s + 1) v := by
    calc _ = X.abelian₂ E₁ E₂ Ks (s + 1) b v * (kaV D δ v * ‖aG L av b s v‖) := by ring
      _ ≤ _ := h
  exact le_of_mul_le_mul_left h2 hka

end Num

end Formalism.MainNotions.BlockEstimateWords

end

end PartNum0

section PartNum1

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

theorem nm_rpow {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) {T T' : ℝ} (h : T * T' = t) :
    (c * T * (c * T')) ^ (-(1 / 2 : ℝ)) = c⁻¹ * (T * T') ^ (-(1 / 2 : ℝ)) := by
  have e : c * T * (c * T') = c ^ 2 * (T * T') := by ring
  rw [e, h, Real.mul_rpow (sq_nonneg _) ht, Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq hc.le]

section Num1

variable {D : D7} {k0 : ℕ} {X : GramWordSpace.Dat D k0} {Ks : ℕ} {E₀ Eg E₁ E₂ C T T' ϱ : ℝ} {δ : D.host.E}
    {x : D.what₂.Tau → LocalDataRealPlace D} {L : LatticeDataWithDual D} {Kd : KernelData D} {B : D.what₂.Tau → LocBessel D.R.k D.R.rS}
    {f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp)}
    {μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    {kap : D.what₂.Tau → ℝ} {av : D.what₂.Tau → ℕ → ℕ → ℂ}
    (hH : ThmAHyp D C Ks δ T T' x L Kd B f μsec) (hX : XTie X x T T' kap)
    (hϱ : IsFrameScale D L ϱ) (hkap : ∀ v, kap v = kaV D δ v / ϱ)
    (hav : ∀ v i s, ‖av v i s‖ = kap v ^ (2 * i + s - 3))
    (hE₁ : 0 < E₁) (hE₁C : E₁ ≤ C) (hE₂ : 0 < E₂) (hE₂C : E₂ ≤ C)

include hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C

theorem lambdaWeight_mul_norm_le_size {b s : ℕ} (hb : IsBlockSL2Embedding D b s) (htop : b - 1 + s = D.R.rS + 1) (v : D.what₂.Tau) :
    X.LamP E₁ E₂ Ks b v * ‖aG L av b s v‖ ≤ szP D C C (Nlet D Ks) T T' δ x b v := by
  have hδ : δ ≠ 0 := hH.2.2.1.1
  have hC : 0 < C := lt_of_lt_of_le hE₁ hE₁C
  have hka := nm_kaV_pos hδ v
  have hP := pow_pos hϱ.1 (2 * D.R.rS)
  obtain ⟨hT, hT'⟩ := nm_T_pos hH v
  have hS := nm_supBe_nonneg D _ T T' hka.le (x v) (Set.Icc (x v).a (x v).b)
  have hN := (nm_N_pos hH).le
  have hw := (nm_w_pos hH hC v).le
  have hτ : 0 ≤ (T * T') ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (mul_pos hT hT').le _
  rw [nm_norm_aG hH.2.2.2.1 hϱ hkap hav hb v]
  show Real.sqrt (E₁ * supBe D 1 (X.T v) (X.T' v) (X.loc v) (Set.Icc (X.a v) (X.b v)) * 1 ^ (2 * b - 1) *
      (X.T v * X.T' v) ^ (-(1 / 2 : ℝ)) * (E₂ * ((GramWordSpace.NN D Ks : ℕ) : ℝ) / (X.b v - X.a v)) ^ (2 * (b - 1))) * _ ≤
    Real.sqrt (C * supBe D (kaV D δ v) T T' (x v) (Set.Icc (x v).a (x v).b) * kaV D δ v ^ (2 * b - 1) *
      (T * T') ^ (-(1 / 2 : ℝ)) * (C * Nlet D Ks / ((x v).b - (x v).a)) ^ (2 * (b - 1)))
  rw [hX.a, hX.b, NN_cast, nm_supBe hX hδ hϱ.1 hkap, hX.hT, hX.hT', hkap,
    nm_rpow (pow_pos (div_pos hka hϱ.1) _) (mul_pos hT hT').le rfl, one_pow, div_pow]
  set S := supBe D (kaV D δ v) T T' (x v) (Set.Icc (x v).a (x v).b)
  set τ := (T * T') ^ (-(1 / 2 : ℝ))
  set ka := kaV D δ v
  set P := ϱ ^ (2 * D.R.rS)
  set n := 2 * b + s - 3
  have hg : 0 ≤ ka ^ n * P⁻¹ := by positivity
  have h1 : 0 ≤ E₂ * Nlet D Ks / ((x v).b - (x v).a) := by positivity
  have h2 : E₂ * Nlet D Ks / ((x v).b - (x v).a) ≤ C * Nlet D Ks / ((x v).b - (x v).a) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hE₂C hN) hw
  conv_lhs => rw [← Real.sqrt_sq hg]
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  have hpow : ka * (ka ^ n) ^ 2 = ka ^ (2 * b - 1) * ka ^ (2 * D.R.rS) := by
    rw [← pow_mul, ← pow_succ', ← pow_add]
    congr 1
    have := hb.1
    omega
  have e : E₁ * (P * ka * S) * 1 * ((ka ^ (2 * D.R.rS) / P)⁻¹ * τ) * (E₂ * Nlet D Ks / ((x v).b - (x v).a)) ^ (2 * (b - 1)) *
      (ka ^ n * P⁻¹) ^ 2 = E₁ * S * ka ^ (2 * b - 1) * τ * (E₂ * Nlet D Ks / ((x v).b - (x v).a)) ^ (2 * (b - 1)) := by
    have h3 := pow_pos hka (2 * D.R.rS)
    have : P * ka * (ka ^ (2 * D.R.rS) / P)⁻¹ * (ka ^ n * P⁻¹) ^ 2 = ka ^ (2 * b - 1) := by
      rw [mul_pow, inv_div]
      calc P * ka * (P / ka ^ (2 * D.R.rS)) * ((ka ^ n) ^ 2 * P⁻¹ ^ 2) = (ka * (ka ^ n) ^ 2) / ka ^ (2 * D.R.rS) := by
            field_simp
        _ = _ := by rw [hpow]; field_simp
    calc _ = E₁ * S * (P * ka * (ka ^ (2 * D.R.rS) / P)⁻¹ * (ka ^ n * P⁻¹) ^ 2) * τ *
          (E₂ * Nlet D Ks / ((x v).b - (x v).a)) ^ (2 * (b - 1)) := by ring
      _ = _ := by rw [this]
  rw [e]
  have h4 : 0 ≤ ka ^ (2 * b - 1) := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE₁C hS) h4) hτ)
    (pow_le_pow_left₀ h1 h2 _) (pow_nonneg h1 _) (by positivity)

theorem nm_base_nonneg (v : D.what₂.Tau) : 0 ≤ E₂ * 1 * ((GramWordSpace.NN D Ks : ℕ) : ℝ) / (X.b v - X.a v) := by
  have hC : 0 < C := lt_of_lt_of_le hE₁ hE₁C
  have := (nm_w_pos hH hC v).le
  rw [hX.a, hX.b]
  positivity

theorem nm_xi_nonneg (i : ℕ) (v : D.what₂.Tau) : 0 ≤ X.xi E₁ E₂ Ks i v :=
  mul_nonneg (mul_nonneg hE₁.le (nm_supBe_nonneg D 1 _ _ zero_le_one _ _))
    (pow_nonneg (nm_base_nonneg hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C v) _)

theorem nm_lam_nonneg (s b : ℕ) (v : D.what₂.Tau) : 0 ≤ X.abelian₂ E₁ E₂ Ks s b v :=
  mul_nonneg (mul_nonneg hE₁.le (nm_supBe_nonneg D 1 _ _ zero_le_one _ _))
    (pow_nonneg (nm_base_nonneg hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C v) _)

theorem block_size_nonneg (j0 s : ℕ) (v : D.what₂.Tau) : 0 ≤ GramWordSpace.blockLiftThreshold X E₁ E₂ Ks j0 s v := by
  unfold GramWordSpace.blockLiftThreshold
  split_ifs
  · exact nm_lam_nonneg hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C _ _ v
  · exact mul_nonneg zero_le_two (Real.sqrt_nonneg _)

theorem norm_le_third_threshold (i s : ℕ) (v : D.what₂.Tau) (hs : 1 ≤ s) (hsi : s ≤ i) (hi : i ≤ D.R.rS + 1) (hns : ¬ (i = D.R.rS + 1 ∧ s = 1)) :
    GramWordSpace.blockLiftThreshold X E₁ E₂ Ks (i - s) s v * ‖aG L av (i - s + 1) s v‖ ≤ thr3 D C C (Nlet D Ks) T T' δ x i s v := by
  unfold GramWordSpace.blockLiftThreshold thr3
  rw [Nat.sub_add_cancel hsi]
  by_cases h : i ≤ D.R.rS
  · rw [if_pos h, if_pos h]
    exact lam_next_le hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C ⟨by omega, by omega, by omega⟩ hs v
  · rw [if_neg h, if_neg h, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (lambdaWeight_mul_norm_le_size hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C ⟨by omega, hs, by omega⟩ (by omega) v) zero_le_two

end Num1

end Formalism.MainNotions.BlockEstimateWords

end

end PartNum1

section PartNum2

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

theorem nm_expo (c t : ℕ) : ∑ l ∈ Finset.Ico (c + 1) (c + 1 + (t + 1)), 4 * (l - 1) =
    (t + 1) * t + 2 * (2 * c + t) + ∑ s' ∈ Finset.Ico 1 (t + 1), 2 * (2 * (c + 1) + s' - 3) := by
  induction t with
  | zero =>
    rw [show c + 1 + (0 + 1) = (c + 1) + 1 from rfl, Finset.sum_Ico_succ_top (le_refl _), Finset.Ico_self, Finset.sum_empty]
    simp <;> ring
  | succ t ih =>
    rw [show c + 1 + (t + 1 + 1) = (c + 1 + (t + 1)) + 1 from rfl, Finset.sum_Ico_succ_top (by omega), ih,
      Finset.sum_Ico_succ_top (by omega : 1 ≤ t + 1)]
    have e1 : c + 1 + (t + 1) - 1 = c + t + 1 := by omega
    have e2 : 2 * (c + 1) + (t + 1) - 3 = 2 * c + t := by omega
    rw [e1, e2]; ring

theorem nm_cblk {κ : ℝ} (hκ : 0 < κ) {b s : ℕ} (hb : 1 ≤ b) (hs : 1 ≤ s) :
    cblk κ b s = (κ ^ (2 * b + s - 3)) ^ 2 * ∏ s' ∈ Finset.Ico 1 s, (κ ^ (2 * b + s' - 3)) ^ 2 := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have R : ∏ s' ∈ Finset.Ico 1 (t + 1), (κ ^ (2 * (c + 1) + s' - 3)) ^ 2 =
      κ ^ (∑ s' ∈ Finset.Ico 1 (t + 1), 2 * (2 * (c + 1) + s' - 3)) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun _ _ => by rw [← pow_mul, mul_comm]
  unfold cblk
  rw [R, Finset.prod_pow_eq_pow_sum, nm_expo, Nat.add_sub_cancel, (by omega : 2 * (c + 1) + (t + 1) - 3 = 2 * c + t),
    pow_add, pow_add, ← pow_mul, mul_comm (2 * c + t) 2]
  have := pow_pos hκ ((t + 1) * t)
  field_simp

theorem nm_alg {A K2 R KA SZ Nn κ Pi : ℝ} (hR : 0 < R) (hN : 0 < Nn) (hκ : 0 ≤ κ) (hSZ : 0 ≤ SZ) (h1 : A * K2 * R ≤ KA * SZ)
    (h2 : κ * (KA / R) * Nn ≤ Pi) : A * (κ * K2) ≤ Pi * (SZ / Nn) := by
  calc A * (κ * K2) = κ * (A * K2 * R) / R := by field_simp
    _ ≤ κ * (KA * SZ) / R := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hκ) hR.le
    _ = (κ * (KA / R) * Nn) * (SZ / Nn) := by field_simp
    _ ≤ Pi * (SZ / Nn) := mul_le_mul_of_nonneg_right h2 (div_nonneg hSZ hN.le)

theorem nm_nrmHalf_sq (D : D7) (aa : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    nrmHalf D aa ^ 2 = ((FractionalIdeal.absNorm aa : ℚ) : ℝ) := by
  unfold nrmHalf
  exact Real.sq_sqrt (by exact_mod_cast FractionalIdeal.absNorm_nonneg aa)

section Num2

variable {D : D7} {k0 : ℕ} {X : GramWordSpace.Dat D k0} {Ks : ℕ} {E₀ Eg E₁ E₂ C T T' ϱ : ℝ} {δ : D.host.E}
    {x : D.what₂.Tau → LocalDataRealPlace D} {L : LatticeDataWithDual D} {Kd : KernelData D} {B : D.what₂.Tau → LocBessel D.R.k D.R.rS}
    {f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp)}
    {μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    {kap : D.what₂.Tau → ℝ} {av : D.what₂.Tau → ℕ → ℕ → ℂ}
    (hH : ThmAHyp D C Ks δ T T' x L Kd B f μsec) (hX : XTie X x T T' kap)
    (hϱ : IsFrameScale D L ϱ) (hkap : ∀ v, kap v = kaV D δ v / ϱ)
    (hav : ∀ v i s, ‖av v i s‖ = kap v ^ (2 * i + s - 3))
    (hE₁ : 0 < E₁) (hE₁C : E₁ ≤ C) (hE₂ : 0 < E₂) (hE₂C : E₂ ≤ C)

include hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C

theorem nm_aG_pos {b s : ℕ} (hb : IsBlockSL2Embedding D b s) (v : D.what₂.Tau) : 0 < ‖aG L av b s v‖ := by
  rw [nm_norm_aG hH.2.2.2.1 hϱ hkap hav hb v]
  have := nm_kaV_pos hH.2.2.1.1 v
  have := hϱ.1
  positivity

theorem nm_norm_aDual {b s : ℕ} (hb : IsBlockSL2Embedding D b s) (v : D.what₂.Tau) :
    ‖aDual (aG L av) δ b s v‖ = kaV D δ v / ‖aG L av b s v‖ := by
  unfold aDual kaV
  rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have : ‖(2 : ℂ)‖ = 2 := by simp
  rw [this, mul_one, div_div]

theorem block_product_le_sqrt_norm (hΘ : 1 ≤ ThS D C C (Nlet D Ks) T T' δ x L) {b s : ℕ} (hs : 2 ≤ s) (hb : IsBlockSL2Embedding D b s) :
    ∏ v, X.abelian₂ E₁ E₂ Ks s b v ≤ Real.sqrt (GramWordSpace.scNorm D (aDual (aG L av) δ b s) (L.aaV b s)) := by
  have hC : 0 < C := lt_of_lt_of_le hE₁ hE₁C
  have hOK := szOK_of_LatAx hH.2.2.1.1 hH.2.2.2.1 (szPos_of_ThmAHyp hC hH)
  have h1 : ∏ v, szL D C C (Nlet D Ks) T T' δ x b s v ≤ nrmHalf D (L.aaV b s) :=
    local_size_product_le_half_norm D C C (Nlet D Ks) T T' δ x L b s hb.1 hs hb.2.2 (hOK.aaV_ne b s hb)
      (hOK.aaP_ne b (s - 1) ⟨hb.1, by omega, by have := hb.2.2; omega⟩) (fun v => hOK.l_pos b s v) hΘ
  have e : Real.sqrt (GramWordSpace.scNorm D (aDual (aG L av) δ b s) (L.aaV b s)) =
      nrmHalf D (L.aaV b s) * ∏ v, ‖aDual (aG L av) δ b s v‖ := by
    unfold GramWordSpace.scNorm nrmHalf
    rw [Real.sqrt_mul (by exact_mod_cast FractionalIdeal.absNorm_nonneg _), Finset.prod_pow,
      Real.sqrt_sq (Finset.prod_nonneg fun v _ => norm_nonneg _)]
  rw [e]
  calc ∏ v, X.abelian₂ E₁ E₂ Ks s b v ≤ ∏ v, (szL D C C (Nlet D Ks) T T' δ x b s v * ‖aDual (aG L av) δ b s v‖) := by
        refine Finset.prod_le_prod (fun v _ => nm_lam_nonneg hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C _ _ v) fun v _ => ?_
        rw [nm_norm_aDual hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C hb v, mul_div_assoc', le_div_iff₀
          (nm_aG_pos hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C hb v), mul_comm (szL D C C (Nlet D Ks) T T' δ x b s v)]
        exact lam_le hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C hb v
    _ = (∏ v, szL D C C (Nlet D Ks) T T' δ x b s v) * ∏ v, ‖aDual (aG L av) δ b s v‖ := Finset.prod_mul_distrib
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 (Finset.prod_nonneg fun v _ => norm_nonneg _)

theorem nm_lamG_le {b s : ℕ} (hb : IsBlockSL2Embedding D b s) (v : D.what₂.Tau) :
    0 ≤ X.LamG E₁ E₂ Ks s b v ∧
    X.LamG E₁ E₂ Ks s b v * ‖aG L av b s v‖ ≤ kaV D δ v * szG D C C (Nlet D Ks) T T' δ x b s v := by
  unfold GramWordSpace.Dat.LamG szG
  by_cases h : s = 1
  · subst h
    rw [if_pos rfl, if_pos rfl]
    exact ⟨nm_xi_nonneg hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C _ v,
      xi_le hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C hb.1 (by have := hb.2.2; omega) v⟩
  · rw [if_neg h, if_neg h]
    exact ⟨nm_lam_nonneg hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C _ _ v, lam_le hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C hb v⟩

theorem nm_claim1 (hDD : DualDensity D δ L) {b s : ℕ} (hb : IsBlockSL2Embedding D b s) :
    (∏ v, X.LamG E₁ E₂ Ks s b v ^ 2) * (L.κ * ∏ v, (kap v ^ (2 * b + s - 3)) ^ 2) ≤
      Real.pi ^ (2 * D.R.f) * volB D C C (Nlet D Ks) T T' δ x L b s := by
  have hC : 0 < C := lt_of_lt_of_le hE₁ hE₁C
  have hL := hH.2.2.2.1
  have hOK := szOK_of_LatAx hH.2.2.1.1 hL (szPos_of_ThmAHyp hC hH)
  have hρ := (hL.2 b s hb).1
  have hN : 0 < ((FractionalIdeal.absNorm (L.aaV b s) : ℚ) : ℝ) := by
    rw [← nm_nrmHalf_sq]; exact pow_pos (nrmHalf_pos D _ (hOK.aaV_ne b s hb)) 2
  unfold volB
  rw [nm_nrmHalf_sq]
  refine nm_alg (R := ∏ _v : D.what₂.Tau, L.ρ b s ^ 2) (KA := ∏ v, kaV D δ v ^ 2)
    (Finset.prod_pos fun _ _ => pow_pos hρ 2) hN hL.1.le (sq_nonneg _) ?_ ?_
  · rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun v _ => by positivity) fun v _ => ?_
    obtain ⟨g0, g1⟩ := nm_lamG_le hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C hb v
    rw [norm_aG hL hav hb v] at g1
    have hk0 : 0 ≤ kap v ^ (2 * b + s - 3) * L.ρ b s := by
      rw [← norm_aG hL hav hb v]; exact norm_nonneg _
    calc X.LamG E₁ E₂ Ks s b v ^ 2 * (kap v ^ (2 * b + s - 3)) ^ 2 * L.ρ b s ^ 2
        = (X.LamG E₁ E₂ Ks s b v * (kap v ^ (2 * b + s - 3) * L.ρ b s)) ^ 2 := by ring
      _ ≤ (kaV D δ v * szG D C C (Nlet D Ks) T T' δ x b s v) ^ 2 := pow_le_pow_left₀ (mul_nonneg g0 hk0) g1 2
      _ = _ := by ring
  · have := hDD b s hb
    rwa [show (∏ v, (kaV D δ v / L.ρ b s) ^ 2) = (∏ v, kaV D δ v ^ 2) / ∏ _v : D.what₂.Tau, L.ρ b s ^ 2 by
      rw [← Finset.prod_div_distrib]; exact Finset.prod_congr rfl fun v _ => div_pow _ _ _] at this

end Num2

end Formalism.MainNotions.BlockEstimateWords

end

end PartNum2

section PartNum3

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

theorem add_ne_zero_of_mem_Icc {k0 n : ℕ} (hkn : k0 + 1 ≤ n) {lam : Fin n → ℝ} (hl : StrictAnti lam) {u u' : Fin (k0 + 1) → ℝ}
    (h1 : InterlaceS hkn u lam) (h2 : InterlaceS hkn u' lam) (l : Fin (k0 + 1)) {a b Y : ℝ}
    (ha : min (-u l) (-u' l) + 2 ≤ a) (hb : b ≤ max (-u l) (-u' l) - 2) (hY : Y ∈ Set.Icc a b) (s : Fin n) :
    Y + lam s ≠ 0 := by
  intro h0
  have hl2 := l.2
  by_cases hs : s.val < l.val
  · have hi : (l.val - 1) + 1 < k0 + 1 := by omega
    have e : (⟨l.val - 1 + 1, hi⟩ : Fin (k0 + 1)) = l := Fin.ext (by show l.val - 1 + 1 = l.val; omega)
    have a1 := (h1.1 (l.val - 1) hi).2
    have a2 := (h2.1 (l.val - 1) hi).2
    rw [e] at a1 a2
    have a3 : lam ⟨l.val - 1, by omega⟩ ≤ lam s := hl.antitone (Fin.le_def.2 (by show s.val ≤ l.val - 1; omega))
    have : Y < min (-u l) (-u' l) := lt_min (by linarith) (by linarith)
    linarith [hY.1]
  · obtain ⟨m, hm, c1, c2⟩ : ∃ m : Fin n, m.val = l.val ∧ lam m < u l ∧ lam m < u' l := by
      by_cases hl1 : l.val + 1 < k0 + 1
      · exact ⟨⟨l.val, by omega⟩, rfl, (h1.1 l.val hl1).1, (h2.1 l.val hl1).1⟩
      · have e : (⟨k0 + 1 - 1, by omega⟩ : Fin (k0 + 1)) = l := Fin.ext (by show k0 + 1 - 1 = l.val; omega)
        refine ⟨⟨k0 + 1 - 1, by omega⟩, by show k0 + 1 - 1 = l.val; omega, ?_, ?_⟩
        · have := h1.2 (Nat.succ_pos _); rwa [e] at this
        · have := h2.2 (Nat.succ_pos _); rwa [e] at this
    have b3 : lam s ≤ lam m := hl.antitone (Fin.le_def.2 (by omega))
    have : max (-u l) (-u' l) < Y := max_lt (by linarith) (by linarith)
    linarith [hY.2]

theorem nm_brk_pos {D : D7} {k0 : ℕ} {X : GramWordSpace.Dat D k0} {Ks : ℕ} {E₀ Eg : ℝ} (hstd : X.Std Ks E₀ Eg) (w : GramWordSpace.GWord D)
    (hw : X.admitted w) : 0 < X.brk w := by
  unfold GramWordSpace.Dat.brk
  refine Finset.prod_pos fun v _ => ?_
  unfold brkW
  refine List.prod_pos ?_
  intro y hy
  simp at hy
  obtain ⟨Y, hY, rfl⟩ := hy
  obtain ⟨lt, hlt, rfl⟩ : ∃ lt ∈ w v, lt.2 = Y := by
    rcases hY with h | h
    · exact ⟨_, h, rfl⟩
    · exact ⟨_, h, rfl⟩
  obtain ⟨_, _, _, _, ⟨_, c2, _, c4⟩, _, _, _, _, i1, i2, _⟩ := hstd.2 v
  rw [norm_pos_iff]
  unfold capP
  refine Finset.prod_ne_zero_iff.2 fun s _ => ?_
  have := add_ne_zero_of_mem_Icc _ (X.B v).hlam.1 i1 i2 (X.l v) c2 c4 ((hw v).1 lt hlt) s
  show ((lt.2 : ℝ) : ℂ) + (((X.B v).lam s : ℝ) : ℂ) ≠ 0
  exact_mod_cast this

section Num3

variable {D : D7} {k0 : ℕ} {X : GramWordSpace.Dat D k0} {Ks : ℕ} {E₀ Eg E₁ E₂ C T T' ϱ : ℝ} {δ : D.host.E}
    {x : D.what₂.Tau → LocalDataRealPlace D} {L : LatticeDataWithDual D} {Kd : KernelData D} {B : D.what₂.Tau → LocBessel D.R.k D.R.rS}
    {f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp)}
    {μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    {kap : D.what₂.Tau → ℝ} {av : D.what₂.Tau → ℕ → ℕ → ℂ}

theorem nm_κLG (hL : LatAx D δ L) (hav : ∀ v i s, ‖av v i s‖ = kap v ^ (2 * i + s - 3)) {b s : ℕ} (hb : IsBlockSL2Embedding D b s) :
    κLG L av b s = L.κ * ∏ v, (kap v ^ (2 * b + s - 3)) ^ 2 := by
  unfold κLG
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [norm_aG hL hav hb v, mul_div_assoc, div_self (hL.2 b s hb).1.ne', mul_one]

variable (hH : ThmAHyp D C Ks δ T T' x L Kd B f μsec) (hX : XTie X x T T' kap)
    (hϱ : IsFrameScale D L ϱ) (hkap : ∀ v, kap v = kaV D δ v / ϱ)
    (hav : ∀ v i s, ‖av v i s‖ = kap v ^ (2 * i + s - 3))
    (hE₁ : 0 < E₁) (hE₁C : E₁ ≤ C) (hE₂ : 0 < E₂) (hE₂C : E₂ ≤ C)

include hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C

theorem block_estimate_bound (hDD : DualDensity D δ L) {E₃ C4 : ℝ} (hE₃ : 0 ≤ E₃) (hC4 : Real.pi * E₃ ≤ C4) {b s : ℕ} (hs : 2 ≤ s)
    (hb : IsBlockSL2Embedding D b s) :
    cbG L kap b s / κLG L av b s * (E₃ ^ (D.R.f * s) * ∏ s' ∈ Finset.Ico 1 s, ∏ v, X.LamG E₁ E₂ Ks s' b v ^ 2) ≤
      bdB D C C (Nlet D Ks) T T' δ x L C4 (b + s - 1) s := by
  have hL := hH.2.2.2.1
  have hκ := hL.1
  have hkp : ∀ v, 0 < kap v := fun v => by rw [hkap]; exact div_pos (nm_kaV_pos hH.2.2.1.1 v) hϱ.1
  have hblk : ∀ s' ∈ Finset.Ico 1 s, IsBlockSL2Embedding D b s' := fun s' h =>
    ⟨hb.1, (Finset.mem_Ico.1 h).1, by have := hb.2.2; have := (Finset.mem_Ico.1 h).2; omega⟩
  have hq : cbG L kap b s / κLG L av b s = ∏ s' ∈ Finset.Ico 1 s, (L.κ * ∏ v, (kap v ^ (2 * b + s' - 3)) ^ 2) := by
    have e2 : cbG L kap b s = L.κ ^ s * ((∏ v, (kap v ^ (2 * b + s - 3)) ^ 2) *
        ∏ v, ∏ s' ∈ Finset.Ico 1 s, (kap v ^ (2 * b + s' - 3)) ^ 2) := by
      unfold cbG
      rw [← Finset.prod_mul_distrib]
      congr 1
      exact Finset.prod_congr rfl fun v _ => nm_cblk (hkp v) hb.1 hb.2.1
    rw [nm_κLG hL hav hb, e2, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico, Finset.prod_comm]
    have h1 : 0 < ∏ v, (kap v ^ (2 * b + s - 3)) ^ 2 := Finset.prod_pos fun v _ => by have := hkp v; positivity
    have h2 : L.κ ^ s = L.κ * L.κ ^ (s - 1) := by rw [← pow_succ']; congr 1; omega
    rw [h2]
    field_simp
  have hvol : ∀ s', 0 ≤ volB D C C (Nlet D Ks) T T' δ x L b s' := fun s' => by unfold volB; positivity
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  rw [hq]
  calc (∏ s' ∈ Finset.Ico 1 s, (L.κ * ∏ v, (kap v ^ (2 * b + s' - 3)) ^ 2)) *
        (E₃ ^ (D.R.f * s) * ∏ s' ∈ Finset.Ico 1 s, ∏ v, X.LamG E₁ E₂ Ks s' b v ^ 2)
      = E₃ ^ (D.R.f * s) * ∏ s' ∈ Finset.Ico 1 s,
          ((∏ v, X.LamG E₁ E₂ Ks s' b v ^ 2) * (L.κ * ∏ v, (kap v ^ (2 * b + s' - 3)) ^ 2)) := by
        have e0 : ∏ s' ∈ Finset.Ico 1 s,
            ((∏ v, X.LamG E₁ E₂ Ks s' b v ^ 2) * (L.κ * ∏ v, (kap v ^ (2 * b + s' - 3)) ^ 2)) =
            (∏ s' ∈ Finset.Ico 1 s, ∏ v, X.LamG E₁ E₂ Ks s' b v ^ 2) *
              ∏ s' ∈ Finset.Ico 1 s, (L.κ * ∏ v, (kap v ^ (2 * b + s' - 3)) ^ 2) := Finset.prod_mul_distrib
        rw [e0]; ring
    _ ≤ E₃ ^ (D.R.f * s) * ∏ s' ∈ Finset.Ico 1 s, (Real.pi ^ (2 * D.R.f) * volB D C C (Nlet D Ks) T T' δ x L b s') := by
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun s' _ => ?_) fun s' h =>
          nm_claim1 hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C hDD (hblk s' h)) (pow_nonneg hE₃ _)
        exact mul_nonneg (Finset.prod_nonneg fun v _ => sq_nonneg _)
          (mul_nonneg hκ.le (Finset.prod_nonneg fun v _ => sq_nonneg _))
    _ = E₃ ^ (D.R.f * s) * (Real.pi ^ D.R.f) ^ (s - 1) *
          ∏ s' ∈ Finset.Ico 1 s, (Real.pi ^ D.R.f * volB D C C (Nlet D Ks) T T' δ x L b s') := by
        have e : ∀ s', Real.pi ^ (2 * D.R.f) * volB D C C (Nlet D Ks) T T' δ x L b s' =
            Real.pi ^ D.R.f * (Real.pi ^ D.R.f * volB D C C (Nlet D Ks) T T' δ x L b s') := fun s' => by
          rw [two_mul, pow_add]; ring
        simp_rw [e]
        rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico]
        ring
    _ ≤ C4 ^ (D.R.f * s) * ∏ s' ∈ Finset.Ico 1 s, (Real.pi ^ D.R.f * volB D C C (Nlet D Ks) T T' δ x L b s') := by
        refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun s' _ => mul_nonneg (by positivity) (hvol s'))
        have h1 : (Real.pi ^ D.R.f) ^ (s - 1) ≤ Real.pi ^ (D.R.f * s) := by
          rw [← pow_mul]; exact pow_le_pow_right₀ hpi (Nat.mul_le_mul_left _ (by omega))
        calc E₃ ^ (D.R.f * s) * (Real.pi ^ D.R.f) ^ (s - 1) ≤ E₃ ^ (D.R.f * s) * Real.pi ^ (D.R.f * s) :=
              mul_le_mul_of_nonneg_left h1 (pow_nonneg hE₃ _)
          _ = (Real.pi * E₃) ^ (D.R.f * s) := by rw [mul_pow]; ring
          _ ≤ C4 ^ (D.R.f * s) := pow_le_pow_left₀ (by positivity) hC4 _
    _ = _ := by
        unfold bdB
        rw [show b + s - 1 - s + 1 = b by have := hb.1; omega]

theorem mod_of_tie {E₃ C4 : ℝ} {Aa : D.what₂.Tau → ℝ} (hstd : X.Std Ks E₀ Eg) (hA : ∀ v, 0 < Aa v)
    (hLat : LatOpen D δ L) (hDD : DualDensity D δ L) (hE₃ : 0 ≤ E₃) (hC4 : Real.pi * E₃ ≤ C4)
    (hΘ : 1 ≤ ThS D C C (Nlet D Ks) T T' δ x L) :
    Mod D X (aG L av) (cbG L kap) (c0G L Aa) Ks E₀ Eg E₁ E₂ E₃ C C4 T T' δ x L (κLG L av) := by
  have hL := hH.2.2.2.1
  have hkp : ∀ v, 0 < kap v := fun v => by rw [hkap]; exact div_pos (nm_kaV_pos hH.2.2.1.1 v) hϱ.1
  have ha : ∀ i s v, aG L av i s v ≠ 0 := fun i s v => by
    unfold aG
    refine mul_ne_zero (norm_pos_iff.1 (by rw [hav]; exact pow_pos (hkp v) _)) ?_
    split_ifs with h
    · simp
    · exact_mod_cast h
  exact
    { std := hstd
      δ_ne := hH.2.2.1.1
      a_ne := ha
      cb_pos := fun i s => by
        unfold cbG cblk
        refine mul_pos (pow_pos hL.1 _) (Finset.prod_pos fun v _ => ?_)
        exact mul_pos (inv_pos.2 (pow_pos (hkp v) _)) (Finset.prod_pos fun l _ => pow_pos (hkp v) _)
      lowerConstantNonneg := div_nonneg (Finset.prod_nonneg fun v _ => (hA v).le) (pow_nonneg hL.1.le _)
      brk_pos := nm_brk_pos hstd
      xi_nn := nm_xi_nonneg hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C
      blockSizeNonneg := block_size_nonneg hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C
      thr1 := fun i v h1 h2 => xi_le hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C h1 h2 v
      thr3 := fun i s v h1 h2 h3 h4 => norm_le_third_threshold hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C i s v h1 h2 h3 h4
      lat := fun b s hb => (hLat (aG L av) b s hb (fun v => ha b s v)).1
      dual := fun b s hb => (hLat (aG L av) b s hb (fun v => ha b s v)).2
      dualV := fun b s hb => (hL.2 b s hb).2.2.2.2.1
      cb1 := fun i h1 h2 => by
        rw [nm_κLG hL hav ⟨h1, le_rfl, by omega⟩]
        unfold cbG
        rw [pow_one]
        congr 1
        refine Finset.prod_congr rfl fun v _ => ?_
        rw [nm_cblk (hkp v) h1 le_rfl, Finset.Ico_self, Finset.prod_empty, mul_one]
      blockProductBound := fun b s h1 h2 => block_product_le_sqrt_norm hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C hΘ h1 h2
      blockSL2Embedding_bound := fun b s h1 h2 => block_estimate_bound hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C hDD hE₃ hC4 h1 h2 }

end Num3

end Formalism.MainNotions.BlockEstimateWords

end

end PartNum3

section PartVal0

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

theorem nm_sqrt_pow {y : ℝ} (hy : 0 ≤ y) (n : ℕ) : Real.sqrt (y ^ n) = Real.sqrt y ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hy n), ih, pow_succ]

theorem nm_sqrt_prod {ι : Type} (s : Finset ι) (g : ι → ℝ) (h : ∀ i ∈ s, 0 ≤ g i) :
    Real.sqrt (∏ i ∈ s, g i) = ∏ i ∈ s, Real.sqrt (g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Real.sqrt_mul (h a (Finset.mem_insert_self a s)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem vl_wt_nonneg (k r : ℕ) (T T' : ℝ) : ∀ (bs : List (ℂ × ℕ)) (o : ℕ), o + (bs.map Prod.snd).sum = r + 1 →
    (∀ b ∈ bs, 1 ≤ b.2) → (∀ t : ℂ, bs.getLast? = some (t, 1) → T * T' < Complex.normSq t) →
    0 ≤ ptWeightFrom k r T T' o bs := by
  intro bs
  induction bs with
  | nil => intro o _ _ _; simp [ptWeightFrom]
  | cons b bs ih =>
    intro o ho hs hl
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at ho
    have htail : 0 ≤ ptWeightFrom k r T T' (o + s) bs := by
      refine ih (o + s) (by omega) (fun b hb => hs b (List.mem_cons_of_mem _ hb)) fun t' ht' => hl t' ?_
      rw [List.getLast?_cons, ht']; rfl
    show 0 ≤ (if s = 1 ∧ o + 1 = r + 1 then (Complex.normSq t - T * T') ^ (k - 1)
      else ‖t‖ ^ (2 * s * (Ml k r (o + s) + s - 3))) * ptWeightFrom k r T T' (o + s) bs
    refine mul_nonneg ?_ htail
    split_ifs with h
    · obtain ⟨rfl, h2⟩ := h
      have hbs : bs = [] := by
        cases bs with
        | nil => rfl
        | cons c cs =>
          have := hs c (by simp)
          simp only [List.map_cons, List.sum_cons] at ho
          omega
      subst hbs
      have := hl t (by simp)
      exact pow_nonneg (by linarith) _
    · positivity

section Val

variable {D : D7} {L : LatticeDataWithDual D}

theorem vl_scl (hρ : ∀ i s, IsBlockSL2Embedding D i s → L.ρ i s ≠ 0) (av : D.what₂.Tau → ℕ → ℕ → ℂ) (v : D.what₂.Tau) :
    ∀ (bs : List (D.host.E × ℕ)) (o : ℕ), (∀ b ∈ bs, 1 ≤ b.2) → o + (bs.map Prod.snd).sum ≤ D.R.rS + 1 →
      sclL (av v) o (locBlocksFrom D L.ρ v o bs) = lbF (aG L av) v o (bs.map Prod.swap) := by
  intro bs
  induction bs with
  | nil => intro o _ _; rfl
  | cons b bs ih =>
    intro o hs ho
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at ho
    have h1 : 1 ≤ s := hs (t, s) (by simp)
    have hb : IsBlockSL2Embedding D (o + 1) s := ⟨by omega, h1, by omega⟩
    show (av v (o + 1) s * (((L.ρ (o + 1) s : ℝ) : ℂ) * plEmb D v t), s) :: sclL (av v) (o + s) (locBlocksFrom D L.ρ v (o + s) bs) =
      (aG L av (o + 1) s v * plEmb D v t, s) :: lbF (aG L av) v (o + s) (bs.map Prod.swap)
    rw [ih (o + s) (fun b hb => hs b (List.mem_cons_of_mem _ hb)) (by omega)]
    unfold aG
    rw [if_neg (hρ _ _ hb), mul_assoc]

theorem vl_ok (hρ : ∀ i s, IsBlockSL2Embedding D i s → L.ρ i s ≠ 0) (v : D.what₂.Tau) :
    ∀ (bs : List (D.host.E × ℕ)) (o : ℕ), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → o + (bs.map Prod.snd).sum ≤ D.R.rS + 1 →
      ∀ c ∈ locBlocksFrom D L.ρ v o bs, c.1 ≠ 0 ∧ 1 ≤ c.2 := by
  intro bs
  induction bs with
  | nil => intro o _ _ c hc; simp [locBlocksFrom] at hc
  | cons b bs ih =>
    intro o hs ho c hc
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at ho
    have h1 := hs (t, s) (by simp)
    have hb : IsBlockSL2Embedding D (o + 1) s := ⟨by omega, h1.2, by omega⟩
    simp only [locBlocksFrom, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨mul_ne_zero (by exact_mod_cast hρ _ _ hb) ((map_ne_zero (plEmb D v)).2 h1.1), h1.2⟩
    · exact ih (o + s) (fun b hb => hs b (List.mem_cons_of_mem _ hb)) (by omega) c hc

theorem vl_w {k0 : ℕ} (X : GramWordSpace.Dat D k0) (a : ℕ → ℕ → D.what₂.Tau → ℂ) (v : D.what₂.Tau) :
    ∀ (p : TA.Pt D.host.E) (o : ℕ), wLoc (k0 + 1) D.R.rS (X.T v) (X.T' v) o (lbF a v o p) = wF X a v o p := by
  intro p
  induction p with
  | nil => intro o; rfl
  | cons b bs ih =>
    intro o
    obtain ⟨s, t⟩ := b
    show (if okL D.R.rS (X.T v) (X.T' v) o s (a (o + 1) s v * plEmb D v t) then
        Real.sqrt (ptWeightFrom (k0 + 1) D.R.rS (X.T v) (X.T' v) o [(a (o + 1) s v * plEmb D v t, s)]) else 0) *
        wLoc (k0 + 1) D.R.rS (X.T v) (X.T' v) (o + s) (lbF a v (o + s) bs) =
      wB X v o s (a (o + 1) s v * plEmb D v t) * wF X a v (o + s) bs
    rw [ih (o + s)]
    rfl

theorem vl_sqrt_cb (hκ : 0 < L.κ) {kap : D.what₂.Tau → ℝ} (hkp : ∀ v, 0 ≤ kap v) (i s : ℕ) :
    Real.sqrt (cbG L kap i s) = Real.sqrt L.κ ^ s * ∏ v, Real.sqrt (cblk (kap v) i s) := by
  unfold cbG
  rw [Real.sqrt_mul (pow_nonneg hκ.le _), nm_sqrt_pow hκ.le, nm_sqrt_prod]
  intro v _
  unfold cblk
  exact mul_nonneg (inv_nonneg.2 (pow_nonneg (hkp v) _)) (Finset.prod_nonneg fun l _ => pow_nonneg (hkp v) _)

theorem vl_nF (hκ : 0 < L.κ) {kap : D.what₂.Tau → ℝ} (hkp : ∀ v, 0 ≤ kap v) :
    ∀ (bs : List (D.host.E × ℕ)) (o : ℕ), nF (D := D) (cbG L kap) o (bs.map Prod.swap) =
      Real.sqrt L.κ ^ ((bs.map Prod.snd).sum) * ∏ v, ccL (kap v) o (locBlocksFrom D L.ρ v o bs) := by
  intro bs
  induction bs with
  | nil => intro o; simp [nF, ccL, locBlocksFrom]
  | cons b bs ih =>
    intro o
    obtain ⟨t, s⟩ := b
    show Real.sqrt (cbG L kap (o + 1) s) * nF (D := D) (cbG L kap) (o + s) (bs.map Prod.swap) =
      Real.sqrt L.κ ^ (s + (bs.map Prod.snd).sum) *
        ∏ v, (Real.sqrt (cblk (kap v) (o + 1) s) * ccL (kap v) (o + s) (locBlocksFrom D L.ρ v (o + s) bs))
    rw [ih (o + s), vl_sqrt_cb hκ hkp, pow_add, Finset.prod_mul_distrib]
    ring

end Val

def vlPt {D : D7} {δ : D.host.E} {L : LatticeDataWithDual D} (hL : LatAx D δ L) (v : D.what₂.Tau) (q : Point D.host.E (D.R.rS + 1)) :
    Point ℂ (D.R.rS + 1) :=
  ⟨locBlocks D L.ρ v q.1, vl_ok (fun i s h => (hL.2 i s h).1.ne') v q.1 0 q.2.1 (by rw [q.2.2]; omega), by
    rw [locBlocks, locBlocksFrom_snd]; exact q.2.2⟩

end Formalism.MainNotions.BlockEstimateWords

end

end PartVal0

section PartVal

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

theorem hs_zero_left {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : hsInner (0 : Wq →L[ℂ] Wp) A = 0 := by
  simp [hsInner]

theorem hs_zero_right {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : hsInner A (0 : Wq →L[ℂ] Wp) = 0 := by
  simp [hsInner]

section ValM

variable {D : D7} {k0 : ℕ} (hk : k0 + 1 = D.R.k) {G : GramWordSpace.GramMap k0 D.R.rS} {B : D.what₂.Tau → LocBessel D.R.k D.R.rS}
    {f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp)}
    {μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (Fr : ∀ v, LocFrame D hk G (B v) (f v) (μsec v)) (x : D.what₂.Tau → LocalDataRealPlace D) (l : D.what₂.Tau → Fin (k0 + 1))
    (R : ∀ v (j : ℕ) (hj : j ≤ D.R.rS), ℂ → Matrix (Fin 2) (Fin 2) (GramWordSpace.lev (Fr v).B' (Fr v).μ' j hj).POp)
    (Th : ∀ v (j : ℕ) (_ : j ≤ D.R.rS) (w : TopsChoicePartA.Word), TopsChoicePartA.AuxiliarySlotStates w.length → GramWordSpace.GFn (Fr v).B' → GramWordSpace.GFn (Fr v).B')

theorem vl_zero {T T' : ℝ} {δ : D.host.E} {L : LatticeDataWithDual D} (hL : LatAx D δ L)
    (hT : ∀ v, Tz D.R.k D.R.rS (B v).z = T) (hT' : ∀ v, Tz D.R.k D.R.rS (B v).z' = T')
    (q : Point D.host.E (D.R.rS + 1)) (v : D.what₂.Tau)
    (hneg : ptWeightFrom D.R.k D.R.rS T T' 0 (locBlocks D L.ρ v q.1) < 0) :
    (BlockEstimateTheorem.vmOf D hk G).V (B v) (f v) (locBlocks D L.ρ v q.1) = 0 := by
  refine (BlockEstimateTheorem.vmOf D hk G).val0 (B v) (f v) (vlPt hL v q) fun hrep => ?_
  have h1 := hrep.1
  rw [hT v, hT' v] at h1
  have := vl_wt_nonneg D.R.k D.R.rS T T' (vlPt hL v q).1 0 (by rw [(vlPt hL v q).2.2]; omega)
    (fun b hb => ((vlPt hL v q).2.1 b hb).2) h1
  exact absurd hneg (not_lt.2 this)

theorem val_of_frames {T T' : ℝ} {δ : D.host.E} {L : LatticeDataWithDual D} (hL : LatAx D δ L)
    (hT : ∀ v, Tz D.R.k D.R.rS (B v).z = T) (hT' : ∀ v, Tz D.R.k D.R.rS (B v).z' = T')
    (p q : Point D.host.E (D.R.rS + 1)) :
    ((Real.sqrt (ptWeightG D L.ρ T T' q.1) : ℝ) : ℂ) * ((Real.sqrt (ptWeightG D L.ρ T T' p.1) : ℝ) : ℂ) *
      ∏ v, hsInner ((BlockEstimateTheorem.vmOf D hk G).V (B v) (f v) (locBlocks D L.ρ v q.1))
        ((BlockEstimateTheorem.vmOf D hk G).V (B v) (f v) (locBlocks D L.ρ v p.1)) =
    GkLim G (mkX hk Fr x l R Th) (aG L fun v => (Fr v).av) (cbG L fun v => ‖(B v).c‖ / 2) (c0G L fun v => (Fr v).A)
      (unsw q) (unsw p) := by
  have hρ : ∀ i s, IsBlockSL2Embedding D i s → L.ρ i s ≠ 0 := fun i s h => (hL.2 i s h).1.ne'
  have hκ := hL.1
  have hkp : ∀ v, 0 ≤ ‖(B v).c‖ / 2 := fun v => by positivity
  have hsz : ∀ q : Point D.host.E (D.R.rS + 1), (∀ b ∈ q.1, 1 ≤ b.2) ∧ 0 + (q.1.map Prod.snd).sum ≤ D.R.rS + 1 := fun q =>
    ⟨fun b hb => (q.2.1 b hb).2, by rw [q.2.2]; omega⟩
  have hscl : ∀ (q : Point D.host.E (D.R.rS + 1)) v, sclL (Fr v).av 0 (locBlocks D L.ρ v q.1) =
      lbF (aG L fun v => (Fr v).av) v 0 (unsw q) := fun q v =>
    vl_scl hρ (fun v => (Fr v).av) v q.1 0 (hsz q).1 (hsz q).2

  have hv : ∀ v, ((Real.sqrt (ptWeightFrom D.R.k D.R.rS T T' 0 (locBlocks D L.ρ v q.1)) *
        Real.sqrt (ptWeightFrom D.R.k D.R.rS T T' 0 (locBlocks D L.ρ v p.1)) : ℝ) : ℂ) *
      hsInner ((BlockEstimateTheorem.vmOf D hk G).V (B v) (f v) (locBlocks D L.ρ v q.1))
        ((BlockEstimateTheorem.vmOf D hk G).V (B v) (f v) (locBlocks D L.ρ v p.1)) =
      (((Fr v).A * (ccL (‖(B v).c‖ / 2) 0 (locBlocks D L.ρ v q.1) * ccL (‖(B v).c‖ / 2) 0 (locBlocks D L.ρ v p.1)) *
        (wF (mkX hk Fr x l R Th) (aG L fun v => (Fr v).av) v 0 (unsw q) *
          wF (mkX hk Fr x l R Th) (aG L fun v => (Fr v).av) v 0 (unsw p)) : ℝ) : ℂ) *
      hsInner (G.V (Fr v).B' (Fr v).f' (lbF (aG L fun v => (Fr v).av) v 0 (unsw q)))
        (G.V (Fr v).B' (Fr v).f' (lbF (aG L fun v => (Fr v).av) v 0 (unsw p))) := fun v => by
    have h := (Fr v).val (vlPt hL v q) (vlPt hL v p)
    rw [hT v, hT' v] at h
    rw [← vl_w (mkX hk Fr x l R Th) _ v (unsw q) 0, ← vl_w (mkX hk Fr x l R Th) _ v (unsw p) 0, ← hscl q v, ← hscl p v]
    exact h

  have ha : ((Real.sqrt (ptWeightG D L.ρ T T' q.1) : ℝ) : ℂ) * ((Real.sqrt (ptWeightG D L.ρ T T' p.1) : ℝ) : ℂ) *
      ∏ v, hsInner ((BlockEstimateTheorem.vmOf D hk G).V (B v) (f v) (locBlocks D L.ρ v q.1))
        ((BlockEstimateTheorem.vmOf D hk G).V (B v) (f v) (locBlocks D L.ρ v p.1)) =
      ∏ v, (((Real.sqrt (ptWeightFrom D.R.k D.R.rS T T' 0 (locBlocks D L.ρ v q.1)) *
        Real.sqrt (ptWeightFrom D.R.k D.R.rS T T' 0 (locBlocks D L.ρ v p.1)) : ℝ) : ℂ) *
      hsInner ((BlockEstimateTheorem.vmOf D hk G).V (B v) (f v) (locBlocks D L.ρ v q.1))
        ((BlockEstimateTheorem.vmOf D hk G).V (B v) (f v) (locBlocks D L.ρ v p.1))) := by
    by_cases hall : (∀ v, 0 ≤ ptWeightFrom D.R.k D.R.rS T T' 0 (locBlocks D L.ρ v q.1)) ∧
        ∀ v, 0 ≤ ptWeightFrom D.R.k D.R.rS T T' 0 (locBlocks D L.ρ v p.1)
    · unfold ptWeightG
      rw [nm_sqrt_prod _ _ fun v _ => hall.1 v, nm_sqrt_prod _ _ fun v _ => hall.2 v, Finset.prod_mul_distrib]
      push_cast
      rw [Finset.prod_mul_distrib]
    · have hz : ∃ v, hsInner ((BlockEstimateTheorem.vmOf D hk G).V (B v) (f v) (locBlocks D L.ρ v q.1))
          ((BlockEstimateTheorem.vmOf D hk G).V (B v) (f v) (locBlocks D L.ρ v p.1)) = 0 := by
        rw [not_and_or, not_forall, not_forall] at hall
        rcases hall with ⟨v, h⟩ | ⟨v, h⟩
        · exact ⟨v, by rw [vl_zero hk hL hT hT' q v (not_le.1 h)]; exact hs_zero_left _⟩
        · exact ⟨v, by rw [vl_zero hk hL hT hT' p v (not_le.1 h)]; exact hs_zero_right _⟩
      obtain ⟨v, hz⟩ := hz
      rw [Finset.prod_eq_zero (Finset.mem_univ v) hz, mul_zero,
        Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hz, mul_zero])]
  rw [ha, Finset.prod_congr rfl fun v _ => hv v, Finset.prod_mul_distrib]
  unfold GkLim
  congr 1
  rw [← Complex.ofReal_prod]
  congr 1
  unfold sc c0G
  have e1 : nF (D := D) (cbG L fun v => ‖(B v).c‖ / 2) 0 (q.1.map Prod.swap) =
      Real.sqrt L.κ ^ ((q.1.map Prod.snd).sum) * ∏ v, ccL (‖(B v).c‖ / 2) 0 (locBlocks D L.ρ v q.1) := vl_nF (L := L) hκ hkp q.1 0
  have e2 : nF (D := D) (cbG L fun v => ‖(B v).c‖ / 2) 0 (p.1.map Prod.swap) =
      Real.sqrt L.κ ^ ((p.1.map Prod.snd).sum) * ∏ v, ccL (‖(B v).c‖ / 2) 0 (locBlocks D L.ρ v p.1) := vl_nF (L := L) hκ hkp p.1 0
  rw [q.2.2] at e1
  rw [p.2.2] at e2
  show _ = _ / _ * (nF (D := D) _ 0 (q.1.map Prod.swap) * _ * (nF (D := D) _ 0 (p.1.map Prod.swap) * _))
  rw [e1, e2, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have e3 : Real.sqrt L.κ ^ (D.R.rS + 1) * Real.sqrt L.κ ^ (D.R.rS + 1) = L.κ ^ (D.R.rS + 1) := by
    rw [← mul_pow, Real.mul_self_sqrt hκ.le]
  have h4 := pow_pos hκ (D.R.rS + 1)
  rw [← e3]
  have h5 : 0 < Real.sqrt L.κ ^ (D.R.rS + 1) := pow_pos (Real.sqrt_pos.2 hκ) _
  field_simp

end ValM

end Formalism.MainNotions.BlockEstimateWords

end

end PartVal

section PartOuter

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

structure OpenAt (D : D7) {k0 : ℕ} (hk : k0 + 1 = D.R.k) (G : GramWordSpace.GramMap k0 D.R.rS) : Prop where
  frame : FrameOpen D hk G
  cut : CutOpen D G
  rad : RadOpen k0 D.R.rS

theorem latOpen_of_LatAx {D : D7} {δ : D.host.E} {L : LatticeDataWithDual D} (hδ : δ ≠ 0) (hL : LatAx D δ L) : LatOpen D δ L :=
  fun a _ _ hb ha => ⟨isLat_of_LatAx a hL hb ha, dual_of_LatAx a hL hδ hb ha⟩

theorem dualDensity_of_LatAx {D : D7} {δ : D.host.E} {L : LatticeDataWithDual D} (hδ : δ ≠ 0) (hv : 1 ≤ D.host.v) (hL : LatAx D δ L) :
    DualDensity D δ L := fun _ _ hb => dualDensity D δ L hL hδ hv hb

theorem c_facts {D : D7} {δ : D.host.E} (hψ : PsiAx D δ) {ϱ : ℝ} (hϱ : 0 < ϱ) (v : D.what₂.Tau) :
    cPsi D δ v / (ϱ : ℂ) ≠ 0 ∧ ((cPsi D δ v / (ϱ : ℂ)).re = 0 ∨ (cPsi D δ v / (ϱ : ℂ)).im = 0) ∧
      ‖cPsi D δ v / (ϱ : ℂ)‖ / 2 = kaV D δ v / ϱ := by
  have hδ : plEmb D v δ ≠ 0 := (map_ne_zero (plEmb D v)).2 hψ.1
  have hϱ' : (ϱ : ℂ) ≠ 0 := by exact_mod_cast hϱ.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · unfold cPsi
    exact div_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) hpi) hδ) hϱ'
  · have e : cPsi D δ v / (ϱ : ℂ) = ((4 * Real.pi / (ϱ * Complex.normSq (plEmb D v δ)) : ℝ) : ℂ) * conj (plEmb D v δ) := by
      unfold cPsi
      have hn : (Complex.normSq (plEmb D v δ) : ℂ) = plEmb D v δ * conj (plEmb D v δ) := (Complex.mul_conj _).symm
      have hc : conj (plEmb D v δ) ≠ 0 := (map_ne_zero _).2 hδ
      push_cast
      rw [hn]
      field_simp
    rw [e]
    rcases hψ.2 with h | h
    · left
      rw [Complex.re_ofReal_mul, Complex.conj_re, h v, mul_zero]
    · right
      rw [Complex.im_ofReal_mul, Complex.conj_im, h v, neg_zero, mul_zero]
  · unfold cPsi kaV
    rw [norm_div, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      Real.norm_of_nonneg hϱ.le]
    have : ‖(4 : ℂ)‖ = 4 := by simp
    rw [this]
    ring

theorem stThmA_of_frames (Kst : ℕ) (hK : 4 ≤ Kst) (E₃ : ℝ) (hE₃ : 0 ≤ E₃) : ∃ Ca Cb : ℝ, ∀ C ≥ Ca, ∀ C' ≥ Cb,
    ∀ (E₀ Eg E₁ E₂ : ℝ), E₀ ≤ C → Eg ≤ C → 0 < E₁ → E₁ ≤ C → 0 < E₂ → E₂ ≤ C →
    ∀ (D : D7) (k0 : ℕ) (hk : k0 + 1 = D.R.k) (G : GramWordSpace.GramMap k0 D.R.rS),
      GramWordSpace.SingleLevelGramEstimate D G Kst E₀ Eg E₁ E₂ → GramWordSpace.BlockLiftEstimate D G Kst E₀ Eg E₁ E₂ → GramWordSpace.LargeBlockLiftEstimate D G Kst E₀ Eg E₁ E₂ E₃ →
      GramWordSpace.E D k0 Kst E₀ Eg → GramWordSpace.TopPos D G Kst E₀ Eg → GramWordSpace.LowPos D k0 Kst E₀ Eg → GramWordSpace.LettersExist →
      OpenAt D hk G → stThmA D C C' Kst (BlockEstimateTheorem.vmOf D hk G) := by
  have hC4 : (1 : ℝ) ≤ max 1 (Real.pi * E₃) := le_max_left _ _
  obtain ⟨C0, C1', Cc, hC01, hmain⟩ := sRowForm_of_levelEstU Kst hK (max 1 (Real.pi * E₃)) hC4
  refine ⟨max C0 (max Cc 0), max C1' 1, ?_⟩
  intro C hC C' hC' E₀ Eg E₁ E₂ hE₀ hEg hE₁ hE₁C hE₂ hE₂C D k0 hk G h72 h73 h74 hE hTop hLow hLet hO δ T T' x L
    Kd B f μsec ι _ c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr hΘ hRows
  have hCC0 : C0 ≤ C := le_trans (le_max_left _ _) hC
  have hCCc : Cc ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hC0' : 0 ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  set Θ : ℝ := ThS D C C (Nlet D Kst) T T' δ x L with hΘdef
  have hΘ1 : C1' ≤ Θ := le_trans (le_trans (le_max_left _ _) hC') hΘ
  have hΘone : 1 ≤ Θ := le_trans (le_trans (le_max_right _ _) hC') hΘ
  have hΘpos : 0 < Θ := lt_of_lt_of_le one_pos hΘone
  have hHyp : ThmAHyp D C Kst δ T T' x L Kd B f μsec := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  have hOK := szOK_of_LatAx h3.1 h4 (szPos_of_ThmAHyp (lt_of_lt_of_le one_pos (le_trans hC01 hCC0)) hHyp)

  obtain ⟨ϱ, hϱ, hBc⟩ := h5
  have hcf := fun v => c_facts h3 hϱ.1 v
  have hFr : ∀ v, Nonempty (LocFrame D hk G (B v) (f v) (μsec v)) := fun v =>
    hO.frame (B v) (f v) (μsec v) (by rw [hBc v]; exact (hcf v).1) (by rw [hBc v]; exact (hcf v).2.1) (h7 v).2.1 (h7 v).2.2
  let Fr : ∀ v, LocFrame D hk G (B v) (f v) (μsec v) := fun v => (hFr v).some
  obtain ⟨l, R, Th, hstd⟩ := std_of_frames hk Fr hHyp hE₀ hEg hO.rad hLet
  have hX := xtie_of_frames hk Fr x l R Th (fun v => (h7 v).1)
  have hkap : ∀ v, ‖(B v).c‖ / 2 = kaV D δ v / ϱ := fun v => by rw [hBc v]; exact (hcf v).2.2
  have hM := mod_of_tie (E₃ := E₃) (C4 := max 1 (Real.pi * E₃)) (Aa := fun v => (Fr v).A) hHyp hX hϱ hkap
    (fun v i s => (Fr v).hav i s) hE₁ hE₁C hE₂ hE₂C hstd (fun v => (Fr v).hA) (latOpen_of_LatAx h3.1 h4)
    (dualDensity_of_LatAx h3.1 h2 h4) hE₃ (le_max_right _ _) hΘone
  obtain ⟨χ, hχ⟩ := isCutoff_exists
  have hcut : ∀ v (γ : Point ℂ (D.R.rS + 1)), ∀ᶠ eps in 𝓝[>] (0 : ℝ),
      G.V ((mkX hk Fr x l R Th).B v) ((mkX hk Fr x l R Th).Fv χ eps v) γ.1 =
        G.V ((mkX hk Fr x l R Th).B v) ((mkX hk Fr x l R Th).f v) γ.1 := fun v γ =>
    hO.cut (Fr v).B' (Fr v).f' χ (Fr v).hc hχ (Fr v).hf γ
  obtain ⟨H, i1, i2, i3, Wv, hW, Wd, iW, len, Φ, tr, w0, hEst, hEn, hw0, hcutΦ⟩ :=
    levelEst_of_model hM h4 hχ (poissonPi D) h72 h73 h74 hE hTop hLow Kd hcut
  have hTz : ∀ v, Tz D.R.k D.R.rS (B v).z = T := fun v => (h7 v).1.2.2.2.1
  have hTz' : ∀ v, Tz D.R.k D.R.rS (B v).z' = T' := fun v => (h7 v).1.2.2.2.2.1
  have hjn := energy_of_frames hk Fr x l R Th h4 hTz hTz'
  set jn : ℝ := c0G L (fun v => (Fr v).A) * (mkX hk Fr x l R Th).jn2.re with hjndef
  have y0 : 0 ≤ C0 / Θ := div_nonneg (by linarith) hΘpos.le
  have y1 : (C0 / Θ) ^ D.R.f ≤ (C / Θ) ^ D.R.f :=
    pow_le_pow_left₀ y0 (div_le_div_of_nonneg_right hCC0 hΘpos.le) _
  have y2 : 0 ≤ (C0 / Θ) ^ D.R.f := pow_nonneg y0 _
  have hr0 : (0 : ℝ) ≤ (D.R.rS : ℝ) := Nat.cast_nonneg _
  have hr' : (D.R.rS : ℝ) * (C0 / Θ) ^ D.R.f ≤ 1 := by
    refine le_trans ?_ hr
    exact mul_le_mul (by linarith) y1 y2 (by linarith)
  have key := hmain D C C (Nlet D Kst) T T' δ x L Kd (taLv D δ L) h6 hOK hΘ1 hr'
    (fun v => (B v).Wq →L[ℂ] (B v).Wp) (fun _ => hsInner) (fun v => ta_psdk_hsInner)
    (fun h => ptWeightG D L.ρ T T' h.1) ι c (fun v h => (BlockEstimateTheorem.vmOf D hk G).V (B v) (f v) (locBlocks D L.ρ v h.1)) hRows H
    (fun q => Wv (unsw q))
    (fun p q => by rw [hW]; exact (val_of_frames hk Fr x l R Th h4 hTz hTz' p q).symm)
    Wd len _ _ Φ tr w0 jn hEst hEn hw0
    (fun p hp => by
      refine (hcutΦ p hp).mono fun eps he => ?_
      rw [he, unsw_ph hp])
  refine le_trans key ?_
  have hjn0 : 0 ≤ jn := by
    refine ge_of_tendsto' (hEn w0 (by rw [hw0]; exact Nat.zero_le _)) fun eps => by positivity
  have hprod : 0 ≤ ∏ i ∈ Icc 1 (D.R.rS + 1), (1 + Kd.e i) := by
    refine Finset.prod_nonneg fun i hi => ?_
    have := (h6.2.2.1 i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2).1
    linarith
  have ha : (1 + Cc * ((D.R.rS : ℝ) + 1) * (C0 / Θ) ^ D.R.f) ≤ (1 + C * ((D.R.rS : ℝ) + 1) * (C / Θ) ^ D.R.f) := by
    have t1 : Cc * ((D.R.rS : ℝ) + 1) * (C0 / Θ) ^ D.R.f ≤ C * ((D.R.rS : ℝ) + 1) * (C0 / Θ) ^ D.R.f :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCCc (by linarith)) y2
    have t2 : C * ((D.R.rS : ℝ) + 1) * (C0 / Θ) ^ D.R.f ≤ C * ((D.R.rS : ℝ) + 1) * (C / Θ) ^ D.R.f :=
      mul_le_mul_of_nonneg_left y1 (mul_nonneg hC0' (by linarith))
    linarith
  have ha' : 0 ≤ (1 + C * ((D.R.rS : ℝ) + 1) * (C / Θ) ^ D.R.f) * ∏ i ∈ Icc 1 (D.R.rS + 1), (1 + Kd.e i) := by
    refine mul_nonneg ?_ hprod
    have : 0 ≤ C * ((D.R.rS : ℝ) + 1) * (C / Θ) ^ D.R.f :=
      mul_nonneg (mul_nonneg hC0' (by linarith)) (le_trans y2 y1)
    linarith
  calc ENNReal.ofReal ((1 + Cc * ((D.R.rS : ℝ) + 1) * (C0 / Θ) ^ D.R.f) * (∏ i ∈ Icc 1 (D.R.rS + 1), (1 + Kd.e i)) * jn)
      ≤ ENNReal.ofReal ((1 + C * ((D.R.rS : ℝ) + 1) * (C / Θ) ^ D.R.f) * (∏ i ∈ Icc 1 (D.R.rS + 1), (1 + Kd.e i)) * jn) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha hprod) hjn0)
    _ = ENNReal.ofReal ((1 + C * ((D.R.rS : ℝ) + 1) * (C / Θ) ^ D.R.f) * ∏ i ∈ Icc 1 (D.R.rS + 1), (1 + Kd.e i)) *
          ENNReal.ofReal jn := ENNReal.ofReal_mul ha'
    _ ≤ _ := mul_le_mul' le_rfl hjn

end Formalism.MainNotions.BlockEstimateWords

end

end PartOuter

section PartPack

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

def OpenAll (D : D7) (Gm : BlockEstimateTheorem.GM) : Prop := ∀ (k0 : ℕ) (hk : k0 + 1 = D.R.k), OpenAt D hk (Gm k0 D.R.rS)

theorem block_statement_of_open (Kst : ℕ) (hK : 4 ≤ Kst) (E₃ : ℝ) (hE₃ : 0 ≤ E₃) : ∃ Ca Cb : ℝ, ∀ C ≥ Ca, ∀ C' ≥ Cb,
    ∀ (E₀ Eg E₁ E₂ : ℝ), E₀ ≤ C → Eg ≤ C → 0 < E₁ → E₁ ≤ C → 0 < E₂ → E₂ ≤ C →
    ∀ (CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ : ℝ) (D : D7) (Gm : BlockEstimateTheorem.GM), OpenAll D Gm →
      BlockEstimateTheorem.Stmt D Gm Kst CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ C C' := by
  obtain ⟨Ca, Cb, h⟩ := stThmA_of_frames Kst hK E₃ hE₃
  refine ⟨Ca, Cb, fun C hC C' hC' E₀ Eg E₁ E₂ a1 a2 a3 a4 a5 a6 CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ D Gm hO hAdm k0 hk => ?_⟩
  obtain ⟨-, e12e, -, e19, e20, e21, e22, e12g, e23⟩ := hAdm
  exact h C hC C' hC' E₀ Eg E₁ E₂ a1 a2 a3 a4 a5 a6 D k0 hk (Gm k0 D.R.rS) (e20 k0) (e21 k0) (e22 k0) (e19 k0) (e12e k0)
    (e12g k0) e23 (hO k0 hk)

theorem block_family_of_open (E₃ : ℝ) (hE₃ : 0 ≤ E₃) : ∃ Ca Cb : ℝ, ∀ CA ≥ Ca, ∀ CA' ≥ Cb,
    ∀ (E₀ Eg E₁ E₂ : ℝ), E₀ ≤ CA → Eg ≤ CA → 0 < E₁ → E₁ ≤ CA → 0 < E₂ → E₂ ≤ CA →
    ∀ (CB Co Cd Cv K1 K2 Cs cD C₁ Cg₁ Cg₂ : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Gm : BlockEstimateTheorem.GM),
      (∀ x (i : Fm.Ix x), OpenAll (Fm.D x i) Gm) →
      BlockEstimateTheorem.KudlaFamilyStatement Fm Gm 5 CB Co Cd Cv K1 K2 Cs cD C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ CA CA' := by
  obtain ⟨Ca, Cb, h⟩ := block_statement_of_open 5 (by norm_num) E₃ hE₃
  refine ⟨Ca, Cb, fun CA hC CA' hC' E₀ Eg E₁ E₂ a1 a2 a3 a4 a5 a6 CB Co Cd Cv K1 K2 Cs cD C₁ Cg₁ Cg₂ eps Fm Gm hO => ?_⟩
  exact BlockEstimateTheorem.familyStatement_of_pointwise Fm Gm 5 CB Co Cd Cv K1 K2 Cs cD C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ CA CA' fun x i =>
    h CA hC CA' hC' E₀ Eg E₁ E₂ a1 a2 a3 a4 a5 a6 CB Co Cd Cv K1 K2 Cs cD C₁ Cg₁ Cg₂ (Fm.D x i) Gm (hO x i)

def blockThresholdFirst (E₃ : ℝ) : ℝ := if h : 0 ≤ E₃ then (block_family_of_open E₃ h).choose else 0

def blockThresholdSecond (E₃ : ℝ) : ℝ := if h : 0 ≤ E₃ then (block_family_of_open E₃ h).choose_spec.choose else 0

theorem block_theorem_family_at_thresholds {E₃ : ℝ} (hE₃ : 0 ≤ E₃) {CA CA' : ℝ} (hCA : blockThresholdFirst E₃ ≤ CA) (hCA' : blockThresholdSecond E₃ ≤ CA')
    {E₀ Eg E₁ E₂ : ℝ} (h0 : E₀ ≤ CA) (hg : Eg ≤ CA) (h1 : 0 < E₁) (h1' : E₁ ≤ CA) (h2 : 0 < E₂) (h2' : E₂ ≤ CA)
    (CB Co Cd Cv K1 K2 Cs cD C₁ Cg₁ Cg₂ : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Gm : BlockEstimateTheorem.GM)
    (hO : ∀ x (i : Fm.Ix x), OpenAll (Fm.D x i) Gm) :
    BlockEstimateTheorem.KudlaFamilyStatement Fm Gm 5 CB Co Cd Cv K1 K2 Cs cD C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ CA CA' := by
  unfold blockThresholdFirst at hCA
  unfold blockThresholdSecond at hCA'
  rw [dif_pos hE₃] at hCA hCA'
  exact (block_family_of_open E₃ hE₃).choose_spec.choose_spec CA hCA CA' hCA' E₀ Eg E₁ E₂ h0 hg h1 h1' h2 h2'
    CB Co Cd Cv K1 K2 Cs cD C₁ Cg₁ Cg₂ Fm Gm hO

theorem block_statement_uniform_of_open (hO : ∀ (D : D7) (Gm : BlockEstimateTheorem.GM), OpenAll D Gm) : BlockEstimateTheorem.UniformExportStatement := by
  intro Kst CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ E₀ Eg E₁ E₂ E₃ hK h1 h2 h3
  obtain ⟨Ca, Cb, h⟩ := block_statement_of_open Kst hK E₃ h3.le
  refine ⟨max Ca (max E₀ (max Eg (max E₁ E₂))), Cb, fun C hC C' hC' D Gm => ?_⟩
  have b1 : Ca ≤ C := le_trans (le_max_left _ _) hC
  have b2 : max E₀ (max Eg (max E₁ E₂)) ≤ C := le_trans (le_max_right _ _) hC
  have b3 : max Eg (max E₁ E₂) ≤ C := le_trans (le_max_right _ _) b2
  have b4 : max E₁ E₂ ≤ C := le_trans (le_max_right _ _) b3
  exact h C b1 C' hC' E₀ Eg E₁ E₂ (le_trans (le_max_left _ _) b2) (le_trans (le_max_left _ _) b3) h1
    (le_trans (le_max_left _ _) b4) h2 (le_trans (le_max_right _ _) b4) CB Co Cd Cv C1 C2 Cs c C₁ Cg₁ Cg₂ D Gm (hO D Gm)

end Formalism.MainNotions.BlockEstimateWords

end

end PartPack
