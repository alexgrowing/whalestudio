import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.OpLocal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

set_option linter.unusedSectionVars false

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms

open Formalism.FourierDecayAlt.P.CutMP

section defs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def FFB (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) : Set (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) :=
  Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs)

def IsGaugeQQB (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
    ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
      MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
        MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ

def PInv (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (o κ : ℕ) (Θ : B.DiffOp P.k P.r Wp Wq) : Prop :=
  CutMP.PolyOp o κ Θ ∧ B.Commutes Bs (B.GPos Bs) Θ

def RealF (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (o κ : ℕ)
    (Φ : (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → M.Ty P → MA.SmQ P.r P.TT) : Prop :=
  ∃ ts : List (MA.A P (MA.DQ P) × B.DiffOp P.k P.r Wp Wq),
    (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet P L) ∧ PInv P Bs o κ t.2) ∧
    ∀ J ∈ FFB P Bs, Φ J = (ts.map fun t => MA.actA P t.1 (Gauge.trJB P Bs e (B.opApply t.2 J))).sum

def IsTr (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (X : MA.A P (MA.DQ P)) : Prop :=
  ∃ Θ : B.DiffOp P.k P.r Wp Wq, PInv P Bs (2 * P.r + P.k + 1) ((P.r + 1) * (2 * P.r + P.k + 1)) Θ ∧
    ∀ J ∈ FFB P Bs, Gauge.trJB P Bs e (B.opApply Θ J) = MA.actA P X (Gauge.trJB P Bs e J)

end defs

def CapAB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    ∀ L : R.LevelData (MA.A P (MA.DQ P)) P.r, MA.IsModelLevel P (MA.DQ P) L →
    ∀ y : ℂ, IsTr P Bs e (L.Ahat y) ∧ IsTr P Bs e (L.Ahatv y)

def CapRB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    IsGaugeQQB P Bs e → ∀ L : R.LevelData (MA.A P (MA.DQ P)) P.r, MA.IsModelLevel P (MA.DQ P) L →
    ∀ y : ℝ, IsTr P Bs e (RhM P L y) ∧ IsTr P Bs e (RhvM P L y)

def HatProdB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    IsGaugeQQB P Bs e → ∀ L : R.LevelData (MA.A P (MA.DQ P)) P.r, MA.IsModelLevel P (MA.DQ P) L →
    ∀ w : List (MA.A P (MA.DQ P)), (∀ a ∈ w, a ∈ MA.hatSet P L) →
      RealF P Bs e L (w.length * (2 * P.r + P.k + 1)) (w.length * ((P.r + 1) * (2 * P.r + P.k + 1)))
        (fun J => MA.actA P w.prod (Gauge.trJB P Bs e J))

section place

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem isDom_omB {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) : Q.IsDom k r Bs.z Bs.z' 0 (Gauge.OmB Bs) := by
  refine ⟨?_, ?_⟩
  · have e : Gauge.OmB Bs = {g | 0 < Gf k r Bs.z Bs.z' g} ∩
        ⋂ a : Fin r, {g | Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
      ext g; simp [Gauge.OmB]
    rw [e]
    exact (isOpen_lt continuous_const (BetaSesquilinearity.Gf_cont _ _)).inter
      (isOpen_iInter_of_finite fun a => isOpen_ne_fun (BetaSesquilinearity.Dmin_cont _ _ _) continuous_const)
  · rintro g ⟨-, hg⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    have hs : h * m ∈ Sset k r Bs.z := ⟨h, hh, m, hm.1, rfl⟩
    have hs' : h' * m' ∈ Sset k r Bs.z' := ⟨h', hh', m', hm'.1, rfl⟩
    refine ⟨?_, fun a => ?_⟩
    · rw [gInv k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem _ hs _ hs' g]; exact hg.1
    · rw [dInv k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem _ hs _ hs' g]; exact hg.2 a

variable {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem tt_eq (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') : P.TT = Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' := by
  rw [hpl.2.2.2.1, hpl.2.2.2.2.1]; rfl

theorem gq_mem (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT) :
    B.gq Bs q.1 ∈ B.GV P.k P.r ∩ Gauge.OmB Bs := by
  have h := BigCellHermitian.gqDom Bs (q := q.1) ⟨q.2.1, by rw [← tt_eq hpl]; exact q.2.2⟩
  exact ⟨h.1, h.2.2, fun a => h.2.1 _ (by simp)⟩

theorem trJB_congr (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    {J J' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (h : ∀ g ∈ B.GV P.k P.r ∩ Gauge.OmB Bs, J g = J' g) :
    Gauge.trJB P Bs e J = Gauge.trJB P Bs e J' := by
  funext ρ
  unfold Gauge.trJB
  congr 1
  funext q
  unfold Gauge.rawJ
  rw [h _ (gq_mem hpl q)]

theorem ffb_op {o κ : ℕ} {Θ : B.DiffOp P.k P.r Wp Wq} (h : PInv P Bs o κ Θ) {J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ FFB P Bs) : B.opApply Θ J ∈ FFB P Bs :=
  ffl_opApply Bs (UU := B.GPos Bs) (isDom_omB Bs) (fun _ hg hG => ⟨hG, hg.1⟩) (polyOp_ck h.1 _) h.2 hJ

theorem pInv_comp {o₁ κ₁ o₂ κ₂ : ℕ} {Θ₁ Θ₂ : B.DiffOp P.k P.r Wp Wq} (h₁ : PInv P Bs o₁ κ₁ Θ₁)
    (h₂ : PInv P Bs o₂ κ₂ Θ₂) : ∃ Θ : B.DiffOp P.k P.r Wp Wq, PInv P Bs (o₁ + o₂) (κ₁ + κ₂) Θ ∧
      ∀ J ∈ FFB P Bs, ∀ g ∈ B.GV P.k P.r ∩ Gauge.OmB Bs, B.opApply Θ J g = B.opApply Θ₁ (B.opApply Θ₂ J) g := by
  obtain ⟨Θ, hP, hl, hc⟩ := polyOp_comp h₁.1 h₂.1
  refine ⟨Θ, ⟨hP, hc Bs {g | 0 < Gf P.k P.r Bs.z Bs.z' g} (isOpen_lt continuous_const (BetaSesquilinearity.Gf_cont _ _)) h₁.2 h₂.2⟩,
    fun J hJ g hg => hl _ J (BetaSesquilinearity.sCkOn_mono le_top (ck_of_smoothLev hJ.1)) g hg hg.1⟩

variable {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)} {L : R.LevelData (MA.A P (MA.DQ P)) P.r} {o κ : ℕ}

theorem realF_congr {Φ Ψ : (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → M.Ty P → MA.SmQ P.r P.TT}
    (h : ∀ J ∈ FFB P Bs, Ψ J = Φ J) (hΦ : RealF P Bs e L o κ Φ) : RealF P Bs e L o κ Ψ := by
  obtain ⟨ts, h1, h2⟩ := hΦ
  exact ⟨ts, h1, fun J hJ => (h J hJ).trans (h2 J hJ)⟩

theorem realF_zero : RealF P Bs e L o κ (fun _ => 0) :=
  ⟨[], fun _ ht => absurd ht List.not_mem_nil, fun _ _ => rfl⟩

theorem realF_add {Φ Ψ : (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → M.Ty P → MA.SmQ P.r P.TT}
    (hΦ : RealF P Bs e L o κ Φ) (hΨ : RealF P Bs e L o κ Ψ) : RealF P Bs e L o κ (fun J => Φ J + Ψ J) := by
  obtain ⟨ts, hts, hJ⟩ := hΦ
  obtain ⟨ts', hts', hJ'⟩ := hΨ
  refine ⟨ts ++ ts', fun t ht => ?_, fun J hJJ => ?_⟩
  · rcases List.mem_append.1 ht with h | h
    · exact hts t h
    · exact hts' t h
  · rw [List.map_append, List.sum_append, ← hJ J hJJ, ← hJ' J hJJ]

theorem realF_act {b : MA.A P (MA.DQ P)} (hb : b ∈ Submonoid.closure (MA.bddSet P L))
    {Φ : (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → M.Ty P → MA.SmQ P.r P.TT} (hΦ : RealF P Bs e L o κ Φ) :
    RealF P Bs e L o κ (fun J => MA.actA P b (Φ J)) := by
  obtain ⟨ts, hts, hJ⟩ := hΦ
  refine ⟨ts.map fun t => (b * t.1, t.2), fun t ht => ?_, fun J hJJ => ?_⟩
  · obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact ⟨Submonoid.mul_mem _ hb (hts t' ht').1, (hts t' ht').2⟩
  · show MA.actA P b (Φ J) = _
    rw [hJ J hJJ, jdh_actA_listsum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply]
    rw [Gauge.actA_mul]

theorem realF_listsum {ι : Type} (l : List ι)
    (Φ : ι → (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → M.Ty P → MA.SmQ P.r P.TT)
    (h : ∀ i ∈ l, RealF P Bs e L o κ (Φ i)) : RealF P Bs e L o κ (fun J => (l.map fun i => Φ i J).sum) := by
  induction l with
  | nil => exact realF_zero
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact realF_add (h i (by simp)) (ih fun j hj => h j (by simp [hj]))

theorem realF_comp (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') {o' κ' : ℕ} {Θ : B.DiffOp P.k P.r Wp Wq}
    (hΘ : PInv P Bs o' κ' Θ) {Φ : (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) → M.Ty P → MA.SmQ P.r P.TT}
    (hΦ : RealF P Bs e L o κ Φ) : RealF P Bs e L (o + o') (κ + κ') (fun J => Φ (B.opApply Θ J)) := by
  obtain ⟨ts, hts, hJ⟩ := hΦ
  refine realF_congr (fun J hJJ => hJ _ (ffb_op hΘ hJJ)) (realF_listsum ts
    (fun t J => MA.actA P t.1 (Gauge.trJB P Bs e (B.opApply t.2 (B.opApply Θ J)))) fun t ht => ?_)
  obtain ⟨Θ', h1, h2⟩ := pInv_comp (hts t ht).2 hΘ
  refine ⟨[(t.1, Θ')], fun t' ht' => ?_, fun J hJJ => ?_⟩
  · rw [List.mem_singleton] at ht'
    subst ht'
    exact ⟨(hts t ht).1, h1⟩
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [trJB_congr hpl e (h2 J hJJ)]

variable (P Bs e L o κ) in

def RealX (X : MA.A P (MA.DQ P)) : Prop := RealF P Bs e L o κ (fun J => MA.actA P X (Gauge.trJB P Bs e J))

theorem realX_zero : RealX P Bs e L o κ 0 :=
  realF_congr (fun _ _ => Gauge.actA_zero _ _) realF_zero

theorem realX_add {X Y : MA.A P (MA.DQ P)} (hX : RealX P Bs e L o κ X) (hY : RealX P Bs e L o κ Y) :
    RealX P Bs e L o κ (X + Y) :=
  realF_congr (fun _ _ => Gauge.actA_add _ _ _ _) (realF_add hX hY)

theorem realX_mul {b X : MA.A P (MA.DQ P)} (hb : b ∈ Submonoid.closure (MA.bddSet P L))
    (hX : RealX P Bs e L o κ X) : RealX P Bs e L o κ (b * X) :=
  realF_congr (fun _ _ => Gauge.actA_mul _ _ _ _) (realF_act hb hX)

theorem realX_smul (c : ℂ) {X : MA.A P (MA.DQ P)} (hX : RealX P Bs e L o κ X) : RealX P Bs e L o κ (c • X) := by
  rw [jdh_smul_eq]
  exact realX_mul (jdh_kap_mem _ L _) hX

theorem realX_sub {X Y : MA.A P (MA.DQ P)} (hX : RealX P Bs e L o κ X) (hY : RealX P Bs e L o κ Y) :
    RealX P Bs e L o κ (X - Y) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ Y]
  exact realX_add hX (realX_smul _ hY)

theorem realX_sum {ι : Type} (s : Finset ι) (X : ι → MA.A P (MA.DQ P)) (h : ∀ i ∈ s, RealX P Bs e L o κ (X i)) :
    RealX P Bs e L o κ (∑ i ∈ s, X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact realX_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact realX_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem realX_of_isTr {X : MA.A P (MA.DQ P)} (h : IsTr P Bs e X) :
    RealX P Bs e L (2 * P.r + P.k + 1) ((P.r + 1) * (2 * P.r + P.k + 1)) X := by
  obtain ⟨Θ, h1, h2⟩ := h
  refine ⟨[(1, Θ)], fun t ht => ?_, fun J hJ => ?_⟩
  · rw [List.mem_singleton] at ht
    subst ht
    exact ⟨Submonoid.one_mem _, h1⟩
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [jdh_actA_one, h2 J hJ]

theorem realX_one : RealX P Bs e L 0 0 1 := by
  obtain ⟨Θ, h1, h2, h3⟩ := polyOp_one (k := P.k) (r := P.r) (Wp := Wp) (Wq := Wq)
  refine ⟨[(1, Θ)], fun t ht => ?_, fun J _ => ?_⟩
  · rw [List.mem_singleton] at ht
    subst ht
    exact ⟨Submonoid.one_mem _, h1, h3 _ _⟩
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [h2]

theorem realX_hat (h1 : ResidueSplittingModelAlgebra) (h2 : MirrorResidueSplittingModelAlgebra) (h3 : JDHatLagrange) (h4 : JDHatNodes)
    (hL : MA.IsModelLevel P (MA.DQ P) L) (hA : ∀ y : ℂ, IsTr P Bs e (L.Ahat y) ∧ IsTr P Bs e (L.Ahatv y))
    (hR : ∀ y : ℝ, IsTr P Bs e (RhM P L y) ∧ IsTr P Bs e (RhvM P L y)) :
    ∀ X ∈ MA.hatSet P L, RealX P Bs e L (2 * P.r + P.k + 1) ((P.r + 1) * (2 * P.r + P.k + 1)) X := by
  intro X hX
  obtain ⟨ν, hinj, hreg⟩ := h4 P
  rcases hX with (((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩)
  · exact realX_of_isTr (hA y).1
  · rw [(h3 P L ν hinj y).1]
    refine realX_sum _ _ fun j _ => realX_smul _ ?_
    rw [h1 P L hL (ν j) (hreg j)]
    refine realX_sub (realX_mul (jdh_kap_mem _ L _) (realX_of_isTr (hR (ν j)).1)) (realX_sum _ _ fun l hl => ?_)
    refine realX_mul ?_ (realX_of_isTr (hA _).1)
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (jdh_kap_mem _ L _) (jdh_SSn_mem _ L l hl)) (jdh_kap_mem _ L _)
  · exact realX_of_isTr (hA y).2
  · rw [(h3 P L ν hinj y).2]
    refine realX_sum _ _ fun j _ => realX_smul _ ?_
    rw [h2 P L hL (ν j) (hreg j)]
    refine realX_sub (realX_mul (jdh_kap_mem _ L _) (realX_of_isTr (hR (ν j)).2)) (realX_sum _ _ fun l hl => ?_)
    refine realX_mul ?_ (realX_of_isTr (hA _).2)
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (jdh_kap_mem _ L _) (jdh_kap_mem _ L _)) (jdh_SSns_mem _ L l hl)

theorem realX_prod (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (hBdd : ∀ X ∈ MA.hatSet P L, ∀ b ∈ Submonoid.closure (MA.bddSet P L), X * b ∈ Submodule.span ℂ (bddHat P L))
    (hHat : ∀ X ∈ MA.hatSet P L, RealX P Bs e L o κ X) :
    ∀ w : List (MA.A P (MA.DQ P)), (∀ a ∈ w, a ∈ MA.hatSet P L) →
      RealX P Bs e L (w.length * o) (w.length * κ) w.prod := by
  have hspan : ∀ c ∈ Submodule.span ℂ (bddHat P L), RealX P Bs e L o κ c := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, X, hX, rfl⟩ := hx
      exact realX_mul hb (hHat X hX)
    | zero => exact realX_zero
    | add x y _ _ h1 h2 => exact realX_add h1 h2
    | smul c x _ h1 => exact realX_smul c h1
  intro w
  induction w with
  | nil => intro _; simpa using realX_one
  | cons a w ih =>
    intro hw
    obtain ⟨ts, hts, hJ⟩ := ih fun x hx => hw x (List.mem_cons_of_mem _ hx)
    have ha := hw a (List.mem_cons_self ..)
    have e1 : (a :: w).length * o = o + w.length * o := by rw [List.length_cons]; ring
    have e2 : (a :: w).length * κ = κ + w.length * κ := by rw [List.length_cons]; ring
    rw [e1, e2]
    refine realF_congr (fun J hJJ => ?_) (realF_listsum ts
      (fun t J => MA.actA P (a * t.1) (Gauge.trJB P Bs e (B.opApply t.2 J))) fun t ht =>
        realF_comp hpl (hts t ht).2 (hspan _ (hBdd a ha _ (hts t ht).1)))
    have hJ' : MA.actA P w.prod (Gauge.trJB P Bs e J) = _ := hJ J hJJ
    show MA.actA P (a :: w).prod (Gauge.trJB P Bs e J) = _
    rw [List.prod_cons, Gauge.actA_mul, hJ', jdh_actA_listsum]
    congr 1
    apply List.map_congr_left
    intro t _
    rw [Gauge.actA_mul]

end place

theorem hatProdB_of (hA : CapAB) (hR : CapRB) (h0 : JDHatBdd) (h1 : ResidueSplittingModelAlgebra) (h2 : MirrorResidueSplittingModelAlgebra)
    (h3 : JDHatLagrange) (h4 : JDHatNodes) : HatProdB := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he hQ L hL w hw
  have hTT : 0 ≤ P.TT := by rw [tt_eq hpl]; exact (mul_pos Bs.T_pos Bs.T'_pos).le
  exact realX_prod hpl (h0 P L hTT hL)
    (realX_hat h1 h2 h3 h4 hL (hA Wp Wq P Bs hpl hk e he L hL) (hR Wp Wq P Bs hpl hk e he hQ L hL)) w hw

end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
