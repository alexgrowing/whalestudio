import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeCut

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section model

variable (P : M.Par)

def RhM (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (y : ℂ) : MA.A P (MA.DQ P) :=
  L.Drb * (MA.t21 P (MA.DQ P) y * L.Ar y + MA.t22 P (MA.DQ P) y * L.Br y)

def RhvM (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (y : ℂ) : MA.A P (MA.DQ P) :=
  L.Dr * (MA.t12 P (MA.DQ P) y * L.Avr y + MA.t22 P (MA.DQ P) y * L.Bvr y)

def xInvM (y : ℂ) : MA.A P (MA.DQ P) := MA.kap P (MA.DQ P) fun π => (M.xC P π y)⁻¹

def SSn (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (l : ℕ) : MA.A P (MA.DQ P) :=
  L.Drb * L.Dri * MA.SS P (MA.DQ P) l

def RegY (y : ℂ) : Prop := ∀ π : M.Ty P, M.xC P π y ≠ 0

end model

def lagC {m : ℕ} (ν : Fin m → ℝ) (j : Fin m) (y : ℂ) : ℂ :=
  ∏ i ∈ Finset.univ.erase j, (y - (ν i : ℂ)) / ((ν j : ℂ) - (ν i : ℂ))

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def HatOK (Cc : ℝ) (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) : Prop :=
  B.SmoothCoef (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θ ∧
    GlobCoef Θ (Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) ∧ (B.opOrder Θ : ℝ) ≤ Cc * nDim S.G.k S.G.r

def IsGaugeQQ (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : Prop :=
  ∀ (Dc : (Fin (D.parOf S v).r → ℂ) → Set (Q.Mx (D.parOf S v).k (D.parOf S v).r))
    (Φ : Q.Fn (D.parOf S v).k (D.parOf S v).r (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
    Gauge.FamR (D.parOf S v) (T v).base Dc Φ →
    ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty (D.parOf S v)),
      MA.toSm (D.parOf S v) (Gauge.rawR (D.parOf S v) (T v).base.μsec e
          (Q.QL (D.parOf S v).k (D.parOf S v).r (T v).base.z (T v).base.z' (Fin.last (D.parOf S v).r) (Y : ℂ) a b Φ) ρ) =
        MA.actA (D.parOf S v) (MA.QQr (D.parOf S v) (MA.DQ (D.parOf S v)) (Y : ℂ) a b)
          (fun ρ' => MA.toSm (D.parOf S v) (Gauge.rawR (D.parOf S v) (T v).base.μsec e Φ ρ')) ρ

end defs

def ResidueSplittingModelAlgebra : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), MA.IsModelLevel P (MA.DQ P) L → ∀ y : ℂ, RegY P y →
    L.R0 y = xInvM P y * RhM P L y -
      ∑ l ∈ Finset.Icc 1 (P.k - 1),
        xInvM P y * SSn P L l * MA.kap P (MA.DQ P) (fun π => M.xEx P {l} π y) * L.Ahat y

def MirrorResidueSplittingModelAlgebra : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), MA.IsModelLevel P (MA.DQ P) L → ∀ y : ℂ, RegY P y →
    L.R0v y = xInvM P y * RhvM P L y -
      ∑ l ∈ Finset.Icc 1 (P.k - 1),
        xInvM P y * MA.kap P (MA.DQ P) (fun π => M.xEx P {l} π y) * star (SSn P L l) * L.Ahatv y

def JDHatLagrange : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (ν : Fin (P.r + 2) → ℝ), Function.Injective ν → ∀ y : ℂ,
    L.R0 y = ∑ j, lagC ν j y • L.R0 (ν j) ∧ L.R0v y = ∑ j, lagC ν j y • L.R0v (ν j)

def JDHatNodes : Prop :=
  ∀ P : M.Par, ∃ ν : Fin (P.r + 2) → ℝ, Function.Injective ν ∧ ∀ j, RegY P (ν j)

def JDOpA : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc : ℝ, K ≤ Cc → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L → ∀ y : ℂ,
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)), HatOK Cc S T v Θ ∧ HatOK Cc S T v Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          trJ S T v e (B.opApply Θ J) = MA.actA (D.parOf S v) (L.Ahat y) (trJ S T v e J) ∧
          trJ S T v e (B.opApply Θv J) = MA.actA (D.parOf S v) (L.Ahatv y) (trJ S T v e J)

def JDOpR : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc : ℝ, K ≤ Cc → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L → ∀ y : ℝ,
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)), HatOK Cc S T v Θ ∧ HatOK Cc S T v Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          trJ S T v e (B.opApply Θ J) = MA.actA (D.parOf S v) (RhM (D.parOf S v) L y) (trJ S T v e J) ∧
          trJ S T v e (B.opApply Θv J) = MA.actA (D.parOf S v) (RhvM (D.parOf S v) L y) (trJ S T v e J)

def JDGaugeQQ : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e

section gen

variable (P : M.Par)

theorem jdh_actA_one (f : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 1 f = f := by
  funext π
  show ∑ π', ((1 : MA.A P (MA.DQ P)) π π').1 (f π') = f π
  rw [Finset.sum_eq_single π (fun π' _ h => by rw [Matrix.one_apply_ne (Ne.symm h)]; rfl)
    (fun h => absurd (Finset.mem_univ π) h), Matrix.one_apply_eq]
  rfl

theorem jdh_actA_zeroR (a : MA.A P (MA.DQ P)) : MA.actA P a 0 = 0 := by
  funext π
  show ∑ π', (a π π').1 0 = 0
  exact Finset.sum_eq_zero fun π' _ => map_zero _

theorem jdh_actA_addR (a : MA.A P (MA.DQ P)) (x y : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (x + y) = MA.actA P a x + MA.actA P a y := by
  funext π
  show ∑ π', (a π π').1 (x π' + y π') = ∑ π', (a π π').1 (x π') + ∑ π', (a π π').1 (y π')
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => map_add _ _ _

theorem jdh_actA_listsum {ι : Type} (a : MA.A P (MA.DQ P)) (l : List ι) (g : ι → M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (l.map g).sum = (l.map fun i => MA.actA P a (g i)).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil]; exact jdh_actA_zeroR P a
  | cons i l ih => simp only [List.map_cons, List.sum_cons]; rw [jdh_actA_addR, ih]

theorem jdh_kap_mem (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (g : M.Ty P → ℂ) :
    MA.kap P (MA.DQ P) g ∈ Submonoid.closure (MA.bddSet P L) :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨g, rfl⟩)))

theorem jdh_SSn_mem (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (l : ℕ) (hl : l ∈ Finset.Icc 1 (P.k - 1)) :
    SSn P L l ∈ Submonoid.closure (MA.bddSet P L) :=
  Submonoid.subset_closure (Or.inl (Or.inr ⟨l, Finset.mem_Icc.1 hl, rfl⟩))

theorem jdh_SSns_mem (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (l : ℕ) (hl : l ∈ Finset.Icc 1 (P.k - 1)) :
    star (SSn P L l) ∈ Submonoid.closure (MA.bddSet P L) :=
  Submonoid.subset_closure (Or.inr ⟨l, Finset.mem_Icc.1 hl, rfl⟩)

theorem jdh_smul_eq (c : ℂ) (a : MA.A P (MA.DQ P)) : c • a = MA.kap P (MA.DQ P) (fun _ => c) * a := by
  rw [Algebra.smul_def, ← (MA.kap P (MA.DQ P)).commutes c]
  rfl

end gen

section realise

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cc : ℝ} {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
  {v : Fin S.f} {e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))}
  {L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r}

variable (Cc S T v e L) in

def HReal (X : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) : Prop :=
  ∃ ts : List (MA.A (D.parOf S v) (MA.DQ (D.parOf S v)) × B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))),
    (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) ∧ HatOK Cc S T v t.2) ∧
    ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
      MA.actA (D.parOf S v) X (trJ S T v e J) =
        (ts.map fun t => MA.actA (D.parOf S v) t.1 (trJ S T v e (B.opApply t.2 J))).sum

theorem hReal_op {X : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))} (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (hΘ : HatOK Cc S T v Θ)
    (h : ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
      trJ S T v e (B.opApply Θ J) = MA.actA (D.parOf S v) X (trJ S T v e J)) :
    HReal Cc S T v e L X := by
  refine ⟨[(1, Θ)], fun t ht => ?_, fun J hJ => ?_⟩
  · rw [List.mem_singleton] at ht
    subst ht
    exact ⟨Submonoid.one_mem _, hΘ⟩
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [jdh_actA_one, h J hJ]

theorem hReal_zero : HReal Cc S T v e L 0 :=
  ⟨[], fun t ht => absurd ht List.not_mem_nil, fun J _ => by
    simp only [List.map_nil, List.sum_nil]; exact Gauge.actA_zero _ _⟩

theorem hReal_add {X Y : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))} (hX : HReal Cc S T v e L X)
    (hY : HReal Cc S T v e L Y) : HReal Cc S T v e L (X + Y) := by
  obtain ⟨ts, hts, hJ⟩ := hX
  obtain ⟨ts', hts', hJ'⟩ := hY
  refine ⟨ts ++ ts', fun t ht => ?_, fun J hJJ => ?_⟩
  · rcases List.mem_append.1 ht with h | h
    · exact hts t h
    · exact hts' t h
  · rw [Gauge.actA_add, hJ J hJJ, hJ' J hJJ, List.map_append, List.sum_append]

theorem hReal_mul {b X : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))}
    (hb : b ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L)) (hX : HReal Cc S T v e L X) :
    HReal Cc S T v e L (b * X) := by
  obtain ⟨ts, hts, hJ⟩ := hX
  refine ⟨ts.map fun t => (b * t.1, t.2), fun t ht => ?_, fun J hJJ => ?_⟩
  · obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact ⟨Submonoid.mul_mem _ hb (hts t' ht').1, (hts t' ht').2⟩
  · rw [Gauge.actA_mul, hJ J hJJ, jdh_actA_listsum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply]
    rw [Gauge.actA_mul]

theorem hReal_sum {ι : Type} (s : Finset ι) (X : ι → MA.A (D.parOf S v) (MA.DQ (D.parOf S v)))
    (h : ∀ i ∈ s, HReal Cc S T v e L (X i)) : HReal Cc S T v e L (∑ i ∈ s, X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact hReal_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hReal_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem hReal_smul (c : ℂ) {X : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))} (hX : HReal Cc S T v e L X) :
    HReal Cc S T v e L (c • X) := by
  rw [jdh_smul_eq]
  exact hReal_mul (jdh_kap_mem _ L _) hX

theorem hReal_sub {X Y : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))} (hX : HReal Cc S T v e L X)
    (hY : HReal Cc S T v e L Y) : HReal Cc S T v e L (X - Y) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ Y]
  exact hReal_add hX (hReal_smul _ hY)

end realise

theorem jDHatOp_of_hatLeaves (hA : JDOpA) (hR : JDOpR) (hG : JDGaugeQQ) (h1 : ResidueSplittingModelAlgebra) (h2 : MirrorResidueSplittingModelAlgebra)
    (h3 : JDHatLagrange) (h4 : JDHatNodes) : JDHatOp := by
  obtain ⟨KA, hKA0, hA⟩ := hA
  obtain ⟨KR, -, hR⟩ := hR
  refine ⟨max KA KR, le_max_of_le_left hKA0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hL X hX
  have hQQ := hG (max KA KR) E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa
  have hA' := hA (max KA KR) (le_max_left _ _) E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hL
  have hR' := hR (max KA KR) (le_max_right _ _) E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hQQ hL
  suffices hH : HReal (max KA KR) S T v e L X by
    obtain ⟨ts, hts, hJ⟩ := hH
    exact ⟨ts, hts, hJ⟩
  have rA : ∀ y : ℂ, HReal (max KA KR) S T v e L (L.Ahat y) := fun y => by
    obtain ⟨Θ, Θv, hΘ, -, h⟩ := hA' y
    exact hReal_op Θ hΘ fun J hJ => (h J hJ).1
  have rAv : ∀ y : ℂ, HReal (max KA KR) S T v e L (L.Ahatv y) := fun y => by
    obtain ⟨Θ, Θv, -, hΘv, h⟩ := hA' y
    exact hReal_op Θv hΘv fun J hJ => (h J hJ).2
  have rR : ∀ y : ℝ, HReal (max KA KR) S T v e L (RhM (D.parOf S v) L y) := fun y => by
    obtain ⟨Θ, Θv, hΘ, -, h⟩ := hR' y
    exact hReal_op Θ hΘ fun J hJ => (h J hJ).1
  have rRv : ∀ y : ℝ, HReal (max KA KR) S T v e L (RhvM (D.parOf S v) L y) := fun y => by
    obtain ⟨Θ, Θv, -, hΘv, h⟩ := hR' y
    exact hReal_op Θv hΘv fun J hJ => (h J hJ).2
  obtain ⟨ν, hinj, hreg⟩ := h4 (D.parOf S v)
  rcases hX with (((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩)
  · exact rA y
  · rw [(h3 (D.parOf S v) L ν hinj y).1]
    refine hReal_sum _ _ fun j _ => hReal_smul _ ?_
    rw [h1 (D.parOf S v) L hL (ν j) (hreg j)]
    refine hReal_sub (hReal_mul (jdh_kap_mem _ L _) (rR (ν j))) (hReal_sum _ _ fun l hl => ?_)
    refine hReal_mul ?_ (rA _)
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (jdh_kap_mem _ L _) (jdh_SSn_mem _ L l hl)) (jdh_kap_mem _ L _)
  · exact rAv y
  · rw [(h3 (D.parOf S v) L ν hinj y).2]
    refine hReal_sum _ _ fun j _ => hReal_smul _ ?_
    rw [h2 (D.parOf S v) L hL (ν j) (hreg j)]
    refine hReal_sub (hReal_mul (jdh_kap_mem _ L _) (rRv (ν j))) (hReal_sum _ _ fun l hl => ?_)
    refine hReal_mul ?_ (rAv _)
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (jdh_kap_mem _ L _) (jdh_kap_mem _ L _)) (jdh_SSns_mem _ L l hl)

end

end Formalism.FourierDecayAlt.P.CutMP
