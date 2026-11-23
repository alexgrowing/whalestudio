import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsExpEqOfSubstLg
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeNabValBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormEqNegOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open NumberField IsDedekindDomain MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

section Log

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} {σ : Type}

def expPt (G : LogFGL v d) (w : Fin d → MvPowerSeries σ C) : Fin d → MvPowerSeries σ C :=
  fun i => subst w (expOf G i)

def lgPt (G : LogFGL v d) (x : Fin d → MvPowerSeries σ C) : Fin d → MvPowerSeries σ C :=
  fun i => subst x (G.lg i)

def IntLog (G : LogFGL v d) (w : Fin d → MvPowerSeries σ C) : Prop :=
  (∀ i, constantCoeff (w i) = 0) ∧ ∀ i, MvIsInt v (expPt G w i)

def mv (A : Matrix (Fin d) (Fin d) C) (w : Fin d → MvPowerSeries σ C) : Fin d → MvPowerSeries σ C :=
  fun e => ∑ e', A e e' • w e'

def pairSer (G : LogFGL v d) (h : PS C 2 d) (w z : Fin d → MvPowerSeries σ C) : MvPowerSeries σ C :=
  subst (fun q : Fin 2 × Fin d => (![expPt G w, expPt G z] : Fin 2 → Fin d → MvPowerSeries σ C) q.1 q.2) h

def LogUnit [CharZero C] (v : AddValuation C (WithTop ℝ)) (s : MvPowerSeries σ C) : Prop :=
  constantCoeff s = 0 ∧ MvIsInt v (PowerSeries.subst s (PowerSeries.exp C))

variable (G : LogFGL v d)

theorem cc_expPt {w : Fin d → MvPowerSeries σ C} (hw : ∀ i, constantCoeff (w i) = 0) (i : Fin d) :
    constantCoeff (expPt G w i) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hw) hw ((isExp_expOf G).1 i)

theorem cc_lgPt {x : Fin d → MvPowerSeries σ C} (hx : ∀ i, constantCoeff (x i) = 0) (i : Fin d) :
    constantCoeff (lgPt G x i) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hx) hx (G.lg_const i)

theorem cc_mv (A : Matrix (Fin d) (Fin d) C) {w : Fin d → MvPowerSeries σ C} (hw : ∀ i, constantCoeff (w i) = 0)
    (i : Fin d) : constantCoeff (mv A w i) = 0 := by
  simp [mv, hw]

theorem expPt_lgPt {x : Fin d → MvPowerSeries σ C} (hx : ∀ i, constantCoeff (x i) = 0) :
    expPt G (lgPt G x) = x := by
  funext i
  have h := subst_comp_subst_apply (hasSubst_of_constantCoeff_zero G.lg_const) (hasSubst_of_constantCoeff_zero hx)
    (expOf G i)
  rw [subst_lg_expOf, subst_X (hasSubst_of_constantCoeff_zero hx)] at h
  exact h.symm

theorem lgPt_expPt {w : Fin d → MvPowerSeries σ C} (hw : ∀ i, constantCoeff (w i) = 0) :
    lgPt G (expPt G w) = w := by
  funext i
  have h := subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (isExp_expOf G).1)
    (hasSubst_of_constantCoeff_zero hw) (G.lg i)
  rw [(isExp_expOf G).2, subst_X (hasSubst_of_constantCoeff_zero hw)] at h
  exact h.symm

theorem subst_expPt {τ : Type} {t : σ → MvPowerSeries τ C} (ht : HasSubst t) {w : Fin d → MvPowerSeries σ C}
    (hw : ∀ i, constantCoeff (w i) = 0) (i : Fin d) :
    subst t (expPt G w i) = expPt G (fun e => subst t (w e)) i :=
  subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hw) ht _

theorem subst_lgPt {τ : Type} {t : σ → MvPowerSeries τ C} (ht : HasSubst t) {x : Fin d → MvPowerSeries σ C}
    (hx : ∀ i, constantCoeff (x i) = 0) (i : Fin d) :
    subst t (lgPt G x i) = lgPt G (fun e => subst t (x e)) i :=
  subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hx) ht _

theorem subst_mv {τ : Type} {t : σ → MvPowerSeries τ C} (ht : HasSubst t) (A : Matrix (Fin d) (Fin d) C)
    (w : Fin d → MvPowerSeries σ C) (i : Fin d) : subst t (mv A w i) = mv A (fun e => subst t (w e)) i := by
  simp only [mv, ← coe_substAlgHom ht, map_sum, map_smul]

theorem intLog_lgPt_X (s : Fin d → σ) : IntLog G (lgPt G fun i => (X (s i) : MvPowerSeries σ C)) := by
  classical
  refine ⟨cc_lgPt G (by simp), fun i α => ?_⟩
  rw [expPt_lgPt G (by simp)]
  unfold IsIntV
  rw [coeff_X]
  split_ifs <;> simp

end Log

section Biext

variable {C : Type} [Field C] [CharZero C] {d : ℕ} {R : Type} [CommRing R] [Algebra R C]
  {O : Type} [CommRing O] [StarRing O]

def IsIntFB (v : AddValuation C (WithTop ℝ)) (B : FB R d O) : Prop :=
  (∀ a, MvIsInt v (subst (twoVars C d) ((GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G).F a))) ∧
    (∀ a i, MvIsInt v (B.actK C a i)) ∧ MvIsInt v (FB.toK C B.ph1) ∧ MvIsInt v (FB.toK C B.ph2) ∧
    ∀ a, MvIsInt v (FB.toK C (B.ad a))

def fglOf {v : AddValuation C (WithTop ℝ)} {B : FB R d O} (hB : IsIntFB v B) : LogFGL v d :=
  logFGLOf v (GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G) hB.1

def frameSer (B : FB R d O) (h : PS C 2 d) (w0 : O) (n : ℕ) : PS C n d :=
  FB.expS C (∑ b : Fin n, ev (n := n) ![pt C d b] (B.hL C h w0))

end Biext

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
  (Ch : IntegralChartA3 Xo c T io y) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def dActX (a : 𝓞 E) : Matrix (Fin (chD Ch.ch)) (Fin (chD Ch.ch)) X.C :=
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  dAct X.C Ch.ch.B a

def frameX (n : ℕ) : PS X.C n (chD Ch.ch) :=
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  frameSer Ch.ch.B (MvPowerSeries.map X.ιF Ch.ch.h) H.w0 n

theorem mvIsInt_map_map {σ : Type} (f : MvPowerSeries σ T.V) :
    MvIsInt (vX_vp X) (MvPowerSeries.map X.ιF (MvPowerSeries.map (algebraMap T.V T.Fr) f)) := fun α => by
  rw [coeff_map, coeff_map]
  exact isIntV_jX X _

theorem isIntFB_chart :
    letI := io.toAlgebra
    letI : Algebra T.Fr X.C := X.ιF.toAlgebra
    IsIntFB (vX_vp X) Ch.ch.B := by
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  obtain ⟨-, h2, h3, h4, -, h6, -⟩ := Ch.gen.1
  refine ⟨(fgl Ch X).F_int, fun a i => ?_, ?_, ?_, fun a => ?_⟩
  · unfold FB.actK; rw [h2]; exact mvIsInt_map_map X _
  · unfold FB.toK; rw [h3]; exact mvIsInt_map_map X _
  · unfold FB.toK; rw [h4]; exact mvIsInt_map_map X _
  · unfold FB.toK; rw [h6]; exact mvIsInt_map_map X _

theorem fgl_eq_fglOf :
    letI := io.toAlgebra
    letI : Algebra T.Fr X.C := X.ιF.toAlgebra
    fgl Ch X = fglOf (isIntFB_chart Ch X) := rfl

theorem gauge_chart :
    letI := io.toAlgebra
    letI : Algebra T.Fr X.C := X.ιF.toAlgebra
    Ch.ch.B.IsCanonGauge X.C (MvPowerSeries.map X.ιF Ch.ch.h) := by
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  exact (GlobalTheory.canonGauge_nabVal_baseChange T.Fr _ _ Ch.ch.B T.Fr X.C (Algebra.ofId T.Fr X.C) _ Ch.ch.gauge).1

include X in

theorem not_isUnit_p : ¬ IsUnit (p : T.V) := fun h => X.nonunit.out (by simpa using h.map X.ι)

end Chart

def AddSt : Prop :=
  ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (G : LogFGL v d) (σ : Type) [Finite σ],
    IntLog G (0 : Fin d → MvPowerSeries σ C) ∧
    (∀ w w' : Fin d → MvPowerSeries σ C, (∀ i, constantCoeff (w i) = 0) → (∀ i, constantCoeff (w' i) = 0) →
      expPt G (w + w') = fun i => subst (Sum.elim (expPt G w) (expPt G w')) (G.F i)) ∧
    ∀ w w' : Fin d → MvPowerSeries σ C, IntLog G w → IntLog G w' → IntLog G (w + w')

def ActSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (R : Type) [CommRing R] [Algebra R C]
    (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (hB : IsIntFB v B) (σ : Type) [Finite σ] (a : O),
    (∀ w : Fin d → MvPowerSeries σ C, (∀ i, constantCoeff (w i) = 0) →
      expPt (fglOf hB) (mv (dAct C B a) w) =
        fun i => subst (fun q : Fin 1 × Fin d => expPt (fglOf hB) w q.2) (B.actK C a i)) ∧
    ∀ w : Fin d → MvPowerSeries σ C, IntLog (fglOf hB) w → IntLog (fglOf hB) (mv (dAct C B a) w)

def UnitSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (σ : Type) [Finite σ],
    LogUnit v (0 : MvPowerSeries σ C) ∧
    (∀ s t : MvPowerSeries σ C, LogUnit v s → LogUnit v t → LogUnit v (s + t)) ∧
    (∀ s : MvPowerSeries σ C, LogUnit v s → LogUnit v (-s)) ∧
    (∀ s t : MvPowerSeries σ C, constantCoeff s = 0 → constantCoeff t = 0 →
      PowerSeries.subst (s + t) (PowerSeries.exp C) =
        PowerSeries.subst s (PowerSeries.exp C) * PowerSeries.subst t (PowerSeries.exp C)) ∧
    (∀ s : MvPowerSeries σ C, constantCoeff s = 0 → constantCoeff (PowerSeries.subst s (PowerSeries.exp C)) = 1) ∧
    ∀ U : MvPowerSeries σ C, MvIsInt v U → constantCoeff U = 1 → ∃ U', MvIsInt v U' ∧ U * U' = 1

def BiaddSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (R : Type) [CommRing R] [Algebra R C]
    (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (hB : IsIntFB v B) (h : PS C 2 d), B.IsCanonGauge C h →
    ∀ (σ : Type) [Finite σ] (w w' z : Fin d → MvPowerSeries σ C),
      IntLog (fglOf hB) w → IntLog (fglOf hB) w' → IntLog (fglOf hB) z →
      constantCoeff (pairSer (fglOf hB) h w z) = 0 ∧
      LogUnit v (pairSer (fglOf hB) h w z + pairSer (fglOf hB) h w' z - pairSer (fglOf hB) h (w + w') z) ∧
      LogUnit v (pairSer (fglOf hB) h z w + pairSer (fglOf hB) h z w' - pairSer (fglOf hB) h z (w + w')) ∧
      ∀ a : O, LogUnit v (pairSer (fglOf hB) h (mv (dAct C B a) w) z -
        pairSer (fglOf hB) h w (mv (dAct C B (star a)) z))

def FrameSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (R : Type) [CommRing R] [Algebra R C]
    (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (hB : IsIntFB v B) (h : PS C 2 d), B.IsCanonGauge C h →
    ∀ (w0 : O) (n : ℕ), constantCoeff (frameSer B h w0 n) = 1 ∧
      (∀ k : ℕ, FB.expS C ((k : C) • ∑ b : Fin n, ev (n := n) ![pt C d b] (B.hL C h w0)) = frameSer B h w0 n ^ k) ∧
      ∀ (σ : Type) [Finite σ] (y : Fin n → Fin d → MvPowerSeries σ C), (∀ j i, constantCoeff (y j i) = 0) →
        subst (fun q : Fin n × Fin d => expPt (fglOf hB) (y q.1) q.2) (frameSer B h w0 n) =
          PowerSeries.subst (∑ j, pairSer (fglOf hB) h (y j) (mv (dAct C B w0) (y j))) (PowerSeries.exp C)

def FinSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (R : Type) [CommRing R] [Algebra R C]
    (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (hB : IsIntFB v B) (h : PS C 2 d), B.IsCanonGauge C h →
    ∀ (σ : Type) [Finite σ] (κ : Type) [Fintype κ] (w : κ → Fin d → MvPowerSeries σ C),
      (∀ b, IntLog (fglOf hB) (w b)) → ∀ (w0 : O) (n : ℕ) (a : κ → Fin n → O) (ι : Type) [Fintype ι] (e : ι → O)
      (t : κ → κ → ι → ℤ), (∀ b b', (∑ j, star (a b j) * a b' j) * w0 = ∑ i, t b b' i • e i) →
      LogUnit v (∑ j, pairSer (fglOf hB) h (∑ b, mv (dAct C B (a b j)) (w b))
          (mv (dAct C B w0) (∑ b, mv (dAct C B (a b j)) (w b))) -
        ∑ b, ∑ b', ∑ i, (t b b' i : C) • pairSer (fglOf hB) h (w b) (mv (dAct C B (e i)) (w b')))

def ContSt : Prop :=
  ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (τ σ ι : Type) [Fintype τ] [Finite σ] [Fintype ι]
    (W : MvPowerSeries τ C) (g : ι → MvPowerSeries σ C), (∀ i, constantCoeff (g i) = 0) →
    ∀ α : σ →₀ ℕ, ∃ N₀ : ℕ, ∀ s s' : τ → ι → C, (∀ q i, IsIntV v (s q i)) → (∀ q i, IsIntV v (s' q i)) →
      (∀ q i, ((N₀ : ℝ) : WithTop ℝ) ≤ v (s q i - s' q i)) →
      IsIntV v (coeff α (subst (fun q => ∑ i, s q i • g i) W : MvPowerSeries σ C) -
        coeff α (subst (fun q => ∑ i, s' q i • g i) W : MvPowerSeries σ C))

def LimPtSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (R : Type) [CommRing R] [Algebra R C]
    (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (hB : IsIntFB v B)
    (σ : Type) [Finite σ] (κ : Type) [Fintype κ] (w : κ → Fin d → MvPowerSeries σ C),
    (∀ b, IntLog (fglOf hB) (w b)) → ∀ (A : κ → Matrix (Fin d) (Fin d) C) (a : ℕ → κ → O),
    (∀ (N : ℕ) b e e', ((N : ℝ) : WithTop ℝ) ≤ v (A b e e' - dAct C B (a N b) e e')) →
    IntLog (fglOf hB) (∑ b, mv (A b) (w b))

def LimFrameSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), v (p : C) = 1 →
    ∀ (d : ℕ) (R : Type) [CommRing R] [Algebra R C]
    (O : Type) [CommRing O] [StarRing O] [Module.Finite ℤ O] (B : FB R d O) (hB : IsIntFB v B) (h : PS C 2 d),
    B.IsCanonGauge C h → ∀ (σ : Type) [Finite σ] (κ : Type) [Fintype κ] (w : κ → Fin d → MvPowerSeries σ C),
    (∀ b, IntLog (fglOf hB) (w b)) → ∀ (w0 : O) (n : ℕ) (A : κ → Fin n → Matrix (Fin d) (Fin d) C)
      (a : ℕ → κ → Fin n → O),
    (∀ (N : ℕ) b j e e', ((N : ℝ) : WithTop ℝ) ≤ v (A b j e e' - dAct C B (a N b j) e e')) →
    (∀ (N : ℕ) b b', ∑ j, star (a N b j) * a N b' j ∈ Ideal.span {(p : O) ^ N}) →
    MvIsInt v (subst (fun q : Fin n × Fin d => expPt (fglOf hB) (∑ b, mv (A b q.1) (w b)) q.2) (frameSer B h w0 n) :
      MvPowerSeries σ C)

def EpsSt : Prop :=
  ∀ (R V : Type) [CommRing R] [IsDedekindDomain R] [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (φ : R →+* V) (q : R), φ q ≠ 0 → ¬ IsUnit (φ q) →
    ∃ ε : ℕ → R, ∀ N : ℕ, (∃ z, φ (ε N) = 1 + φ q ^ N * z) ∧
      ∀ M ≤ N, ∀ a : R, (∃ z, φ a = φ q ^ M * z) → ε N * a ∈ Ideal.span {q ^ M}

def InvSt : Prop :=
  ∀ (R V : Type) [CommRing R] [IsDedekindDomain R] [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (φ : R →+* V) (q : R), φ q ≠ 0 → ¬ IsUnit (φ q) → ∀ (i : ℕ) (M : Matrix (Fin i) (Fin i) V), IsUnit M.det →
    (∀ b b' (N : ℕ), ∃ a z, φ a = M b b' + φ q ^ N * z) →
    ∃ M' : Matrix (Fin i) (Fin i) V, M * M' = 1 ∧ ∀ b b' (N : ℕ), ∃ a z, φ a = M' b b' + φ q ^ N * z

def PairSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (bar : R ≃+* R), (∀ x, bar (bar x) = x) →
    ∀ (w : Ideal R) [w.IsMaximal] [Finite (R ⧸ w)] (y : R), y - bar y ∉ w → ∀ q : R, q ≠ 0 →
    ∃ u a : ℕ → R, (∀ N : ℕ, u N * bar (u N) + a N * bar (a N) ∈ Ideal.span {q ^ N}) ∧
      ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
        [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (φ : R →+* V),
        (IsLocalRing.maximalIdeal V).comap φ = w → φ q ≠ 0 →
        ∃ α : V, ∀ N : ℕ, (∃ z, φ (u N) = 1 + φ q ^ N * z) ∧ ∃ z, φ (a N) = α + φ q ^ N * z

def InvDerSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (F : FGLaw C d)
    (hF : ∀ a, MvIsInt v (subst (twoVars C d) (F.F a))) (n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n)
    (u : ι → Fin d → C) (P : MvPolynomial ι C) (Φ : PS C n d),
    constantCoeff (DpolyN F.F cp u P Φ) =
      derivAt0 P (subst (fun q : Fin n × Fin d => expPt (logFGLOf v F hF)
        (fun e => ∑ l, (if cp l = q.1 then u l e else 0) • (X l : MvPowerSeries ι C)) q.2) Φ)

def LinSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (ι Λ : Type) [Fintype ι] [Fintype Λ] (β : Λ → ι → C) (P : MvPolynomial Λ C)
    (Ψ : MvPowerSeries ι C),
    derivAt0 (MvPolynomial.aeval (fun lam => ∑ l, MvPolynomial.C (β lam l) * (MvPolynomial.X l : MvPolynomial ι C)) P) Ψ =
      derivAt0 P (subst (fun l => ∑ lam, β lam l • (X lam : MvPowerSeries Λ C)) Ψ)

def ColsSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l)
    (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ColsExist Dw c p la

def LimActSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime]
      (X : ValExt T p) (τ : E →+* ℂ), ∃ ε : ℕ → 𝓞 E, ∀ (t : T.V) (x : ℕ → 𝓞 E),
      (∀ N : ℕ, ∃ z : T.V, io (embK c τ (x N)) = algebraMap T.V T.Fr (t + (p : T.V) ^ N * z)) →
      ∃ A : Matrix (Fin (chD Ch.ch)) (Fin (chD Ch.ch)) X.C,
        (∀ (N : ℕ) e e', ((N : ℝ) : WithTop ℝ) ≤ vX_vp X (A e e' - dActX Ch X (ε N * x N) e e')) ∧
        ∀ i : Fin (Dw.mult τ), A.mulVec (lieVec Ch X ⟨τ, i⟩) = jX X t • lieVec Ch X ⟨τ, i⟩

def NabSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y)
    (p : ℕ) [Fact p.Prime] (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V)
    (k : ℕ) (g : PS X.C n (chD Ch.ch)),
    nabX Ch X cx B k g = derivAt0 (polyH X.C cx) (subst (colPt Ch X cx B) (g * frameX Ch X n ^ k))

def InclSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y)
    (p : ℕ) [Fact p.Prime] (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V),
    IsCols c T io p cx B →
    ∃ ψ : Fin n × Fin (chD Ch.ch) → MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C,
      (∀ q, constantCoeff (ψ q) = 0) ∧ (∀ q, MvIsInt (vX_vp X) (ψ q)) ∧
      (∀ q, subst (expH Ch X cx) (ψ q) = colPt Ch X cx B q) ∧ MvIsInt (vX_vp X) (subst ψ (frameX Ch X n))

def RetrSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y)
    (p : ℕ) [Fact p.Prime] (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V),
    IsCols c T io p cx B →
    ∃ ρ : (Σ _ : Col cx, Fin (chD Ch.ch)) → PS X.C n (chD Ch.ch),
      (∀ q, constantCoeff (ρ q) = 0) ∧ (∀ q, MvIsInt (vX_vp X) (ρ q)) ∧
      ∀ q, subst (colPt Ch X cx B) (ρ q) = expH Ch X cx q

def BaseSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y)
    (p : ℕ) [Fact p.Prime] (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V)
    (k e : ℕ), vV T.V (p : T.Fr) = e → nuLocOf Ch e k (polyT B cx) = nuLocX_vp Ch X cx B k

end GlobalTheory.IsoTriv
