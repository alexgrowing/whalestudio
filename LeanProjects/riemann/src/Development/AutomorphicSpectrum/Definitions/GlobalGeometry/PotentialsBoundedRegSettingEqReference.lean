import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open AlgebraicGeometry CategoryTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
open ReciprocityTheory.AnForm.M (LocPot)

section Free

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  (D : ComponentData II Ψ K J Ω W)

def offBd (a : Fin D.nCharts) : Set (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) :=
  {t | t ∈ Metric.ball 0 1 ∧ (D.chart a).γ t ∉ D.Bd}

def ChartPsh (w : ((Σ k, J k) → ℂ) → ℝ) : Prop :=
  ∀ a, ReciprocityTheory.AnForm.A.IsPsh (offBd D a) fun t => w ((D.chart a).γ t)

def ChartCont (w : ((Σ k, J k) → ℂ) → ℝ) : Prop :=
  ∀ a, ContinuousOn (fun t => w ((D.chart a).γ t)) (offBd D a)

def ChartBdd (w : ((Σ k, J k) → ℂ) → ℝ) : Prop :=
  ∀ a, ∀ t₀ ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, ∃ ε > (0 : ℝ), ∃ C : ℝ,
    ∀ t ∈ offBd D a, ‖t - t₀‖ < ε → |w ((D.chart a).γ t)| ≤ C

def LogHom (a : K → ℤ) (w : ((Σ k, J k) → ℂ) → ℝ) : Prop :=
  ∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → w (torusSmul c z) = w z + ∑ k, (a k : ℝ) * Real.log ‖c k‖

def ConjOff (w : ((Σ k, J k) → ℂ) → ℝ) : Prop := ∀ z ∈ D.Xo, w (conjVec z) = w z

variable {D} (M : XModel D)

def ThRef (ref : HermLine J) (th : LocPot M.Xc) : Prop :=
  ∀ x, ∀ y ∈ th.U x, ∃ U : Set M.Xc, IsOpen U ∧ y ∈ U ∧ U ⊆ th.U x ∧
    ∃ s : M.Xc → (Σ k, J k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (s y') = y') ∧
      (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧
        ∀ y' ∈ U, th.φ x y' - Real.log (ref.h (s y')) = (G y').re

def Adapted (P : PotentialCharts M.atlas) (S : Fin P.N → Finset (Fin D.n)) : Prop :=
  ∀ j, ∀ z ∈ mcPts (mCoordIdeal D.y), M.proj z ∈ (P.chart j).source →
    (z ∈ D.Bd ↔ P.chart j (M.proj z) ∈ ReciprocityTheory.AnForm.A.coordDiv (S j))

def FromSnc (P : PotentialCharts M.atlas) : Prop :=
  ∀ j, (P.chart j).target = Metric.ball 0 1 ∧
    ∃ (a : Fin D.nCharts) (t₀ : Fin D.n → ℂ) (ε : ℝ), ‖t₀‖ ≤ 1 / 2 ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧
      (∀ i : Fin D.n, (i : ℕ) < (D.chart a).a → t₀ i ≠ 0 → 2 * ε ≤ ‖t₀ i‖) ∧
      ((∀ t ∈ (P.chart j).target, (P.chart j).symm t = M.proj ((D.chart a).γ (t₀ + (ε : ℂ) • t))) ∨
        ∀ t ∈ (P.chart j).target, (P.chart j).symm t = M.proj (conjVec ((D.chart a).γ (t₀ + (ε : ℂ) • star t))))

def SymmCharts (P : PotentialCharts M.atlas) (κ : Equiv.Perm (Fin P.N)) : Prop :=
  (∀ j, κ (κ j) = j) ∧ (∀ j t, P.q (κ j) (star t) = P.q j t) ∧ ∀ j, ∀ z ∈ mcPts (mCoordIdeal D.y),
    (M.proj (conjVec z) ∈ (P.chart (κ j)).source ↔ M.proj z ∈ (P.chart j).source) ∧
    (M.proj (conjVec z) ∈ P.mid (κ j) ↔ M.proj z ∈ P.mid j) ∧
    (M.proj (conjVec z) ∈ P.inner (κ j) ↔ M.proj z ∈ P.inner j) ∧
    (M.proj z ∈ (P.chart j).source → P.chart (κ j) (M.proj (conjVec z)) = star (P.chart j (M.proj z)))

end Free

def detLat {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E]
    [Module Ω E] (L : Lat ξ E) {r : ℕ} (b₀ : Fin r → E) : Lat ξ Ω := fun p =>
  Submodule.span (regAt ξ p) {t | ∃ (b : Fin r → E) (T : Matrix (Fin r) (Fin r) Ω), L.IsFrameAt b p ∧
    (∀ k, b k = ∑ k', T k' k • b₀ k') ∧ t = T.det}

namespace SncPiece

section Coord

variable {K : Type} {J : K → Type}

theorem conj_conj (z : (Σ k, J k) → ℂ) : conjVec (conjVec z) = z := by
  funext p
  simp [conjVec]

theorem conj_mem {P : Ideal (MRing J)} {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts P) : conjVec z ∈ mcPts P := by
  have h : ∀ f : MRing J, eval (conjVec z) (map (Int.castRingHom ℂ) f) =
      starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := fun f => by
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp, conjVec]
  exact ⟨fun k => (hz.1 k).imp fun i hi => (map_ne_zero _).2 hi, fun f hf => by rw [h, hz.2 f hf, map_zero]⟩

theorem add_smul_mem_ball {n : ℕ} {t₀ t : Fin n → ℂ} {ε : ℝ} (h₀ : ‖t₀‖ ≤ 1 / 2) (hε : 0 < ε) (hε' : ε ≤ 1 / 4)
    (ht : ‖t‖ < 2) : t₀ + (ε : ℂ) • t ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff]
  refine (norm_add_le _ _).trans_lt ?_
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hε.le]
  nlinarith [norm_nonneg t]

theorem add_smul_eq_zero_iff {n : ℕ} {t₀ t : Fin n → ℂ} {ε : ℝ} (hε : 0 < ε) (ht : ‖t‖ < 2) {i : Fin n}
    (hi : t₀ i ≠ 0 → 2 * ε ≤ ‖t₀ i‖) : (t₀ + (ε : ℂ) • t) i = 0 ↔ t₀ i = 0 ∧ t i = 0 := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨fun h => ?_, fun h => by rw [h.1, h.2, mul_zero, add_zero]⟩
  have h0 : t₀ i = 0 := by
    by_contra hne
    have h1 := hi hne
    rw [eq_neg_of_add_eq_zero_left h, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le] at h1
    nlinarith [norm_le_pi_norm t i]
  rw [h0, zero_add] at h
  exact ⟨h0, (mul_eq_zero.1 h).resolve_left (Complex.ofReal_ne_zero.2 hε.ne')⟩

end Coord

section Free

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  (D : ComponentData II Ψ K J Ω W)

theorem conj_mem_bd_iff (z : (Σ k, J k) → ℂ) : conjVec z ∈ D.Bd ↔ z ∈ D.Bd :=
  ⟨fun h => conj_conj z ▸ D.bd_conj _ h, D.bd_conj z⟩

theorem conj_mem_Xo {z : (Σ k, J k) → ℂ} (hz : z ∈ D.Xo) : conjVec z ∈ D.Xo :=
  ⟨conj_mem hz.1, fun h => hz.2 ((conj_mem_bd_iff D z).1 h)⟩

theorem mem_offBd {a : Fin D.nCharts} {t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ} :
    t ∈ offBd D a ↔ ‖t‖ < 1 ∧ ∀ i : Fin _, (i : ℕ) < (D.chart a).a → t i ≠ 0 := by
  rw [← mem_ball_zero_iff]
  refine and_congr_right fun h => ?_
  rw [(D.chart a).boundary t h]
  simp

theorem isOpen_offBd (a : Fin D.nCharts) : IsOpen (offBd D a) := by
  have : offBd D a = {t | ‖t‖ < 1} ∩ ⋂ i : Fin (Fintype.card Ψ * D.j * (D.N - D.j)), {t | (i : ℕ) < (D.chart a).a → t i ≠ 0} := by
    ext t
    simp [mem_offBd]
  rw [this]
  refine (isOpen_lt continuous_norm continuous_const).inter (isOpen_iInter_of_finite fun i => ?_)
  by_cases h : (i : ℕ) < (D.chart a).a
  · simpa [h] using isOpen_ne_fun (continuous_apply i) continuous_const
  · simp [h]

theorem mem_Xo_of_offBd {a : Fin D.nCharts} {t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ} (ht : t ∈ offBd D a) :
    (D.chart a).γ t ∈ D.Xo := ⟨(D.chart a).mem t ht.1, ht.2⟩

theorem mem_bd_iff {a : Fin D.nCharts} {t₀ t : Fin D.n → ℂ} {ε : ℝ} (h₀ : ‖t₀‖ ≤ 1 / 2) (hε : 0 < ε) (hε' : ε ≤ 1 / 4)
    (hsep : ∀ i : Fin D.n, (i : ℕ) < (D.chart a).a → t₀ i ≠ 0 → 2 * ε ≤ ‖t₀ i‖) (ht : ‖t‖ < 2) :
    (D.chart a).γ (t₀ + (ε : ℂ) • t) ∈ D.Bd ↔ ∃ i : Fin D.n, ((i : ℕ) < (D.chart a).a ∧ t₀ i = 0) ∧ t i = 0 := by
  refine ((D.chart a).boundary _ (add_smul_mem_ball h₀ hε hε' ht)).trans (exists_congr fun i => ?_)
  rw [and_assoc]
  exact and_congr_right fun hi => add_smul_eq_zero_iff hε ht (hsep i hi)

theorem logHom_log (A : HermLine J) : LogHom D A.a fun z => Real.log (A.h z) := by
  intro z hz c hc
  have hp : ∀ k, ‖c k‖ ^ A.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  change Real.log (A.h fun p => c p.1 * z p) = _
  rw [A.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => hp k) (A.pos z hz.1.1).ne',
    Real.log_prod fun k _ => hp k, add_comm]
  simp only [Real.log_zpow]

variable {D} {M : XModel D}

end Free

section Det

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E]
  [Module Ω E] {L : Lat ξ E} {r : ℕ} {b₀ : Fin r → E} {p : Cpt ξ}

theorem det_mem_detLat {b : Fin r → E} {T : Matrix (Fin r) (Fin r) Ω} (hb : L.IsFrameAt b p)
    (hT : ∀ k, b k = ∑ k', T k' k • b₀ k') : T.det ∈ detLat L b₀ p :=
  Submodule.subset_span ⟨b, T, hb, hT, rfl⟩

example {a b c d : Ω} (h : LinearIndependent Ω ![(a, b), (c, d)]) :
    a * d - b * c ∈ detLat (fun q => Submodule.span (regAt ξ q) (Set.range ![(a, b), (c, d)]) : Lat ξ (Ω × Ω))
      ![(1, 0), (0, 1)] p := by
  have := det_mem_detLat (L := (fun q => Submodule.span (regAt ξ q) (Set.range ![(a, b), (c, d)]) : Lat ξ (Ω × Ω)))
    (b₀ := ![(1, 0), (0, 1)]) (p := p) (T := !![a, c; b, d]) ⟨h, rfl⟩ fun k => by fin_cases k <;> simp
  rwa [Matrix.det_fin_two_of, mul_comm c] at this

end Det

end SncPiece

section Free

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W} {M : XModel D} {P : PotentialCharts M.atlas} {S : Fin P.N → Finset (Fin D.n)}

theorem Adapted.mem_bd_iff (h : Adapted M P S) {j : Fin P.N} {t : Fin D.n → ℂ} (ht : t ∈ (P.chart j).target)
    {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) (e : (P.chart j).symm t = M.proj z) :
    z ∈ D.Bd ↔ t ∈ ReciprocityTheory.AnForm.A.coordDiv (S j) := by
  rw [h j z hz (e ▸ (P.chart j).map_target ht), ← e, (P.chart j).right_inv ht]

theorem Adapted.mem_iff_of_piece (h : Adapted M P S) {j : Fin P.N} (hj : (P.chart j).target = Metric.ball 0 1)
    {a : Fin D.nCharts} {t₀ : Fin D.n → ℂ} {ε : ℝ} (h₀ : ‖t₀‖ ≤ 1 / 2) (hε : 0 < ε) (hε' : ε ≤ 1 / 4)
    (hsep : ∀ i : Fin D.n, (i : ℕ) < (D.chart a).a → t₀ i ≠ 0 → 2 * ε ≤ ‖t₀ i‖)
    (hγ : (∀ t ∈ (P.chart j).target, (P.chart j).symm t = M.proj ((D.chart a).γ (t₀ + (ε : ℂ) • t))) ∨
      ∀ t ∈ (P.chart j).target, (P.chart j).symm t = M.proj (conjVec ((D.chart a).γ (t₀ + (ε : ℂ) • star t))))
    (i : Fin D.n) : i ∈ S j ↔ (i : ℕ) < (D.chart a).a ∧ t₀ i = 0 := by
  let t : Fin D.n → ℂ := fun l => if l = i then 0 else 1 / 2
  have ht0 : ∀ l, t l = 0 ↔ l = i := fun l => by by_cases hl : l = i <;> simp [t, hl]
  have hst : star t = t := funext fun l => by by_cases hl : l = i <;> simp [t, hl]
  have hn : ‖t‖ < 1 := (pi_norm_lt_iff one_pos).2 fun l => by by_cases hl : l = i <;> norm_num [t, hl]
  have ht : t ∈ (P.chart j).target := hj ▸ mem_ball_zero_iff.2 hn
  have hm := (D.chart a).mem _ (SncPiece.add_smul_mem_ball h₀ hε hε' (hn.trans one_lt_two))
  have key : (D.chart a).γ (t₀ + (ε : ℂ) • t) ∈ D.Bd ↔ t ∈ ReciprocityTheory.AnForm.A.coordDiv (S j) := by
    rcases hγ with hγ | hγ
    · exact h.mem_bd_iff ht hm (hγ t ht)
    · exact (SncPiece.conj_mem_bd_iff D _).symm.trans
        (h.mem_bd_iff ht (SncPiece.conj_mem hm) (by rw [hγ t ht, hst]))
  rw [SncPiece.mem_bd_iff D h₀ hε hε' hsep (hn.trans one_lt_two)] at key
  simpa [ReciprocityTheory.AnForm.A.coordDiv, ht0] using key.symm

theorem Adapted.exists_piece (h : Adapted M P S) (h' : FromSnc M P) (j : Fin P.N) :
    ∃ (a : Fin D.nCharts) (t₀ : Fin D.n → ℂ) (ε : ℝ), ‖t₀‖ ≤ 1 / 2 ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧
      (∀ i : Fin D.n, (i : ℕ) < (D.chart a).a → t₀ i ≠ 0 → 2 * ε ≤ ‖t₀ i‖) ∧
      ((∀ t ∈ (P.chart j).target, (P.chart j).symm t = M.proj ((D.chart a).γ (t₀ + (ε : ℂ) • t))) ∨
        ∀ t ∈ (P.chart j).target, (P.chart j).symm t = M.proj (conjVec ((D.chart a).γ (t₀ + (ε : ℂ) • star t)))) ∧
      ∀ i, i ∈ S j ↔ (i : ℕ) < (D.chart a).a ∧ t₀ i = 0 := by
  obtain ⟨hj, a, t₀, ε, h₀, hε, hε', hsep, hγ⟩ := h' j
  exact ⟨a, t₀, ε, h₀, hε, hε', hsep, hγ, h.mem_iff_of_piece hj h₀ hε hε' hsep hγ⟩

theorem Adapted.unique {S' : Fin P.N → Finset (Fin D.n)} (h : Adapted M P S) (h₁ : Adapted M P S')
    (h' : FromSnc M P) : S = S' := by
  funext j
  obtain ⟨hj, a, t₀, ε, h₀, hε, hε', hsep, hγ⟩ := h' j
  ext i
  rw [h.mem_iff_of_piece hj h₀ hε hε' hsep hγ, h₁.mem_iff_of_piece hj h₀ hε hε' hsep hγ]

end Free

namespace SncLine

open Metric GroundTheory.Heights₂.Heights.LowerBoundFree.Line GroundTheory.Heights₂.Heights.Regular.ProjectiveLine
open GroundTheory.Heights₂.Heights (CP)
open scoped Matrix ComplexOrder

def bd : Set ((Σ _ : Unit, Fin 2) → ℂ) := {z | z ∈ mcPts (mCoordIdeal yLine) ∧ z ⟨(), 1⟩ = 0}

theorem chartMap_mem (a : Fin 2) (t : Fin 1 → ℂ) : chartMap a t ∈ mcPts (mCoordIdeal yLine) :=
  mem_mcPts_line.2 ⟨a, by rw [chartMap_apply, if_pos rfl]; exact one_ne_zero⟩

def chart (a : Fin 2) : SncChart (mCoordIdeal yLine) 1 bd where
  γ t := chartMap a ((4 : ℂ) • t)
  a := 1 - a
  a_le := Nat.sub_le _ _
  analytic t _ := (analyticAt_const.add ((chartLin a).analyticAt _)).comp
    (((4 : ℂ) • ContinuousLinearMap.id ℂ (Fin 1 → ℂ)).analyticAt t)
  mem t _ := mem_mcPts_line.2 ⟨a, by rw [chartMap_apply, if_pos rfl]; exact one_ne_zero⟩
  immersion t _ v := by
    rintro ⟨c, hc⟩
    have hd : HasFDerivAt (fun t : Fin 1 → ℂ => chartMap a ((4 : ℂ) • t))
        ((chartLin a).comp ((4 : ℂ) • ContinuousLinearMap.id ℂ (Fin 1 → ℂ))) t :=
      (hasFDerivAt_chartMap a _).comp t ((4 : ℂ) • ContinuousLinearMap.id ℂ (Fin 1 → ℂ)).hasFDerivAt
    rw [hd.fderiv] at hc
    obtain ⟨b, hb⟩ := other_index a
    have h1 := congrFun hc ⟨(), a⟩
    have h2 := congrFun hc ⟨(), b⟩
    simp only [torusSmul, ContinuousLinearMap.comp_apply] at h1 h2
    rw [chartLin_apply, chartMap_apply, if_pos rfl, if_pos rfl, mul_one] at h1
    rw [chartLin_apply, chartMap_apply, if_neg hb, if_neg hb, ← h1, zero_mul] at h2
    funext i
    rw [Subsingleton.elim i 0]
    simpa using h2
  injective t _ t' _ c _ h := by
    obtain ⟨b, hb⟩ := other_index a
    have h1 := congrFun h ⟨(), a⟩
    have h2 := congrFun h ⟨(), b⟩
    simp only [torusSmul] at h1 h2
    rw [chartMap_apply, chartMap_apply, if_pos rfl, if_pos rfl, mul_one] at h1
    rw [chartMap_apply, chartMap_apply, if_neg hb, if_neg hb, ← h1, one_mul] at h2
    funext i
    rw [Subsingleton.elim i 0]
    simpa using h2
  boundary t _ := by
    fin_cases a <;> simp [bd, chartMap_mem, chartMap_apply]

theorem chart_cover : ∀ z ∈ mcPts (mCoordIdeal yLine), ∃ a, ∃ t : Fin 1 → ℂ,
    ‖t‖ ≤ 1 / 2 ∧ ∃ c : Unit → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c ((chart a).γ t) := by
  intro z hz
  obtain ⟨a, t, ht, c, hc, h⟩ := lineChart_cover z hz
  refine ⟨a, (4 : ℂ)⁻¹ • t, ?_, c, hc, ?_⟩
  · rw [norm_smul]; norm_num; linarith [norm_nonneg t]
  · rw [h]
    show _ = torusSmul c (chartMap a ((4 : ℂ) • (4 : ℂ)⁻¹ • t))
    rw [smul_smul]; norm_num; rfl

theorem one_le_logR (a : Fin 2) {t : Fin 1 → ℂ} (ht : ‖t‖ < 1) : 1 ≤ (chart a).logR t := by
  refine le_add_of_le_of_nonneg (Real.one_le_exp zero_le_one) (Finset.sum_nonneg fun i _ => ?_)
  split_ifs
  · rw [one_div, Real.log_inv, neg_nonneg]
    exact Real.log_nonpos (by positivity) (pow_le_one₀ (norm_nonneg _) ((norm_le_pi_norm t i).trans ht.le))
  · exact le_rfl

def metric : HermMetric yLine (GroundTheory.Heights₂.Heights.LowerBoundFree.trivialBundle (segreCoord yLine) 2)
    (mcPts (mCoordIdeal yLine) \ bd) chart where
  m := 2
  chart := lineMetric.chart
  fr := lineMetric.fr
  b := lineMetric.b
  isFrame := lineMetric.isFrame
  gram _ _ := 1
  cover z hz := lineMetric.cover z ⟨hz.1, Set.notMem_empty _⟩
  posDef l z hz := lineMetric.posDef l z ⟨hz.1, Set.notMem_empty _⟩
  compat l l' z hz := lineMetric.compat l l' z ⟨hz.1, Set.notMem_empty _⟩
  torus l z hz := lineMetric.torus l z ⟨hz.1, Set.notMem_empty _⟩
  conj l z hz := lineMetric.conj l z ⟨hz.1, Set.notMem_empty _⟩
  smooth _ _ _ _ _ _ _ _ := contDiffAt_const
  logBound a t₀ _ := by
    refine ⟨a, inFrameDomain_line (by
        show chartMap a _ _ ≠ 0
        rw [chartMap_apply, if_pos rfl]; exact one_ne_zero),
      1, one_pos, 1, one_pos, 1, one_pos, fun t _ ht _ _ => ⟨?_, ?_, ?_⟩⟩
    · rw [inv_one, Complex.ofReal_one, one_smul, sub_self]
      exact Matrix.PosSemidef.zero
    · rw [inv_one, one_mul]
      have : (((chart a).logR t : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - 1 =
          (((chart a).logR t - 1 : ℝ) : ℂ) • 1 := by
        rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
      rw [this]
      exact Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr (one_le_logR a ht)))
    · intro p q
      show ‖fderiv ℝ (fun _ : Fin 1 → ℂ => (1 : Matrix (Fin 2) (Fin 2) ℂ) p q) t‖ ≤ _
      rw [fderiv_const_apply, norm_zero]
      positivity

def data : ComponentData zeroSystem Unit Unit (PBlk 2) Line.Ω (fun _ => Fin 2 → Line.Ω) :=
  { lineDataZero with
    Bd := bd
    bd_subset := fun _ h => h.1
    bd_closed := by
      have e : ((↑) ⁻¹' bd : Set (mcPts (mCoordIdeal yLine))) = {z | z.1 ⟨(), 1⟩ = 0} :=
        Set.ext fun z => and_iff_right z.2
      change IsClosed ((↑) ⁻¹' bd : Set (mcPts (mCoordIdeal yLine)))
      rw [e]
      exact isClosed_eq ((continuous_apply _).comp continuous_subtype_val) continuous_const
    bd_torus := fun z hz c hc => ⟨mem_mcPts_line.2 ((mem_mcPts_line.1 hz.1).imp fun _ hi => mul_ne_zero (hc _) hi),
      mul_eq_zero_of_right _ hz.2⟩
    bd_conj := fun z hz => ⟨SncPiece.conj_mem hz.1, (map_eq_zero _).2 hz.2⟩
    chart := chart
    chart_cover := chart_cover
    h := fun _ => metric }

def model : XModel data := lineModel

def charts : PotentialCharts model.atlas := cpCharts

def hyp : Fin charts.N → Finset (Fin data.n) := (![Finset.univ, ∅] : Fin 2 → Finset (Fin 1))

theorem projL_chartMap (a : Fin 2) (t : Fin 1 → ℂ) : projL (chartMap a t) = CP.chartInv a ((2 : ℂ) • t) := by
  have hv : vecL (chartMap a t) = CP.chartVec a ((2 : ℂ) • t) := by
    funext m
    rcases fin_two_other a m with rfl | rfl
    · simp [vecL, chartMap_apply]
    · rw [CP.chartVec_succAbove]
      simp [vecL, chartMap_apply, Fin.succAbove_ne]
  unfold projL
  rw [dif_pos (by rw [hv]; exact CP.chartVec_ne_zero _ _)]
  simp only [hv]
  rfl

theorem fromSnc : FromSnc model charts := by
  intro (j : Fin 2)
  refine ⟨rfl, j, 0, 1 / 4, by simp, by norm_num, le_rfl, fun _ _ h => absurd rfl h,
    Or.inl fun (t : Fin 1 → ℂ) _ => ?_⟩
  show CP.chartInv j ((2 : ℂ) • t) = projL (chartMap j ((4 : ℂ) • ((0 : Fin 1 → ℂ) + ((1 / 4 : ℝ) : ℂ) • t)))
  rw [projL_chartMap, zero_add, smul_smul (4 : ℂ)]
  norm_num

theorem adapted : Adapted model charts hyp := by
  intro (j : Fin 2) z hz hs
  replace hz : z ∈ mcPts (mCoordIdeal yLine) := hz
  have h1 := vecL_ne_zero hz
  have hs' : projL z ∈ CP.chartDomain j := hs.1
  change z ∈ bd ↔ ∃ i ∈ (![Finset.univ, ∅] : Fin 2 → Finset (Fin 1)) j, sChart j (projL z) i = 0
  rw [sChart_apply]
  unfold projL at hs' ⊢
  rw [dif_pos h1] at hs' ⊢
  fin_cases j <;> simp [vecL, bd, hz] at hs' ⊢ <;> simp [hs']

theorem conj_region (j : Fin 2) {z : (Σ _ : Unit, Fin 2) → ℂ} (hz : z ∈ mcPts (mCoordIdeal yLine)) :
    (projL (conjVec z) ∈ CP.chartDomain j ↔ projL z ∈ CP.chartDomain j) ∧
      CP.chartCoord j (projL (conjVec z)) = star (CP.chartCoord j (projL z)) := by
  have h1 := vecL_ne_zero hz
  have h2 : vecL (conjVec z) ≠ 0 := fun h => h1 (funext fun i => by simpa [vecL, conjVec] using congrFun h i)
  unfold projL
  rw [dif_pos h1, dif_pos h2]
  refine ⟨by simp [vecL, conjVec], ?_⟩
  funext i
  simp [vecL, conjVec]

theorem symmCharts : SymmCharts model charts 1 := by
  refine ⟨fun _ => rfl, fun _ _ => rfl, fun (j : Fin 2) z hz => ?_⟩
  obtain ⟨h1, h2⟩ := conj_region j hz
  refine ⟨?_, ?_, ?_, fun _ => ?_⟩
  · show projL (conjVec z) ∈ (sChart j).source ↔ projL z ∈ (sChart j).source
    rw [mem_sChart_source_iff, mem_sChart_source_iff, h1, h2, norm_star]
  · show projL (conjVec z) ∈ cpMid j ↔ projL z ∈ cpMid j
    unfold cpMid
    rw [mem_region_iff _ _ (by norm_num), mem_region_iff _ _ (by norm_num), h1, h2, norm_star]
  · show projL (conjVec z) ∈ cpInner j ↔ projL z ∈ cpInner j
    unfold cpInner
    rw [mem_region_iff _ _ (by norm_num), mem_region_iff _ _ (by norm_num), h1, h2, norm_star]
  · show sChart j (projL (conjVec z)) = star (sChart j (projL z))
    rw [sChart_apply, sChart_apply, h2]
    simp

theorem thRef : ThRef model refOne charts.th := fun x y _ => th_ref_line x y

example : ThRef model refOne charts.th ∧ Adapted model charts hyp ∧ FromSnc model charts ∧ SymmCharts model charts 1 ∧
    ¬ Adapted model charts fun _ => ∅ :=
  ⟨thRef, adapted, fromSnc, symmCharts, fun h =>
    Finset.univ_nonempty.ne_empty (congrFun (adapted.unique h fromSnc) (0 : Fin 2))⟩

example : LogHom data (fun _ => 1) (fun z => Real.log ‖z ⟨(), 1⟩‖) ∧
    ¬ ChartBdd data fun z => Real.log ‖z ⟨(), 1⟩‖ := by
  refine ⟨fun z hz c hc => ?_, fun h => ?_⟩
  · have h1 : z ⟨(), 1⟩ ≠ 0 := fun h => hz.2 ⟨hz.1, h⟩
    simp [torusSmul, Real.log_mul, h1, hc, add_comm]
  · obtain ⟨ε, hε, C, hC⟩ := h (0 : Fin 2) 0 (mem_ball_self one_pos)
    set s : ℝ := min (min ε 1 / 2) (Real.exp (-(C + 1)) / 8) with hs
    have hm : 0 < min ε 1 := lt_min hε one_pos
    have hs0 : 0 < s := lt_min (by linarith) (by positivity)
    have hn : ‖(fun _ => (s : ℂ) : Fin 1 → ℂ)‖ < min ε 1 := by
      rw [pi_norm_const, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      exact (min_le_left _ _).trans_lt (by linarith)
    have h1 := hC (fun _ => (s : ℂ)) ((SncPiece.mem_offBd data).2 ⟨hn.trans_le (min_le_right _ _),
      fun _ _ => Complex.ofReal_ne_zero.2 hs0.ne'⟩) (by rw [sub_zero]; exact hn.trans_le (min_le_left _ _))
    have h2 : ‖(data.chart (0 : Fin 2)).γ (fun _ => (s : ℂ)) ⟨(), 1⟩‖ = 8 * s := by
      change ‖chartMap 0 ((4 : ℂ) • fun _ => (s : ℂ)) ⟨(), 1⟩‖ = _
      simp [chartMap_apply, abs_of_pos hs0]
      ring
    have h3 : Real.log (8 * s) ≤ -(C + 1) := by
      rw [Real.log_le_iff_le_exp (by positivity)]
      linarith [min_le_right (min ε 1 / 2) (Real.exp (-(C + 1)) / 8)]
    simp only [h2] at h1
    linarith [(abs_le.1 h1).1]

end SncLine

end GlobalTheory.CompanionTheory.Ar.Cusp
