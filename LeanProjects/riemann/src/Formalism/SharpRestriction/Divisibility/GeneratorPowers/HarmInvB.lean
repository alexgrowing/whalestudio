import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpOfPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.HarmInvA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.KillAdd

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (logOf)

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

section Log

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.TB.LogPf

theorem logOf_props (G : FGLaw S d) :
    (∀ i, constantCoeff ((fun i => logOf G i) i) = 0) ∧ dLin (fun i => logOf G i) = 1 ∧
    comp1 (fun i => logOf G i) (G.add (pt S (n := 2) d 0) (pt S (n := 2) d 1)) =
      comp1 (fun i => logOf G i) (pt S (n := 2) d 0) + comp1 (fun i => logOf G i) (pt S (n := 2) d 1) := by
  refine ⟨fun i => ReciprocityTheory.ChartRestriction.G.TB.LogPf.constantCoeff_prim _, ?_, ?_⟩
  · ext i j
    have hc := congrFun (congrFun (ReciprocityTheory.ChartRestriction.G.TB.LogPf.cc_om (G := G)) i) j
    simp only [Matrix.map_apply] at hc
    show coeff (Finsupp.single ((0 : Fin 1), j) 1) (logOf G i) = (1 : Matrix (Fin d) (Fin d) S) i j
    unfold logOf
    rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.coeff_prim, Finset.sum_eq_single ((0 : Fin 1), j)]
    · simp [Finsupp.degree_single, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hc]
    · intro w _ hw
      have h0 : (Finsupp.single ((0 : Fin 1), j) 1 : Fin 1 × Fin d →₀ ℕ) w = 0 := by
        rw [Finsupp.single_apply, if_neg (Ne.symm hw)]
      rw [if_pos h0]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · funext i
    show ev ![G.add (pt S (n := 2) d 0) (pt S (n := 2) d 1)] (logOf G i) =
      ev ![pt S (n := 2) d 0] (logOf G i) + ev ![pt S (n := 2) d 1] (logOf G i)
    have hF : G.add (pt S (n := 2) d 0) (pt S (n := 2) d 1) = G.F := by
      funext l
      show MvPowerSeries.subst (fun p : Fin 2 × Fin d =>
        (![pt S (n := 2) d 0, pt S (n := 2) d 1] : Fin 2 → Pt S 2 d) p.1 p.2) (G.F l) = G.F l
      have hX : (fun p : Fin 2 × Fin d =>
          (![pt S (n := 2) d 0, pt S (n := 2) d 1] : Fin 2 → Pt S 2 d) p.1 p.2) = MvPowerSeries.X := by
        funext p
        rcases p with ⟨a, c⟩
        fin_cases a <;> rfl
      rw [hX]
      first
      | exact congrFun MvPowerSeries.subst_self _
      | (rw [MvPowerSeries.subst_self]; rfl)
      | (rw [← MvPowerSeries.map_algebraMap_eq_subst_X]; simp)
    rw [hF]
    exact ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf_add G i

end Log

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem hasSubst0 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ S}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) : MvPowerSeries.HasSubst a := by
  first
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
  | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)

theorem log_expPhi (G : FGLaw S d) (uvec : Lt1 Dw → Fin d → S) (ε : Pt S 1 d)
    (hinv : IsInvPair ε (fun i => logOf G i)) (i : Fin d) :
    MvPowerSeries.subst (fun p : Fin 1 × Fin d => expPhi uvec ε p.2) (logOf G i) = linPt uvec (0 : Fin 1) i := by
  obtain ⟨hε0, -, -, hcomp⟩ := hinv
  have h1 := congrFun hcomp i
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.comp1, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt] at h1
  have hε : (fun p : Fin 1 × Fin d => (![ε] p.1 p.2 : MvPowerSeries (Fin 1 × Fin d) S)) = fun p => ε p.2 := by
    funext p
    rcases p with ⟨a, c⟩
    rw [Subsingleton.elim a 0]
    rfl
  rw [hε] at h1
  have h0 : ∀ p : Fin 1 × Fin d, MvPowerSeries.constantCoeff (ε p.2) = 0 := fun p => hε0 p.2
  have hA : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => ε p.2) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero h0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero h0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' h0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [h0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [h0 s]; exact IsNilpotent.zero)
  have hL0 : ∀ p : Fin 1 × Fin d, MvPowerSeries.constantCoeff (linPt uvec (0 : Fin 1) p.2) = 0 := by
    intro p
    simp [Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.linPt]
  have hL : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => linPt uvec (0 : Fin 1) p.2) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hL0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hL0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hL0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hL0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [hL0 s]; exact IsNilpotent.zero)
  change MvPowerSeries.subst (fun p : Fin 1 × Fin d => MvPowerSeries.subst (fun q : Fin 1 × Fin d => linPt uvec (0 : Fin 1) q.2) (ε p.2)) (logOf G i) = _
  rw [← MvPowerSeries.subst_comp_subst_apply hA hL, h1, MvPowerSeries.subst_X hL]

theorem log_expPhi_act (G : FGLaw S d) (uvec : Lt1 Dw → Fin d → S) (ε : Pt S 1 d)
    (hinv : IsInvPair ε (fun i => logOf G i)) (a : Fin 1 × Fin (dL Dw) → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (ha : ∀ q, MvPowerSeries.constantCoeff (a q) = 0) (i : Fin d) :
    MvPowerSeries.subst (fun p : Fin 1 × Fin d => MvPowerSeries.subst a (expPhi uvec ε p.2)) (logOf G i) =
      MvPowerSeries.subst a (linPt uvec (0 : Fin 1) i) := by
  have hε0 : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0 := by
    obtain ⟨h, -⟩ := hinv
    exact h
  have hE0 : ∀ p : Fin 1 × Fin d, MvPowerSeries.constantCoeff (expPhi uvec ε p.2) = 0 :=
    fun p => Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.expPhi_const uvec ε hε0 p.2
  have hE : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => expPhi uvec ε p.2) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hE0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hE0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hE0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hE0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [hE0 s]; exact IsNilpotent.zero)
  have ha' : MvPowerSeries.HasSubst a := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
  rw [← MvPowerSeries.subst_comp_subst_apply hE ha', log_expPhi G uvec ε hinv i]

theorem germCompOne_identityPoint_left (φ : Pt S 1 d) : comp1 φ (pt S (n := 1) d 0) = φ := by
  funext i
  change MvPowerSeries.subst (fun p : Fin 1 × Fin d => (![pt S (n := 1) d 0] p.1 p.2 : MvPowerSeries (Fin 1 × Fin d) S)) (φ i) = φ i
  have hX : (fun p : Fin 1 × Fin d => (![pt S (n := 1) d 0] p.1 p.2 : MvPowerSeries (Fin 1 × Fin d) S)) = MvPowerSeries.X := by
    funext p
    rcases p with ⟨a, c⟩
    rw [Subsingleton.elim a 0]
    rfl
  rw [hX]
  first
  | exact congrFun MvPowerSeries.subst_self _
  | (rw [MvPowerSeries.subst_self]; rfl)
  | (rw [← MvPowerSeries.map_algebraMap_eq_subst_X]; simp)

theorem subst_lg (G : FGLaw S d) {τ : Type} (Bφ : Fin 2 × Fin d → MvPowerSeries τ S)
    (hB : ∀ p, MvPowerSeries.constantCoeff (Bφ p) = 0) (j : Fin 2) (i : Fin d) :
    MvPowerSeries.subst Bφ (lg G j i) = MvPowerSeries.subst (fun p : Fin 1 × Fin d => Bφ (j, p.2)) (logOf G i) := by
  have h0 : ∀ p : Fin 1 × Fin d, MvPowerSeries.constantCoeff (![pt S (n := 2) d j] p.1 p.2 : MvPowerSeries (Fin 2 × Fin d) S) = 0 := by
    intro p
    rcases p with ⟨a, c⟩
    rw [Subsingleton.elim a 0]
    simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  have hA : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => (![pt S (n := 2) d j] p.1 p.2 : MvPowerSeries (Fin 2 × Fin d) S)) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero h0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero h0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' h0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [h0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [h0 s]; exact IsNilpotent.zero)
  have hBs : MvPowerSeries.HasSubst Bφ := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hB
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hB
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hB
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hB s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [hB s]; exact IsNilpotent.zero)
  change MvPowerSeries.subst Bφ (MvPowerSeries.subst (fun p : Fin 1 × Fin d => (![pt S (n := 2) d j] p.1 p.2 : MvPowerSeries (Fin 2 × Fin d) S)) (logOf G i)) = _
  rw [MvPowerSeries.subst_comp_subst_apply hA hBs]
  congr 1
  funext p
  rcases p with ⟨a, c⟩
  rw [Subsingleton.elim a 0]
  simp only [Matrix.cons_val_zero, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt, MvPowerSeries.subst_X hBs]

theorem compL_diagL {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (w0 : O) (cc : Fin d → Fin d → S)
    (uvec : Lt1 Dw → Fin d → S) (ε : Pt S 1 d) (hinv : IsInvPair ε (fun i => logOf B.G i))
    (a : Fin 1 × Fin (dL Dw) → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (ha : ∀ q, MvPowerSeries.constantCoeff (a q) = 0)
    (hact : ∀ j, MvPowerSeries.subst (fun p : Fin 1 × Fin d => expPhi uvec ε p.2) (B.A.act w0 j) =
      MvPowerSeries.subst a (expPhi uvec ε j)) :
    compL (expPhi uvec ε) (diagL B w0 cc) =
      ∑ i, ∑ l, cc i l • (linPt uvec (0 : Fin 1) i * MvPowerSeries.subst a (linPt uvec (0 : Fin 1) l)) := by
  have hε0 : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0 := by
    obtain ⟨h, -⟩ := hinv
    exact h
  have hE0 : ∀ p : Fin 1 × Fin d, MvPowerSeries.constantCoeff (expPhi uvec ε p.2) = 0 :=
    fun p => Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.expPhi_const uvec ε hε0 p.2
  have hE : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => expPhi uvec ε p.2) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hE0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hE0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hE0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hE0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [hE0 s]; exact IsNilpotent.zero)
  have hV0 : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff ((fun p : Fin 2 × Fin d => (![pt S d 0, comp1 (B.A.act w0) (pt S d 0)] : Fin 2 → Pt S 1 d) p.1 p.2) p) = 0 := by
    intro p
    rcases p with ⟨j, c⟩
    fin_cases j
    · simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
    · simp [germCompOne_identityPoint_left, B.A.const]
  have hV : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d => (![pt S d 0, comp1 (B.A.act w0) (pt S d 0)] : Fin 2 → Pt S 1 d) p.1 p.2) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hV0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hV0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hV0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hV0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [hV0 s]; exact IsNilpotent.zero)
  change MvPowerSeries.subst (fun p : Fin 1 × Fin d => expPhi uvec ε p.2) (MvPowerSeries.subst (fun p : Fin 2 × Fin d => (![pt S d 0, comp1 (B.A.act w0) (pt S d 0)] : Fin 2 → Pt S 1 d) p.1 p.2) (bilL B.G cc)) = _
  rw [← MvPowerSeries.coe_substAlgHom hV, ← MvPowerSeries.coe_substAlgHom hE]
  simp only [Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL, map_sum, map_smul, map_mul]
  simp only [MvPowerSeries.coe_substAlgHom]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => ?_))
  rw [subst_lg B.G (fun p : Fin 2 × Fin d => (![pt S d 0, comp1 (B.A.act w0) (pt S d 0)] : Fin 2 → Pt S 1 d) p.1 p.2) hV0 0 i, subst_lg B.G (fun p : Fin 2 × Fin d => (![pt S d 0, comp1 (B.A.act w0) (pt S d 0)] : Fin 2 → Pt S 1 d) p.1 p.2) hV0 1 l]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, germCompOne_identityPoint_left]
  have hP0 : ∀ p : Fin 1 × Fin d, MvPowerSeries.constantCoeff (pt S (n := 1) d 0 p.2) = 0 := by
    intro p
    simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  have hP : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => pt S (n := 1) d 0 p.2) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hP0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hP0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hP0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hP0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [hP0 s]; exact IsNilpotent.zero)
  have hQ0 : ∀ p : Fin 1 × Fin d, MvPowerSeries.constantCoeff (B.A.act w0 p.2) = 0 := fun p => B.A.const w0 p.2
  have hQ : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => B.A.act w0 p.2) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hQ0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hQ0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hQ0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hQ0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [hQ0 s]; exact IsNilpotent.zero)
  rw [MvPowerSeries.subst_comp_subst_apply hP hE, MvPowerSeries.subst_comp_subst_apply hQ hE]
  simp only [hact]
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt, MvPowerSeries.subst_X hE]
  rw [log_expPhi B.G uvec ε hinv i, log_expPhi_act B.G uvec ε hinv a ha l]

def qT (cc : Fin d → Fin d → S) (u : Lt1 Dw → Fin d → S) (t : Fin 1 × Fin (dL Dw) → S) (i l : Fin d)
    (ℓ ℓ' : Lt1 Dw) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  MvPowerSeries.C (cc i l * u ℓ i * u ℓ' l * t (0, ltIdx Dw ℓ')) *
    (MvPowerSeries.X ((0 : Fin 1), ltIdx Dw ℓ) * MvPowerSeries.X ((0 : Fin 1), ltIdx Dw ℓ'))

def qβ (cc : Fin d → Fin d → S) (u : Lt1 Dw → Fin d → S) (t : Fin 1 × Fin (dL Dw) → S) :
    Matrix (Fin (dL Dw)) (Fin (dL Dw)) S :=
  fun p p' => ∑ i, ∑ l, cc i l * u ((ltIdx Dw).symm p) i * u ((ltIdx Dw).symm p') l * t (0, p')

theorem quad_form (cc : Fin d → Fin d → S) (u : Lt1 Dw → Fin d → S) (t : Fin 1 × Fin (dL Dw) → S) :
    ∑ i, ∑ l, cc i l • (linPt u (0 : Fin 1) i * MvPowerSeries.subst
      (fun q => t q • (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) (linPt u (0 : Fin 1) l)) =
    quadCol (n := 1) (qβ cc u t) := by
  have hC : ∀ (c : S) (f : MvPowerSeries (Fin 1 × Fin (dL Dw)) S), MvPowerSeries.C c * f = c • f :=
    fun c f => by rw [MvPowerSeries.smul_eq_C_mul]
  have hT0 : ∀ q : Fin 1 × Fin (dL Dw), MvPowerSeries.constantCoeff (t q • (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) = 0 := by
    intro q
    simp [MvPowerSeries.smul_eq_C_mul]
  have hT : MvPowerSeries.HasSubst (fun q => t q • (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hT0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hT0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hT0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hT0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [hT0 s]; exact IsNilpotent.zero)
  have hsub : ∀ l, MvPowerSeries.subst (fun q => t q • (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) (linPt u (0 : Fin 1) l) =
      ∑ ℓ, (u ℓ l * t (0, ltIdx Dw ℓ)) • (MvPowerSeries.X ((0 : Fin 1), ltIdx Dw ℓ) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) := by
    intro l
    rw [← MvPowerSeries.coe_substAlgHom hT]
    simp only [Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.linPt, hC, map_sum, map_smul]
    simp only [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hT, smul_smul]
  have hlin : ∀ i, linPt u (0 : Fin 1) i = ∑ ℓ, u ℓ i • (MvPowerSeries.X ((0 : Fin 1), ltIdx Dw ℓ) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) := by
    intro i
    simp only [Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.linPt, hC]
  have key : ∀ {M : Type} [AddCommMonoid M] (F : Fin d → Fin d → Lt1 Dw → Lt1 Dw → M),
      ∑ ℓ, ∑ ℓ', ∑ i, ∑ l, F i l ℓ ℓ' = ∑ i, ∑ l, ∑ ℓ, ∑ ℓ', F i l ℓ ℓ' := by
    intro M _ F
    calc ∑ ℓ, ∑ ℓ', ∑ i, ∑ l, F i l ℓ ℓ' = ∑ ℓ, ∑ i, ∑ ℓ', ∑ l, F i l ℓ ℓ' :=
          Finset.sum_congr rfl (fun ℓ _ => Finset.sum_comm)
      _ = ∑ i, ∑ ℓ, ∑ ℓ', ∑ l, F i l ℓ ℓ' := Finset.sum_comm
      _ = ∑ i, ∑ ℓ, ∑ l, ∑ ℓ', F i l ℓ ℓ' :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun ℓ _ => Finset.sum_comm))
      _ = ∑ i, ∑ l, ∑ ℓ, ∑ ℓ', F i l ℓ ℓ' :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
  have hR : quadCol (n := 1) (qβ cc u t) = ∑ i, ∑ l, ∑ ℓ, ∑ ℓ', (cc i l * u ℓ i * u ℓ' l * t (0, ltIdx Dw ℓ')) •
      ((MvPowerSeries.X ((0 : Fin 1), ltIdx Dw ℓ) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) * (MvPowerSeries.X ((0 : Fin 1), ltIdx Dw ℓ') : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) := by
    rw [← key]
    simp only [ReciprocityTheory.ChartRestriction.G.TB.quadCol, Fin.sum_univ_one, mul_assoc, hC]
    rw [← (ltIdx Dw).sum_comp]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    rw [← (ltIdx Dw).sum_comp]
    refine Finset.sum_congr rfl (fun ℓ' _ => ?_)
    simp only [qβ, Equiv.symm_apply_apply, Finset.sum_smul, mul_assoc, Finset.sum_mul, smul_mul_assoc]
  rw [hR]
  simp only [hsub]
  simp only [hlin]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  first
  | simp only [smul_mul_smul_comm, Finset.smul_sum, smul_smul]
  | simp only [smul_mul_smul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun ℓ _ => Finset.sum_congr rfl (fun ℓ' _ => ?_))))
  congr 1
  ring

end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvB
