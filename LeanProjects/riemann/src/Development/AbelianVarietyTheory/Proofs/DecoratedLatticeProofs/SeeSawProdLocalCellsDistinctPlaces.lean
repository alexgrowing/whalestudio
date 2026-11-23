import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.CellProd

theorem prod_ofFn_mul {M : Type} [Monoid M] : ∀ {n : ℕ} (r u : Fin n → M), (∀ i i', i ≠ i' → Commute (u i) (r i')) →
    (List.ofFn fun i => r i * u i).prod = (List.ofFn r).prod * (List.ofFn u).prod
  | 0, _, _, _ => by simp
  | n + 1, r, u, h => by
    have ih := prod_ofFn_mul (fun i => r i.succ) (fun i => u i.succ)
      (fun i i' hi => h _ _ fun e => hi (Fin.succ_injective _ e))
    have hc : Commute (u 0) (List.ofFn fun i : Fin n => r i.succ).prod := by
      refine Commute.list_prod_right _ _ fun x hx => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact h _ _ (Fin.succ_ne_zero i).symm
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ih, mul_assoc, mul_assoc, ← mul_assoc (u 0), hc.eq, mul_assoc]

theorem prod_ofFn_single {M : Type} [Monoid M] : ∀ {n : ℕ} (f : Fin n → M) (i : Fin n), (∀ i', i' ≠ i → f i' = 1) →
    (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | n + 1, f, i, h => by
    simp only [List.ofFn_succ, List.prod_cons]
    induction i using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact h _ (Fin.succ_ne_zero i)
    | succ i =>
      rw [h 0 (Fin.succ_ne_zero i).symm, one_mul]
      exact prod_ofFn_single (fun i => f i.succ) i fun i' hi => h _ fun e => hi (Fin.succ_injective _ e)

variable {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem idAt_le {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) : idAt D P ≤ idAt D P' :=
  inf_le_inf_left _ (le_iInf fun w => iInf_le_of_le ⟨w.1, fun hw => w.2 (h _ hw)⟩ le_rfl)

theorem mem_idAt (q : SplitPt D k) {a : AE D} (h : (q.e + cA D q.e) * a = a) : a ∈ idAt D (· = q.v) := by
  obtain ⟨ε, hε, hs⟩ := q.above
  exact ((placeIdem_acts D q.v ε hε).1 a).2 (hs ▸ h)

theorem idem_mul_eq_zero (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {a : AE D}
    (h : (q'.e + cA D q'.e) * a = a) : (q.e + cA D q.e) * a = 0 := by
  obtain ⟨ε, hε, hs⟩ := q.above
  rw [hs]
  exact (placeIdem_acts D q.v ε hε).2 a (idAt_le (fun v (e : v = q'.v) => e ▸ hv) (mem_idAt q' h))

theorem pr_eq_zero (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {a : AE D}
    (h : (q'.e + cA D q'.e) * a = a) : q.pr a = 0 := by
  have h0 := idem_mul_eq_zero q q' hv h
  obtain ⟨h1, h2, -⟩ := q.split
  have : q.e * a = 0 := by
    have := congrArg (q.e * ·) h0
    simpa only [← mul_assoc, mul_add, h1, h2, add_zero, mul_zero] using this
  rw [← q.pr_sec (q.pr a), q.sec_pr, this, map_zero]

theorem mem_grpAt (q : SplitPt D k) {V : HSp D} {g : GA D V} (hg : SuppAt q.e V g) {P : Pl D → Prop} (hP : P q.v) :
    g ∈ grpAt V P := by
  rw [grpAt, congGrp, MonoidHom.mem_ker]
  ext i j
  change Ideal.Quotient.mk _ (mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j
  rw [← Matrix.map_one (Ideal.Quotient.mk (idAt D P)) (map_zero _) (map_one _), Matrix.map_apply, Ideal.Quotient.eq]
  exact idAt_le (fun v (e : v = q.v) => e ▸ hP) (mem_idAt q (hg i j))

theorem mt_mul' (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  simp [Formalism.L2.Theta.mt]

theorem sub_mul_sub (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {V : HSp D} {g h : GA D V}
    (hg : SuppAt q.e V g) (hh : SuppAt q'.e V h) :
    (mt V g - 1) * (mt V h - 1) = 0 ∧ (mt V h - 1) * (mt V g - 1) = 0 := by
  have key : ∀ a b c d, (mt V g - 1) a b * (mt V h - 1) c d = 0 := fun a b c d => by
    rw [← hg a b, mul_comm (q.e + _), mul_assoc, idem_mul_eq_zero q q' hv (hh c d), mul_zero]
  constructor
  · ext a b
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun c _ => key _ _ _ _
  · ext a b
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun c _ => by rw [mul_comm]; exact key _ _ _ _

theorem commute_of_suppAt (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {V : HSp D} {g h : GA D V}
    (hg : SuppAt q.e V g) (hh : SuppAt q'.e V h) : Commute g h := by
  obtain ⟨h1, h2⟩ := sub_mul_sub q q' hv hg hh
  have : mt V (g * h) = mt V (h * g) := by
    rw [mt_mul', mt_mul', ← sub_eq_zero]
    have e : mt V g * mt V h - mt V h * mt V g = (mt V g - 1) * (mt V h - 1) - (mt V h - 1) * (mt V g - 1) := by
      noncomm_ring
    rw [e, h1, h2, sub_zero]
  exact Subtype.ext (Units.ext this)

theorem map_eq_one (q : SplitPt D k) (q' : SplitPt D k') (hv : q'.v ≠ q.v) {V : HSp D} {g : GA D V}
    (hg : SuppAt q'.e V g) : (mt V g).map q.pr = 1 := by
  ext i j
  have := pr_eq_zero q q' hv (hg i j)
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this, ← Matrix.map_one q.pr (map_zero _) (map_one _), Matrix.map_apply]

def matAt (q : SplitPt D k) (V : HSp D) : GA D V →* Matrix (Fin V.rank) (Fin V.rank) k :=
  (q.pr.mapMatrix.toMonoidHom.comp (Units.coeHom _)).comp (matHom V)

end GlobalTheory.SeeSaw.CellProd

open GlobalTheory.SeeSaw.CellProd in

theorem GlobalTheory.SeeSaw.prod_local_cells : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ} (G : Fin n → GLoc v), GPin G → ∀ (j' : ℕ), j' < D.R.m → ∀ (R : Subgroup (GA D (c.V j'))) (b : Fin n → ℕ) (hb : ∀ i, j' + b i = (G i).s + 1) (xs : Fin n → GA D (c.V j')), (∀ i, ∃ r ∈ R, SuppAt (G i).q.e (c.V j') r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit (G i).q).IsLoc ((G i).FY j' (b i) (hb i)) u uk ∧ uk ∈ (((G i).S.T (Fin D.R.t)).lev j' (b i) (hb i)).J ∧ xs i = r * u) → ∃ r ∈ R, r ∈ grpAt (c.V j') (· ∈ v.gP) ∧ ∃ k ∈ v.JG j', (List.ofFn xs).prod = r * k := by
  intro D c v n G hG j' hj R b hb xs H
  choose r hr hrs u uk hu huk hx using H
  have hne : ∀ i i', i ≠ i' → (G i).q.v ≠ (G i').q.v := fun i i' h e => h (hG.inj e)
  have hP : ∀ i, (G i).q.v ∈ v.gP := fun i => (hG.places _).2 ⟨i, rfl⟩
  have hus : ∀ i, SuppAt (G i).q.e (c.V j') (u i) := fun i => (hu i).1
  refine ⟨(List.ofFn r).prod, R.list_prod_mem ?_, Subgroup.list_prod_mem _ ?_, (List.ofFn u).prod,
    (hG.lev j' hj _).2 ⟨Subgroup.list_prod_mem _ ?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact hr i
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact mem_grpAt (G i).q (hrs i) (hP i)
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact mem_grpAt (G i).q (hus i) (hP i)
  · intro i a ha y hy
    obtain rfl : a = b i := by have := hb i; omega
    have e : matAt (G i).q (c.V j') (List.ofFn u).prod = matAt (G i).q (c.V j') (u i) := by
      rw [map_list_prod, List.map_ofFn]
      exact prod_ofFn_single _ i fun i' hi => map_eq_one (G i).q (G i').q (hne _ _ hi) (hus i')
    have e2 : ((G i).FY j' (b i) ha).β * y.val * ((G i).FY j' (b i) ha).γ =
        ((G i).FY j' (b i) ha).β * (uk i).val * ((G i).FY j' (b i) ha).γ := hy.symm.trans (e.trans (hu i).2)
    have e3 := congrArg (fun x => ((G i).FY j' (b i) ha).γ * x * ((G i).FY j' (b i) ha).β) e2
    simp only [← Matrix.mul_assoc, GlobalTheory.LocMod.Frame.γβ, Matrix.one_mul] at e3
    simp only [Matrix.mul_assoc, GlobalTheory.LocMod.Frame.γβ, Matrix.mul_one] at e3
    rw [Units.ext e3]
    exact huk i
  · rw [show xs = fun i => r i * u i from funext hx]
    exact prod_ofFn_mul r u fun i i' h => commute_of_suppAt (G i).q (G i').q (hne _ _ h.symm) (hus i) (hrs i')

end
