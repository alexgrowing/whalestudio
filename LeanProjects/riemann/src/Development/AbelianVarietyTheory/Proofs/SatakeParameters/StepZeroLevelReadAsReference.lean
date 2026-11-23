import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDeco
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.LevZero

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem moves_iff (hI : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl)
    (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0) :
    (∃ κ : (I.stp u a 0).G c.1, (I.stp u a 0).gam c.1 κ = 1 ∧ ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1 = q ∧
        cosetIn ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)) = cosetIn ((I.stp u a 0).rep c)) ↔
      ∃ g : FormG (colLev I.Ch 0), ufGL B.fields.E (B.R.N 0) g.1 = 1 ∧ g • ((I.stp u a 0).rep c).1.1.deco = q.deco := by
  have hL := hI.idx_ok a
  have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  constructor
  · rintro ⟨κ, h1, h2, -⟩
    refine ⟨StepZero.down (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := Chart0.lvQ I a) ((I.Tp a).pref u 0) hΛ c.1 κ, h1, ?_⟩
    exact (StepZero.deco_smul (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := Chart0.lvQ I a) _ hΛ c.1 κ _).symm.trans
      (congrArg (fun q => q.deco) h2)
  · rintro ⟨g₀, h0, hg⟩
    obtain ⟨p, hp⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) q
    obtain ⟨g, h2, h3⟩ := StepZero.exists_lift ((I.Tp a).pref u 0) hy hΛ hΘ c.1 ((I.stp u a 0).rep c) p g₀ (by rw [hp]; exact hg)
    refine ⟨g, ?_, ?_, Chart0.cos0 I _ _⟩
    · exact (congrArg (fun g => ufGL B.fields.E (B.R.N 0) g.1) h2).trans h0
    · exact (congrArg (fun p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => p.1.1) h3).trans hp

theorem lev_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)) (U : Subgroup (GA B (B.R.N 0))) (chi : U →* ℂˣ) (y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)) (st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E) (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st (fun _ => k) → ∀ (c : (I.stp u I.mu0 0).Cl) (κ0 : U) (c' : (I.stp u a 0).Cl), c' = I.eCls0 l u a c → PtOf (y c * κ0.1 * k) (extTo I.SQ ((I.stp u a 0).rep c').1.1) → ∀ (x : GA B (B.R.N 0)) (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0), PtOf (y c * κ0.1 * x * k) q → (x ∈ U ↔ ∃ κ : (I.stp u a 0).G c'.1, (I.stp u a 0).gam c'.1 κ = 1 ∧ ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1 = q ∧ cosetIn ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')) = cosetIn ((I.stp u a 0).rep c')) := by
  intro B X I hI _ l _ u a Lb U chi y st k hR c κ0 c' hc' _ x q hq
  have hQ : I.Q I.mu0 = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
  have hq0 : PtOf (y c * (κ0.1 * x) * k) (extTo (I.Q I.mu0) q) := by
    rw [← mul_assoc]
    exact IsPtOf.extTo (hQ ▸ Finset.empty_subset _) (hQ ▸ Finset.disjoint_empty_right _) hq
  have h1 := hR.lev c (κ0.1 * x) (extTo (I.Q I.mu0) q) hq0
  have e : ((I.stp u a 0).rep c').1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco := by
    rw [hc']
    exact ClsZero.stepZero_corresponding_representatives_same_deco hI u a _ c
  refine (Subgroup.mul_mem_cancel_left U κ0.2).symm.trans (h1.trans ((moves_iff I hI u I.mu0 c _).trans ?_))
  refine Iff.trans ?_ (moves_iff I hI u a c' q).symm
  rw [e]
  rfl

end GlobalTheory.Mem.Col2.TC.LevZero

end
