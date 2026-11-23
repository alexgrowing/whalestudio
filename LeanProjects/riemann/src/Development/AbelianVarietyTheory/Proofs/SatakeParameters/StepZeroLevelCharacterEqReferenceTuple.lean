import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDeco
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimesReferenceTupleEqEmpty
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.StepZeroChr

theorem isPtOf_of_deco {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q Q' : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q' = ∅)
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} {p' : DecoF E n ST SG Q'} (e : p'.deco = p.deco)
    (h : IsPtOf hc g p) : IsPtOf hc g p' :=
  ⟨h.uni, e ▸ h.lat, e ▸ h.f, e ▸ h.be, fun P => (Finset.eq_empty_iff_forall_notMem.1 hQ P.1 P.2).elim⟩

set_option maxHeartbeats 1000000 in

theorem chr_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)) (U : Subgroup (GA B (B.R.N 0))) (chi : U →* ℂˣ) (y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)) (st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E) (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st (fun _ => k) → ∀ (c : (I.stp u I.mu0 0).Cl) (κ0 : U) (c' : (I.stp u a 0).Cl), c' = I.eCls0 l u a c → PtOf (y c * κ0.1 * k) (extTo I.SQ ((I.stp u a 0).rep c').1.1) → chi κ0 = 1 → ∀ (x : U) (κ : (I.stp u a 0).G c'.1), (I.stp u a 0).gam c'.1 κ = 1 → PtOf (y c * κ0.1 * x.1 * k) ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1 → ((chi x : ℂˣ) : ℂ) = B.embLL (((I.stp u a 0).chr c'.1 κ : B.LLˣ) : B.LL) := by
  intro B X I hI hP l Z u a Lb U chi y st k hR c κ0 c' hc' _ hchi x κ hκ hpt
  have hd : ((I.stp u a 0).rep c').1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco := by
    subst hc'
    exact ClsZero.stepZero_corresponding_representatives_same_deco hI u a _ c
  have hΛ := ClsZero.levelTypePrimes_stepZero_eq_colLev hI a c'.1
  have hΛ0 := ClsZero.levelTypePrimes_stepZero_eq_colLev hI I.mu0 c.1
  have hm : κ.2.1.1 ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).grp := by
    rw [hΛ0, ← hΛ]
    exact κ.2.1.2
  let κ' : (I.stp u I.mu0 0).G c.1 := (κ.1, ⟨κ.2.1.1, hm⟩, 1)
  have e1 : ((I.stp u I.mu0 0).act c.1 κ' ((I.stp u I.mu0 0).rep c)).1.1.deco =
      ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1.deco := by
    show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs) •
      ((I.stp u I.mu0 0).rep c).1.1.deco = ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs) •
      ((I.stp u a 0).rep c').1.1.deco
    rw [hd]
  have h1 : PtOf (y c * (κ0 * x).1 * k) ((I.stp u I.mu0 0).act c.1 κ' ((I.stp u I.mu0 0).rep c)).1.1 := by
    rw [Subgroup.coe_mul, ← mul_assoc]
    exact isPtOf_of_deco (RefTup.twistPrimes_reference_tuple_eq_empty B X I) e1 hpt
  have h2 := hR.chr c (κ0 * x) κ' hκ h1
  rw [map_mul, hchi, one_mul] at h2
  refine h2.trans ?_
  congr 2
  show (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr ⟨κ.2.1.1, hm⟩ *
      (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr 1 =
    (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 c'.1).chr κ.2.1 * (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 c'.1).chr κ.2.2
  rw [map_one, StepZero.chr_eq_one (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI a c'.1), StepZero.chr_congr hΛ, StepZero.chr_congr hΛ0]

end GlobalTheory.TwU.StepZeroChr
