import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm

noncomputable section

namespace GlobalTheory.TopVal.DecoPt

section General

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix GlobalTheory.Mem.ColAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem hasRes_red {P : HeightOneSpectrum (𝓞 E)} {a : E} (ha : IntAt P a) :
    HasRes P (algebraMap E _ a) (redP P a) := by
  obtain ⟨r, s, hs, h⟩ := id ha
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (redP P a)
  refine ⟨t, ht, ?_⟩
  have h1 := reduction_spec P hs h
  rw [← ht, ← map_mul, eq_comm, Ideal.Quotient.eq] at h1
  have h2 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) P _).2 h1
  have h3 : P.valuation E (algebraMap (𝓞 E) E s) = 1 :=
    le_antisymm (HeightOneSpectrum.valuation_le_one (K := E) P s)
      (not_lt.1 fun hl => hs ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) P _).1 hl))
  have h4 : P.valuation E (algebraMap (𝓞 E) E s * (a - algebraMap (𝓞 E) E t)) < 1 := by
    rw [mul_sub, h, ← map_mul, ← map_sub]
    exact h2
  rw [map_mul, h3, one_mul] at h4
  rw [← map_sub, valued_algebraMap]
  exact h4

variable [StarRing E] {hc : CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g : GL (Fin n) (AfE F E)}

theorem adAt_pull {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (P : Q) (x : Sp E n) (i : Fin n) :
    adAt F P.1 (GlobalTheory.Mem.Col2.pullV g x i) = algebraMap E _ ((p.fr P).symm x i) := by
  have e : ratM P.1 (p.fr P) = locM P.1 g := Matrix.ext fun i j => (h.fr P i j).symm
  have h1 := ratM_mulVec (P := P.1) (p.fr P) ((p.fr P).symm x)
  rw [LinearEquiv.apply_symm_apply, e] at h1
  have h2 := congrFun (congrArg (fun v => locM P.1 g⁻¹ *ᵥ v) h1) i
  simp only [Matrix.mulVec_mulVec] at h2
  rw [← locM_mul, inv_mul_cancel, locM_one, Matrix.one_mulVec] at h2
  rw [h2]
  simp only [GlobalTheory.Mem.Col2.pullV, Matrix.mulVec, dotProduct, map_sum, map_mul, adAt_inclE, locM, Matrix.map_apply]

def noFr (p : DecoF E n ST SG Q) : DecoF E n ST (uSG SG Q) ∅ :=
  ⟨(forgetFr p, fun _ => 1), fun P => absurd P.2 (Finset.notMem_empty _)⟩

theorem isPtOf_noFr {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) : IsPtOf hc g (noFr p) := by
  refine ⟨h.uni, h.lat, h.f, fun w x hx i => ?_, fun P => absurd P.2 (Finset.notMem_empty _)⟩
  show HasRes _ _ ((forgetDeco p).be w x i)
  by_cases hw : w.1 ∈ SG
  · rw [forgetDeco_be_of_mem p w hw]
    exact h.be ⟨w.1, hw⟩ x hx i
  · have hs : (p.fr (rightOf w hw)).symm x ∈ stdAt E n w.1 := by
      refine (p.2 (rightOf w hw) _).1 ?_
      show p.fr (rightOf w hw) ((p.fr (rightOf w hw)).symm x) ∈ _
      rw [LinearEquiv.apply_symm_apply]
      exact le_locP _ _ hx
    have e : frBe w.1 (p.fr (rightOf w hw)) x = redV w.1 ((p.fr (rightOf w hw)).symm x) := if_pos hs
    rw [forgetDeco_be_of_not p w hw, e, adAt_pull h (rightOf w hw) x i]
    exact hasRes_red (mem_stdAt.1 hs i)

theorem decoOf_eq_forgetFr [NeZero n] {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) :
    decoOf ST (uSG SG Q) g = forgetFr p :=
  Subtype.ext ((rlc_decoOf_val hc n ST (uSG SG Q) h.uni).trans (near_of_isPtOf (isPtOf_noFr h) 0).deco)

end General

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem latOf_eq_toRow : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X), I.Ok → ∀ (a : I.ι) (y : GlobalTheory.Mem.Col2.TC.GA B (B.R.N B.R.m - 1)) (p : GlobalTheory.Mem.Col2.XPt (B.primes X) B.R I.sel (I.tup a)), GlobalTheory.Mem.Col2.TC.PtOf y p → GlobalTheory.TopVal.latOf I a y = GlobalTheory.Mem.Col2.toRow I.sel (I.tup a) p := by
  intro B X I _ a y p h
  letI := GlobalTheory.Mem.Col2.starE B
  exact decoOf_eq_forgetFr (F := B.fields.F) (E := B.fields.E) h

end GlobalTheory.TopVal.DecoPt

end
