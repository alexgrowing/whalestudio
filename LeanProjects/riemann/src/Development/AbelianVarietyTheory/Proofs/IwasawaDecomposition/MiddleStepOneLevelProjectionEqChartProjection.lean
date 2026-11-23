import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Formalism.LocalToGlobal.Columns.TiedLv
import Formalism.LocalToGlobal.Columns.TiedUpDnA
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt

set_option maxHeartbeats 4000000 in

theorem pr_lvC_eq_lv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) v (c : ((I.rec7 l Z).mem u).C.cls i), (∀ (z : Formalism.L2.Forms.Ld (I.rec7 l Z) u i (le_of_succ_m h2) c) (z' : LdG (I.rec7 l Z) i (le_of_succ_m h2) (clsCrd (I.rec7 l Z) u i (le_of_succ_m h2) c)), z'.1 = z.1 → ((F u).lvC i h1 h2).pr v c z' = ((F u).lv i (le_of_succ_m h2)).pr v c z) ∧ ∀ (z : Formalism.L2.Forms.Lk (F u).atT i (le_of_succ_m h2) v c) (z' : LkG (I.rec7 l Z) i (le_of_succ_m h2) (PvG (F u).atT.res v) (clsCrd (I.rec7 l Z) u i (le_of_succ_m h2) c)), z'.1 = z.1 → ((F u).lvC i h1 h2).prk v c z' = ((F u).lv i (le_of_succ_m h2)).prk v c z := by
  intro B X I hI hP l Z H F hS hC u i h1 h2 v c
  have hi := le_of_succ_m h2
  obtain ⟨-, -, -, hsp⟩ := spaces_in_coordinates I hI hP l Z
  obtain ⟨hg, -, hL⟩ := hsp i hi
  have hlat := (hL u I.mu0).1 c
  obtain ⟨hF, hFC⟩ := hS u
  have hcl : clsCrd (I.rec7 l Z) u i hi c = (((I.stp u I.mu0 i).rep c).1.1.deco).1.L := hlat
  have hres := hF.res
  have hsep := sepElt_of_ok l.pr u
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hLd : Ld (I.rec7 l Z) u i hi c = (((I.stp u I.mu0 i).rep c).1.1.deco).1.Lsh := by
    show dualL (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) (clsCrd (I.rec7 l Z) u i hi c) = _
    rw [hg, hcl]
    exact rlc_span_dualSet (I.rec7 l Z).sp.cm _ _
  have hPv : (F u).atT.Pv v = (show (B.primes X).vT u from v).1.asIdeal := by
    ext x
    show (F u).atT.res v x = 0 ↔ _
    rw [hres]
    exact Ideal.Quotient.eq_zero_iff_mem (I := (show HeightOneSpectrum (𝓞 B.fields.E) from v.1).asIdeal)
  have hLk : Formalism.L2.Forms.Lk (F u).atT i hi v c = (((I.stp u I.mu0 i).rep c).1.1.deco).1.LshKer v := by
    rw [lv_LshKer_eq _ hsep v]
    show clsCrd (I.rec7 l Z) u i hi c ⊔ (F u).atT.Pv v • Ld (I.rec7 l Z) u i hi c = _
    rw [hLd, hcl, hPv]
    rfl
  obtain ⟨s, hs⟩ : ∃ s : 𝓞 (I.rec7 l Z).host.E, s = cO B.fields.E ((B.primes X).piT u) := ⟨_, rfl⟩
  have hu : (F u).atT.res v s ≠ 0 := by
    rw [hres, hs]
    exact fun h => hsep.off v (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hd : ∀ x : Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E, x ∈ Ld (I.rec7 l Z) u i hi c →
      s • x ∈ (((I.stp u I.mu0 i).rep c).1.1.deco).1.N := fun x hx => by
    rw [hs]
    exact (((I.stp u I.mu0 i).rep c).1.1.deco).2.smul_Lsh_mem_N hsep.conj (hLd ▸ hx)
  have hk : ∀ x : Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E, x ∈ Formalism.L2.Forms.Lk (F u).atT i hi v c →
      s • x ∈ (((I.stp u I.mu0 i).rep c).1.1.deco).1.dnN v := fun x hx => by
    rw [hs]
    exact (le_sup_left : _ ≤ (((I.stp u I.mu0 i).rep c).1.1.deco).1.dnN v) (lv_smul_LshKer_mem _ hsep v (hLk ▸ hx))
  refine ⟨fun z z' e => ?_, fun z z' e => ?_⟩
  · obtain ⟨x, hx⟩ := z
    obtain ⟨x', hx'⟩ := z'
    have e' : x' = x := e
    subst e'
    have e1 := hF.pr i hi v c (s • ⟨x', hx⟩) (hd x' hx)
    have e2 := (hFC.1 i h1 h2).1 v c (s • ⟨x', hx'⟩) (hd x' hx)
    rw [((F u).lv i hi).pr_smul] at e1
    rw [((F u).lvC i h1 h2).pr_smul] at e2
    exact smul_right_injective _ hu (e2.trans e1.symm)
  · obtain ⟨x, hx⟩ := z
    obtain ⟨x', hx'⟩ := z'
    have e' : x' = x := e
    subst e'
    have e1 := hF.prk i hi v c (s • ⟨x', hx⟩) (hk x' hx)
    have e2 := (hFC.1 i h1 h2).2 v c (s • ⟨x', hx'⟩) (hk x' hx)
    rw [((F u).lv i hi).prk_smul] at e1
    rw [((F u).lvC i h1 h2).prk_smul] at e2
    exact smul_right_injective _ hu (e2.trans e1.symm)

end GlobalTheory.Mem.Col2.HAt
