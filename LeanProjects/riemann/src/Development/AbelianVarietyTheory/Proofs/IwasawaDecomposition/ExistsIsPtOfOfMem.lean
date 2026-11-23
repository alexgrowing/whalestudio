import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

namespace GlobalTheory.Mem.Col2.ChiFinTop

open GlobalTheory.Mem.Col2.PtExist

theorem exists_isPtOf_of_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q = ∅)
    {g : GL (Fin n) (AfE F E)} (hg : g ∈ UAd hc n) : ∃ p : DecoF E n ST SG Q, IsPtOf hc g p := by
  classical
  obtain ⟨p, hd, -⟩ := GlobalTheory.Mem.ColAd.exists_near (ST := ST) (SG := SG) (Q := Q) hc 0 hg
  have hN : Formalism.UG.CS.globLat g (stdLat E n) = p.deco.1.N := congrArg Deco.N hd
  refine ⟨p, hg, hN ▸ carries_globLat g, fun P v hv i hi => ?_, fun P v hv i => ?_, fun P => absurd P.2 (by simp [hQ])⟩
  · have e : lastIdx n = i := Fin.ext (by simp [lastIdx]; omega)
    rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv), e]
    exact hasRes_redA _ ((mem_globLat g v).1 hv i)
  · rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv)]
    exact hasRes_redA _ ((mem_globLat g v).1 hv i)

theorem chi_top_root_rat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (K : ClsTied (D := (I.rec7 l Z)) u B.R.m le_rfl), (∃ k, I.Reads u I.mu0 B.R.m (fun _ => ()) (fun _ => K.lev.Lb) (fun _ => K.lev.U) (fun _ => K.lev.chi) (fun c => (K.y c).1) (fun c s => (K.stabI c s).1) k) → ∃ n : ℕ, 0 < n ∧ ∀ x : K.lev.U, ((K.lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : B.LL, B.embLL r = ((K.lev.chi x : ℂˣ) : ℂ) := by
  intro B X I hI hP l Z u K ⟨k, hR⟩
  obtain ⟨c, -⟩ := hR.onto ()
  have hpt := hR.pt c
  have hg1 : gramN (I.rec7 l Z) B.R.m le_rfl = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 B.R.m le_rfl).1
  have eU : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) B.R.m le_rfl) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      UAd B.sp.cm (B.R.N B.R.m) := by rw [hg1]; rfl
  have hxU : ∀ x : K.lev.U, x.1 ∈ UAd B.sp.cm (B.R.N B.R.m) := fun x => eU ▸ ((K.lev.U_eq x.1).1 x.2).1
  have hyk := hpt.uni
  obtain ⟨p0, hp0, -⟩ := hR.k_std ()
  have hk := hp0.uni
  have hQ : I.Q I.mu0 = ∅ := by
    show QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅
    rw [I.trueColumn_tuple_trivial_eq_one]
    exact twistPrimes_trivialTuple_empty I.sel I.S

  have hQ' : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := hQ
  obtain ⟨N, hN, hroot⟩ : ∃ N, 0 < N ∧ ∀ κ : (I.stp u I.mu0 B.R.m).G c.1, (I.stp u I.mu0 B.R.m).chr c.1 κ ^ N = 1 := by
    let Λ := levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) B.R.m c.1
    let Θ := levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) B.R.m c.1
    haveI : Subsingleton ↥Θ.grp := ⟨fun a b => Subtype.ext (funext fun P => absurd P.2 (by simp [hQ']))⟩
    haveI : Finite ↥Λ.grp := inferInstance
    refine ⟨Nat.card (↥Λ.grp × ↥Θ.grp), Nat.card_pos, fun κ => ?_⟩
    have h2 : κ.2 ^ Nat.card (↥Λ.grp × ↥Θ.grp) = 1 := pow_card_eq_one'
    rw [← map_pow]
    show Λ.chr ((κ ^ Nat.card (↥Λ.grp × ↥Θ.grp)).2.1) * Θ.chr ((κ ^ Nat.card (↥Λ.grp × ↥Θ.grp)).2.2) = 1
    rw [Prod.pow_snd, h2]
    simp
  haveI : NeZero (B.R.N B.R.m) := ⟨(B.R.N_pos B.R.m).ne'⟩
  refine ⟨N, hN, fun x => ?_⟩
  let yc : GA B (B.R.N B.R.m) := (K.y c).1
  let xg : GA B (B.R.N B.R.m) := x.1
  have hxg : xg ∈ UAd B.sp.cm (B.R.N B.R.m) := hxU x
  have hyk' : yc * k () ∈ UAd B.sp.cm (B.R.N B.R.m) := hyk
  have hg : yc * xg * k () ∈ UAd B.sp.cm (B.R.N B.R.m) := by
    have h1 : yc * xg * k () = (yc * k ()) * ((k ())⁻¹ * xg * k ()) := by group
    rw [h1]
    exact mul_mem hyk' (mul_mem (mul_mem (inv_mem hk) hxg) hk)
  obtain ⟨q, hq⟩ := GlobalTheory.Mem.Col2.ChiFinTop.exists_isPtOf_of_mem (ST := (B.primes X).vT u) (SG := (B.primes X).vGs)
    (Q := QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K)) B.sp.cm hQ' hg
  obtain ⟨κ, hgam, hκq, -⟩ := (hR.lev c x.1 q hq).1 x.2
  have hchi : ((K.lev.chi x : ℂˣ) : ℂ) = B.embLL (((I.stp u I.mu0 B.R.m).chr c.1 κ : B.LLˣ) : B.LL) :=
    hR.chr c x κ hgam (by rw [hκq]; exact hq)
  refine ⟨by rw [hchi, ← map_pow, ← Units.val_pow_eq_pow_val, hroot κ, Units.val_one, map_one], _, hchi.symm⟩

end GlobalTheory.Mem.Col2.ChiFinTop

end
