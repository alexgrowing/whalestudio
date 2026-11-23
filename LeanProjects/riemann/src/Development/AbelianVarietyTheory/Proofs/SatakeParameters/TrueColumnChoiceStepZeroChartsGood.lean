import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnTupleStepZeroReadByMemberLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InclMulInvMul
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentTypeLevelCharacterFiniteOrderRootsOfUni
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.TwU.AtTrue.charts_zero_good : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ Kc : Fam I l Z u a 0 (Nat.zero_le _) (badQ (I.rec7 l Z) Q) (fun _ => ()), (ReadsOne I l Z u a 0 (Nat.zero_le _) (fun _ => ()) Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1) ∧ (∀ β, (Kc β).lev.Lb = F.to0.cls0.lev.Lb ∧ (Kc β).lev.Uloc = F.to0.cls0.lev.Uloc ∧ (Kc β).lev.U = F.to0.cls0.lev.U ∧ ∀ (κ : (Kc β).lev.U) (κ' : F.to0.cls0.lev.U), κ.1 = κ'.1 → (Kc β).lev.chi κ = F.to0.cls0.lev.chi κ') ∧ ∀ c, ∃ κ : F.to0.cls0.lev.U, ((Kc ((fun _ : (I.stp u a 0).Cl => ()) (I.eCls0 l u a c))).y ⟨I.eCls0 l u a c, rfl⟩).1 = (F.to0.cls0.y c).1 * κ.1 ∧ F.to0.cls0.lev.chi κ = 1 ∧ ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1 := by
  intro B X I hI hP l Z u Ch0 chOf0 F a Q hQ hStd
  obtain ⟨K0, hR, hEq, hy⟩ := GlobalTheory.T.columnTuple_stepZero_read_by_memberLevel I hI hP l Z u F a Q hQ hStd
  obtain ⟨N, hN, hNc⟩ := GlobalTheory.unipotent_type_character_finite_order _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F.to0.glev0 ℂ (RingHom.id ℂ)
    (fun i => (I.rec7 l Z).host.g_prime i) (fun i => ⟨_, Complex.isPrimitiveRoot_exp _ ((I.rec7 l Z).host.g_prime i).ne_zero⟩)
  have hPr := l.pr
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  haveI : NeZero (B.R.N 0) := ⟨(B.R.N_pos 0).ne'⟩
  obtain ⟨-, -, -, hc⟩ := TC.spaces_in_coordinates I hI hP l Z
  obtain ⟨hgr, -, -⟩ := hc 0 (Nat.zero_le _)
  have hB := basePi_of_ok hX hPr u
  have hLb : ∀ β, (K0 β).lev.Lb = baseLb B.fields.E (B.R.N 0) ((B.primes X).vT u) := fun β => by
    obtain ⟨k, hk⟩ := hR.readsK
    ext x
    exact (hk.lb β x).trans (GlobalTheory.Mem.Col2.Reside.mem_baseLb hPr u _ x).symm
  have hlaws := fun β => GlobalTheory.Mem.Col2.Reside.swapLaws B.sp.cm hB (hPr.T_prime u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => hPr.vT_norm u P hP) hgr (K0 β).lev (hLb β)
  choose hl hk using hlaws
  refine ⟨fun β => { K0 β with lev := GlobalTheory.Mem.Col2.Reside.swap (K0 β).lev _ (hl β) }, ⟨hR, fun β => ⟨hk β, N, hN, fun κ => ?_⟩⟩, fun β => hEq β, hy⟩
  have hm : κ.1 ∈ F.to0.cls0.lev.U := (hEq β).2.2.1 ▸ κ.2
  have e := (hEq β).2.2.2 κ ⟨κ.1, hm⟩ rfl
  show (K0 β).lev.chi κ ^ N = 1
  rw [e]
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact (hNc _).1)
