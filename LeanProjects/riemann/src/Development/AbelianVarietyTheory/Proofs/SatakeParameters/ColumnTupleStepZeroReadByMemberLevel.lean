import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroChartOfMemberLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelCharacterEqReferenceTupleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberRepresentativeMovedAtTwistEqTupleFramesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelReadAsReferenceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.AtTrue.StepZeroRead

set_option maxHeartbeats 4000000 in

theorem reads : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ K0 : Fam I l Z u a 0 (Nat.zero_le _) (badQ (I.rec7 l Z) Q) (fun _ => ()), ReadsOne I l Z u a 0 (Nat.zero_le _) (fun _ => ()) K0 ∧ (∀ β, (K0 β).lev.Lb = F.to0.cls0.lev.Lb ∧ (K0 β).lev.Uloc = F.to0.cls0.lev.Uloc ∧ (K0 β).lev.U = F.to0.cls0.lev.U ∧ ∀ (κ : (K0 β).lev.U) (κ' : F.to0.cls0.lev.U), κ.1 = κ'.1 → (K0 β).lev.chi κ = F.to0.cls0.lev.chi κ') ∧ ∀ c, ∃ κ : F.to0.cls0.lev.U, ((K0 ((fun _ : (I.stp u a 0).Cl => ()) (I.eCls0 l u a c))).y ⟨I.eCls0 l u a c, rfl⟩).1 = (F.to0.cls0.y c).1 * κ.1 ∧ F.to0.cls0.lev.chi κ = 1 ∧ ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1 := by
  intro B X I hI hP l Z u Ch0 chOf0 F a Q hQ hF
  obtain ⟨k, hk⟩ := hF.ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hk' : I.Reads u I.mu0 0 (fun _ => ()) (fun _ => F.to0.cls0.lev.Lb) (fun _ => F.to0.cls0.lev.U)
      (fun _ => F.to0.cls0.lev.chi) (fun c => (F.to0.cls0.y c).1) (fun c s => (F.to0.cls0.stabI c s).1) (fun _ => k ()) := hk
  choose κ hκ using GlobalTheory.T.memberRepresentative_moved_at_twist_eq_tupleFrames I hI hP l Z u F a Q hQ hF (k ()) hk'
  obtain ⟨K0, hLb, hUloc, hU, hchi, hy, hst⟩ :=
    GlobalTheory.T.stepZeroChart_of_memberLevel I hI hP l Z u a Q F.to0.cls0 κ (fun c s => hk'.stab c s)
  have nQ : ∀ v, ¬ I.UnderQ I.mu0 v := fun v ⟨P, hP', _⟩ => by
    rw [I.twistPrimes_reference_tuple_eq_empty] at hP'
    simp at hP'
  letI := StepZero.idxUnique (hI.idx_ok a)
  refine ⟨K0, ⟨fun _ => k (), ⟨?key, ?onto, ?lb, ?kstd, ?koff, ?kT, ?pt, ?lev, ?chr, ?stab⟩, ?off⟩, ?levs, ?ys⟩
  case key =>
    intro c c'
    exact ⟨fun _ => ⟨Subsingleton.elim _ _, Chart0.cos0 I _ _⟩, fun _ => rfl⟩
  case onto =>
    intro β
    obtain ⟨c0, -⟩ := hk'.onto ()
    exact ⟨I.eCls0 l u a c0, Subsingleton.elim _ _⟩
  case lb =>
    intro β x
    cases β
    rw [hLb]
    exact hk'.lb () x
  case kstd => exact fun _ => hk'.k_std ()
  case koff => exact fun _ v hT _ _ => hk'.k_off () v hT (nQ v) (Or.inl rfl)
  case kT => exact fun _ => hk'.k_T ()
  case pt =>
    intro c
    obtain ⟨c0, rfl⟩ := (I.eCls0 l u a).surjective c
    show PtOf ((show GA B (B.R.N 0) from ((K0 ()).y ⟨I.eCls0 l u a c0, rfl⟩).1) * k ()) _
    rw [hy c0]
    exact (hκ c0).2.2
  case lev =>
    intro c x q hq
    obtain ⟨c0, rfl⟩ := (I.eCls0 l u a).surjective c
    change PtOf ((show GA B (B.R.N 0) from ((K0 ()).y ⟨I.eCls0 l u a c0, rfl⟩).1) * x * k ()) q at hq
    rw [hy c0] at hq
    show x ∈ (K0 ()).lev.U ↔ _
    rw [hU]
    exact GlobalTheory.T.stepZero_level_readAsReference I hI hP l Z u a _ _ _ _ _ (k ()) hk' c0 (κ c0) _ rfl (hκ c0).2.2 x q hq
  case chr =>
    intro c x κ' hg hq
    obtain ⟨c0, rfl⟩ := (I.eCls0 l u a).surjective c
    change PtOf ((show GA B (B.R.N 0) from ((K0 ()).y ⟨I.eCls0 l u a c0, rfl⟩).1) * x.1 * k ()) _ at hq
    rw [hy c0] at hq
    let x' : F.to0.cls0.lev.U := ⟨x.1, hU ▸ x.2⟩
    show (((K0 ()).lev.chi x : ℂˣ) : ℂ) = _
    rw [hchi x x' rfl]
    exact GlobalTheory.T.stepZero_levelCharacter_eq_referenceTuple I hI hP l Z u a _ _ _ _ _ (k ()) hk' c0 (κ c0) _ rfl (hκ c0).2.2 (hκ c0).2.1 x' κ' hg hq
  case stab => exact fun c s => hst ⟨c, rfl⟩ s
  case off => exact fun _ v hT => hk'.k_off () v hT (nQ v) (Or.inl rfl)
  case levs => exact fun β => by cases β; exact ⟨hLb, hUloc, hU, hchi⟩
  case ys => exact fun c => ⟨κ c, hy c, (hκ c).2.1, (hκ c).1⟩

end GlobalTheory.TwU.AtTrue.StepZeroRead

end
