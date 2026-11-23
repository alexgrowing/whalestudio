import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NearPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnKernelDataCompatibleStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalFramesNearAdelicAtBadPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesShapeAtBadPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepGroupCharacterInverseTypeAtLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongAtOfNearSame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointsFramesCongrAwayFromBadPrimes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi.LocVal

theorem midLev_one_one {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (al : (I.idx a).β i)
    (P : SBof I a) : GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) 1 1 := by
  classical
  obtain ⟨z, r, hr, hrx, hz⟩ := (GlobalTheory.TwU.exists_midLev_iff I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) 1).2 (Subgroup.one_mem _)
  refine ⟨r, hr, hrx, ?_⟩
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · rw [chiInv_at_type I hOk a i al P hP 1 1 r hr hrx 1 (one_mem _) (fun x _ => by simp) (congE_refl _ _ _)]
    have e : (((I.idx a).levG i al) ⟨P.1, hP⟩).lam ⟨1, one_mem _⟩ = 1 := map_one (((I.idx a).levG i al) ⟨P.1, hP⟩).lam
    rw [e]; simp
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
    rw [chiInv_at_twist I hOk a i hi al P hQ 1 1 r hr hrx 1 (one_mem _) (by simp) (congE_refl _ _ _)]
    have e : (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam ⟨1, one_mem _⟩ = 1 := map_one (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam
    rw [e]; simp

open Classical in

theorem exists_frNear_one_over {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (n : ℕ)
    (k : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))
    (hk : bc (prV (E := (I.rec7 l Z).host.E) v) k = 1) :
    ∃ fb : SBof I a → GL (Fin n) (I.rec7 l Z).host.E, FrNear I l Z a k fb ∧ ∀ P, IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → fb P = 1 := by
  obtain ⟨fb0, h0⟩ := GlobalTheory.Mem.Col2.AdT.frNear_exists I hOk l Z a n k
  refine ⟨fun P => if IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) then 1 else fb0 P, fun P => ?_, fun P hP => if_pos hP⟩
  by_cases hv : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)
  · simp only [if_pos hv]
    refine ⟨?_, ?_⟩
    · have h2 := GlobalTheory.AwayFr.congAt_of_prV_eq _ _ hv ((I.cst a).D P) k 1 (by rw [map_one, hk])
      simpa using h2
    · have h2 := GlobalTheory.AwayFr.congAt_of_prV_eq _ _ hv ((I.cst a).D P) 1 k (by rw [map_one, hk])
      simpa using h2
  · simp only [if_neg hv]
    exact h0 P

theorem nearAt_emb_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (hP : ¬ IsOver v P) (d : ℕ)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g : GL (Fin n) E) (hg : g = 1) :
    GlobalTheory.TwU.NearAt P d (y⁻¹ * GlobalTheory.Mem.Col2.ChartLevel.emb v x * y) g := by
  subst hg
  have hw : IsOver (P.under (𝓞 F)) P := by
    unfold IsOver
    rw [HeightOneSpectrum.under_asIdeal]
  have hne : P.under (𝓞 F) ≠ v := fun e => hP (e ▸ hw)
  unfold GlobalTheory.TwU.NearAt
  refine GlobalTheory.AwayFr.congAt_of_prV_eq _ _ hw d _ _ ?_
  rw [map_one, map_one, map_mul, map_mul, GlobalTheory.Mem.Col2.ChartLevel.emb_ne hne, mul_one, ← map_mul, inv_mul_cancel, map_one]

end GlobalTheory.Mem.Col2.QChi.LocVal

namespace GlobalTheory.Mem.Col2.QChi

set_option maxHeartbeats 4000000 in

theorem chi_embU_mul_valV : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Q → ∀ β (x : (K β).lev.Uloc v), (((K β).lev.chi (GlobalTheory.Mem.Col2.ChartLevel.embU (K β).lev v x) : ℂˣ) : ℂ) * GlobalTheory.Mem.Col2.QChi.valV I l Z a v x.1 = 1 := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch _ chOf K g hQ _ _ hRd hFin _ _ Lb0 _ v hvQ β x
  classical
  obtain ⟨k, hR, hk1⟩ := hRd
  obtain ⟨c, rfl⟩ := hR.onto β
  obtain ⟨fb, hfb, hfb1⟩ := LocVal.exists_frNear_one_over I hOk l Z a _ (k (chOf c)) v (hk1 _ v ((hQ v).1 hvQ))
  have hm : B.R.m - 1 < B.R.m := by omega
  have hlast : B.R.m - 1 + 1 = B.R.m := by omega
  let y0 : SBof I a → Sp B.fields.E (B.R.N (B.R.m - 1)) := fun P =>
    ((GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a _ ((I.stp u a _).rep c) P).2 hlast).1.some
  have H := lev_mid hOk hPins hR c hfb (hFin _) hm y0
    (Rel := fun P g z => MidAt I hm c.1 P g z ∧ (B.R.m - 1 + 1 = B.R.m → GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P (g (y0 P)) (y0 P)))
    (fun _ P => ((GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a _ ((I.stp u a _).rep c) P).2 hlast).1.some_mem) (fun _ _ _ => Iff.rfl)
  have hx : bc (prV (E := (I.rec7 l Z).host.E) v) (GlobalTheory.Mem.Col2.ChartLevel.emb v x.1) ∈ (K (chOf c)).lev.Uloc v := by
    rw [GlobalTheory.Mem.Col2.ChartLevel.emb_self]; exact x.2
  have key : ∀ (P : SBof I a) (j : ℕ), j = B.R.m - 2 + 1 → ∀ b, (I.idx a).h j b P = 1 := by
    rintro P j rfl b
    exact (hOk.idx_ok a).last_h b P
  have hall : ∀ P : SBof I a, ∃ g z, ((MidAt I hm c.1 P g z ∧ (B.R.m - 1 + 1 = B.R.m →
      GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P (g (y0 P)) (y0 P))) ∧
      GlobalTheory.TwU.InFrame (sm I l Z) fb (I.cst a).D P (GlobalTheory.Mem.Col2.ChartLevel.emb v x.1) g) ∧
      z = (if h : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x.1 g z then h.2.choose_spec.choose else 1) := by
    intro P
    by_cases hP : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)
    · obtain ⟨g, z, hrel, hin⟩ := H.1 P v hP _ (((K (chOf c)).lev.U_eq _).1 (GlobalTheory.Mem.Col2.ChartLevel.embU _ v x).2).1 hx
      have hnp : NearPair I l Z a v P x.1 g z := by
        refine ⟨?_, ?_⟩
        · have hmid := hrel.1
          unfold MidAt at hmid
          rw [key P _ (by omega)] at hmid
          exact hmid
        · have hin' := hin
          unfold NearV
          unfold GlobalTheory.TwU.InFrame at hin'
          rw [hfb1 P hP] at hin'
          first
            | (simp only [GlobalTheory.TwU.ratA, map_one, inv_one, one_mul, mul_one] at hin'; exact hin')
            | (erw [map_one, inv_one, one_mul, mul_one] at hin'; exact hin')
            | (convert hin' using 2; simp)
      have hh : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x.1 g z := ⟨hP, g, z, hnp⟩
      refine ⟨g, z, ⟨hrel, hin⟩, ?_⟩
      rw [dif_pos hh]
      exact nearPair_val_unique I hOk l Z a v P x.1 _ _ _ _ hnp hh.2.choose_spec.choose_spec
    · refine ⟨1, 1, ⟨⟨LocVal.midLev_one_one I hOk a _ hm _ P, fun _ t => ?_⟩, ?_⟩, by rw [dif_neg (fun h => hP (And.left h))]⟩
      · have e : ((1 : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (y0 P) - y0 P) t = 0 := by
          show (y0 P - y0 P) t = 0
          rw [sub_self]; rfl
        rw [e, mul_zero]
        simpa using GlobalTheory.TopInv.intAt_nat (P := P.1) 0
      · unfold GlobalTheory.TwU.InFrame
        exact LocVal.nearAt_emb_one v _ hP _ _ _ _ (map_one (GlobalTheory.TwU.seamGL (sm I l Z)))
  choose gg zz hgz hz using hall
  have hc := H.2.2 (GlobalTheory.Mem.Col2.ChartLevel.embU _ v x) gg zz hgz
  unfold valV
  rw [← Finset.prod_congr rfl fun P _ => hz P]
  exact hc

end GlobalTheory.Mem.Col2.QChi

end
