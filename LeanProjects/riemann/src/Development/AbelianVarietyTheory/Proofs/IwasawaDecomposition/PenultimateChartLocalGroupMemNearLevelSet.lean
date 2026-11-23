import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NearPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelElementSameCharacterNearBad
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelElementAtBadPrimesIntegralAndNearStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceMoveRationalFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdPointMatrixAndInverseIntegralAtEveryPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMiddleStepLevelInverseLiftsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceBadPrimeIffCompletionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointsFramesCongrAwayFromBadPrimes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi.NearLev

def triv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) :
    StepLevel F E σ J T f bad :=
  { S with chi := 1, chi_triv := fun _ _ => rfl }

theorem chiFin_triv {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {T i : ℕ} {hi : i ≤ B.R.m}
    {bad : Set (HeightOneSpectrum (𝓞 B.host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) :
    ChiFin I l Z (triv S) :=
  ⟨1, one_pos, fun _ _ => by simp only [triv, pow_one]; rfl⟩

set_option maxHeartbeats 4000000 in

theorem exists_level_elt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (κ : (K (chOf c)).lev.U), ∃ x : (K (chOf c)).lev.U, (∃ q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, PtOf ((show GA B (B.R.N i) from ((K (chOf c)).y ⟨c, rfl⟩).1) * (show GA B (B.R.N i) from x.1) * k (chOf c)) q) ∧ ∀ P : SBof I a, GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (κ.1⁻¹ * x.1) := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c κ
  classical
  have : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hg : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 i hi).1
  have eU : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) = UAd B.sp.cm (B.R.N i) := by rw [hg]; rfl
  set y : GA B (B.R.N i) := ((K (chOf c)).y ⟨c, rfl⟩).1 with hy
  set kk : GA B (B.R.N i) := k (chOf c) with hkk
  have hsel : ∀ P : SBof I a, ∃ z : (K (chOf c)).lev.U,
      (∀ P' : SBof I a, P' ≠ P → ∀ r s, adAt B.host.F P'.1 (((show GA B (B.R.N i) from z.1) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P'.1.adicCompletion B.fields.E)) r s) ∧
      GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) z.1 ∧
      (P.1 ∈ I.Q a → ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P.1 ((((y * (show GA B (B.R.N i) from κ.1)) * (show GA B (B.R.N i) from z.1) * kk : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s)) := by
    intro P
    by_cases hP : P.1 ∈ I.Q a
    · obtain ⟨v, hv, hv'⟩ := LevelElt.place_under I hOk hPins l Z a P hP
      obtain ⟨z, -, hz2, hz3, hz4⟩ := LevelElt.one_prime I hOk hPins l Z a _ i hi bad (triv (K (chOf c)).lev) (chiFin_triv I l Z _) P hP v hv ((I.cst a).D P) (y * (show GA B (B.R.N i) from κ.1)) kk
      refine ⟨⟨z.1, z.2⟩, fun P' hP' r s => ?_, hz3, fun _ => hz4⟩
      have e := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) 0 P' z.1).1
      have h2 := hv' P' hP'
      rw [e] at h2
      exact LevelElt.support_one z.1 v hz2 P'.1 h2 r s
    · refine ⟨1, fun P' _ r s => ?_, GlobalTheory.TwU.congAt_one _ _, fun h => absurd h hP⟩
      show adAt B.host.F P'.1 ((1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = _
      simp only [Matrix.one_apply]
      split_ifs <;> simp
  choose zf hzf2 hzf3 hzf4 using hsel
  let cP : ∀ P : HeightOneSpectrum (𝓞 B.fields.E), GA B (B.R.N i) →* Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P.adicCompletion B.fields.E) :=
    fun P => (RingHom.mapMatrix (adAt B.host.F P)).toMonoidHom.comp (Units.coeHom _)
  have cP_apply : ∀ P (g : GA B (B.R.N i)) r s, cP P g r s = adAt B.host.F P ((g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) := fun _ _ _ _ => rfl
  let ι : (K (chOf c)).lev.U →* GA B (B.R.N i) := (K (chOf c)).lev.U.subtype
  have hone : ∀ P P' : SBof I a, P' ≠ P → cP P'.1 (ι (zf P)) = 1 := fun P P' h => Matrix.ext fun r s => by
    rw [cP_apply]; exact hzf2 P P' h r s
  have hlist : ∀ (L : List (SBof I a)), L.Nodup → ∀ P' : SBof I a, cP P'.1 (ι (L.map zf).prod) = if P' ∈ L then cP P'.1 (ι (zf P')) else 1 := by
    intro L
    induction L with
    | nil => intro _ P'; simp
    | cons P L ih =>
      intro hL P'
      rw [List.nodup_cons] at hL
      rw [List.map_cons, List.prod_cons, map_mul, map_mul, ih hL.2]
      by_cases h : P = P'
      · subst h
        simp [hL.1]
      · rw [hone P P' (Ne.symm h)]
        simp [Ne.symm h]
  obtain ⟨w, hw⟩ : ∃ w : (K (chOf c)).lev.U, w = ((Finset.univ : Finset (SBof I a)).toList.map zf).prod := ⟨_, rfl⟩
  have hwP : ∀ P : SBof I a, cP P.1 (ι w) = cP P.1 (ι (zf P)) := fun P => by
    rw [hw, hlist _ (Finset.nodup_toList _) P, if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
  have hpt : ∀ g : GA B (B.R.N i), g ∈ UAd B.sp.cm (B.R.N i) → (∀ P ∈ I.Q a, ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P ((g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s)) → ∃ q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, PtOf g q :=
    fun g hg hr => LevelElt.point_of_rat B.sp.cm _ _ _ g hg hr
  have hQsub : ∀ P ∈ I.Q a, P ∈ SBof I a := fun P hP => by
    show P ∈ uSG _ _
    exact Finset.mem_union_right _ hP
  refine ⟨κ * w, ?_, ?_⟩
  · obtain ⟨p0, hp0, -⟩ := hR.k_std (chOf c)
    have hyU : y ∈ UAd B.sp.cm (B.R.N i) := eU ▸ ((K (chOf c)).y ⟨c, rfl⟩).2
    have hxU : (show GA B (B.R.N i) from (κ * w).1) ∈ UAd B.sp.cm (B.R.N i) := eU ▸ (((K (chOf c)).lev.U_eq _).1 (κ * w).2).1
    have hkU : kk ∈ UAd B.sp.cm (B.R.N i) := hp0.uni
    refine hpt _ (mul_mem (mul_mem hyU hxU) hkU) fun P hP => ?_
    let P' : SBof I a := ⟨P, hQsub P hP⟩
    obtain ⟨γ, hγ⟩ := hzf4 P' hP
    refine ⟨γ, fun r s => ?_⟩
    have e1 := LevelElt.mul_comp_eq (cP P) y (show GA B (B.R.N i) from κ.1) (show GA B (B.R.N i) from w.1) (show GA B (B.R.N i) from (zf P').1) kk (hwP P')
    have e2 := congrFun (congrFun e1 r) s
    exact (cP_apply P _ r s).symm.trans (e2.trans ((cP_apply P _ r s).trans (hγ r s)))
  · intro P
    have e : κ.1⁻¹ * (κ * w).1 = w.1 := inv_mul_cancel_left κ.1 w.1
    refine (congrArg (GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P)) e).mpr ?_
    refine ((GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) ((I.cst a).D P) P w.1).2.2).mpr fun r s => ?_
    have e := LevelElt.entry_eq_of_eq (cP P.1) _ _ (hwP P) r s
    have D2 := ((GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) ((I.cst a).D P) P (zf P).1).2.2.1 (hzf3 P)) r s
    convert D2 using 3
    exact e

set_option maxHeartbeats 4000000 in

theorem exists_stepElt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (κ : (K (chOf c)).lev.U), ∃ κ' : (I.stp u a i).G c.1, Keeps I κ' ((I.stp u a i).rep c) ∧ ∀ (P : SBof I a) (f : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) ((show GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E) from k (chOf c))⁻¹ * GlobalTheory.TwU.ratA (I.rec7 l Z).host.F f) → GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) ((GlobalTheory.TwU.ratA (I.rec7 l Z).host.F f)⁻¹ * (show GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E) from k (chOf c))) → ∀ (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), LiftsInv I κ' P g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) (fun _ : SBof I a => f) (I.cst a).D P κ.1 g := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c κ
  obtain ⟨x, ⟨q, hq⟩, hxκ⟩ := exists_level_elt I hOk hPins l Z u a i hi bad Ch chOf K k hR c κ
  have hl := hR.lev c x.1 q hq
  have hx : x.1 ∈ (fun β => (K β).lev.U) (chOf c) := x.2
  obtain ⟨κ', h3⟩ := hl.mp hx
  refine ⟨κ', ⟨h3.1, h3.2.2⟩, fun P f he hei g hL => ?_⟩
  obtain ⟨hm1, hm2, hn⟩ := GlobalTheory.T.levelElement_at_bad_primes_integral_and_near I hOk l Z u a i hi bad Ch chOf K k hR c x.1 κ' h3.1 (h3.2.1 ▸ hq) P
  obtain ⟨p, hp, hpN⟩ := hR.k_std (chOf c)
  exact GlobalTheory.T.adelicMatrixCongruence_move_rational_frame _ _ κ.1 x.1 (k (chOf c)) f _ (fun r s => (GlobalTheory.T.stdPointMatrix_and_inverse_integral_at_every_prime _ _ p hp hpN _ r s).1)
    (fun r s => (GlobalTheory.T.stdPointMatrix_and_inverse_integral_at_every_prime _ _ p hp hpN _ r s).2) hm1 hm2 (hxκ P) (hn g hL) he hei

end GlobalTheory.Mem.Col2.QChi.NearLev

namespace GlobalTheory.Mem.Col2.QChi

theorem idx_h_last_step {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) :
    ∀ (j : ℕ), j = B.R.m - 2 + 1 → ∀ (b : (I.idx a).β j) (P : SBof I a), (I.idx a).h j b P = 1 := by
  intro j hj
  subst hj
  exact (hOk.idx_ok a).last_h

set_option maxHeartbeats 4000000 in

theorem mem_nearSet_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Q → ∀ β (x : (K β).lev.Uloc v), x.1 ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch _ chOf K g hQ _ _ hk _ _ Lb0 _ v hv β x
  obtain ⟨k, hR, hk1⟩ := hk
  have hm : B.R.m - 1 < B.R.m := by omega
  have hm2 : B.R.m - 1 = B.R.m - 2 + 1 := by have := hOk.hm; omega
  obtain ⟨c, rfl⟩ := hR.onto β
  intro P hPv
  let κ : (K (chOf c)).lev.U := GlobalTheory.Mem.Col2.ChartLevel.embU (K (chOf c)).lev v x
  obtain ⟨κ', -, hκ'⟩ := NearLev.exists_stepElt I hOk hPins l Z u a (B.R.m - 1) (Nat.sub_le _ _) (badQ (I.rec7 l Z) Q) Ch chOf K k hR c κ
  obtain ⟨g', z, hMid, hL⟩ := GlobalTheory.T.exists_middleStep_level_inverse_lifts I hOk u a (B.R.m - 1) hm c.1 κ' P
  let kk : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E) := k (chOf c)
  have hv1 : bc (prV (E := (I.rec7 l Z).host.E) v) kk = 1 := hk1 (chOf c) v ((hQ v).1 hv)
  have he : GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (kk⁻¹ * 1) :=
    GlobalTheory.AwayFr.congAt_of_prV_eq v _ hPv ((I.cst a).D P) kk 1 ((map_one _).trans hv1.symm)
  have hei : GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (1⁻¹ * kk) :=
    GlobalTheory.AwayFr.congAt_of_prV_eq v _ hPv ((I.cst a).D P) 1 kk (hv1.trans (map_one _).symm)
  have hIF := hκ' P 1 (by rw [map_one]; exact he) (by rw [map_one]; exact hei) g' hL
  refine ⟨g', z, ?_, ?_⟩
  · have h := hMid
    unfold MidAt at h
    rw [idx_h_last_step I hOk a _ hm2] at h
    exact h
  · unfold GlobalTheory.TwU.InFrame at hIF
    rw [map_one, inv_one, one_mul, mul_one] at hIF
    exact hIF

end GlobalTheory.Mem.Col2.QChi

end
