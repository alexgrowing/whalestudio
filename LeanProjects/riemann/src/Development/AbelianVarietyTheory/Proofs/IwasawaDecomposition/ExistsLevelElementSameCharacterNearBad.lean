import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceBadPrimeIffCompletionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelElt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarNe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdAtEntryEqOneOfNotOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LevelElt

theorem one_prime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad), ChiFin I l Z S → ∀ (P : SBof I a), P.1 ∈ I.Q a → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ (N : ℕ) (g₁ g₂ : GA B (B.R.N i)), ∃ z : S.U, S.chi z = 1 ∧ (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') z.1 = 1) ∧ GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z.1 ∧ ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P.1 (((g₁ * (show GA B (B.R.N i) from z.1) * g₂ : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.OnePrime.exists_level_elt | exact GlobalTheory.Mem.Col2.AdT.OnePrime.exists_level_elt | (intros; apply GlobalTheory.Mem.Col2.AdT.OnePrime.exists_level_elt <;> assumption)

theorem place_under : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (P : SBof I a), P.1 ∈ I.Q a → ∃ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∀ P' : SBof I a, P' ≠ P → ¬ Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P'.1) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.PlaceUnder.main | exact GlobalTheory.Mem.Col2.AdT.PlaceUnder.main | (intros; apply GlobalTheory.Mem.Col2.AdT.PlaceUnder.main <;> assumption)

theorem support_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F)), (∀ v', v' ≠ v → bc (prV (E := E) v') z = 1) → ∀ P : HeightOneSpectrum (𝓞 E), ¬ Formalism.L2.Col.IsOver v P → ∀ r s, adAt F P ((z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s := by
  first | exact @GlobalTheory.Mem.Col2.AdSupport.adAt_entry_eq_one_of_not_over | exact GlobalTheory.Mem.Col2.AdSupport.adAt_entry_eq_one_of_not_over | (intros; apply GlobalTheory.Mem.Col2.AdSupport.adAt_entry_eq_one_of_not_over <;> assumption)

theorem point_of_rat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (AfE F E)), g ∈ UAd hc n → (∀ P ∈ Q, ∃ γ : GL (Fin n) E, ∀ r s, adAt F P ((g : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s)) → ∃ p : DecoF E n ST SG Q, IsPtOf hc g p := by
  first | exact @GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat | exact GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat | (intros; apply GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat <;> assumption)

theorem mul_comp_eq {M N : Type} [Monoid M] [Monoid N] (f : M →* N) (y a b c k : M) (h : f b = f c) :
    f (y * (a * b) * k) = f (y * a * c * k) := by
  simp only [map_mul, h, mul_assoc]

theorem entry_eq_of_eq {M : Type} [Monoid M] {n : ℕ} {R : Type} [Semiring R] (f : M →* Matrix (Fin n) (Fin n) R) (b c : M)
    (h : f b = f c) (r s : Fin n) : f b r s = f c r s := by rw [h]

set_option maxHeartbeats 4000000 in

theorem exists_level_elt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl), ChiFin I l Z (K (chOf c)).lev → ∀ κ : (K (chOf c)).lev.U, ∃ x : (K (chOf c)).lev.U, (K (chOf c)).lev.chi x = (K (chOf c)).lev.chi κ ∧ (∃ q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, PtOf ((show GA B (B.R.N i) from ((K (chOf c)).y ⟨c, rfl⟩).1) * (show GA B (B.R.N i) from x.1) * k (chOf c)) q) ∧ ∀ P : SBof I a, GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (κ.1⁻¹ * x.1) := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c hChi κ
  classical
  have : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hg : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 i hi).1
  have eU : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) = UAd B.sp.cm (B.R.N i) := by rw [hg]; rfl
  set y : GA B (B.R.N i) := ((K (chOf c)).y ⟨c, rfl⟩).1 with hy
  set kk : GA B (B.R.N i) := k (chOf c) with hkk
  have hsel : ∀ P : SBof I a, ∃ z : (K (chOf c)).lev.U, (K (chOf c)).lev.chi z = 1 ∧
      (∀ P' : SBof I a, P' ≠ P → ∀ r s, adAt B.host.F P'.1 (((show GA B (B.R.N i) from z.1) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P'.1.adicCompletion B.fields.E)) r s) ∧
      GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) z.1 ∧
      (P.1 ∈ I.Q a → ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P.1 ((((y * (show GA B (B.R.N i) from κ.1)) * (show GA B (B.R.N i) from z.1) * kk : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s)) := by
    intro P
    by_cases hP : P.1 ∈ I.Q a
    · obtain ⟨v, hv, hv'⟩ := place_under I hOk hPins l Z a P hP
      obtain ⟨z, hz1, hz2, hz3, hz4⟩ := one_prime I hOk hPins l Z a _ i hi bad (K (chOf c)).lev hChi P hP v hv ((I.cst a).D P) (y * (show GA B (B.R.N i) from κ.1)) kk
      refine ⟨z, hz1, fun P' hP' r s => ?_, hz3, fun _ => hz4⟩
      have e := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) 0 P' z.1).1
      have h2 := hv' P' hP'
      rw [e] at h2
      exact support_one z.1 v hz2 P'.1 h2 r s
    · refine ⟨1, map_one _, fun P' _ r s => ?_, GlobalTheory.TwU.congAt_one _ _, fun h => absurd h hP⟩
      show adAt B.host.F P'.1 ((1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = _
      simp only [Matrix.one_apply]
      split_ifs <;> simp
  choose zf hzf1 hzf2 hzf3 hzf4 using hsel
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
  have hchiw : (K (chOf c)).lev.chi w = 1 := by
    rw [hw, map_list_prod]
    refine List.prod_eq_one fun x hx => ?_
    rw [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [List.mem_map] at hz
    obtain ⟨P, -, rfl⟩ := hz
    exact hzf1 P
  have hpt : ∀ g : GA B (B.R.N i), g ∈ UAd B.sp.cm (B.R.N i) → (∀ P ∈ I.Q a, ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P ((g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s)) → ∃ q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, PtOf g q :=
    fun g hg hr => point_of_rat B.sp.cm _ _ _ g hg hr
  have hQsub : ∀ P ∈ I.Q a, P ∈ SBof I a := fun P hP => by
    show P ∈ uSG _ _
    exact Finset.mem_union_right _ hP
  refine ⟨κ * w, ?_, ?_, ?_⟩
  · exact (map_mul (K (chOf c)).lev.chi κ w).trans ((congrArg _ hchiw).trans (mul_one _))
  · obtain ⟨p0, hp0, -⟩ := hR.k_std (chOf c)
    have hyU : y ∈ UAd B.sp.cm (B.R.N i) := eU ▸ ((K (chOf c)).y ⟨c, rfl⟩).2
    have hxU : (show GA B (B.R.N i) from (κ * w).1) ∈ UAd B.sp.cm (B.R.N i) := eU ▸ (((K (chOf c)).lev.U_eq _).1 (κ * w).2).1
    have hkU : kk ∈ UAd B.sp.cm (B.R.N i) := hp0.uni
    refine hpt _ (mul_mem (mul_mem hyU hxU) hkU) fun P hP => ?_
    let P' : SBof I a := ⟨P, hQsub P hP⟩
    obtain ⟨γ, hγ⟩ := hzf4 P' hP
    refine ⟨γ, fun r s => ?_⟩
    have e1 := mul_comp_eq (cP P) y (show GA B (B.R.N i) from κ.1) (show GA B (B.R.N i) from w.1) (show GA B (B.R.N i) from (zf P').1) kk (hwP P')
    have e2 := congrFun (congrFun e1 r) s
    exact (cP_apply P _ r s).symm.trans (e2.trans ((cP_apply P _ r s).trans (hγ r s)))
  · intro P
    have e : κ.1⁻¹ * (κ * w).1 = w.1 := inv_mul_cancel_left κ.1 w.1
    refine (congrArg (GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P)) e).mpr ?_
    refine ((GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) ((I.cst a).D P) P w.1).2.2).mpr fun r s => ?_
    have e := entry_eq_of_eq (cP P.1) _ _ (hwP P) r s
    have D2 := ((GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a (B.R.N i) ((I.cst a).D P) P (zf P).1).2.2.1 (hzf3 P)) r s
    convert D2 using 3
    exact e

end GlobalTheory.Mem.Col2.AdT.LevelElt

end
