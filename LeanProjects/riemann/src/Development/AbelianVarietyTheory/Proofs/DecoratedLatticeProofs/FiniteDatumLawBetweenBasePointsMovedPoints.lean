import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainMoveCharactersEqRhoUpToBase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PolOfFnOfOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalMoveClassRepIffLocalConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesPreimageUnderLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedCompAtDetIdl
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.MovedLaw

section Rat
open Formalism.L2.DIV Formalism.L2.Col
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def ratAt (F : Type) [Field F] [NumberField F] [Algebra F E] (n : ℕ) (P : HeightOneSpectrum (𝓞 E)) : Subgroup (GL (Fin n) (AfE F E)) :=
  (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap E (P.adicCompletion E))).range.comap
    (Matrix.GeneralLinearGroup.map (n := Fin n) (adAt F P))

theorem mem_ratAt_of {P : HeightOneSpectrum (𝓞 E)} {g : GL (Fin n) (AfE F E)} (M : Matrix (Fin n) (Fin n) E)
    (h : ∀ r s, adAt F P ((g : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E _ (M r s)) : g ∈ ratAt F n P := by
  have e : (adAt F P).mapMatrix (g : Matrix (Fin n) (Fin n) (AfE F E)) = (algebraMap E (P.adicCompletion E)).mapMatrix M := by
    exact Matrix.ext h
  have hu : IsUnit ((adAt F P) (g : Matrix (Fin n) (Fin n) (AfE F E)).det) :=
    ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).map _
  rw [RingHom.map_det, e, ← RingHom.map_det] at hu
  have hM : M.det ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hu
    exact hu.ne_zero rfl
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hM, Units.ext e.symm⟩

theorem of_mem_ratAt {P : HeightOneSpectrum (𝓞 E)} {g : GL (Fin n) (AfE F E)} (h : g ∈ ratAt F n P) :
    ∃ γ : GL (Fin n) E, ∀ r s, adAt F P ((g : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s) := by
  obtain ⟨γ, hγ⟩ := h
  exact ⟨γ, fun r s => (congrArg (fun z : GL (Fin n) (P.adicCompletion E) => z.1 r s) hγ).symm⟩

theorem ratAt_of_pt [StarRing E] {hc : Formalism.BasicNotions.CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g : GL (Fin n) (AfE F E)}
    {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) {P : HeightOneSpectrum (𝓞 E)} (hP : P ∈ Q) : g ∈ ratAt F n P :=
  mem_ratAt_of (Matrix.of fun i j => p.fr ⟨P, hP⟩ (Pi.single j 1) i) fun r s => h.fr ⟨P, hP⟩ r s

end Rat

section Step
open Formalism.L2.DIV Formalism.L2.Col
attribute [local instance] GlobalTheory.Mem.Col2.starE
variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem fst_eq_one {u : B.Word} {a : I.ι} {j : ℕ} {b : (I.stp u a j).β} {g : (I.stp u a j).G b} (h : (I.stp u a j).gam b g = 1) :
    g.1 = 1 := Subtype.ext ((toGLm B.fields.E (B.R.N j)).injective (h.trans (map_one _).symm))

theorem act_eq {u : B.Word} {a : I.ι} {j : ℕ} {b : (I.stp u a j).β} {g : (I.stp u a j).G b} (h : (I.stp u a j).gam b g = 1)
    (p : (I.stp u a j).D b) : ((I.stp u a j).act b g p).1.1 =
      ((1, g.2.1.1, g.2.2.1) : UF B.fields.E (B.R.N j) × GLG B.fields.E (B.R.N j) (B.primes X).vGs ×
        GLQ B.fields.E (B.R.N j) (I.Q a)) • p.1.1 := by
  show ((g.1, g.2.1.1, g.2.2.1) : UF B.fields.E (B.R.N j) × GLG B.fields.E (B.R.N j) (B.primes X).vGs ×
        GLQ B.fields.E (B.R.N j) (I.Q a)) • p.1.1 = _
  rw [fst_eq_one h]

theorem cosetIn_act_congr (hI : I.Ok) {u : B.Word} {a : I.ι} {j : ℕ} {b : (I.stp u a j).β} {g : (I.stp u a j).G b}
    (h : (I.stp u a j).gam b g = 1) {p p' : (I.stp u a j).D b} (e : cosetIn p = cosetIn p') :
    cosetIn ((I.stp u a j).act b g p) = cosetIn ((I.stp u a j).act b g p') := by
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  funext P
  have hex : ∃ t, AdT.LiftsInv I g P t := by
    by_cases hP : P.1 ∈ (B.primes X).vGs
    · obtain ⟨t, ht⟩ := redGL_surjective (n := B.R.N j) P.1 (g.2.1.1 ⟨P.1, hP⟩)⁻¹
      refine ⟨t.1, t.2, fun _ x hx => ?_, fun hQ => absurd hQ (Finset.disjoint_left.1 hd hP)⟩
      rw [GlobalTheory.TopStep.redV_redGL t hx, ht]
    · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.1 P.2).resolve_left hP
      exact ⟨((g.2.2.1 ⟨P.1, hQ⟩)⁻¹).1, ((g.2.2.1 ⟨P.1, hQ⟩)⁻¹).2, fun h' => absurd h' hP, fun _ => rfl⟩
  obtain ⟨t, ht⟩ := hex
  ext z
  rw [AdT.cosetIn_act_of_liftsInv I hI u a j b g p P t h ht, AdT.cosetIn_act_of_liftsInv I hI u a j b g p' P t h ht, e]

end Step

section Main
open Formalism.L2.DIV Formalism.L2.Col
attribute [local instance] GlobalTheory.Mem.Col2.starE
variable {B : Base} {X : PreX B.toPre} {I : TC B X}

set_option maxHeartbeats 1000000 in

theorem exists_move_of_reads (hI : I.Ok) {u : B.Word} {a : I.ι} {i : ℕ} {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (TC.GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → TC.GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → TC.GA B (B.R.N i)} (hR : I.Reads u a i chOf Lb U chi y st k) (c : (I.stp u a i).Cl) (x : U (chOf c))
    (hx : x.1 ∈ UAd B.sp.cm (B.R.N i)) (hr : ∀ P ∈ I.Q a, x.1 ∈ ratAt B.host.F (B.R.N i) P) (p : (I.stp u a i).D c.1)
    (hp : TC.PtOf (k (chOf c)) p.1.1) (hc : cosetIn ((I.stp u a i).rep c) = cosetIn p) :
    ∃ g : (I.stp u a i).G c.1, (I.stp u a i).gam c.1 g = 1 ∧ TC.PtOf (x.1 * k (chOf c)) ((I.stp u a i).act c.1 g p).1.1 ∧
      cosetIn ((I.stp u a i).act c.1 g p) = cosetIn p ∧
      ((chi (chOf c) x : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 g : B.LLˣ) : B.LL) := by
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have hy : TC.PtOf (y c * k (chOf c)) ((I.stp u a i).rep c).1.1 :=
    IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  have e : y c * x.1 * k (chOf c) = y c * k (chOf c) * ((k (chOf c))⁻¹ * x.1 * k (chOf c)) := by group
  have e' : x.1 * k (chOf c) = k (chOf c) * ((k (chOf c))⁻¹ * x.1 * k (chOf c)) := by group
  have hu : y c * x.1 * k (chOf c) ∈ UAd B.sp.cm (B.R.N i) := by
    rw [e]
    exact mul_mem hy.uni (mul_mem (mul_mem (inv_mem hp.uni) hx) hp.uni)
  obtain ⟨q, hq⟩ := GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat B.sp.cm ((B.primes X).vT u) (B.primes X).vGs (I.Q a) _ hu fun P hP => by
    refine of_mem_ratAt ?_
    rw [e]
    exact mul_mem (ratAt_of_pt hy hP) (mul_mem (mul_mem (inv_mem (ratAt_of_pt hp hP)) (hr P hP)) (ratAt_of_pt hp hP))
  obtain ⟨g, h1, h2, h3⟩ := (hR.lev c x.1 q hq).1 x.2
  have hq' : TC.PtOf (y c * x.1 * k (chOf c)) ((I.stp u a i).act c.1 g ((I.stp u a i).rep c)).1.1 := h2 ▸ hq
  refine ⟨g, h1, ?_, ?_, hR.chr c x g h1 hq'⟩
  · rw [e, act_eq h1] at hq'
    obtain ⟨⟨k1, k2, k3, k4⟩, k5⟩ := GlobalTheory.Mem.Col2.TC.ChTw.Match.LocForm.conds_of_pts hy hq'
    rw [e', act_eq h1]
    exact GlobalTheory.Mem.Col2.TC.ChTw.Match.LocForm.pt_of_conds hp k1 k2 k3 k4 k5
  · rw [← cosetIn_act_congr hI h1 hc, h3, hc]

variable {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch : ℕ → Type} {A : TwDat I l Z u a Ch}

set_option maxHeartbeats 1000000 in

theorem exists_move (hI : I.Ok) (hA : A.Is) (j : ℕ) (hj : j ≤ B.R.m) (β : Ch j) (κ : A.U j β)
    (hr : ∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) j hj) κ.1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s))
    (κ₀ : TC.GA B (B.R.N j)) (h0 : finM _ (rankN (I.rec7 l Z) j hj) κ.1 = κ₀.1) :
    ∃ g : (I.stp u a j).G (A.b0 j β), (I.stp u a j).gam (A.b0 j β) g = 1 ∧
      TC.PtOf (κ₀ * A.kb j β) ((I.stp u a j).act (A.b0 j β) g (A.p0 j β)).1.1 ∧
      cosetIn ((I.stp u a j).act (A.b0 j β) g (A.p0 j β)) = cosetIn (A.p0 j β) ∧
      ((A.chi j β κ : ℂˣ) : ℂ) = B.embLL (((I.stp u a j).chr (A.b0 j β) g : B.LLˣ) : B.LL) := by
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  obtain ⟨c, rfl⟩ := hA.chOf_onto j hj β
  obtain ⟨x, hx⟩ := ((hA.U j hj _ κ.1).1 κ.2).2
  obtain rfl : κ₀ = x.1 := Units.ext (h0.symm.trans hx.symm)
  obtain ⟨hb, hc⟩ := hA.rep j hj c
  have hV : ((I.rec7 l Z).sp.X j).gram = 1 := hI.gram_X j
  have hJ : gramN (I.rec7 l Z) j hj = 1 := by
    unfold gramN
    rw [hV]
    simp
  have hu : x.1 ∈ UAd B.sp.cm (B.R.N j) := by
    have h := (((A.K j hj (A.chOf j c)).lev.U_eq x.1).1 x.2).1
    generalize x.1 = z at h ⊢
    rw [hJ] at h
    exact h
  rw [hA.chi j hj _ κ x hx, ← hb]
  exact exists_move_of_reads hI (hA.reads j hj) c x hu
    (fun P hP => by
      obtain ⟨M, hM⟩ := hr P hP
      exact mem_ratAt_of M (by rw [h0] at hM; exact hM))
    (A.p0 j (A.chOf j c)) ((hA.base j hj _).1.of_extTo (ColIn.Q_subset_SQ I a) hd) hc

set_option maxHeartbeats 1000000 in

theorem chr_root_eq (hI : I.Ok) (hA : A.Is) (j : Fin B.R.m) (k : ℕ) (hk : k ≤ B.R.m) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X k))
    (hg : g ∈ GfC _) (y : TC.GA B (B.R.N k)) (hy : finM _ (rankN (I.rec7 l Z) k hk) g = y.1) (x : (AE (I.rec7 l Z))ˣ)
    (hx : IsDetRoot _ g x) (p : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u k) (hp : TC.PtOf y p) :
    (A.chr ((j : ℕ) + 1) x : ℂ)⁻¹ =
      B.embLL (muInvDet (X := B.fields) I.sel (rowSG (B.primes X) I.sel (I.tup a)) (mUof (R := B.R) I.Ch (I.tup a) j.1)
        (muAtT (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) j.1) p.deco.1.N (frsF I.sel (I.tup a) p)) := by
  have hlev := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hQ := ColIn.Q_subset_SQ I a
  have hd : Disjoint (B.primes X).vGs (I.Q a) := Finset.disjoint_of_subset_right hQ hlev.2.1
  obtain ⟨a', ha'⟩ := GlobalTheory.Mem.DetLift.exists_isDetLift B.R B.host (B.R.N k) _ hp.uni
  have htw := (GlobalTheory.Mem.ReadTwist.isTwist_of_reads B.R B.host _ B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1
  have key := GlobalTheory.DetRootRead.chr_at_detRoot (I.rec7 l Z) (A.chr ((j : ℕ) + 1)) (I.C.mu0 j * I.xi a) (hA.chr j)
    (Formalism.L2.Host.HChar.TrivOn.mul (I.C.isMu0 j).triv htw.2.1) _ _ _ _ hg hy _ hx a' ha'
  have hfac : KDq B.host (I.Q a) ≤ ((I.C.mu0 j * I.xi a).1.comp (Chr.finPartI B.host.E)).ker := fun b hb => by
    have e : (I.C.mu0 j).1 (Chr.finPartI B.host.E b) = 1 := reference_characters_factor_tame (I.Q a) I.C j hb
    have e' : (I.xi a).1 (Chr.finPartI B.host.E b) = 1 := (hlev.2.2 a).1 hb
    show (I.C.mu0 j).1 (Chr.finPartI B.host.E b) * (I.xi a).1 (Chr.finPartI B.host.E b) = 1
    rw [e, e', one_mul]
  have hp' : IsPtOf (host_cmData B.R B.host) y (extTo (I.Q a) p) := by
    rw [extTo_self hd]
    exact hp
  rw [GlobalTheory.LvT.Built.KMap.map_muInvDet_pt I hI a u j p, key, ← xiDet_eq I.SQ ((KDq_anti B.host hQ).trans hfac), xiDet,
    ← tildeQ_toDtQ hQ hfac, DetProj.toDtQ_detPt B.R B.host _ _ _ _ _ hQ p hlev.1,
    ← GlobalTheory.Mem.Col2.DetSpec.mk_eq_detPt B.R B.host _ _ _ _ _ _ _ a' (hlev.1.mono hQ) hp' ha', tildeQ_mk _ _ hfac]
  rfl

set_option maxHeartbeats 1000000 in

theorem chr_root_eq_prod (hI : I.Ok) (hA : A.Is) (j : Fin B.R.m) (k : ℕ) (hk : k ≤ B.R.m) (β : Ch k) (κ : A.U k β)
    (κ₀ : TC.GA B (B.R.N k)) (h0 : finM _ (rankN (I.rec7 l Z) k hk) κ.1 = κ₀.1) (x : (AE (I.rec7 l Z))ˣ) (hx : IsDetRoot _ κ.1 x)
    (g : (I.stp u a k).G (A.b0 k β)) (hg : (I.stp u a k).gam (A.b0 k β) g = 1)
    (hq : TC.PtOf (κ₀ * A.kb k β) ((I.stp u a k).act (A.b0 k β) g (A.p0 k β)).1.1)
    (t : GLQ B.fields.E (B.R.N k) (rowSG (B.primes X) I.sel (I.tup a)))
    (ht : ∀ P, frsF I.sel (I.tup a) ((I.stp u a k).act (A.b0 k β) g (A.p0 k β)).1.1 P =
      g.1.1 * (frsF I.sel (I.tup a) (A.p0 k β).1.1 P * (t P).1)) :
    (A.chr ((j : ℕ) + 1) x : ℂ)⁻¹ = B.embLL (∏ P : rowSG (B.primes X) I.sel (I.tup a),
      rhoS (R := B.R) I.Ch I.sel (I.tup a) j.1 P ((LinearEquiv.det (t P).1 : B.fields.Eˣ) : B.fields.E)) := by
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  obtain ⟨hkA, hkAm, hxr⟩ := hA.kA k hk β
  have hκ := ((hA.U k hk β κ.1).1 κ.2).1
  have hfin : finM _ (rankN (I.rec7 l Z) k hk) (κ.1 * A.kA k β) = (κ₀ * A.kb k β).1 := by
    rw [GlobalTheory.RepLattice.finM_mul', h0, hkAm, Units.val_mul]
    rfl
  have e1 := chr_root_eq hI hA j k hk _ (mul_mem hκ hkA) _ hfin _ (GlobalTheory.TwistFinPart.isDetRoot_mul' _ _ _ _ _ hx hxr) _ hq
  have e2 := chr_root_eq hI hA j k hk _ hkA _ hkAm _ hxr _ ((hA.base k hk β).1.of_extTo (ColIn.Q_subset_SQ I a) hd)
  have hD := muDetLaw_chain (Pr := B.primes X) I.Ch I.sel (I.tup a) (I.cst a) j.1 (B.R.N k)
  rw [muAt_eq_muAtT I.Ch I.sel (I.tup a) (I.cst a) (muqTie_of_ok _ _ _ _ _ (hI.idx_ok a)) j.1 j.2] at hD
  have hN : ((I.stp u a k).act (A.b0 k β) g (A.p0 k β)).1.1.deco.1.N = (A.p0 k β).1.1.deco.1.N := by
    rw [act_eq hg]
    exact Submodule.map_id _
  have hF : frsF I.sel (I.tup a) ((I.stp u a k).act (A.b0 k β) g (A.p0 k β)).1.1 =
      fun P => frsF I.sel (I.tup a) (A.p0 k β).1.1 P * (t P).1 := funext fun P => by
    rw [ht P, fst_eq_one hg]
    exact one_mul _
  rw [hN, hF] at e1
  unfold muInvDet at e1 e2
  simp only [hD _ _ _, Finset.prod_mul_distrib] at e1
  rw [← mul_assoc, map_mul B.embLL, ← e2, map_mul, Circle.coe_mul, mul_inv, mul_comm] at e1
  exact mul_left_cancel₀ (inv_ne_zero (Circle.coe_ne_zero _)) e1

end Main

set_option maxHeartbeats 2000000 in

theorem moved_law : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (κ : A.U i α) (κ' : A.U (i + 1) γ), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) → ∀ x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (κ₀ : TC.GA B (B.R.N i)) (κ₀' : TC.GA B (B.R.N (i + 1))), finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ.1 = κ₀.1 → finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ'.1 = κ₀'.1 → ∃ (q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1)), TC.PtOf (κ₀ * A.kb i α) q.1.1 ∧ TC.PtOf (κ₀' * A.kb (i + 1) γ) q'.1.1 ∧ cosetIn q = cosetIn (A.p0 i α) ∧ cosetIn q' = cosetIn (A.p0 (i + 1) γ) ∧ ∀ w : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)), (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) q q' w) = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) (A.p0 i α) (A.p0 (i + 1) γ) w) := by
  intro B X I hI _ l Z u a Ch A hA i hi α γ κ κ' hr hr' x y hx hy κ₀ κ₀' h0 h0'
  have hi0 := Nat.le_of_succ_le hi
  obtain ⟨g, g1, g2, g3, g4⟩ := exists_move hI hA i hi0 α κ hr κ₀ h0
  obtain ⟨g', g1', g2', g3', g4'⟩ := exists_move hI hA (i + 1) hi γ κ' hr' κ₀' h0'
  refine ⟨_, _, g2, g2', g3, g3', fun w => ?_⟩
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨t, t', ht, ht', law⟩ := GlobalTheory.KerDia.Eqv.xiAt_law (Pr := B.primes X) hX hPr hI.sel_ok (hI.T_mem u) hI.g_mem (hI.idx_ok a)
    (hI.sharp a) hi (A.b0 i α) (A.b0 (i + 1) γ) g g' (A.p0 i α) (A.p0 (i + 1) γ)
  have e1 := chr_root_eq_prod hI hA ⟨i, hi⟩ i hi0 α κ κ₀ h0 x hx g g1 g2 t ht
  have e2 := chr_root_eq_prod hI hA ⟨i, hi⟩ (i + 1) hi γ κ' κ₀' h0' y hy g' g1' g2' t' ht'
  have key := congrArg B.embLL (law w)
  have hw : (g'.1.1.toLinearMap ∘ₗ w ∘ₗ g.1.1.symm.toLinearMap : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))) = w := by
    rw [fst_eq_one g1, fst_eq_one g1']
    rfl
  simp only [unitInv_rho I.Ch I.sel (I.tup a) i _ _, Finset.prod_mul_distrib, Finset.prod_inv_distrib] at key
  rw [hw, map_mul, map_mul, map_inv₀, map_mul, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀] at key
  rw [g4, g4', e1, inv_eq_iff_eq_inv.1 e2]
  exact ((mul_comm _ _).trans key).trans (congrArg (· * _) (mul_comm _ _))

end GlobalTheory.AdForm.MovedLaw
