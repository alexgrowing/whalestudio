import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CongAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiTTransport
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfOfIsIdemSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupleUnitaryFormsEquivPeriodRowForms
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EntryDatumTransportBadPrimeAnyTupleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BeforeLastStepDatumTransportBadPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepDatumTransportBadPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.AdForm.TwResid

theorem phiT_tw {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ)
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N i)) (k' y' : TC.GA B (B.R.N (i + 1)))
    (hp : TC.PtOf k p.1.1) (hpN : p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i))
    (hp' : TC.PtOf k' p'.1.1) (hpN' : p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)))
    (hq : TC.PtOf (y * k) q.1.1) (hq' : TC.PtOf (y' * k') q'.1.1) :
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)),
      (∀ P ∈ (B.primes X).vT u, GlobalTheory.Transport.CongAt B P M₀ y y' x x₀) →
      Formalism.L2.Col.phiT B.fields.K p.1.1.deco.1 p'.1.1.deco.1 x₀ = Formalism.L2.Col.phiT B.fields.K q.1.1.deco.1 q'.1.1.deco.1 x := by
  refine ⟨∏ P ∈ (B.primes X).vT u, Ideal.absNorm P.asIdeal,
    Finset.prod_pos fun P _ => Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot), fun M₀ hM x x₀ h => ?_⟩
  exact GlobalTheory.Transport.LevelDatum.phiT_eq B.fields.K (B.R.N_pos i) (B.R.N_pos (i + 1)) hp hpN hp' hpN' hq hq' x x₀
    fun P hP r s => lt_of_le_of_lt (h P hP r s) (GlobalTheory.Transport.LevelDatum.val_natCast_lt hM hP)

theorem xiAt_transport_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (hok : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ)
    (hi : i + 1 ≤ B.R.m)
    (b : Idx I.sel (I.tup a) (I.idx a) i) (b' : Idx I.sel (I.tup a) (I.idx a) (i + 1))
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N i)) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 → cosetIn q = cosetIn p → cosetIn q' = cosetIn p' →
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)),
      (∀ P ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u, ∀ r s,
        Valued.v (adAt B.host.F P
          ((HMul.hMul (HMul.hMul ((y'⁻¹ : TC.GA B (B.R.N (i + 1))).1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E))
          ((LinearMap.toMatrix' x).map (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)))
          (y.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) -
          ((LinearMap.toMatrix' x₀).map (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E))) r s)) ≤
        Valued.v ((M₀ : ℕ) : P.adicCompletion B.host.E)) →
      xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i b b' p p' x₀ =
        xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i b b' q q' x := by
  intro B X I l hok u a i hi b b' p q p' q' k y k' y' hk hN hk' hN' hq hq' hc hc'
  obtain ⟨M1, hM1, H1⟩ := phiT_tw I u a i p q p' q' k y k' y' hk hN hk' hN' hq hq'
  have Hent := GlobalTheory.T.entryDatum_transport_badPrime_anyTuple I hok l u a
  have Hcp := GlobalTheory.T.beforeLastStep_datum_transport_badPrime I hok l u a
  have Hlast := GlobalTheory.T.lastStep_datum_transport_badPrime I l hok u a
  have hrowT : ∀ (M₀ : ℕ) (x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))),
      (∀ P ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u, GlobalTheory.Transport.CongAt B P M₀ y y' x x₀) →
      (∀ P ∈ (B.primes X).vT u, GlobalTheory.Transport.CongAt B P M₀ y y' x x₀) ∧
        ∀ P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a), GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ :=
    fun M₀ x x₀ hx => ⟨fun P hP => hx P (Finset.mem_union_left _ hP), fun P => hx P.1 (Finset.mem_union_right _ P.2)⟩
  by_cases h2 : i + 2 < B.R.m
  · have hlt : i < B.R.m := by omega
    have hlt' : i + 1 < B.R.m := by omega
    choose Mf hMf Hf using fun P => Hent i h2 (b.get hlt) (b'.get hlt') P p q p' q' k y k' y' hk hN hk' hN' hq hq'
    refine ⟨M1 * ∏ P, Mf P, Nat.mul_pos hM1 (Finset.prod_pos fun P _ => hMf P), ?_⟩
    intro x x₀ hx
    obtain ⟨hvT, hrow⟩ := hrowT _ x x₀ hx
    unfold xiAt
    rw [dif_pos h2, dif_pos h2]
    unfold Formalism.L2.Col.XiEntry
    rw [H1 _ (dvd_mul_right _ _) x x₀ hvT]
    refine congrArg (HMul.hMul _) (Finset.prod_congr rfl fun P _ => ?_)
    exact Hf P _ (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ P)) _) x x₀ (hrow P)
  by_cases h3 : i + 2 = B.R.m
  · have hlt : i < B.R.m := by omega
    choose Mf hMf Hf using fun P => Hcp i h3 (b.get hlt) P p q p' q' k y k' y' hk hN hk' hN' hq hq' hc'
    refine ⟨M1 * ∏ P, Mf P, Nat.mul_pos hM1 (Finset.prod_pos fun P _ => hMf P), ?_⟩
    intro x x₀ hx
    obtain ⟨hvT, hrow⟩ := hrowT _ x x₀ hx
    unfold xiAt
    rw [dif_neg h2, dif_neg h2, dif_pos h3, dif_pos h3]
    unfold Formalism.L2.Col.XiCpl1
    rw [H1 _ (dvd_mul_right _ _) x x₀ hvT]
    refine congrArg (HMul.hMul _) (Finset.prod_congr rfl fun P _ => ?_)
    exact Hf P _ (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ P)) _) x x₀ (hrow P)
  · have h4 : i + 1 = B.R.m := by omega
    have h2m := B.R.two_le_m
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    choose Mf hMf Hf using fun P => Hlast n h4 P p q p' q' k y k' y' hk hN hk' hN' hq hq' hc
    refine ⟨M1 * ∏ P, Mf P, Nat.mul_pos hM1 (Finset.prod_pos fun P _ => hMf P), ?_⟩
    intro x x₀ hx
    obtain ⟨hvT, hrow⟩ := hrowT _ x x₀ hx
    rw [xiAt_last _ _ _ _ _ h4, xiAt_last _ _ _ _ _ h4]
    unfold xiOver
    rw [H1 _ (dvd_mul_right _ _) x x₀ hvT]
    refine congrArg (HMul.hMul _) (Finset.prod_congr rfl fun P _ => ?_)
    exact Hf P _ (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ P)) _) x x₀ (hrow P)

theorem tw_resid_datum : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) g g', g ∈ GfC _ → g' ∈ GfC _ → finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) g = ((A.K i (Nat.le_of_succ_le hi) (A.chOf i c)).y ⟨c, rfl⟩).1.1 → finM _ (rankN (I.rec7 l Z) (i + 1) hi) g' = ((A.K (i + 1) hi (A.chOf (i + 1) c')).y ⟨c', rfl⟩).1.1 → ∃ M : ℕ, 0 < M ∧ ∀ (γ γ₀ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), v ∈ stdHom _ _ → IsHalf A.e v → γ₀.map (fun r => A.e * incA (I.rec7 l Z) r) = actO _ _ g⁻¹ g'⁻¹ (γ.map fun r => A.e * incA (I.rec7 l Z) r) + M • v → A.xi i hi (A.chOf i c) (A.chOf (i + 1) c') γ₀ = B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) γ)) := by
  intro B X I hok hpins l Z u a Ch A hA i hi c c' g g' hg hg' hy hy'
  have hi0 := Nat.le_of_succ_le hi
  obtain ⟨d, hd, h1⟩ := GlobalTheory.AdForm.CongAtIdem.cong_at_idem ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))
    (rankN (I.rec7 l Z) i hi0) (rankN (I.rec7 l Z) (i + 1) hi) A.e _ hA.idem
  have hd0 := GlobalTheory.Mem.Df.disjoint_vGs_Q I hok l a
  have hQ := GlobalTheory.Mem.Col2.ColIn.Q_subset_SQ I a
  have hb := hA.base i hi0 (A.chOf i c)
  have hb' := hA.base (i + 1) hi (A.chOf (i + 1) c')
  have hr := hA.rep i hi0 c
  have hr' := hA.rep (i + 1) hi c'
  have hq := (hA.reads i hi0).pt c
  have hq' := (hA.reads (i + 1) hi).pt c'
  obtain ⟨M₀, hM₀, h2⟩ := xiAt_transport_tw I l hok u a i hi (A.b0 i (A.chOf i c)) (A.b0 (i + 1) (A.chOf (i + 1) c'))
    (A.p0 i (A.chOf i c)) ((I.stp u a i).rep c) (A.p0 (i + 1) (A.chOf (i + 1) c')) ((I.stp u a (i + 1)).rep c')
    (A.kb i (A.chOf i c)) (((A.K i hi0 (A.chOf i c)).y ⟨c, rfl⟩).1)
    (A.kb (i + 1) (A.chOf (i + 1) c')) (((A.K (i + 1) hi (A.chOf (i + 1) c')).y ⟨c', rfl⟩).1)
    (hb.1.of_extTo hQ hd0) hb.2 (hb'.1.of_extTo hQ hd0) hb'.2 (hq.of_extTo hQ hd0) (hq'.of_extTo hQ hd0) hr.2 hr'.2
  refine ⟨d * M₀, Nat.mul_pos hd hM₀, fun γ γ₀ v hv _ hγ => ?_⟩
  have hc := h1 g g' _ _ hy hy' M₀ γ γ₀ v hv hγ
  refine congrArg B.embLL ((h2 _ _ hc).trans ?_)
  rw [← hr.1, ← hr'.1]
  rfl

end GlobalTheory.AdForm.TwResid
