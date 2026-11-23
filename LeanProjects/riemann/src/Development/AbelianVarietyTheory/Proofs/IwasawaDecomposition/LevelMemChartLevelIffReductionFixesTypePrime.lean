import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianStepLevelOfChartFormsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedTopLevelChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepBeforeClNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIffRead
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetReductionFixedIffResiduesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.Mem.Col2.TypeRead in
set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.Col2.TC.typeRead_core : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0), I.StdF l Z u F → (∀ j v h, F.glevJ.fr j v h = 1) → ∀ (h1 : 1 ≤ B.R.m - 1) (β0 : Ch0 (B.R.m - 1)), ∃ w : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → Fin (B.R.N (B.R.m - 1)) → kv (I.rec7 l Z).host.F v, ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), (∃ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) → ∀ x, x ∈ F.levJ.Uloc v → (rll_put ((I.rec7 l Z).R.N (B.R.m - 1)) v x ∈ (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev.U ↔ ∀ j (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) x) *ᵥ w j v hv = w j v hv) := by
  intro B X I hI hP l Z u Ch0 chOf0 F hF hfr h1 β0
  classical
  obtain ⟨k, H⟩ := hF.mid (B.R.m - 1) h1 (succ_pred_m _)
  obtain ⟨c, rfl⟩ := H.onto β0
  have hm2 := B.R.two_le_m
  have hmj : B.R.m - 1 + 1 = B.R.m := by omega
  haveI : NeZero (B.R.N (B.R.m - 1)) := ⟨by unfold Ranks.N; have := B.R.m_add_three_le_k; omega⟩
  have hX := (base_fields_primes_ok B X).1
  have hPr := (base_fields_primes_ok B X).2.1
  obtain ⟨wOf, hwOf, hwP, -⟩ := GlobalTheory.Mem.TypePrimes.primes_over_places B.fields (B.primes X) B.sp.cm hPr
  have hres := fun (a : Fin 2) (v : HeightOneSpectrum (𝓞 B.host.F)) (h : (B.host.g a : 𝓞 B.host.F) ∈ v.asIdeal) =>
    GlobalTheory.SplitResidue.exists_residue_equiv B.host.F B.host.E v (wOf a v h).1 (F.gl.phi a v h)
    (B.fields.conjO ((B.primes X).piG a)) (fun t => congrArg Prod.fst (F.gl.sp_alg a v h t)) (by
      have := F.gl.sp_pi a v h
      rw [hF.gl.piG] at this
      exact this) (hwP a v h).1
  choose ρ e hρ hρe using hres
  let P0 : ∀ a v h, rowSG (B.primes X) I.sel (I.tup I.mu0) := fun a v h => ⟨(wOf a v h).1, Finset.mem_union_left _ (wOf a v h).2⟩
  refine ⟨fun a v h i => e a v h (cvec ((I.stp u I.mu0 (B.R.m - 1)).rep c) (P0 a v h) i), fun v hv x hx => ?_⟩

  obtain ⟨a, ha⟩ := hv
  have hgram : gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) = 1 :=
    ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 (B.R.m - 1) (Nat.sub_le _ _)).1
  have hB := basePi_of_ok hX hPr u
  have hLb : F.levJ.Lb = baseLb B.host.E (B.R.N (B.R.m - 1)) ((B.primes X).vT u) := by
    ext y
    rw [← F.levJ_Lb h1 (chOf0 _ c)]
    refine (H.lb _ y).trans (Iff.trans ?_ (rll_mem_baseLb _ _ y).symm)
    simp only [baseL, Set.mem_setOf_eq]
    have hl : (lastIdx (B.R.N (B.R.m - 1))).1 + 1 = B.R.N (B.R.m - 1) := by
      have := NeZero.pos (B.R.N (B.R.m - 1)); simp only [lastIdx]; omega
    constructor
    · intro h
      choose r hr1 hr2 using h
      exact ⟨r, fun i => (hr1 i).symm, (hB.dvd _).2 (hr2 _ hl)⟩
    · rintro ⟨r, hr1, hr2⟩ i
      refine ⟨r i, (hr1 i).symm, fun hi => ?_⟩
      obtain rfl : i = lastIdx (B.R.N (B.R.m - 1)) := Fin.ext (by omega)
      exact (hB.dvd _).1 hr2
  have hxL : x ∈ levelVL B.sp.cm.sig (1 : Matrix (Fin (B.R.N (B.R.m - 1))) (Fin (B.R.N (B.R.m - 1))) B.host.E) v
      (baseLb B.host.E (B.R.N (B.R.m - 1)) ((B.primes X).vT u)) := by
    have := F.levJ.Uloc_lev v hx
    have hgram' : gramN (I.rec7 l Z) ((I.rec7 l Z).R.m - 1) (Nat.sub_le _ _) = 1 := hgram
    rw [hLb] at this
    rw [hgram'] at this
    exact this
  have hT : v ∉ plUnder B.host.F ((B.primes X).vT u) := fun hvT => rls_T_notUnder hPr u v
      ((mem_plUnder_iff_norm B.sp.cm (rls_vT_iff hX hPr u) ((B.primes X).T u) (hPr.piT_norm u) v).1 hvT)
      ⟨(wOf a v ha).1, (wOf a v ha).2, (hwOf a v ha _).2 rfl⟩
  have hJ := put_mem_J0 B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) v hT x hxL
  have hUA := congruence_le_adelic_unitary B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) hJ
  refine (mem_iff_read H c _ hUA).trans ?_

  obtain ⟨b, hb⟩ : ∃ b, (c.1 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) (B.R.m - 1)).1 = some b :=
    Option.isSome_iff_exists.1 (c.1.2.2 (by omega))
  have hgrp : levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) (B.R.m - 1) c.1 = (I.idx I.mu0).levG (B.R.m - 1) b := by
    simp only [levGAt, hb, Option.elim]
  have hred := fun a' (h' : (B.host.g a' : 𝓞 B.host.F) ∈ v.asIdeal) => red_put_at B.sp.cm _ _ (B.primes X).vGs F.gl a' v h' (wOf a' v h') (e a' v h')
    (fun z => ⟨hρ a' v h' z ▸ (ρ a' v h' z).2, (congrArg (IsLocalRing.residue _) (Subtype.ext (hρ a' v h' z).symm)).trans (hρe a' v h' z)⟩) x hJ
  have hm0 : (redG B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs ⟨_, hJ⟩)⁻¹ ∈
      (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) (B.R.m - 1) c.1).grp := by
    rw [hgrp]
    refine inv_mem (fun w _ => ?_)
    by_cases hw : w = wOf a v ha
    · subst hw
      apply GlobalTheory.Mem.LastGrp.mem_levG_last _ _ _ _ _ _ _ hX hPr hI.sel_ok (hI.idx_ok I.mu0) (hI.sharp I.mu0) (B.R.m - 1) hmj b
        (wOf a v ha) _ (e a v ha)
      obtain ⟨M, hM, hMe⟩ := (F.glevJ.mem a v ha x (F.levJ.Uloc_lev v hx)).1 hx
      rw [hfr a v ha] at hMe
      have e2 : Matrix.GeneralLinearGroup.map (e a v ha).toRingHom
          (redG B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs ⟨_, hJ⟩ (wOf a v ha)) = M := by
        apply Units.ext
        refine Eq.trans ?_ ((hred a ha).trans hMe.symm)
        rfl
      rw [e2]
      exact hM
    · have e1 := red_put_off B.sp.cm (B.R.N (B.R.m - 1)) _ (B.primes X).vGs v x hJ w (fun h => hw ((hwOf a v ha w).1 h))
      show _ ∈ ((I.idx I.mu0).levG (B.R.m - 1) b w).H
      erw [e1]
      exact one_mem _

  have hQ : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := by
    rw [I.trueColumn_tuple_trivial_eq_one]
    exact twistPrimes_trivialTuple_empty I.sel I.S
  have hvG : ∀ P : rowSG (B.primes X) I.sel (I.tup I.mu0), P.1 ∈ (B.primes X).vGs := fun P =>
    (Finset.mem_union.1 P.2).resolve_right fun h => by simp [hQ] at h
  have hdeg : ∀ P : rowSG (B.primes X) I.sel (I.tup I.mu0), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 := fun P =>
    GlobalTheory.UnfoldTwoSided.degOne_bad hX hPr hI.sel_ok P
  have hcos := fun P => GlobalTheory.T.couplingCoset_reduction_fixed_iff_residues hmj ((I.stp u I.mu0 (B.R.m - 1)).rep c)
    ((I.stp u I.mu0 (B.R.m - 1)).act c.1 (1, ⟨_, hm0⟩, 1) ((I.stp u I.mu0 (B.R.m - 1)).rep c))
    (redG B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs ⟨_, hJ⟩)⁻¹ rfl (Set.image_id _) P (hvG P) (hdeg P)
  constructor
  · rintro ⟨hJ', hm', hc'⟩ j hv
    have hfix := (hcos (P0 j v hv)).1 (congrFun hc' _)
    have hfix' := (fix_inv_iff _ _).1 hfix
    have key := (fix_map_iff (e j v hv) _ _).2 hfix'
    rw [hfr j v hv]
    have hM : redM (I.rec7 l Z).host.F v (F.gl.mat j v hv 1 x) = _ := (hred j hv).symm
    rw [hM]
    exact key
  · intro hall
    refine ⟨hJ, hm0, funext fun P => (hcos P).2 ?_⟩
    refine (fix_inv_iff _ _).2 ?_
    by_cases hw : (⟨P.1, hvG P⟩ : (B.primes X).vGs) = wOf a v ha
    · have hP : P = P0 a v ha := Subtype.ext (show P.1 = (wOf a v ha).1 from congrArg Subtype.val hw)
      subst hP
      have h2 := hall a ha
      rw [hfr a v ha] at h2
      refine (fix_map_iff (e a v ha) _ _).1 ?_
      have hM : redM (I.rec7 l Z).host.F v (F.gl.mat a v ha 1 x) = _ := (hred a ha).symm
      rw [hM] at h2
      exact h2
    · have e1 := red_put_off B.sp.cm (B.R.N (B.R.m - 1)) _ (B.primes X).vGs v x hJ ⟨P.1, hvG P⟩
        (fun h => hw ((hwOf a v ha _).1 h))
      erw [e1]
      simp

end
