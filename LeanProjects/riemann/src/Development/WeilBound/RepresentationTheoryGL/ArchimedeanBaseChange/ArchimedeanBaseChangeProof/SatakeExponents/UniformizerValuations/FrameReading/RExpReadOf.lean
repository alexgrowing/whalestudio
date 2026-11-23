import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.JoinType
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ExpToSat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeEigenFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorHeckeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEigenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEigenRealStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionFixedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubEigenTailHeckeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCountTailStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusExponentTailStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardBlocksExponentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlocksExponentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentToSaturationStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.Tail

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem gap_iff {m : ℕ} (x : Fin m → ℤ) : Gap x ↔ StrictAnti x :=
  ⟨fun h i j hij => by have := h i j hij; omega, fun h i j hij => by have := h hij; omega⟩

theorem gap_neg (m : ℕ) : Gap (fun i : Fin m => -((i : ℕ) : ℤ)) := fun i j hij => by
  have : (i : ℕ) < j := hij
  show -((j : ℕ) : ℤ) + 1 ≤ -((i : ℕ) : ℤ)
  omega

theorem dcos_eq (m : ℕ) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (x : Fin m → ℤ) :
    dcos m w (tdiag ϖ x) = GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.cosetInd (fun i => ϖ ^ x i) := by
  funext g
  by_cases h : ∃ a ∈ iwGL m w, ∃ b ∈ iwGL m w, g = a * tdiag ϖ x * b
  · rw [dcos, if_pos h, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.cosetInd, Set.indicator_of_mem]
    exact h
  · rw [dcos, if_neg h, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.cosetInd, Set.indicator_of_notMem]
    exact h

theorem dcos_right (m : ℕ) (w : Pl E) (t g : GLw m w) (i : GLw m w) (hi : i ∈ iwGL m w) :
    dcos m w t (g * i) = dcos m w t g := by
  have key : (∃ a ∈ iwGL m w, ∃ b ∈ iwGL m w, g * i = a * t * b) ↔
      (∃ a ∈ iwGL m w, ∃ b ∈ iwGL m w, g = a * t * b) := by
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, ha, b * i⁻¹, mul_mem hb (inv_mem hi), by rw [← mul_assoc, ← e]; group⟩
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, ha, b * i, mul_mem hb hi, by rw [e]; group⟩
  unfold dcos
  simp only [key]

theorem smul_cancel {M : Type} [AddCommGroup M] [Module ℂ M] {δ dh c p d : ℂ} {J y : M} (hne : δ ≠ 0)
    (hd : d = δ * dh) (h : (c * (d * p)) • y = δ • J) : J = (c * p * dh) • y := by
  have e : (c * (d * p)) • y = δ • ((c * p * dh) • y) := by
    rw [smul_smul, hd]
    congr 1
    ring
  rw [e] at h
  exact (smul_right_injective M hne h).symm

set_option maxHeartbeats 1000000 in

theorem sat_of_eig (hSub : PExp.SubEig) (hCC0 : PExp.CosetCount) (hTE : PExp.TorusExp) (hDl : PExp.DlBridge)
    (hES : PExp.ExpToSat) {m : ℕ} (P : Pre E m) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ)
    (hϖ : ordL (ϖ : w.adicCompletion E) = 1) (ξ : Fin m → ℂˣ) (hm : N3.Mono ξ) (u : _)
    (hu : u ∈ fixed (prodAt P w) (iwGL m w)) (hu0 : u ≠ 0) (c : ℂ)
    (heig : ∀ x, Gap x → hkG (prodAt P w) (iwGL m w) (dcos m w (tdiag ϖ x)) u = (c * (dl w x * pw ξ x)) • u) :
    P.Sat w (Finset.univ.val.map ξ) := by
  have hD := hDl E w ϖ hϖ
  have hcon : ∀ x : Fin m → ℤ, Gap x → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.Contracts (fun i => ϖ ^ x i) := fun x hx =>
    GlobalTheory.IwahoriTraceProof.dominantContracts ϖ hD.1 x ((gap_iff x).1 hx).antitone
  have hCC := fun x hx => hCC0 (w.adicCompletion E) m _ (hcon x hx)
  obtain ⟨P', hsub, u', hu', hu0', heig'⟩ := hSub (GLw m w) _ (prodAt P w) (GlobalTheory.SmGL.isSmooth_parInd _ _)
    (iwGL m w) {x : Fin m → ℤ // Gap x} (fun x => GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.cosetInd (fun i => ϖ ^ x.1 i))
    (fun x => c * (dl w x.1 * pw ξ x.1)) (fun x => (hCC x.1 x.2).1) u hu hu0
    (fun x => by rw [← dcos_eq]; exact heig x.1 x.2)
  obtain ⟨y, hy⟩ : ∃ y : Jacquet P'.ρ (GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin m)), y = Submodule.Quotient.mk u' :=
    ⟨_, rfl⟩
  have hinj := GlobalTheory.IwahoriInj.iwahoriProj_injective (w.adicCompletion E) (Fin m) P'.V P'.ρ P'.smooth
  have hy0 : y ≠ 0 := by
    intro h0
    rw [hy] at h0
    have : GlobalTheory.SmGL.iwahoriProj P'.ρ ⟨u', hu'⟩ = 0 := Subtype.ext h0
    exact hu0' (congrArg Subtype.val (hinj (this.trans (map_zero _).symm)))
  have hyfix : y ∈ fixed (GlobalTheory.SmGL.jacBU P'.ρ) (GlobalTheory.SmGL.torusO (w.adicCompletion E) (Fin m)) :=
    hy ▸ (GlobalTheory.SmGL.iwahoriProj P'.ρ ⟨u', hu'⟩).2
  have hstep : ∀ x : Fin m → ℤ, StrictAnti x → GlobalTheory.SmGL.jacBU P'.ρ (fun i => ϖ ^ x i) y =
      (c * (∏ i, ((ξ i ^ x i : ℂˣ) : ℂ)) * (GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (fun _ : Fin m => Unit)
        (GlobalTheory.SmGL.leviTorus (w.adicCompletion E) (Fin m) fun i => ϖ ^ x i) : ℂ)) • y := by
    intro x hx
    have hg : Gap x := (gap_iff x).2 hx
    have h1 := (hCC x hg).2 P'.V P'.ρ u' hu'
    have h1' : PExp.hkS P'.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion E) (Fin m))
        (GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.cosetInd fun i => ϖ ^ x i) u' = (c * (dl w x * pw ξ x)) • u' := heig' ⟨x, hg⟩
    rw [h1', Submodule.Quotient.mk_smul, ← hy] at h1
    have hne : ((((GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.deltaB (fun i => ϖ ^ x i))⁻¹ : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (inv_pos.2 (GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.deltaB_pos (fun i => ϖ ^ x i))).ne'
    exact smul_cancel hne (hD.2 m x).symm h1
  have hall := hTE (w.adicCompletion E) m P'.V P'.ρ ϖ hD.1 ξ c y hy0 hyfix hstep
  obtain ⟨hsph, b, hb, hsum⟩ := hES E w P.c m P.N P.h (fun i => P.σ i w) P' ξ hsub hm ⟨y, hy0, hall⟩
  exact ⟨b, fun i => ⟨hsph i, hb i⟩, hsum⟩

set_option maxHeartbeats 1000000 in
theorem rExpRead_of (h0 : PExp.HkEFin) (h1 : PExp.TensHk) (h2 : PExp.TensEig) (h3 : PExp.TensEigR)
    (h4 : PExp.ContrFix) (hSub : PExp.SubEig) (hCC0 : PExp.CosetCount) (hTE : PExp.TorusExp) (hDl : PExp.DlBridge)
    (hES : PExp.ExpToSat) : RExpRead := by
  intro _ E _ _ _ a b Pa Pb w ϖ ξa ξb hϖ hma hmb hJ
  obtain ⟨v, hv, hv0, heig⟩ := hJ
  have hD := hDl E w ϖ hϖ
  have hcon : ∀ {m : ℕ} (x : Fin m → ℤ), Gap x → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.Contracts (fun i => ϖ ^ x i) := fun x hx =>
    GlobalTheory.IwahoriTraceProof.dominantContracts ϖ hD.1 x ((gap_iff x).1 hx).antitone
  have hfin : ∀ {m : ℕ} (x : Fin m → ℤ), Gap x → {q : GLw m w ⧸ iwGL m w | dcos m w (tdiag ϖ x) q.out ≠ 0}.Finite :=
    fun x hx => by
      rw [dcos_eq]
      exact (hCC0 (w.adicCompletion E) _ _ (hcon x hx)).1
  have hdl : ∀ {m : ℕ} (x : Fin m → ℤ) (ξ : Fin m → ℂˣ), dl w x * pw ξ x ≠ 0 := fun {m} x ξ => by
    refine mul_ne_zero ?_ ?_
    · rw [show dl w x = _ from (hD.2 m x).symm]
      refine mul_ne_zero ?_ (Units.ne_zero _)
      exact_mod_cast (inv_pos.2 (GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.deltaB_pos _)).ne'
    · exact Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _
  let A : {x : Fin a → ℤ // Gap x} → Module.End ℂ _ := fun x =>
    PExp.hkE (prodAt Pa w) (iwGL a w) (dcos a w (tdiag ϖ x.1))
  let B : {y : Fin b → ℤ // Gap y} → Module.End ℂ _ := fun y =>
    PExp.hkE (prodAt Pb w) (iwGL b w) (dcos b w (tdiag ϖ y.1))
  have hT : ∀ x y, TensorProduct.map (A x) (B y) v =
      ((dl w x.1 * pw ξa x.1) * (dl w y.1 * pw ξb y.1)) • v := by
    intro x y
    exact (h1 _ _ _ _ (prodAt Pa w) (prodAt Pb w) (iwGL a w) (iwGL b w) _ _
      (fun g i hi => dcos_right a w _ g i hi) (fun g i hi => dcos_right b w _ g i hi) (hfin x.1 x.2) (hfin y.1 y.2)
      v hv).symm.trans (heig x.1 y.1 x.2 y.2)
  have hA : ∀ {m : ℕ} (P : Pre E m) (x : Fin m → ℤ), Gap x → ∀ z,
      PExp.hkE (prodAt P w) (iwGL m w) (dcos m w (tdiag ϖ x)) z = hkG (prodAt P w) (iwGL m w) (dcos m w (tdiag ϖ x)) z :=
    fun P x hx z => h0 _ _ (prodAt P w) _ _ (hfin x hx) z
  constructor
  · obtain ⟨l, c, hc, hu0, hAu⟩ := h2 _ _ _ _ A B (fun x => dl w x.1 * pw ξa x.1)
      (fun y => dl w y.1 * pw ξb y.1) v hv0 ⟨⟨_, gap_neg b⟩⟩ (fun x => hdl x.1 ξa) (fun y => hdl y.1 ξb) hT
    refine sat_of_eig hSub hCC0 hTE hDl hES Pa w ϖ hϖ ξa hma _ ((h4 _ _ _ _ (prodAt Pa w) (prodAt Pb w) (iwGL a w) (iwGL b w) v hv).1 l)
      hu0 c fun x hx => ?_
    exact (hA Pa x hx _).symm.trans (hAu ⟨x, hx⟩)
  · obtain ⟨l, c, hc, hu0, hBu⟩ := h3 _ _ _ _ A B (fun x => dl w x.1 * pw ξa x.1)
      (fun y => dl w y.1 * pw ξb y.1) v hv0 ⟨⟨_, gap_neg a⟩⟩ (fun x => hdl x.1 ξa) (fun y => hdl y.1 ξb) hT
    refine sat_of_eig hSub hCC0 hTE hDl hES Pb w ϖ hϖ ξb hmb _ ((h4 _ _ _ _ (prodAt Pa w) (prodAt Pb w) (iwGL a w) (iwGL b w) v hv).2 l)
      hu0 c fun y hy => ?_
    exact (hA Pb y hy _).symm.trans (hBu ⟨y, hy⟩)

theorem rExpRead : RExpRead :=
  rExpRead_of GlobalTheory.T.hecke_eigen_finite GlobalTheory.T.tensor_hecke GlobalTheory.T.tensor_eigen GlobalTheory.T.tensor_eigen_real GlobalTheory.T.contraction_fixed GlobalTheory.T.sub_eigen_tail_hecke GlobalTheory.T.coset_count_tail
    GlobalTheory.T.torus_exponent_tail GlobalTheory.T.delta_blocks_exponent GlobalTheory.T.exponent_to_saturation

end PositivityTheory.Rg.BcB.F.Tail

end
