import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairAlongChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilVacuumFiniteSelfDualLatticeSplitting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinUnitIsDetRoot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenPlacesAdmissibleGoodSetup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCartanInvOneSplitStab
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.StabMove

variable {D : D7}

def IntG (V : HSp D) (g : GA D V) : Prop := ∀ i j, finPart D (Formalism.L2.Theta.mt V g i j) ∈ intAE D

theorem IntG.inv {V : HSp D} (hV : V.gram = 1) {g : GA D V} (h : IntG V g) : IntG V g⁻¹ := by
  have e : ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ * V.gram.map (incA D) * Formalism.L2.Theta.mt V g = V.gram.map (incA D) := g.2
  rw [hV, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at e
  have e2 : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
    rw [← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one]
  have e3 : Formalism.L2.Theta.mt V g⁻¹ = ((Formalism.L2.Theta.mt V g).map (cA D))ᵀ := by
    rw [← Matrix.one_mul (Formalism.L2.Theta.mt V g⁻¹), ← e, Matrix.mul_assoc, e2, Matrix.mul_one]
  intro i j
  rw [e3, Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.MovedIdem.finPart_cA]
  exact GlobalTheory.MovedIdem.sigR_mem_intAE (h j i)

theorem intG_of_moves {V : HSp D} {n : ℕ} (hn : V.rank = n) {k : GA D V}
    (h : GlobalTheory.AdForm.Moves V hn k (Formalism.L2.Col.stdLat D.host.E n)) : IntG V k⁻¹ := by
  subst hn
  intro i j
  have h1 := (h (Pi.single j 1)).1 (fun a _ => by
    rw [Pi.single_apply]
    split_ifs
    · exact Submodule.one_le.1 le_rfl
    · exact zero_mem _) i
  refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
  have e : (fun a => eToEAf D ((Pi.single j 1 : Fin V.rank → D.host.E) a)) = Pi.single j 1 := by
    funext a
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs
    · exact map_one _
    · exact map_zero _
  rw [e, Matrix.mulVec_single_one] at h1
  exact h1

theorem mem_hatV_iff {n : ℕ} (u : Fin n → GlobalTheory.Ker.AfE D) :
    u ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E n) ↔ ∀ i, u i ∈ intAE D := by
  constructor
  · intro hu i
    induction hu using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨a, ha, ⟨x i, (GlobalTheory.SW.Base.mem_stdL x).1 hx i⟩, rfl⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | neg y _ hy => exact neg_mem hy
  · intro hu
    rw [← Finset.univ_sum_single u]
    refine sum_mem fun i _ => ?_
    have key : ∀ z ∈ intAE D, (Pi.single i z : Fin n → GlobalTheory.Ker.AfE D) ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E n) := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, x, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), (GlobalTheory.SW.Base.mem_stdL _).2 fun b => ?_, ?_⟩
        · rw [Pi.single_apply]
          split_ifs
          · exact x.2
          · exact isIntegral_zero
        · funext b
          rw [Pi.single_apply, Pi.single_apply]
          split_ifs
          · rfl
          · rw [TensorProduct.tmul_zero]
      | zero => rw [Pi.single_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [Pi.single_add]; exact add_mem hy hz
      | neg y _ hy => rw [Pi.single_neg]; exact neg_mem hy
    exact key _ (hu i)

theorem isMov_of_intG {V : HSp D} {k : GA D V} (h : IntG V k) (h' : IntG V k⁻¹) :
    GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt V k) (GlobalTheory.SW.stdL D.host.E V.rank) (GlobalTheory.SW.stdL D.host.E V.rank) := by
  have key : ∀ g, IntG V g → ∀ u ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E V.rank),
      GlobalTheory.Ker.fmt V g *ᵥ u ∈ GlobalTheory.Ker.hatV (GlobalTheory.SW.stdL D.host.E V.rank) := fun g hg u hu =>
    (mem_hatV_iff _).2 fun i => sum_mem (t := Finset.univ) fun j _ => GlobalTheory.GeoActCompare.TameConj.mul_mem_intAE (hg i j) ((mem_hatV_iff _).1 hu j)
  intro u
  refine ⟨fun hu => ⟨_, key _ h' u hu, ?_⟩, ?_⟩
  · rw [Matrix.mulVec_mulVec, GlobalTheory.Ker.fmt, GlobalTheory.Ker.fmt, ← Matrix.map_mul, ← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel,
      GlobalTheory.AdelicLatMove.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  · rintro ⟨u₀, h0, rfl⟩
    exact key _ h u₀ h0

theorem finM_mul (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) : finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  change (Formalism.L2.Theta.mt V (g * h)).map (toEAf D) = (Formalism.L2.Theta.mt V g).map (toEAf D) * (Formalism.L2.Theta.mt V h).map (toEAf D)
  rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.map_mul]

theorem moves_of_mul {V : HSp D} {n : ℕ} (hn : V.rank = n) {g k : GA D V} (h : IntG V k) (h' : IntG V k⁻¹) {N}
    (hN : GlobalTheory.AdForm.Moves V hn (g * k) N) : GlobalTheory.AdForm.Moves V hn g N := by
  have key : ∀ a, IntG V a → ∀ u : Fin n → EF D, (∀ i, u i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
      ∀ i, (finM V hn a *ᵥ u) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun a ha u hu i =>
    sum_mem (t := Finset.univ) fun j _ => mul_mem
      (GlobalTheory.IdemIntegral.toEAf_mem_of_finPart (ha ((finCongr hn).symm i) ((finCongr hn).symm j))) (hu j)
  intro x
  rw [hN x]
  constructor
  · intro hx
    have := key k h _ hx
    rwa [Matrix.mulVec_mulVec, ← finM_mul, _root_.mul_inv_rev, mul_inv_cancel_left] at this
  · intro hx
    have := key _ h' _ hx
    rwa [Matrix.mulVec_mulVec, ← finM_mul, ← _root_.mul_inv_rev] at this

theorem root_eq {V : HSp D} {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (hn : Even n) {g : GA D V} {x x' : (AE D)ˣ}
    (hx : IsDetRoot V g x) (hx' : IsDetRoot V g x') : χ x' = χ x := by
  obtain ⟨a, rfl⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 g x x' hx hx'
  obtain ⟨⟨η, hη⟩, h2⟩ := h
  obtain ⟨m, rfl⟩ := hn
  rw [map_mul, h2 η hη a, pow_add, ← mul_pow, GlobalTheory.VolHeckeCompare.IsEta_mul_self hη, one_pow, mul_one]

theorem unramAt_of_chrEq {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ)
    (hu : ∀ P : HeightOneSpectrum (𝓞 D.host.E), (∀ k : Fin 2, ¬ Formalism.L2.Host.OverP D.host (D.host.g k) P) → χ.UnrAt P)
    {v ε} (hv : GlobalTheory.WeilParts.NonSplitAt D v ε) : GlobalTheory.WeilParts.UnramAt ε c := by
  refine GlobalTheory.UnramOver.unramAt_of_unrAt D c χ hc v ε hv.1 fun P hP => hu P fun k hk => ?_
  obtain ⟨e, he⟩ := GlobalTheory.ChoiceAdm.exists_idem
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime k) (D.nd.g_split k) P hk).2.2.1
  exact GlobalTheory.AdTh.RecPair.under_ne he hv hP

theorem coe_stdL (n : ℕ) : (GlobalTheory.SW.stdL D.host.E n : Set (Fin n → D.host.E)) = intVec D n :=
  Set.ext fun x => GlobalTheory.SW.Base.mem_stdL x

theorem om_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {δ : ℂ} {sc : ℝ} (hP : StdPair θ S T δ sc ψ)
    {μ : (AE D)ˣ →* Circle} {om : Om S T} (hW : IsWeilDatumO ψ S T μ μ om)
    (hu : ∀ v ε, GlobalTheory.WeilParts.NonSplitAt D v ε → GlobalTheory.WeilParts.UnramAt ε μ) {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) f) {k : GA D S} {k' : GA D T}
    (hk : k ∈ GfC S) (hk' : k' ∈ GfC T) (a : IntG S k) (a' : IntG T k') :
    ∃ x y, IsDetRoot S k x ∧ IsDetRoot T k' y ∧ om (k, k') f = (((μ x)⁻¹ * μ y : Circle) : ℂ) • f := by
  have m := isMov_of_intG a (a.inv hP.gS)
  have m' := isMov_of_intG a' (a'.inv hP.gT)
  have sS := GlobalTheory.Ker.Base.selfDualC_stdL hP.gS
  have sT := GlobalTheory.Ker.Base.selfDualC_stdL hP.gT
  obtain ⟨x, hx, rx⟩ := GlobalTheory.LatticeUnitRoot.exists_finUnit_isDetRoot D S _ sS k hk m
  obtain ⟨y, hy, ry⟩ := GlobalTheory.LatticeUnitRoot.exists_finUnit_isDetRoot D T _ sT k' hk' m'
  have hc : ∀ V : HSp D, V.gram = 1 → ∀ τ, IsCartanInv (gramAt D V τ) 1 := fun V hV τ => by
    have : gramAt D V τ = 1 := by
      unfold gramAt
      rw [hV]
      simp
    rw [this]
    exact GlobalTheory.AdTh.isCartanInv_one_splitStab _
  refine ⟨x, y, rx, ry, GlobalTheory.FinVac.om_vacuum_finite D S T ψ θ hP.inf hP.sigS hP.sigT μ μ om hW
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) (fun v ε hv => ⟨hu v ε hv, hu v ε hv⟩) (fun _ => 1) (fun _ => 1)
    (hc S hP.gS) (hc T hP.gT) _ _ sS sT f ?_ k hk k' hk' m m' x y hx hy rx ry⟩
  rwa [coe_stdL, coe_stdL]

theorem xiN_smul (θ : InfFam D) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ) (c : ℂ)
    (f : WO S T → ℂ) : xiN θ S T hS hT δ sc (c • f) = fun z => c * xiN θ S T hS hT δ sc f z := by
  funext z
  simp only [xiN, Pi.smul_apply, smul_eq_mul]
  ring

theorem moveAt_mul_stab : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word) (A : ColDat I l Z u (w.C.herm.base.Ch u)) ψ θ, A.Is (w.C.forms u) ψ θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → A.MoveAt θ i hi c₀ g h → ∀ k ∈ GfC _, ∀ k' ∈ GfC _, Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) k (Formalism.L2.Col.stdLat B.fields.E _) → Moves _ (rankN (I.rec7 l Z) (i + 1) hi) k' (Formalism.L2.Col.stdLat B.fields.E _) → A.MoveAt θ i hi c₀ (g * k) (h * k') := by
  intro B X I l Z w u A ψ θ hA i hi c₀ g h hg hh hM k hk k' hk' mk mk' N N' hN hN' x y hx hy
  have hP := (GlobalTheory.AdForm.StdSteps.stdPair_steps I l Z w u A ψ θ hA i hi).1
  have hW := hA.om i hi
  have b := intG_of_moves _ mk
  have b' := intG_of_moves _ mk'
  have a := b.inv hP.gS
  have a' := b'.inv hP.gT
  rw [inv_inv] at a a'
  obtain ⟨x₁, y₁, rx, ry, e⟩ := om_vac hP hW
    (fun v ε hv => unramAt_of_chrEq (hA.chr ⟨i, hi⟩) (I.C.isMu0 ⟨i, hi⟩).unr hv) (hA.vac i hi) hk hk' a a'
  obtain ⟨x₀, sx⟩ := (GlobalTheory.Member.isDetRoot_laws _ _).1 g
  obtain ⟨y₀, sy⟩ := (GlobalTheory.Member.isDetRoot_laws _ _).1 h
  have e0 := hM N N' (moves_of_mul _ a b hN) (moves_of_mul _ a' b' hN') x₀ y₀ sx sy
  have ex := root_eq hW.resS hP.rk.2.2.1 ((GlobalTheory.Member.isDetRoot_laws _ _).2.2.2 _ _ _ _ sx rx) hx
  have ey := root_eq hW.resS hP.rk.2.2.1 ((GlobalTheory.Member.isDetRoot_laws _ _).2.2.2 _ _ _ _ sy ry) hy
  rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, e, map_smul, ex, ey]
  refine (xiN_smul _ _ _ _ _ _ _ _ _).trans ?_
  funext z
  have e1 := congrFun e0 z
  simp only [ColDat.xiS] at e1
  rw [e1]
  simp only [map_mul, Circle.coe_mul, Circle.coe_inv, mul_inv]
  ring

end GlobalTheory.AdForm.StabMove
