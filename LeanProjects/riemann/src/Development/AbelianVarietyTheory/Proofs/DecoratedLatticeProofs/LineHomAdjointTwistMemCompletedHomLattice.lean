import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawCombinationsOperatorDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroRightMemCoreLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.KapLat

open GlobalTheory.FinPl

variable {D : D7}

def pairH (L : HSp D) (z y : Fin L.rank → AE D) : AE D := (fun a => cA D (z a)) ⬝ᵥ (gA L *ᵥ y)

theorem incA_eq (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

theorem tmul_eq (γ : Af D.host.F) (e : D.host.E) :
    pairA D.host.F 0 γ ⊗ₜ[D.host.F] (1 * e) = (pairA D.host.F 0 γ ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D e := by
  rw [incA_eq, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem cA_tmul_one (a : AF D.host.F) : cA D (a ⊗ₜ[D.host.F] (1 : D.host.E)) = a ⊗ₜ[D.host.F] (1 : D.host.E) := by
  have := GlobalTheory.SelfDualAt.cA_alg (D := D) a
  simpa [Algebra.TensorProduct.algebraMap_apply] using this

theorem pairH_add_left (L : HSp D) (z z' y : Fin L.rank → AE D) : pairH L (z + z') y = pairH L z y + pairH L z' y := by
  simp only [pairH, dotProduct, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem pairH_neg_left (L : HSp D) (z y : Fin L.rank → AE D) : pairH L (-z) y = -pairH L z y := by
  simp only [pairH, dotProduct, Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem pairH_zero_left (L : HSp D) (y : Fin L.rank → AE D) : pairH L 0 y = 0 := by
  simp only [pairH, dotProduct, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]

theorem pairH_add_right (L : HSp D) (z y y' : Fin L.rank → AE D) : pairH L z (y + y') = pairH L z y + pairH L z y' := by
  simp only [pairH, Matrix.mulVec_add, dotProduct_add]

theorem pairH_neg_right (L : HSp D) (z y : Fin L.rank → AE D) : pairH L z (-y) = -pairH L z y := by
  simp only [pairH, Matrix.mulVec_neg, dotProduct_neg]

theorem pairH_zero_right (L : HSp D) (z : Fin L.rank → AE D) : pairH L z 0 = 0 := by
  simp only [pairH, Matrix.mulVec_zero, dotProduct_zero]

theorem pairH_gen (L : HSp D) (α β : Af D.host.F) (x x' : Fin L.rank → D.host.E) :
    pairH L (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i)) =
      pairA D.host.F 0 (α * β) ⊗ₜ[D.host.F] (1 * ∑ i, ∑ j, star (x i) * L.gram i j * x' j) := by
  have hp : pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := Prod.ext (zero_mul _) rfl
  simp only [tmul_eq, pairH, dotProduct, Matrix.mulVec, gA, rat, Matrix.map_apply, map_mul, cA_tmul_one,
    GlobalTheory.DualPairCheck.cA_incA, map_sum]
  rw [← hp, ← one_mul (1 : D.host.E), ← Algebra.TensorProduct.tmul_mul_tmul, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem pairH_int {L : HSp D} {LL : Lat L} (hL : IsSelfDualC L LL) {P : Pl D → Prop} {z y : Fin L.rank → AE D}
    (hz : z ∈ latV L LL P) (hy : y ∈ latV L LL P) : finPart D (pairH L z y) ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hαi, -, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨β, hβi, -, c', hc', x', hx', rfl⟩ := hy
      rw [Set.mem_singleton_iff] at hc'
      subst hc'
      obtain ⟨b, hb⟩ := (hL.2 x').1 hx' x hx
      rw [pairH_gen, ← hb, GlobalTheory.LatVac.finPart_tmul, one_mul]
      exact AddSubgroup.subset_closure ⟨α * β, GlobalTheory.FinPl.LatMem.intAf_mul' hαi hβi, b, rfl⟩
    | zero => rw [pairH_zero_right]; exact zero_mem _
    | add y y' _ _ h h' => rw [pairH_add_right, RingHom.map_add]; exact add_mem h h'
    | neg y _ h => rw [pairH_neg_right, RingHom.map_neg]; exact neg_mem h
  | zero => rw [pairH_zero_left]; exact zero_mem _
  | add z z' _ _ h h' => rw [pairH_add_left, RingHom.map_add]; exact add_mem h h'
  | neg z _ h => rw [pairH_neg_left, RingHom.map_neg]; exact neg_mem h

end GlobalTheory.KapLat

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.KapLat2

open GlobalTheory.FinPl GlobalTheory.KapLat

variable {D : D7}

theorem pairH_eq (S : HSp D) (t : Fin S.rank → D.host.E) (x : Fin S.rank → AE D) :
    pairH S (fun l => incA D (t l)) x = ∑ b, (∑ k, incA D (star (t k)) * gA S k b) * x b := by
  unfold pairH
  rw [Matrix.dotProduct_mulVec]
  simp only [dotProduct, Matrix.vecMul, GlobalTheory.DualPairCheck.cA_incA]

theorem smul_mulVec' {m n : ℕ} (c : AE D) (M : Mx D m n) (v : Fin n → AE D) : (c • M) *ᵥ v = c • (M *ᵥ v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc]

set_option maxHeartbeats 800000 in

theorem mem_latV_of_pairH {S : HSp D} {MS : Lat S} (hS : IsSelfDualC S MS) {P : Pl D → Prop}
    {x : Fin S.rank → AE D} (hx : ∀ b, x b ∈ idAt D P)
    (hint : ∀ t ∈ MS, finPart D (pairH S (fun a => incA D (t a)) x) ∈ intAE D) : x ∈ latV S MS P := by
  obtain ⟨m, s, s', hs, hs', hdual⟩ := GlobalTheory.FinPl.LatMem.exists_dualBasis S hS
  have hyv : ∀ i, (fun l => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F P) ⊗ₜ[D.host.F] (1 * s i l)) ∈
      latV S MS P := fun i =>
    AddSubgroup.subset_closure ⟨GlobalTheory.FinPl.LatMem.indP D.host.F P, GlobalTheory.FinPl.LatMem.indicatorAdele_mem_integralAdeles' _ _,
      GlobalTheory.FinPl.LatMem.indicatorAdele_supported _ _, 1, rfl, s i, hs i, rfl⟩
  have hdualA : ∀ a b, ∑ i, incA D (s i a) * ∑ k, incA D (star (s' i k)) * gA S k b = incA D (if a = b then 1 else 0) := by
    intro a b
    rw [← hdual a b, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, map_sum, gA, rat, Matrix.map_apply]
  have h2 : ∀ a, ∑ i, incA D (s i a) * ∑ b, (∑ k, incA D (star (s' i k)) * gA S k b) * x b = x a := by
    intro a
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h3 : ∀ b, ∑ i, incA D (s i a) * ((∑ k, incA D (star (s' i k)) * gA S k b) * x b) =
        incA D (if a = b then 1 else 0) * x b := by
      intro b
      rw [← hdualA a b, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    simp only [h3]
    rw [Finset.sum_eq_single a]
    · rw [if_pos rfl, map_one, one_mul]
    · intro b _ hb
      rw [if_neg (Ne.symm hb), map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  have key : x = ∑ i, fun a => pairH S (fun l => incA D (s' i l)) x *
      pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F P) ⊗ₜ[D.host.F] (1 * s i a) := by
    funext a
    rw [Finset.sum_apply]
    have h1 : ∀ i, pairH S (fun l => incA D (s' i l)) x *
        pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F P) ⊗ₜ[D.host.F] (1 * s i a) =
        (incA D (s i a) * ∑ b, (∑ k, incA D (star (s' i k)) * gA S k b) * x b) *
          (pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F P) ⊗ₜ[D.host.F] (1 : D.host.E)) := by
      intro i
      rw [tmul_eq, pairH_eq]
      ring
    simp only [h1]
    rw [← Finset.sum_mul, h2 a]
    exact (GlobalTheory.FinPl.LatMem.mul_indP (hx a)).symm
  rw [key]
  exact sum_mem fun i _ => GlobalTheory.FinPl.LatIndHalf.mul_mem_latV (hint _ (hs' i)) (hyv i)

theorem pairH_kap (S L L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (w : WO S L'')
    (t : Fin S.rank → D.host.E) (y : Fin L.rank → AE D) :
    pairH S (fun a => incA D (t a)) (GlobalTheory.FinPl.kap τ S w *ᵥ y) =
      incA D (-D.host.xi0⁻¹) * pairH L ((rat τ : Mx D L.rank L''.rank) *ᵥ (w *ᵥ fun a => incA D (t a))) y := by
  unfold pairH GlobalTheory.FinPl.kap GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  rw [Matrix.mulVec_mulVec, Matrix.mul_smul, gA_giA_cancel, smul_mulVec', dotProduct_smul, smul_eq_mul]
  congr 1
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  congr 1
  funext a
  rw [Matrix.mulVec_mulVec, RingHom.map_mulVec, adj, Matrix.vecMul_transpose]
  rfl

end GlobalTheory.KapLat2

namespace GlobalTheory.KapLat2

open GlobalTheory.FinPl GlobalTheory.KapLat

set_option maxHeartbeats 800000 in

theorem kap_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S L L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (MS : GlobalTheory.FinPl.Lat S) (LL : GlobalTheory.FinPl.Lat L) (LZ : GlobalTheory.FinPl.Lat L''), q.UnitAA → IsSelfDualC S MS → IsSelfDualC L LL → IsSelfDualC L'' LZ → (∀ y ∈ GlobalTheory.FinPl.latV L'' LZ (· = q.v), (rat τ : Mx D L.rank L''.rank) *ᵥ y ∈ GlobalTheory.FinPl.latV L LL (· = q.v)) → ∀ w ∈ latO S L'' (MS : Set _) (LZ : Set _) (· = q.v), GlobalTheory.FinPl.kap τ S w ∈ latO L S (LL : Set _) (MS : Set _) (· = q.v) := by
  intro D k _ _ _ _ q S L L'' τ MS LL LZ hU hS hL hZ hτ w hw
  have hwP : MxAt (· = q.v) w := GlobalTheory.FinPl.LatMem.latO_mxAt hw
  have huP : MxAt (· = q.v) (GlobalTheory.FinPl.kap τ S w) := GlobalTheory.LastOpPf.mxAt_kap τ S hwP
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D L S LL MS hL hS]
  refine ⟨huP, fun y hy => ?_⟩
  rw [hU.2 S MS]
  have hyP : ∀ b, y b ∈ idAt D (· = q.v) := GlobalTheory.ContrComb.LatT.latV_entry_mem hy
  refine mem_latV_of_pairH hS (fun b => ?_) (fun t ht => ?_)
  · show (GlobalTheory.FinPl.kap τ S w *ᵥ y) b ∈ _
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (huP b j)
  · show finPart D (pairH S (fun a => incA D (t a)) (GlobalTheory.FinPl.kap τ S w *ᵥ y)) ∈ intAE D
    rw [pairH_kap]

    let yv : Fin S.rank → AE D := fun l =>
      pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = q.v)) ⊗ₜ[D.host.F] (1 * t l)
    have hyv : yv ∈ latV S MS (· = q.v) :=
      AddSubgroup.subset_closure ⟨GlobalTheory.FinPl.LatMem.indP D.host.F (· = q.v), GlobalTheory.FinPl.LatMem.indicatorAdele_mem_integralAdeles' _ _,
        GlobalTheory.FinPl.LatMem.indicatorAdele_supported _ _, 1, rfl, t, ht, rfl⟩
    have hwt : (w *ᵥ fun a => incA D (t a)) = w *ᵥ yv := by
      funext j
      simp only [Matrix.mulVec, dotProduct, yv, tmul_eq]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← mul_assoc, GlobalTheory.FinPl.LatMem.mul_indP (hwP j l)]
    have hz : (rat τ : Mx D L.rank L''.rank) *ᵥ (w *ᵥ fun a => incA D (t a)) ∈ latV L LL (· = q.v) := by
      rw [hwt]
      refine hτ _ ?_
      rw [← hU.2 L'' LZ]
      exact GlobalTheory.FinPl.LatMem.latO_maps hS hw hyv
    have hint := pairH_int hL hz hy
    have hid : pairH L ((rat τ : Mx D L.rank L''.rank) *ᵥ (w *ᵥ fun a => incA D (t a))) y ∈ idAt D (· = q.v) := by
      simp only [pairH, Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ (hyP b))
    have h3 := (hU.1 _ ⟨hid, hint⟩).2.2
    rw [map_neg, neg_mul, map_neg]
    exact neg_mem h3

end GlobalTheory.KapLat2
