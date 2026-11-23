import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LineProj

open GlobalTheory.IwaPlace

variable {D : D7}

theorem hermAt_eq (S : HSp D) (x y : Fin S.rank → AE D) :
    hermAt S x y = (fun i => cA D (y i)) ⬝ᵥ (gA S *ᵥ x) := by
  simp only [hermAt, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hermAt_mulVec (S : HSp D) {π : Mx D S.rank S.rank} (h : adj π ⬝ gA S = gA S ⬝ π) (x y : Fin S.rank → AE D) :
    hermAt S (π *ᵥ x) y = hermAt S x (π *ᵥ y) := by
  have e : (fun i => cA D ((π *ᵥ y) i)) = (fun i => cA D (y i)) ᵥ* adj π := by
    funext i
    rw [adj, Matrix.vecMul_transpose]
    exact RingHom.map_mulVec (cA D) π y i
  have e2 : gA S *ᵥ (π *ᵥ x) = adj π *ᵥ (gA S *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ x) h.symm
  rw [hermAt_eq, hermAt_eq, e, e2]
  exact Matrix.dotProduct_mulVec _ _ _

theorem hermAt_smul (S : HSp D) (a : AE D) (x y : Fin S.rank → AE D) :
    hermAt S (a • x) y = hermAt S x (cA D a • y) := by
  simp only [hermAt, Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.DualPairCheck.cA_cA]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hermAt_add_left (S : HSp D) (x x' y : Fin S.rank → AE D) :
    hermAt S (x + x') y = hermAt S x y + hermAt S x' y := by
  simp only [hermAt, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem add_mem_intAt {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add]; exact add_mem ha.2 hb.2⟩

theorem proj_selfAdj {S A L : HSp D} (o : OrthDec S A L) :
    adj (o.jB ⬝ o.pB) ⬝ gA S = gA S ⬝ (o.jB ⬝ o.pB) := by
  rw [o.pB_eq]
  simp only [adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mulVec_mem_of_half (p : SplitPt D k) {S : HSp D} {M : Lat S} (hM : IsSelfDualC S M) {π : Mx D S.rank S.rank}
    (h : adj π ⬝ gA S = gA S ⬝ π)
    (hw : ∀ z ∈ latV S M (· = p.v), π *ᵥ (p.e • z) ∈ latV S M (· = p.v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S M (· = p.v)) : π *ᵥ y ∈ latV S M (· = p.v) := by
  obtain ⟨hs, -, hd⟩ := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S M p.v hM
  refine (hd _ (mulVec_mem_idAt π (hs y hy))).2 fun x hx => ?_
  have hy' : y = p.e • y + cA D p.e • y := by
    funext i
    rw [← add_smul, Pi.smul_apply, smul_eq_mul]
    exact ((FrameLat.idem_iff p (y i)).1 (hs y hy i)).symm
  rw [hy', Matrix.mulVec_add, hermAt_add_left]
  refine add_mem_intAt ((hd _ (hs _ (hw y hy))).1 (hw y hy) x hx) ?_
  rw [hermAt_mulVec S h, hermAt_smul, GlobalTheory.DualPairCheck.cA_cA, ← Matrix.mulVec_smul]
  exact (hd y (hs y hy)).1 hy _ (hw x hx)

theorem proj_frame {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {S A L : HSp D} (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) {α : Frame p A n} {α₀ : Frame p S (n ⊕ Fin 1)} (h : IsSumFrame o ζ α α₀)
    (x : n ⊕ Fin 1 → k) :
    (o.jB ⬝ o.pB).map p.pr *ᵥ (α₀.b *ᵥ x) = α₀.b *ᵥ Sum.elim 0 (x ∘ Sum.inr) := by
  have h1 : (o.jB ⬝ o.pB).map p.pr * o.jA.map p.pr = 0 := by
    rw [← Matrix.map_mul, Matrix.mul_assoc, o.pB_jA, Matrix.mul_zero]
    exact Matrix.map_zero _ (map_zero _)
  have h2 : (o.jB ⬝ o.pB) *ᵥ ratV (vecB o ζ) = ratV (vecB o ζ) := by
    have e : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
      funext i
      exact RingHom.map_mulVec (incA D) o.iB ζ i
    rw [e, Matrix.mulVec_mulVec, Matrix.mul_assoc, o.pB_jB, Matrix.mul_one]
  have h3 : (o.jB ⬝ o.pB).map p.pr *ᵥ (fun i => p.pr (ratV (vecB o ζ) i)) = fun i => p.pr (ratV (vecB o ζ) i) := by
    funext i
    have := RingHom.map_mulVec p.pr (o.jB ⬝ o.pB) (ratV (vecB o ζ)) i
    rw [h2] at this
    exact this.symm
  rw [IsSumFrame] at h
  rw [h, Matrix.mulVec_mulVec, Matrix.mul_fromCols, ← Matrix.mul_assoc, h1, Matrix.zero_mul,
    ← Matrix.replicateCol_mulVec, h3, Matrix.fromCols_mulVec, Matrix.fromCols_mulVec_sumElim, Matrix.zero_mulVec,
    Matrix.mulVec_zero]

theorem proj_half {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {S A L : HSp D} (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) {α : Frame p A n} {α₀ : Frame p S (n ⊕ Fin 1)} (h : IsSumFrame o ζ α α₀)
    {M : Lat S} {Λ : Submodule 𝒪[k] (n → k)} (hΛ : α₀.IsLat M (lastKer Λ)) {z : Fin S.rank → AE D}
    (hz : z ∈ latV S M (· = p.v)) : (o.jB ⬝ o.pB) *ᵥ (p.e • z) ∈ latV S M (· = p.v) := by
  have hb : α₀.b *ᵥ (α₀.b' *ᵥ fun i => p.pr (z i)) = fun i => p.pr (z i) := by
    rw [Matrix.mulVec_mulVec, α₀.bb', Matrix.one_mulVec]
  have h1 : (α₀.b' *ᵥ fun i => p.pr (z i)) ∈ lastKer Λ := by
    refine (hΛ _).2 ?_
    rw [hb]
    simp only [p.sec_pr]
    exact GlobalTheory.FinPlLoc.smul_latV p.v (FrameLat.e_mem_intAt p) hz
  have h2 : (Sum.elim 0 ((α₀.b' *ᵥ fun i => p.pr (z i)) ∘ Sum.inr) : n ⊕ Fin 1 → k) ∈ lastKer Λ :=
    GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨Λ.zero_mem, (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 h1).2⟩
  have h3 := (hΛ _).1 h2
  rw [← proj_frame o ζ h, hb] at h3
  convert h3 using 1
  funext i
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← p.sec_pr, RingHom.map_mulVec]
  rfl

theorem lineProj_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' : Type) [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (Λ : ι → Submodule 𝒪[k] (n' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ x ∈ latO B.V₀ S (M : Set _) (LS : Set _) P, (B.o.resS S).symm (0, (B.o.resS S x).2) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P := by
  intro D k _ _ _ _ ι p I P hP n' _ _ ρ B S α α₀ M LS Λ hM hLS h x hx
  have hπ : ∀ y ∈ latV B.V₀ M P, (B.o.jB ⬝ B.o.pB) *ᵥ y ∈ latV B.V₀ M P := by
    intro y hy
    refine (GlobalTheory.FinPlLoc.part_lat P B.V₀ M _ hM.1).2 ⟨mulVec_mem_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hy), fun v hv e he => ?_⟩
    obtain ⟨i, rfl⟩ := (hP.mem v).1 hv
    rw [← Matrix.mulVec_smul]
    exact mulVec_mem_of_half (p i) hM (proj_selfAdj B.o) (fun z hz => proj_half B.o B.ζ (h i).1 (h i).2 hz)
      (GlobalTheory.FinPlLoc.smul_latV _ he hy)
  obtain ⟨hx1, hx2⟩ := (GlobalTheory.FinPl.LatMem.mem_latO_iff D B.V₀ S M LS hM hLS P x).1 hx
  have e : (B.o.resS S).symm (0, (B.o.resS S x).2) = x ⬝ (B.o.jB ⬝ B.o.pB) := by
    rw [OrthDec.resS_symm_apply, OrthDec.resS_apply, Matrix.zero_mul, zero_add, Matrix.mul_assoc]
  rw [e]
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D B.V₀ S M LS hM hLS P _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx1 i l)
  · have := hx2 _ (hπ y hy)
    rwa [Matrix.mulVec_mulVec] at this

end GlobalTheory.LineProj
