import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMapsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAAScaledEqAtUnitSplitPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineMultipleMemSplitCoreLatticeCompletionIffStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineProjectionMemSplitCoreCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesSelfDualOfSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaAdjointTauFactorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MxAtEmbedKappa
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Corev.KappaLeft

theorem latV_mem_idAt {D : D7} {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) : ∀ r, y r ∈ idAt D P := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at hy
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, hα, a, -, s, -, rfl⟩ := hw
    intro r
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt hα _
  | zero => intro r; exact zero_mem _
  | add x y _ _ hx hy => intro r; exact add_mem (hx r) (hy r)
  | neg x _ hx => intro r; exact neg_mem (hx r)

end GlobalTheory.Corev.KappaLeft

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.Corev.kappa_mem_latO_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' : Type) [Fintype n'] [DecidableEq n'] (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (Λ : ι → Submodule 𝒪[k] (n' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ x : WO S B'.L, MxAt P x → ((B.o.resS S).symm (0, l.κ S x) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P ↔ ∀ y ∈ latV S LS P, ∃ d : AE D, d ∈ idAt D P ∧ (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ ∀ c : AE D, c ∈ idAt D P → (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ)) ∈ 𝒪[k]) → incA D (D.host.xi0⁻¹) * cA D d * c * incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) ∈ intAt D P) := by
  intro D k _ _ _ _ ι p I P hP n' _ _ ρ σ B B' l S α α₀ M LS Λ hM hLS hα x hx
  have hcA : ∀ e : D.host.E, cA D (incA D e) = incA D (star e) := fun e => rfl
  have hMx : MxAt P ((B.o.resS S).symm (0, l.κ S x)) :=
    (GlobalTheory.KapLatSupp.mxAt_embed_kappa D ρ B B'.L B'.ζ l S B'.V₀ B'.A B'.o P x hx).1
  have hu : (B.o.resS S).symm (0, l.κ S x) = l.κ S x ⬝ B.o.pB := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]

  have hline : ∀ (L : HSp D) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ v : Fin L.rank → AE D,
      (∀ r, v r ∈ idAt D P) → ∃ c : AE D, c ∈ idAt D P ∧ v = c • ratV ζ := by
    intro L ζ hL v hv
    obtain ⟨hrk, hne⟩ := hL
    have hr : ∀ r r' : Fin L.rank, r = r' := fun r r' => Fin.ext (by omega)
    let r₀ : Fin L.rank := ⟨0, by omega⟩
    have hζ : ζ r₀ ≠ 0 := by
      intro h0
      apply hne
      have : ζ = 0 := funext fun r => by rw [hr r r₀, h0]; rfl
      rw [this, Matrix.mulVec_zero, dotProduct_zero]
    refine ⟨v r₀ * incA D (ζ r₀)⁻¹, Ideal.mul_mem_right _ _ (hv r₀), ?_⟩
    funext r
    rw [hr r r₀, Pi.smul_apply, smul_eq_mul, ratV, mul_assoc, ← map_mul, inv_mul_cancel₀ hζ, map_one, mul_one]
  have hjB : ∀ c : AE D, B.o.jB *ᵥ (c • ratV B.ζ) = fun r => c * incA D (vecB B.o B.ζ r) := by
    intro c
    funext r
    simp only [Matrix.mulVec, dotProduct, OrthDec.jB, rat, Matrix.map_apply, ratV, Pi.smul_apply, smul_eq_mul, vecB,
      map_sum, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hpj : ∀ c : AE D, B.o.pB *ᵥ (B.o.jB *ᵥ (c • ratV B.ζ)) = c • ratV B.ζ := by
    intro c
    rw [Matrix.mulVec_mulVec, OrthDec.pB_jB, Matrix.one_mulVec]

  have hsupp : ∀ m : Fin B.V₀.rank → AE D, ∀ r, (((B.o.resS S).symm (0, l.κ S x) : Matrix _ _ (AE D)) *ᵥ m) r ∈ idAt D P := by
    intro m r
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hMx r j)

  have hpair : ∀ (y : Fin S.rank → AE D) (d c : AE D), (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ →
      (∑ i, ∑ j, cA D (y i) * incA D (HSpace.gram S i j) * ((l.κ S x : Matrix _ _ (AE D)) *ᵥ (c • ratV B.ζ)) j) =
        incA D (D.host.xi0⁻¹) * cA D d * c * incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) := by
    intro y d c hxy
    rw [GlobalTheory.T.besselLinkKappa_adjoint_tau_factor D ρ B B'.L B'.ζ l S x (c • ratV B.ζ) y]
    have h1 : ((rat l.τ : Matrix _ _ (AE D)) * (x : Matrix _ _ (AE D))) *ᵥ y = d • ratV (-B.ζ) := by
      rw [← Matrix.mulVec_mulVec, hxy, Matrix.mulVec_smul, ← l.map]
      congr 1
      funext i
      simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, ratV, map_sum, map_mul]
    rw [h1]
    have hh : incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) =
        ∑ i, ∑ j, incA D (star (B.ζ i)) * incA D (HSpace.gram B.L i j) * incA D (B.ζ j) := by
      simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, Finset.mul_sum, mul_assoc]
    rw [hh, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, ratV, Pi.neg_apply, map_mul, map_neg, hcA, star_neg]
    ring
  rw [GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D B.V₀ S M LS hM hLS P, GlobalTheory.T.latticeCompletionAAScaled_eq_at_unitSplitPlaces D k ι p I P hP S LS]
  constructor
  · rintro ⟨-, h⟩ y hy
    have hz : ∀ r, ((x : Matrix _ _ (AE D)) *ᵥ y) r ∈ idAt D P := by
      intro r
      simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hx r j)
    obtain ⟨d, hdI, hxd⟩ := hline B'.L B'.ζ B'.line _ hz
    refine ⟨d, hdI, hxd, fun c hc hl => ?_⟩
    have hm : (fun r => c * incA D (vecB B.o B.ζ r)) ∈ latV B.V₀ M P :=
      (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n' B.V₀ B.A B.L B.o B.ζ B.line α α₀ M Λ hM hα c hc).2 hl
    have h1 := h _ hm
    have hI := hsupp (fun r => c * incA D (vecB B.o B.ζ r))
    have heq : ((B.o.resS S).symm (0, l.κ S x) : Matrix _ _ (AE D)) *ᵥ (fun r => c * incA D (vecB B.o B.ζ r)) =
        (l.κ S x : Matrix _ _ (AE D)) *ᵥ (c • ratV B.ζ) := by
      rw [hu, ← hjB, ← Matrix.mulVec_mulVec, hpj]
    rw [heq] at h1 hI
    have h2 := (GlobalTheory.T.latticeCompletionAtPlaces_selfDual_of_selfDual D S LS hLS P _ hI).1 h1 y hy
    rwa [hpair y d c hxd] at h2
  · intro h
    refine ⟨hMx, fun m hm => ?_⟩
    have hv : ∀ r, (B.o.pB *ᵥ m) r ∈ idAt D P := by
      intro r
      simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (GlobalTheory.Corev.KappaLeft.latV_mem_idAt hm j)
    obtain ⟨c, hc, hcv⟩ := hline B.L B.ζ B.line _ hv
    have hjp := GlobalTheory.T.lineProjection_mem_splitCoreCompletion D k ι p I P hP n' B.V₀ B.A B.L B.o B.ζ B.line α α₀ M Λ hM hα m hm
    rw [hcv, hjB] at hjp
    have hl := (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n' B.V₀ B.A B.L B.o B.ζ B.line α α₀ M Λ hM hα c hc).1 hjp
    have hI := hsupp m
    have heq : ((B.o.resS S).symm (0, l.κ S x) : Matrix _ _ (AE D)) *ᵥ m = (l.κ S x : Matrix _ _ (AE D)) *ᵥ (c • ratV B.ζ) := by
      rw [hu, ← Matrix.mulVec_mulVec, hcv]
    rw [heq] at hI ⊢
    refine (GlobalTheory.T.latticeCompletionAtPlaces_selfDual_of_selfDual D S LS hLS P _ hI).2 fun s hs => ?_
    obtain ⟨d, -, hxd, hd⟩ := h s hs
    rw [hpair s d c hxd]
    exact hd c hc hl
