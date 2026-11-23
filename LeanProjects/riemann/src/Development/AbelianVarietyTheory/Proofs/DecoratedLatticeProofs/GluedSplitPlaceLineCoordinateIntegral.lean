import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
open GlobalTheory.RootEx (embX)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.GluedInt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mt_sec' (p : SplitPt D k) {S : HSp D} (h : GA D S) (u : Fin S.rank → k) :
    mt S h *ᵥ (fun i => p.sec (u i)) = fun i => p.sec (((mt S h).map p.pr *ᵥ u) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [FrameLat.sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, FrameLat.e_mul_sec]

theorem cAe_smul (p : SplitPt D k) {r : ℕ} (z : Fin r → AE D) :
    cA D p.e • z = fun i => cA D (p.sec (p.pr (cA D (z i)))) := by
  funext i
  rw [Pi.smul_apply, smul_eq_mul, p.sec_pr, map_mul, cA_cA]

def form (p : SplitPt D k) (S : HSp D) (x w : Fin S.rank → k) : k :=
  ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * w j

theorem form_eq (p : SplitPt D k) (S : HSp D) (x : Fin S.rank → k) (c : Fin S.rank → D.host.E) :
    form p S x (fun j => p.pr (cA D (incA D (c j)))) =
      x ⬝ᵥ fun i => p.pr (incA D ((star (S.gram *ᵥ c)) i)) := by
  unfold form
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  simp only [Pi.star_apply, Matrix.mulVec, dotProduct, star_sum, map_sum, star_mul', map_mul]
  rfl

theorem row_orth {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) :
    star (S.gram *ᵥ vecB o ζ) ᵥ* o.iA = 0 ∧ star (S.gram *ᵥ vecB o ζ) ⬝ᵥ vecB o ζ = star ζ ⬝ᵥ L.gram *ᵥ ζ := by
  have hr : star (S.gram *ᵥ vecB o ζ) = star ζ ᵥ* (o.iBᴴ * S.gram) := by
    rw [vecB, Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_mul, gram_conjTranspose]
  rw [hr]
  constructor
  · rw [Matrix.vecMul_vecMul, o.orth, Matrix.vecMul_zero]
  · rw [vecB, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, o.isoB]

theorem form_frame (p : SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) {n : Type} [Fintype n] [DecidableEq n]
    (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (hs : IsSumFrame B.o B.ζ β β₀) (y : n ⊕ Fin 1 → k) :
    form p B.V₀ (β₀.b *ᵥ y) (fun j => p.pr (cA D (ratV (vecB B.o B.ζ) j))) =
      p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) * y (Sum.inr 0) := by
  obtain ⟨h1, h2⟩ := row_orth B.o B.ζ
  set ι : D.host.E →+* k := p.pr.comp (incA D) with hι
  set r := star (B.V₀.gram *ᵥ vecB B.o B.ζ) with hr
  change form p B.V₀ _ (fun j => p.pr (cA D (incA D (vecB B.o B.ζ j)))) = _
  rw [form_eq, ← hr, hs, Matrix.fromCols_mulVec, add_dotProduct]
  have hA : (⇑ι ∘ r) ᵥ* (B.o.jA.map p.pr) = 0 := by
    funext a
    have hm : B.o.jA.map p.pr = B.o.iA.map ι := by
      rw [OrthDec.jA, rat, Matrix.map_map]; rfl
    rw [hm, ← RingHom.map_vecMul, h1]
    simp
  have e1 : ((B.o.jA.map p.pr * β.b) *ᵥ (y ∘ Sum.inl)) ⬝ᵥ (fun i => p.pr (incA D (r i))) = 0 := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul]
    change ((⇑ι ∘ r) ᵥ* (B.o.jA.map p.pr) ᵥ* β.b) ⬝ᵥ _ = 0
    rw [hA, Matrix.zero_vecMul, zero_dotProduct]
  have e2 : (replicateCol (Fin 1) (fun i => p.pr (ratV (vecB B.o B.ζ) i)) *ᵥ (y ∘ Sum.inr)) =
      y (Sum.inr 0) • (⇑ι ∘ vecB B.o B.ζ) := by
    funext i
    simp [Matrix.mulVec, dotProduct, replicateCol, mul_comm, ratV, hι]
  rw [e1, zero_add, e2, smul_dotProduct, smul_eq_mul, mul_comm]
  congr 1
  change (⇑ι ∘ vecB B.o B.ζ) ⬝ᵥ (⇑ι ∘ r) = ι _
  rw [← RingHom.map_dotProduct, dotProduct_comm, h2]

end GlobalTheory.FinPl.GluedInt

open GlobalTheory.FinPl.GluedInt in

theorem GlobalTheory.FinPl.glued_last_integral : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ) (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (P : Pair k n), IsSelfDualC B.V₀ L₀ → GluedCore B L₀ q β β₀ P → ∀ γ ∈ grpAt B.V₀ (· = p.v), (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) → mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) → ∀ x : n ⊕ Fin 1 → k, mt B.V₀ γ⁻¹ *ᵥ (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV B.V₀ L₀ (· = p.v) → (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k] := by
  intro D k _ _ _ _ p n _ _ q σ B L₀ β β₀ P hsd hg γ _ hyp x hx
  have hu := hg.unit.2 B.V₀ L₀
  have hz := cAe_smul p (ratV (vecB B.o B.ζ))
  set zk : Fin B.V₀.rank → k := fun j => p.pr (cA D (ratV (vecB B.o B.ζ) j)) with hzk
  have hN : ∀ y : n ⊕ Fin 1 → k, form p B.V₀ (β₀.b *ᵥ y) zk =
      p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) * y (Sum.inr 0) := form_frame p B β β₀ hg.sum
  have hvN := hg.norm
  set N := p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) with hNdef
  have hq0 : valuation k ((q.1 : 𝒪[k]) : k) ≠ 0 := by
    rw [Ne, map_eq_zero]; exact q.ne_zero
  have hmem : (fun i => cA D (p.sec (zk i))) ∈ latV B.V₀ L₀ (· = p.v) := by
    rw [FrameLat.csec_mem_iff hsd]
    intro x' hx'
    have hb : β₀.b *ᵥ (β₀.b' *ᵥ x') = x' := by rw [Matrix.mulVec_mulVec, β₀.bb', Matrix.one_mulVec]
    have hy : β₀.b' *ᵥ x' ∈ gluedS q 1 P.ker P.vec := (hg.lat _).2 (by rw [hb]; exact hx')
    rw [← gluedLat_one, mem_gluedLat] at hy
    obtain ⟨s, -, hs⟩ := hy
    have h0 := (hs 0).2.1 rfl
    change form p B.V₀ x' zk ∈ 𝒪[k]
    rw [← hb, hN, h0, Valuation.mem_integer_iff, map_mul, map_mul, hvN, Unif.inv, map_inv₀, ← mul_assoc,
      mul_inv_cancel₀ hq0, one_mul]
    exact s.2
  have hA : cA D p.e • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) := by rw [hu, hz]; exact hmem
  have h1 := hyp (cA D p.e) hA
  rw [hu, hz, FrameLat.mt_csec] at h1
  rw [mt_sec' p] at hx
  have h2 := (FrameLat.csec_mem_iff hsd _).1 h1 _ hx
  rw [FrameLat.pairing_inv] at h2
  change form p B.V₀ (β₀.b *ᵥ x) zk ∈ 𝒪[k] at h2
  rw [hN, Valuation.mem_integer_iff, map_mul, hvN] at h2
  rw [Valuation.mem_integer_iff, map_mul]
  exact h2
