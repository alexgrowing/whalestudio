import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

section AlgExPf

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem keepQ {Q : Submodule ℂ H} {Γ : Type} {op : Γ → (H →L[ℂ] H)} {v : Γ → ℂ}
    (hQ : ∀ x, ∀ f ∈ Q, op x f ∈ Q ∧ star (op x) f ∈ Q) {y : (H →L[ℂ] H) × ℂ}
    (hy : y ∈ StarAlgebra.adjoin ℂ (Set.range fun x => (op x, v x))) :
    (∀ f ∈ Q, y.1 f ∈ Q) ∧ ∀ f ∈ Q, (star y.1) f ∈ Q := by
  induction hy using StarAlgebra.adjoin_induction with
  | mem x h =>
    obtain ⟨a, rfl⟩ := h
    exact ⟨fun f hf => (hQ a f hf).1, fun f hf => (hQ a f hf).2⟩
  | algebraMap r =>
    have h1 : (algebraMap ℂ ((H →L[ℂ] H) × ℂ) r).1 = r • (1 : H →L[ℂ] H) := by
      rw [Prod.algebraMap_apply, Algebra.algebraMap_eq_smul_one]
    rw [h1]
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · simpa using Q.smul_mem r hf
    · simpa [star_smul] using Q.smul_mem (star r) hf
  | add x y _ _ hx hy =>
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · exact Q.add_mem (hx.1 f hf) (hy.1 f hf)
    · rw [Prod.fst_add, star_add]
      exact Q.add_mem (hx.2 f hf) (hy.2 f hf)
  | mul x y _ _ hx hy =>
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · exact hx.1 _ (hy.1 f hf)
    · rw [Prod.fst_mul, star_mul]
      exact hy.2 _ (hx.2 f hf)
  | star x _ hx =>
    refine ⟨fun f hf => hx.2 f hf, fun f hf => ?_⟩
    have : (star (star x).1) = x.1 := by rw [Prod.fst_star, star_star]
    rw [this]
    exact hx.1 f hf

end AlgExPf

end UpperTheory.Zero.ConvolutionTheory.EB

theorem UpperTheory.Zero.ConvolutionTheory.EB.algEx :
    UpperTheory.Zero.ConvolutionTheory.EB.AlgEx := by
  intro H _ _ _ Q _ Γ op v hc hs hQ
  let s : Set ((H →L[ℂ] H) × ℂ) := Set.range fun x => (op x, v x)
  have hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact Prod.ext (hc x y).eq (mul_comm _ _)
  have hcs : ∀ a ∈ s, ∀ b ∈ s, a * star b = star b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact Prod.ext (hs x y).eq (mul_comm _ _)
  letI : CommRing (StarAlgebra.adjoin ℂ s) := StarAlgebra.adjoinCommRingOfComm ℂ hcomm hcs
  have keep : ∀ y : StarAlgebra.adjoin ℂ s, (∀ f ∈ Q, y.1.1 f ∈ Q) ∧ ∀ f ∈ Q, (star y.1.1) f ∈ Q :=
    fun y => UpperTheory.Zero.ConvolutionTheory.EB.keepQ hQ y.2
  let res : StarAlgebra.adjoin ℂ s → (Q →L[ℂ] Q) := fun y =>
    (y.1.1 ∘L Q.subtypeL).codRestrict Q fun q => (keep y).1 q q.2
  let R : StarAlgebra.adjoin ℂ s →⋆ₐ[ℂ] (Q →L[ℂ] Q) :=
    { toFun := res
      map_one' := by ext q; rfl
      map_mul' := fun a b => by ext q; rfl
      map_zero' := by ext q; rfl
      map_add' := fun a b => by ext q; rfl
      commutes' := fun r => by
        ext q
        have h1 : ((algebraMap ℂ (StarAlgebra.adjoin ℂ s) r).1).1 = r • (1 : H →L[ℂ] H) := by
          show (algebraMap ℂ ((H →L[ℂ] H) × ℂ) r).1 = _
          rw [Prod.algebraMap_apply, Algebra.algebraMap_eq_smul_one]
        have h2 : algebraMap ℂ (Q →L[ℂ] Q) r = r • (1 : Q →L[ℂ] Q) :=
          Algebra.algebraMap_eq_smul_one r
        show ((algebraMap ℂ (StarAlgebra.adjoin ℂ s) r).1).1 (q : H) = _
        rw [h1, h2]
        simp
      map_star' := fun y => by
        show res (star y) = star (res y)
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
        intro p q
        show inner ℂ (star y.1.1 (p : H)) (q : H) = inner ℂ (p : H) (y.1.1 (q : H))
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left] }
  let ι : Γ → StarAlgebra.adjoin ℂ s := fun x => ⟨(op x, v x), StarAlgebra.subset_adjoin ℂ s ⟨x, rfl⟩⟩
  have all : ∀ y : StarAlgebra.adjoin ℂ s, y ∈ StarAlgebra.adjoin ℂ (Set.range ι) := by
    intro y
    induction y using StarAlgebra.adjoin_induction_subtype with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact StarAlgebra.subset_adjoin ℂ _ ⟨a, rfl⟩
    | algebraMap r => exact algebraMap_mem _ r
    | add x y hx hy => exact add_mem hx hy
    | mul x y hx hy => exact mul_mem hx hy
    | star x hx => exact star_mem hx
  have top : StarAlgebra.adjoin ℂ (Set.range ι) = ⊤ := eq_top_iff.2 fun y _ => all y
  exact ⟨{ B := StarAlgebra.adjoin ℂ s
           R := R
           P := (StarAlgHom.snd ℂ (H →L[ℂ] H) ℂ).comp (StarSubalgebra.subtype _)
           F := (StarAlgHom.fst ℂ (H →L[ℂ] H) ℂ).comp (StarSubalgebra.subtype _)
           ι := ι
           hF := fun _ => rfl
           hP := fun _ => rfl
           hR := fun _ _ => rfl
           top := top }⟩
