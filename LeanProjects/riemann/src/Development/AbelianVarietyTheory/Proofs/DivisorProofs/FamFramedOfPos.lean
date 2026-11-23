import Mathlib
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement

namespace GlobalTheory.FamilyFrames

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

theorem posDef_sum_dep {ι γ : Type} {κ : γ → Type} [Fintype ι] [Fintype γ] [∀ c, Fintype (κ c)]
    (G : ∀ c, Matrix (κ c) (κ c) ℂ) (hG : ∀ c, (G c).PosDef) (P : ∀ c, Matrix (κ c) ι ℂ)
    (hinj : ∀ x, (∀ c, P c *ᵥ x = 0) → x = 0) : (∑ c, (P c)ᴴ * G c * P c).PosDef := by
  have hs : ∀ c, ((P c)ᴴ * G c * P c).PosSemidef := fun c =>
    (hG c).posSemidef.conjTranspose_mul_mul_same (P c)
  have hS := Matrix.posSemidef_sum (s := Finset.univ) (fun c _ => hs c)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hS.1 fun x hx => ?_
  rw [Matrix.sum_mulVec, dotProduct_sum]
  obtain ⟨c, hc⟩ : ∃ c, P c *ᵥ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (hinj x hcon)
  refine Finset.sum_pos' (fun c _ => (hs c).dotProduct_mulVec_nonneg x) ⟨c, Finset.mem_univ c, ?_⟩
  have h1 := (hG c).dotProduct_mulVec_pos hc
  have h2 : star x ⬝ᵥ (((P c)ᴴ * G c * P c) *ᵥ x) = star (P c *ᵥ x) ⬝ᵥ (G c *ᵥ (P c *ᵥ x)) := by
    simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [h2]
  exact h1

section Generic

open Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem isSesq_pi {γ : Type} [Fintype γ] {V : γ → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module K (V c)]
    (H : ∀ c, InfinitePlace K → V c → V c → ℂ) (hH : ∀ c, IsSesq (H c)) :
    IsSesq (fun v (x y : ∀ c, V c) => ∑ c, H c v (x c) (y c)) := by
  intro v
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩
  · simp only [Pi.add_apply, fun c => (hH c v).1, Finset.sum_add_distrib]
  · simp only [Pi.add_apply, fun c => (hH c v).2.1, Finset.sum_add_distrib]
  · simp only [Pi.smul_apply, fun c => (hH c v).2.2.1, Finset.mul_sum]
  · simp only [Pi.smul_apply, fun c => (hH c v).2.2.2, Finset.mul_sum]

theorem posAt_pi {γ : Type} [Fintype γ] [DecidableEq γ] {V : γ → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module K (V c)]
    {κ : γ → Type} [∀ c, Fintype (κ c)] [∀ c, DecidableEq (κ c)] (b : ∀ c, Basis (κ c) K (V c))
    (H : ∀ c, InfinitePlace K → V c → V c → ℂ) (hH : ∀ c, IsSesq (H c)) (hP : ∀ c, PosAt (b c) (H c)) :
    PosAt (Pi.basis b) (fun v (x y : ∀ c, V c) => ∑ c, H c v (x c) (y c)) := by
  intro v
  let P : ∀ c, Matrix (κ c) (Σ c, κ c) ℂ := fun c => Matrix.of fun i s => vecAt (b c) v (Pi.basis b s c) i
  have hgram : gramOf (Pi.basis b) (fun (x y : ∀ c, V c) => ∑ c, H c v (x c) (y c)) =
      ∑ c, (P c)ᴴ * gramOf (b c) (H c v) * P c := by
    ext s t
    simp only [Matrix.sum_apply]
    rw [gramOf, Matrix.of_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sesq_eq_sum (hH c) (b c) v]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, P, Matrix.of_apply]
    rw [Finset.sum_comm]
    rfl
  rw [hgram]
  refine posDef_sum_dep _ (fun c => hP c v) P fun x hx => ?_
  funext ⟨c, i⟩
  have h1 := congrFun (hx c) i
  have h2 : ∀ s, P c i s = if s = ⟨c, i⟩ then 1 else 0 := by
    intro s
    have : P c i s = v.embedding ((Pi.basis b).repr (Pi.basis b s) ⟨c, i⟩) := by
      rw [Pi.basis_repr]
      rfl
    rw [this, Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  simpa [Matrix.mulVec, dotProduct, h2] using h1

theorem exists_frames {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (H : InfinitePlace K → V → V → ℂ) (hH : IsSesq H) (hP : PosAt b H) :
    ∃ (n : ℕ) (e : (Fin n → K) ≃ₗ[K] V) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) ∧
      ∀ v x, ((normAt (Pi.basisFun K (Fin n)) X v x ^ 2 : ℝ) : ℂ) = H v (e x) (e x) := by
  let e : (Fin (Fintype.card ι) → K) ≃ₗ[K] V := (b.reindex (Fintype.equivFin ι)).equivFun.symm
  let c := Pi.basisFun K (Fin (Fintype.card ι))
  have hH' := isSesq_comp hH e.toLinearMap
  have hP' := posAt_comp b c hH hP e.toLinearMap e.injective
  have hs := fun v => frameOf_spec (hP' v)
  refine ⟨_, e, fun v => frameOf (gramOf c fun x y => H v (e x) (e y)), fun v => (hs v).1, fun v x => ?_⟩
  rw [← majAt_self]
  have e1 := sesq_eq_sum (isSesq_maj c (fun v => frameOf (gramOf c fun x y => H v (e x) (e y)))) c v x x
  have e2 := sesq_eq_sum hH' c v x x
  rw [gramOf_maj] at e1
  refine e1.trans (Eq.trans ?_ e2.symm)
  have e3 := (hs v).2
  simp only [LinearEquiv.coe_coe] at e3 ⊢
  rw [e3]

theorem famFramed_of_pos (F : Formalism.L2.Col.GFam K) (h : F.Ok)
    (hpos : ∀ b (v : InfinitePlace K), ((F.mem b).gramV.map v.embedding).PosDef) : GlobalTheory.ColRows.FamFramed F h :=
  exists_frames (Pi.basis fun b => (F.mem b).hB (h b)) _
    (isSesq_pi (fun b v (φ ψ : (F.mem b).EqFun) => (F.mem b).ipAt (h b) v φ ψ) fun b => (F.mem b).isSesq_ipAt (h b))
    (posAt_pi _ (fun b v (φ ψ : (F.mem b).EqFun) => (F.mem b).ipAt (h b) v φ ψ) (fun b => (F.mem b).isSesq_ipAt (h b))
      fun b => (F.mem b).posAt_ipAt (h b) (hpos b) _)

end Generic

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

theorem famFramed_chF : ∀ (X : Fields) (hX : X.Ok) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (j : ℕ) (h : (chF W sel mu I u j).Ok), FamFramed (chF W sel mu I u j) h := by
  intro X hX Pr R W _ sel Sg mu I u j h
  exact famFramed_of_pos _ h fun _ v =>
    (roundPk_ratP (W.lamTrue u j) (fun d : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs => d.1.Lsh) hX).pos v

end GlobalTheory.FamilyFrames
