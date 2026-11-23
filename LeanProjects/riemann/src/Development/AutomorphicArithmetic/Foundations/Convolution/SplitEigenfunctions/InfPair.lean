import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEig
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfCharConjEmbeddingNegOfInvariantPairing

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem neg_of_prod_eq {m m' : Multiset ℂ} (hc : m.card = 2) (hc' : m'.card = 2)
    (h : ∀ u : ℂ, (m.map (u + ·)).prod = (m'.map (-u + ·)).prod) : m' = m.map Neg.neg := by
  obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.1 hc
  obtain ⟨c, d, rfl⟩ := Multiset.card_eq_two.1 hc'
  have key : ∀ u : ℂ, (u + a) * (u + b) = (-u + c) * (-u + d) := fun u => by
    simpa [Multiset.insert_eq_cons] using h u
  have h0 := key 0
  have h1 := key 1
  have hs : a + b = -(c + d) := by linear_combination h1 - h0
  have hz : (c + a) * (c + b) = 0 := by
    have := key c
    simpa using this
  rcases mul_eq_zero.1 hz with e | e
  · have e1 : c = -a := by linear_combination e
    have e2 : d = -b := by linear_combination hs - e
    simp [e1, e2, Multiset.insert_eq_cons]
  · have e1 : c = -b := by linear_combination e
    have e2 : d = -a := by linear_combination hs - e
    simp only [e1, e2, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
    exact Multiset.cons_swap _ _ _

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.infPair :
    InfPair := by
  intro E _ _ _ V Q B hB hne τ m m' hc hm hm'
  obtain ⟨x, y, hxy⟩ : ∃ x y, B x y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (LinearMap.ext fun x => LinearMap.ext fun y => hcon x y)
  let S := GlobalTheory.CapPair.adjPairs V Q.V B
  have h1 : ∀ i j z, (GlobalTheory.CuspRep.lieS E 2 i j (GlobalTheory.CuspRep.atEmb τ z),
      -MulOpposite.op (GlobalTheory.CuspRep.lieS E 2 i j (GlobalTheory.CuspRep.atEmb τ z))) ∈ S := by
    intro i j z φ ψ
    have h := hB.lie (toL (Matrix.single i j (GlobalTheory.CuspRep.atEmb τ z))) φ ψ
    rw [add_eq_zero_iff_eq_neg, ← map_neg] at h
    exact ⟨hB.st (.lie _) _ φ.2, neg_mem (hB.st' (.lie _) _ ψ.2), h⟩
  have h2 : ∀ i j, (GlobalTheory.CuspRep.Eop (a := 2) τ i j, -MulOpposite.op (GlobalTheory.CuspRep.Eop (a := 2) τ i j)) ∈ S := fun i j => by
    convert S.smul_mem (S.sub_mem (h1 i j 1) (S.smul_mem (h1 i j Complex.I) Complex.I)) (1 / 2) using 1
    refine Prod.ext rfl ?_
    simp only [GlobalTheory.CuspRep.Eop, MulOpposite.op_smul, MulOpposite.op_sub, Prod.smul_snd, Prod.snd_sub]
    module
  have h3 : ∀ w, Formalism.REAL.qdet (fun i j => (GlobalTheory.CuspRep.Eop (a := 2) τ i j, -MulOpposite.op (GlobalTheory.CuspRep.Eop (a := 2) τ i j))) w ∈ S := fun w => by
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (h2 _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  have h4 : ∀ u, (GlobalTheory.CuspRep.cap (a := 2) τ u, MulOpposite.op ((-1 : ℂ) ^ 2 • GlobalTheory.CuspRep.cap (a := 2) τ (-u) : Module.End ℂ (Sm E 2))) ∈ S := fun u => by
    convert h3 (u + (((2 : ℕ) : ℂ) - 1) / 2) using 1
    rw [GlobalTheory.CapPair.qdet_prod, GlobalTheory.CapPair.qdet_antipode (A := Module.End ℂ (Sm E 2)) (GlobalTheory.CuspRep.glRel_Eop (a := 2) τ),
      show ((2 : ℕ) : ℂ) - 1 - (u + (((2 : ℕ) : ℂ) - 1) / 2) = -u + (((2 : ℕ) : ℂ) - 1) / 2 by ring]
    rfl
  refine neg_of_prod_eq hc hm'.1 fun u => ?_
  obtain ⟨h, h', e'⟩ := h4 u x y
  have e1 : (⟨_, h⟩ : V) = (m.map (u + ·)).prod • x := Subtype.ext (hm u _ x.2)
  have e3 : (⟨_, h'⟩ : Q.V) = (m'.map (-u + ·)).prod • y := Subtype.ext (by
    change (-1 : ℂ) ^ 2 • GlobalTheory.CuspRep.cap (a := 2) τ (-u) y.1 = _ • y.1
    rw [hm'.2 _ _ y.2]
    simp)
  have e4 : B ((m.map (u + ·)).prod • x) y = B x ((m'.map (-u + ·)).prod • y) := by
    rw [← e1, ← e3]
    exact e'
  rw [map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at e4
  exact mul_right_cancel₀ hxy e4
