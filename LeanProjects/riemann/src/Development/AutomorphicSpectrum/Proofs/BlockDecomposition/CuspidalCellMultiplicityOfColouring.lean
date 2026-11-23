import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSingleNonzeroFactorEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySublistPaddingStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SubsingletonIrrClZero

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProdCell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_class_of_degree (n : ℕ) (t : IrrGL k) (h : t.1 = n) :
    ∃ u : IrrCl (GL (Fin n) k), (⟨n, u⟩ : IrrGL k) = t := by
  subst h
  exact ⟨t.2, rfl⟩

theorem subsingleton_irrCl_of_eq_zero (n : ℕ) (h : n = 0) : Subsingleton (IrrCl (GL (Fin n) k)) := by
  subst h
  exact GlobalTheory.SmGL.SegModel.subsingleton_irrCl_zero

theorem class_eq_of_sigma_eq (t : IrrGL k) (z : IrrCl (GL (Fin t.1) k))
    (h : (⟨t.1, z⟩ : IrrGL k) = t) : z = t.2 :=
  eq_of_heq (Sigma.ext_iff.1 h).2

set_option maxHeartbeats 1600000 in

theorem jhMult_cell_colour : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (x : Fin h → IrrGL k) (W : List (IrrGL k)) (b : Fin h → Fin W.length → ℕ) (hrow : ∀ i, ∑ j, b i j = (x i).1) (hcol : ∀ j, ∑ i, b i j = (W.get j).1) (c : Fin W.length → Fin h), (∀ i j, b i j = if c j = i then (W.get j).1 else 0) → jhMult (piTensor fun j => (W.get j).rep) (cellFunctor (c := fun i j => Fin (b i j)) (fun i => stdBlocks (b i) (hrow i)) (fun j => stdBlocks (fun i => b i j) (hcol j)) (piTensor fun i => (x i).rep)) = ∏ i, jmL (sub W c i) (x i).rep := by
  intro k _ _ _ _ h x W b hrow hcol c hb
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hC : CellSemisimplification k := (GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).2
  obtain ⟨T, hT0, hT⟩ := hC (Fin h) (Fin W.length) (fun i => Fin (x i).1) (fun j => Fin (W.get j).1)
    (fun i j => Fin (b i j)) (fun i => stdBlocks (b i) (hrow i))
    (fun j => stdBlocks (fun i => b i j) (hcol j)) (fun i => (x i).2.rep.V) (fun i => (x i).rep)
    (fun i => (x i).2.rep.smooth) (fun i => (x i).2.rep.hasFiniteLength)
  have hirr : (piTensor fun j => (W.get j).rep).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (W.get j).2.rep
  let τ : IrrRep (Levi k fun j => Fin (W.get j).1) :=
    ⟨_, piTensor fun j => (W.get j).rep, isSmooth_piTensor fun j => (W.get j).2.rep.smooth, hirr⟩
  refine (hT τ).trans ?_
  have hzero : ∀ i j, c j ≠ i → b i j = 0 := fun i j hij => by rw [hb, if_neg hij]

  have hcolumn : ∀ (s : ∀ i j, IrrCl (GL (Fin (b i j)) k)) (j : Fin W.length),
      ∃ z : IrrCl (GL (Fin (W.get j).1) k), (⟨_, z⟩ : IrrGL k) = ⟨b (c j) j, s (c j) j⟩ ∧
        Nonempty ((multiProd (stdBlocks (fun i => b i j) (hcol j))
          fun i => (s i j).rep.ρ).Equiv z.rep.ρ) := fun s j =>
    GlobalTheory.T.product_single_nonzero_factor_equiv (fun i => (⟨b i j, s i j⟩ : IrrGL k)) (hcol j) (c j)
      fun i hi => hzero i j (Ne.symm hi)

  have hex : ∀ i j, ∃ u : IrrCl (GL (Fin (b i j)) k),
      c j = i → (⟨b i j, u⟩ : IrrGL k) = W.get j := by
    intro i j
    by_cases hij : c j = i
    · obtain ⟨u, hu⟩ := exists_class_of_degree (b i j) (W.get j) (by rw [hb, if_pos hij])
      exact ⟨u, fun _ => hu⟩
    · exact ⟨(IrrRep.det (Fin (b i j)) 1 isSmoothChar_one).cl, fun h' => absurd h' hij⟩
  choose s₀ hs₀ using hex
  have hfirst : ∀ i, jhMult (piTensor fun j => (s₀ i j).rep.ρ)
      (jac (stdBlocks (b i) (hrow i)) (x i).rep) = jmL (sub W c i) (x i).rep := fun i =>
    GlobalTheory.T.jacquet_multiplicity_sublist_padding W c i (fun j => (⟨b i j, s₀ i j⟩ : IrrGL k)) (fun j hj => hs₀ i j hj)
      (fun j hj => hzero i j hj) (hrow i) (x i).rep
  rw [Finset.sum_eq_single s₀]
  · choose z hz e using hcolumn s₀
    have hzW : ∀ j, z j = (W.get j).2 := fun j =>
      class_eq_of_sigma_eq _ _ ((hz j).trans (hs₀ (c j) j rfl))
    have hsecond : jhMult τ.ρ (piTensor fun j =>
        multiProd (stdBlocks (fun i => b i j) (hcol j)) fun i => (s₀ i j).rep.ρ) = 1 := by
      have a : (piTensor fun j => multiProd (stdBlocks (fun i => b i j) (hcol j))
          fun i => (s₀ i j).rep.ρ).Equiv (piTensor fun j => (W.get j).rep) :=
        LocGL.piTensorEquiv fun j => (e j).some.trans (by rw [hzW j]; exact .refl _)
      exact (jhMult_congr_right _ a).trans (jhMult_self hirr)
    rw [hsecond, mul_one]
    exact Finset.prod_congr rfl fun i _ => hfirst i
  · intro s _ hs
    refine mul_eq_zero_of_right _ ?_
    choose z hz e using hcolumn s
    have a : (piTensor fun j => multiProd (stdBlocks (fun i => b i j) (hcol j))
        fun i => (s i j).rep.ρ).Equiv (piTensor fun j => (z j).rep.ρ) :=
      LocGL.piTensorEquiv fun j => (e j).some
    refine (jhMult_congr_right _ a).trans ?_
    by_contra hne
    obtain ⟨φ⟩ := (jhMult_ne_zero_iff.1 hne).nonempty_equiv hirr
      (GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (z j).rep)
    have hcl : ∀ j, (W.get j).2 = z j := fun j => by
      have := GlobalTheory.T.tensor_product_determines_factor_classes _ (fun j => GL (Fin (W.get j).1) k) (fun j => (W.get j).2.rep)
        (fun j => (z j).rep) ⟨φ.symm⟩ j
      rwa [IrrCl.cl_rep, IrrCl.cl_rep] at this
    refine hs (funext fun i => funext fun j => ?_)
    by_cases hij : c j = i
    · subst hij
      have h1 : (⟨b (c j) j, s (c j) j⟩ : IrrGL k) = ⟨b (c j) j, s₀ (c j) j⟩ := by
        rw [hs₀ (c j) j rfl, ← hz j, ← hcl j]
      exact eq_of_heq (Sigma.mk.inj_iff.1 h1).2
    · haveI := subsingleton_irrCl_of_eq_zero (k := k) (b i j) (hzero i j hij)
      exact Subsingleton.elim _ _
  · intro hs
    obtain ⟨i, hi⟩ := hT0 s₀ hs
    exact mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ i) hi) _

end GlobalTheory.CompanionTheory.FineProdCell
