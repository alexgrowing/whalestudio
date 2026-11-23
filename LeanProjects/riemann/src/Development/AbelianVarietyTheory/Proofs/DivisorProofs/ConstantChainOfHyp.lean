import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasChainW
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousAevalOfWeighted
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootLetterInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleModelCommutes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernModelRootConsistent

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.HodgeTateGlobal

namespace GlobalTheory.ConsWhole

variable {D : D7} {p : ℕ} [Fact p.Prime] {N : ℕ} {rk : Emb D p → ℕ} (M : DV.Mdl D p N rk)
  (rt : Bool × Rt D.what₂.Tau N → M.Z.LB)

theorem lieW_pow_divP (hc : Comm M) (j : ℕ) (e : Fin (D.R.f * N) ≃ Rt D.what₂.Tau N)
    (V : Fin (D.R.f * N) → M.Z.VDiv)
    (he : ∀ l, M.Z.c1 (M.lieW.x l) = (if ((e l).2 : ℕ) < j then (1 : ℚ) else -1) • M.Z.c1 (rt (false, e l)) +
      M.Z.cD (V l)) (k : ℕ) (Q : M.Z.Ch) :
    M.Z.capDeg M.Z.divP ((∑ l, M.Z.c1 (M.lieW.x l) ^ k) * Q) =
      M.Z.capDeg M.Z.divP (evC M rt (∑ τ, (liePow (N := N) j k (Sum.inl τ) + liePow j k (Sum.inr τ))) * Q) := by
  simp only [he, Finset.sum_mul, map_sum, capDeg_divP_pow hc]
  rw [← map_sum, ← Finset.sum_mul]
  congr 2
  have e1 : ∀ F : D.what₂.Tau → MvPolynomial (Vm D.what₂.Tau N) ℚ,
      evC M rt (∑ τ, F τ) = ∑ τ, evC M rt (F τ) := fun F => by simp [evC, evQ]
  have e2 : ∀ F G : MvPolynomial (Vm D.what₂.Tau N) ℚ, evC M rt (F + G) = evC M rt F + evC M rt G :=
    fun F G => by simp [evC, evQ]
  rw [e1, e.sum_comp (fun r => ((if (r.2 : ℕ) < j then (1 : ℚ) else -1) • M.Z.c1 (rt (false, r))) ^ k),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [e2, evC_liePow_inl, evC_liePow_inr, sum_split j]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_pos (Finset.mem_filter.1 hi).2, one_smul]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_neg (not_lt.2 (Finset.mem_filter.1 hi).2), neg_one_smul]

theorem consW_of (j : ℕ) (chern : MvPolynomial (Rt D.what₂.Tau N) ℝ →ₗ[ℝ] ℝ) (hc : Comm M)
    (hg : ∃ (e : Fin (D.R.f * N) ≃ Rt D.what₂.Tau N) (V : Fin (D.R.f * N) → M.Z.VDiv), ∀ l,
      M.Z.c1 (M.lieW.x l) = (if ((e l).2 : ℕ) < j then (1 : ℚ) else -1) • M.Z.c1 (rt (false, e l)) + M.Z.cD (V l))
    (hC : Cons M rt chern) : ConsW M rt j chern := by
  obtain ⟨e, V, he⟩ := hg
  intro m hm G hG
  have hH : (∑ τ, (liePow (N := N) j 1 (Sum.inl τ) + liePow j 1 (Sum.inr τ))).IsWeightedHomogeneous
      (wt D.what₂.Tau N) 1 :=
    IsWeightedHomogeneous.sum _ _ _ fun τ _ => (homog_liePow _ _ (Sum.inl τ)).add (homog_liePow _ _ (Sum.inr τ))
  have hHG := hH.mul hG
  rw [show 1 + m = dimFl D.what₂.Tau N by omega] at hHG
  have key := hC _ hHG
  rw [evC_mul, ← lieW_pow_divP M rt hc j e V he 1] at key
  have e3 : collapse D N (toR (∑ τ, (liePow (N := N) j 1 (Sum.inl τ) + liePow j 1 (Sum.inr τ)))) = chLieA D N j 1 := by
    simp only [chLieA, chLie_eq, toR, map_sum, map_add, Nat.factorial_one, Nat.cast_one, inv_one, map_one, one_mul]
  rw [chDiv, Nat.factorial_one, Nat.cast_one, div_one, key, ← e3, ← map_mul, toR, toR, toR, map_mul]

theorem consWSt_of (hC : AtAll fun _ O _ _ _ _ jc z => Cons (mdlOf z jc) (rootOf z jc) O.Y.chern) : ConsWSt := by
  intro D O hO p _ W hW jc hP z
  exact consW_of (mdlOf z jc) (rootOf z jc) O.Y.j O.Y.chern
    (GlobalTheory.VertCommAdm.comm_mdlOf D O.A O.N O.j O.S O.κ p Fact.out W hW z jc)
    (GlobalTheory.ShFam.Pad.LieGen.lieW_gen D O.A O.N O.j O.S O.κ p Fact.out W hW z jc) (hC D O hO p W hW jc hP z)

theorem consWSt : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ScholzeWeinsteinB →
    GlobalTheory.Published.PrismaticDieudonnePerfd → ConsWSt :=
  fun h1 h2 h3 h4 h5 => consWSt_of (GlobalTheory.T.chern_model_root_consistent h1 h2 h3 h4 h5)

end GlobalTheory.ConsWhole

end
