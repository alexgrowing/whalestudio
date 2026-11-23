import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BundleDegreeEqSumValuationsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeBasisAdaptedToSubspaceStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundlesStatement

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg

theorem det_adapted {K V : Type} [Field K] [AddCommGroup V] [Module K V] (W : Submodule K V)
    {m n : ℕ} (bW cW : Module.Basis (Fin m) K W) (bQ cQ : Module.Basis (Fin n) K (V ⧸ W))
    (b c : Module.Basis (Fin (m + n)) K V)
    (hb1 : ∀ j, b (Fin.castAdd _ j) = bW j) (hb2 : ∀ j, W.mkQ (b (Fin.natAdd _ j)) = bQ j)
    (hc1 : ∀ j, c (Fin.castAdd _ j) = cW j) (hc2 : ∀ j, W.mkQ (c (Fin.natAdd _ j)) = cQ j) :
    b.det c = bW.det cW * bQ.det cQ := by
  have h1 : ∀ (i : Fin m) (x : W), b.repr (x : V) (Fin.castAdd _ i) = bW.repr x i := by
    intro i x
    have : (b.coord (Fin.castAdd _ i)).comp W.subtype = bW.coord i := by
      refine bW.ext fun j => ?_
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply,
        ← hb1, Module.Basis.repr_self, Finsupp.single_apply, Fin.castAdd_inj]
    exact LinearMap.congr_fun this x
  have h2 : ∀ (i : Fin n) (x : V), b.repr x (Fin.natAdd _ i) = bQ.repr (W.mkQ x) i := by
    intro i x
    have : b.coord (Fin.natAdd _ i) = (bQ.coord i).comp W.mkQ := by
      refine b.ext fun j => ?_
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · have h0 : W.mkQ (b (Fin.castAdd n j)) = 0 := by
          rw [hb1]; simp
        have hne : Fin.castAdd n j ≠ Fin.natAdd m i := by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
        simp only [LinearMap.comp_apply, Module.Basis.coord_apply, h0, map_zero,
          Module.Basis.repr_self, Finsupp.single_apply, hne, if_false, Finsupp.coe_zero,
          Pi.zero_apply]
      · simp only [LinearMap.comp_apply, Module.Basis.coord_apply, hb2,
          Module.Basis.repr_self, Finsupp.single_apply, Fin.natAdd_inj]
    exact LinearMap.congr_fun this x
  have key : (b.toMatrix c).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (bW.toMatrix cW)
        (Matrix.of fun i j => b.repr (c (Fin.natAdd _ j)) (Fin.castAdd _ i)) 0
        (bQ.toMatrix cQ) := by
    ext (i | i) (j | j)
    · simp [Module.Basis.toMatrix_apply, hc1, h1]
    · simp [Module.Basis.toMatrix_apply]
    · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
        Module.Basis.toMatrix_apply, hc1, h2, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 (cW j).2]
      simp
    · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right,
        Module.Basis.toMatrix_apply, hc2, h2, Matrix.fromBlocks_apply₂₂]
  rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply,
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv, key, Matrix.det_fromBlocks_zero₂₁]

theorem deg_eq_subDeg_add_deg_quot : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type)
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V)
    (W : Submodule K V), IsBun C L → deg C L = subDeg C L W + deg C (quot C L W) := by
  intro K _ C V _ _ _ L W hL
  rcases isEmpty_or_nonempty C.I with hI | ⟨⟨i₀⟩⟩
  · simp [subDeg, deg, finsum_of_isEmpty]
  have hex := fun i => (hL.1 i).elim fun b hb => GlobalTheory.T.lattice_basis_adapted_to_subspace K C V i _ b (L i) W hb
  choose bW bQ b hb hbW hbQ h1 h2 using hex
  obtain ⟨hS, hQ⟩ := GlobalTheory.T.sub_and_quotient_bundles K C V L W hL
  obtain ⟨-, eL⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L _ (b i₀) b hL hb
  obtain ⟨fS, eS⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C W (sub C L W) _ (bW i₀) bW hS hbW
  obtain ⟨fQ, eQ⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C (V ⧸ W) (quot C L W) _ (bQ i₀) bQ hQ hbQ
  rw [subDeg, eL, eS, eQ, ← finsum_add_distrib]
  · refine finsum_congr fun i => ?_
    rw [det_adapted W (bW i₀) (bW i) (bQ i₀) (bQ i) (b i₀) (b i) (h1 i₀) (h2 i₀) (h1 i) (h2 i),
      map_mul, WithZero.log_mul, mul_add]
    · exact (C.v i).ne_zero_iff.2 ((bW i₀).isUnit_det (bW i)).ne_zero
    · exact (C.v i).ne_zero_iff.2 ((bQ i₀).isUnit_det (bQ i)).ne_zero
  · refine fS.subset fun i hi h => hi ?_
    simp only [h, WithZero.log_one, mul_zero]
  · refine fQ.subset fun i hi h => hi ?_
    simp only [h, WithZero.log_one, mul_zero]

end GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg
