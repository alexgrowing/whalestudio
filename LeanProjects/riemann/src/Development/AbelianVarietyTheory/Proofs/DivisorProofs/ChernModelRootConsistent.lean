import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasChainW
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleModelCommutesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousCollapseQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteLengthOfIsTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernEvaluationCollapseVerticalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsSumToVolumeProportional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimComponent
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsSum
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison

namespace GlobalTheory.ConsAll

private theorem ext_of_prod {ι : Type} {d : ℕ} (f g : MvPolynomial ι ℚ →ₗ[ℚ] ℝ)
    (h : ∀ ν : Fin d → ι, f (∏ i, X (ν i)) = g (∏ i, X (ν i))) {P : MvPolynomial ι ℚ} (hP : P.IsHomogeneous d) :
    f P = g P := by
  classical
  rw [P.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  have h1 : u.degree = d := by
    have := hP (mem_support_iff.1 hu)
    rw [Finsupp.degree_eq_weight_one]; exact this
  have e₁ : (monomial u (P.coeff u) : MvPolynomial ι ℚ) = P.coeff u • monomial u 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  have e₂ : (monomial u 1 : MvPolynomial ι ℚ) = ((Finsupp.toMultiset u).map X).prod := by
    rw [monomial_eq, C_1, one_mul, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _]
  have e₃ : Multiset.card (Finsupp.toMultiset u) = d := by
    rw [Finsupp.card_toMultiset, ← h1]; rfl
  obtain ⟨l, hl⟩ := Quotient.exists_rep (Finsupp.toMultiset u)
  rw [e₁, map_smul, map_smul, e₂, ← hl]
  rw [← hl] at e₃
  obtain rfl : l.length = d := e₃
  have e₄ : (Multiset.map X (⟦l⟧ : Multiset ι)).prod = ∏ i, (X (l.get i) : MvPolynomial ι ℚ) := by
    change (Multiset.map X (l : Multiset ι)).prod = _
    rw [Multiset.map_coe, Multiset.prod_coe, ← List.prod_ofFn]
    congr 1
    conv_lhs => rw [← List.ofFn_get l]
    rw [List.map_ofFn]
    rfl
  rw [e₄, h]

private theorem interPoly_prod' {F : Type} [Field F] (Y : GlobalTheory.ProjVar.Var F) {κ : Type} (Δ : κ → Y.Dv) {d : ℕ}
    (h : Y.dim = d) (ν : Fin d → κ) : Y.interPoly Δ (∏ i, X (ν i)) =
      (interNum F (GlobalTheory.structureModule Y.X) fun i => GlobalTheory.Cartier.toLB (Δ (ν i)) : ℤ) := by
  subst h
  exact Y.interPoly_prod Δ ν

private noncomputable def ch {D : D7} (O : Setup D) : MvPolynomial (Rt D.what₂.Tau O.N) ℝ →ₗ[ℝ] ℝ := O.Y.chern

open Classical in

private theorem sum_interPoly (h2 : GlobalTheory.CovTop.Hypotheses2) {D : D7} (O : Setup D) {P : MvPolynomial (Rt D.what₂.Tau O.N) ℝ}
    (hP : P.IsHomogeneous (dimFl D.what₂.Tau O.N)) :
    ∑ c, (O.var c).interPoly (fun x : Rt D.what₂.Tau O.N => divOf (O.Φ.C c) (O.ex x)) P = ch O P := by
  let d := dimFl D.what₂.Tau O.N
  let ψ : MvPolynomial (Rt D.what₂.Tau O.N) ℝ →ₗ[ℝ] ℝ :=
    ∑ c, (O.var c).interPoly (fun x : Rt D.what₂.Tau O.N => divOf (O.Φ.C c) (O.ex x)) - ch O
  have hc {Q : MvPolynomial (Rt D.what₂.Tau O.N) ℝ} {e : ℕ} (hQ : Q.IsHomogeneous e) :
      homogeneousComponent d Q = if d = e then Q else 0 :=
    homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hQ)
  have hl (n : Rt D.what₂.Tau O.N → ℝ) : (GlobalTheory.ArInt.lin n ^ d).IsHomogeneous d := by
    have h1 : (GlobalTheory.ArInt.lin n).IsHomogeneous 1 := IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X (n i) i
    simpa using h1.pow d
  have key := GlobalTheory.ArInt.Model.eq_zero_of_pow d (ψ ∘ₗ homogeneousComponent d)
    (fun n => by
      rw [LinearMap.comp_apply, hc (hl _), if_pos rfl, LinearMap.sub_apply, LinearMap.sum_apply, sub_eq_zero]
      have hl : linRoot (fun τ i => ((-n (τ, i) : ℤ) : ℝ)) = GlobalTheory.ArInt.lin fun x => (n x : ℝ) := by
        simp [linRoot, GlobalTheory.ArInt.lin, Finset.sum_neg_distrib]
      have hv : ∀ Q, ch O Q = (∑ c, (O.s.cx O.L O.B O.fl).volC c) * degFl D.what₂.Tau O.N Q := fun Q => by
        show O.Y.vol * Formalism.L2.Geo.degFlL D.what₂.Tau O.N Q = _
        erw [Formalism.L2.Geo.degFlL_apply]; rfl
      rw [hv, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      have h := GlobalTheory.CompPropObj.interPoly_int (GlobalTheory.T.stronger_published_hypotheses_imply h2).p16 O c fun τ i => -n (τ, i)
      simp only [neg_neg, O.dim_eq c] at h
      refine h.trans ?_
      rw [← hl]
      rfl)
    (fun Q e he hQ => by rw [LinearMap.comp_apply, hc hQ, if_neg (Ne.symm he), map_zero])
  have := LinearMap.congr_fun key P
  rwa [LinearMap.comp_apply, hc hP, if_pos rfl, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.zero_apply,
    sub_eq_zero] at this

private theorem geo_prod (h2 : GlobalTheory.CovTop.Hypotheses2) {D : D7} (O : Setup D) (p : ℕ) [Fact p.Prime] (W : ValuationSubring ℂ)
    (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt O.S O.κ (Fact.out : p.Prime) hW)
    [IsDiscreteValuationRing (z.Z.i.c.V W)] (ν : Fin (dimFl D.what₂.Tau O.N) → Rt D.what₂.Tau O.N) :
    ((∑ C : (nmodel z.Z).Comp, ((nmodel z.Z).comp C).toBase.fibreDeg (picSymPull ((nmodel z.Z).compι C)
      (∏ i, (z.rootLB false (tauEmb D (ν i).1) (ν i).2).c1)) : ℚ) : ℝ) = (cov z : ℝ) * ch O (∏ i, X (ν i)) := by
  have hN := O.S.rank_eq
  have hN2 := O.S.two_le
  have hs := GlobalTheory.ConsGeo.sum_fibreDeg (Fact.out : p.Prime) hW (by omega) z O.Φ (dimFl D.what₂.Tau O.N) O.dim_eq
    (RelDim.relDim_comp D O.A O.N O.j O.S O.κ p Fact.out W hW z)
    (fun i => z.rootLB false (tauEmb D (ν i).1) (ν i).2) (fun c i => divOf (O.Φ.C c) (O.ex (ν i)))
    fun L c X _ ι sX h₁ h₂ θ h₃ i => GlobalTheory.ConsGeo.root_agree h2.p22 Fact.out hW z L _ X ι sX h₁ h₂ θ h₃ _
      (if_pos (O.A.cm (ν i).1)) _ ((ν i).2.2.trans_eq hN.symm)
  have hh : (∏ i, X (ν i) : MvPolynomial (Rt D.what₂.Tau O.N) ℝ).IsHomogeneous (dimFl D.what₂.Tau O.N) := by
    simpa using IsHomogeneous.prod Finset.univ (fun i => (X (ν i) : MvPolynomial (Rt D.what₂.Tau O.N) ℝ)) (fun _ => 1)
      fun i _ => isHomogeneous_X ℝ _
  refine (congrArg (fun a : ℚ => (a : ℝ)) hs).trans ?_
  rw [← sum_interPoly h2 O hh, Rat.cast_mul, Rat.cast_natCast, Rat.cast_sum]
  refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
  rw [interPoly_prod' (O.var c) _ (O.dim_eq c) ν, Rat.cast_intCast]

private theorem aeval_ext {ι A : Type} [CommRing A] [Algebra ℚ A] {d : ℕ} (f : A →ₗ[ℚ] ℚ) (a : ι → A)
    (g : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (c : ℝ) (h : ∀ ν : Fin d → ι, (f (∏ i, a (ν i)) : ℝ) = c * g (∏ i, X (ν i)))
    {P : MvPolynomial ι ℚ} (hP : P.IsHomogeneous d) : (f (aeval a P) : ℝ) = c * g (toR P) :=
  ext_of_prod (Algebra.linearMap ℚ ℝ ∘ₗ f ∘ₗ (aeval a).toLinearMap)
    (((c • g).restrictScalars ℚ) ∘ₗ (mapAlgHom (Algebra.ofId ℚ ℝ)).toLinearMap) (fun ν => by simpa using h ν) hP

private theorem geoAll (h2 : GlobalTheory.CovTop.Hypotheses2) {D : D7} (O : Setup D) (p : ℕ) [Fact p.Prime] (W : ValuationSubring ℂ)
    (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt O.S O.κ (Fact.out : p.Prime) hW)
    [IsDiscreteValuationRing (z.Z.i.c.V W)] (P : MvPolynomial (Rt D.what₂.Tau O.N) ℚ)
    (hP : P.IsHomogeneous (dimFl D.what₂.Tau O.N)) :
    ((∑ C : (nmodel z.Z).Comp, ((nmodel z.Z).comp C).toBase.fibreDeg (picSymPull ((nmodel z.Z).compι C)
      (aeval (fun x : Rt D.what₂.Tau O.N => (z.rootLB false (tauEmb D x.1) x.2).c1) P)) : ℚ) : ℝ) =
      (cov z : ℝ) * ch O (toR P) := by
  let f : PicSym z.Z.X →ₗ[ℚ] ℚ :=
    ∑ C : (nmodel z.Z).Comp, ((nmodel z.Z).comp C).toBase.fibreDeg ∘ₗ (picSymPull ((nmodel z.Z).compι C)).toLinearMap
  have hf (Q : PicSym z.Z.X) : f Q = ∑ C : (nmodel z.Z).Comp, ((nmodel z.Z).comp C).toBase.fibreDeg
      (picSymPull ((nmodel z.Z).compι C) Q) := LinearMap.sum_apply _ _ _
  rw [← hf]
  refine aeval_ext f _ (ch O) _ (fun ν => ?_) hP
  rw [hf]
  exact geo_prod h2 O p W hW z ν

private theorem capDeg_divP_eq_sum {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime]
    [CharZero O] [CharP (ResidueField O) p] (Z : NModel O) (d : ℕ) (hd : ∀ C, (Z.comp C).relDim = d) (Q : PicSym Z.X) :
    Z.capDeg_vp p d (NModel.toQ (Z.divP p)) Q = ∑ C, (Z.comp C).toBase.fibreDeg (picSymPull (Z.compι C) Q) := by
  rw [NModel.capDeg_vp_eq_sum, Finset.filter_true_of_mem fun C _ => hd C]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [NModel.vResQ_toQ, NModel.divP, NModel.vRes_div]
  exact GlobalTheory.T.capDeg_divP_eq_fibreDeg' O p (Z.comp C) _

end GlobalTheory.ConsAll

set_option maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.chern_model_root_consistent : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PrismaticDieudonnePerfd → AtAll fun _ O _ _ _ _ jc z => Cons (mdlOf z jc) (rootOf z jc) O.Y.chern := by
  intro h2 _ _ _ _ D O _ p _ W hW jc _ z G hG
  have hcomm : Comm (mdlOf z jc) := GlobalTheory.T.admissible_model_commutes D O.A O.N O.j O.S O.κ p Fact.out W hW z jc
  have hI : ∀ y ∈ Ideal.span (Set.range (mdlOf z jc).Z.cD), (mdlOf z jc).Z.capDeg (mdlOf z jc).Z.divP y = 0 := by
    intro y hy
    suffices h : ∀ a, (mdlOf z jc).Z.capDeg (mdlOf z jc).Z.divP (a * y) = 0 by simpa using h 1
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨V, rfl⟩ := hx
      intro a
      rw [mul_comm, hcomm, (mdlOf z jc).Z.cD_divP, zero_mul, map_zero]
    | zero => intro a; simp
    | add x y _ _ hx hy => intro a; rw [mul_add, map_add, hx, hy, add_zero]
    | smul b x _ hx => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hx _
  have e1 : (mdlOf z jc).Z.capDeg (mdlOf z jc).Z.divP (evC (mdlOf z jc) (rootOf z jc) G) =
      (mdlOf z jc).Z.capDeg (mdlOf z jc).Z.divP
        (aeval (fun x => (mdlOf z jc).Z.c1 (rootOf z jc (false, x))) (GlobalTheory.ConsNumber.collapseQ D O.N G)) := by
    rw [← sub_eq_zero, ← map_sub]
    exact hI _ (GlobalTheory.T.chern_evaluation_collapse_vertical D O.A O.N O.j O.S O.κ p Fact.out W hW z jc G)
  haveI := isDiscreteValuationRing_V z.Z.i.c (Fact.out : p.Prime) hW
  haveI := charP_residueField_of_mem_nonunits z.Z.i.c (Fact.out : p.Prime) hW
  have e2 : ∀ Q : (mdlOf z jc).Z.Ch, (mdlOf z jc).Z.capDeg (mdlOf z jc).Z.divP Q =
      ∑ C, ((nmodel z.Z).comp C).toBase.fibreDeg (picSymPull ((nmodel z.Z).compι C) Q) := fun Q =>
    GlobalTheory.ConsAll.capDeg_divP_eq_sum p (nmodel z.Z) _ (RelDim.relDim_comp D O.A O.N O.j O.S O.κ p Fact.out W hW z) Q
  have hcov : (0 : ℝ) < ((mdlOf z jc).cov : ℝ) := Nat.cast_pos.2 (mdlOf z jc).cov_pos
  have e3 := (GlobalTheory.ConsAll.geoAll h2 O p W hW z _ (GlobalTheory.ConsNumber.isHomogeneous_collapseQ D O.N hG)).trans
    (congrArg (fun Q => (cov z : ℝ) * GlobalTheory.ConsAll.ch O Q) (GlobalTheory.ConsNumber.toR_collapseQ D O.N G))
  exact (div_eq_iff hcov.ne').2 ((congrArg (fun a : ℚ => (a : ℝ)) (e1.trans (e2 _))).trans (e3.trans (mul_comm _ _)))
