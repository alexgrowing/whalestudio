import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Unfold2
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.EisCellsAsm

section Compl

variable {K : Type} [Field K]

theorem exists_isCompl {n r : ℕ} (c : Matrix (Fin r) (Fin n) K) (hc : LinearIndependent K c) :
    ∃ a : Matrix (Fin n) (Fin n) K, IsCompl c a := by
  classical
  set W := Submodule.span K (Set.range c) with hW
  obtain ⟨W', hWW'⟩ := Submodule.exists_isCompl W
  have hrW : Module.finrank K W = r := by
    rw [hW, finrank_span_eq_card hc, Fintype.card_fin]
  have hsum := Submodule.finrank_add_eq_of_isCompl hWW'
  rw [hrW, Module.finrank_fin_fun] at hsum
  set m := Module.finrank K W' with hm
  have hn : n = r + m := hsum.symm
  let bW : Module.Basis (Fin m) K W' := Module.finBasisOfFinrankEq K W' hm.symm
  let d : Fin m → (Fin n → K) := fun j => (bW j : Fin n → K)
  have hd : LinearIndependent K d :=
    bW.linearIndependent.map' W'.subtype (Submodule.ker_subtype W')
  have hdisj : Disjoint (Submodule.span K (Set.range c)) (Submodule.span K (Set.range d)) := by
    refine hWW'.disjoint.mono_right ?_
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (bW j).2
  have hv : LinearIndependent K (Sum.elim c d) := hc.sum_type hd hdisj
  let e : Fin n ≃ Fin r ⊕ Fin m := (finCongr hn).trans finSumFinEquiv.symm
  refine ⟨fun i => Sum.elim c d (e i), ?_, ?_⟩
  · have hli : LinearIndependent K (fun i => Sum.elim c d (e i)) := hv.comp e e.injective
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hli)
  · intro i hi
    have he : e i = Sum.inl ⟨i, hi⟩ := by
      have : finCongr hn i = Fin.castAdd m ⟨i, hi⟩ := Fin.ext rfl
      simp only [e, Equiv.trans_apply, this, finSumFinEquiv_symm_apply_castAdd]
    change Sum.elim c d (e i) = c ⟨i, hi⟩
    rw [he]
    rfl

end Compl

variable {D : D7} {n : ℕ}

abbrev sg (D : D7) : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)

theorem sg_sg (D : D7) (x : D.host.E) : sg D (sg D x) = x := by
  show star (star x) = x
  exact star_star x

theorem mat_mul' (x y : G D n) : mat (x * y) = mat x * mat y := by
  simp only [mat, map_mul, Units.val_mul]

theorem mat_inv_of (x : G D n) {g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} (hg : IsUnit g.det)
    (h : mat x = g.map (incA D)) : mat x⁻¹ = g⁻¹.map (incA D) := by
  have h1 : mat x⁻¹ = (mat x)⁻¹ := by
    simp only [mat, map_inv, Matrix.coe_units_inv]
  rw [h1, h]
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul g hg, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mk_eq_iff_siegel (hR : RatPts) (x y : GF D n) {gx gy : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E}
    (hx : IsUnit gx.det) (mx : mat x.1 = gx.map (incA D)) (my : mat y.1 = gy.map (incA D)) :
    mk ((P D n).subgroupOf (GF D n)) x = mk ((P D n).subgroupOf (GF D n)) y ↔ IsSiegelP (gy * gx⁻¹) := by
  have hmem : y.1 * x.1⁻¹ ∈ GF D n := mul_mem y.2 (inv_mem x.2)
  have hmat : mat (y.1 * x.1⁻¹) = (gy * gx⁻¹).map (incA D) := by
    rw [mat_mul', mat_inv_of x.1 hx mx, my, Matrix.map_mul]
  rw [← (hR D n).2.2 _ hmem _ hmat]
  show Quotient.mk _ x = Quotient.mk _ y ↔ _
  rw [Quotient.eq, QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem isSiegelParabolic_one (K : Type) [Field K] (n : ℕ) : IsSiegelP (1 : Matrix (Fin (n + n)) (Fin (n + n)) K) := by
  unfold IsSiegelP
  intro i j
  exact Matrix.one_apply_ne (finSumFinEquiv.injective.ne Sum.inr_ne_inl)

theorem eisCells_of : Bruhat → RatPts → PInv → Term2 → EisCells := by
  intro hBr hRat hPInv hT2 D n V ψ χ θ μ ω hS Φ hconv μr hμr c hc
  classical
  have ha : ∀ U : Submodule D.host.E (Fin n → D.host.E), ∃ a, IsCompl (c U) a :=
    fun U => exists_isCompl (c U) (hc U).1
  choose a haU using ha
  obtain ⟨hU, huniq⟩ := hBr D.host.E (sg D) (sg_sg D) two_ne_zero n c hc a haU
  have hq : ∀ q : (U : Submodule D.host.E (Fin n → D.host.E)) × HermE D (Module.finrank D.host.E U),
      ∃ γ ∈ GF D n, mat γ = (repMat (sg D) q.2.1 (a q.1)).map (incA D) :=
    fun q => (hRat D n).2.1 _ (hU q.1 q.2.1 q.2.2).1 (hU q.1 q.2.1 q.2.2).2
  choose γ hγGF hγmat using hq
  have hdet : ∀ q : (U : Submodule D.host.E (Fin n → D.host.E)) × HermE D (Module.finrank D.host.E U),
      IsUnit (repMat (sg D) q.2.1 (a q.1)).det := fun q => (hU q.1 q.2.1 q.2.2).1
  let f : ((U : Submodule D.host.E (Fin n → D.host.E)) × HermE D (Module.finrank D.host.E U)) →
      GlobalTheory.Eis.Cosets (P D n) (GF D n) :=
    fun q => mk ((P D n).subgroupOf (GF D n)) ⟨γ q, hγGF q⟩
  have hinj : Function.Injective f := by
    intro q q' hqq
    have h1 : IsSiegelP (repMat (sg D) q'.2.1 (a q'.1) * (repMat (sg D) q.2.1 (a q.1))⁻¹) :=
      (mk_eq_iff_siegel hRat ⟨γ q, hγGF q⟩ ⟨γ q', hγGF q'⟩ (hdet q) (hγmat q) (hγmat q')).mp hqq
    have h2 : IsSiegelP (repMat (sg D) q'.2.1 (a q'.1) * (repMat (sg D) q'.2.1 (a q'.1))⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ (hdet q')]
      exact isSiegelParabolic_one _ n
    exact (huniq _ (hdet q') (hU q'.1 q'.2.1 q'.2.2).2).unique h1 h2
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨g, hg, hgu, hgm⟩ := (hRat D n).1 _ (Quotient.out z).2
    obtain ⟨q, hqs, -⟩ := huniq g hg hgu
    refine ⟨q, ?_⟩
    rw [← Quotient.out_eq z]
    exact (mk_eq_iff_siegel hRat ⟨γ q, hγGF q⟩ (Quotient.out z) (hdet q) (hγmat q) hgm).mpr hqs
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hrle : ∀ U : Submodule D.host.E (Fin n → D.host.E), Module.finrank D.host.E U ≤ n := fun U =>
    (Submodule.finrank_le U).trans_eq (Module.finrank_fin_fun _)
  have hsum : Summable (GlobalTheory.Eis.term (P D n) (GF D n) (fun γ => ((ω γ) Φ).1 0) 1) := Summable.of_norm hconv
  have h3 := (e.hasSum_iff).mpr hsum.hasSum
  unfold GlobalTheory.Eis.cosetSum
  convert h3 using 1
  funext q
  have hrel : (⟨γ q, hγGF q⟩ : GF D n) * (Quotient.out (e q))⁻¹ ∈ (P D n).subgroupOf (GF D n) := by
    have h0 : Quotient.mk _ (Quotient.out (e q)) = Quotient.mk _ (⟨γ q, hγGF q⟩ : GF D n) :=
      Quotient.out_eq (f q)
    exact QuotientGroup.rightRel_apply.mp (Quotient.exact h0)
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hrel
  have hp : ((Quotient.out (e q) : GF D n) : G D n) * (γ q)⁻¹ ∈ (P D n ⊓ GF D n : Subgroup (G D n)) := by
    refine Subgroup.mem_inf.mpr ⟨?_, (GF D n).mul_mem (Quotient.out (e q)).2 ((GF D n).inv_mem (hγGF q))⟩
    have h2 : ((Quotient.out (e q) : GF D n) : G D n) * (γ q)⁻¹ =
        (γ q * ((Quotient.out (e q) : GF D n) : G D n)⁻¹)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
    rw [h2]
    exact (P D n).inv_mem hrel
  have hw' := hPInv D n V ψ χ θ μ ω hS Φ _ hp (γ q)
  simp only [inv_mul_cancel_right] at hw'
  simp only [Function.comp_apply, GlobalTheory.Eis.term, mul_one]
  rw [hw']
  exact (hT2 D n V ψ χ θ μ ω hS Φ _ (hrle q.1) (μr _) (hμr _) (c q.1) (a q.1) (haU q.1) q.2
    (γ q) (hγGF q) (hγmat q)).symm

end GlobalTheory.CompanionTheory.EisCellsAsm

end
