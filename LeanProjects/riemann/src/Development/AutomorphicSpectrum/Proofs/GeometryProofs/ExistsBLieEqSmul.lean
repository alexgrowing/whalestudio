import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapToModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentEvLieOfLieTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlCSurjectiveAndLinearIndependentBLie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieTieOfFrMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.RamifiedEigenLiftsGeneral
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHTFrameCpAndNonempty

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Plug.LowHeightBounds

section Gen

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem exists_bLie_eq_smul (q : O) (hq0 : q ≠ 0) (hcok : ∀ f : omega P.Gt, q • f ∈ LinearMap.range P.al)
    (χ : Λ →+* O) {u : P.V} (hu : u ∈ P.latT) (hspan : u ∈ Submodule.span C (Set.range P.bLie))
    (heig : u ∈ P.eigV χ) :
    ∃ x : LieG P.Gt, AvDefs.IsEig P.Gt P.oGt χ x ∧ P.bLie x = algebraMap O C q • u := by
  haveI := P.isLocalRing
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  obtain ⟨e, h₁, h₂⟩ := exists_param P.G (smoothDim_model P)
  obtain ⟨e', h₃, h₄⟩ := exists_lieEquiv P
  let F := e.trans e'
  have hFadd : ∀ c d, F (c + d) = lieAdd (F c) (F d) := fun c d => Subtype.ext (h₃ _ _ _ (h₁ c d))
  have hFsmul : ∀ (a : O) c, F (a • c) = AvDefs.lieScale P.Gt a (F c) := fun a c =>
    Subtype.ext (h₄ a _ _ (h₂ a c))
  let B : (Fin P.A.g → O) →ₗ[O] P.V :=
    { toFun := fun c => P.bLie (F c)
      map_add' := fun c d => by rw [hFadd, P.bLie_add]
      map_smul' := fun a c => by rw [hFsmul, P.bLie_scale]; rfl }
  have hB : ∀ c, B c = P.bLie (F c) := fun _ => rfl
  let f : Fin P.A.g → omega P.Gt := fun j => ⟨fun x => F.symm x j, fun x y h => by
      have : (⟨x.1 * y.1, h⟩ : LieG P.Gt) = F (F.symm x + F.symm y) := by
        rw [hFadd, F.apply_symm_apply, F.apply_symm_apply]; rfl
      rw [this]; simp only [F.symm_apply_apply, Pi.add_apply], fun a x h => by
      have : (⟨ptMap (dualScale a) ≫ x.1, h⟩ : LieG P.Gt) = F (a • F.symm x) := by
        rw [hFsmul, F.apply_symm_apply]; rfl
      rw [this]; simp only [F.symm_apply_apply, Pi.smul_apply, smul_eq_mul]⟩
  have hf : ∀ j c, (f j).1 (F c) = c j := fun j c => by
    change F.symm (F c) j = c j
    rw [F.symm_apply_apply]
  choose y hy using fun j => hcok (f j)
  have hyF : ∀ j c, P.pairV (B c) (P.inclT (y j)) = algebraMap O C (q * c j) := fun j c => by
    rw [hB, GlobalTheory.FlatModel.BoundProof.pairV_bLie_inclT, hy j, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hf]
  have hBinj : ∀ c c', B c = B c' → c = c' := fun c c' hcc => funext fun j =>
    mul_left_cancel₀ hq0 (P.integers.hom_inj (by rw [← hyF, ← hyF, hcc]))
  have hinj : ∀ x x' : LieG P.Gt, P.bLie x = P.bLie x' → x = x' := fun x x' hxx => by
    rw [← F.apply_symm_apply x, ← F.apply_symm_apply x'] at hxx ⊢
    exact congrArg F (hBinj _ _ hxx)
  let s : Fin P.A.g → P.V := fun i => B fun j => if i = j then 1 else 0
  have hBs : ∀ c, B c = ∑ i, c i • s i := fun c => B.pi_apply_eq_sum_univ c
  have hspan' : u ∈ Submodule.span C (Set.range s) := by
    refine Submodule.span_le.2 ?_ hspan
    rintro _ ⟨x, rfl⟩
    rw [← F.apply_symm_apply x, ← hB, hBs]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← algebraMap_smul C]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 hspan'
  have hint : ∀ j, (algebraMap O C q * a j) ∈ (algebraMap O C).range := fun j => by
    have h := GlobalTheory.FlatModel.BoundProof.pairV_inclT_mem P hu (y j)
    rw [← ha] at h
    convert h using 1
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · rw [hyF]
      simp [mul_comm]
    · intro i _ hij
      rw [hyF]
      simp [hij, Ne.symm hij]
    · simp
  choose b hb using hint
  have hx : P.bLie (F b) = algebraMap O C q • u := by
    rw [← hB, hBs, ← ha, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul C (b i), hb, smul_smul]
  refine ⟨F b, fun c => hinj _ _ ?_, hx⟩
  rw [P.bLie_act, P.bLie_scale, hx, map_smul, mem_eigenSub.1 heig c, RingHom.comp_apply,
    ← algebraMap_smul C (χ c) (algebraMap O C q • u), smul_smul, smul_smul, mul_comm]

end Gen

section Diff

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E))

theorem delta_smul_proj_mem {_ : DecidableEq (E →+* C)} (i : E →+* C) {δ : 𝓞 E}
    (hδ : δ ∈ differentIdeal ℤ (𝓞 E)) {y : P.V} (hy : y ∈ P.latT) :
    i (δ : E) • proj (isSplitting_embO (E := E) P.integers) P.actV i y ∈ P.latT := by
  classical
  let eq := Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))
  have hI : ∀ j, IsIntegral ℤ ((δ : E) * ReciprocityTheory.ChartRestriction.G.TB.trDual (integralBasis E) j) := fun j => by
    have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.dual_int δ hδ (eq j)
    simpa [ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.omDF, eq] using h
  let ω := RingOfIntegers.basis E
  let r : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E := fun j => ⟨_, hI j⟩
  let t : C ⊗[ℤ] 𝓞 E := ∑ j, algebraMap O C (embO P.integers i (r j)) ⊗ₜ ω j
  have ht : t = i (δ : E) • idem (isSplitting_embO (E := E) P.integers) i := by
    apply (isSplitting_embO (E := E) P.integers).1
    rw [map_smul, splitMap_idem]
    ext k
    simp only [t, map_sum, Finset.sum_apply, splitMap_tmul, RingHom.comp_apply, Pi.smul_apply, smul_eq_mul,
      algebraMap_embO]
    have h := _root_.idempotent_evaluation E C _ (integralBasis E) k i
    have h2 : ∑ j, i (ReciprocityTheory.ChartRestriction.G.TB.trDual (integralBasis E) j) * k (integralBasis E j) =
        ReciprocityTheory.ChartRestriction.G.TB.evAt i (ReciprocityTheory.ChartRestriction.G.TB.idemOf (integralBasis E) k) := by
      simp only [ReciprocityTheory.ChartRestriction.G.TB.idemOf, ReciprocityTheory.ChartRestriction.G.TB.evAt, map_sum,
        Algebra.TensorProduct.productMap_apply_tmul, map_mul]
      rfl
    have h3 : ∑ j, i ((r j : 𝓞 E) : E) * k ((ω j : 𝓞 E) : E) =
        i (δ : E) * ReciprocityTheory.ChartRestriction.G.TB.evAt i (ReciprocityTheory.ChartRestriction.G.TB.idemOf (integralBasis E) k) := by
      rw [← h2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e1 : ((r j : 𝓞 E) : E) = (δ : E) * ReciprocityTheory.ChartRestriction.G.TB.trDual (integralBasis E) j := rfl
      have e2 : integralBasis E j = ((ω j : 𝓞 E) : E) := integralBasis_apply E j
      rw [e1, e2, map_mul, _root_.mul_assoc]
    refine h3.trans ?_
    rw [h]
    by_cases hik : i = k
    · subst hik; simp
    · simp [hik, Ne.symm hik]
  have e2 : i (δ : E) • proj (isSplitting_embO (E := E) P.integers) P.actV i y =
      tensorAction P.actV t y := by
    rw [ht, map_smul, proj, LinearMap.smul_apply]
  rw [e2]
  simp only [t, map_sum, LinearMap.sum_apply, tensorAction_tmul]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [algebraMap_smul]
  exact Submodule.smul_mem _ _ (GlobalTheory.FlatModel.BoundProof.actV_mem_latT P _ hy)

end Diff

section Lin

variable {O C U : Type} [CommRing O] [Field C] [Algebra O C] [AddCommGroup U] [Module C U] [Module O U]
  [IsScalarTower O C U] {n : ℕ}

theorem inv_diag_mem (La : Submodule O U) (b : Fin n → U) (g : Matrix (Fin n) (Fin n) C)
    (hg : ∀ i j, i < j → g i j = 0) (hb : IsLatBasis C La fun i => ∑ j, g i j • b j) (hmem : ∀ j, b j ∈ La)
    (i : Fin n) : g i i ≠ 0 ∧ (g i i)⁻¹ ∈ (algebraMap O C).range := by
  have hl : LinearIndependent C g.row := LinearIndependent.of_comp (Fintype.linearCombination C b) hb.1
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hl)
  letI : Invertible g := Matrix.invertibleOfIsUnitDet g hu
  have ht : g.BlockTriangular OrderDual.toDual := fun a b hab => hg a b hab
  have hinv : g⁻¹.BlockTriangular OrderDual.toDual := Matrix.blockTriangular_inv_of_blockTriangular ht
  have hgi : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hu
  have hbj : ∀ j, ∑ i, g⁻¹ j i • ∑ k, g i k • b k = b j := fun j => by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have e : ∀ k, ∑ i, g⁻¹ j i * g i k = (1 : Matrix (Fin n) (Fin n) C) j k := fun k => by
      rw [← Matrix.mul_apply, hgi]
    simp_rw [e]
    simp [Matrix.one_apply]
  have hI : ∀ j i, g⁻¹ j i ∈ (algebraMap O C).range := fun j =>
    (hb.sum_mem_iff (g⁻¹ j)).1 (by rw [hbj j]; exact hmem j)
  have hd : g⁻¹ i i * g i i = 1 := by
    have h1 := congrFun (congrFun hgi i) i
    rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at h1
    · exact h1
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hg k i h, mul_zero]
      · rw [hinv (OrderDual.toDual_lt_toDual.2 h), zero_mul]
    · simp
  have h0 : g i i ≠ 0 := fun h => by rw [h, mul_zero] at hd; exact zero_ne_one hd
  exact ⟨h0, by rw [← eq_inv_of_mul_eq_one_left hd]; exact hI i i⟩

end Lin

section Wt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem sum_abs_exOf_le (u : GlobalTheory.AllWt.Weight Dw) :
    ∑ s : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), |((exOf Dw u 0 (some s) : ℤ) : ℝ)| ≤ GlobalTheory.CovHt.l1 u := by
  classical
  have hm1 : ∀ {τ : E →+* ℂ}, τ (H.rt : E) = H.rt0 → Dw.mult τ = Dw.p := fun h => if_pos h
  have hm2 : ∀ {τ : E →+* ℂ}, ¬ τ (H.rt : E) = H.rt0 → Dw.mult τ = Dw.q := fun h => if_neg h
  let φ : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Psi H × Fin (Dw.p + Dw.q) := fun s =>
    if h : s.1 (H.rt : E) = H.rt0 then
      (⟨s.1, h⟩, ⟨s.2, by have := lt_of_lt_of_eq s.2.2 (hm1 h); omega⟩)
    else (⟨conjEmb s.1, conj_mem h⟩, ⟨Dw.p + (Dw.q - 1 - s.2), by have := lt_of_lt_of_eq s.2.2 (hm2 h); omega⟩)
  have hφ : ∀ s, |((exOf Dw u 0 (some s) : ℤ) : ℝ)| = |((u (φ s).1 (φ s).2 : ℤ) : ℝ)| := by
    rintro ⟨τ, i⟩
    by_cases h : τ (H.rt : E) = H.rt0
    · have hi := lt_of_lt_of_eq i.2 (hm1 h)
      have e : exOf Dw u 0 (some ⟨τ, i⟩) = (wtOf Dw u 0).1 (τ, i) := rfl
      rw [e, wtOf_big u 0 ⟨τ, h⟩ i hi]
      simp [φ, h]
    · have hi := lt_of_lt_of_eq i.2 (hm2 h)
      have e : exOf Dw u 0 (some ⟨τ, i⟩) = (wtOf Dw u 0).1 (τ, i) := rfl
      have key := wtOf_small u 0 ⟨conjEmb τ, conj_mem h⟩ i hi
      simp only [conjEmb_conjEmb] at key
      rw [e, key]
      simp [φ, h, abs_neg]
  have hinj : Function.Injective φ := by
    rintro ⟨τ, i⟩ ⟨τ', i'⟩ e
    by_cases h : τ (H.rt : E) = H.rt0 <;> by_cases h' : τ' (H.rt : E) = H.rt0
    · simp only [φ, dif_pos h, dif_pos h'] at e
      have e1 : τ = τ' := congrArg (fun x : Psi H × Fin (Dw.p + Dw.q) => x.1.1) e
      subst e1
      have e2 : (i : ℕ) = i' := congrArg (fun x : Psi H × Fin (Dw.p + Dw.q) => (x.2 : ℕ)) e
      exact congrArg (Sigma.mk τ) (Fin.ext e2)
    · simp only [φ, dif_pos h, dif_neg h'] at e
      have e2 : (i : ℕ) = Dw.p + (Dw.q - 1 - i') := congrArg (fun x : Psi H × Fin (Dw.p + Dw.q) => (x.2 : ℕ)) e
      have hi := lt_of_lt_of_eq i.2 (hm1 h)
      omega
    · simp only [φ, dif_neg h, dif_pos h'] at e
      have e2 : Dw.p + (Dw.q - 1 - i) = (i' : ℕ) := congrArg (fun x : Psi H × Fin (Dw.p + Dw.q) => (x.2 : ℕ)) e
      have hi' := lt_of_lt_of_eq i'.2 (hm1 h')
      omega
    · simp only [φ, dif_neg h, dif_neg h'] at e
      have e1 : conjEmb τ = conjEmb τ' := congrArg (fun x : Psi H × Fin (Dw.p + Dw.q) => x.1.1) e
      have e3 : τ = τ' := by rw [← conjEmb_conjEmb τ, e1, conjEmb_conjEmb]
      subst e3
      have e2 : Dw.p + (Dw.q - 1 - i) = Dw.p + (Dw.q - 1 - i') :=
        congrArg (fun x : Psi H × Fin (Dw.p + Dw.q) => (x.2 : ℕ)) e
      have hi := lt_of_lt_of_eq i.2 (hm2 h)
      have hi' := lt_of_lt_of_eq i'.2 (hm2 h)
      exact congrArg (Sigma.mk τ) (Fin.ext (by omega))
  calc ∑ s : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), |((exOf Dw u 0 (some s) : ℤ) : ℝ)|
      = ∑ s : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), |((u (φ s).1 (φ s).2 : ℤ) : ℝ)| := Finset.sum_congr rfl fun s _ => hφ s
    _ = ∑ x ∈ Finset.univ.image φ, |((u x.1 x.2 : ℤ) : ℝ)| :=
        (Finset.sum_image (f := fun x : Psi H × Fin (Dw.p + Dw.q) => |((u x.1 x.2 : ℤ) : ℝ)|) fun a _ b _ h => hinj h).symm
    _ ≤ ∑ x : Psi H × Fin (Dw.p + Dw.q), |((u x.1 x.2 : ℤ) : ℝ)| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _
    _ = GlobalTheory.CovHt.l1 u := by rw [GlobalTheory.CovHt.l1, Fintype.sum_prod_type]

end Wt

section Coef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  [Algebra c.F C] [StarRing (𝓞 E)]

theorem cok_of_htChar (P : Point p v O (𝓞 E)) (h : HTChar p v P.Gt) (κ : O)
    (hκ : v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C)) (f : omega P.Gt) : κ • f ∈ LinearMap.range P.al := by
  have h2 := h κ hκ f.1 f.2
  rw [← (weilChar_surjective_and_map_range_al p C v O (𝓞 E) P).2] at h2
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := h2
  exact ⟨t, Subtype.ext ht⟩

theorem coef_mem {T : CDVR} {io : c.F →+* T.Fr} (y₀ : IntFr Xo c T io) (hy : y₀.IsAlg)
    (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E))
    (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C)
    (hP : letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) (hz : letI := io.toAlgebra; FrMap k y₀.1 z)
    (τ : E →+* ℂ) (x : Fin (Dw.mult τ) → LieG P.Gt) (hx : ∀ j, LieTie P ψ (x j) (z.u τ j))
    (κ d : O) (hκ0 : κ ≠ 0) (hκ : v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C))
    (hd : ∀ w ∈ htLat c P τ, algebraMap O C d • w ∈ P.latT) (a : Fin (Dw.mult τ) → C)
    (ha : ∑ j, a j • P.bLie (x j) ∈ htLat c P τ) (j : Fin (Dw.mult τ)) :
    algebraMap O C κ * algebraMap O C d * a j ∈ (algebraMap O C).range := by
  letI := io.toAlgebra
  have hht : HTChar p v P.Gt := htChar_of_pointOver E H Dw l Xo c p C v O T io y₀ hy k.toRingHom kO P ψ hP
  have hli := (alC_surjective_and_linearIndependent_bLie p C v O (𝓞 E) P hht).2 _ _
    (linearIndependent_evLie_of_lieTie E H Dw l Xo c p C v O T io y₀ k kO P ψ z hP hz τ x hx)
  have hsp := RecSpan.span_bLie_eq_wRec E H Dw l Xo c p C v O T io y₀ k kO P ψ z hP hz τ x hx
  have heig1 : ∀ j, P.bLie (x j) ∈ P.eigV (embInt c P.integers τ) := fun j =>
    bLie_mem_eigV ((hx j).isEig hP (z.eig τ j))
  have hspan : algebraMap O C d • ∑ j, a j • P.bLie (x j) ∈ Submodule.span C (Set.range P.bLie) :=
    Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  have heig : algebraMap O C d • ∑ j, a j • P.bLie (x j) ∈ P.eigV (embInt c P.integers τ) :=
    Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (heig1 j))
  obtain ⟨x', hx', hb⟩ := exists_bLie_eq_smul P κ hκ0 (cok_of_htChar P hht κ hκ) (embInt c P.integers τ)
    (hd _ ha) hspan heig
  have hmem : P.bLie x' ∈ Submodule.span O (Set.range fun j => P.bLie (x j)) := by
    rw [hsp]
    exact ⟨⟨x', hx'⟩, rfl⟩
  obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hmem
  have hcc' : ∑ j, algebraMap O C (cc j) • P.bLie (x j) = P.bLie x' := by
    rw [← hcc]
    exact Finset.sum_congr rfl fun j _ => algebraMap_smul C _ _
  have hrel : ∑ j, (algebraMap O C (cc j) - algebraMap O C κ * algebraMap O C d * a j) • P.bLie (x j) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [hcc', hb, sub_eq_zero, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, smul_smul, _root_.mul_assoc]
  have h0 := Fintype.linearIndependent_iff.1 hli _ hrel j
  exact ⟨cc j, sub_eq_zero.1 h0⟩

theorem exists_diag {T : CDVR} {io : c.F →+* T.Fr} (y₀ : IntFr Xo c T io) (hy : y₀.IsAlg)
    (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E))
    (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C)
    (hP : letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) (hz : letI := io.toAlgebra; FrMap k y₀.1 z)
    {w : FrPt Xo c C} (h : IsHTChange P ψ z w) (κ : O) (hκ0 : κ ≠ 0)
    (hκ : v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C)) (d : (E →+* ℂ) → O)
    (hd : ∀ τ, ∀ w ∈ htLat c P τ, algebraMap O C (d τ) • w ∈ P.latT) :
    ∃ t : Ix Dw → Cˣ, FrBor t z w ∧ v (t none : C) = 1 ∧ ∀ s : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)),
      1 ≤ v (t (some s) : C) ∧ v (algebraMap O C κ) * v (algebraMap O C (d s.1)) * v (t (some s) : C) ≤ 1 := by
  classical
  letI := io.toAlgebra
  obtain ⟨g, a, x, ⟨h1, h2, pm, h3, h4, h5⟩, hg, ha, hx, hb⟩ := h
  have hmem : ∀ τ j, P.bLie (x τ j) ∈ htLat c P τ := fun τ j =>
    wRec_le_htLat P τ ⟨⟨x τ j, (hx τ j).isEig hP (z.eig τ j)⟩, rfl⟩
  have hdiag := fun τ i => inv_diag_mem (htLat c P τ) (fun j => P.bLie (x τ j)) (g τ) (hg τ) (hb τ) (hmem τ) i
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  refine ⟨fun i => Option.rec (Units.mk0 a ha0) (fun s => Units.mk0 _ (hdiag s.1 s.2).1) i,
    ⟨h1, fun τ i => ⟨g τ i, rfl, hg τ i, h2 τ i⟩, pm, h3, ?_, h5⟩, ha, fun s => ⟨?_, ?_⟩⟩
  · rw [h4, show spMap (RingHom.id C) = 𝟙 _ from Spec.map_id _]
    exact Category.comp_id _
  · change 1 ≤ v (g s.1 s.2 s.2)
    obtain ⟨r, hr⟩ := (hdiag s.1 s.2).2
    have h6 := P.integers.map_le_one r
    rw [hr, map_inv₀] at h6
    exact (inv_le_one₀ (pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 (hdiag s.1 s.2).1))).1 h6
  · change v (algebraMap O C κ) * v (algebraMap O C (d s.1)) * v (g s.1 s.2 s.2) ≤ 1
    obtain ⟨r, hr⟩ := coef_mem y₀ hy k kO P ψ z hP hz s.1 (x s.1) (hx s.1) κ (d s.1) hκ0 hκ (hd s.1) (g s.1 s.2)
      ((hb s.1).2.le (Submodule.subset_span ⟨s.2, rfl⟩)).1 s.2
    have h6 := P.integers.map_le_one r
    rw [hr, map_mul, map_mul] at h6
    exact h6

theorem exists_diff [IsGalois ℚ E] {T : CDVR} {io : c.F →+* T.Fr} {la : HeightOneSpectrum (𝓞 c.F)} {e : ℕ}
    (ho : OverLa la T.V io e) (hpl : (p : 𝓞 c.F) ∈ la.asIdeal) (hv : v.Integers O) (k : T.Fr →+* C)
    (kO : T.V →+* O) (hk : ∀ a, algebraMap O C (kO a) = k (algebraMap T.V T.Fr a))
    (hkc : ∀ x, k (io x) = algebraMap c.F C x) (τ : E →+* ℂ) :
    ∃ δ ∈ differentIdeal ℤ (𝓞 E), δ ≠ 0 ∧ Real.log (v (embAt c C τ (δ : E))) * (Module.finrank ℚ E : ℝ) =
      (padicValNat p (discr E).natAbs : ℝ) * Real.log (v (p : C)) := by
  have hp : p.Prime := Fact.out
  have hn : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  let ψ : E →+* T.Fr := io.comp (embF c τ)
  have hψp : ψ (p : E) = io (p : c.F) := by simp [ψ]
  have hpos : 0 < vV T.V (ψ (p : E)) := by
    rw [hψp, ho.2]
    exact mul_pos (by exact_mod_cast ho.1) (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.vLa_pos la p hp.ne_zero hpl)
  have hdisc : (discr E).natAbs = p ^ padicValNat p (discr E).natAbs * ((discr E).natAbs / p ^ (discr E).natAbs.factorization p) := by
    rw [← Nat.factorization_def _ hp]
    exact (Nat.ordProj_mul_ordCompl_eq_self _ p).symm
  obtain ⟨δ, hδ, h0, hval⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.exists_delta_val (V := T.V) p _ _ hp
    (Nat.not_dvd_ordCompl hp hn) hdisc ψ ψ.injective hpos
  refine ⟨δ, hδ, h0, ?_⟩
  obtain ⟨r, hr⟩ := exists_log_eq hv k kO hk
  have hδ0 : ψ (δ : E) ≠ 0 := (map_ne_zero ψ).2 (by exact_mod_cast h0)
  have hp0 : ψ (p : E) ≠ 0 := (map_ne_zero ψ).2 (Nat.cast_ne_zero.2 hp.ne_zero)
  have e1 := hr _ hδ0
  have e2 := hr _ hp0
  have k1 : k (ψ (δ : E)) = embAt c C τ (δ : E) := hkc _
  have k2 : k (ψ (p : E)) = (p : C) := by simp
  rw [k1] at e1
  rw [k2] at e2
  have hval' : (vV T.V (ψ (δ : E)) : ℝ) * (Module.finrank ℚ E : ℝ) =
      (padicValNat p (discr E).natAbs : ℝ) * (vV T.V (ψ (p : E)) : ℝ) := by
    have h9 := congrArg (Int.cast : ℤ → ℝ) hval
    simp only [Int.cast_mul, Int.cast_natCast] at h9
    exact h9
  rw [e1, e2]
  linear_combination r * hval'

end Coef

section Bound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  [Algebra c.F C] [StarRing (𝓞 E)]

theorem exists_bound [IsGalois ℚ E] {T : CDVR} {io : c.F →+* T.Fr} {la : HeightOneSpectrum (𝓞 c.F)} {e : ℕ}
    (ho : OverLa la T.V io e) (hpl : (p : 𝓞 c.F) ∈ la.asIdeal) (y₀ : IntFr Xo c T io) (hy : y₀.IsAlg)
    (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E))
    (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C)
    (hP : letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) (hz : letI := io.toAlgebra; FrMap k y₀.1 z)
    {w : FrPt Xo c C} (h : IsHTChange P ψ z w) :
    ∃ t : Ix Dw → Cˣ, FrBor t z w ∧ v (t none : C) = 1 ∧ ∀ s : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)),
      |Real.log (v (t (some s) : C)) / Real.log (v (p : C))| ≤ exTwo E p := by
  classical
  letI := io.toAlgebra
  have hp : p.Prime := Fact.out
  have hv1 : v (p : C) < 1 := lt_one_of_not_isUnit P.integers Fact.out
  have hpC : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hvp0 : 0 < v (p : C) := pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 hpC)
  have hl : Real.log (v (p : C)) < 0 :=
    Real.log_neg (by exact_mod_cast hvp0) (by exact_mod_cast hv1)
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  obtain ⟨κ₀, hκ₀⟩ := IsAlgClosed.exists_pow_nat_eq (p : C) (Nat.pos_of_ne_zero hp1)
  have hvκ : v κ₀ ^ (p - 1) = v (p : C) := by rw [← map_pow, hκ₀]
  have hκ1 : v κ₀ ≤ 1 := by
    by_contra hn
    have := one_le_pow₀ (n := p - 1) (not_le.1 hn).le
    rw [hvκ] at this
    exact absurd hv1 (not_lt.2 this)
  obtain ⟨κ, rfl⟩ := P.integers.exists_of_le_one hκ1
  have hκC : algebraMap O C κ ≠ 0 := fun h0 => hpC (by rw [← hκ₀, h0, zero_pow hp1])
  have hκ0 : κ ≠ 0 := fun h0 => hκC (by rw [h0, map_zero])
  choose δ hδ hδ0 hδv using fun τ : E →+* ℂ => exists_diff (c := c) ho hpl P.integers k.toRingHom kO hP.1
    (fun x => k.commutes x) τ
  have hd : ∀ τ, ∀ w ∈ htLat c P τ, algebraMap O C (embO P.integers (embAt c C τ) (δ τ)) • w ∈ P.latT := by
    intro τ w hw
    rw [algebraMap_embO]
    unfold htLat at hw
    split_ifs at hw with hc
    · obtain ⟨y', hy', rfl⟩ := hw
      exact delta_smul_proj_mem P _ (hδ τ) hy'
    · have h1 : ((embAt c C τ) ((δ τ : 𝓞 E) : E)) = algebraMap O C (embO P.integers (embAt c C τ) (δ τ)) :=
        (algebraMap_embO P.integers _ _).symm
      rw [h1, algebraMap_smul]
      exact Submodule.smul_mem _ _ hw.1
  obtain ⟨t, hb, h1, h2⟩ := exists_diag y₀ hy k kO P ψ z hP hz h κ hκ0 hvκ.le _ hd
  refine ⟨t, hb, h1, fun s => ?_⟩
  obtain ⟨h3, h4⟩ := h2 s
  rw [algebraMap_embO] at h4
  have hδC : embAt c C s.1 ((δ s.1 : 𝓞 E) : E) ≠ 0 :=
    (map_ne_zero _).2 (by exact_mod_cast hδ0 s.1)
  have hpκ : (0 : ℝ) < v (algebraMap O C κ) := by
    exact_mod_cast pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 hκC)
  have hpd : (0 : ℝ) < v (embAt c C s.1 ((δ s.1 : 𝓞 E) : E)) := by
    exact_mod_cast pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 hδC)
  have hpt : (1 : ℝ) ≤ v (t (some s) : C) := by exact_mod_cast h3
  have hG : 0 ≤ Real.log (v (t (some s) : C)) := Real.log_nonneg hpt
  have h5 : Real.log (v (algebraMap O C κ)) + Real.log (v (embAt c C s.1 ((δ s.1 : 𝓞 E) : E))) +
      Real.log (v (t (some s) : C)) ≤ 0 := by
    have h6 : ((v (algebraMap O C κ) : ℝ)) * v (embAt c C s.1 ((δ s.1 : 𝓞 E) : E)) * v (t (some s) : C) ≤ 1 := by
      exact_mod_cast h4
    have h7 := Real.log_nonpos (by positivity) h6
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)] at h7
  have hK : Real.log (v (algebraMap O C κ)) * ((p : ℝ) - 1) = Real.log (v (p : C)) := by
    have h6 := congrArg (fun r : ℝ≥0 => Real.log (r : ℝ)) hvκ
    simp only [NNReal.coe_pow, Real.log_pow] at h6
    rw [← h6, Nat.cast_sub hp.one_le, Nat.cast_one]
    ring
  have hD := hδv s.1
  have hp2 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have hn : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := by exact_mod_cast Module.finrank_pos
  set ℓ := Real.log (v (p : C))
  set K := Real.log (v (algebraMap O C κ))
  set D := Real.log (v (embAt c C s.1 ((δ s.1 : 𝓞 E) : E)))
  set G := Real.log (v (t (some s) : C))
  set a : ℝ := (padicValNat p (discr E).natAbs : ℝ)
  set n : ℝ := (Module.finrank ℚ E : ℝ)
  have ha0 : 0 ≤ a := Nat.cast_nonneg _
  have hKe : K = ℓ * (1 / ((p : ℝ) - 1)) := by field_simp; linarith
  have hDe : D = ℓ * (a / n) := by field_simp; linarith
  have hex : 1 / ((p : ℝ) - 1) + a / n ≤ exTwo E p := by
    have h8 : 0 ≤ a / n := div_nonneg ha0 hn.le
    have h9 : (0 : ℝ) ≤ if p = 2 then 1 else 0 := by split_ifs <;> norm_num
    simp only [exTwo, GlobalTheory.CovHt.htEx]
    linarith
  rw [abs_div, abs_of_nonneg hG, abs_of_neg hl, div_le_iff₀ (neg_pos.2 hl)]
  have h10 : G ≤ (1 / ((p : ℝ) - 1) + a / n) * (-ℓ) := by
    rw [hKe, hDe] at h5
    nlinarith
  exact h10.trans (mul_le_mul_of_nonneg_right hex (neg_pos.2 hl).le)

end Bound

section Main

attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

theorem prime_unique {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (h1 : (p : 𝓞 K) ∈ la.asIdeal) (h2 : (q : 𝓞 K) ∈ la.asIdeal) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ : IsCoprime (p : 𝓞 K) (q : 𝓞 K) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem log_prod_zpow {A C : Type} [Fintype A] [Field C] (v : Valuation C ℝ≥0) (t : A → Cˣ) (e : A → ℤ) :
    Real.log (v ((∏ i, t i ^ e i : Cˣ) : C)) = ∑ i, (e i : ℝ) * Real.log (v (t i : C)) := by
  have h0 : ∀ i, (0 : ℝ) < v (t i : C) := fun i => by
    exact_mod_cast pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 (t i).ne_zero)
  rw [Units.coe_prod, map_prod, NNReal.coe_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, NNReal.coe_zpow, Real.log_zpow]
  · intro i _
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, NNReal.coe_zpow]
    exact (zpow_pos (h0 i) _).ne'

theorem htLow_all (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) :
    HTLow Xo c := by
  intro q la hq hql w hw
  obtain ⟨p, hp, _, T, io, e, y₀, k, y, ho, hAlg, hy, rfl⟩ := hw
  obtain rfl : p = q := prime_unique hp.out hq (hy.mem ho) hql
  letI := H.starRing
  letI := io.toAlgebra
  have hy' : IsHTFrame p (Valued.v : Valuation ℂ_[p] ℝ≥0) 𝓞_ℂ_[p] y₀ k y := hy
  have hm := hy'.val_vw_map ho
  obtain ⟨-, kO, P, ψ, z, hPO, hz, hch⟩ := hy'
  obtain ⟨t, hb, h1, h2⟩ := exists_bound ho hql y₀ hAlg k kO P ψ z hPO hz hch
  refine ⟨vAtV (PtV.mk (cls := algCls Xo c) (lies := fun _ _ _ _ => True) la ho y₀ hAlg () trivial), ⟨_, rfl⟩,
    fun u f hf => ?_⟩
  have hS : Out.SecBaseChangeSt := GlobalTheory.allSixLaws.1.secBaseChange
  have hA := GlobalTheory.evR_frBor_of_mem_secZ hS Xo c _ hf ℂ_[p] t z y hb
  have hB : evR Xo c f z = k (evI y₀ f) := GlobalTheory.FlagTan.evR_frMap hf.1 hz
  show nval T.V e (evI y₀ f) ≤ val_vw la p (Valued.v : Valuation ℂ_[p] ℝ≥0) (evR Xo c f y) +
    (((vLa la (p : c.F) : ℝ) * exTwo E p * GlobalTheory.CovHt.l1 u : ℝ) : EReal)
  rw [hA, hB, val_vw_mul, hm, val_vw_of_ne la p _ (Units.ne_zero _), log_prod_zpow]
  have hex0 : 0 ≤ exTwo E p := by
    have h3 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
      exact div_nonneg zero_le_one (by linarith)
    have h4 : (0 : ℝ) ≤ (padicValNat p (discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h5 : (0 : ℝ) ≤ if p = 2 then 1 else 0 := by split_ifs <;> norm_num
    simp only [exTwo, GlobalTheory.CovHt.htEx]
    linarith
  set ℓ := Real.log (Valued.v (p : ℂ_[p]) : ℝ≥0)
  set R : ℝ := ∑ s : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), ((exOf Dw u 0 (some s) : ℤ) : ℝ) *
    (Real.log (Valued.v ((t (some s) : ℂ_[p]ˣ) : ℂ_[p]) : ℝ≥0) / ℓ) with hRdef
  have hR : (∑ i, ((exOf Dw u 0 i : ℤ) : ℝ) * Real.log (Valued.v ((t i : ℂ_[p]ˣ) : ℂ_[p]) : ℝ≥0)) / ℓ = R := by
    rw [Fintype.sum_option, h1, NNReal.coe_one, Real.log_one, mul_zero, zero_add, Finset.sum_div, hRdef]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hRb : -(exTwo E p * GlobalTheory.CovHt.l1 u) ≤ R := by
    refine neg_le_of_abs_le ((Finset.abs_sum_le_sum_abs _ _).trans ?_)
    calc ∑ s : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), |((exOf Dw u 0 (some s) : ℤ) : ℝ) *
          (Real.log (Valued.v ((t (some s) : ℂ_[p]ˣ) : ℂ_[p]) : ℝ≥0) / ℓ)|
        ≤ ∑ s : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), |((exOf Dw u 0 (some s) : ℤ) : ℝ)| * exTwo E p :=
          Finset.sum_le_sum fun s _ => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (h2 s) (abs_nonneg _)
      _ = (∑ s : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), |((exOf Dw u 0 (some s) : ℤ) : ℝ)|) * exTwo E p :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ GlobalTheory.CovHt.l1 u * exTwo E p := mul_le_mul_of_nonneg_right (sum_abs_exOf_le u) hex0
      _ = exTwo E p * GlobalTheory.CovHt.l1 u := mul_comm _ _
  have hvl : (0 : ℝ) ≤ (vLa la (p : c.F) : ℝ) := by
    exact_mod_cast (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.vLa_pos la p hp.out.ne_zero hql).le
  rw [hR]
  have hc : 0 ≤ (vLa la (p : c.F) : ℝ) * R + (vLa la (p : c.F) : ℝ) * exTwo E p * GlobalTheory.CovHt.l1 u := by
    have := mul_le_mul_of_nonneg_left hRb hvl
    nlinarith
  have hXb := nval_ne_bot (V := T.V) e (evI y₀ f)
  generalize nval T.V e (evI y₀ f) = X at hXb ⊢
  rcases eq_or_ne X ⊤ with hT | hT
  · subst hT
    rw [EReal.coe_add_top, EReal.top_add_coe]
  · lift X to ℝ using ⟨hT, hXb⟩
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith

end Main

end GlobalTheory.CompanionTheory.Ar.Plug.LowHeightBounds
