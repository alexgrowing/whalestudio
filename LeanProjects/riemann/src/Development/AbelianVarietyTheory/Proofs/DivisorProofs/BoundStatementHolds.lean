import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel.BoundProof

section Gen

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem actV_mem_latT (a : Λ) {y : P.V} (hy : y ∈ P.latT) : P.actV a y ∈ P.latT :=
  (P.mem_latT_iff _).2 fun t => by
    obtain ⟨c, hc⟩ := (P.mem_latT_iff y).1 hy (P.actT (star a) t)
    exact ⟨c, by rw [hc, P.pairV_act]; rfl⟩

theorem pairV_inclT_mem {u : P.V} (hu : u ∈ P.latT) (y : O ⊗[ℤ_[p]] P.T) :
    P.pairV u (P.inclT y) ∈ (algebraMap O C).range := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add, map_add, map_add, ha, hb]⟩
  | tmul c t =>
    obtain ⟨b, hb⟩ := (P.mem_latT_iff u).1 hu t
    refine ⟨c * b, ?_⟩
    have e : (algebraMap O C c ⊗ₜ[ℤ_[p]] t : P.V) = algebraMap O C c • ((1 : C) ⊗ₜ[ℤ_[p]] t) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [P.inclT_tmul, e, map_smul, smul_eq_mul, map_mul, hb]

end Gen

section Gen2

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem pairV_bLie_inclT (x : LieG P.Gt) (y : O ⊗[ℤ_[p]] P.T) :
    P.pairV (P.bLie x) (P.inclT y) = algebraMap O C ((P.al y).1 x) := by
  rw [pairV_bLie_eq_evLie, P.alC_inclT, Point.inclOm, TensorProduct.mk_apply, evLie,
    LinearMap.liftBaseChange_tmul, one_smul]
  rfl

theorem exists_bLie_eq_sq_smul (hcok : ∀ f : omega P.Gt, (p : O) ^ 2 • f ∈ LinearMap.range P.al)
    (χ : Λ →+* O) {u : P.V} (hu : u ∈ P.latT) (hspan : u ∈ Submodule.span C (Set.range P.bLie))
    (heig : u ∈ P.eigV χ) :
    ∃ x : LieG P.Gt, AvDefs.IsEig P.Gt P.oGt χ x ∧ P.bLie x = ((p : C) ^ 2) • u := by
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
  have hyF : ∀ j c, P.pairV (B c) (P.inclT (y j)) = algebraMap O C ((p : O) ^ 2 * c j) := fun j c => by
    rw [hB, pairV_bLie_inclT, hy j, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hf]
  have hp0 : ((p : O) ^ 2) ≠ 0 := pow_ne_zero _ fun h0 => (Nat.cast_ne_zero (R := C)).2
    (Fact.out : p.Prime).ne_zero (by rw [← map_natCast (algebraMap O C), h0, map_zero])
  have hBinj : ∀ c c', B c = B c' → c = c' := fun c c' hcc => funext fun j =>
    mul_left_cancel₀ hp0 (P.integers.hom_inj (by rw [← hyF, ← hyF, hcc]))
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
  have hint : ∀ j, ((p : C) ^ 2 * a j) ∈ (algebraMap O C).range := fun j => by
    have h := pairV_inclT_mem P hu (y j)
    rw [← ha] at h
    convert h using 1
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · rw [hyF]
      simp [map_pow, map_natCast, mul_comm]
    · intro i _ hij
      rw [hyF]
      simp [hij, Ne.symm hij]
    · simp
  choose b hb using hint
  have hx : P.bLie (F b) = ((p : C) ^ 2) • u := by
    rw [← hB, hBs, ← ha, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul C (b i), hb, smul_smul]
  refine ⟨F b, fun c => hinj _ _ ?_, hx⟩
  rw [P.bLie_act, P.bLie_scale, hx, map_smul, mem_eigenSub.1 heig c, RingHom.comp_apply,
    ← algebraMap_smul C (χ c) ((p : C) ^ 2 • u), smul_smul, smul_smul, mul_comm]

end Gen2

section Discr

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E))

theorem discr_smul_proj_mem {_ : DecidableEq (E →+* C)} (i : E →+* C) {y : P.V} (hy : y ∈ P.latT) :
    ((discr E : ℤ) : C) • proj (isSplitting_embO (E := E) P.integers) P.actV i y ∈ P.latT := by
  classical
  have hc : Fintype.card (E →+* C) = Module.finrank ℚ E := NumberField.Embeddings.card E C
  obtain ⟨b⟩ := nonempty_basis (E := E) hc
  let M : Matrix (E →+* C) (E →+* C) O := Matrix.of fun k j => embO P.integers k (b j)
  have hM : M.map (algebraMap O C) = Matrix.of fun k j => k (b j) := by
    ext k j
    simp [M, algebraMap_embO]
  have hd : algebraMap O C M.det ^ 2 = ((discr E : ℤ) : C) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
    exact det_sq_eq_discr_of_field (φ := fun φ : E →+* C => φ) (fun _ _ h => h) b
  let o : (E →+* C) → O := fun j => M.det * M.adjugate j i
  let t : C ⊗[ℤ] 𝓞 E := ∑ j, algebraMap O C (o j) ⊗ₜ b j
  have ht : t = ((discr E : ℤ) : C) • idem (isSplitting_embO (E := E) P.integers) i := by
    apply (isSplitting_embO (E := E) P.integers).1
    rw [map_smul, splitMap_idem]
    ext k
    simp only [t, map_sum, Finset.sum_apply, splitMap_tmul, RingHom.comp_apply, Pi.smul_apply, smul_eq_mul]
    have e1 : ∑ j, algebraMap O C (o j) * algebraMap O C (embO P.integers k (b j)) =
        algebraMap O C (M.det * (M * M.adjugate) k i) := by
      rw [Matrix.mul_apply, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [o, M, Matrix.of_apply, map_mul]
      ring
    rw [e1, Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply, ← hd]
    by_cases hki : k = i
    · subst hki; simp [sq]
    · simp [hki]
  have e2 : ((discr E : ℤ) : C) • proj (isSplitting_embO (E := E) P.integers) P.actV i y =
      tensorAction P.actV t y := by
    rw [ht, map_smul, proj, LinearMap.smul_apply]
  rw [e2]
  simp only [t, map_sum, LinearMap.sum_apply, tensorAction_tmul]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [algebraMap_smul]
  exact Submodule.smul_mem _ _ (actV_mem_latT P _ hy)

end Discr

theorem discr_smul_mem_latT {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) {p : ℕ} [Fact p.Prime] [Algebra c.F ℂ_[p]] [StarRing (𝓞 E)] (P : PtP E p)
    (σ : E →+* ℂ) {w : P.V} (hw : w ∈ htLat c P σ) : ((discr E : ℤ) : ℂ_[p]) • w ∈ P.latT := by
  unfold htLat at hw
  split_ifs at hw with h
  · obtain ⟨y, hy, rfl⟩ := hw
    exact discr_smul_proj_mem P _ hy
  · rw [Int.cast_smul_eq_zsmul]
    exact zsmul_mem hw.1 _

end GlobalTheory.FlatModel.BoundProof

namespace GlobalTheory.FlatModel

theorem boundSt : BoundSt := by
  intro E _ _ _ H l c p _ _ _ P hcok σ w hw hspan heig
  obtain ⟨x, hx, hbx⟩ := BoundProof.exists_bLie_eq_sq_smul P hcok (embInt c P.integers σ)
    (BoundProof.discr_smul_mem_latT c P σ hw) (Submodule.smul_mem _ _ hspan) (Submodule.smul_mem _ _ heig)
  exact ⟨x, hx, by rw [hbx, smul_smul, mul_comm]⟩

end GlobalTheory.FlatModel
