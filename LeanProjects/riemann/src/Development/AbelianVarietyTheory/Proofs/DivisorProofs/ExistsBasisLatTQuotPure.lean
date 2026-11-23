import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleGramRelationsBlocksOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealNormEquationFromLocalAssociatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateLinearTensorModuleDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialLatticeEndomorphismLiftStatement

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit
open scoped TensorProduct NNReal

namespace GlobalTheory.IndexIdeal

section Index

variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U]

variable (C) in

def HasIndex (n : ℕ) (L L' : Submodule O U) (I : Ideal O) : Prop :=
  ∃ (w : Fin n → U) (g : Matrix (Fin n) (Fin n) O), LinearIndependent C w ∧ Submodule.span O (Set.range w) = L ∧
    Submodule.span O (Set.range fun i => ∑ j, g i j • w j) = L' ∧ g.det ≠ 0 ∧ Ideal.span {g.det} = I

example {x : U} (hx : x ≠ 0) {a : O} (ha : a ≠ 0) :
    HasIndex C 1 (Submodule.span O {x}) (Submodule.span O {a • x}) (Ideal.span {a}) :=
  ⟨fun _ => x, Matrix.of fun _ _ => a, by simpa using hx, by simp, by simp, by simpa using ha, by simp⟩

theorem hasIndex_of_fintype {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ} (hn : Fintype.card κ = n) {w : κ → U}
    (g : Matrix κ κ O) (hw : LinearIndependent C w) (hg : g.det ≠ 0) :
    HasIndex C n (Submodule.span O (Set.range w)) (Submodule.span O (Set.range fun i => ∑ j, g i j • w j))
      (Ideal.span {g.det}) := by
  let e : Fin n ≃ κ := (Fintype.equivFinOfCardEq hn).symm
  refine ⟨w ∘ e, g.submatrix e e, hw.comp _ e.injective, by rw [e.surjective.range_comp], ?_,
    by rwa [Matrix.det_submatrix_equiv_self], by rw [Matrix.det_submatrix_equiv_self]⟩
  rw [← e.surjective.range_comp fun i => ∑ j, g i j • w j]
  congr 2
  funext i
  exact e.sum_comp fun j => g (e i) j • w j

theorem HasIndex.le {n : ℕ} {L L' : Submodule O U} {I : Ideal O} (h : HasIndex C n L L' I) : L' ≤ L := by
  obtain ⟨w, g, -, rfl, rfl, -⟩ := h
  exact Submodule.span_le.2 (Set.range_subset_iff.2 fun i =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

theorem exists_matrix {n : ℕ} {x y : Fin n → U} (h : Submodule.span O (Set.range x) ≤ Submodule.span O (Set.range y)) :
    ∃ a : Matrix (Fin n) (Fin n) O, ∀ i, x i = ∑ j, (a.map (algebraMap O C)) i j • y j := by
  choose a ha using fun i => (Submodule.mem_span_range_iff_exists_fun O).1 (h (Submodule.subset_span ⟨i, rfl⟩))
  exact ⟨Matrix.of a, fun i => by simp only [Matrix.map_apply, Matrix.of_apply, algebraMap_smul, ha]⟩

omit [Module O U] [IsScalarTower O C U] in
theorem comb_comb {n : ℕ} {x y z : Fin n → U} {a b : Matrix (Fin n) (Fin n) C} (h : ∀ i, x i = ∑ j, a i j • y j)
    (h' : ∀ i, y i = ∑ j, b i j • z j) (i : Fin n) : x i = ∑ j, (a * b) i j • z j := by
  simp only [h i, h', Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

omit [Module O U] [IsScalarTower O C U] in
theorem comb_inj {n : ℕ} {x z : Fin n → U} (hz : LinearIndependent C z) {a b : Matrix (Fin n) (Fin n) C}
    (h : ∀ i, x i = ∑ j, a i j • z j) (h' : ∀ i, x i = ∑ j, b i j • z j) : a = b :=
  Matrix.ext fun i => Fintype.linearIndependent_iffₛ.1 hz _ _ ((h i).symm.trans (h' i))

theorem HasIndex.det (hi : Function.Injective (algebraMap O C)) {n : ℕ} {L L' : Submodule O U} {I : Ideal O}
    (h : HasIndex C n L L' I) {x x' : Fin n → U} (hL : Submodule.span O (Set.range x) = L)
    (hL' : Submodule.span O (Set.range x') = L') {a : Matrix (Fin n) (Fin n) C} (ha : ∀ i, x' i = ∑ j, a i j • x j) :
    ∃ d : O, algebraMap O C d = a.det ∧ Ideal.span {d} = I := by
  obtain ⟨w, g, hw, h1, h2, hg, rfl⟩ := h
  haveI : IsDomain O := hi.isDomain (algebraMap O C)
  have hd : ∀ b : Matrix (Fin n) (Fin n) O, (b.map (algebraMap O C)).det = algebraMap O C b.det := fun b =>
    ((algebraMap O C).map_det b).symm
  have hw' : ∀ i, (fun i => ∑ j, g i j • w j) i = ∑ j, (g.map (algebraMap O C)) i j • w j := fun i => by
    simp only [Matrix.map_apply, algebraMap_smul]
  obtain ⟨s, hs⟩ := exists_matrix (C := C) (hL.trans h1.symm).le
  obtain ⟨t, ht⟩ := exists_matrix (C := C) (h1.trans hL.symm).le
  obtain ⟨s', hs'⟩ := exists_matrix (C := C) (hL'.trans h2.symm).le
  obtain ⟨t', ht'⟩ := exists_matrix (C := C) (h2.trans hL'.symm).le
  have e1 := congrArg Matrix.det (comb_inj hw (comb_comb ht hs) (b := 1) fun i => by simp [Matrix.one_apply])
  have e2 := congrArg Matrix.det (comb_inj hw (comb_comb ha hs) (comb_comb hs' hw'))
  have e3 := congrArg Matrix.det (comb_inj hw (comb_comb ht' (comb_comb hs' hw')) hw')
  simp only [Matrix.det_mul, hd, Matrix.det_one] at e1 e2 e3
  have f1 : t.det * s.det = 1 := hi (by rw [map_mul, e1, map_one])
  have f3 : t'.det * s'.det = 1 := mul_right_cancel₀ hg (hi (by rw [map_mul, map_mul, mul_assoc, e3, _root_.one_mul]))
  refine ⟨t.det * s'.det * g.det, ?_, ?_⟩
  · rw [map_mul, map_mul, mul_assoc, ← e2, mul_left_comm, e1, _root_.mul_one]
  · exact Ideal.span_singleton_mul_left_unit ((IsUnit.of_mul_eq_one _ f1).mul (IsUnit.of_mul_eq_one_right _ f3)) _

theorem HasIndex.val_det {v : Valuation C ℝ≥0} (hv : v.Integers O) {n : ℕ} {L L' : Submodule O U} {d : O}
    (h : HasIndex C n L L' (Ideal.span {d})) {x x' : Fin n → U} (hL : Submodule.span O (Set.range x) = L)
    (hL' : Submodule.span O (Set.range x') = L') {a : Matrix (Fin n) (Fin n) C} (ha : ∀ i, x' i = ∑ j, a i j • x j) :
    v a.det = v (algebraMap O C d) := by
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  obtain ⟨d', h1, h2⟩ := h.det hv.hom_inj hL hL' ha
  obtain ⟨u, rfl⟩ := Ideal.span_singleton_eq_span_singleton.1 h2
  rw [← h1, map_mul, map_mul, hv.one_of_isUnit u.isUnit, mul_one]

end Index

section Parts

variable {A R Λ O C : Type} [CommRing A] [CommRing R] [CommRing Λ] [CommRing O] [Field C] [Algebra A R] [Algebra A O]
  [Algebra A C] [Algebra O C] [IsScalarTower A O C] {ι : Λ →+* R} (hι : Submodule.span A (Set.range ι) = ⊤)
  {J : Type} [DecidableEq J] {σ : J → Λ →+* O} (hs : IsSplitting (embC C σ)) (k : J) (χ : R →ₐ[A] O)
  (hχ : ∀ a, χ (ι a) = σ k a) {T : Type} [AddCommGroup T] [Module A T] (ρ : Λ →+* Module.End A T)
  {κ : Type} [Fintype κ] [DecidableEq κ] (f : (κ → R) ≃ₗ[A] T) (hf : ∀ a r, f (ι a • r) = ρ a (f r))

def part (j : κ) : C ⊗[A] T := proj hs (baseChangeAction C ρ) k (1 ⊗ₜ f (Pi.single j 1))

include hι hχ hf in
theorem proj_frame (r : κ → R) :
    proj hs (baseChangeAction C ρ) k (1 ⊗ₜ f r) = ∑ j, χ (r j) • part hs k ρ f j := by
  have h1 : ∀ (s : R) (r : κ → R), proj hs (baseChangeAction C ρ) k (1 ⊗ₜ f (s • r)) =
      χ s • proj hs (baseChangeAction C ρ) k (1 ⊗ₜ f r) := fun s r => by
    have hm : s ∈ Submodule.span A (Set.range ι) := hι ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      have e := (isEquivariant_action (baseChangeAction C ρ) a).proj hs k (1 ⊗ₜ f r)
      rw [mem_eigenSub.1 (proj_mem hs _ k _) a] at e
      rw [hf, hχ, ← algebraMap_smul C]
      exact e.symm
    | zero => simp
    | add x y _ _ hx hy => rw [add_smul, map_add, TensorProduct.tmul_add, map_add, hx, hy, map_add, add_smul]
    | smul a x _ hx =>
      rw [smul_assoc, map_smul, TensorProduct.tmul_smul, LinearMap.map_smul_of_tower, hx, map_smul, smul_assoc]
  conv_lhs => rw [pi_eq_sum_univ' r, map_sum, TensorProduct.tmul_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => h1 _ _

include hχ hf in
theorem linearIndependent_part : LinearIndependent C (part hs k ρ f) := by
  let g : κ → (C ⊗[A] T →ₗ[C] C) := fun j => LinearMap.liftBaseChange C
    ((Algebra.linearMap O C).restrictScalars A ∘ₗ χ.toLinearMap ∘ₗ LinearMap.proj j ∘ₗ f.symm.toLinearMap)
  let ρ' : Λ →+* Module.End C C := (algebraMap C _).comp (embC C σ k)
  have hg : ∀ j, IsEquivariant (baseChangeAction C ρ) ρ' (g j) := fun j a x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c t =>
      obtain ⟨r, rfl⟩ := f.surjective t
      have : baseChangeAction C ρ a (c ⊗ₜ f r) = c ⊗ₜ f (ι a • r) := by rw [hf]; rfl
      rw [this]
      simp [g, ρ', hχ, mul_left_comm]
  have hd : ∀ j l, g j (part hs k ρ f l) = if j = l then 1 else 0 := fun j l => by
    rw [part, (hg j).proj hs k, proj_of_mem hs (mem_eigenSub.2 fun a => by simp [ρ'])]
    simp [g, Pi.single_apply, apply_ite]
  refine Fintype.linearIndependent_iff.2 fun c hc j => ?_
  simpa [hd] using congrArg (g j) hc

include hι hχ hf in
theorem span_part : Submodule.span O (Set.range (part hs k ρ f)) = eigQuotLat (baseChangeAction C ρ) hs k
    (LinearMap.range ((TensorProduct.mk A C T 1).liftBaseChange O)) := by
  refine le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 fun j => ⟨_, ⟨1 ⊗ₜ f (Pi.single j 1), ?_⟩, rfl⟩)) ?_
  · simp
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
    | tmul c t =>
      obtain ⟨r, rfl⟩ := f.surjective t
      rw [LinearMap.liftBaseChange_tmul, map_smul]
      refine Submodule.smul_mem _ _ ?_
      have e := proj_frame hι hs k χ hχ ρ f hf r
      exact e ▸ Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end Parts

section Sum

variable {A R Λ O C : Type} [CommRing A] [CommRing R] [CommRing Λ] [CommRing O] [Field C] [Algebra A R] [Algebra A O]
  [Algebra A C] [Algebra O C] [IsScalarTower A O C] {ι : Λ →+* R} (hι : Submodule.span A (Set.range ι) = ⊤)
  {J : Type} [DecidableEq J] {σ : J → Λ →+* O} (hs : IsSplitting (embC C σ)) (k : J) (χ : R →ₐ[A] O)
  (hχ : ∀ a, χ (ι a) = σ k a) {T : Type} [AddCommGroup T] [Module A T] (ρ : Λ →+* Module.End A T)
  {κ : Type} [Fintype κ] [DecidableEq κ] (f : (κ → R) ≃ₗ[A] T) (hf : ∀ a r, f (ι a • r) = ρ a (f r))
  {T' : Type} [AddCommGroup T'] [Module A T'] (ρ' : Λ →+* Module.End A T')
  (f' : (Unit → R) ≃ₗ[A] T') (hf' : ∀ a r, f' (ι a • r) = ρ' a (f' r))

include hι hχ hf hf' in

theorem map_quot_eq (φ : T' →ₗ[A] T) (hφ : ∀ a x, φ (ρ' a x) = ρ a (φ x)) {m : κ → R} (hm : f m = φ (f' 1)) :
    (eigQuotLat (baseChangeAction C ρ') hs k (LinearMap.range ((TensorProduct.mk A C T' 1).liftBaseChange O))).map
      ((φ.baseChange C).restrictScalars O) = Submodule.span O {∑ j, χ (m j) • part hs k ρ f j} := by
  have he : IsEquivariant (baseChangeAction C ρ') (baseChangeAction C ρ) (φ.baseChange C) := fun a x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c t => exact congrArg (c ⊗ₜ ·) (hφ a t)
  rw [← span_part hι hs k χ hχ ρ' f' hf', Set.range_unique, Submodule.map_span, Set.image_singleton,
    ← proj_frame hι hs k χ hχ ρ f hf, hm]
  congr 2
  refine (he.proj hs k _).trans ?_
  rw [LinearMap.baseChange_tmul]
  congr 4

end Sum

section Completion

variable (ℓ : ℕ) [Fact ℓ.Prime] (Λ : Type) [CommRing Λ]

abbrev toCompl : Λ →+* ℤ_[ℓ] ⊗[ℤ] Λ := (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom

theorem span_toCompl : Submodule.span ℤ_[ℓ] (Set.range (toCompl ℓ Λ)) = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | tmul c a =>
    have : c ⊗ₜ[ℤ] a = c • toCompl ℓ Λ a := by simp [TensorProduct.smul_tmul']
    exact this ▸ Submodule.smul_mem _ c (Submodule.subset_span ⟨a, rfl⟩)

variable {Λ} in

def extChar {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (χ : Λ →+* O) : ℤ_[ℓ] ⊗[ℤ] Λ →ₐ[ℤ_[ℓ]] O :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) χ.toIntAlgHom fun _ _ => Commute.all _ _

variable {Λ} in
theorem extChar_toCompl {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (χ : Λ →+* O) (a : Λ) :
    extChar ℓ χ (toCompl ℓ Λ a) = χ a := by simp [extChar]

end Completion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.FlatCM GlobalTheory.PointMap GlobalTheory.GramAt
attribute [local instance] Over.cartesianMonoidalCategory

section Frames

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]

def IsFrame {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point ℓ v O Λ) {κ : Type}
    (f : (κ → ℤ_[ℓ] ⊗[ℤ] Λ) ≃ₗ[ℤ_[ℓ]] P.T) : Prop :=
  ∀ a r, f (toCompl ℓ Λ a • r) = P.actT a (f r)

variable {E : Type} [Field E] [NumberField E]

theorem exists_isFrame_complex [StarRing (𝓞 E)] {v : Valuation ℂ ℝ≥0} {O : Type} [CommRing O] [Algebra O ℂ]
    (P : Point ℓ v O (𝓞 E)) (κ : Type) [Fintype κ] (h : 2 * P.A.g = Fintype.card κ * Module.finrank ℚ E) :
    ∃ f : (κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) ≃ₗ[ℤ_[ℓ]] P.T, IsFrame P f := by
  have hT : ThetaUnifAV := thetaUnifAV_all
  obtain ⟨u, HA, χA, -, hu, -⟩ := PureType.exists_isThetaUnif hT P.A
  obtain ⟨-, -, -, -, h1, h2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT P.A _ u HA χA hu
  let α := P.oA.toRingAct
  choose F hF using fun a : 𝓞 E => (HomLinear.exists_linear_of_isMonHom P.A.A P.A.A P.A.isAb P.A.isAb _ _ _ _ u u h1 h2
    (α.act a) (α.hom a)).imp fun _ h => h.1
  have hu0 : ∀ M N : (Fin P.A.g → ℂ) →ₗ[ℂ] (Fin P.A.g → ℂ), (∀ z, u.ex (M z) = u.ex (N z)) → M = N := fun M N h => by
    refine sub_eq_zero.1 (PointUnif.linear_eq_zero_of_discrete u.Λ u.discrete _ fun z => (u.ker _).1 ?_)
    have := u.ex_add ((M - N) z) (N z)
    rw [LinearMap.sub_apply, sub_add_cancel, h] at this
    exact mul_eq_right.1 this.symm
  let ρ : 𝓞 E →+* Module.End ℂ (Fin P.A.g → ℂ) := RingHom.mk' (MonoidHom.mk (OneHom.mk F
      (hu0 _ _ fun z => by rw [hF, α.map_one, Category.comp_id]; rfl))
      fun a b => hu0 _ _ fun z => by
        change u.ex (F (a * b) z) = u.ex (F a (F b z))
        rw [hF, hF, hF, α.map_mul, Category.assoc])
    fun a b => hu0 _ _ fun z => by
      change u.ex (F (a + b) z) = u.ex (F a z + F b z)
      rw [u.ex_add, hF, hF, hF, actPts_add]
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  exact GlobalTheory.T.exponential_lattice_endomorphism_lift E ℓ _ ρ (ChTor.Pts P.A.A) u.ex u.ex_add u.ex_onto u.Λ u.ker (ZLattice.module_finite ℝ u.Λ)
    (actPts α _) hF P.actT (fun _ _ _ => rfl) inferInstance inferInstance κ
    (by rw [ZLattice.rank ℝ u.Λ, Module.finrank_pi_fintype, ← h]; simp [mul_comm]) (P.hodgeTateLatticePoint_finrank_tateModule.trans h)

variable [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K] [IsAlgClosed C] [CharZero C]
  (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C)

theorem exists_isFrame (T : PAT H (Sp (𝓞 K))) (κ : Type) [Fintype κ]
    (h : 2 * T.g = Fintype.card κ * Module.finrank ℚ E) : letI := H.starRing
    ∃ f : (κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) ≃ₗ[ℤ_[ℓ]] (patPoint hv ε i T).T, IsFrame (patPoint hv ε i T) f := by
  classical
  letI := H.starRing
  obtain ⟨ε'⟩ : Nonempty (Eps ℓ ℂ) := inferInstance
  have hv' : (1 : Valuation ℂ ℝ≥0).Integers ℂ :=
    ⟨fun _ _ h => h, fun x => Valuation.one_apply_le_one x, fun {x} _ => ⟨x, rfl⟩⟩
  let i' : K →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ)).toRingHom
  obtain ⟨e, he, -⟩ := exists_patT_equiv (H := H) hv' ε' i' hv ε i
  obtain ⟨f, hf⟩ := exists_isFrame_complex (patPoint hv' ε' i' T) κ h
  exact ⟨f.trans (e T), fun a r => (congrArg (e T) (hf a r)).trans (he T a _)⟩

end Frames

section Points

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ] [Algebra ℤ_[ℓ] C] [Algebra ℤ_[ℓ] O] [IsScalarTower ℤ_[ℓ] O C]
  {J : Type} [DecidableEq J] {σ : J → Λ →+* O} (hs : IsSplitting (embC C σ)) (k : J)

theorem IsFrame.exists_basis {P : Point ℓ v O Λ} {n : ℕ} {f : (Fin n → ℤ_[ℓ] ⊗[ℤ] Λ) ≃ₗ[ℤ_[ℓ]] P.T}
    (hf : IsFrame P f) :
    ∃ w : Fin n → P.V, LinearIndependent C w ∧ Submodule.span O (Set.range w) = P.latTQuot hs k :=
  ⟨part hs k P.actT f, linearIndependent_part hs k (extChar ℓ (σ k)) (extChar_toCompl ℓ _) P.actT f hf,
    span_part (span_toCompl ℓ Λ) hs k (extChar ℓ (σ k)) (extChar_toCompl ℓ _) P.actT f hf⟩

theorem hasIndex_of_frames {A A' B : Point ℓ v O Λ} {p q : ℕ} (φ : Fin p → (A.T →ₗ[ℤ_[ℓ]] B.T))
    (φ' : Fin q → (A'.T →ₗ[ℤ_[ℓ]] B.T)) (hφ : ∀ a c x, φ a (A.actT c x) = B.actT c (φ a x))
    (hφ' : ∀ a c x, φ' a (A'.actT c x) = B.actT c (φ' a x)) {f₁ : (Unit → ℤ_[ℓ] ⊗[ℤ] Λ) ≃ₗ[ℤ_[ℓ]] A.T}
    {f₂ : (Unit → ℤ_[ℓ] ⊗[ℤ] Λ) ≃ₗ[ℤ_[ℓ]] A'.T} {f : (Fin p ⊕ Fin q → ℤ_[ℓ] ⊗[ℤ] Λ) ≃ₗ[ℤ_[ℓ]] B.T}
    (h₁ : IsFrame A f₁) (h₂ : IsFrame A' f₂) (h : IsFrame B f)
    {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (ℤ_[ℓ] ⊗[ℤ] Λ)} (hM₁ : ∀ a, f (M (.inl a)) = φ a (f₁ 1))
    (hM₂ : ∀ a, f (M (.inr a)) = φ' a (f₂ 1)) (hd : extChar ℓ (σ k) M.det ≠ 0) :
    HasIndex C (p + q) (B.latTQuot hs k)
      ((⨆ a, (A.latTQuot hs k).map (((φ a).baseChange C).restrictScalars O)) ⊔
        ⨆ b, (A'.latTQuot hs k).map (((φ' b).baseChange C).restrictScalars O))
      (Ideal.span {extChar ℓ (σ k) M.det}) := by
  have hχ := extChar_toCompl ℓ (σ k)
  have e := hasIndex_of_fintype (n := p + q) (by simp) (M.map (extChar ℓ (σ k)))
    (linearIndependent_part hs k _ hχ B.actT f h) (((extChar ℓ (σ k)).map_det M).symm.trans_ne hd)
  rw [span_part (span_toCompl ℓ Λ) hs k _ hχ B.actT f h, Submodule.span_range_eq_iSup, iSup_sum] at e
  have e₁ : ∀ a, (A.latTQuot hs k).map (((φ a).baseChange C).restrictScalars O) = _ := fun a =>
    map_quot_eq (span_toCompl ℓ Λ) hs k _ hχ B.actT f h A.actT f₁ h₁ (φ a) (hφ a) (hM₁ a)
  have e₂ : ∀ a, (A'.latTQuot hs k).map (((φ' a).baseChange C).restrictScalars O) = _ := fun a =>
    map_quot_eq (span_toCompl ℓ Λ) hs k _ hχ B.actT f h A'.actT f₂ h₂ (φ' a) (hφ' a) (hM₂ a)
  rw [iSup_congr e₁, iSup_congr e₂, (extChar ℓ (σ k)).map_det M]
  exact e

end Points

section Object

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ}

section At

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C) (X : CMObj H K ρ σ₁ p q)

def IsFrameDet (δ : ℤ_[ℓ] ⊗[ℤ] 𝓞 E) : Prop :=
  letI := H.starRing
  ∃ (f₁ : (Unit → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) ≃ₗ[ℤ_[ℓ]] (pointA hv ε i X true).T)
    (f₂ : (Unit → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) ≃ₗ[ℤ_[ℓ]] (pointA hv ε i X false).T)
    (f : (Fin p ⊕ Fin q → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) ≃ₗ[ℤ_[ℓ]] (pointB hv ε i X).T)
    (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (ℤ_[ℓ] ⊗[ℤ] 𝓞 E)),
    IsFrame _ f₁ ∧ IsFrame _ f₂ ∧ IsFrame _ f ∧ (∀ a, f (M (.inl a)) = phiTP hv ε i X a (f₁ 1)) ∧
      (∀ a, f (M (.inr a)) = phiTQ hv ε i X a (f₂ 1)) ∧ M.det = δ

variable [IsAlgClosed C] [CharZero C]

omit [NumberField K] in
theorem two_mul_half : 2 * (Module.finrank ℚ E / 2) = Module.finrank ℚ E :=
  Nat.mul_div_cancel' ⟨Module.finrank ℚ (maximalRealSubfield E), by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E, Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]⟩

theorem exists_isFrameDet : ∃ δ, IsFrameDet hv ε i X δ := by
  letI := H.starRing
  obtain ⟨h1, h2, -⟩ := dims X
  obtain ⟨f₁, h₁⟩ := exists_isFrame hv ε i (X.A true) Unit (by simp [h1, two_mul_half])
  obtain ⟨f₂, h₂⟩ := exists_isFrame hv ε i (X.A false) Unit (by simp [h1, two_mul_half])
  obtain ⟨f, h⟩ := exists_isFrame hv ε i X.B (Fin p ⊕ Fin q) (by
    rw [h2, ← mul_assoc, two_mul_half, mul_comm]; simp)
  exact ⟨_, f₁, f₂, f, Matrix.of (Sum.elim (fun a => f.symm (phiTP hv ε i X a (f₁ 1)))
    fun a => f.symm (phiTQ hv ε i X a (f₂ 1))), h₁, h₂, h, fun a => f.apply_symm_apply _,
    fun a => f.apply_symm_apply _, rfl⟩

variable {hv ε i X}

theorem IsFrameDet.transport {δ : ℤ_[ℓ] ⊗[ℤ] 𝓞 E} (h : IsFrameDet hv ε i X δ) {C' : Type} [Field C']
    {v' : Valuation C' ℝ≥0} {O' : Type} [CommRing O'] [Algebra O' C'] [IsAlgClosed C'] [CharZero C']
    (hv' : v'.Integers O') (ε' : Eps ℓ C') (i' : K →+* C') : IsFrameDet hv' ε' i' X δ := by
  letI := H.starRing
  obtain ⟨f₁, f₂, f, M, h₁, h₂, h, hM₁, hM₂, hd⟩ := h
  obtain ⟨e, he, he'⟩ := exists_patT_equiv (H := H) hv ε i hv' ε' i'
  exact ⟨f₁.trans (e (X.A true)), f₂.trans (e (X.A false)), f.trans (e X.B), M,
    fun a r => (congrArg (e _) (h₁ a r)).trans (he _ a _), fun a r => (congrArg (e _) (h₂ a r)).trans (he _ a _),
    fun a r => (congrArg (e _) (h a r)).trans (he _ a _),
    fun a => (congrArg (e _) (hM₁ a)).trans (he' (X.A true) X.B _ (X.lin (.inl a)) _),
    fun a => (congrArg (e _) (hM₂ a)).trans (he' (X.A false) X.B _ (X.lin (.inr a)) _), hd⟩

theorem IsFrameDet.associated {δ : ℤ_[ℓ] ⊗[ℤ] 𝓞 E} (h : IsFrameDet hv ε i X δ) {gP : Matrix (Fin p) (Fin p) (𝓞 E)}
    {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (hg : IsGram X gP gQ) :
    Associated (δ * Algebra.TensorProduct.map (AlgHom.id ℤ_[ℓ] ℤ_[ℓ]) (H.bar : 𝓞 E →+* 𝓞 E).toIntAlgHom δ)
      ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] (gP.det * gQ.det)) := by
  letI := H.starRing
  obtain ⟨f₁, f₂, f, M, h₁, h₂, h, hM₁, hM₂, rfl⟩ := h
  obtain ⟨hP, hQ, hO⟩ := tateModule_gram_relations_blocks_orthogonal hv ε i X hg
  exact GlobalTheory.T.conjugate_linear_tensor_module_decomposition ℤ_[ℓ] _ (𝓞 E) (toCompl ℓ _) (span_toCompl ℓ _) (H.bar : 𝓞 E →+* 𝓞 E) _ (fun _ => rfl)
    (fun a => star_star a) _ _ _ (pointA hv ε i X true).actT (pointA hv ε i X false).actT (pointB hv ε i X).actT
    (pairT (pointA hv ε i X true).A ε) (pairT (pointA hv ε i X false).A ε) (pairT (pointB hv ε i X).A ε)
    (pointA hv ε i X true).pairT_bijective (pointA hv ε i X false).pairT_bijective (pointB hv ε i X).pairT_bijective
    (pairT_act (pointA hv ε i X true).oA ε) (pairT_act (pointA hv ε i X false).oA ε)
    (pairT_act (pointB hv ε i X).oA ε) _ _ (phiTP hv ε i X) (phiTQ hv ε i X) gP gQ
    (fun a => patT_actT (T := X.A true) hv ε i (X.lin (.inl a)))
    (fun a => patT_actT (T := X.A false) hv ε i (X.lin (.inr a))) hP hQ hO
    (fun a b s t => ((isAlt_pairT (pointB hv ε i X).A ε).neg_eq _ _).symm.trans (neg_eq_zero.2 (hO b a t s)))
    f₁ f₂ f h₁ h₂ h M hM₁ hM₂

variable (hv ε i X) [Algebra ℤ_[ℓ] C] [Algebra ℤ_[ℓ] O] [IsScalarTower ℤ_[ℓ] O C]
  {J : Type} [DecidableEq J] {σ : J → 𝓞 E →+* O} (hs : IsSplitting (embC C σ)) (k : J)

abbrev quotImage : letI := H.starRing; Submodule O (pointB hv ε i X).V :=
  letI := H.starRing
  (⨆ a, ((pointA hv ε i X true).latTQuot hs k).map ((phiVP hv ε i X a).restrictScalars O)) ⊔
    ⨆ b, ((pointA hv ε i X false).latTQuot hs k).map ((phiVQ hv ε i X b).restrictScalars O)

theorem exists_basis_latTQuot_pure (b : Bool) : letI := H.starRing
    ∃ w : Fin 1 → (pointA hv ε i X b).V, LinearIndependent C w ∧
      Submodule.span O (Set.range w) = (pointA hv ε i X b).latTQuot hs k := by
  letI := H.starRing
  obtain ⟨f, h⟩ := exists_isFrame hv ε i (X.A b) (Fin 1) (by simp [(dims X).1, two_mul_half])
  exact h.exists_basis hs k

end At

theorem exists_indexIdeal (X : CMObj H K ρ σ₁ p q) {gP : Matrix (Fin p) (Fin p) (𝓞 E)}
    {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) : letI := H.starRing
    ∃ 𝔫 : Ideal (𝓞 E), 𝔫 * 𝔫.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {gP.det * gQ.det} ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type)
        [CommRing O] [Algebra O C] [Algebra ℤ_[ℓ] C] [Algebra ℤ_[ℓ] O] [IsScalarTower ℤ_[ℓ] O C] (hv : v.Integers O)
        (ε : Eps ℓ C) (i : K →+* C) (J : Type) [DecidableEq J] (σ : J → 𝓞 E →+* O) (hs : IsSplitting (embC C σ)) (k : J),
        HasIndex C (p + q) ((pointB hv ε i X).latTQuot hs k) (quotImage hv ε i X hs k) (𝔫.map (σ k)) := by
  letI := H.starRing
  have hD : gP.det * gQ.det ≠ 0 := mul_ne_zero (gram_det X h).1 (gram_det X h).2.1
  have hex : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ δ, IsFrameDet (PadicComplexInt.integers ℓ)
      (Classical.arbitrary (Eps ℓ ℂ_[ℓ])) (IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ_[ℓ])).toRingHom X δ :=
    fun ℓ _ => exists_isFrameDet _ _ _ X
  choose δ hδ using hex
  have hm : 0 < Ideal.absNorm (Ideal.span {gP.det * gQ.det}) :=
    Nat.pos_of_ne_zero fun h0 => hD (Ideal.span_singleton_eq_bot.1 (Ideal.absNorm_eq_zero_iff.1 h0))
  obtain ⟨𝔫, h1, h2⟩ := GlobalTheory.T.ideal_norm_equation_from_local_associates (𝓞 E) (H.bar : 𝓞 E →+* 𝓞 E) _ _ hm (Ideal.absNorm_mem _) δ
    fun ℓ _ => (hδ ℓ).associated h
  refine ⟨𝔫, h1, fun ℓ _ C _ _ _ v O _ _ _ _ _ hv ε i J _ σ hs k => ?_⟩
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : CharZero O := (algebraMap O C).charZero
  have e : 𝔫.map (σ k) = Ideal.span {extChar ℓ (σ k) (δ ℓ)} := by
    have e' : (extChar ℓ (σ k)).toRingHom.comp (toCompl ℓ _) = σ k := RingHom.ext (extChar_toCompl ℓ (σ k))
    refine (congrArg 𝔫.map e').symm.trans ?_
    rw [← Ideal.map_map, h2, Ideal.map_span, Set.image_singleton]
    rfl
  have h0 : extChar ℓ (σ k) (δ ℓ) ≠ 0 := fun h0 => by
    have : (Ideal.span {gP.det * gQ.det}).map (σ k) = ⊥ := by
      rw [← h1, Ideal.map_mul, e, h0]; simp
    have h3 := Ideal.mem_map_of_mem (σ k) (Ideal.absNorm_mem (Ideal.span {gP.det * gQ.det}))
    rw [this, map_natCast, Ideal.mem_bot, Nat.cast_eq_zero] at h3
    exact hm.ne' h3
  obtain ⟨f₁, f₂, f, M, h₁, h₂, h', hM₁, hM₂, hd⟩ := (hδ ℓ).transport hv ε i
  rw [e, ← hd]
  exact hasIndex_of_frames hs k (A := pointA hv ε i X true) (A' := pointA hv ε i X false) (B := pointB hv ε i X)
    (phiTP hv ε i X) (phiTQ hv ε i X) (fun a => patT_actT (T := X.A true) hv ε i (X.lin (.inl a)))
    (fun a => patT_actT (T := X.A false) hv ε i (X.lin (.inr a))) h₁ h₂ h' hM₁ hM₂ (hd ▸ h0)

omit [IsCMField E] in

theorem exists_embO_eq {C : Type} [Field C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
    (hv : v.Integers O) (χ : 𝓞 E →+* O) : ∃ φ : E →+* C, embO hv φ = χ := by
  have hi : Function.Injective ((algebraMap O C).comp χ) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra h0
    have h := Ideal.absNorm_mem (RingHom.ker ((algebraMap O C).comp χ))
    rw [RingHom.mem_ker, map_natCast, Nat.cast_eq_zero] at h
    exact h0 (Ideal.absNorm_eq_zero_iff.1 h)
  exact ⟨IsFractionRing.lift hi, RingHom.ext fun a => hv.hom_inj
    ((algebraMap_embO hv _ a).trans (IsFractionRing.lift_algebraMap hi a))⟩

open Classical GlobalTheory.HTLat.OmegaRank in

theorem index_ideal (X : CMObj H K ρ σ₁ p q) {gP : Matrix (Fin p) (Fin p) (𝓞 E)}
    {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) :
    ∃ 𝔫 : Ideal (𝓞 E), 𝔫 * 𝔫.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {gP.det * gQ.det} ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ε : Eps ℓ ℂ_[ℓ]) (i : K →+* ℂ_[ℓ]) (τ : 𝓞 E →+* 𝓞 K),
        letI := H.starRing; letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ
        ∃ φ : E →+* ℂ_[ℓ], embO (PadicComplexInt.integers ℓ) φ = (embO (PadicComplexInt.integers ℓ) i).comp τ ∧
          HasIndex ℂ_[ℓ] (p + q)
            ((pointB (PadicComplexInt.integers ℓ) ε i X).latTQuot
              (σ := fun φ : E →+* ℂ_[ℓ] => embO (PadicComplexInt.integers ℓ) φ)
              (isSplitting_embO (PadicComplexInt.integers ℓ)) φ)
            (quotImage (PadicComplexInt.integers ℓ) ε i X
              (σ := fun φ : E →+* ℂ_[ℓ] => embO (PadicComplexInt.integers ℓ) φ)
              (isSplitting_embO (PadicComplexInt.integers ℓ)) φ)
            (𝔫.map ((embO (PadicComplexInt.integers ℓ) i).comp τ)) := by
  obtain ⟨𝔫, h1, h2⟩ := exists_indexIdeal X h
  refine ⟨𝔫, h1, fun ℓ _ ε i τ => ?_⟩
  letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ
  obtain ⟨φ, hφ⟩ := exists_embO_eq (PadicComplexInt.integers ℓ) ((embO (PadicComplexInt.integers ℓ) i).comp τ)
  exact ⟨φ, hφ, hφ ▸ h2 ℓ ℂ_[ℓ] _ _ (PadicComplexInt.integers ℓ) ε i _
    (fun φ : E →+* ℂ_[ℓ] => embO (PadicComplexInt.integers ℓ) φ) (isSplitting_embO (PadicComplexInt.integers ℓ)) φ⟩

end Object

end GlobalTheory.IndexIdeal
