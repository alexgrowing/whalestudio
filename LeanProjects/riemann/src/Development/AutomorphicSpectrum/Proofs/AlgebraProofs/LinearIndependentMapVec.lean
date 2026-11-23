import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BundleDegreeEqSumValuationsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FrobeniusLatticeDegreeMulPStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeBasisAdaptedToSubspaceStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundlesStatement

noncomputable section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubFrob

variable {K : Type} [Field K]

theorem repr_semilinear {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    {σ : K →+* K} (F : V →ₛₗ[σ] V') {n : ℕ} (b : Module.Basis (Fin n) K V)
    (b' : Module.Basis (Fin n) K V') (h : ∀ j, b' j = F (b j)) (x : V) (j : Fin n) :
    b'.repr (F x) j = σ (b.repr x j) := by
  have hx : F x = ∑ k, σ (b.repr x k) • b' k := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [LinearMap.map_smulₛₗ, h]
  rw [hx, b'.repr_sum_self]

theorem det_semilinear {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    {σ : K →+* K} (F : V →ₛₗ[σ] V') {n : ℕ} (b c : Module.Basis (Fin n) K V)
    (b' c' : Module.Basis (Fin n) K V') (h : ∀ j, b' j = F (b j)) (hc : ∀ j, c' j = F (c j)) :
    b'.det c' = σ (b.det c) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
  congr 1
  ext i j
  simp only [Module.Basis.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hc]
  exact repr_semilinear F b b' h _ _

theorem isLatOf_spanLat (C : ACurve K) {V V' : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] {σ : K →+* K} (F : V →ₛₗ[σ] V') {n : ℕ}
    (L : C.I → AddSubgroup V) (i : C.I) (hσ : ∀ a, C.v i a ≤ 1 → C.v i (σ a) ≤ 1)
    (b : Module.Basis (Fin n) K V) (b' : Module.Basis (Fin n) K V') (h : ∀ j, b' j = F (b j))
    (hL : IsLatOf C i b (L i)) : IsLatOf C i b' (spanLat C L F i) := by
  intro y
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, x, ha, hx, rfl⟩ := hy
      intro q
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, repr_semilinear F b b' h]
      exact mul_le_one' ha (hσ _ ((hL x).1 hx q))
    | zero => intro q; simp
    | add x y _ _ hx hy =>
      intro q
      rw [map_add, Finsupp.add_apply]
      exact (C.v i).map_add_le (hx q) (hy q)
    | neg x _ hx =>
      intro q
      rw [map_neg, Finsupp.neg_apply, Valuation.map_neg]
      exact hx q
  · intro hy
    rw [← b'.sum_repr y]
    refine AddSubgroup.sum_mem _ fun k _ => AddSubgroup.subset_closure ⟨_, b k, hy k, ?_, by rw [h]⟩
    rw [hL]
    intro q
    rw [b.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

theorem isLatOf_comap (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V] (i : C.I)
    {m r : ℕ} (L : AddSubgroup V) (W : Submodule K V) (b : Module.Basis (Fin (m + r)) K V)
    (c : Module.Basis (Fin m) K W) (h : ∀ j, b (Fin.castAdd _ j) = c j) (hL : IsLatOf C i b L) :
    IsLatOf C i c (L.comap W.subtype.toAddMonoidHom) := by
  intro x
  have hx : (x : V) = ∑ k, (Fin.addCases (motive := fun _ => K) (fun j => c.repr x j) (fun _ => 0) k) • b k := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, zero_smul, Finset.sum_const_zero, add_zero, h]
    have := congrArg W.subtype (c.sum_repr x)
    rw [map_sum] at this
    exact this.symm
  have hr : ∀ k, b.repr (x : V) k =
      Fin.addCases (motive := fun _ => K) (fun j => c.repr x j) (fun _ => 0) k := by
    intro k
    conv_lhs => rw [hx, b.repr_sum_self]
  rw [AddSubgroup.mem_comap]
  change (x : V) ∈ L ↔ _
  rw [hL]
  constructor
  · intro H q
    have := H (Fin.castAdd _ q)
    rwa [hr, Fin.addCases_left] at this
  · intro H q
    rw [hr]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) q
    · rw [Fin.addCases_left]; exact H j
    · rw [Fin.addCases_right]; simp

def mapVec (σ : K →+* K) (d : ℕ) : (Fin d → K) →ₛₗ[σ] (Fin d → K) where
  toFun x := fun j => σ (x j)
  map_add' x y := by ext; simp
  map_smul' a x := by ext; simp

theorem linearIndependent_mapVec (σ : K →+* K) {d n : ℕ} (v : Fin n → Fin d → K)
    (hv : LinearIndependent K v) : LinearIndependent K (fun j => mapVec σ d (v j)) := by
  have h1 : Function.Injective (Matrix.of v).vecMulLinear := by
    have := Matrix.vecMul_injective_iff.2 (show LinearIndependent K (Matrix.of v).row from hv)
    exact this
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 h1)
  set B : Matrix (Fin d) (Fin n) K := LinearMap.toMatrixRight' g with hB
  have hgB : ∀ x, g x = Matrix.vecMul x B := by
    intro x
    have : Matrix.toLinearMapRight' B = g := by
      rw [hB]; exact LinearMap.toMatrixRight'.symm_apply_apply g
    rw [← this]; rfl
  have h2 : Matrix.of v * B = 1 := by
    ext a b
    have := congrFun (LinearMap.congr_fun hg (Pi.single a 1)) b
    simp only [LinearMap.comp_apply, hgB, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul,
      LinearMap.id_apply, Matrix.single_one_vecMul] at this
    rw [Matrix.one_apply]
    change Matrix.vecMul (v a) B b = _
    simpa [Pi.single_apply, eq_comm] using this
  have h3 : (Matrix.of v).map σ * B.map σ = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ σ.map_zero σ.map_one]
  have h4 : LinearIndependent K ((Matrix.of v).map σ).row := by
    rw [← Matrix.vecMul_injective_iff]
    intro x y hxy
    have := congrArg (fun z => Matrix.vecMul z (B.map σ)) hxy
    simpa [Matrix.vecMul_vecMul, h3] using this
  exact h4

theorem exists_basis_top (σ : K →+* K) {d n : ℕ} (b : Module.Basis (Fin n) K (Fin d → K)) :
    ∃ b' : Module.Basis (Fin n) K (Fin d → K), ∀ j, b' j = mapVec σ d (b j) :=
  ⟨basisOfLinearIndependentOfCardEqFinrank' _ (linearIndependent_mapVec σ b b.linearIndependent)
    (Module.finrank_eq_card_basis b).symm, fun j => by simp⟩

theorem exists_basis_sub (σ : K →+* K) {d n : ℕ} (W : Submodule K (Fin d → K))
    (c : Module.Basis (Fin n) K W) :
    ∃ c' : Module.Basis (Fin n) K (Submodule.span K (mapVec σ d '' (W : Set (Fin d → K)))),
      ∀ j, (c' j : Fin d → K) = mapVec σ d (c j) := by
  have hli := linearIndependent_mapVec σ (fun j => (c j : Fin d → K))
    (c.linearIndependent.map' W.subtype W.ker_subtype)
  have hs : Submodule.span K (Set.range fun j => mapVec σ d (c j)) =
      Submodule.span K (mapVec σ d '' (W : Set (Fin d → K))) := by
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨j, rfl⟩
      exact ⟨c j, (c j).2, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have : x = ∑ k, c.repr ⟨x, hx⟩ k • (c k : Fin d → K) := by
        have := congrArg W.subtype (c.sum_repr ⟨x, hx⟩)
        rw [map_sum] at this
        exact this.symm
      rw [this, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine ⟨(Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hs), fun j => ?_⟩
  simp [Module.Basis.span_apply]

theorem subDeg_frob : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W : Submodule K (Fin d → K)), IsBun C L → subDeg C (frobLat C p L) (frobSub p W) = p * subDeg C L W := by
  intro K _ C p _ _ d L W hL
  set σ := frobenius K p with hσ
  have hL' : IsBun C (frobLat C p L) := (GlobalTheory.T.frobenius_lattice_degree_mul_p K C p d L hL).1
  have hS := (GlobalTheory.T.sub_and_quotient_bundles K C _ L W hL).1
  have hS' := (GlobalTheory.T.sub_and_quotient_bundles K C _ _ (frobSub p W) hL').1
  have hv : ∀ i a, C.v i (σ a) = C.v i a ^ p := fun i a => by rw [hσ, frobenius_def, map_pow]
  have key : ∀ i, ∃ (c : Module.Basis (Fin (Module.finrank K W)) K W)
      (c' : Module.Basis (Fin (Module.finrank K W)) K (frobSub p W)),
      IsLatOf C i c (sub C L W i) ∧ IsLatOf C i c' (sub C (frobLat C p L) (frobSub p W) i) ∧
      ∀ j, (c' j : Fin d → K) = mapVec σ d (c j) := by
    intro i
    obtain ⟨b, hb⟩ := hL.1 i
    obtain ⟨c, -, b₁, hb₁, hc, -, hbc, -⟩ := GlobalTheory.T.lattice_basis_adapted_to_subspace K C _ i _ b (L i) W hb
    obtain ⟨b', hb'⟩ := exists_basis_top σ b₁
    obtain ⟨c', hc'⟩ := exists_basis_sub σ W c
    refine ⟨c, c', hc, ?_, hc'⟩
    refine isLatOf_comap C i _ _ b' c' (fun j => by rw [hb', hbc]; exact (hc' j).symm) ?_
    exact isLatOf_spanLat C (mapVec σ d) L i (fun a ha => by rw [hv]; exact pow_le_one' ha p)
      b₁ b' hb' hb₁
  choose c c' hc hc' hcc using key
  obtain ⟨e', he'⟩ : ∃ e' : Module.Basis (Fin (Module.finrank K W)) K (frobSub p W),
      ∀ j, (e' j : Fin d → K) = mapVec σ d (Module.finBasis K W j) :=
    exists_basis_sub σ W (Module.finBasis K W)
  let G : W →ₛₗ[σ] frobSub p W :=
    ((mapVec σ d).domRestrict W).codRestrict (frobSub p W)
      (fun x => Submodule.subset_span ⟨x, x.2, rfl⟩)
  obtain ⟨-, h1⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C _ _ _ (Module.finBasis K W) c hS hc
  obtain ⟨-, h2⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C _ _ _ e' c' hS' hc'
  unfold subDeg
  rw [h1, h2, mul_finsum]
  refine finsum_congr fun i => ?_
  have hd := det_semilinear G (Module.finBasis K W) (c i) e' (c' i)
    (fun j => Subtype.ext (he' j)) (fun j => Subtype.ext (hcc i j))
  rw [hd, hv, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.Ar.Crv.SubFrob
