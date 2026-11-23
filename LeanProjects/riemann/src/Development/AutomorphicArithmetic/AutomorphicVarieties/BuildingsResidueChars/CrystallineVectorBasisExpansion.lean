import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.WtMatFix
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Polynomial

section Coord

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {V : Type} [AddCommGroup V] [Module Qp V]
    (ρ : Representation Qp G V) {d : ℕ} (e : Basis (Fin d) Qp V)

private theorem coord_sum (c : Fin d → B) (i : Fin d) :
    (TensorProduct.lid Qp B) (LinearMap.rTensor B (e.coord i) (∑ j, e j ⊗ₜ[Qp] c j)) = c i := by
  simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Basis.coord_apply, Basis.repr_self]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Finsupp.single_apply, hj]
  · simp

private theorem exists_coord (x : V ⊗[Qp] B) : ∃ c : Fin d → B, x = ∑ j, e j ⊗ₜ[Qp] c j := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul v b =>
    refine ⟨fun j => e.repr v j • b, ?_⟩
    conv_lhs => rw [← e.sum_repr v]
    rw [sum_tmul]
    exact Finset.sum_congr rfl fun j _ => smul_tmul _ _ _
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, by simp [tmul_add, Finset.sum_add_distrib]⟩

private theorem act_sum (c : Fin d → B) (g : G) :
    actVB PD ρ g (∑ j, e j ⊗ₜ[Qp] c j) = ∑ i, e i ⊗ₜ[Qp]
      ((LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp B)).mulVec (fun j => PD.actB g (c j)) i := by
  simp only [map_sum, Matrix.mulVec, dotProduct, tmul_sum, Matrix.map_apply, LinearMap.toMatrix_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  change ρ g (e j) ⊗ₜ[Qp] PD.actB g (c j) = _
  conv_lhs => rw [← e.sum_repr (ρ g (e j))]
  rw [sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_tmul, Algebra.smul_def]

private theorem core (M M' : Matrix (Fin d) (Fin d) B) (hM : M * M' = 1)
    (hg : ∀ g, (LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp B) * M.map (PD.actB g) = M)
    (x : V ⊗[Qp] B) (hx : x ∈ Dcris PD ρ) :
    ∃ c : Fin d → K₀, x = ∑ i, e i ⊗ₜ[Qp] (M.mulVec (fun j => algebraMap K₀ B (c j)) i) := by
  obtain ⟨y, rfl⟩ := exists_coord e x
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx
  have hM' : M' * M = 1 := mul_eq_one_comm.1 hM
  have hy : ∀ g, ((LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp B)).mulVec (fun j => PD.actB g (y j)) = y := by
    intro g
    funext i
    have h := hx g
    rw [act_sum] at h
    rw [← coord_sum e y i, ← h, coord_sum]
  have h2 : ∀ g, M' * (LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp B) = M'.map (PD.actB g) := by
    intro g
    have h1 : M.map (PD.actB g) * M'.map (PD.actB g) = 1 := by
      rw [← Matrix.map_mul, hM, Matrix.map_one _ (map_zero _) (map_one _)]
    set R := (LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp B) with hR
    have : R * (M.map (PD.actB g) * M'.map (PD.actB g)) = M * M'.map (PD.actB g) := by
      rw [← Matrix.mul_assoc, hg g]
    rw [h1, Matrix.mul_one] at this
    rw [this, ← Matrix.mul_assoc, hM', Matrix.one_mul]
  choose c hc using fun i => PD.invB (M'.mulVec y i) fun g => by
    conv_rhs => rw [← hy g, Matrix.mulVec_mulVec, h2 g]
    simp [Matrix.mulVec, dotProduct]
  refine ⟨c, ?_⟩
  have h3 : (fun j => algebraMap K₀ B (c j)) = M'.mulVec y := funext hc
  rw [h3, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]

end Coord

theorem UpperTheory.crystalline_vector_basis_expansion :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) {d : ℕ} (e : Basis (Fin d) ℚ_[l] V) (M M' : Matrix (Fin d) (Fin d) (Bcr l)), M * M' = 1 → (∀ g : ↥(GK K), (LinearMap.toMatrix e e (ρ g)).map (algebraMap ℚ_[l] (Bcr l)) * M.map ((PP l).actQ (g : GQ l)) = M) → ∀ x ∈ Dcris ((PP l).PD K) ρ, ∃ c : Fin d → ↥(K0 K), x = ∑ i, e i ⊗ₜ[ℚ_[l]] (M.mulVec (fun j => algebraMap ↥(K0 K) (Bcr l) (c j)) i) := by
  intro l _ K V _ _ _ ρ d e M M' hM hg x hx
  refine core ((PP l).PD K) ρ e M M' hM (fun g => ?_) x hx
  have h5 : M.map (((PP l).PD K).actB g) = M.map ((PP l).actQ (g : GQ l)) := by
    ext i j
    exact (PP l).PD_actB K g _
  rw [h5, hg]
