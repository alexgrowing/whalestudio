import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareMatrixImageSubmoduleContainsUniformiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankResidueBasisMatrixSuccOfAdjoinVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixFibreProductStableLatticeChainLineStatement
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

set_option autoImplicit false

namespace GlobalTheory.WachChain

theorem cancel_left {O ι : Type} [CommRing O] [Fintype ι] {q m : ℕ} (A : Matrix ι (Fin q) O)
    (hA : Function.Injective A.mulVec) {X Y : Matrix (Fin q) (Fin m) O} (h : A * X = A * Y) : X = Y := by
  ext i j
  have h1 := congrArg (fun Z => Z *ᵥ Pi.single j 1) h
  simp only [← Matrix.mulVec_mulVec] at h1
  have h2 := congrFun (hA h1) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2

theorem solve {O ι : Type} [CommRing O] [Fintype ι] {q m : ℕ} (A : Matrix ι (Fin q) O) (Z : Matrix ι (Fin m) O)
    (h : ∀ j, ∃ w, A *ᵥ w = fun i => Z i j) : ∃ Y : Matrix (Fin q) (Fin m) O, A * Y = Z := by
  choose w hw using h
  refine ⟨Matrix.of fun k j => w j k, ?_⟩
  ext i j
  have h1 := congrFun (hw j) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h1

theorem mkRep {Γ O ι : Type} [Group Γ] [CommRing O] [Fintype ι] [DecidableEq ι] {q : ℕ} (A : Matrix ι (Fin q) O)
    (ρ : Γ →* Matrix ι ι O) (hA : Function.Injective A.mulVec)
    (hst : ∀ g v, ∃ w, A *ᵥ w = ρ g *ᵥ (A *ᵥ v)) :
    ∃ r' : Γ →* GL (Fin q) O, ∀ g, A * (r' g : Matrix (Fin q) (Fin q) O) = ρ g * A := by
  have h1 : ∀ g, ∃ Y : Matrix (Fin q) (Fin q) O, A * Y = ρ g * A := fun g =>
    solve A (ρ g * A) fun j => by
      obtain ⟨w, hw⟩ := hst g (Pi.single j 1)
      refine ⟨w, ?_⟩
      rw [hw, Matrix.mulVec_mulVec]
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  choose Y hY using h1
  let f : Γ →* Matrix (Fin q) (Fin q) O :=
    { toFun := Y
      map_one' := cancel_left A hA (by rw [hY, map_one, Matrix.one_mul, Matrix.mul_one])
      map_mul' := fun g h => cancel_left A hA (by
        rw [hY, map_mul, Matrix.mul_assoc, ← hY h, ← Matrix.mul_assoc, ← hY g, Matrix.mul_assoc]) }
  exact ⟨f.toHomUnits, fun g => by rw [MonoidHom.coe_toHomUnits]; exact hY g⟩

theorem chain_of_lattices : ∀ (Γ O : Type) [Group Γ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n t R : ℕ) (r : Γ →* GL (Fin n) O) (ψ : Fin t → Γ →* Oˣ) (ϖ : O) (M : Fin (R + 1) → Submodule O (Fin n → O)) (rs : Fin t → Fin R), Irreducible ϖ → (∀ x, x ∈ M 0 ↔ ∃ y : Fin n → O, x = fun a => ϖ * y a) → M (Fin.last R) = ⊤ → Monotone M → (∀ g k x, x ∈ M k → (r g : Matrix (Fin n) (Fin n) O).mulVec x ∈ M k) → (∀ s, ∃ x ∈ M (rs s).succ, x ∉ M (rs s).castSucc ∧ M (rs s).succ = M (rs s).castSucc ⊔ Submodule.span O {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) O).mulVec x - (fun a => ((ψ s g : Oˣ) : O) * x a) ∈ M (rs s).castSucc) → ∃ (x : GalMats Γ O n t R) (dim : Fin (R + 1) → ℕ), x.Chain (residue O) r (fun s => GlobalTheory.TripleGal.rk1 (ψ s)) rs dim ∧ dim 0 = 0 ∧ dim (Fin.last R) = n ∧ ∀ s, dim (rs s).succ = dim (rs s).castSucc + 1 := by
  intro Γ O _ _ _ _ n t R r ψ ϖ M rs hϖ hM0 hlast hmono hst hline
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hin : ∀ k (y : Fin n → O), (fun a => ϖ * y a) ∈ M k := fun k y =>
    hmono (Fin.zero_le k) ((hM0 _).2 ⟨y, rfl⟩)
  choose A hA hdet using fun k => GlobalTheory.T.exists_square_matrix_image_submodule_contains_uniformizer n ϖ (M k) hϖ0 (hin k)
  have hinj : ∀ k, Function.Injective (A k).mulVec := fun k u v huv => by
    by_contra hne
    refine hdet k ((Matrix.exists_mulVec_eq_zero_iff).1 ⟨u - v, sub_ne_zero.2 hne, ?_⟩)
    rw [Matrix.mulVec_sub, huv, sub_self]
  have hrep : ∀ k, ∃ ρ : Γ →* GL (Fin n) O, Tw ρ r (A k) := fun k =>
    mkRep (A k) ((Units.coeHom _).comp r) (hinj k)
      (fun g v => (hA k _).1 (hst g k _ ((hA k _).2 ⟨v, rfl⟩)))
  choose ρ hρ using hrep
  have hbb : ∀ k : Fin R, ∃ Y, A k.succ * Y = A k.castSucc := fun k =>
    solve _ _ fun j => (hA k.succ _).1 (hmono (Fin.castSucc_lt_succ (i := k)).le
      ((hA k.castSucc _).2 ⟨Pi.single j 1, by funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]⟩))
  choose bb hbbe using hbb
  choose xs hxs hxn hsup hψ using hline
  have hsW : ∀ s w, ∃ u c', A (rs s).succ *ᵥ w = A (rs s).castSucc *ᵥ u + fun a => c' * xs s a := by
    intro s w
    have hm := (hA (rs s).succ _).2 ⟨w, rfl⟩
    rw [hsup s, Submodule.mem_sup] at hm
    obtain ⟨y, hy, z, hz, hyz⟩ := hm
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.1 hz
    obtain ⟨u, rfl⟩ := (hA _ _).1 hy
    exact ⟨u, c', by rw [← hyz]; rfl⟩
  have hxW : ∀ s, ∃ w, A (rs s).succ *ᵥ w = xs s := fun s => (hA _ _).1 (hxs s)
  have hcW : ∀ s u, ∃ w, A (rs s).succ *ᵥ w = A (rs s).castSucc *ᵥ u := fun s u =>
    (hA _ _).1 (hmono Fin.castSucc_lt_succ.le ((hA _ _).2 ⟨u, rfl⟩))
  have hnW : ∀ s, ¬ ∃ u, A (rs s).castSucc *ᵥ u = xs s := fun s h => hxn s ((hA _ _).2 h)
  have hψW : ∀ s g, ∃ u, A (rs s).castSucc *ᵥ u =
      (r g : Matrix (Fin n) (Fin n) O) *ᵥ xs s - fun a => ((ψ s g : Oˣ) : O) * xs s a :=
    fun s g => (hA _ _).1 (hψ s g)
  choose r2 B B' C E hL using fun s => GlobalTheory.T.matrix_fibre_product_stable_lattice_chain_line n r (ψ s) (A (rs s).castSucc) (A (rs s).succ) (ρ _) (ρ _)
    (xs s) (hinj _) (hinj _) (hρ _) (hρ _) (hsW s) (hxW s) (hcW s) (hψW s)
  refine ⟨⟨ρ, A, bb, r2, B, B', C, E⟩, fun k => ((A k).map (residue O)).rank,
    ⟨fun k => ⟨hρ k, hdet k, rfl⟩, fun k => ⟨?_, (hbbe k).symm⟩, fun s => hL s⟩, ?_, ?_,
    fun s => GlobalTheory.T.rank_residue_basis_matrix_succ_of_adjoin_vector n ϖ _ _ (xs s) hϖ (fun y => (hA _ _).1 (hin _ y)) (hsW s) (hxW s) (hcW s) (hnW s)⟩
  · intro g
    apply cancel_left (A k.succ) (hinj _)
    rw [← Matrix.mul_assoc, hbbe k, hρ k.castSucc g, ← hbbe k, ← Matrix.mul_assoc, ← hρ k.succ g,
      Matrix.mul_assoc]
  · have hz : (A 0).map (residue O) = 0 := by
      ext i j
      obtain ⟨y, hy⟩ := (hM0 _).1 ((hA 0 _).2 ⟨Pi.single j 1, rfl⟩)
      have hij : A 0 i j = ϖ * y i := by
        have h1 := congrFun hy i
        simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h1
      have hr : residue O ϖ = 0 :=
        (IsLocalRing.residue_eq_zero_iff ϖ).2 ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit)
      simp [hij, hr]
    simp [hz]
  · obtain ⟨S, hS⟩ := solve (A (Fin.last R)) (1 : Matrix (Fin n) (Fin n) O) fun j =>
      (hA _ _).1 (by rw [hlast]; trivial)
    exact (rank_of_mul_eq_one ((A (Fin.last R)).map (residue O)) (S.map (residue O))
      (by rw [← Matrix.map_mul, hS, Matrix.map_one _ (map_zero _) (map_one _)])).1

end GlobalTheory.WachChain
