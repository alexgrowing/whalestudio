import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
  GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.CoeffExt

namespace GlobalTheory.PstExt

section Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
  {LL LL' : Type} [Field LL] [Field LL'] [Algebra ℚ_[l] LL] [Algebra ℚ_[l] LL']
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
  [Module LL' V'] [IsScalarTower ℚ_[l] LL' V']
  {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL' ↥(GK K) V'}
  {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[LL] (ι → V)}

theorem tensCoord_mulV (c : ↥(MaximalUnramifiedExtension l)) (x : V' ⊗[ℚ_[l]] Bst P) (i : ι) :
    tensCoord E (Bst P) (mulV P LL' V' c x) i = mulV P LL V c (tensCoord E (Bst P) x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

variable (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i))
include hE

theorem tensCoord_stRep (g : ↥(GK K)) (x : V' ⊗[ℚ_[l]] Bst P) (i : ι) :
    tensCoord E (Bst P) (stRep P ρ' g x) i = stRep P ρ g (tensCoord E (Bst P) x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [hE]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem mem_Dpst_coord (x : V' ⊗[ℚ_[l]] Bst P) :
    x ∈ Dpst P ρ' ↔ ∀ i, tensCoord E (Bst P) x i ∈ Dpst P ρ := by
  constructor
  · intro hx i
    obtain ⟨K', hK⟩ := (mem_Dpst P ρ').1 hx
    exact (mem_Dpst P ρ).2 ⟨K', fun g hg => by rw [← tensCoord_stRep P hE, hK g hg]⟩
  · intro hx
    choose K' hK using fun i => (mem_Dpst P ρ).1 (hx i)
    have hsum : x = ∑ i, (tensCoord E (Bst P)).symm (Pi.single i (tensCoord E (Bst P) x i)) := by
      apply (tensCoord E (Bst P)).injective
      rw [map_sum]
      simp only [LinearEquiv.apply_symm_apply]
      exact (Finset.univ_sum_single _).symm
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => (mem_Dpst P ρ').2 ⟨K' i, fun g hg => (tensCoord E (Bst P)).injective ?_⟩
    funext j
    rw [tensCoord_stRep P hE, LinearEquiv.apply_symm_apply]
    by_cases h : j = i
    · subst h
      simp [hK j g hg]
    · simp [Pi.single_eq_of_ne h]

def dpstCoord : DpstUr P ρ' ≃ₗ[↥(MaximalUnramifiedExtension l)] (ι → DpstUr P ρ) where
  toFun x i := toUr P ρ ⟨tensCoord E (Bst P) ((toUr P ρ').symm x).1 i,
    (mem_Dpst_coord P hE _).1 ((toUr P ρ').symm x).2 i⟩
  invFun y := toUr P ρ' ⟨(tensCoord E (Bst P)).symm fun i => ((toUr P ρ).symm (y i)).1,
    (mem_Dpst_coord P hE _).2 fun i => by
      rw [LinearEquiv.apply_symm_apply]
      exact ((toUr P ρ).symm (y i)).2⟩
  map_add' x y := by
    funext i
    exact Subtype.ext (congrFun (map_add (tensCoord E (Bst P)) x.1 y.1) i)
  map_smul' c x := by
    funext i
    exact Subtype.ext (tensCoord_mulV P c x.1 i)
  left_inv x := Subtype.ext ((tensCoord E (Bst P)).symm_apply_apply x.1)
  right_inv y := by
    funext i
    exact Subtype.ext (congrFun ((tensCoord E (Bst P)).apply_symm_apply fun i => (y i).1) i)

theorem isPst_of_coord (h : IsPst P ρ) : IsPst P ρ' := by
  unfold IsPst at h ⊢
  rw [(dpstCoord P hE).rank_eq, (E.restrictScalars ℚ_[l]).rank_eq, rank_fun, rank_fun, h]

end Coord

theorem isPst_enlarge : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) {m : ℕ} {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1) (r₁ : ↥Gw →* GL (Fin m) ↥L₁.1),
    IsPst P (Bw.repE L₁ r₁) → IsPst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) := by
  intro l _ P E Ω _ _ _ Gw O _ _ _ Bw m L₁ L₂ hL r₁ h
  let _ : Algebra ↥L₁.1 ↥L₂.1 := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥L₁.1 ↥L₂.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L₂.2
  have : FiniteDimensional ↥L₁.1 ↥L₂.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  have hρ : ∀ g, ∃ M : Matrix (Fin m) (Fin m) ↥L₁.1, (∀ x, Bw.repE L₁ r₁ g x = M.mulVec x) ∧
      ∀ x, Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x =
        (M.map (algebraMap ↥L₁.1 ↥L₂.1)).mulVec x :=
    fun g => ⟨r₁ (Bw.e.symm g), fun _ => rfl, fun _ => rfl⟩
  exact isPst_of_coord P (E := vecCoord ↥L₁.1 ↥L₂.1 m) (vecCoord_rep hρ) h

end GlobalTheory.PstExt
