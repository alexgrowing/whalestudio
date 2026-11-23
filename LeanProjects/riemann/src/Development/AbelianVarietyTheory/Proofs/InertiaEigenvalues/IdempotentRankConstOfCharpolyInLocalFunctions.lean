import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing Polynomial

namespace GlobalTheory.IdemConstRank

theorem charpoly_of_idem {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : M * M = M) :
    ∃ b : ℕ, M.charpoly = (X - 1) ^ M.rank * X ^ b := by
  classical
  have hf : IsIdempotentElem (Matrix.toLin' M) := by
    have h2 : Matrix.toLin' (M * M) = Matrix.toLin' M := by rw [h]
    rw [Matrix.toLin'_mul] at h2
    exact h2
  have hc := LinearMap.IsIdempotentElem.isCompl hf
  let e := Submodule.prodEquivOfIsCompl _ _ hc
  have key : e.conj ((1 : Module.End K (LinearMap.range (Matrix.toLin' M))).prodMap
      (0 : Module.End K (LinearMap.ker (Matrix.toLin' M)))) = Matrix.toLin' M := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.prodMap_apply, Module.End.one_apply, LinearMap.zero_apply]
    rw [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', map_add,
      LinearMap.mem_ker.mp y.2.2, (LinearMap.IsIdempotentElem.mem_range_iff hf).mp y.1.2]
    simp
  refine ⟨Module.finrank K (LinearMap.ker (Matrix.toLin' M)), ?_⟩
  have hcp : M.charpoly = (e.conj ((1 : Module.End K (LinearMap.range (Matrix.toLin' M))).prodMap
      (0 : Module.End K (LinearMap.ker (Matrix.toLin' M))))).charpoly := by
    rw [key, Matrix.charpoly_toLin']
  rw [hcp, LinearEquiv.charpoly_conj, LinearMap.charpoly_prodMap,
    LinearMap.charpoly_one, LinearMap.charpoly_zero, Matrix.rank, ← Matrix.toLin'_apply']

theorem residue_eq {X O : Type} [CommRing O] [IsLocalRing O] (T : Subalgebra O (X → O))
    [IsLocalRing T] (f : X → O) (hf : f ∈ T) (x y : X) :
    IsLocalRing.residue O (f x) = IsLocalRing.residue O (f y) := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  by_contra hne
  have hu : IsUnit (f x - f y) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hne
    exact hne
  have ev : ∀ z : X, ∀ t : T, IsUnit t → IsUnit ((t : X → O) z) := fun z t ht =>
    ht.map ((Pi.evalRingHom (fun _ : X => O) z).comp T.val.toRingHom)
  let g : T := ⟨f - algebraMap O (X → O) (f y), T.sub_mem hf (T.algebraMap_mem _)⟩
  let g' : T := algebraMap O T (f x - f y) - g
  have hg : g ∈ nonunits T := fun hg => by
    have := ev y g hg
    simp [g] at this
  have hg' : g' ∈ nonunits T := fun hg => by
    have := ev x g' hg
    simp [g', g] at this
  have hsum : g + g' = algebraMap O T (f x - f y) := by
    simp [g']
  exact IsLocalRing.nonunits_add hg hg' (hsum ▸ hu.map (algebraMap O T))

theorem rootMultiplicity_one {k : Type} [Field k] (a b : ℕ) :
    rootMultiplicity (1 : k) ((X - 1) ^ a * X ^ b) = a := by
  have h1 : ((Polynomial.X : k[X]) - 1) ^ a = (Polynomial.X - Polynomial.C 1) ^ a := by
    rw [map_one]
  have hne : ((Polynomial.X : k[X]) - Polynomial.C 1) ^ a * Polynomial.X ^ b ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero 1)) (pow_ne_zero _ X_ne_zero)
  rw [h1, rootMultiplicity_mul hne, rootMultiplicity_X_sub_C_pow, rootMultiplicity_eq_zero, add_zero]
  simp [IsRoot]

theorem rank_eq_rootMultiplicity {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) O) (h : M * M = M) :
    (M.map (toFr O)).rank = rootMultiplicity 1 (M.charpoly.map (IsLocalRing.residue O)) := by
  obtain ⟨b, hb⟩ := charpoly_of_idem (M.map (toFr O)) (by rw [← Matrix.map_mul, h])
  rw [Matrix.charpoly_map] at hb
  have hinj : Function.Injective (toFr O) := IsFractionRing.injective O (FractionRing O)
  have hM : M.charpoly = ((Polynomial.X : O[X]) - 1) ^ (M.map (toFr O)).rank * Polynomial.X ^ b := by
    apply Polynomial.map_injective _ hinj
    rw [hb]
    simp
  rw [hM]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_one]
  exact (rootMultiplicity_one _ _).symm

theorem rank_const : ∀ {X O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {n : ℕ} (T : Subalgebra O (X → O)) (e : X → Matrix (Fin n) (Fin n) O), IsLocalRing T → e * e = e → (∀ j : ℕ, (fun x => (e x).charpoly.coeff j) ∈ T) → ∀ x y, ((e x).map (toFr O)).rank = ((e y).map (toFr O)).rank := by
  intro X O _ _ _ n T e hT he hc x y
  have hx := rank_eq_rootMultiplicity (e x) (congrFun he x)
  have hy := rank_eq_rootMultiplicity (e y) (congrFun he y)
  have hp : (e x).charpoly.map (IsLocalRing.residue O) = (e y).charpoly.map (IsLocalRing.residue O) := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    exact residue_eq T (fun z => (e z).charpoly.coeff j) (hc j) x y
  rw [hx, hy, hp]

end GlobalTheory.IdemConstRank
