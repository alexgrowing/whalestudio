import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.FixBdQZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.DdSumZero
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private def ddBaseCompRingHom (X : Type) [CommRing X] (g : ℕ) : DD X g →+* X where
  toFun := DD.a
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private theorem sandwich_map_smul {R X : Type} [CommRing R] [CommRing X] {n : ℕ} (α : R → X) (φ : R →+ X)
    (c : R) (P Z Q : Matrix (Fin n) (Fin n) R) (h : ∀ i j u, φ (u * Z i j) = α u * φ (Z i j))
    (hα : ∀ u v, α (u * v) = α u * α v) :
    (c • (P * Z * Q)).map φ = α c • (P.map α * Z.map φ * Q.map α) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    map_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [show c * (P i a * Z a b * Q b j) = (c * (P i a * Q b j)) * Z a b by ring, h, hα, hα]
  ring

private theorem rho1_map_ddBaseCompRingHom_eq_mat {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (g : F.G₀) :
    (k.ρ1 x.A g).map (ddBaseCompRingHom x.A k.g) = mat x.ρ g := by
  have h1 : (1 + DD.epM fun j => (k.κ j g).map (algebraMap x.A x.A)).map (ddBaseCompRingHom x.A k.g) = 1 := by
    rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]
    exact add_eq_left.2 (Matrix.ext fun _ _ => rfl)
  rw [Kap.ρ1, Matrix.map_mul, h1, one_mul]
  exact Matrix.ext fun _ _ => rfl

private theorem rho1_map_algebraMap_am_eq_rho1 {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (m : ℕ) (g : F.G₀) :
    (k.ρ1 x.A g).map (fun y => (⟨algebraMap x.A (x.Am m) y.a, fun j => algebraMap x.A (x.Am m) (y.ep j),
      fun j => algebraMap x.A (x.Am m) (y.ep' j), algebraMap x.A (x.Am m) y.eta⟩ : DD (x.Am m) k.g)) =
      k.ρ1 (x.Am m) g := by
  change (x.redD k.g m).mapMatrix (k.ρ1 x.A g) = _
  rw [Kap.ρ1, Kap.ρ1, map_mul, map_add, map_one]
  refine congrArg₂ (· * ·) (congrArg (1 + ·) (Matrix.ext fun i j => ?_)) (Matrix.ext fun i j => ?_)
  · ext <;> simp [DD.epM]
  · exact (x.redD k.g m).commutes _

private theorem site_vector_first {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (D : Subgroup F.G₀)
    (h4 : x.N4 D) (Z : Matrix (Fin n) (Fin n) (DD x.A k.g)) (ha : ∀ i j, (Z i j).a = 0) (he : ∀ i j, (Z i j).ep = 0)
    (hZ : ∀ g ∈ D, epsD k x.A g • (k.ρ1 x.A g * Z * k.ρ1 x.A g⁻¹) = Z) : Z = 0 := by
  have key : ∀ φ : DD x.A k.g →+ x.A, (∀ i j u, φ (u * Z i j) = u.a * φ (Z i j)) → ∀ i j, φ (Z i j) = 0 := by
    intro φ hφ
    have : Z.map φ = 0 := by
      refine h4 _ fun g hg => ?_
      have e := sandwich_map_smul (ddBaseCompRingHom x.A k.g) φ (epsD k x.A g) (k.ρ1 x.A g) Z (k.ρ1 x.A g⁻¹) hφ (map_mul _)
      rw [hZ g hg, rho1_map_ddBaseCompRingHom_eq_mat, rho1_map_ddBaseCompRingHom_eq_mat] at e
      conv_rhs => rw [e]
      rw [smul_mul_assoc, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
      rfl
    exact fun i j => congrFun (congrFun this i) j
  have h' : ∀ t i j, (Z i j).ep' t = 0 := fun t =>
    key ⟨⟨fun y => y.ep' t, rfl⟩, fun _ _ => rfl⟩ fun i j u => by
      show (u * Z i j).ep' t = u.a * (Z i j).ep' t
      simp [ha]
  have h'' : ∀ i j, (Z i j).eta = 0 :=
    key ⟨⟨fun y => y.eta, rfl⟩, fun _ _ => rfl⟩ fun i j u => by
      show (u * Z i j).eta = u.a * (Z i j).eta
      simp [ha, he, h']
  refine Matrix.ext fun i j => ?_
  ext <;> simp [ha, he, h', h'']

theorem UpperTheory.V.Pa.h0v0 :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (D : Subgroup F.G₀), x.N4 D → ∃ C : ℕ, ∀ (m : ℕ), {Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) | Y ∈ k.EpsilonEtaTensorDual (x.Am m) ∧ ∀ g ∈ D, epsD k (x.Am m) g • (k.ρ1 (x.Am m) g * Y * k.ρ1 (x.Am m) g⁻¹) = Y}.ncard ≤ Nat.card x.K ^ C := by
  intro l _ F n x k D h4
  obtain ⟨C, hC⟩ := UpperTheory.V.Pa.fixBd l F n x k _ false false false true false false true false D
    (fun s => algebraMap ℤ_[l] x.A (F.ε (s : F.G₀) : ℤ_[l])) (fun s => k.ρ1 x.A s) (fun s => k.ρ1 x.A (s : F.G₀)⁻¹)
    false rfl
  refine ⟨C, fun m => ?_⟩
  have h := hC m
  rw [(Submodule.eq_bot_iff (_ ⊓ _ ⊓ _)).2 ?_, finrank_bot, mul_zero, zero_add] at h
  · refine le_of_eq_of_le ?_ h
    congr 1
    ext Y
    simp only [Set.mem_setOf_eq, rho1_map_algebraMap_am_eq_rho1, Subtype.forall, epsD, algebraMap_smul, Bool.false_eq_true, false_imp_iff,
      true_and]
    rfl
  · rintro Z ⟨⟨h1, -⟩, h2⟩
    refine site_vector_first k D h4 Z (fun i j => ?_) (fun i j => ?_) fun g hg => ?_
    · by_cases e : ((i : ℕ) < x.a) ↔ ((j : ℕ) < x.a)
      · exact ((h1 i j).1 e).1 rfl
      · exact ((h1 i j).2 e).1 rfl
    · by_cases e : ((i : ℕ) < x.a) ↔ ((j : ℕ) < x.a)
      · exact ((h1 i j).1 e).2.1 rfl
      · exact ((h1 i j).2 e).2.1 rfl
    · have e := (Submodule.mem_iInf _).1 h2 ⟨g, hg⟩
      rw [epsD, algebraMap_smul, mul_assoc, ← sub_eq_zero]
      exact e
