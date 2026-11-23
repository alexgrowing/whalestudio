import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsCoefficientFieldOfFiniteLocalPadic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriCrys
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CocycleCrysAddAnn
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory

theorem tri_crys_push : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B' : Type} [CommRing B'] [IsLocalRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [TopologicalSpace B'] [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] {B : Type} [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] (q : B' →ₐ[ℚ_[l]] B) (e : ℕ), 1 ≤ e → ∀ (κ : Fin 3 → G →* B'ˣ), (∀ i, Continuous fun g => (κ i g : B')) → (∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B' (φ g) ^ ((e : ℤ) * wt1 i)) → ∀ (x y z : G → B') (ρ : G →* GL (Fin 3) B'), Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B') = triM (fun i => κ i g) (x g) (y g) (z g)) → x ∈ Z1 (chRep (κ 0 / κ 1)) → y ∈ Z1 (chRep (κ 1 / κ 2)) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → (∀ b, (((κ 0 / κ 1) σ : B'ˣ) - (cycA l l B' (φ σ) : B')) * b = 0 → q b = 0) → (∀ b, (((κ 1 / κ 2) σ : B'ˣ) - (cycA l l B' (φ σ) : B')) * b = 0 → q b = 0) → IsCr φ (colRep ((Matrix.GeneralLinearGroup.map (q : B' →+* B)).comp ρ)) := by
  intro hP l _ G _ _ _ φ hφ B' _ _ _ _ _ _ _ _ _ B _ _ _ _ q e he κ hκ hI x y z ρ hz hρ hx hy σ hσ hqx hqy

  obtain ⟨E', _, _, _, _, _, π', hπ'⟩ := GlobalTheory.exists_coefficientField_of_finite_local_padic (l := l) B'
  obtain ⟨E, _, _, _, _, _, π, hπ⟩ := GlobalTheory.exists_coefficientField_of_finite_local_padic (l := l) B
  letI : Algebra ℤ_[l] E' := ((algebraMap ℚ_[l] E').comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] E' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra ℤ_[l] E := ((algebraMap ℚ_[l] E).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra ℤ_[l] B := ((algebraMap ℚ_[l] B).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B

  have hqc : Continuous (q : B' → B) := IsModuleTopology.continuous_of_linearMap (q.toLinearMap)
  let qm : B' →* B := (q : B' →+* B)
  let κB : Fin 3 → G →* Bˣ := fun i => (Units.map qm).comp (κ i)
  have hqcyc : ∀ h : GQ l, Units.map qm (cycA l l B' h) = cycA l l B h := by
    intro h
    apply Units.ext
    change q (algebraMap ℤ_[l] B' _) = algebraMap ℚ_[l] B (algebraMap ℤ_[l] ℚ_[l] _)
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B', q.commutes]

  have hw01 : ∀ g, φ g ∈ Iq l → (κ 0 / κ 1) g = cycA l l B' (φ g) ^ (e : ℤ) := by
    intro g hg
    rw [MonoidHom.div_apply, hI g hg 0, hI g hg 1]
    simp [wt1]
  have hw12 : ∀ g, φ g ∈ Iq l → (κ 1 / κ 2) g = cycA l l B' (φ g) ^ (e : ℤ) := by
    intro g hg
    rw [MonoidHom.div_apply, hI g hg 1, hI g hg 2]
    simp [wt1]
  have hcdiv : ∀ i j, Continuous fun g => (((κ i / κ j) g : B'ˣ) : B') := by
    intro i j
    have : (fun g => (((κ i / κ j) g : B'ˣ) : B')) = fun g => (κ i g : B') * (κ j g⁻¹ : B') := by
      funext g
      rw [MonoidHom.div_apply, div_eq_mul_inv, Units.val_mul, ← map_inv]
    rw [this]
    exact (hκ i).mul ((hκ j).comp continuous_inv)
  have he : (1 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he

  obtain ⟨cx, hcx, hxf, -⟩ := GlobalTheory.CrysAnn.cocycle_crys_add_ann hP φ hφ π' hπ' (κ 0 / κ 1) (hcdiv 0 1) e he hw01 σ hσ x hx
  obtain ⟨cy, hcy, hyf, -⟩ := GlobalTheory.CrysAnn.cocycle_crys_add_ann hP φ hφ π' hπ' (κ 1 / κ 2) (hcdiv 1 2) e he hw12 σ hσ y hy
  have push : ∀ (i j : Fin 3) (c : G → B'), c ∈ finiteCocycles φ (chRep (κ i / κ j)) →
      (fun g => q (c g)) ∈ finiteCocycles φ (chRep (κB i / κB j)) := by
    intro i j c hc
    refine (z1fMap φ (chRep (κ i / κ j)) (chRep (κB i / κB j))).2 q.toLinearMap (fun g v => ?_) c hc
    show q ((((κ i / κ j) g : B'ˣ) : B') * v) = (((κB i / κB j) g : Bˣ) : B) * q v
    rw [map_mul]
    congr 1
    simp only [κB, MonoidHom.div_apply, MonoidHom.comp_apply, ← _root_.map_div, Units.coe_map]
    rfl
  have hxB : (fun g => q (x g)) ∈ finiteCocycles φ (chRep (κB 0 / κB 1)) := by
    have h := push 0 1 _ hxf
    convert h using 2 with g
    simp [hqx _ (hcx g)]
  have hyB : (fun g => q (y g)) ∈ finiteCocycles φ (chRep (κB 1 / κB 2)) := by
    have h := push 1 2 _ hyf
    convert h using 2 with g
    simp [hqy _ (hcy g)]
  refine GlobalTheory.tri_crys hP φ hφ π hπ e (by exact_mod_cast he) κB (fun i => hqc.comp (hκ i)) ?_ (fun g => q (x g))
    (fun g => q (y g)) (fun g => q (z g)) ((Matrix.GeneralLinearGroup.map (q : B' →+* B)).comp ρ) (hqc.comp hz) ?_ hxB hyB
  · intro g hg i
    simp only [κB, MonoidHom.comp_apply, hI g hg i, map_zpow, hqcyc]
  · intro g
    rw [MonoidHom.comp_apply]
    show (ρ g : Matrix (Fin 3) (Fin 3) B').map q = _
    rw [hρ g]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, κB, qm]

end GlobalTheory
