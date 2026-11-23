import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiltByRestrictScalarsOfResidualCharacters
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.PosModule

theorem main : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (χ : G →* Bˣ), Continuous (fun g => (χ g : B)) → ∀ w : ℤ, 1 ≤ w → (∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w) → ∀ {N : Type} [AddCommGroup N] [Module B N] [Module E N] [Module ℚ_[l] N] [IsScalarTower E B N] [IsScalarTower ℚ_[l] E N] [IsScalarTower ℚ_[l] B N] [FiniteDimensional ℚ_[l] N] [TopologicalSpace N] [IsModuleTopology ℚ_[l] N] [IsTopologicalAddGroup N] (ρ : Representation E G N), (∀ g x, ρ g x = (χ g : B) • x) → ContAction ρ ∧ Positive φ ρ := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ χ hχc w hw hχI N _ _ _ _ _ _ _ _ _ _ _ ρ hρ

  let bil : B →ₗ[ℚ_[l]] N →ₗ[ℚ_[l]] N := LinearMap.mk₂ ℚ_[l] (fun b x => b • x) (fun _ _ _ => add_smul _ _ _)
    (fun c b x => smul_assoc c b x) (fun _ _ _ => smul_add _ _ _)
    (fun c b x => by rw [← algebraMap_smul B c x, ← algebraMap_smul B c (b • x), smul_smul, smul_smul, mul_comm])
  have hbil : Continuous (fun p : B × N => p.1 • p.2) := IsModuleTopology.continuous_bilinear_of_finite_left bil
  have hcont : ContAction ρ := by
    unfold ReciprocityTheory.Gal.ContAction
    simp only [hρ]
    exact hbil.comp ((hχc.comp continuous_fst).prodMk continuous_snd)
  refine ⟨hcont, ?_⟩
  have hcs : ContinuousConstSMul E N := ⟨fun c => by
    let f : N →ₗ[ℚ_[l]] N :=
      { toFun := fun x => c • x
        map_add' := smul_add c
        map_smul' := fun r x => by
          simp only [RingHom.id_apply]
          rw [← algebraMap_smul E r x, ← algebraMap_smul E r (c • x), smul_smul, smul_smul, mul_comm] }
    exact IsModuleTopology.continuous_of_linearMap f⟩
  have hIne : ∀ g, φ g ∈ Iq l → ∀ x, ρ g x = ((cycA l l E (φ g) ^ w : Eˣ) : E) • x := fun g hg x => by
    rw [hρ, hχI g hg, ← algebraMap_smul B (((cycA l l E (φ g) ^ w : Eˣ) : E)) x,
      ← algebraMap_cycA (E := E) (B := B), ← map_zpow]
    rfl
  have hcr : IsCr φ ρ := crUnr φ hφ ρ hcont w hIne
  have hdr : IsDr φ ρ := (isCrys_isDR_restrict_openSubgroup φ hφ ρ hcont).1 hcr
  refine ⟨hdr, ?_⟩

  have : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have : Module.Finite B N := Module.Finite.of_restrictScalars_finite ℚ_[l] B N
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := B) (M := N)
  let ρB : Representation B G N :=
    { toFun := fun g => ((χ g : Bˣ) : B) • LinearMap.id
      map_one' := by ext; simp
      map_mul' := fun g h => by
        refine LinearMap.ext fun x => ?_
        simp only [map_mul, Units.val_mul, LinearMap.smul_apply, LinearMap.id_apply, Module.End.mul_apply, mul_smul] }
  let κ : G →* Eˣ := (Units.map (π : B →* E)).comp χ
  have hres : resCoef E ρB = ρ := by
    refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
    rw [hρ]
    rfl
  have hκ : κ ∈ {κ : G →* Eˣ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} := by
    refine ⟨w, hw, ⊤, by simp, fun g _ hg => ?_⟩
    apply Units.ext
    change π ((χ g : Bˣ) : B) = _
    rw [hχI g hg, ← algebraMap_cycA (E := E) (B := B), ← map_zpow]
    exact π.commutes _
  rw [← hres]
  refine UpperTheory.filtBy_restrictScalars_of_residual_characters π hπ ρB _ s (fun _ => κ) hs (fun _ => hκ) fun g j => ?_
  have hm : ((χ g : B) - algebraMap E B (π (χ g : B))) • s j ∈ (RingHom.ker (π : B →+* E)) • (⊤ : Submodule B N) :=
    Submodule.smul_mem_smul (by simp) trivial
  convert hm using 1
  rw [sub_smul, algebraMap_smul]
  rfl

end GlobalTheory.PosModule
