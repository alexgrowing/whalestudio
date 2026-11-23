import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MatrixExtendByZeroApply
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

theorem UpperTheory.isCrystalline_upperTriangular_iff_mem_finiteCocycles :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (κ : Fin 3 → G →* Bˣ), (∀ i, Continuous fun g => (κ i g : B)) → ∀ (x y z : G → B) (ρ : G →* GL (Fin 3) B), Continuous x → Continuous y → Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) → ∀ hx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h, IsCr φ (ext2 (κ 0) (κ 1) x hx) → IsCr φ (chRep (κ 2)) → (IsCr φ (colRep ρ) ↔ (fun g => (z g, y g)) ∈ UpperTheory.V.Loc.finiteCocycles φ (twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx))) := by
  intro l _ G _ _ _ φ hφ B _ _ _ _ _ _ κ hκ x y z ρ cx cy cz hρ hx h1 h2
  have hc : Continuous fun g => (ρ g : Matrix (Fin 3) (Fin 3) B) := by
    simp only [hρ]
    exact continuous_triM (t := fun g i => κ i g) hκ cx cy cz
  let f : (B × B) →ₗ[B] (Fin 3 → B) :=
    { toFun := fun v => ![v.1, v.2, 0]
      map_add' := fun v w => by ext i; fin_cases i <;> simp
      map_smul' := fun c v => by ext i; fin_cases i <;> simp }
  have hf : ∀ v, f v = ![v.1, v.2, 0] := fun _ => rfl
  rw [← crOn_top]
  refine crExt φ hφ (ext2 (κ 0) (κ 1) x hx) (colRep ρ) (contAction_charExtension_of_continuous_cocycle (hκ 0) (hκ 1) hx cx)
    (contAction_colRep hc) (κ 2) f (LinearMap.proj 2) ![0, 0, 1] (fun g => (z g, y g)) ?_ ?_ ?_ ?_ ?_ ⊤
    (by simp) ((crOn_top _ _).2 h1) ((crOn_top _ _).2 h2)
  · intro v w h
    exact Prod.ext (congrFun h 0) (congrFun h 1)
  · intro v
    constructor
    · intro h
      refine ⟨(v 0, v 1), ?_⟩
      have h' : v 2 = 0 := h
      ext i
      fin_cases i <;> simp [hf, h']
    · rintro ⟨w, rfl⟩
      rfl
  · rfl
  · intro g v
    rw [colRep_apply, hρ, characterExtensionRep_apply]
    ext i
    fin_cases i <;> simp [hf, triM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · intro g
    rw [colRep_apply, hρ]
    ext i
    fin_cases i <;> simp [hf, triM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_comm]
