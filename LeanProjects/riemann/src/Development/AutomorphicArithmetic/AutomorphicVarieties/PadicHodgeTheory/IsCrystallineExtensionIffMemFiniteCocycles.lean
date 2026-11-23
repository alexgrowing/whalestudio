import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MatrixExtendByZeroApply
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

theorem UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (a b : G →* Bˣ), Continuous (fun g => (a g : B)) → Continuous (fun g => (b g : B)) → ∀ (x : G → B) (hx : ∀ g h, x (g * h) = x g + ((a / b) g : Bˣ) * x h), Continuous x → IsCr φ (chRep a) → IsCr φ (chRep b) → (IsCr φ (ext2 a b x hx) ↔ x ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (a / b))) := by
  intro l _ G _ _ _ φ hφ B _ _ _ _ _ _ a b ha hb x hx hc h1 h2
  have key := UpperTheory.V.Loc.crExt φ hφ (chRep a) (ext2 a b x hx) (contAction_chRep ha) (contAction_charExtension_of_continuous_cocycle ha hb hx hc)
    b (LinearMap.inl B B B) (LinearMap.snd B B B) (0, 1) x LinearMap.inl_injective Function.Exact.inl_snd rfl
    (fun g v => by simp [characterExtensionRep_apply, chRep_apply]) (fun g => by simp [characterExtensionRep_apply, mul_comm])
    ⊤ (by simp) ((crOn_top φ _).2 h1) ((crOn_top φ _).2 h2)
  have e : twist b⁻¹ (chRep a) = chRep (a / b) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    rw [twist_apply, chRep_apply, chRep_apply, div_eq_mul_inv, MonoidHom.mul_apply, Units.val_mul, smul_eq_mul]
    ring
  rwa [crOn_top, e] at key
