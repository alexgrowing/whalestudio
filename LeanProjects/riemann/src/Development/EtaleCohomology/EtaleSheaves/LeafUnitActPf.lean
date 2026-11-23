import Development.EtaleCohomology.EtaleSheaves.LeafUnitPairGPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitActPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafUnitPairGPf

def LeafActSheaf : Prop := ∀ (q : ℕ) [NeZero q], ∃ L : ∀ (F : Shv (ZMod q)) (U : Scheme.{0}),
    Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)] Sec F U →ₗ[ULift.{1} (ZMod q)] Sec F U,
  (∀ (F : Shv (ZMod q)) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec (tw q 0) U) (b : Sec F U),
      Sec.res g (L F U a b) = L F V (Sec.res g a) (Sec.res g b)) ∧
  (∀ {F G : Shv (ZMod q)} (φ : F ⟶ G) (U : Scheme.{0}) (a : Sec (tw q 0) U) (b : Sec F U),
      Sec.map φ (L F U a b) = L G U a (Sec.map φ b)) ∧
  ∀ (F : Shv (ZMod q)) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (b : Sec F U), L F U (twGen 0 ζ) b = b

theorem LeafUnitAct_of (h : LeafActSheaf) : LeafUnitAct := by
  intro q _ i
  obtain ⟨L, hU, hF, hζ⟩ := h q
  refine ⟨fun U t => L ((res _ (tw q i)).X t) U, ⟨fun g t a b => hU _ g a b, fun U t a b => hF _ U a b⟩,
    fun U t ζ b => hζ _ U ζ b⟩

end LateralTheory.E.LeafUnitActPf
