import Development.EtaleCohomology.EtaleSheaves.LeafTw0GenFreeOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0TwFreePf

def aug (q : ℕ) (A : CommRingCat.{0}) : (twF q 0).obj A →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Submodule.liftQ (twRel q 0 A) (Finsupp.linearCombination (ULift.{1} (ZMod q)) (fun _ => (1 : ULift.{1} (ZMod q)))) (by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ, ξ, a, _, rfl⟩
    simp [SetLike.mem_coe, LinearMap.mem_ker, Finsupp.linearCombination_single]
    exact sub_self (1 : ULift.{1} (ZMod q)))

theorem aug_mk (q : ℕ) (A : CommRingCat.{0}) (ζ : Prim q A) :
    aug q A (Submodule.Quotient.mk (Finsupp.single ζ 1)) = 1 := by
  show Finsupp.linearCombination (ULift.{1} (ZMod q)) (fun _ => (1 : ULift.{1} (ZMod q))) (Finsupp.single ζ 1) = 1
  rw [Finsupp.linearCombination_single, one_smul]

theorem aug_map (q : ℕ) (A B : CommRingCat.{0}) (g : A ⟶ B) (ζ : Prim q A) :
    aug q B (((twF q 0).map g).hom (Submodule.Quotient.mk (Finsupp.single ζ 1))) = 1 := by
  show aug q B (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.hom) (Finsupp.single ζ 1))) = 1
  rw [Finsupp.mapDomain_single]
  exact aug_mk q B _

theorem LeafTw0TwFree_of : LateralTheory.E.LeafTw0LocSplitPfM.LeafTw0TwFree := by
  intro q _ V ζ
  let P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) := Scheme.Γ ⋙ twF q 0
  let x : P.obj (op V) := (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q 0).obj Γ(V, ⊤))
  let φ := ((toSheafify Scheme.etaleTopology P).app (op V)).hom
  by_cases hS : ∃ (c : ULift.{1} (ZMod q)), c • twGen 0 ζ = 0 ∧ c ≠ 0
  · obtain ⟨c, hc, hc0⟩ := hS
    have heq : φ (c • x) = φ 0 := by
      rw [φ.map_smul, φ.map_zero]; exact hc
    have hmem := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) (c • x) 0 heq
    by_cases hne : ∃ (U : Scheme.{0}) (f : U ⟶ V), (Presheaf.equalizerSieve (F := P) (X := op V) (c • x) 0).arrows f
    · exfalso
      obtain ⟨U, f, hf⟩ := hne
      apply hc0
      have h1 : (P.map f.op).hom (c • x) = (P.map f.op).hom 0 := hf
      rw [(P.map f.op).hom.map_smul, (P.map f.op).hom.map_zero] at h1
      let y : (twF q 0).obj Γ(U, ⊤) := ((twF q 0).map (Scheme.Γ.map f.op)).hom (Submodule.Quotient.mk (Finsupp.single ζ 1))
      have h3 : aug q Γ(U, ⊤) y = 1 := aug_map q _ _ _ ζ
      have h4 : aug q Γ(U, ⊤) (c • y) = c • aug q Γ(U, ⊤) y := (aug q _).map_smul c y
      have h5 : c • y = 0 := h1
      rw [h5, h3, map_zero, smul_eq_mul, mul_one] at h4
      exact h4.symm
    · left
      push Not at hne
      exact (tw q 0).isSeparated V _ hmem _ _ (fun U f hf => absurd hf (hne U f))
  · right
    intro c hc
    by_contra h0
    exact hS ⟨c, hc, h0⟩

end LateralTheory.E.LeafTw0TwFreePf
