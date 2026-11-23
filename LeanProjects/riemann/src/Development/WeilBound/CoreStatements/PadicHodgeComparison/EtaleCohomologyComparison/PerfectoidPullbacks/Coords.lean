import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison.Pb

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']

structure QMor (Φ : PDF R C) (Φ' : PDF R C') (c : IdF Φ'.A) where
  G : C' ⥤ C
  ρ : ∀ T : C', Φ.A.obj (G.obj T) →ₐ[R] Φ'.A.obj T ⧸ c.S T
  inj : ∀ T, Function.Injective (ρ T)
  nat : ∀ {T T' : C'} (φ : T ⟶ T') (x : Φ.A.obj (G.obj T)) (y : Φ'.A.obj T), ρ T x = Ideal.Quotient.mk _ y →
    ρ T' ((Φ.A.map (G.map φ)).hom x) = Ideal.Quotient.mk _ ((Φ'.A.map φ).hom y)
  dp : ∀ (T : C') (k : ℕ) (x : Φ.A.obj (G.obj T)) (y : Φ'.A.obj T), x ∈ Φ.J.S _ → y ∈ Φ'.J.S T → ρ T x = Ideal.Quotient.mk _ y →
    ρ T (Φ.dp k x) = Ideal.Quotient.mk _ (Φ'.dp k y)

variable {Φ : PDF R C} {Φ' : PDF R C'} {c : IdF Φ'.A}

def QMor.o (m : QMor Φ Φ' c) (b : IdF Φ'.A) (h : ∀ T, c.S T ≤ b.S T) :
    CH.Mor (CH.modF Φ.A) (sq (IdF.top Φ'.A) b) (RingHom.id R) where
  G := m.G
  τ T :=
    { toFun := fun x => ⟨Ideal.Quotient.factor (h T) (m.ρ T x), by
        obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.factor (h T) (m.ρ T x))
        rw [← hy]
        exact Ideal.mem_map_of_mem _ trivial⟩
      map_add' := fun x y => Subtype.ext (by
        change Ideal.Quotient.factor (h T) (m.ρ T ((show Φ.A.obj _ from x) + (show Φ.A.obj _ from y))) = _
        rw [map_add, map_add]; rfl)
      map_smul' := fun r x => Subtype.ext (by
        change Ideal.Quotient.factorₐ R (h T) (m.ρ T (r • (show Φ.A.obj _ from x))) = r • Ideal.Quotient.factorₐ R (h T) (m.ρ T x)
        rw [map_smul, map_smul]) }
  nat φ x := by
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (m.ρ _ x)
    refine Subtype.ext ?_
    change Ideal.Quotient.factor (h _) (m.ρ _ ((Φ.A.map (m.G.map φ)).hom x)) =
      Ideal.quotientMapₐ _ (Φ'.A.map φ).hom (fun _ hx => b.map_mem φ hx) (Ideal.Quotient.factor (h _) (m.ρ _ x))
    rw [m.nat φ x y hy.symm, ← hy]
    rfl

def QMor.Fr (m : QMor Φ Φ' c) {d : ℕ} (E : Frame Φ d) (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D) : Prop :=
  ∀ (i : Fin d) {T : C'} (s s' : E'.D ⟶ T), m.ρ T (E.τ i (e ≫ m.G.map s) (e ≫ m.G.map s')) = Ideal.Quotient.mk _ (E'.τ i s s')

structure PDF.Mul (Φ : PDF R C) : Prop where
  smul : ∀ (T : C) (k : ℕ) (a x : Φ.A.obj T), x ∈ Φ.J.S T → Φ.dp k (a * x) = a ^ k * Φ.dp k x
  mul : ∀ (T : C) (i j : ℕ) (x : Φ.A.obj T), x ∈ Φ.J.S T → Φ.dp i x * Φ.dp j x = ((i + j).choose i : Φ.A.obj T) * Φ.dp (i + j) x

def Frame.Coords {d : ℕ} (E : Frame Φ d) (t : Fin d → Φ.A.obj E.D) : Prop :=
  ∀ (i : Fin d) {T : C} (s s' : E.D ⟶ T), E.τ i s s' = (Φ.A.map s').hom (t i) - (Φ.A.map s).hom (t i)

end CrystallineSemistableComparison.Pb
