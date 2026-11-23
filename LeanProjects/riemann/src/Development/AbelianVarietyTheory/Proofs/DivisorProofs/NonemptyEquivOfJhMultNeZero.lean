import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsDataDualGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaCellSemisimplificationGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelativeJacquetFunctorPiTensorEquivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockRepEquivFirst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorProductDeterminesFactorClasses
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.RegMult

theorem jhMult_cell_eq_zero_of_row {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h : ℕ} {d : Fin h → ℕ} {X : Fin h → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] {ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)}
    (hc : ∀ a, IsCuspidal (ρ a)) (b : SizeMatrix (fun a => Fin (d a)) (fun a => Fin (d a)))
    {i j j' : Fin h} (hjj : j < j') (hj : b.1 i j ≠ 0) (hj' : b.1 i j' ≠ 0)
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d j))
    {Y : Type} [AddCommGroup Y] [Module ℂ Y] {τ : Representation ℂ (Levi k fun a => Fin (d a)) Y}
    (hτ : τ.IsIrreducible) : jhMult τ (cellFunctor f g (piTensor ρ)) = 0 := by
  have hne : unipRad k (f i) ≠ ⊥ := by
    rw [GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff]
    refine ⟨f i ⟨j, ⟨0, Nat.pos_of_ne_zero hj⟩⟩, f i ⟨j', ⟨0, Nat.pos_of_ne_zero hj'⟩⟩, ?_⟩
    simpa [blk_apply] using hjj
  haveI hs : Subsingleton (Jacquet (ρ i) (unipRad k (f i))) := (hc i).2 h (fun j => b.1 i j) (f i) hne
  haveI := GlobalTheory.SmGL.CellSemis.subsingleton_piTensor
    (X := fun a => Jacquet (ρ a) (unipRad k (f a))) i
  obtain ⟨φ⟩ := GlobalTheory.T.relative_jacquet_functor_piTensor_equiv k (Fin h) (Fin h) (fun a => Fin (d a)) (fun i j => Fin (b.1 i j)) f X ρ
  haveI : Subsingleton (Jacquet (piTensor ρ) (relUnip k f)) := φ.toLinearEquiv.injective.subsingleton
  exact GlobalTheory.SmGL.CellSemis.jhMult_relInd_of_subsingleton g _ hτ

end GlobalTheory.RegMult

noncomputable section

namespace GlobalTheory.RegMult

def glCast (R : Type) [CommRing R] {n m : ℕ} (h : n = m) : GL (Fin n) R ≃* GL (Fin m) R :=
  h ▸ MulEquiv.refl _

def permHom (R : Type) [CommRing R] {α : Type} (d : α → ℕ) (σ : α ≃ α) (hσ : ∀ i, d (σ i) = d i) :
    Levi R (fun a => Fin (d a)) →* Levi R (fun a => Fin (d a)) where
  toFun p i := glCast R (hσ i) (p (σ i))
  map_one' := funext fun i => map_one (glCast R (hσ i))
  map_mul' p q := funext fun i => map_mul (glCast R (hσ i)) (p (σ i)) (q (σ i))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.RegMult

end

noncomputable section

namespace GlobalTheory.RegMult

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.RegMult

end

namespace GlobalTheory.RegMult

theorem exists_perm {h : ℕ} {d : Fin h → ℕ} (hd : ∀ a, 0 < d a)
    (b : SizeMatrix (fun a => Fin (d a)) (fun a => Fin (d a)))
    (hrow : ∀ i j j', b.1 i j ≠ 0 → b.1 i j' ≠ 0 → j = j') :
    ∃ σ : Fin h ≃ Fin h, (∀ i, d (σ i) = d i) ∧ (∀ i j, j ≠ σ i → b.1 i j = 0) ∧ ∀ i, b.1 i (σ i) = d i := by
  have hr : ∀ i, ∑ j, b.1 i j = d i := fun i => by simpa using b.2.1 i
  have hc : ∀ j, ∑ i, b.1 i j = d j := fun j => by simpa using b.2.2 j
  have h1 : ∀ i, ∃ j, b.1 i j ≠ 0 := fun i => by
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero ((hr i).trans_ne (hd i).ne')
    exact ⟨j, hj⟩
  choose s hs using h1
  have hz : ∀ i j, j ≠ s i → b.1 i j = 0 := fun i j hj => by_contra fun h0 => hj (hrow i _ _ h0 (hs i))
  have hsurj : Function.Surjective s := fun j => by
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero ((hc j).trans_ne (hd j).ne')
    exact ⟨i, hrow i _ _ (hs i) hi⟩
  have hinj : Function.Injective s := Finite.injective_iff_surjective.2 hsurj
  have hb : ∀ i, b.1 i (s i) = d i := fun i => by
    rw [← hr i, Finset.sum_eq_single (s i) (fun j _ hj => hz i j hj) (by simp)]
  refine ⟨Equiv.ofBijective s ⟨hinj, hsurj⟩, fun i => ?_, hz, hb⟩
  show d (s i) = d i
  rw [← hc, Finset.sum_eq_single i (fun a _ ha => hz a _ fun e => ha (hinj e).symm) (by simp), hb]

theorem nonempty_equiv_of_jhMult_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (hσ : σ.IsIrreducible)
    (hρ : ρ.IsIrreducible) (h : jhMult σ ρ ≠ 0) : Nonempty (ρ.Equiv σ) :=
  (jhMult_ne_zero_iff.1 h).nonempty_equiv hσ hρ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

noncomputable def cellMult {h : ℕ} {d : Fin h → ℕ} (s : ∀ a, IrrRep (GL (Fin (d a)) k)) (b : Fin h → Fin h → ℕ)
    (f : ∀ i, (Σ j, Fin (b i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b i j)) ≃ Fin (d j)) : ℕ∞ :=
  jhMult (piTensor fun a => (s a).ρ) (cellFunctor (m := fun a => Fin (d a)) (m' := fun a => Fin (d a))
    f g (piTensor fun a => (s a).ρ))

end GlobalTheory.RegMult
