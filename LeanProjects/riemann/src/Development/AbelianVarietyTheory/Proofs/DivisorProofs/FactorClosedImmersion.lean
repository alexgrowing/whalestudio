import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

noncomputable section

namespace GlobalTheory.PDivGroup

variable {p : ℕ} {k : Type} [CommRing k]

def liftClosed {K G H : PDivGroup p k} (i : K ⟶ G) (hi : ∀ n : ℕ, Function.Surjective (i.app n))
    (f : H ⟶ G) (hf : ∀ n : ℕ, RingHom.ker (i.app n) ≤ RingHom.ker (f.app n)) : H ⟶ K :=
  ⟨fun n => liftSurj (i.app n) (hi n) (f.app n) (hf n), fun n => BialgHom.ext fun b => by
    obtain ⟨a, rfl⟩ := hi (n + 1) b
    change H.res n (liftSurj (i.app (n + 1)) (hi (n + 1)) (f.app (n + 1)) (hf (n + 1))
        (i.app (n + 1) a)) =
      liftSurj (i.app n) (hi n) (f.app n) (hf n) (K.res n (i.app (n + 1) a))
    rw [liftSurj_apply, res_app, res_app, liftSurj_apply]⟩

theorem liftClosed_comp {K G H : PDivGroup p k} (i : K ⟶ G)
    (hi : ∀ n : ℕ, Function.Surjective (i.app n)) (f : H ⟶ G)
    (hf : ∀ n : ℕ, RingHom.ker (i.app n) ≤ RingHom.ker (f.app n)) :
    liftClosed i hi f hf ≫ i = f :=
  hom_ext fun n => BialgHom.ext fun a => liftSurj_apply (i.app n) (hi n) (f.app n) (hf n) a

theorem cancel_closed {K G H : PDivGroup p k} (i : K ⟶ G)
    (hi : ∀ n : ℕ, Function.Surjective (i.app n)) (g g' : H ⟶ K) (h : g ≫ i = g' ≫ i) :
    g = g' :=
  hom_ext fun n => BialgHom.ext fun b => by
    obtain ⟨a, rfl⟩ := hi n b
    have := DFunLike.congr_fun (congrArg (fun u : H ⟶ G => u.app n) h) a
    simpa using this

end GlobalTheory.PDivGroup

theorem GlobalTheory.PDivGroup.factor_closedImmersion : ∀ (p : ℕ) (k : Type) [CommRing k] (K G : PDivGroup p k) (i : K ⟶ G), (∀ n : ℕ, Function.Surjective (i.app n)) → (∀ (H : PDivGroup p k) (f : H ⟶ G), (∀ n : ℕ, RingHom.ker (i.app n) ≤ RingHom.ker (f.app n)) → ∃ g : H ⟶ K, g ≫ i = f) ∧ ∀ (H : PDivGroup p k) (g g' : H ⟶ K), g ≫ i = g' ≫ i → g = g' :=
  fun _ _ _ _ _ i hi => ⟨fun _ f hf => ⟨liftClosed i hi f hf, liftClosed_comp i hi f hf⟩,
    fun _ g g' h => cancel_closed i hi g g' h⟩
