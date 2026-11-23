import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell faceSign)

open Classical in

def constD (K : Type*) [Fintype K] [LinearOrder K] (ι : K → Type*) [∀ k, LinearOrder (ι k)] (V : Type*)
    [AddCommGroup V] (n : ℕ) (f : Cell K ι n → V) : Cell K ι (n + 1) → V :=
  fun I => ∑ k, ∑ i ∈ I.1 k,
    if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
      faceSign I.1 k i • f ⟨Function.update I.1 k ((I.1 k).erase i), h⟩
    else 0

def CechConstVanish.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, LinearOrder (ι k)] (V : Type) [AddCommGroup V]
    (G : ∀ k, Finset (ι k)) (z : Cell K ι 1 → V),
    (∀ I : Cell K ι 2, (∀ k, I.1 k ⊆ G k) → constD K ι V 1 z I = 0) →
    ∃ f : Cell K ι 0 → V, ∀ J : Cell K ι 1, (∀ k, J.1 k ⊆ G k) → constD K ι V 0 f J = z J

theorem constVanish_hyp_segment :
    ∀ I : Cell Unit (fun _ => Fin 2) 2, (∀ k, I.1 k ⊆ Finset.univ) →
      constD Unit (fun _ => Fin 2) ℤ 1 (fun _ => 1) I = 0 := by
  intro I _
  exfalso
  have h : (I.1 ()).card - 1 = 2 := by simpa using I.2.2
  have hc : (I.1 ()).card ≤ 2 := by simpa using Finset.card_le_univ (I.1 ())
  omega

example (h : CechConstVanish.Statement) :=
  h Unit (fun _ => Fin 2) ℤ (fun _ => Finset.univ) (fun _ => 1) constVanish_hyp_segment

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
