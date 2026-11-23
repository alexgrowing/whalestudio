import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussGLZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVecExistsUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameMatrixIntegralOfConjugateHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualHalfLatticeDetectingCharacter
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
namespace GlobalTheory.ZRepBlock

theorem zrep_block : ∀ (D : D7) (S T : HSp D) {m k : ℕ} (Λ Λ' : AddSubgroup (WO S T)) (e : AE D) (Q : Finset (Pl D.host.E)) (fm : WO S T → Matrix (Fin m) (Fin k) (EAf D)), (∀ w w', fm (w - w') = fm w - fm w') → (∀ w, IsHalf e w → (w ∈ Λ ↔ IsIntM (fm w))) → (∀ w ∈ Λ, ∀ w' ∈ Λ, IsHalf e w → IsHalf e w' → (w - w' ∈ Λ' ↔ ∀ PP ∈ Q, redM PP (fm w) = redM PP (fm w'))) → (∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin m) (Fin k) (kP PP), ∃ w, IsHalf e w ∧ IsIntM (fm w) ∧ ∀ PP ∈ Q, redM PP (fm w) = Y PP) → ∃ X : Finset (WO S T), (∀ x ∈ X, x ∈ Λ ∧ IsHalf e x) ∧ (∀ w ∈ Λ, IsHalf e w → ∃! x, x ∈ X ∧ w - x ∈ Λ') ∧ X.card = (∏ PP ∈ Q, Nat.card (kP PP)) ^ (m * k) ∧ (∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin m) (Fin k) (kP PP), ∃! x, x ∈ X ∧ ∀ PP ∈ Q, redM PP (fm x) = Y PP) := by
  intro D S T m k Λ Λ' e Q fm _hsub H1 H2 H3
  classical

  let Ix := ∀ PP : Q, Matrix (Fin m) (Fin k) (kP (PP : Pl D.host.E))
  haveI : ∀ PP : Pl D.host.E, Fintype (kP PP) := fun PP => Fintype.ofFinite _
  let ext : Ix → ∀ PP : Pl D.host.E, Matrix (Fin m) (Fin k) (kP PP) :=
    fun Y PP => if h : PP ∈ Q then Y ⟨PP, h⟩ else 0
  choose w hwh hwi hwr using H3
  let g : Ix → WO S T := fun Y => w (ext Y)
  have hgr : ∀ Y : Ix, ∀ PP (h : PP ∈ Q), redM PP (fm (g Y)) = Y ⟨PP, h⟩ := by
    intro Y PP h
    have := hwr (ext Y) PP h
    simpa [g, ext, h] using this
  have hginj : Function.Injective g := by
    intro Y Y' hYY
    funext PP
    rw [← hgr Y PP.1 PP.2, ← hgr Y' PP.1 PP.2, hYY]
  have hgΛ : ∀ Y, g Y ∈ Λ ∧ IsHalf e (g Y) :=
    fun Y => ⟨(H1 _ (hwh _)).2 (hwi _), hwh _⟩
  refine ⟨Finset.univ.image g, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hgΛ Y
  · intro v hv hvh
    let Y : Ix := fun PP => redM (PP : Pl D.host.E) (fm v)
    refine ⟨g Y, ⟨Finset.mem_image.2 ⟨Y, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · refine (H2 v hv (g Y) (hgΛ Y).1 hvh (hgΛ Y).2).2 ?_
      intro PP h
      rw [hgr Y PP h]
    · rintro x ⟨hx, hvx⟩
      obtain ⟨Y', -, rfl⟩ := Finset.mem_image.1 hx
      congr 1
      funext PP
      have h1 := (H2 v hv (g Y') (hgΛ Y').1 hvh (hgΛ Y').2).1 hvx PP.1 PP.2
      rw [hgr Y' PP.1 PP.2] at h1
      exact h1.symm
  · rw [Finset.card_image_of_injective _ hginj, Finset.card_univ, Fintype.card_pi]
    calc ∏ i : Q, Fintype.card (Fin m → Fin k → kP (i : Pl D.host.E))
        = ∏ i : Q, Nat.card (kP (i : Pl D.host.E)) ^ (m * k) := by
          refine Finset.prod_congr rfl (fun i _ => ?_)
          simp only [Fintype.card_fun, Fintype.card_fin, Nat.card_eq_fintype_card]
          ring
      _ = (∏ PP ∈ Q, Nat.card (kP PP)) ^ (m * k) := by
          rw [Finset.prod_pow, Finset.prod_coe_sort Q (fun PP => Nat.card (kP PP))]
  · intro Y
    let Y' : Ix := fun PP => Y PP
    refine ⟨g Y', ⟨Finset.mem_image.2 ⟨Y', Finset.mem_univ _, rfl⟩, fun PP h => hgr Y' PP h⟩, ?_⟩
    rintro x ⟨hx, hxr⟩
    obtain ⟨Y'', -, rfl⟩ := Finset.mem_image.1 hx
    congr 1
    funext PP
    rw [← hgr Y'' PP.1 PP.2, hxr PP.1 PP.2]

end GlobalTheory.ZRepBlock
