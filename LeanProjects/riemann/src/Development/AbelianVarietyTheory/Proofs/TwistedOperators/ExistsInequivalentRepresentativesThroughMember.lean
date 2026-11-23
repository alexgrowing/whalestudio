import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrUnion

theorem exists_reps_through : ∀ (G : Type) [Group G] [TopologicalSpace G] (m : ℕ) (W : Fin m → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (σ : ∀ i, Representation ℂ G (W i)), ∀ i₀ : Fin m, ∃ (n : ℕ) (s : Fin n → Fin m), (∀ i j, i ≠ j → IsEmpty ((σ (s i)).Equiv (σ (s j)))) ∧ (∃ j, s j = i₀) ∧ ∀ i, ∃ j, Nonempty ((σ i).Equiv (σ (s j))) := by
  intro G _ _ m W _ _ σ i₀
  classical
  let R : Fin m → Fin m → Prop := fun i j => Nonempty ((σ i).Equiv (σ j))
  have hrefl : ∀ i, R i i := fun i => ⟨Representation.Equiv.refl _⟩
  have hsymm : ∀ {i j}, R i j → R j i := fun ⟨e⟩ => ⟨e.symm⟩
  have htrans : ∀ {i j k}, R i j → R j k → R i k := fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩
  let S : Setoid (Fin m) := ⟨R, ⟨hrefl, hsymm, htrans⟩⟩
  let f : Fin m → Fin m := fun i => if R i i₀ then i₀ else (Quotient.mk S i).out
  have hf : ∀ i, R (f i) i := by
    intro i
    by_cases h : R i i₀
    · simp only [f, if_pos h]; exact hsymm h
    · simp only [f, if_neg h]; exact Quotient.mk_out (s := S) i
  have hfc : ∀ i j, R i j → f i = f j := by
    intro i j hij
    by_cases h : R i i₀
    · have h' : R j i₀ := htrans (hsymm hij) h
      simp only [f, if_pos h, if_pos h']
    · have h' : ¬ R j i₀ := fun h' => h (htrans hij h')
      simp only [f, if_neg h, if_neg h']
      rw [Quotient.sound (s := S) hij]
  let T : Finset (Fin m) := Finset.univ.image f
  let e : T ≃ Fin T.card := T.equivFin
  refine ⟨T.card, fun k => (e.symm k).1, ?_, ?_, ?_⟩
  · intro k l hkl
    refine ⟨fun hR => ?_⟩
    apply hkl
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 (e.symm k).2
    obtain ⟨y, -, hy⟩ := Finset.mem_image.1 (e.symm l).2
    have hxy : R x y := by
      have h1 : R (f x) (f y) := by rw [hx, hy]; exact ⟨hR⟩
      exact htrans (hsymm (hf x)) (htrans h1 (hf y))
    have : (e.symm k).1 = (e.symm l).1 := by rw [← hx, ← hy]; exact hfc x y hxy
    exact e.symm.injective (Subtype.ext this)
  · have hmem : i₀ ∈ T := Finset.mem_image.2 ⟨i₀, Finset.mem_univ _, by simp only [f, if_pos (hrefl i₀)]⟩
    exact ⟨e ⟨i₀, hmem⟩, by simp⟩
  · intro i
    have hmem : f i ∈ T := Finset.mem_image_of_mem f (Finset.mem_univ i)
    refine ⟨e ⟨f i, hmem⟩, ?_⟩
    show R i (e.symm (e ⟨f i, hmem⟩)).1
    rw [Equiv.symm_apply_apply]
    exact hsymm (hf i)

end GlobalTheory.TrUnion
