import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.Vert.Flag

theorem isSubbundle_ι_comp {X : Scheme.{0}} {E K : X.Modules} {i : K ⟶ E} {r : ℕ}
    (hi : IsSubbundle i) (fl : Vert.Flag K r) (j : Fin (r + 1)) : IsSubbundle (fl.ι j ≫ i) := by
  have := hi.mono
  obtain ⟨s, hs⟩ := hi.isVB_cokernel
  obtain ⟨h, -⟩ := VBExt.isVB_and_cls_det_of_shortExact X _ _ _
    (Vert.shortExact_cokernel_comp (fl.ι j) i) (fl.isVB_cokernel j) hs
  exact ⟨inferInstance, _, h⟩

theorem nonempty_extend : ∀ (X : Scheme.{0}) (E K : X.Modules) (i : K ⟶ E) (r : ℕ),
    IsSubbundle i → IsVB E (r + 1) → Vert.Flag K r → Nonempty (Vert.Flag E (r + 1)) := by
  intro X E K i r hi hE fl

  let G : Fin (r + 2) → Σ A : X.Modules, (A ⟶ E) :=
    fun j => Fin.lastCases (motive := fun _ => Σ A : X.Modules, (A ⟶ E)) ⟨E, 𝟙 E⟩
      (fun k => ⟨fl.F k, fl.ι k ≫ i⟩) j
  have hlast : G (Fin.last (r + 1)) = ⟨E, 𝟙 E⟩ := Fin.lastCases_last ..
  have hcast (k : Fin (r + 1)) : G k.castSucc = ⟨fl.F k, fl.ι k ≫ i⟩ :=
    Fin.lastCases_castSucc ..
  have hsub (j : Fin (r + 2)) : IsSubbundle (G j).2 := by
    induction j using Fin.lastCases with
    | last => rw [hlast]; exact VB.isSubbundle_of_isIso _
    | cast k => rw [hcast]; exact isSubbundle_ι_comp hi fl k
  have hvb (j : Fin (r + 2)) : IsVB (G j).1 j := by
    induction j using Fin.lastCases with
    | last => rw [hlast]; exact hE
    | cast k => rw [hcast]; exact fl.isVB k
  have hstep (k : Fin (r + 1)) :
      ∃ f : (G k.castSucc).1 ⟶ (G k.succ).1, f ≫ (G k.succ).2 = (G k.castSucc).2 := by
    induction k using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, hlast, hcast]
      exact ⟨fl.ι _ ≫ i, Category.comp_id _⟩
    | cast k =>
      rw [← Fin.castSucc_succ, hcast, hcast]
      exact ⟨fl.step k, fl.step_ι_assoc k i⟩
  choose step step_ι using hstep
  have hiso : IsIso (G (Fin.last (r + 1))).2 := by
    rw [hlast]; exact IsIso.id E
  exact ⟨{ F := fun j => (G j).1
           ι := fun j => (G j).2
           isSubbundle := hsub
           isVB := hvb
           step := step
           step_ι := step_ι
           isIso_last := hiso }⟩

end GlobalTheory.Vert.Flag
