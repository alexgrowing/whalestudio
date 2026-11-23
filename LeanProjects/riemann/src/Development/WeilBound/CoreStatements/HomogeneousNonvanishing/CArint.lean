import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexConjugationHermCompatStatement
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CPtsat

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem c_arint : SheetIndepStatement → PtsIndepStatement → GoodProjExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn P A s → arInt P s (conjLine A) (fun j => conjLine (L j)) = arInt P s A L := by
  intro hS hP hG K _ ι _ P e L A s hV hL hA hs
  have hex := hG K ι P e hV
  have hgood : IsGoodProj P hex.choose := hex.choose_spec
  let Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] Fin (e + 1) → ℂ :=
    { toFun := fun w i => starRingEnd ℂ (hex.choose (fun c => starRingEnd ℂ (w c)) i)
      map_add' := by
        intro a b
        have h : (fun c => starRingEnd ℂ ((a + b) c)) =
            (fun c => starRingEnd ℂ (a c)) + (fun c => starRingEnd ℂ (b c)) := by
          funext c
          simp
        funext i
        show starRingEnd ℂ (hex.choose (fun c => starRingEnd ℂ ((a + b) c)) i) = _
        rw [h, map_add]
        simp
      map_smul' := by
        intro r a
        have h : (fun c => starRingEnd ℂ ((r • a) c)) =
            starRingEnd ℂ r • (fun c => starRingEnd ℂ (a c)) := by
          funext c
          simp
        funext i
        show starRingEnd ℂ (hex.choose (fun c => starRingEnd ℂ ((r • a) c)) i) = _
        rw [h, map_smul]
        simp }
  have hΨ' : ∀ (w : ((k : K) → ι k) → ℂ) (i : Fin (e + 1)),
      Ψ' w i = starRingEnd ℂ (hex.choose (fun c => starRingEnd ℂ (w c)) i) := fun _ _ => rfl
  obtain ⟨hgood', heq⟩ := c_ptsat hS K ι P e hex.choose Ψ' L A s hV hgood hΨ' hL hA hs
  have hcs : ∀ B : HermLine ι, IsSmoothHerm B → IsSmoothHerm (conjLine B) := by
    intro B hB
    have hmaps : Set.MapsTo (conjPt : ((k : K) × ι k → ℂ) → (k : K) × ι k → ℂ)
        {z : (k : K) × ι k → ℂ | ∀ (k : K), ∃ (i : ι k), z ⟨k, i⟩ ≠ 0}
        {z : (k : K) × ι k → ℂ | ∀ (k : K), ∃ (i : ι k), z ⟨k, i⟩ ≠ 0} := by
      intro z hz k
      obtain ⟨i, hi⟩ := hz k
      exact ⟨i, by simpa [conjPt] using hi⟩
    have hc : ContDiff ℝ (↑(⊤ : ℕ∞)) (conjPt : ((k : K) × ι k → ℂ) → (k : K) × ι k → ℂ) := by
      refine contDiff_pi.2 fun p => ?_
      have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z : (k : K) × ι k → ℂ => z p) := contDiff_apply ℝ ℂ p
      have h2 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℂ => starRingEnd ℂ x) := by
        have h3 : (fun x : ℂ => starRingEnd ℂ x) = (Complex.conjCLE : ℂ → ℂ) := by
          funext x
          simp
        rw [h3]
        exact Complex.conjCLE.contDiff
      exact h2.comp h1
    have hB' : ContDiffOn ℝ (↑(⊤ : ℕ∞)) B.h
        {z : (k : K) × ι k → ℂ | ∀ (k : K), ∃ (i : ι k), z ⟨k, i⟩ ≠ 0} := hB
    exact hB'.comp hc.contDiffOn hmaps
  have hLc : ∀ j, IsSmoothHerm (conjLine (L j)) := fun j => hcs _ (hL j)
  have hAc : IsSmoothHerm (conjLine A) := hcs _ hA
  have hsc : IsSectionOn P (conjLine A) s := by
    obtain ⟨a, ha, h2⟩ := hs
    exact ⟨a, ha, h2⟩
  have hind := hP K ι P e hex.choose Ψ' (fun j => conjLine (L j)) (conjLine A) s hV hgood hgood'
    hLc hAc hsc
  unfold arInt ptsIntegral
  rw [dif_pos hex, dif_pos hex]
  exact hind.trans heq

end PositivityTheory.UnitarySelfGeneration
