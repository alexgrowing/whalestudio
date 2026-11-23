import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory

theorem prod_comp_eq_of_finite_family {S : Type} (A : Finset (S → ℂ)) (a : S → S)
    (h : ∀ f ∈ A, ∃ f' ∈ A, f = f' ∘ a) (w : ℂ) (x : S) :
    ∏ f ∈ A, (w - f (a x)) = ∏ f ∈ A, (w - f x) := by
  classical
  choose! φ hφA hφ using h
  have hinj : Set.InjOn φ A := fun f hf k hk hfk => by rw [hφ f hf, hφ k hk, hfk]
  have himg : A.image φ = A := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hy
      exact hφA f hf
    · rw [Finset.card_image_of_injOn hinj]
  calc ∏ f ∈ A, (w - f (a x)) = ∏ f ∈ A.image φ, (w - f (a x)) := by rw [himg]
    _ = ∏ f ∈ A, (w - φ f (a x)) := Finset.prod_image hinj
    _ = ∏ f ∈ A, (w - f x) :=
        Finset.prod_congr rfl (fun f hf => congrArg (w - ·) (congrFun (hφ f hf) x).symm)

theorem differentiableOn_finite_prod {K E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {s : Set E} (A : Finset K) {f : K → E → ℂ} (h : ∀ i ∈ A, DifferentiableOn ℂ (f i) s) :
    DifferentiableOn ℂ (fun x => ∏ i ∈ A, f i x) s := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert j B hj ih =>
    simp only [Finset.prod_insert hj]
    exact (h j (Finset.mem_insert_self j B)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem const_of_finite_family_spAct :
    Key.PhHoloStatement → ∀ (g : ℕ) (I : Type) [Finite I] (F : I → Matrix (Fin g) (Fin g) ℂ → ℂ), 2 ≤ g → (∀ i, Key.IsHoloSiegel g (F i)) → (∀ sp ∈ Matrix.symplecticGroup (Fin g) ℤ, ∀ i, ∃ j, ∀ τ ∈ ReciprocityTheory.PTheta.SiegelH (Fin g), F i τ = F j (Key.Chi.spAct sp τ)) → ∀ i, ∃ c, ∀ τ ∈ ReciprocityTheory.PTheta.SiegelH (Fin g), F i τ = c := by
  intro hPh g I _ F hg hF h i
  classical
  have : Fintype I := Fintype.ofFinite I
  let S := ReciprocityTheory.PTheta.SiegelH (Fin g)
  have hmem : ∀ τ ∈ S, τ.IsSymm ∧ (τ.map Complex.im).PosDef := fun τ hτ => hτ
  let G : I → (S → ℂ) := fun j τ => F j τ
  let A : Finset (S → ℂ) := Finset.univ.image G
  have hGA : ∀ j, G j ∈ A := fun j => Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hA : ∀ f ∈ A, ∃ j, G j = f := fun f hf => by simpa [A] using hf
  have : Nonempty I := ⟨i⟩
  choose! rep hrep using hA
  have heval : ∀ f ∈ A, ∀ τ (hτ : τ ∈ S), F (rep f) τ = f ⟨τ, hτ⟩ :=
    fun f hf τ hτ => congrFun (hrep f hf) ⟨τ, hτ⟩
  have hsym : ∀ τ ∈ S, Key.phSym τ = τ := by
    intro τ hτ
    have ht : Matrix.transpose τ = τ := (hmem τ hτ).1.eq
    simp only [Key.phSym, ht]
    ext p q
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hholo : ∀ w : ℂ, Key.IsHoloSiegel g (fun τ => ∏ f ∈ A, (w - F (rep f) τ)) := by
    intro w
    exact differentiableOn_finite_prod A
      (f := fun f x => w - F (rep f) (Key.phSym (Matrix.of x)))
      (fun f _ => (differentiableOn_const w).sub (hF (rep f)))
  have hinv : ∀ w : ℂ, Key.IsSpInvariant g (fun τ => ∏ f ∈ A, (w - F (rep f) τ)) := by
    intro w gm hgm τ hτ
    choose J hJ using h gm hgm
    let act : S → S := fun σ => ⟨Key.Chi.spAct gm σ, Key.Chi.spAct_mem hgm σ.2⟩
    have hfam : ∀ f ∈ A, ∃ f' ∈ A, f = f' ∘ act := by
      intro f hf
      refine ⟨G (J (rep f)), hGA _, ?_⟩
      funext σ
      exact (congrFun (hrep f hf) σ).symm.trans (hJ (rep f) σ.1 σ.2)
    have hstep := prod_comp_eq_of_finite_family A act hfam w ⟨τ, hτ⟩
    have hact : Key.phAct gm τ = Key.Chi.spAct gm τ := rfl
    show ∏ f ∈ A, (w - F (rep f) (Key.phAct gm τ)) = ∏ f ∈ A, (w - F (rep f) τ)
    calc ∏ f ∈ A, (w - F (rep f) (Key.phAct gm τ)) = ∏ f ∈ A, (w - f (act ⟨τ, hτ⟩)) :=
          Finset.prod_congr rfl (fun f hf => by rw [hact, heval f hf _ (Key.Chi.spAct_mem hgm hτ)])
      _ = ∏ f ∈ A, (w - f ⟨τ, hτ⟩) := hstep
      _ = ∏ f ∈ A, (w - F (rep f) τ) :=
          Finset.prod_congr rfl (fun f hf => by rw [heval f hf τ hτ])
  by_cases hne : S.Nonempty
  swap
  · exact ⟨0, fun τ hτ => (hne ⟨τ, hτ⟩).elim⟩
  obtain ⟨τ0, hτ0⟩ := hne
  refine ⟨F i τ0, fun τ hτ => ?_⟩
  have hval : ∀ τ ∈ S, F i τ ∈ ((A.image (fun f => F (rep f) τ0) : Finset ℂ) : Set ℂ) := by
    intro τ hτ
    obtain ⟨c, hc⟩ := hPh g hg _ (hholo (F i τ)) (hinv (F i τ))
    have h0 : ∏ f ∈ A, (F i τ - F (rep f) τ) = 0 := by
      apply Finset.prod_eq_zero (hGA i)
      rw [heval _ (hGA i) τ hτ]
      exact sub_self _
    have h1 : ∏ f ∈ A, (F i τ - F (rep f) τ0) = 0 := (hc τ0 hτ0).trans ((hc τ hτ).symm.trans h0)
    obtain ⟨f, hf, hz⟩ := Finset.prod_eq_zero_iff.1 h1
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨f, hf, (sub_eq_zero.1 hz).symm⟩)
  have hcont : ContinuousOn (F i) S := by
    have hc0 := (hF i).continuousOn
    refine (hc0.mono (fun σ hσ => ?_)).congr (fun σ hσ => ?_)
    · show Key.phSym σ ∈ S
      rw [hsym σ hσ]
      exact hσ
    · show F i σ = F i (Key.phSym σ)
      rw [hsym σ hσ]
  have hconv : Convex ℝ S := by
    intro x hx y hy s t hs ht hst
    obtain ⟨hx1, hx2⟩ := hmem x hx
    obtain ⟨hy1, hy2⟩ := hmem y hy
    change Matrix.IsSymm (s • x + t • y) ∧ ((s • x + t • y).map Complex.im).PosDef
    refine ⟨(hx1.smul s).add (hy1.smul t), ?_⟩
    have hm : (s • x + t • y).map Complex.im = s • x.map Complex.im + t • y.map Complex.im := by
      ext p q
      simp
    rw [hm]
    rcases hs.lt_or_eq with hs' | hs'
    · exact (hx2.smul hs').add_posSemidef (hy2.posSemidef.smul ht)
    · subst hs'
      rw [zero_add] at hst
      subst hst
      simpa using hy2
  exact hconv.isPreconnected.constant_of_mapsTo DiscreteTopology.isDiscrete hcont
    (fun σ hσ => hval σ hσ) hτ hτ0

end GlobalTheory
