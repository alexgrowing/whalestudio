import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.FixMulKer

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT boxA fouA intF)

variable {F : Type} [Field F] [NumberField F]

theorem add_mem_iff_of_zero {X : Type} [AddCommGroup X] {P : Set X} (h0 : (0 : X) ∈ P) {a b : X} (hab : a = 0 ∨ b = 0) :
    a + b ∈ P ↔ a ∈ P ∧ b ∈ P := by
  rcases hab with h | h <;> subst h <;> simp [h0]

theorem box_split {S S' : Finset (HeightOneSpectrum (𝓞 F))} (hSS : S ⊆ S') {ε : AF F} (hε : IsIdF S ε)
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, (0 : Fv F v) ∈ U v) {h y : AF F} (hh : ε * h = h)
    (hy : ε * y = 0) : sndA F (h + y) ∈ boxA S' U ↔ sndA F h ∈ boxA S' U ∧ sndA F y ∈ boxA S' U := by
  have hz : ∀ v, h.2 v = 0 ∨ y.2 v = 0 := fun v => by
    by_cases hv : v ∈ S
    · exact Or.inr (ker_snd hε hy hv)
    · exact Or.inl (fix_snd hε hh hv)
  have hadd : ∀ v, (sndA F (h + y)) v = h.2 v + y.2 v := fun v => rfl
  simp only [boxA, Set.mem_ofPred_eq, hadd]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun v hv => ((add_mem_iff_of_zero (hU v) (hz v)).1 (h1 v hv)).1,
      fun v hv => ((add_mem_iff_of_zero (zero_mem _) (hz v)).1 (h2 v hv)).1⟩,
      ⟨fun v hv => ((add_mem_iff_of_zero (hU v) (hz v)).1 (h1 v hv)).2,
      fun v hv => ((add_mem_iff_of_zero (zero_mem _) (hz v)).1 (h2 v hv)).2⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨fun v hv => (add_mem_iff_of_zero (hU v) (hz v)).2 ⟨h1 v hv, h3 v hv⟩,
      fun v hv => (add_mem_iff_of_zero (zero_mem _) (hz v)).2 ⟨h2 v hv, h4 v hv⟩⟩

def tR (ρ : Ainf F → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (y : AF F) : ℝ :=
  ρ (fstA F y) * (boxA S U).indicator (fun _ => (1 : ℝ)) (sndA F y)

theorem testT_eq (ρ : Ainf F → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (y : AF F) : testT ρ S U y = ((tR ρ S U y : ℝ) : ℂ) := by
  simp only [testT, tR, Set.indicator]
  split_ifs <;> simp

theorem tR_nonneg {ρ : Ainf F → ℝ} (hρ : ∀ y, 0 ≤ ρ y) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (y : AF F) : 0 ≤ tR ρ S U y :=
  mul_nonneg (hρ _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

def bR (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (y : AF F) : ℝ :=
  (boxA S U).indicator (fun _ => (1 : ℝ)) (sndA F y)

theorem tR_split {S S' : Finset (HeightOneSpectrum (𝓞 F))} (hSS : S ⊆ S') {ε : AF F} (hε : IsIdF S ε) (ρ : Ainf F → ℝ)
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, (0 : Fv F v) ∈ U v) {h y : AF F} (hh : ε * h = h)
    (hy : ε * y = 0) : tR ρ S' U (h + y) = tR ρ S' U h * bR S' U y := by
  have hf : fstA F (h + y) = fstA F h := by
    rw [map_add, fst_eq y, ker_fst hε hy, add_zero]
  have hb := box_split hSS hε U hU hh hy
  unfold tR bR
  rw [hf]
  by_cases h1 : sndA F h ∈ boxA S' U <;> by_cases h2 : sndA F y ∈ boxA S' U
  · rw [Set.indicator_of_mem (hb.2 ⟨h1, h2⟩), Set.indicator_of_mem h1, Set.indicator_of_mem h2]; ring
  · rw [Set.indicator_of_notMem (fun h' => h2 (hb.1 h').2), Set.indicator_of_notMem h2]; ring
  · rw [Set.indicator_of_notMem (fun h' => h1 (hb.1 h').1), Set.indicator_of_notMem h1]; ring
  · rw [Set.indicator_of_notMem (fun h' => h1 (hb.1 h').1), Set.indicator_of_notMem h1]; ring

end PositivityTheory.Rg.Rsw.L.LApproxId

end
