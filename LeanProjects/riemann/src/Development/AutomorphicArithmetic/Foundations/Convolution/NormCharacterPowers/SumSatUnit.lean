import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.OrderAsym
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChangeLifts.SplitLift

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Published UpperTheory.CBC PositivityTheory.RgJS

namespace UpperTheory.ConvolutionTheory.R

def sumSat {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {ι : Type} [Fintype ι] {m : ι → ℕ} (P : ∀ i, CG E (m i))
    (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  ∃ B' : ι → Multiset ℂˣ, (∀ i, (P i).HasSat w (B' i)) ∧ B = ∑ i, B' i

theorem sumSat_unit {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} (P : CG E n) :
    sumSat (m := fun _ : Unit => n) (fun _ => P) = P.HasSat := by
  funext w B
  exact propext ⟨fun ⟨B', h, e⟩ => by simpa [e] using h (), fun h => ⟨fun _ => B, fun _ => h, by simp⟩⟩

def ForCyc (Q : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsTotallyComplex K]
    [IsTotallyComplex M], Prop) : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M] [IsTotallyComplex K]
    [IsTotallyComplex M], (Module.finrank K M).Prime → Q K M

def IsGenChar {K : Type} (M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (η : HChar K) : Prop :=
  IsNormChar M η ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, η.UnrAt (w.under (𝓞 K)) ∧
    (normV w = normV (w.under (𝓞 K)) ∨ IsPrimitiveRoot (η.val (w.under (𝓞 K))) (Module.finrank K M))

def ClassChar : Prop := ForCyc fun K M => ∃ η : HChar K, IsGenChar M η

def Decomp : Prop := ForCyc fun K M => ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
  (Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} = Module.finrank K M ∧
    ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v → normV w = normV v) ∨
  (Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} = 1 ∧
    ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v → normV w = normV v ^ Module.finrank K M)

def SysEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (X : Set (Σ a, CG E a)), X.Finite →
  (∀ x ∈ X, 1 ≤ x.1 ∧ x.2.IsUnitary ∧ ∀ᶠ w in Filter.cofinite, ∃ B, x.2.HasSat w B) →
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 E)), ∀ S, S₀ ⊆ S → ∃ α : ∀ x : X, Off E S → Fin x.1.1 → ℂˣ,
      (∀ x : X, SatOff x.1.2 S (α x)) ∧ Sys nq X (fun x => x.1.1) fun x w a => (α x w a : ℂ)

def CoverEx : Prop := ForCyc fun K M => ∀ η : HChar K, IsGenChar M η → ∀ (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
  (T₀ : Finset (HeightOneSpectrum (𝓞 M))), ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 M)))
    (u : Off M T → Off K S) (f : Off M T → ℕ), S₀ ⊆ S ∧ T₀ ⊆ T ∧ (∀ w, (u w).1 = w.1.under (𝓞 K)) ∧ (∀ v : Off K S, η.UnrAt v.1) ∧
      (∀ w, normV w.1 = normV (u w).1 ^ f w) ∧ Cover (Module.finrank K M) nq nq u f fun v => (η.val v.1 : ℂ)

open Classical in

def Count : Prop := ForCyc fun K M => ∀ η : HChar K, IsGenChar M η → ∀ (n : ℕ) (π π₁ : CG K n) (ι : Type) [Fintype ι] (m : ι → ℕ)
  (P : ∀ i, CG M (m i)), 1 ≤ n → (∀ i, 1 ≤ m i) → WeakBC π.HasSat (sumSat P) → WeakBC π₁.HasSat (sumSat P) →
    ((Finset.range (Module.finrank K M)).filter fun j => π₁ = π.twist (η ^ j)).card =
      (Finset.univ.filter fun p : ι × ι => (⟨m p.1, P p.1⟩ : Σ a, CG M a) = ⟨m p.2, P p.2⟩).card

def NormCharPow : Prop := ForCyc fun K M => ∀ η : HChar K, IsGenChar M η →
  (∀ χ : HChar K, IsNormChar M χ → ∃ j, 0 < j ∧ j < Module.finrank K M ∧ χ = η ^ j) ∧
  ∀ j, 0 < j → j < Module.finrank K M → IsNormChar M (η ^ j)

def FibreCG : Prop := ForCyc fun K M => ∀ (n : ℕ) (π : CG K n) (P : CG M n), 1 ≤ n → WeakBC π.HasSat P.HasSat →
  (∀ η : HChar K, IsNormChar M η → π.twist η ≠ π) ∧
  ∀ π₁ : CG K n, WeakBC π₁.HasSat P.HasSat → ∃ η : HChar K, (η = 1 ∨ IsNormChar M η) ∧ π.twist η = π₁

def Fibre : Prop := ForCyc fun K M => ∀ n : ℕ, 1 ≤ n → ∀ (π : Cusp K n) (P : Cusp M n), WeakBC π.sat P.sat →
  (∀ η : HChar K, IsNormChar M η → ¬ (π.twist η).Iso π) ∧
  ∀ π₁ : Cusp K n, WeakBC π₁.sat P.sat → ∃ η : HChar K, (η = 1 ∨ IsNormChar M η) ∧ (π.twist η).Iso π₁

def TwoParts : Prop := ForCyc fun K M => ∀ (n : ℕ) (π : CG K n) (ι : Type) [Fintype ι] (m : ι → ℕ) (P : ∀ i, CG M (m i)),
  1 ≤ n → (∀ i, 1 ≤ m i) → 2 ≤ Fintype.card ι → WeakBC π.HasSat (sumSat P) → ∃ η : HChar K, IsNormChar M η ∧ π.twist η = π

def NonCAP : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (π : CG E n) (ι : Type) [Fintype ι]
  (m : ι → ℕ) (P : ∀ i, CG E (m i)), 1 ≤ n → (∀ i, 1 ≤ m i) →
  (Fintype.card ι ≠ 1 ∨ ∃ i, (⟨m i, P i⟩ : Σ a, CG E a) ≠ ⟨n, π⟩) → (∀ᶠ w in Filter.cofinite, ∃ B, π.HasSat w B) →
  (∀ i, ∀ᶠ w in Filter.cofinite, ∃ B, (P i).HasSat w B) → ∀ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite →
    ∃ w, w ∉ S ∧ ∃ B B', π.HasSat w B ∧ sumSat P w B' ∧ B ≠ B'

def LiftSum : Prop := ForCyc fun K M => ∀ (ι : Type) [Fintype ι] (κ : ι → Type) [∀ i, Fintype (κ i)] (n : ι → ℕ)
  (m : (Σ i, κ i) → ℕ) (π : ∀ i, CG K (n i)) (P : ∀ a, CG M (m a)),
  (∀ i, WeakBC (π i).HasSat (sumSat fun k : κ i => P ⟨i, k⟩)) → WeakBC (sumSat π) (sumSat P)

def LiftPow : Prop := ForCyc fun K M => ∃ (ν : ℂ → HChar K) (ν' : ℂ → HChar M),
  (∀ z v, (ν z).UnrAt v ∧ ((ν z).val v : ℂ) = (normV v : ℂ) ^ (-z)) ∧
  (∀ z w, (ν' z).UnrAt w ∧ ((ν' z).val w : ℂ) = (normV w : ℂ) ^ (-z)) ∧
  ∀ (n : ℕ) (π : CG K n) (ι : Type) [Fintype ι] (m : ι → ℕ) (P : ∀ i, CG M (m i)) (z : ℂ),
    WeakBC π.HasSat (sumSat P) → WeakBC (π.twist (ν z)).HasSat (sumSat fun i => (P i).twist (ν' z))

end UpperTheory.ConvolutionTheory.R
