import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty

noncomputable section

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

namespace UpperTheory.V.Z.Int

section Defs

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {E : Type} [Field E] [NumberField E]

def nu (x : ℂ) : ℝ := ‖ι.symm x‖

def Ov (w : HeightOneSpectrum (𝓞 E)) : Finset (E →+* ℂ) := Finset.univ.filter fun τ => ∀ x : 𝓞 E, x ∈ w.asIdeal ↔ nu ι (τ x) < 1

def Bnd (w : HeightOneSpectrum (𝓞 E)) (a : (E →+* ℂ) → ℤ) (b : ℂ) : Prop := nu ι b * ∏ τ ∈ Ov ι w, nu ι (τ (unif w : E)) ^ a τ ≤ 1

def Within (n : ℕ) (m : Multiset ℂ) (lo hi : ℤ) : Prop := ∀ z ∈ m, ∃ k : ℤ, z = ((n : ℂ) - 1) / 2 + k ∧ lo ≤ k ∧ k ≤ hi

def Slope (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (inf : (E →+* ℂ) → Multiset ℂ) (B : Multiset ℂˣ) : Prop :=
  ∀ lo hi : (E →+* ℂ) → ℤ, (∀ τ, Within n (inf τ) (lo τ) (hi τ)) →
    ∀ b ∈ algSat n (normV w) B, Bnd ι w hi b ∧ Bnd ι w (fun τ => -lo τ) b⁻¹

end Defs

def AbsBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (G : Type) [Group G] (Γ K : Subgroup G) (I : Type) [Fintype I] (R : G →* Matrix I I ℂ) (F : G → I → ℂ) (s : Finset G) (a : ℂ)
    (c C : ℝ), 0 ≤ c → Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) → F ≠ 0 → (∀ γ ∈ Γ, ∀ g, F (γ * g) = R γ *ᵥ F g) →
    (∀ k ∈ K, ∀ g, F (g * k) = F g) → (∀ g, ∑ x ∈ s, F (g * x) = a • F g) → (∀ k ∈ K, ∀ i j, nu ι (R k i j) ≤ C) →
    (∀ L : List G, (∀ x ∈ L, x ∈ s) → ∀ i j, nu ι (R L.prod i j) ≤ C * c ^ L.length) → nu ι a ≤ c

def RootBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (S : Multiset ℂ) (c : ℝ), 0 ≤ c → (∀ j, 1 ≤ j → j ≤ S.card → nu ι (S.esymm j) ≤ c ^ j) → ∀ b ∈ S, nu ι b ≤ c

def RepBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E : Type) [Field E] [NumberField E] (u : HeightOneSpectrum (𝓞 E)) (ψ : u.adicCompletion E →+* ℂ), (∀ x, Valued.v x ≤ 1 → nu ι (ψ x) ≤ 1) →
    ∀ (n : ℕ) (lam : DomWeight n) (d : ℕ) (e : Module.Basis (Fin d) ℂ (nablaSq ℂ n lam)), ∃ C : ℝ, 0 ≤ C ∧
    ∀ lo hi : ℤ, (∀ i, lo ≤ lam.w i ∧ lam.w i ≤ hi) → ∀ g : GL (Fin n) (u.adicCompletion E), (∀ i j, Valued.v (g.val i j) ≤ 1) → ∀ i j,
      nu ι (LinearMap.toMatrix e e (GlobalTheory.Branching.sqRep ℂ n lam (GeneralLinearGroup.map ψ g)) i j) ≤ C * nu ι (ψ g.val.det) ^ lo ∧
      nu ι (LinearMap.toMatrix e e (GlobalTheory.Branching.sqRep ℂ n lam (GeneralLinearGroup.map ψ g⁻¹)) i j) ≤ C * nu ι (ψ g.val.det) ^ (-hi)

def PlaceHom : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E : Type) [Field E] [NumberField E] (τ : E →+* ℂ), ∃ (u : HeightOneSpectrum (𝓞 E)) (ψ : u.adicCompletion E →+* ℂ),
    (∀ x : E, ψ (algebraMap E _ x) = τ x) ∧ (∀ x, nu ι (ψ x) ≤ 1 ↔ Valued.v x ≤ 1) ∧ ∀ w, τ ∈ Ov ι w ↔ w = u

def PlaceConj : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∀ τ : E →+* ℂ,
    (τ ∈ Ov ι w → ComplexEmbedding.conjugate τ ∉ Ov ι w) ∧ ∀ u, τ ∈ Ov ι u → u ≠ w →
      u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → ComplexEmbedding.conjugate τ ∈ Ov ι w

def ProdNorm : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), (∀ τ ∈ Ov ι w, 0 < nu ι (τ (unif w : E)) ∧ nu ι (τ (unif w : E)) < 1) ∧
    ∏ τ ∈ Ov ι w, nu ι (τ (unif w : E)) = nu ι (normV w : ℂ)

def CharVal : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (κ : HChar E) (m : (E →+* ℂ) → ℤ), κ.IsAlg m → ∀ w, κ.UnrAt w →
    nu ι (κ.val w : ℂ) * ∏ τ ∈ Ov ι w, nu ι (τ (unif w : E)) ^ m τ = 1

def VecForm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ → ∀ (φ : InfinitePlace E → (E →+* ℂ)),
    (∀ v, InfinitePlace.mk (φ v) = v) → ∀ lam : InfinitePlace E → DomWeight n, (∀ v, HasWeightAt σ (φ v) (lam v)) →
    ∀ w : HeightOneSpectrum (𝓞 E), IsUnramU σ w → ∃ (f : MultilinearMap ℂ (fun v => nablaSq ℂ n (lam v)) (UA E n → ℂ)) (K : Subgroup (finU E n)),
      f ≠ 0 ∧ (∀ x, f x ∈ σ) ∧ (∀ g ∈ infU E n, ∀ x, f (fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb (φ v) g) (x v)) = RU E n g (f x)) ∧
      IsOpen (K : Set (finU E n)) ∧ (∀ k ∈ K, ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u n) ∧ (∀ k ∈ K, ∀ x, RU E n k.1 (f x) = f x) ∧
      ∀ y ∈ locU n w, cLoc w y ∈ GlobalTheory.LFun.KGL w n → ∀ x, RU E n y (f x) = f x

def EigAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : Submodule ℂ (UA E n → ℂ)), IsAutRepU σ → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w →
    ∀ (τ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
    GlobalTheory.LFun.HasSatGL w τ.ρ B → IsUnramU σ w ∧ B.card = n ∧ ∀ j ≤ n, ∃ s s' : Finset (UA E n),
      (∀ x ∈ s, x ∈ locU n w ∧ (∀ a b, Valued.v ((cLoc w x).val a b) ≤ 1) ∧ Valued.v (cLoc w x).val.det = WithZero.exp (-(j : ℤ))) ∧
      (∀ x ∈ s', x ∈ locU n w ∧ (∀ a b, Valued.v ((cLoc w x⁻¹).val a b) ≤ 1) ∧ Valued.v (cLoc w x⁻¹).val.det = WithZero.exp (-(j : ℤ))) ∧
      ∀ f ∈ σ, (∀ y ∈ locU n w, cLoc w y ∈ GlobalTheory.LFun.KGL w n → RU E n y f = f) →
        (normV w : ℂ) ^ j.choose 2 • ∑ x ∈ s, RU E n x f = (algSat n (normV w) B).esymm j • f ∧
        (normV w : ℂ) ^ j.choose 2 • ∑ x ∈ s', RU E n x f = (algSat n (normV w) (B.map (·⁻¹))).esymm j • f

def OpBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ →
    ∀ lam : (E →+* ℂ) → DomWeight n, (∀ τ, HasWeightAt σ τ (lam τ)) → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → IsUnramU σ w →
    ∀ lo hi : (E →+* ℂ) → ℤ, (∀ τ i, lo τ ≤ (lam τ).w i ∧ (lam τ).w i ≤ hi τ) → ∀ (j : ℕ) (s : Finset (UA E n)) (a : ℂ),
    (∀ f ∈ σ, (∀ y ∈ locU n w, cLoc w y ∈ GlobalTheory.LFun.KGL w n → RU E n y f = f) → ∑ x ∈ s, RU E n x f = a • f) →
    ((∀ x ∈ s, x ∈ locU n w ∧ (∀ a b, Valued.v ((cLoc w x).val a b) ≤ 1) ∧ Valued.v (cLoc w x).val.det = WithZero.exp (-(j : ℤ))) →
      nu ι a ≤ (∏ τ ∈ Ov ι w, nu ι (τ (unif w : E)) ^ (-hi τ)) ^ j) ∧
    ((∀ x ∈ s, x ∈ locU n w ∧ (∀ a b, Valued.v ((cLoc w x⁻¹).val a b) ≤ 1) ∧ Valued.v (cLoc w x⁻¹).val.det = WithZero.exp (-(j : ℤ))) →
      nu ι a ≤ (∏ τ ∈ Ov ι w, nu ι (τ (unif w : E)) ^ lo τ) ^ j)

def CoreU : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ →
    ∀ lam : (E →+* ℂ) → DomWeight n, (∀ τ, HasWeightAt σ τ (lam τ)) → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w →
    ∀ (τ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
    GlobalTheory.LFun.HasSatGL w τ.ρ B → Slope ι n w (fun φ => infOfWeight (lam φ)) B

def SlopeOn (s : GlobalTheory.GalCut.Level) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E : Type) [Field E] [NumberField E] [IsCMField E] (l' n : ℕ), l'.Prime → 1 ≤ n →
    ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), GlobalTheory.GalCut.InScope s l' π χ → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w →
    ∀ B, (CG.mk π).HasSat w B → Slope ι n w (CG.mk π).infChar B

def SlopeAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ π : CuspSub E n, (∀ τ, π.HasInfChar τ (infOf m)) →
    (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) → ∀ (w : HeightOneSpectrum (𝓞 E)) B, (CG.mk π).HasSat w B → SlopesIn (normV w) m (algSat n (normV w) B)

end UpperTheory.V.Z.Int
