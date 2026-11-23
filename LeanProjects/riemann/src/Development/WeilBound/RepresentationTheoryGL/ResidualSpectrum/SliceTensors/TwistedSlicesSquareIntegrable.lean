import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs

def ExhReg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N → ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ τ, RegInt V τ →
  ∃ (a d : ℕ) (π : CuspSub E a), π.IsUnitary ∧ IsNormalised π ∧ IsSpehOf V π d

def Dich : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N → ∀ V : Submodule ℂ (Sm E N), IsDiscrete V →
  (∃ π : CuspSub E N, π.IsUnitary ∧ IsNormalised π ∧ ∀ π', π.Iso π' → AscEmb V π' 1) ∨ ∃ r, 0 < r ∧ r < N ∧ (ExpV r V).Nonempty

def ExpFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ r, 0 < r → r < N → (ExpV r V).Finite

def ExpNeg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (φ : Sm E N), IsAutForm φ → IsSqInt φ.1 →
  ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, pE E N r c < 0

def SqIntCrit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (φ : Sm E N), IsAutForm φ → (∀ t g, φ.1 (splitCentre E N t * g) = φ.1 g) →
  (∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, pE E N r c < 0) → IsSqInt φ.1

def ExpTw : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (φ : Sm E N) (z : ℂ), IsAutForm φ →
  ∀ r, 0 < r → r < N → ∀ c ∈ Exp r (mulChi N (GlobalTheory.CuspRep.Model.absC E z) φ).1,
    c - z * r * (Module.finrank ℚ E : ℂ) ∈ Exp r φ.1

def Slice : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ), 0 < r → 0 < s → ∀ V : Submodule ℂ (Sm E (r + s)), IsDiscrete V →
  ∀ c ∈ ExpV r V, ∃ T, IsSliceMap V c T

def TwistedSlicesSquareIntegrable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (V : Submodule ℂ (Sm E (r + s)))
    (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) (z₁ z₂ : ℂ) : Prop :=
  ∀ φ ∈ V, ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)),
    (∀ m₂, ∃ ψ : Sm E r, IsAutForm ψ ∧ IsSqInt ψ.1 ∧ ∀ m₁, (mulChi r (GlobalTheory.CuspRep.Model.absC E z₁) ψ).1 m₁ =
      (T φ).1 (lev (Ad E) r s (m₁, m₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) ∧
    ∀ m₁, ∃ ψ : Sm E s, IsAutForm ψ ∧ IsSqInt ψ.1 ∧ ∀ m₂, (mulChi s (GlobalTheory.CuspRep.Model.absC E z₂) ψ).1 m₂ =
      (T φ).1 (lev (Ad E) r s (m₁, m₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))

def Chord : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ), 0 < r → 0 < s → ∀ (V : Submodule ℂ (Sm E (r + s))) (c : ℂ) (T) (lam : ℝ), 0 < lam →
  IsSliceMap V c T → pE E (r + s) r c = -lam * (r * s) →
  (∀ m, 0 < m → m < r + s → ∀ c' ∈ ExpV m V, pE E (r + s) m c' ≤ -lam * (m * ((r + s : ℕ) - m : ℝ))) →
  TwistedSlicesSquareIntegrable V T (c / (r * (Module.finrank ℚ E : ℂ))) (-c / (s * (Module.finrank ℚ E : ℂ)))

def A2 (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) : Submodule ℂ (Sm E N) :=
  Submodule.span ℂ {ψ | IsAutForm ψ ∧ IsSqInt ψ.1}

def Pr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), IsStable (A2 E N) ∧ ∀ ψ ∈ A2 E N, ψ ≠ 0 →
  ∃ (V : Submodule ℂ (Sm E N)) (p : Sm E N →ₗ[ℂ] Sm E N), IsDiscrete V ∧ (∀ χ ∈ A2 E N, p χ ∈ V) ∧
    (∀ o, ∀ χ ∈ A2 E N, p (act o χ) = act o (p χ)) ∧ p ψ ≠ 0

def SliceTens : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (V : Submodule ℂ (Sm E (r + s))), IsDiscrete V →
  ∀ (c z₁ z₂ : ℂ) (T), IsSliceMap V c T → TwistedSlicesSquareIntegrable V T z₁ z₂ → ∀ φ ∈ V, MemInd2 (tw (A2 E r) z₁) (tw (A2 E s) z₂) (T φ)

def IndMap : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (V : Submodule ℂ (Sm E (r + s))) (U₁ : Submodule ℂ (Sm E r))
  (U₂ : Submodule ℂ (Sm E s)) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) (f₁ : Sm E r →ₗ[ℂ] Sm E r) (f₂ : Sm E s →ₗ[ℂ] Sm E s),
  IsStable V → (∀ φ ∈ V, IsAutForm φ) → IsStable U₁ → IsStable U₂ → (∀ o, ∀ φ ∈ V, T (act o φ) = act o (T φ)) →
  (∀ φ ∈ V, MemInd2 U₁ U₂ (T φ)) → (∀ o, ∀ ψ ∈ U₁, f₁ (act o ψ) = act o (f₁ ψ)) →
  (∀ o, ∀ ψ ∈ U₂, f₂ (act o ψ) = act o (f₂ ψ)) →
  ∃ T' : Sm E (r + s) →ₗ[ℂ] Sm E (r + s), (∀ o, ∀ φ ∈ V, T' (act o φ) = act o (T' φ)) ∧
    (∀ φ ∈ V, ∀ (x : BlockIx (r + s) r → Ad E) g, (T' φ).1 (unip x * g) = (T' φ).1 g) ∧
    ∀ φ ∈ V, ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (n : ℕ) (ψ₁ : Fin n → Sm E r) (ψ₂ : Fin n → Sm E s),
      (∀ i, ψ₁ i ∈ U₁) → (∀ i, ψ₂ i ∈ U₂) →
      (∀ m : GA E r × GA E s, (T φ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
        ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) →
      ∀ m : GA E r × GA E s, (T' φ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
        ∑ i, (f₁ (ψ₁ i)).1 m.1 * (f₂ (ψ₂ i)).1 m.2

def Proj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ), 0 < r → 0 < s → ∀ V : Submodule ℂ (Sm E (r + s)), IsDiscrete V →
  ∀ (c z₁ z₂ : ℂ) (T), IsSliceMap V c T → TwistedSlicesSquareIntegrable V T z₁ z₂ →
  ∃ (V₁ : Submodule ℂ (Sm E r)) (V₂ : Submodule ℂ (Sm E s)), IsDiscrete V₁ ∧ IsDiscrete V₂ ∧
    Emb V (MemInd2 (tw V₁ z₁) (tw V₂ z₂))

def InfInd2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (V : Submodule ℂ (Sm E (r + s))) (V₁ : Submodule ℂ (Sm E r))
  (V₂ : Submodule ℂ (Sm E s)) (z₁ z₂ : ℂ), IsDiscrete V → IsDiscrete V₁ → IsDiscrete V₂ →
  Emb V (MemInd2 (tw V₁ z₁) (tw V₂ z₂)) → ∀ τ m, HasInfCharGL V τ m → ∃ m₁ m₂, HasInfCharGL V₁ τ m₁ ∧
    HasInfCharGL V₂ τ m₂ ∧ m = m₁.map (· + (z₁ - (s : ℂ) / 2)) + m₂.map (· + (z₂ + (r : ℂ) / 2))

def InfAsc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N a d : ℕ) (V : Submodule ℂ (Sm E N)) (π : CuspSub E a), IsDiscrete V → AscEmb V π d →
  ∀ τ m, HasInfCharGL V τ m → ∃ m₀, π.HasInfChar τ m₀ ∧ m = ∑ i : Fin d, m₀.map (· + (spehExp d i : ℂ))

def SatInd2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (V : Submodule ℂ (Sm E (r + s))) (V₁ : Submodule ℂ (Sm E r))
  (V₂ : Submodule ℂ (Sm E s)) (z₁ z₂ : ℂ), IsDiscrete V → IsDiscrete V₁ → IsDiscrete V₂ →
  Emb V (MemInd2 (tw V₁ z₁) (tw V₂ z₂)) → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
    ∃ B B₁ B₂, SatV V w B ∧ SatV V₁ w B₁ ∧ SatV V₂ w B₂ ∧
      B.map (fun b : ℂˣ => (b : ℂ)) = satTw w (z₁ - (s : ℂ) / 2) B₁ + satTw w (z₂ + (r : ℂ) / 2) B₂

def SatAsc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N a d : ℕ) (V : Submodule ℂ (Sm E N)) (π : CuspSub E a), IsDiscrete V → AscEmb V π d →
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B₀, (CG.mk π).HasSat w B₀ ∧
    ∀ B, SatV V w B → B.map (fun b : ℂˣ => (b : ℂ)) = ∑ i : Fin d, satTw w (spehExp d i : ℂ) B₀

def SatHerm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ),
  (∀ V : Submodule ℂ (Sm E N), IsDiscrete V → SatV V w B → B.map (fun b => (star b)⁻¹) = B) ∧
    ∀ π : CuspSub E N, 1 ≤ N → π.IsUnitary → IsNormalised π → (CG.mk π).HasSat w B → B.map (fun b => (star b)⁻¹) = B

def Gap : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ (w : HeightOneSpectrum (𝓞 E))
  (B : Multiset ℂˣ), SatV V w B → ∀ z : ℂ, ‖z‖ < (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) →
    (B.map fun b : ℂˣ => (b : ℂ)).count z ≤ (B.map fun b : ℂˣ => (b : ℂ)).count ((Ideal.absNorm w.asIdeal : ℂ) * z)

def StringStep : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ), 0 < r → 0 < s → ∀ (V : Submodule ℂ (Sm E (r + s)))
  (V₁ : Submodule ℂ (Sm E r)) (V₂ : Submodule ℂ (Sm E s)) (z₁ z₂ : ℂ), IsDiscrete V → IsDiscrete V₁ → IsDiscrete V₂ →
  Emb V (MemInd2 (tw V₁ z₁) (tw V₂ z₂)) → ∀ τ, RegInt V τ → (r : ℂ) * z₁ + s * z₂ = 0 → z₁.re < (s : ℝ) / 2 →
  ∀ (a₁ d₁ a₂ d₂ : ℕ) (π₁ : CuspSub E a₁) (π₂ : CuspSub E a₂), π₁.IsUnitary → IsNormalised π₁ → AscEmb V₁ π₁ d₁ →
    π₂.IsUnitary → IsNormalised π₂ → AscEmb V₂ π₂ d₂ →
    (⟨a₁, CG.mk π₁⟩ : Σ b, CG E b) = ⟨a₂, CG.mk π₂⟩ ∧ z₁ = ((s : ℂ) - d₂) / 2 ∧ z₂ = ((d₁ : ℂ) - r) / 2

def Stages : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s a d₁ d₂ : ℕ) (V : Submodule ℂ (Sm E (r + s))) (V₁ : Submodule ℂ (Sm E r))
  (V₂ : Submodule ℂ (Sm E s)) (π : CuspSub E a), IsDiscrete V → IsDiscrete V₁ → IsDiscrete V₂ →
  Emb V (MemInd2 (tw V₁ (((s : ℂ) - d₂) / 2)) (tw V₂ (((d₁ : ℂ) - r) / 2))) → AscEmb V₁ π d₁ → AscEmb V₂ π d₂ →
  AscEmb V π (d₁ + d₂)

def Dual : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N a d : ℕ), 1 ≤ N → ∀ (V : Submodule ℂ (Sm E N)) (π : CuspSub E a), IsDiscrete V → π.IsUnitary →
  IsNormalised π → AscEmb V π d → IsSpehOf V π d

def AscAll : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N → ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ τ, RegInt V τ →
  ∃ (a d : ℕ) (π : CuspSub E a), π.IsUnitary ∧ IsNormalised π ∧ ∀ π', π.Iso π' → AscEmb V π' d

end PositivityTheory.Rg.Rs

end
