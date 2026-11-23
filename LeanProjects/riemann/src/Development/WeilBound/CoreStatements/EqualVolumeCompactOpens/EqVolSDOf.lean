import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.SameUpToScalars

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField IsDedekindDomain MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def SDHerm (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) : Prop :=
  ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm G x y)

def SDTrace (ξ : E) (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, EFf ξ G x y = k) ∧ ∀ φ : L →+ ℤ, ∃ x ∈ L, ∀ y : L, (φ y : ℚ) = EFf ξ G x y

def SDPair (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) (G' : Matrix (Fin r) (Fin r) E)
    (L' : Submodule (𝓞 E) (Fin r → E)) : Prop :=
  (SDHerm G L ∧ SDHerm G' L') ∨ ∃ ξ : E, ξ ≠ 0 ∧ cc ξ = -ξ ∧ SDTrace ξ G L ∧ SDTrace ξ G' L'

end defs

def Isotropic : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 3 ≤ r → 0 < X.p0 → X.p0 < r →
    ∃ e : Fin r → E, e ≠ 0 ∧ herm X.Gm e e = 0

def DualTransport : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G G' : Matrix (Fin r) (Fin r) E) (a : GL (Fin r) E)
    (L' : Submodule (𝓞 E) (Fin r → E)),
    (a : Matrix (Fin r) (Fin r) E)ᵀ * G * (a : Matrix (Fin r) (Fin r) E).map (ccH E) = G' → IsLat L' →
    ∃ aL' : Submodule (𝓞 E) (Fin r → E), IsLat aL' ∧ (∀ x, x ∈ L' ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ aL') ∧
      (SDHerm G' L' → SDHerm G aL') ∧ ∀ ξ, SDTrace ξ G' L' → SDTrace ξ G aL'

def LocalToAdelic : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (L L' : Submodule (𝓞 E) (Fin r → E)), IsLat L → IsLat L' →
    (∃ γ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), GL (Fin r) (GlobalTheory.SelfDualGenus.LocAlg v),
      (∀ v, GlobalTheory.SelfDualGenus.IsLocalIsometry v G L' G L (γ v)) ∧ {v | γ v ≠ 1}.Finite) →
    AdGenus (IsCMField.complexConj E) G L L'

def EqVolSD : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (r : ℕ) (X X' : Data E r) (L L' : Submodule (𝓞 E) (Fin r → E)) (𝔞 : Ideal (𝓞 E)),
    X.Ψ = X'.Ψ → X.p0 = X'.p0 → 3 ≤ r → 0 < X.p0 → X.p0 < r → IsLat L → IsLat L' → SDPair X.Gm L X'.Gm L' →
    𝔞 ≠ ⊥ → Neat (IsCMField.complexConj E) 𝔞 →
    SameOrbits X X.Γ (levelGrp (ccH E) X.Gm L 𝔞) → SameOrbits X' X'.Γ (levelGrp (ccH E) X'.Gm L' 𝔞) →
    ∀ (x : Frame X.Ψ r) (x' : Frame X'.Ψ r) (FF : Set (V (nd X))) (FF' : Set (V (nd X'))),
      IsOrth X x → IsOrth X' x' → IsFundSet X x FF → IsFundSet X' x' FF' → muF X x FF = muF X' x' FF'

theorem eqVolSD_of (hL : GlobalTheory.Published.Landherr) (hH : GlobalTheory.Published.HasseNormSt) (h0 : EqVolFD) (h1 : Isotropic)
    (h2 : DualTransport) (h3 : LocalToAdelic) : EqVolSD := by
  intro E _ _ _ _ r X X' L L' 𝔞 hΨ hp hr hp0 hpr hL₁ hL₂ hSD h𝔞 hN hO hO'
  obtain ⟨P, hP, hPG⟩ := (GlobalTheory.selfDual_lattices_one_genus X.Gm_herm X'.Gm_herm X.Gm_det X'.Gm_det hL₁ hL₂ hSD).2.2
    hL hH (X.Ψ : Set (E →+* ℂ))
    (fun τ => by
      by_cases h : τ ∈ X.Ψ
      · exact Or.inl h
      · exact Or.inr (by_contra fun h' => h ((X.cmType τ).2 h')))
    (fun τ hτ => ⟨X.p0, X.signature ⟨τ, hτ⟩, hp ▸ X'.signature ⟨τ, hΨ ▸ hτ⟩⟩)
  let a : GL (Fin r) E := Matrix.GeneralLinearGroup.mkOfDetNeZero P hP
  have ha : (a : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (a : Matrix (Fin r) (Fin r) E).map (ccH E) = X'.Gm := hPG.symm
  obtain ⟨aL', haL', hmap, t1, t2⟩ := h2 E r X.Gm X'.Gm a L' ha hL₂
  have hSD' : SDPair X.Gm aL' X.Gm L := by
    rcases hSD with ⟨s, s'⟩ | ⟨ξ, e1, e2, s, s'⟩
    · exact Or.inl ⟨t1 s', s⟩
    · exact Or.inr ⟨ξ, e1, e2, t2 ξ s', s⟩
  have hg := h3 E r X.Gm L aL' hL₁ haL'
    ((GlobalTheory.selfDual_lattices_one_genus X.Gm_herm X.Gm_herm X.Gm_det X.Gm_det haL' hL₁ hSD').2.1 rfl)
  exact h0 E r X X' a L L' aL' 𝔞 hΨ hp ha (h1 E r X hr hp0 hpr) hL₁ hL₂ haL' hmap hg h𝔞 hN hO hO'

end PositivityTheory.EqVol
