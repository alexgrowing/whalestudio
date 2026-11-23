import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.IsIsotropicHermitianSetting

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
  ReciprocityTheory.L2DbarEstimates

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

abbrev ccH (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E := (IsCMField.complexConj E).toRingHom

def FundFor (X : Data E r) (Γ : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : Prop :=
  MeasurableSet FF ∧ FF ⊆ OmF X x0 ∧
  (∀ z ∈ FF, ∀ z' ∈ FF, ∀ γ ∈ Γ, ∀ b ∈ Bor X.Ψ r, cpt X x0 z' = lact γ (rmul (cpt X x0 z) b) → z = z') ∧
  ∀ᵐ z ∂muF X x0, ∃ z' ∈ FF, ∃ γ ∈ Γ, ∃ b ∈ Bor X.Ψ r, cpt X x0 z = lact γ (rmul (cpt X x0 z') b)

theorem fundFor_iff (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) :
    FundFor X X.Γ x0 FF ↔ IsFundSet X x0 FF := by
  exact Iff.rfl

def FreeOn (X : Data E r) (Γ : Subgroup (GL (Fin r) E)) : Prop :=
  ∀ γ ∈ Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, lact γ x = rmul x b → γ = 1

def SameUpToScalars (Γ Γ' : Subgroup (GL (Fin r) E)) : Prop :=
  (∀ γ ∈ Γ, ∃ s : Eˣ, ∃ γ' ∈ Γ', (γ' : Matrix (Fin r) (Fin r) E) = (s : E) • (γ : Matrix (Fin r) (Fin r) E)) ∧
  ∀ γ' ∈ Γ', ∃ s : Eˣ, ∃ γ ∈ Γ, (γ : Matrix (Fin r) (Fin r) E) = (s : E) • (γ' : Matrix (Fin r) (Fin r) E)

def SameOrbits (X : Data E r) (Γ Γ' : Subgroup (GL (Fin r) E)) : Prop :=
  ∀ x ∈ X.dom, ∀ y ∈ X.dom, (∃ γ ∈ Γ, ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul x b)) ↔
    ∃ γ ∈ Γ', ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul x b)

end defs

def VolOfIdx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Γ₁ Γ₂ : Subgroup (GL (Fin r) E))
    (x₁ x₂ : Frame X.Ψ r) (F₁ F₂ : Set (V (nd X))),
    Γ₁ ≤ uGrp (ccH E) X.Gm → Γ₂ ≤ uGrp (ccH E) X.Gm → FreeOn X Γ₁ → FreeOn X Γ₂ → EqIdx Γ₁ Γ₂ →
    IsOrth X x₁ → IsOrth X x₂ → FundFor X Γ₁ x₁ F₁ → FundFor X Γ₂ x₂ F₂ → muF X x₁ F₁ = muF X x₂ F₂

def Transport : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (a : GL (Fin r) E)
    (Γ' : Subgroup (GL (Fin r) E)) (x' : Frame X'.Ψ r) (F' : Set (V (nd X'))),
    X.Ψ = X'.Ψ → X.p0 = X'.p0 →
    (a : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (a : Matrix (Fin r) (Fin r) E).map (ccH E) = X'.Gm →
    IsOrth X' x' → FreeOn X' Γ' → FundFor X' Γ' x' F' →
    FreeOn X (conjBy a Γ') ∧ ∃ (x : Frame X.Ψ r) (F : Set (V (nd X))),
      IsOrth X x ∧ FundFor X (conjBy a Γ') x F ∧ muF X x F = muF X' x' F'

def ScalarSwap : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Γ Γ' : Subgroup (GL (Fin r) E)),
    SameUpToScalars Γ Γ' →
    (∀ γ ∈ Γ', (∃ s : E, (γ : Matrix (Fin r) (Fin r) E) = s • (1 : Matrix (Fin r) (Fin r) E)) → γ = 1) →
    FreeOn X Γ → FreeOn X Γ' ∧ ∀ x0 FF, FundFor X Γ x0 FF → FundFor X Γ' x0 FF

def ScalarsOfOrbits : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Γ Γ' : Subgroup (GL (Fin r) E)),
    Γ ≤ uGrp (ccH E) X.Gm → Γ' ≤ uGrp (ccH E) X.Gm → SameOrbits X Γ Γ' → SameUpToScalars Γ Γ'

def LevelFacts : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (c : E ≃ₐ[F] E)
    (J : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) (𝔞 : Ideal (𝓞 E)), IsLat Λ → IsUnit J.det →
    (Neat c 𝔞 → ∀ γ ∈ levelGrp c.toRingHom J Λ 𝔞,
      (∃ s : E, (γ : Matrix (Fin N) (Fin N) E) = s • (1 : Matrix (Fin N) (Fin N) E)) → γ = 1) ∧
    ∀ (J₀ : Matrix (Fin N) (Fin N) E) (a : GL (Fin N) E) (Λ₀ : Submodule (𝓞 E) (Fin N → E)),
      (a : Matrix (Fin N) (Fin N) E)ᵀ * J₀ * (a : Matrix (Fin N) (Fin N) E).map c.toRingHom = J →
      (∀ x, x ∈ Λ ↔ (a : Matrix (Fin N) (Fin N) E) *ᵥ x ∈ Λ₀) →
      conjBy a (levelGrp c.toRingHom J Λ 𝔞) = levelGrp c.toRingHom J₀ Λ₀ 𝔞

def EqVolFD : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (a : GL (Fin r) E)
    (L L' aL' : Submodule (𝓞 E) (Fin r → E)) (𝔞 : Ideal (𝓞 E)),
    X.Ψ = X'.Ψ → X.p0 = X'.p0 →
    (a : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (a : Matrix (Fin r) (Fin r) E).map (ccH E) = X'.Gm →
    (∃ e : Fin r → E, e ≠ 0 ∧ herm X.Gm e e = 0) →
    IsLat L → IsLat L' → IsLat aL' → (∀ x, x ∈ L' ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ aL') →
    AdGenus (IsCMField.complexConj E) X.Gm L aL' → 𝔞 ≠ ⊥ → Neat (IsCMField.complexConj E) 𝔞 →
    SameOrbits X X.Γ (levelGrp (ccH E) X.Gm L 𝔞) → SameOrbits X' X'.Γ (levelGrp (ccH E) X'.Gm L' 𝔞) →
    ∀ (x : Frame X.Ψ r) (x' : Frame X'.Ψ r) (FF : Set (V (nd X))) (FF' : Set (V (nd X'))),
      IsOrth X x → IsOrth X' x' → IsFundSet X x FF → IsFundSet X' x' FF' → muF X x FF = muF X' x' FF'

theorem gamma_le_u {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) :
    X.Γ ≤ uGrp (ccH E) X.Gm := by
  intro γ hγ
  have hst := (X.Γ_stab γ hγ).1
  show (↑γ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (↑γ : Matrix (Fin r) (Fin r) E).map ⇑(ccH E) = X.Gm
  ext i j
  have h := hst (Pi.single i 1) (Pi.single j 1)
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, ReciprocityTheory.ChartRestriction.G.FD.cc, Matrix.mulVec, dotProduct, Pi.single_apply,
    apply_ite (⇑(NumberField.IsCMField.complexConj E)), map_one, map_zero, mul_ite, ite_mul, mul_one, one_mul,
    mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [← h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem eqVolFD_of (h1 : LevelIndexEq) (h2 : VolOfIdx) (h3 : Transport) (h4 : ScalarSwap) (h5 : ScalarsOfOrbits)
    (h6 : LevelFacts) : EqVolFD := by
  intro E _ _ _ r X X' a L L' aL' 𝔞 hΨ hp0 ha hiso hL hL' haL' hLL' hgen h𝔞 hneat hSO hSO' x x' FF FF'
    hx hx' hF hF'
  have hdetX : IsUnit X.Gm.det := isUnit_iff_ne_zero.mpr X.Gm_det
  have hdetX' : IsUnit X'.Gm.det := isUnit_iff_ne_zero.mpr X'.Gm_det
  obtain ⟨hscal, -⟩ := h6 _ E r (NumberField.IsCMField.complexConj E) X.Gm L 𝔞 hL hdetX
  obtain ⟨hscal', hconj'⟩ := h6 _ E r (NumberField.IsCMField.complexConj E) X'.Gm L' 𝔞 hL' hdetX'
  have hΓ' : conjBy a (levelGrp (ccH E) X'.Gm L' 𝔞) = levelGrp (ccH E) X.Gm aL' 𝔞 :=
    hconj' X.Gm a aL' ha hLL'
  have hlev_le : ∀ (J : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)),
      levelGrp (ccH E) J Λ 𝔞 ≤ uGrp (ccH E) J := fun J Λ => inf_le_left
  have hs1 := h5 E r X X.Γ (levelGrp (ccH E) X.Gm L 𝔞) (gamma_le_u X) (hlev_le _ _) hSO
  have hs1' := h5 E r X' X'.Γ (levelGrp (ccH E) X'.Gm L' 𝔞) (gamma_le_u X') (hlev_le _ _) hSO'
  have hfreeX : FreeOn X X.Γ := X.Γ_free
  have hfreeX' : FreeOn X' X'.Γ := X'.Γ_free
  obtain ⟨hfree1, hfund1⟩ := h4 E r X X.Γ _ hs1 (hscal hneat) hfreeX
  obtain ⟨hfree1', hfund1'⟩ := h4 E r X' X'.Γ _ hs1' (hscal' hneat) hfreeX'
  have hF1 := hfund1 x FF ((fundFor_iff X x FF).mpr hF)
  have hF1' := hfund1' x' FF' ((fundFor_iff X' x' FF').mpr hF')
  obtain ⟨hfree2, x₂, F₂, hx₂, hF₂, hmu⟩ := h3 E r X X' a _ x' FF' hΨ hp0 ha hx' hfree1' hF1'
  rw [hΓ'] at hfree2 hF₂
  have hisoS : IsIsotropicHermitianSetting (NumberField.IsCMField.complexConj E) X.Gm := by
    refine ⟨Algebra.IsQuadraticExtension.finrank_eq_two _ _, NumberField.IsCMField.complexConj_ne_one E, ?_,
      hdetX, hiso⟩
    ext i j
    exact (X.Gm_herm i j).symm
  have hidx := h1 _ E r (NumberField.IsCMField.complexConj E) X.Gm L aL' 𝔞 hisoS hL haL' h𝔞 hneat hgen
  rw [← hmu]
  exact h2 E r X _ _ x x₂ FF F₂ (hlev_le _ _) (hlev_le _ _) hfree1 hfree2 hidx hx hx₂ hF1 hF₂

end PositivityTheory.EqVol
