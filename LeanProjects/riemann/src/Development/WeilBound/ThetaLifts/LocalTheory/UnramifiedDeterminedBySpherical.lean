import Development.WeilBound.ThetaLifts.LocalTheory.IsArchimedeanLocalEquivariantMap
import Development.WeilBound.ThetaLifts.ConeHypotheses.PolDense
import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj

noncomputable section

namespace PositivityTheory.ThKG.Loc

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def MeasEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ K : Subgroup (UA σ X.J), IsStab B K → ∃ m : LocMeas K, m.Is

open Classical in

def ConeFacB : Prop :=
  ∃ e₁ e₂ : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e ei ev, IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e → IsEvLoc G.M' G₁.M' e ei ev →
    ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ) (m : LocMeas K), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → m.Is →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∃ (L : SInf F _ →L[ℂ] SInf F _) (Λ : ∀ v : Pl F, Fl F v _ _ →ₗ[ℂ] Fl F v _ _) (u : Pl F → ℂ),
        IsConeI B G.M' om' m ei (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) L ∧ (∀ f ∈ G.M'.Pol B.ψ B.emb, L f ∈ G₁.M'.Pol B.ψ B.emb) ∧
        (∀ v, ∀ φ ∈ SB _, Λ v φ = coneF B G.M' om' m v (ev v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ ∧ Λ v φ ∈ SB _) ∧
        (∀ v ∉ X.T, u v ≠ 0 ∧ Λ v (G.M'.vac v) = u v • G₁.M'.vac v) ∧
        (∀ Φ ∈ schA F _, ∀ Ψ ∈ schA F _, ∀ c : ℂ, cone B G.M' om' e K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (Φ + c • Ψ) =
          cone B G.M' om' e K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) Φ + c • cone B G.M' om' e K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) Ψ) ∧
        ∀ T : Finset (Pl F), X.T ⊆ T → ∀ (f : SInf F _) φ, (∀ v, φ v ∈ SB _) → (∀ v ∉ T, φ v = G.M'.vac v) →
          (∏ v ∈ T \ X.T, u v) • cone B G.M' om' e K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (pure f φ) =
            (κ * ((idealVal X.ν H.𝔟 ^ (e₁ : ℤ) * idealVal X.ν H'.𝔟 ^ (e₂ : ℤ) : ℂˣ) : ℂ) * charL X.ν (X.S₀ : Set (Pl F)) ((((a - (b + 2)) / 2 + 1) : ℕ) : ℂ)) •
              pure (L f) fun v => if v ∈ T then Λ v (φ v) else G₁.M'.vac v

open Classical in

def ConeFacA : Prop :=
  ∃ e₁ e₂ : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e ei ev, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → IsEvLoc G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ) (m : LocMeas K), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → m.Is →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∃ (L : SInf F _ →L[ℂ] SInf F _) (Λ : ∀ v : Pl F, Fl F v _ _ →ₗ[ℂ] Fl F v _ _) (u : Pl F → ℂ),
        IsConeI B G.M om m ei (shiftA H H') X.ν ((b + 2 - a') / 2) L ∧ (∀ f ∈ G.M.Pol B.ψ B.emb, L f ∈ G₁.M.Pol B.ψ B.emb) ∧
        (∀ v, ∀ φ ∈ SB _, Λ v φ = coneF B G.M om m v (ev v) (shiftA H H') X.ν ((b + 2 - a') / 2) φ ∧ Λ v φ ∈ SB _) ∧
        (∀ v ∉ X.T, u v ≠ 0 ∧ Λ v (G.M.vac v) = u v • G₁.M.vac v) ∧
        (∀ Φ ∈ schA F _, ∀ Ψ ∈ schA F _, ∀ c : ℂ, cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (Φ + c • Ψ) =
          cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Φ + c • cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Ψ) ∧
        ∀ T : Finset (Pl F), X.T ⊆ T → ∀ (f : SInf F _) φ, (∀ v, φ v ∈ SB _) → (∀ v ∉ T, φ v = G.M.vac v) →
          (∏ v ∈ T \ X.T, u v) • cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (pure f φ) =
            (κ * ((idealVal X.ν H.𝔟 ^ (e₁ : ℤ) * idealVal X.ν H'.𝔟 ^ (e₂ : ℤ) : ℂˣ) : ℂ) * charL X.ν (X.S₀ : Set (Pl F)) ((((b + 2 - a') / 2) : ℕ) : ℂ)) •
              pure (L f) fun v => if v ∈ T then Λ v (φ v) else G₁.M.vac v

def StdB : Prop :=
  ∃ s : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e ei ev e' ei' ev', IsEv B G.M G₁.M 1 H'.ι (iso0 a H') e → IsEvLoc G.M G₁.M e ei ev →
    IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → IsEvLoc G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)) (m : LocMeas K), IsStab B K → m.Is →
    ∀ X om om' R Rf om₁ om₁' R₁ Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
    ∀ v : B.P, v.1 ∈ X.T → ∃ φ ∈ SB _, ∃ φ' ∈ SB _, Rf.p v φ = Rf.p' v φ' ∧ Rf₁.p v (ev v φ) ≠ 0 ∧
      Rf₁.p' v (coneF B G.M' om' m v (ev' v) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ') =
        ((chrW X.ν (B.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) *
          eps B.ψ (chrW X.ν (B.τ v)) (-(((a - (b + 2)) / 2 : ℕ) : ℤ))) • Rf₁.p v (ev v φ)

def StdA : Prop :=
  ∃ s : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e ei ev e' ei' ev', IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → IsEvLoc G.M G₁.M e ei ev →
    IsEv B G.M' G₁.M' 1 H'.ι (iso0 a' H') e' → IsEvLoc G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V.J)) (m : LocMeas K), IsStab B K → m.Is →
    ∀ X om om' R Rf om₁ om₁' R₁ Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
    ∀ v : B.P, v.1 ∈ X.T → ∃ φ ∈ SB _, ∃ φ' ∈ SB _, Rf.p v φ = Rf.p' v φ' ∧ Rf₁.p' v (ev' v φ') ≠ 0 ∧
      Rf₁.p v (coneF B G.M om m v (ev v) (shiftA H H') X.ν ((b + 2 - a') / 2) φ) =
        ((chrW X.ν (B.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) *
          eps B.ψ (chrW X.ν (B.τ v)) (1 - (((b + 2 - a') / 2 : ℕ) : ℤ))) • Rf₁.p' v (ev' v φ')

def FLocB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e' ei' ev', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → IsEvLoc G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)) (m : LocMeas K), IsStab B K → m.Is →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      (∀ g ∈ UAt σ G.V' (evFin F B.v₁), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F B.v₁) (om' (g, 1)) φ φ₁ →
        ∀ l : Fl F B.v₁ _ _ →ₗ[ℂ] ℂ, augAt om₁' B.v₁ ≤ LinearMap.ker l →
        l (coneF B G.M' om' m B.v₁ (ev' B.v₁) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ₁) =
          l (coneF B G.M' om' m B.v₁ (ev' B.v₁) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ)) ∧
      ∀ φ ∈ G.M'.SoLoc B.ψ B.τ₁, coneF B G.M' om' m B.v₁ (ev' B.v₁) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ ∈ G₁.M'.SoLoc B.ψ B.τ₁

def BumpB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e' ei' ev', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → IsEvLoc G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)) (m : LocMeas K), IsStab B K → m.Is →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ L, IsConeI B G.M' om' m ei' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) L →
    ∀ l : SInf F _ →L[ℂ] ℂ, l ≠ 0 → (∀ g ∈ UAt σ G₁.V' (evI F), ∀ f f₁ : SInf F _, Acts (evI F) (om₁' (g, 1)) f f₁ → l f₁ = l f) →
      ∃ f, l (L f) ≠ 0

def BumpA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e ei ev, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → IsEvLoc G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)) (m : LocMeas K), IsStab B K → m.Is →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ L, IsConeI B G.M om m ei (shiftA H H') X.ν ((b + 2 - a') / 2) L →
    ∀ l : SInf F _ →L[ℂ] ℂ, l ≠ 0 → (∀ g ∈ UAt σ G₁.V (evI F), ∀ f f₁ : SInf F _, Acts (evI F) (om₁ (g, 1)) f f₁ → l f₁ = l f) →
      ∃ f, l (L f) ≠ 0

def RealUniq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW χX' χW' : Chr F E) (om om' : Rep σ X W)
    (r s r' s' : ℕ) (k : InfinitePlace F → ℤ), IsPair B M χX χW om r s r' s' → IsPair B M χX' χW' om' r s r' s' →
    HasExp B.emb χW k → HasExp B.emb χW' k → ∀ g ∈ UAt σ X (evI F), ∀ Φ ∈ schA F _, om (g, 1) Φ = om' (g, 1) Φ

def StepTy {a a' a₁ a₁' : ℕ} (G : Geo σ a a') (G₁ : Geo σ a₁ a₁') (X : Chars F E) (χ : Chr F E) (r : ℝ) : Prop :=
  (a₁ = a ∧ a₁' + 2 = a' ∧ G₁.p = G.p ∧ G₁.q + 1 = G.q ∧ χ = X.β ∧ r = a / 2) ∨
    (a₁ + 2 = a ∧ a₁' = a' ∧ G₁.p + 1 = G.p ∧ G₁.q = G.q ∧ χ = X.α ∧ r = a' / 2)

def UnramifiedDeterminedBySpherical : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' a₁ a₁' : ℕ) (G : Geo σ a a') (G₁ : Geo σ a₁ a₁') (X : Chars F E) om om' om₁ om₁' R Rf R₁ Rf₁
    (H' : Plane E (a + a') (a₁ + a₁')) (i₀ i₁ : ℕ) χ r, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
    StepTy G G₁ X χ r → H'.IsAdapted σ B G.W G₁.W i₀ i₁ → ∀ v ∉ X.T, ∀ lam, IsFiniteLocalEquivariantMap om om₁ H' v χ r (Rf.p v) (Rf₁.p v) lam → lam (Rf.p v (G.M.vac v)) = 0 → lam = 0

def RamifiedMultiplicityOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' a₁ a₁' : ℕ) (G : Geo σ a a') (G₁ : Geo σ a₁ a₁') (X : Chars F E) om om' om₁ om₁' R Rf R₁ Rf₁
    (H' : Plane E (a + a') (a₁ + a₁')) (i₀ i₁ : ℕ) χ r, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
    StepTy G G₁ X χ r → H'.IsAdapted σ B G.W G₁.W i₀ i₁ → ∀ v ∈ X.T, ∀ lam lam', IsFiniteLocalEquivariantMap om om₁ H' v χ r (Rf.p v) (Rf₁.p v) lam → IsFiniteLocalEquivariantMap om om₁ H' v χ r (Rf.p v) (Rf₁.p v) lam' →
      lam ≠ 0 → ∃ c : ℂ, lam' = c • lam

def ArchimedeanMultiplicityOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' a₁ a₁' : ℕ) (G : Geo σ a a') (G₁ : Geo σ a₁ a₁') (X : Chars F E) om om' om₁ om₁' R Rf R₁ Rf₁
    (H' : Plane E (a + a') (a₁ + a₁')) (i₀ i₁ : ℕ) χ r, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
    StepTy G G₁ X χ r → H'.IsAdapted σ B G.W G₁.W i₀ i₁ → ∀ lam lam', IsArchimedeanLocalEquivariantMap B G.M G₁.M om om₁ H' χ r R.p R₁.p lam → IsArchimedeanLocalEquivariantMap B G.M G₁.M om om₁ H' χ r R.p R₁.p lam' →
      lam ≠ 0 → ∃ c : ℂ, lam' = c • lam

def InjPure : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om' R Rf, IsMatched B G X om om' R Rf → NZ B G om om' →
    (∀ f ∈ G.M.Pol B.ψ B.emb, ∀ φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) →
      R.p f ≠ 0 → (∀ v, Rf.p v (φ v) ≠ 0) → G.M.I om (pure f φ) ≠ 0) ∧
    ∀ f ∈ G.M'.Pol B.ψ B.emb, ∀ φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
      (G.q = 0 ∨ φ B.v₁ ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁)) →
      R.p' f ≠ 0 → (∀ v, Rf.p' v (φ v) ≠ 0) → G.M'.I om' (pure f φ) ≠ 0

end PositivityTheory.ThKG.Loc

end
