import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def IsPart (a : AF F) (l l' : (AE F E)ˣ) : Prop := (l' : AE F E) = a • (l : AE F E) + (1 - a) • (1 : AE F E)

def IsPartU {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a : AF F) (g g' : UA σ J) : Prop := mat g' = a • mat g + (1 - a) • (1 : Matrix _ _ (AE F E))

def InAt (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (v : Pl F) (x : AE F E) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
    Valued.v (finAdEquiv F E (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x) w) ≤ WithZero.exp (-FractionalIdeal.count E w 𝔞)

def wt (ν : Chr F E) (z : ℕ) (l : (AE F E)ˣ) : ℂ := (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z

open Classical in

def uLoc (v : Pl F) (x : @Measure (idAt E (evFin F v)) (borel _)) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (ν : Chr F E) (z : ℕ) : ℂ :=
  @integral _ _ _ _ (borel _) x fun l => (if InAt 𝔞 v (l.1 : AE F E) then 1 else 0) * wt ν z l.1

open Classical in

def IdeleFub : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (K : Subgroup (UA σ X.J)) (m : LocMeas K) (μ : Measure (AE F E)ˣ), B.IsGood σ → m.Is → μ.IsHaarMeasure →
    ∀ (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (z : ℕ), 𝔞 ≠ 0 → 2 ≤ z →
    ∃ (πi : (AE F E)ˣ → idAt E (evI F)) (π : ∀ v : Pl F, (AE F E)ˣ → idAt E (evFin F v)) (κ : ℂ), κ ≠ 0 ∧
      (∀ l, IsPart (realAd F 1) l (πi l).1 ∧ ∀ v, IsPart (idem F v) l (π v l).1) ∧
      ∀ (ν : Chr F E) (S₀ S : Finset (Pl F)), Continuous ν → S₀ ⊆ S → UnrOff ν (S : Set (Pl F)) →
        (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ S → ¬ UnrAt ν w ∧ FractionalIdeal.count E w 𝔞 = 0) →
        (∀ v ∉ S, uLoc v (m.xf v) 𝔞 ν z ≠ 0 ∧ @Integrable _ _ _ _ (borel _)
          (fun l => (if InAt 𝔞 v (l.1 : AE F E) then 1 else 0) * wt ν z l.1) (m.xf v)) ∧
        ∀ T : Finset (Pl F), S ⊆ T → ∀ (gi : idAt E (evI F) → ℂ) (g : ∀ v : Pl F, idAt E (evFin F v) → ℂ),
          @Integrable _ _ _ _ (borel _) (fun l => gi l * wt ν z l.1) m.xi →
          (∀ v ∈ T, @Integrable _ _ _ _ (borel _) (fun l => g v l * wt ν z l.1) (m.xf v)) →
          Integrable (fun l => gi (πi l) * (∏ v ∈ T, g v (π v l)) * (if ∀ v ∉ T, InAt 𝔞 v (l : AE F E) then 1 else 0) * wt ν z l) μ ∧
          (∏ v ∈ T \ S, uLoc v (m.xf v) 𝔞 ν z) *
            ∫ l, gi (πi l) * (∏ v ∈ T, g v (π v l)) * (if ∀ v ∉ T, InAt 𝔞 v (l : AE F E) then 1 else 0) * wt ν z l ∂μ =
          κ * (idealVal ν 𝔞 : ℂ) * charL ν (S₀ : Set (Pl F)) (z : ℂ) *
            (@integral _ _ _ _ (borel _) m.xi fun l => gi l * wt ν z l.1) *
            ∏ v ∈ T, @integral _ _ _ _ (borel _) (m.xf v) fun l => g v l * wt ν z l.1

def KFub : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (K : Subgroup (UA σ X.J)) (m : LocMeas K) (μK : Measure K), IsStab B K → m.Is → μK.IsHaarMeasure →
    ∃ (πi : K → kAt K (evI F)) (π : ∀ v : Pl F, K → kAt K (evFin F v)) (κ : ℂ), κ ≠ 0 ∧
      (∀ k, IsPartU (realAd F 1) k.1 (πi k).1 ∧ ∀ v, IsPartU (idem F v) k.1 (π v k).1) ∧
      ∀ (T : Finset (Pl F)) (hi : kAt K (evI F) → ℂ) (h : ∀ v : Pl F, kAt K (evFin F v) → ℂ),
        Integrable hi m.ki → (∀ v ∈ T, Integrable (h v) (m.kf v)) →
        Integrable (fun k => hi (πi k) * ∏ v ∈ T, h v (π v k)) μK ∧
        ∫ k, hi (πi k) * ∏ v ∈ T, h v (π v k) ∂μK = κ * (∫ k, hi k ∂m.ki) * ∏ v ∈ T, ∫ k, h v k ∂(m.kf v)

section
variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

structure Cfg (B : Base F E) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)) : Prop where
  base : B.IsGood σ
  herm : ∃ r s, X.IsHerm σ B r s
  skew : ∃ r s, W.IsSkew σ B r s
  herm₁ : ∃ r s, X₁.IsHerm σ B r s
  skew₁ : ∃ r s, W₁.IsSkew σ B r s
  good : M.IsGood B.ψ
  good₁ : M₁.IsGood B.ψ
  hH : ∃ i j, H.IsAdapted σ B X X₁ i j
  hH' : ∃ i j, H'.IsAdapted σ B W W₁ i j
  ev : (IsEv B M M₁ H.ι H'.ι (isoA H H') e ∧ u = shiftA H H') ∨ (IsEv B M M₁ H.ι H'.ι (isoB H H') e ∧ u = shiftB σ H H')

end

def VacFixX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ K : Subgroup (UA σ X.J), IsStab B K → ∀ v : Pl F,
    (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χX w ∧ UnrAt χW w) →
    ∀ k ∈ kAt K (evFin F v), Acts (evFin F v) (om (k, 1)) (M.vac v) (M.vac v)

def IdealId : Prop :=
  ∃ a₁ a₂ b₁ b₂ : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁) (r s r' s' i j i' j' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ i j → H'.IsAdapted σ B W W₁ i' j' →
    ∀ u (e₁ e₂ : ℤˣ), (u = shiftA H H' ∧ e₁ = a₁ ∧ e₂ = a₂) ∨ (u = shiftB σ H H' ∧ e₁ = b₁ ∧ e₂ = b₂) →
    ∃ 𝔞 : FractionalIdeal (𝓞 E)⁰ E, 𝔞 ≠ 0 ∧ (∀ v l, idem F v • u l ∈ latAtV X W v ↔ InAt 𝔞 v (l : AE F E)) ∧
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P → FractionalIdeal.count E w 𝔞 = 0) ∧
      ∀ ν : Chr F E, Continuous ν → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range ν 0 → UnrOff ν (B.P : Set (Pl F)) →
        idealVal ν 𝔞 = idealVal ν H.𝔟 ^ (e₁ : ℤ) * idealVal ν H'.𝔟 ^ (e₂ : ℤ)

def ArchCone : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁) e u ei ev, Cfg B M M₁ H H' e u → IsEvLoc M M₁ e ei ev →
    ∀ (K : Subgroup (UA σ X.J)) (m : LocMeas K), IsStab B K → m.Is → ∀ χX χW om r s r' s', IsPair B M χX χW om r s r' s' →
    ∀ (ν : Chr F E) (z : ℕ), Continuous ν → 1 ≤ z →
    ∃ L : SInf F _ →L[ℂ] SInf F _, IsConeI B M om m ei u ν z L ∧ (∀ f ∈ M.Pol B.ψ B.emb, L f ∈ M₁.Pol B.ψ B.emb) ∧
      ∀ (f : SInf F _) y, (∀ k : kAt K (evI F), @Integrable _ _ _ _ (borel _) (fun l : idAt E (evI F) =>
          ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • u l.1) (om (k.1, 1) Φ)) f) y * wt ν z l.1) m.xi) ∧
        Integrable (fun k : kAt K (evI F) => @integral _ _ _ _ (borel _) m.xi fun l =>
          ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • u l.1) (om (k.1, 1) Φ)) f) y * wt ν z l.1) m.ki

open Classical in

def FinCone : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁) e u ei ev, Cfg B M M₁ H H' e u → IsEvLoc M M₁ e ei ev →
    ∀ v : Pl F, (∀ l, ev v (opF v (M.co.rho B.ψ (idem F v • u l)) (M.vac v)) = if idem F v • u l ∈ latAtV X W v then M₁.vac v else 0) ∧
    (∀ l, idem F v • u l ∈ latAtV X W v → Acts (evFin F v) (M.co.rho B.ψ (idem F v • u l)) (M.vac v) (M.vac v)) ∧
    ∀ (K : Subgroup (UA σ X.J)) (m : LocMeas K), IsStab B K → m.Is → ∀ χX χW om r s r' s', IsPair B M χX χW om r s r' s' →
    ∀ (ν : Chr F E) (z : ℕ), Continuous ν → 1 ≤ z →
    ∃ Λ : Fl F v _ _ →ₗ[ℂ] Fl F v _ _, ∀ φ ∈ SB _, Λ φ = coneF B M om m v (ev v) u ν z φ ∧ Λ φ ∈ SB _ ∧ ∀ y,
      (∀ k : kAt K (evFin F v), @Integrable _ _ _ _ (borel _) (fun l : idAt E (evFin F v) =>
          ev v (opF v (fun Φ => M.co.rho B.ψ (idem F v • u l.1) (om (k.1, 1) Φ)) φ) y * wt ν z l.1) (m.xf v)) ∧
        Integrable (fun k : kAt K (evFin F v) => @integral _ _ _ _ (borel _) (m.xf v) fun l =>
          ev v (opF v (fun Φ => M.co.rho B.ψ (idem F v • u l.1) (om (k.1, 1) Φ)) φ) y * wt ν z l.1) (m.kf v)

open Classical in

def PureFac : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁) e u ei ev, Cfg B M M₁ H H' e u → IsEvLoc M M₁ e ei ev →
    ∀ K : Subgroup (UA σ X.J), IsStab B K → ∀ χX χW om r s r' s', IsPair B M χX χW om r s r' s' →
    ∀ T : Finset (Pl F), UnrOff χX (T : Set (Pl F)) → UnrOff χW (T : Set (Pl F)) →
    ∀ (f : SInf F _) φ, (∀ v, φ v ∈ SB _) → (∀ v ∉ T, φ v = M.vac v) →
    ∀ k ∈ K, ∀ l : (AE F E)ˣ, ∀ (ki : UA σ X.J) (kf : Pl F → UA σ X.J) (li : (AE F E)ˣ) (lf : Pl F → (AE F E)ˣ),
      IsPartU (realAd F 1) k ki → (∀ v, IsPartU (idem F v) k (kf v)) → IsPart (realAd F 1) l li → (∀ v, IsPart (idem F v) l (lf v)) →
      e (M.co.rho B.ψ (u l) (om (k, 1) (pure f φ))) =
        (if ∀ v ∉ T, idem F v • u l ∈ latAtV X W v then (1 : ℂ) else 0) •
          pure (ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • u li) (om (ki, 1) Φ)) f)) fun v =>
            if v ∈ T then ev v (opF v (fun Φ => M.co.rho B.ψ (idem F v • u (lf v)) (om (kf v, 1) Φ)) (φ v)) else M₁.vac v

def SchSpan : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, vac v ∈ SB _) →
    (∀ᶠ v in cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    schA F κ = Submodule.span ℂ {Φ | ∃ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (T : Finset (Pl F)),
      (∀ v, φ v ∈ SB _) ∧ (∀ v ∉ T, φ v = vac v) ∧ Φ = pure f φ}

end PositivityTheory.ThKG.Loc.Cone

end
