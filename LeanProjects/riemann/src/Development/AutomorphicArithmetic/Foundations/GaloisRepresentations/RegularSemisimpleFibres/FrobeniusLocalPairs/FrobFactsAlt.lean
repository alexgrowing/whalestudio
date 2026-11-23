import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut
import Development.AbelianVarietyTheory.Definitions.Divisors.IntersectionFamilySymmetric

noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DZA UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

structure IsRes {k K : Type} [Field k] [ValuativeRel k] [Field K] [ValuativeRel K] [Algebra k K] {F₀ F₁ : Type} [Field F₀]
    [Fintype F₀] [Field F₁] [Algebra F₀ F₁] (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁) : Prop where
  deg : Module.finrank F₀ F₁ = Module.finrank k K
  onto₀ : Function.Surjective rk
  onto₁ : Function.Surjective rK
  inc : ∀ (x : 𝒪[k]) (y : 𝒪[K]), (y : K) = algebraMap k K x → rK y = algebraMap F₀ F₁ (rk x)
  gal : ∀ x y : 𝒪[K], (y : K) = s x → rK y = sb (rK x)
  frob : ∀ z : F₁, sb z = z ^ Fintype.card F₀

def ResEx : Prop :=
  ∀ (k K : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] [IsGalois k K], PositivityTheory.Rg.Tf.Loc.IsUnramifiedLoc k K →
    ∃ (F₀ F₁ : Type) (_ : Field F₀) (_ : Fintype F₀) (_ : Field F₁) (_ : Fintype F₁) (_ : Algebra F₀ F₁)
      (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb

def InflFacts : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (F₀ : Type) [Field F₀] [Fintype F₀]
    (rd : 𝒪[k] →+* F₀), Function.Surjective rd → ∀ n : ℕ,
    KO k n = PositivityTheory.Rg.Tf.Loc.unitGL k ∧ IsOpen (K1 rd n : Set (GL (Fin n) k)) ∧ IsCompact (K1 rd n : Set (GL (Fin n) k)) ∧
      K1 rd n ≤ KO k n ∧
      (∀ (fb : GL (Fin n) F₀ → ℂ) (y : GL (Fin n) 𝒪[k]),
        infl rd fb (GeneralLinearGroup.map (algebraMap 𝒪[k] k) y) = fb (GeneralLinearGroup.map rd y)) ∧
      ∀ fb : GL (Fin n) F₀ → ℂ, GlobalTheory.BCT.IsHecke (K1 rd n) (infl rd fb) ∧ Test (infl rd fb) ∧ ∀ x, infl rd fb x ≠ 0 → x ∈ KO k n

def FrobFacts : Prop :=
  ∀ (k K : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] [IsGalois k K],
    ∀ (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁] (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
    (∀ τ : K ≃ₐ[k] K, τ ∈ Subgroup.zpowers s) ∧ ∀ n : ℕ, GlobalTheory.LBC.IsStable s (K1 rK n) ∧ GlobalTheory.LBC.IsStable s (KO K n) ∧
      ∀ y : GL (Fin n) 𝒪[K], ∃ y' : GL (Fin n) 𝒪[K],
        GeneralLinearGroup.map (algebraMap 𝒪[K] K) y' = GlobalTheory.LBC.galAct s n (GeneralLinearGroup.map (algebraMap 𝒪[K] K) y) ∧
        GeneralLinearGroup.map rK y' = GlobalTheory.LBC.galAct sb n (GeneralLinearGroup.map rK y)

def GlobOf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E], (Module.finrank F E).Prime →
    ∀ (v : Pl F) (w : PlacesOver E v), (∀ w' : PlacesOver E v, w' = w) →
    ∀ [Algebra (v.adicCompletion F) (w.1.adicCompletion E)], (∀ x, completionMap v w.1 x = algebraMap _ (w.1.adicCompletion E) x) →
    ¬ GM.Split E v ∧ Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = Module.finrank F E ∧
      ∀ s : w.1.adicCompletion E ≃ₐ[v.adicCompletion F] w.1.adicCompletion E, (∀ τ, τ ∈ Subgroup.zpowers s) →
        ∃ σ : E ≃ₐ[F] E, (∀ τ, τ ∈ Subgroup.zpowers σ) ∧ ∀ y, galFin σ v y w = s (y w)

def InflTrace : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E], (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (π : CuspSub F n) (P : CuspSub E n), (∀ g : E ≃ₐ[F] E, (Cusp.cx P).ConjIso g.toRingEquiv) →
      WeakBC (Cusp.cx π).sat (Cusp.cx P).sat → ∀ (v : Pl F) (w : PlacesOver E v), (∀ w' : PlacesOver E v, w' = w) → GM.Unr E v →
    ∀ [Algebra (v.adicCompletion F) (w.1.adicCompletion E)] [ValuativeExtension (v.adicCompletion F) (w.1.adicCompletion E)]
      [FiniteDimensional (v.adicCompletion F) (w.1.adicCompletion E)] [IsGalois (v.adicCompletion F) (w.1.adicCompletion E)],
      (∀ x, completionMap v w.1 x = algebraMap _ (w.1.adicCompletion E) x) →
    ∀ (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁] (rk : 𝒪[v.adicCompletion F] →+* F₀) (rK : 𝒪[w.1.adicCompletion E] →+* F₁)
      (s : w.1.adicCompletion E ≃ₐ[v.adicCompletion F] w.1.adicCompletion E) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
    ∀ (τ : SmIrr (Gw n v)) (τ' : SmIrr (Gw n w.1)), (Cusp.cx π).locComp v τ → (Cusp.cx P).locComp w.1 τ' →
      ∃ (I : τ'.V →ₗ[ℂ] τ'.V) (c : ℂ), GlobalTheory.LBC.IsTwInt (v.adicCompletion F) s τ'.ρ I ∧ c ≠ 0 ∧
        ∀ fb : GL (Fin n) F₀ → ℂ, (∀ a b, fb (b⁻¹ * a * b) = fb a) →
          GlobalTheory.BCT.twTr τ'.ρ (KO _ n) (K1 rK n) (infl rK (normLift sb fb)) I =
            c * GlobalTheory.BCT.twTr τ.ρ (KO _ n) (K1 rk n) (infl rk fb) LinearMap.id

def bor {F₀ : Type} [Field F₀] {n : ℕ} (θ : Fin n → (F₀ˣ →* ℂˣ)) (g : GL (Fin n) F₀) : ℂ :=
  if h : ∃ d : Fin n → F₀ˣ, (g : Matrix (Fin n) (Fin n) F₀).BlockTriangular id ∧ ∀ i, (g : Matrix (Fin n) (Fin n) F₀) i i = d i then
    ((∏ i, θ i (h.choose i) : ℂˣ) : ℂ) else 0

def borCard (F₀ : Type) [Field F₀] (n : ℕ) : ℕ :=
  Nat.card {g : GL (Fin n) F₀ // (g : Matrix (Fin n) (Fin n) F₀).BlockTriangular id}

def indBor {F₀ : Type} [Field F₀] {n : ℕ} (t : GL (Fin n) F₀ →* GL (Fin n) F₀) (θ : Fin n → (F₀ˣ →* ℂˣ)) (g : GL (Fin n) F₀) : ℂ :=
  (borCard F₀ n : ℂ)⁻¹ * ∑ᶠ x : GL (Fin n) F₀, bor θ (x⁻¹ * g * t x)

def HasTor {k : Type} [Field k] [ValuativeRel k] {F₀ : Type} [Field F₀] (rd : 𝒪[k] →+* F₀) {n : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V) (θ : Fin n → (F₀ˣ →* ℂˣ)) : Prop :=
  ∃ x : V, x ≠ 0 ∧ ∀ y : GL (Fin n) 𝒪[k], bor θ (GeneralLinearGroup.map rd y) ≠ 0 →
    ρ (GeneralLinearGroup.map (algebraMap 𝒪[k] k) y) x = bor θ (GeneralLinearGroup.map rd y) • x

def nrmChar (F₁ : Type) {F₀ : Type} [Field F₀] [Field F₁] [Algebra F₀ F₁] (χ : F₀ˣ →* ℂˣ) : F₁ˣ →* ℂˣ :=
  χ.comp (Units.map (Algebra.norm F₀ : F₁ →* F₀))

def TorLift : Prop :=
  ∀ (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁] (sb : F₁ ≃ₐ[F₀] F₁), (∀ z : F₁, sb z = z ^ Fintype.card F₀) → ∀ (n : ℕ) (θ : Fin n → (F₀ˣ →* ℂˣ)),
    normLift sb (indBor (MonoidHom.id _) θ) = indBor (GlobalTheory.LBC.galAct sb n) fun i => nrmChar F₁ (θ i)

def TorFin : Prop :=
  ∀ (F₀ : Type) [Field F₀] [Fintype F₀] (n : ℕ) (θ : Fin n → (F₀ˣ →* ℂˣ)) (W : Type) [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (r : Representation ℂ (GL (Fin n) F₀) W),
    (∀ a b, indBor (MonoidHom.id _) θ (b⁻¹ * a * b) = indBor (MonoidHom.id _) θ a) ∧
    ((∃ x : W, x ≠ 0 ∧ ∀ g, bor θ g ≠ 0 → r g x = bor θ g • x) →
      LinearMap.trace ℂ W (∑ᶠ g, indBor (MonoidHom.id _) (fun i => (θ i)⁻¹) g • r g) ≠ 0) ∧
    ∀ (t : GL (Fin n) F₀ →* GL (Fin n) F₀) (A : W →ₗ[ℂ] W), (∀ g, r (t g) ∘ₗ A = A ∘ₗ r g) →
      LinearMap.trace ℂ W (∑ᶠ g, indBor t (fun i => (θ i)⁻¹) g • (r g ∘ₗ A)) ≠ 0 →
      ∃ x : W, x ≠ 0 ∧ ∀ g, bor θ g ≠ 0 → r g x = bor θ g • x

def FinAct : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (F₀ : Type) [Field F₀] [Fintype F₀]
    (rd : 𝒪[k] →+* F₀), Function.Surjective rd → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) k) V),
    (∀ g : GL (Fin n) F₀, ∃ y : GL (Fin n) 𝒪[k], GeneralLinearGroup.map rd y = g) ∧
    ∃ r : Representation ℂ (GL (Fin n) F₀) (fixed ρ (K1 rd n)),
      (∀ (y : GL (Fin n) 𝒪[k]) (x : fixed ρ (K1 rd n)),
        (r (GeneralLinearGroup.map rd y) x : V) = ρ (GeneralLinearGroup.map (algebraMap 𝒪[k] k) y) x) ∧
      ∀ (fb : GL (Fin n) F₀ → ℂ) (A : V →ₗ[ℂ] V) (hA : ∀ x ∈ fixed ρ (K1 rd n), A x ∈ fixed ρ (K1 rd n)),
        GlobalTheory.BCT.twTr ρ (KO k n) (K1 rd n) (infl rd fb) A =
          (Nat.card (GL (Fin n) F₀) : ℂ)⁻¹ * LinearMap.trace ℂ _ (∑ᶠ g, fb g • (r g ∘ₗ A.restrict hA))

def TorBC : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E], (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (π : CuspSub F n) (P : CuspSub E n), (∀ g : E ≃ₐ[F] E, (Cusp.cx P).ConjIso g.toRingEquiv) →
      WeakBC (Cusp.cx π).sat (Cusp.cx P).sat → ∀ (v : Pl F) (w : PlacesOver E v), (∀ w' : PlacesOver E v, w' = w) → GM.Unr E v →
    ∀ [Algebra (v.adicCompletion F) (w.1.adicCompletion E)] [ValuativeExtension (v.adicCompletion F) (w.1.adicCompletion E)]
      [FiniteDimensional (v.adicCompletion F) (w.1.adicCompletion E)] [IsGalois (v.adicCompletion F) (w.1.adicCompletion E)],
      (∀ x, completionMap v w.1 x = algebraMap _ (w.1.adicCompletion E) x) →
    ∀ (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁] (rk : 𝒪[v.adicCompletion F] →+* F₀) (rK : 𝒪[w.1.adicCompletion E] →+* F₁)
      (s : w.1.adicCompletion E ≃ₐ[v.adicCompletion F] w.1.adicCompletion E) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
    ∀ (τ : SmIrr (Gw n v)) (τ' : SmIrr (Gw n w.1)), (Cusp.cx π).locComp v τ → (Cusp.cx P).locComp w.1 τ' →
      ∀ θ : Fin n → (F₀ˣ →* ℂˣ), HasTor rk τ.ρ θ → HasTor rK τ'.ρ fun i => nrmChar F₁ (θ i)

end UpperTheory.Gal.InertialTypesAlt.L
