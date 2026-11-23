import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod

noncomputable section

namespace GlobalTheory.PendOf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.NPin ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def IsConjGen (D : D7) (w w' : PlE D.host) (γ γ' : GE D.nd) : Prop :=
  ∃ c : D.nd.Om ≃+* D.nd.Om,
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
    (∀ y, y ∈ D.nd.plOm.1 w ↔ c y ∈ D.nd.plOm.1 w') ∧ ∀ y, γ' (c y) = c (γ y)

def LabAll (D : D7) (T : WDTie D.nd D.naut) : Prop :=
  ∃ γ : Fin 2 → PlE D.host → GE D.nd, (∀ k v, γ k (D.naut.plGw k v) = D.ntypes.tg k v) ∧
    (∀ k v w', IsConjPl D.host (D.naut.plGw k v) w' →
      IsConjGen D (D.naut.plGw k v) w' (D.ntypes.tg k v) (γ k w')) ∧
    ∀ k : Fin 2, ∀ w ∈ placesOver D.host.E (D.host.g k), ∀ a : D.naut.LP w,
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      D.naut.items₂ k w a = GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) (γ k w) (T.e w a)

def gPl (D : D7) : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) :=
  {v | ∃ kv : (Σ k : Fin 2, D.nd.PlG k), NG.OverPl (D.naut.plGw kv.1 kv.2) v}

def IsLiftAt {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L) (r p : ℕ)
    (g : GL (Fin r) (ZMod p)) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Prop :=
  ∀ a b : Fin n,
    if hab : a.val < r ∧ b.val < r then
      Valued.v (h.val a b - (((g : Matrix (Fin r) (Fin r) (ZMod p)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩).val :
        s.v.adicCompletion (maximalRealSubfield L))) < 1
    else h.val a b = if a = b then 1 else 0

def IsTypeGroupBlockLift (D : D7) (n : ℕ) (L : G0g D.nd → GAf D.host.E n) : Prop :=
  ∀ g : G0g D.nd, TrivOutside (gPl D) (L g) ∧
    ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E), s.w = D.naut.plGw kv.1 kv.2 →
      IsLiftAt s D.R.r (D.host.g kv.1) (g kv) (s.loc n (L g))

def actSum (D : D7) {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (L : G0g D.nd → GAf D.host.E n)
    (z : MonoidAlgebra ℂ (G0g D.nd)) (f : GAf D.host.E n → W) : GAf D.host.E n → W :=
  z.coeff.sum fun g c => c • NG.rt D.host.E n (L g) f

def CenReal (D : D7) (M : MtFam D) : Prop :=
  ∀ (μ : D.what₂.Tup) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), ∃ L : G0g D.nd → GAf D.host.E D.R.nV,
    IsTypeGroupBlockLift D D.R.nV L ∧ ∀ (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) (x : D.what₂.Mt μ j),
      (M μ j h1 h2).real (D.ntypes.cenMt μ j z x) = actSum D L (z : MonoidAlgebra ℂ (G0g D.nd)) ((M μ j h1 h2).real x)

def GreenLab {D : D7} (Γ : GrpSide D) : Prop :=
  ∀ (k : Fin 2) (d : ℕ), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ τ : FDRep ℂ (GL (Fin d) (ZMod (D.host.g k))), 1 ≤ d → CategoryTheory.Simple τ →
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod (D.host.g k)) τ →
      Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k)) τ
        ((Γ.O k).lab d τ)

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def IsLiftN {n r p : ℕ} (g : GL (Fin r) (ZMod p)) (h : GL (Fin n) F) : Prop :=
  ∀ a b : Fin n,
    if hab : a.val < r ∧ b.val < r then
      valuation F (h.val a b - (((g : Matrix (Fin r) (Fin r) (ZMod p)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩).val : F)) < 1
    else h.val a b = if a = b then 1 else 0

def NotKilled {n r p : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) F) W)
    (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (v : W) : Prop :=
  ∃ ℓ : GL (Fin r) (ZMod p) → GL (Fin n) F, (∀ g, IsLiftN g (ℓ g)) ∧ (z.coeff.sum fun g c => c • π (ℓ g) v) ≠ 0

def IsLevelOne {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) F) W) (v : W) : Prop :=
  ∀ h : GL (Fin n) F, (∀ a b, valuation F (h.val a b - if a = b then 1 else 0) < 1) → π h v = v

end Local

def labAt (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (π : Irr ((D.naut.plGw k v).adicCompletion D.host.E) n) : (ZMod (D.host.g k))[X] :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (rcAt hL D (D.naut.plGw k v) n π)

def InSeries (D : D7) (k : Fin 2) (ρ : FDRep ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) (f : (ZMod (D.host.g k))[X]) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  CategoryTheory.Simple ρ ∧ Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * D.ntypes.eSer k f = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ

def idemOf (D : D7) (k : Fin 2) (ρ : FDRep ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ

def RegLoc (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (π : Irr ((D.naut.plGw k v).adicCompletion D.host.E) D.R.r) ρ f, InSeries D k ρ f →
    Squarefree f → (∃ x, IsLevelOne π.π x ∧ NotKilled π.π (idemOf D k ρ) x) →
    (rcAt hL D (D.naut.plGw k v) D.R.r π).mono0 ∧ labAt hL D k v π = f

def SplitLoc (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (u : ZMod (D.host.g k)) (π : Irr ((D.naut.plGw k v).adicCompletion D.host.E) (D.R.r + D.R.t)) ρ f,
    IsTame χ → labAt hL D k v (Irr.ofDet 1 χ hχ) = X - C u → InSeries D k ρ f → ¬ f.IsRoot u →
    (∃ x, IsBlockVec χ π.π x ∧ NotKilled π.π (idemOf D k ρ) x) →
    ∃ (π₁ : Irr ((D.naut.plGw k v).adicCompletion D.host.E) D.R.r)
      (π₂ : Irr ((D.naut.plGw k v).adicCompletion D.host.E) D.R.t), IsSpherical π₂.π ∧
      Nonempty (π.π.Equiv (prod₂ π₁.π (twist π₂.π (detChar (Fin D.R.t) χ)))) ∧
      ∃ y, IsLevelOne π₁.π y ∧ NotKilled π₁.π (idemOf D k ρ) y

def LocDZ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (u : ZMod (D.host.g k)) (π : Irr ((D.naut.plGw k v).adicCompletion D.host.E) (D.R.r + D.R.t)) ρ f,
    IsTame χ → labAt hL D k v (Irr.ofDet 1 χ hχ) = X - C u → InSeries D k ρ f → Squarefree f → ¬ f.IsRoot u →
    (∃ x, IsBlockVec χ π.π x ∧ NotKilled π.π (idemOf D k ρ) x) →
    (rcAt hL D (D.naut.plGw k v) _ π).mono0 ∧ labAt hL D k v π = f * (X - C u) ^ D.R.t

def ConjDual (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (w' : PlE D.host),
    IsConjPl D.host (D.naut.plGw k v) w' → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (D.naut.mono0 (D.naut.locV i PI (D.naut.plGw k v)) → D.naut.mono0 (D.naut.locV i PI w')) ∧
    (TameLP D (D.naut.locV i PI (D.naut.plGw k v)) → TameLP D (D.naut.locV i PI w')) ∧
    Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w' (D.naut.locV i PI w')) =
      (Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locV i PI (D.naut.plGw k v)))).map (·⁻¹)

end GlobalTheory.PendOf

end
