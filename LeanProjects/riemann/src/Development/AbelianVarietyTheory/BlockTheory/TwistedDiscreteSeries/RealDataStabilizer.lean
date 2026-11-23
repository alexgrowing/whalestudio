import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhds

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult
  MeasureTheory Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics

variable {D : D7}

abbrev Bas (V : HSp D) : Type := D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ

abbrev Pol (S T : HSp D) : Type := MvPolynomial (FVar D T.rank S.rank) ℂ

abbrev MIdx (S T : HSp D) : Type := FVar D T.rank S.rank →₀ ℕ

abbrev cmp (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (g : GA D V) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  infMat D.sp.cm.sig V.gram (θ τ) g

def HasPar (θ : InfFam D) {V : HSp D} (c : CoefA V) (S : D.what₂.Tau → SPar) : Prop :=
  c.Is ∧ ∀ τ, isoDef (gramAt D V τ) (fun g => c.ρ (atTau θ V τ g)) (S τ) = ⊤

def entries (S : SPar) : Finset ℚ := S.image Prod.fst

def entry (S : SPar) (l : ℕ) : ℚ := ((entries S).sort (· ≥ ·)).getD l 0

def hw (S : SPar) (n : ℕ) (l : Fin n) : ℤ := ⌊entry S l - ((n : ℚ) + 1 - 2 * ((l : ℕ) + 1)) / 2⌋

def IsExtremal (θ : InfFam D) {V : HSp D} (B : Bas V) (c : CoefA V) (S : D.what₂.Tau → SPar) (v : c.W) : Prop :=
  ‖v‖ = 1 ∧ ∀ τ (t : Fin V.rank → Circle),
    c.ρ (atTau θ V τ (B τ * Matrix.diagonal (fun a => (t a : ℂ)) * (B τ)⁻¹)) v = (∏ a, (t a : ℂ) ^ hw (S τ) V.rank a) • v

def StrictInterlace (n : ℕ) (A B : Finset ℚ) : Prop :=
  ∃ (a : Fin (n + 1) → ℚ) (b : Fin n → ℚ), A = Finset.univ.image a ∧ B = Finset.univ.image b ∧
    ∀ i : Fin n, b i < a i.castSucc ∧ a i.succ < b i

section Pair

variable (θ : InfFam D) {S T : HSp D} (BS : Bas S) (BT : Bas T) (e : D.what₂.Tau → ℚ)

def vacChar (g : GA D S) (h : GA D T) : ℂ :=
  ∏ τ, (cmp θ S τ g).det ^ ⌊e τ - (T.rank : ℚ) / 2⌋ * (cmp θ T τ h).det ^ (-⌊e τ - (S.rank : ℚ) / 2⌋)

def subst (g : GA D S) (h : GA D T) (x : FVar D T.rank S.rank) : Pol S T :=
  ∑ i, ∑ c, MvPolynomial.C (((BT x.1)⁻¹ * cmp θ T x.1 h * BT x.1) i x.2.1 * ((BS x.1)⁻¹ * cmp θ S x.1 g⁻¹ * BS x.1) x.2.2 c) *
    MvPolynomial.X (x.1, i, c)

def polAct (g : GA D S) (h : GA D T) : Pol S T →ₗ[ℂ] Pol S T :=
  vacChar θ e g h • (MvPolynomial.aeval (subst θ BS BT g h)).toLinearMap

variable (π : CoefA S) (π' : CoefA T)

def dAct {V : HSp D} (c : CoefA V) (g : GA D V) (ξ : Module.Dual ℂ c.W) : Module.Dual ℂ c.W := ξ ∘ₗ c.ρ g⁻¹

abbrev Ker (π : CoefA S) (π' : CoefA T) : Type := Module.Dual ℂ π.W →ₗ[ℂ] π'.W →ₗ[ℂ] Pol S T

def IsInvKer (κ : Ker π π') : Prop :=
  ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∀ ξ v', κ (dAct π g ξ) (π'.ρ h v') = polAct θ BS BT e g h (κ ξ v')

def IsInvElt (σ : Module.Dual ℂ π.W →ₗ[ℂ] Pol S T) : Prop :=
  ∀ g ∈ GinfC S, ∀ ξ, σ (dAct π g ξ) = polAct θ BS BT e g 1 (σ ξ)

def nu (A : D.what₂.Tau → SPar) (S T : HSp D) (τ : D.what₂.Tau) (l : ℕ) : ℕ :=
  ⌊entry (A τ) l + e τ - ((S.rank : ℚ) + T.rank + 1 - 2 * (l + 1)) / 2⌋₊

def minors (A : D.what₂.Tau → SPar) (S T : HSp D) : Pol S T :=
  delta (fun _ => S.rank) (fun _ => 0) (nu e A S T) (fun _ _ => 0)

def IsIt (κ : Ker π π') (ν : Measure (GinfC S)) (it : Pol S T →ₗ[ℂ] π.W →ₗ[ℂ] π'.W) : Prop :=
  ∀ Φ v ξ (d : MIdx S T), (κ ξ (it Φ v)).coeff d = ∫ k, (polAct θ BS BT e k.1 1 Φ).coeff d * ξ (π.ρ k.1 v) ∂ν

def mfact (α : MIdx S T) : ℝ := α.prod fun _ n => (n.factorial : ℝ)

def fock (Φ Φ' : Pol S T) : ℂ := ∑ α ∈ Φ.support, Φ.coeff α * star (Φ'.coeff α) * (mfact α : ℂ)

end Pair

def IsProbHaar (V : HSp D) (ν : Measure (GinfC V)) : Prop := ν.IsHaarMeasure ∧ IsProbabilityMeasure ν

def fp (V : HSp D) (g : GA D V) : GfC V := ⟨GlobalTheory.LevelNbhd.finPartG V g, GlobalTheory.LevelNbhd.finPartG_mem_GfC V g⟩

abbrev VFun {V : HSp D} (c : CoefA V) : Type := GfC V → Module.Dual ℂ c.W

def IsForm {V : HSp D} (c : CoefA V) (G : VFun c) : Prop :=
  (∀ γ ∈ GQ V, ∀ x, G (fp V γ * x) = dAct c γ (G x)) ∧
    ∃ U : Subgroup (GfC V), IsOpen (U : Set (GfC V)) ∧ ∀ k ∈ U, ∀ x, G (x * k) = G x

def scal {V : HSp D} (c : CoefA V) (G : VFun c) (v : c.W) (h : GA D V) : ℂ := G (fp V h) (c.ρ h v)

def ratFin (V : HSp D) : Subgroup (GfC V) := ((GQ V).map (finHom V)).comap ((finHom V).comp (GfC V).subtype)

abbrev Cls (V : HSp D) (K : Subgroup (GfC V)) : Type := DoubleCoset.Quotient (ratFin V : Set (GfC V)) (K : Set (GfC V))

def stab (V : HSp D) (K : Subgroup (GfC V)) (x : GfC V) : Set (GfC V) := {γ | γ ∈ ratFin V ∧ x⁻¹ * γ * x ∈ K}

def ClassFin (V : HSp D) (K : Subgroup (GfC V)) : Prop := Finite (Cls V K) ∧ ∀ x, (stab V K x).Finite

def classSum {V : HSp D} (K : Subgroup (GfC V)) {M : Type} [AddCommGroup M] [Module ℂ M] (F : GfC V → M) : M :=
  ∑ᶠ c : Cls V K, ((stab V K c.out).ncard : ℂ)⁻¹ • F c.out

def IsLevMeas (V : HSp D) (K : Subgroup (GfC V)) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  IsOpen (K : Set (GfC V)) ∧ IsCompact (K : Set (GfC V)) ∧ μ.IsHaarMeasure ∧ μ {g | fp V g ∈ K} = 1 ∧
    IsFundamentalDomain (GQ V) 𝓕 μ

section Global

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (BS : Bas S) (BT : Bas T)

def IsFinDat (S T : HSp D) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f

def pt (f : WO S T → ℂ) : Pol S T →ₗ[ℂ] (WO S T → ℂ) := pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f

def IsColWeil (e : D.what₂.Tau → ℚ) (χ : (AE D)ˣ →* Circle) (om : Om S T) : Prop :=
  IsWeilDatumO ψ S T χ χ om ∧ ∀ τ, HasInfExp D χ τ (-e τ)

variable {π : CoefA S} {π' : CoefA T}

def Th (om : Om S T) (f : WO S T → ℂ) (g : GA D S) (h : GA D T) : Pol S T →ₗ[ℂ] ℂ :=
  LinearMap.proj (0 : WO S T) ∘ₗ om (g, h) ∘ₗ pt ψ θ BS BT f

def Kad (κ : Ker π π') (om : Om S T) (f : WO S T → ℂ) (K : Subgroup (GfC S)) (G : VFun π) : VFun π' :=
  fun h => classSum K fun g => Th ψ θ BS BT om f g.1 h.1 ∘ₗ κ (G g)

def LevInv (om : Om S T) (f : WO S T → ℂ) (K : Subgroup (GfC S)) (G : VFun π) : Prop :=
  ∀ k ∈ K, ∀ g v w, G (g * k) v * om ((g * k).1, 1) f w = G g v * om (g.1, 1) f w

end Global

section Last

variable {V A L : HSp D} (o : OrthDec V A L) (π : CoefA V) (δ : CoefA A)

def tpair (ξ : Module.Dual ℂ π.W) (η : Module.Dual ℂ δ.W) (β : π.W ⊗[ℂ] δ.W) : ℂ :=
  TensorProduct.dualDistrib ℂ π.W δ.W (ξ ⊗ₜ η) β

def branchInv : Submodule ℂ (π.W ⊗[ℂ] δ.W) :=
  ⨅ k : GinfC A, LinearMap.eqLocus (TensorProduct.map (π.ρ (o.emb (k.1, 1))) (δ.ρ k.1)) LinearMap.id

def IsB (β : π.W ⊗[ℂ] δ.W) (ν : Measure (GinfC A)) (b : π.W →ₗ[ℂ] δ.W →ₗ[ℂ] ℂ) : Prop :=
  ∀ v' w ξ η, ∫ k, ξ (π.ρ (o.emb (k.1, 1)) v') * η (δ.ρ k.1 w) ∂ν = b v' w * tpair π δ ξ η β

def Ptil (β : π.W ⊗[ℂ] δ.W) (K : Subgroup (GfC A)) (G : VFun π) (F : VFun δ) : ℂ :=
  classSum K fun g => tpair π δ (G (fp V (o.emb (g.1, 1)))) (F g) β

def LevInvLast (K : Subgroup (GfC A)) (G : VFun π) (F : VFun δ) : Prop :=
  ∀ k ∈ K, ∀ g v w, G (fp V (o.emb ((g * k).1, 1))) v * F (g * k) w = G (fp V (o.emb (g.1, 1))) v * F g w

def per (μ : Measure (GA D A)) (𝓕 : Set (GA D A)) (φ : GA D V → ℂ) (φ' : GA D A → ℂ) : ℂ :=
  ∫ h in 𝓕, φ (o.emb (h, 1)) * φ' h ∂μ

end Last

section Chain

variable (P : TPar D) (θ : InfFam D) (X : ℕ → HSp D) {X' L : HSp D} (o : OrthDec (X D.R.m) X' L) (B : ∀ j, Bas (X j))

def eAt (j : ℕ) (τ : D.what₂.Tau) : ℚ := if h : j < D.R.m then P.e τ ⟨j, h⟩ else 0

def ParOK : Prop :=
  P.t = D.R.t ∧ P.Interlace ∧
  (∀ τ j, ((P.t : ℚ) + 3) / 2 ≤ P.e τ j - P.b τ j) ∧
  (∀ τ (j : Fin D.R.m) (h : j.1 + 1 < D.R.m), ((P.t : ℚ) + 3) / 2 ≤ P.b τ ⟨j.1 + 1, h⟩ - P.e τ j) ∧
  (∀ τ i, ∃ n : ℤ, P.u τ i = n + 1 / 2) ∧ (∀ τ i, ∃ n : ℤ, P.v τ i = n) ∧ (∀ τ j, ∃ n : ℤ, P.b τ j = n) ∧
  ∀ τ j, ∃ n : ℤ, P.e τ j = n

def SpOK (L : HSp D) : Prop :=
  IsInfFam θ ∧ L.rank = 1 ∧
    ∀ j ≤ D.R.m, (X j).rank = D.R.N j ∧ ∀ τ, IsONBasis (gramAt D (X j) τ) 1 (B j τ) (X j).rank

abbrev act (j : ℕ) (g : GA D (X j)) (h : GA D (X (j + 1))) : Pol (X j) (X (j + 1)) →ₗ[ℂ] Pol (X j) (X (j + 1)) :=
  polAct θ (B j) (B (j + 1)) (eAt P j) g h

abbrev MForm (π₀ : CoefA (X 0)) (δ : CoefA X') : Type :=
  π₀.W →ₗ[ℂ] δ.W →ₗ[ℂ] MultilinearMap ℂ (fun j : Fin D.R.m => Pol (X j) (X (j + 1))) ℂ

def LL (π₀ : CoefA (X 0)) (δ : CoefA X') : Submodule ℂ (MForm X π₀ δ) where
  carrier := {l | ∀ (g : ∀ j, GA D (X j)) (h : GA D X'), (∀ j < D.R.m, g j ∈ GinfC (X j)) → h ∈ GinfC X' →
    g D.R.m = o.emb (h, 1) → ∀ v w Φ,
      l (π₀.ρ (g 0) v) (δ.ρ h w) (fun j => act P θ X B j (g j) (g (j + 1)) (Φ j)) = l v w Φ}
  zero_mem' := fun _ _ _ _ _ _ _ _ => rfl
  add_mem' := fun {a b} ha hb g h h1 h2 h3 v w Φ => by
    simp only [LinearMap.add_apply, _root_.add_apply, ha g h h1 h2 h3, hb g h h1 h2 h3]
  smul_mem' := fun c a ha g h h1 h2 h3 v w Φ => by
    simp only [LinearMap.smul_apply, _root_.smul_apply, ha g h h1 h2 h3]

variable {X} (π : ∀ j, CoefA (X j))

def itChain (it : ∀ j, Pol (X j) (X (j + 1)) →ₗ[ℂ] (π j).W →ₗ[ℂ] (π (j + 1)).W) (v : (π 0).W)
    (Φ : ∀ j, Pol (X j) (X (j + 1))) (n : ℕ) : (π n).W :=
  Nat.rec (motive := fun j => (π j).W) v (fun j x => it j (Φ j) x) n

variable (ψ : AddChar (AF D.host.F) ℂ) (om : ∀ j, Om (X j) (X (j + 1))) (f : ∀ j, WO (X j) (X (j + 1)) → ℂ)

def colK (κ : ∀ j, Ker (π j) (π (j + 1))) (K : ∀ j, Subgroup (GfC (X j))) (φ : VFun (π 0)) (n : ℕ) : VFun (π n) :=
  Nat.rec (motive := fun j => VFun (π j)) φ (fun j G => Kad ψ θ (B j) (B (j + 1)) (κ j) (om j) (f j) (K j) G) n

variable (μ : ∀ j, Measure (GA D (X j))) (𝓕 : ∀ j, Set (GA D (X j)))

def liftChain (φ : GA D (X 0) → ℂ) (Ψ : ∀ j, WO (X j) (X (j + 1)) → ℂ) (n : ℕ) : GA D (X n) → ℂ :=
  Nat.rec (motive := fun j => GA D (X j) → ℂ) φ (fun j φ' => liftT (om j) (μ j) (𝓕 j) φ' (Ψ j)) n

abbrev WAll (X : ℕ → HSp D) : Type := ∀ j, WO (X j) (X (j + 1))

open Classical in

def liftAll (φ : GA D (X 0) → ℂ) (Ψ : WAll X → ℂ) (n : ℕ) : GA D (X n) → WAll X → ℂ :=
  Nat.rec (motive := fun j => GA D (X j) → WAll X → ℂ) (fun g => φ g • Ψ)
    (fun j M h w => ∫ g in 𝓕 j, om j (g, h) (fun x => M g (Function.update w j x)) 0 ∂(μ j)) n

open Classical in

def LiftAllConv (φ : GA D (X 0) → ℂ) (Ψ : WAll X → ℂ) : Prop :=
  ∀ j < D.R.m, ∀ h w,
    IntegrableOn (fun g => om j (g, h) (fun x => liftAll om μ 𝓕 φ Ψ j g (Function.update w j x)) 0) (𝓕 j) (μ j)

abbrev MAll (X : ℕ → HSp D) : Type := ∀ j : Fin D.R.m, MIdx (X j) (X (j + 1))

def mono (α : MAll X) (j : Fin D.R.m) : Pol (X j) (X (j + 1)) := MvPolynomial.monomial (α j) 1

def IsRealDat (c : MAll X → ℂ) : Prop :=
  ∀ N : ℕ, Summable fun α => ‖c α‖ ^ 2 * (∏ j, mfact (α j)) * (1 + ∑ j, ((α j).sum fun _ n => (n : ℝ))) ^ N

def datTerm (c : MAll X → ℂ) (w : WAll X) (α : MAll X) : ℂ :=
  c α * ∏ j : Fin D.R.m, pt ψ θ (B j) (B (j + 1)) (f j) (mono α j) (w j)

def datAll (c : MAll X → ℂ) (w : WAll X) : ℂ := ∑' α, datTerm θ B ψ f c w α

def extForm {π₀ : CoefA (X 0)} {δ : CoefA X'} (l : MForm X π₀ δ) (v : π₀.W) (w : δ.W) (c : MAll X → ℂ) : ℂ :=
  ∑ᶠ α, c α * l v w (mono α)

def Weights (P : TPar D) : Prop :=
  (∀ τ, ∀ j : Fin D.R.m, ∀ x ∈ entries (P.Xpar j τ), -P.e τ j + ((P.t : ℚ) + 2) / 2 ≤ x) ∧
  (∀ τ, ∀ j ≤ D.R.m, (entries (P.Xpar j τ)).card = D.R.N j ∧ ∀ x ∈ entries (P.Xpar j τ), ∃ n : ℤ, x = n + 1 / 2) ∧
  ∀ τ, StrictInterlace (D.R.r + D.R.m * D.R.t) (entries (P.Xpar D.R.m τ)) (entries (P.Dpar D.R.m τ))

def StepReal (j : ℕ) (π : CoefA (X j)) (π' : CoefA (X (j + 1))) : Prop :=
  (∃ v v', IsExtremal θ (B j) π (P.Xpar j) v ∧ IsExtremal θ (B (j + 1)) π' (P.Xpar (j + 1)) v') ∧
  minors (eAt P j) (P.Xpar j) (X j) (X (j + 1)) ≠ 0 ∧
  (∀ v v', IsExtremal θ (B j) π (P.Xpar j) v → IsExtremal θ (B (j + 1)) π' (P.Xpar (j + 1)) v' →
    ∃! κ : Ker π π', IsInvKer θ (B j) (B (j + 1)) (eAt P j) π π' κ ∧
      κ (innerₛₗ ℂ v) v' = minors (eAt P j) (P.Xpar j) (X j) (X (j + 1))) ∧
  ∀ κ : Ker π π', IsInvKer θ (B j) (B (j + 1)) (eAt P j) π π' κ → κ ≠ 0 →
    (∀ σ, IsInvElt θ (B j) (B (j + 1)) (eAt P j) π σ → ∃! v', σ = κ.flip v') ∧
    ∀ ν, IsProbHaar (X j) ν →
      (∃! it, IsIt θ (B j) (B (j + 1)) (eAt P j) π π' κ ν it) ∧
      ∀ it, IsIt θ (B j) (B (j + 1)) (eAt P j) π π' κ ν it →
        Function.Surjective (TensorProduct.lift it) ∧
        (∀ g ∈ GinfC (X j), ∀ Φ v, it (act P θ X B j g 1 Φ) (π.ρ g v) = it Φ v) ∧
        (∀ h ∈ GinfC (X (j + 1)), ∀ Φ v, it (act P θ X B j 1 h Φ) v = π'.ρ h (it Φ v)) ∧
        ∀ Φ, (∀ ξ v', fock Φ (κ ξ v') = 0) → it Φ = 0

def StepGlobal (j : ℕ) (π : CoefA (X j)) (π' : CoefA (X (j + 1))) : Prop :=
  ∀ κ : Ker π π', IsInvKer θ (B j) (B (j + 1)) (eAt P j) π π' κ → κ ≠ 0 → ∀ ν, IsProbHaar (X j) ν →
  ∀ it, IsIt θ (B j) (B (j + 1)) (eAt P j) π π' κ ν it →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) χ (om : Om (X j) (X (j + 1))), IsColWeil ψ (eAt P j) χ om →
  ∀ f, IsFinDat ψ θ (X j) (X (j + 1)) f → ∀ G, IsForm π G → ∀ K μ 𝓕, IsLevMeas (X j) K μ 𝓕 → LevInv om f K G →
    ClassFin (X j) K ∧ IsForm π' (Kad ψ θ (B j) (B (j + 1)) κ om f K G) ∧
    ∀ v Φ, (∀ h, IntegrableOn (fun g => om (g, h) (pt ψ θ (B j) (B (j + 1)) f Φ) 0 * scal π G v g) 𝓕 μ) ∧
      liftT om μ 𝓕 (scal π G v) (pt ψ θ (B j) (B (j + 1)) f Φ) =
        scal π' (Kad ψ θ (B j) (B (j + 1)) κ om f K G) (it Φ v)

def LastStep (π : CoefA (X D.R.m)) (δ : CoefA X') : Prop :=
  Module.finrank ℂ (branchInv o π δ) = 1 ∧
  ∀ β ∈ branchInv o π δ, β ≠ 0 → ∀ ν, IsProbHaar X' ν →
    (∃! b, IsB o π δ β ν b) ∧ ∀ b, IsB o π δ β ν b →
      b ≠ 0 ∧ (∀ k ∈ GinfC X', ∀ v' w, b (π.ρ (o.emb (k, 1)) v') (δ.ρ k w) = b v' w) ∧
      ∀ G F, IsForm π G → IsForm δ F → ∀ K μ 𝓕, IsLevMeas X' K μ 𝓕 → LevInvLast o π δ K G F →
        ClassFin X' K ∧ ∀ v' w, IntegrableOn (fun h => scal π G v' (o.emb (h, 1)) * scal δ F w h) 𝓕 μ ∧
          per o μ 𝓕 (scal π G v') (scal δ F w) = b v' w * Ptil o π δ β K G F

def IsLam {δ : CoefA X'} (it : ∀ j, Pol (X j) (X (j + 1)) →ₗ[ℂ] (π j).W →ₗ[ℂ] (π (j + 1)).W)
    (b : (π D.R.m).W →ₗ[ℂ] δ.W →ₗ[ℂ] ℂ) (l : MForm X (π 0) δ) : Prop :=
  ∀ v w (Φ : ∀ j, Pol (X j) (X (j + 1))), l v w (fun j => Φ j) = b (itChain π it v Φ D.R.m) w

def Factor {δ : CoefA X'} (κ : ∀ j, Ker (π j) (π (j + 1))) (β : (π D.R.m).W ⊗[ℂ] δ.W) (l : MForm X (π 0) δ) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (χ : ℕ → (AE D)ˣ →* Circle) (om : ∀ j, Om (X j) (X (j + 1)))
    (f : ∀ j, WO (X j) (X (j + 1)) → ℂ) (φ : VFun (π 0)) (F : VFun δ) (K : ∀ j, Subgroup (GfC (X j)))
    (μ : ∀ j, Measure (GA D (X j))) (𝓕 : ∀ j, Set (GA D (X j))) (K' : Subgroup (GfC X')) (μ' : Measure (GA D X'))
    (𝓕' : Set (GA D X')),
    (∀ j < D.R.m, IsColWeil ψ (eAt P j) (χ j) (om j) ∧ IsFinDat ψ θ (X j) (X (j + 1)) (f j) ∧
      IsLevMeas (X j) (K j) (μ j) (𝓕 j) ∧ LevInv (om j) (f j) (K j) (colK θ B π ψ om f κ K φ j)) →
    IsForm (π 0) φ → IsForm δ F → IsLevMeas X' K' μ' 𝓕' →
    LevInvLast o (π D.R.m) δ K' (colK θ B π ψ om f κ K φ D.R.m) F →
    (∀ v w (Φ : ∀ j, Pol (X j) (X (j + 1))),
      per o μ' 𝓕' (liftChain om μ 𝓕 (scal (π 0) φ v) (fun j => pt ψ θ (B j) (B (j + 1)) (f j) (Φ j)) D.R.m) (scal δ F w) =
        l v w (fun j => Φ j) * Ptil o (π D.R.m) δ β K' (colK θ B π ψ om f κ K φ D.R.m) F) ∧
    ∀ c : MAll X → ℂ, IsRealDat c → (∀ x, Summable (datTerm θ B ψ f c x)) ∧ ∀ v w,
      LiftAllConv om μ 𝓕 (scal (π 0) φ v) (datAll θ B ψ f c) ∧
      IntegrableOn (fun h => liftAll om μ 𝓕 (scal (π 0) φ v) (datAll θ B ψ f c) D.R.m (o.emb (h, 1)) 0 * scal δ F w h) 𝓕' μ' ∧
      per o μ' 𝓕' (fun h => liftAll om μ 𝓕 (scal (π 0) φ v) (datAll θ B ψ f c) D.R.m h 0) (scal δ F w) =
        extForm l v w c * Ptil o (π D.R.m) δ β K' (colK θ B π ψ om f κ K φ D.R.m) F

def Construct (δ : CoefA X') : Prop :=
  ∀ (κ : ∀ j, Ker (π j) (π (j + 1))) (ν : ∀ j, Measure (GinfC (X j)))
    (it : ∀ j, Pol (X j) (X (j + 1)) →ₗ[ℂ] (π j).W →ₗ[ℂ] (π (j + 1)).W),
    (∀ j < D.R.m, IsInvKer θ (B j) (B (j + 1)) (eAt P j) (π j) (π (j + 1)) (κ j) ∧ κ j ≠ 0 ∧ IsProbHaar (X j) (ν j) ∧
      IsIt θ (B j) (B (j + 1)) (eAt P j) (π j) (π (j + 1)) (κ j) (ν j) (it j)) →
  ∀ β ∈ branchInv o (π D.R.m) δ, β ≠ 0 → ∀ ν', IsProbHaar X' ν' → ∀ b, IsB o (π D.R.m) δ β ν' b →
    ∃ l : MForm X (π 0) δ, IsLam π it b l ∧ l ∈ LL P θ X o B (π 0) δ ∧ l ≠ 0 ∧
      LL P θ X o B (π 0) δ = Submodule.span ℂ {l} ∧
      {α : MAll X | ∃ v w, l v w (mono α) ≠ 0}.Finite ∧ Factor P θ o B π κ β l

end Chain

def OneFunctional (D : D7) : Prop :=
  ∀ (P : TPar D), ParOK P → Weights P ∧
    ∀ (θ : InfFam D) (X : ℕ → HSp D) (X' L : HSp D) (o : OrthDec (X D.R.m) X' L) (B : ∀ j, Bas (X j)), SpOK θ X B L →
      (∀ j ≤ D.R.m, ∃ c : CoefA (X j), HasPar θ c (P.Xpar j)) ∧ (∃ δ : CoefA X', HasPar θ δ (parB P D.R.m)) ∧
      (∀ (π₀ : CoefA (X 0)) (δ : CoefA X'), HasPar θ π₀ (P.Xpar 0) → HasPar θ δ (parB P D.R.m) →
        Module.rank ℂ (LL P θ X o B π₀ δ) = 1) ∧
      (∀ j < D.R.m, ∀ (π : CoefA (X j)) (π' : CoefA (X (j + 1))), HasPar θ π (P.Xpar j) → HasPar θ π' (P.Xpar (j + 1)) →
        StepReal P θ B j π π' ∧ StepGlobal P θ B j π π') ∧
      (∀ (π : CoefA (X D.R.m)) (δ : CoefA X'), HasPar θ π (P.Xpar D.R.m) → HasPar θ δ (parB P D.R.m) → LastStep o π δ) ∧
      ∀ (π : ∀ j, CoefA (X j)) (δ : CoefA X'), (∀ j ≤ D.R.m, HasPar θ (π j) (P.Xpar j)) → HasPar θ δ (parB P D.R.m) →
        Construct P θ o B π δ

example : StrictInterlace 1 {3 / 2, -1 / 2} {0} :=
  ⟨![3 / 2, -1 / 2], ![0], by ext x; simp [Fin.exists_fin_two, eq_comm], by ext x; simp [eq_comm],
    fun i => by fin_cases i; norm_num⟩

example (θ : InfFam D) {S T : HSp D} (BS : Bas S) (BT : Bas T) (e : D.what₂.Tau → ℚ) (g : GA D S) (h : GA D T) :
    polAct θ BS BT e g h 1 = vacChar θ e g h • (1 : Pol S T) := by simp [polAct]

end GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics

end
