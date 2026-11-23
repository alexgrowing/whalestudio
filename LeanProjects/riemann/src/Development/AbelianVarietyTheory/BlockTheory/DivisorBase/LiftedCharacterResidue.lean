import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.BaseEmbeddingInclusion
import Formalism.LocalToGlobal.ProjectiveLattices.KsCore
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LiftedCharacterResidue

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def stabLat (V : HSp D) : Subgroup (GA D V) where
  carrier := {k | k ∈ GfC V ∧ ∀ z, (finHom V k).1.mulVec z ∈ latHat V ↔ z ∈ latHat V}
  one_mem' := ⟨(GfC V).one_mem, fun z => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(GfC V).mul_mem ha hb, fun z => ?_⟩
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ha', hb']
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(GfC V).inv_mem ha, fun z => ?_⟩
    rw [← ha' ((finHom V a⁻¹).1.mulVec z), Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel,
      map_one, Units.val_one, Matrix.one_mulVec]

def prinLev (V : HSp D) (N : ℕ) : Set (GA D V) :=
  {k | k ∈ stabLat V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y}

abbrev levN (D : D7) : ℕ := D.host.g 0 * D.host.g 1

def jx {j : ℕ} (hj : InR D j) : Fin D.R.m := ⟨j - 1, by have := hj.1; have := hj.2; omega⟩

def IsKappa {j : ℕ} (hj : InR D j) (κ : WeightFamilies.Wt D j) : Prop :=
  κ.n = D.R.r + D.R.t ∧ ∀ τ : D.what₂.Tau,
    (∀ i, (κ.aP τ i : ℚ) + (κ.n : ℚ) / 2 - (D.hc τ).e (jx hj) =
      Formalism.L2.NTheta.kapQ (D.hc τ) (D.R.sigW j).1 (D.R.sigW j).2 (Sum.inl i)) ∧
    ∀ i, -(κ.aM τ (Fin.rev i) : ℚ) - (κ.n : ℚ) / 2 - (D.hc τ).e (jx hj) =
      Formalism.L2.NTheta.kapQ (D.hc τ) (D.R.sigW j).1 (D.R.sigW j).2 (Sum.inr i)

variable (T : CoreJ D)

def SitsAt (σ : T.Q.c.F →+* ℂ) (τ ρ : D.what₂.Tau) : Prop := relab T.Q.c σ (tauE D τ) = tauE D ρ

def IsLiftChar {j : ℕ} (hj : InR D j) : Prop :=
  (∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = levN D • y) → T.chiW j T.σ₀ x = 1) ∧
    ∀ σ, GoodEmb T.Q.c σ → ∀ τ ρ, SitsAt T σ τ ρ → HasInfExp D (T.chiW j σ) ρ (-(D.hc τ).e (jx hj))

def conjWt (V : HSp D) (lab : D.what₂.Tau → D.what₂.Tau) (ρ : D.what₂.Tau) :
    Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 → ℤ :=
  Formalism.L2.NTheta.kapW (D.hc (lab ρ)) _ _

def iotaW {j : ℕ} (hj : InR D j) : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2)) ∘ₗ T.iota j

def Reduces {j : ℕ} (hj : InR D j) (k : GA D (D.sp.W j)) (u : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) : Prop :=
  ∀ a ∈ T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La),
    ∃ w ∈ latGHat (D.sp.W j) 1,
      finVec (D.sp.W j) (iotaW T hj (u a)) - (finHom (D.sp.W j) k).1.mulVec (finVec (D.sp.W j) (iotaW T hj a)) =
        levN D • w

abbrev LevEnd (j : ℕ) : Type :=
  ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) × ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)

def IsCover {j : ℕ} (hj : InR D j) {G : Type} [Group G] (red : stabLat (D.sp.W j) →* G) (lev : G → LevEnd T j) :
    Prop :=
  Function.Surjective red ∧ (∀ k : stabLat (D.sp.W j), red k = 1 ↔ (k : GA D (D.sp.W j)) ∈ prinLev (D.sp.W j) (levN D)) ∧
    (∀ k : stabLat (D.sp.W j), Reduces T hj k (lev (red k)).1) ∧ ∀ g, (lev g).2 = LinearMap.id

def KeepsInt (j : ℕ) (κ : WeightFamilies.Wt D j) {G : Type} [Group G] (lev : G → LevEnd T j) : Prop :=
  ∀ g, ∀ f ∈ T.C j κ, (∀ la (y : T.PtM j la), T.nrmM j la y f ≤ 1) →
    ∀ la (y : T.PtM j la), T.nrmM j la y (actLev (Xo := T.Q.Xo j) T.Q.c lev g f) ≤ 1

variable {LL : Type} [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]

def IsChiDet {j : ℕ} (σ₀ : LL →+* ℂ) {G : Type} [Group G] (red : stabLat (D.sp.W j) →* G) (χ : G →* LLˣ) : Prop :=
  ∀ (k : stabLat (D.sp.W j)) (x : (AE D)ˣ), IsDetRoot (D.sp.W j) k x →
    σ₀ (χ (red k) : LL) = (((T.chiW j T.σ₀ x)⁻¹ : Circle) : ℂ)

abbrev resK (σ : LL →+* ℂ) : T.Q.c.F →+* ℂ := σ.comp (algebraMap T.Q.c.F LL)

def Pos (σ : LL →+* ℂ) : Prop := GoodEmb T.Q.c (resK T σ)

abbrev Phases (j : ℕ) : Type := ∀ σ : T.Q.c.F →+* ℂ, (T.U j σ).Comp → ℂ

def UnitPhases {j : ℕ} (c : Phases T j) : Prop := ∀ σ, GoodEmb T.Q.c σ → CUnit (c σ)

def castFun {V V' : HSp D} (h : V = V') : (GA D V → ℂ) →ₗ[ℂ] (GA D V' → ℂ) :=
  LinearMap.funLeft ℂ ℂ (cast (congrArg (GA D) h.symm))

def readK {j : ℕ} (κ : WeightFamilies.Wt D j) (c : Phases T j) (σ : T.Q.c.F →+* ℂ) (h : T.V j σ = D.sp.W j) :
    T.C j κ →ₛₗ[σ] (GA D (D.sp.W j) → ℂ) :=
  (((lieFac (T.Q.Dw j) (xiR D) (wtA κ) : ℝ) : ℂ) • (castFun h ∘ₗ
      adel (T.V j σ) (T.dict j σ) (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) (c σ)))).comp
    ((rdU (T.U j σ)).comp (T.C j κ).subtype)

abbrev FormsLL (LL : Type) [Field LL] [Algebra T.Q.c.F LL] (j : ℕ) (κ : WeightFamilies.Wt D j) : Type :=
  LL ⊗[T.Q.c.F] T.C j κ

def readL {j : ℕ} (κ : WeightFamilies.Wt D j) (c : Phases T j) (σ : LL →+* ℂ) (h : T.V j (resK T σ) = D.sp.W j) :
    FormsLL T LL j κ →ₛₗ[σ] (GA D (D.sp.W j) → ℂ) :=
  extJ σ (readK T κ c (resK T σ) h)

def IsoFor {j : ℕ} (κ : WeightFamilies.Wt D j) (c : Phases T j) (σ : LL →+* ℂ) (h : T.V j (resK T σ) = D.sp.W j)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {S : D.what₂.Tau → SPar}
    (M : DSModel (D.sp.W j) S) : Prop :=
  ∃ (v₀ : M.Vec) (J : FormsLL T LL j κ →ₛₗ[σ] Mult θ M (prinLev (D.sp.W j) (levN D)) (fun _ => 1)),
    (∀ ρ, ‖(v₀ ρ : M.H ρ)‖ = 1) ∧
    (∀ Φ ∈ Mult θ M (prinLev (D.sp.W j) (levN D)) (fun _ => 1), Φ v₀ = 0 → Φ = 0) ∧
    (∀ x, (J x : MMap M) v₀ = readL T κ c σ h x) ∧
    (∀ (n : ℕ) (b : Fin n → FormsLL T LL j κ), LinearIndependent LL b → LinearIndependent ℂ fun i => J (b i)) ∧
    Submodule.span ℂ (Set.range J) = ⊤

def IsoAt {j : ℕ} (κ : WeightFamilies.Wt D j) (c : Phases T j) (σ : LL →+* ℂ) (h : T.V j (resK T σ) = D.sp.W j) : Prop :=
  AllSome (IsInfFam (D := D)) fun θ =>
    AllSome (fun lab : D.what₂.Tau → D.what₂.Tau => ∀ ρ, SitsAt T (resK T σ) (lab ρ) ρ) fun lab =>
      AllSome (fun _ : DSModel (D.sp.W j) (parW (D.sp.W j) (conjWt (D.sp.W j) lab)) => True) fun M =>
        IsoFor T κ c σ h θ M

def EquivAt {j : ℕ} (κ : WeightFamilies.Wt D j) (c : Phases T j) {G : Type} [Group G] (red : stabLat (D.sp.W j) →* G)
    (lev : G → LevEnd T j) (χ : G →* LLˣ) (σ : LL →+* ℂ) (h : T.V j (resK T σ) = D.sp.W j) : Prop :=
  ∀ (k : stabLat (D.sp.W j)) (x : FormsLL T LL j κ) (g : GA D (D.sp.W j)),
    readL T κ c σ h (rhoOf LL (KsCore.rhoGeo T.toCore j κ lev) (red k) x) g =
      σ (χ (red k) : LL) * readL T κ c σ h x (g * k)

def UnifWith (hT : LawsJ T) {j : ℕ} (hj : InR D j) (κ : WeightFamilies.Wt D j) (c : Phases T j) {G : Type} [Group G]
    (red : stabLat (D.sp.W j) →* G) (lev : G → LevEnd T j) (χ : G →* LLˣ) : Prop :=
  ∀ (σ : LL →+* ℂ) (hσ : Pos T σ),
    IsoAt T κ c σ (hT.spaceW j hj _ hσ) ∧ EquivAt T κ c red lev χ σ (hT.spaceW j hj _ hσ)

def UnifEvery (hT : LawsJ T) : Prop :=
  ∀ (j : ℕ) (hj : InR D j) (κ : WeightFamilies.Wt D j), IsKappa hj κ → IsLiftChar T hj →
    ∀ (LL : Type) [Field LL] [NumberField LL] [Algebra T.Q.c.F LL] (σ₀ : LL →+* ℂ), BaseEmbeddingInclusion T.Q.c.F σ₀ →
      (∀ k ∈ stabLat (D.sp.W j), ∃ u, Reduces T hj k u) ∧
      (∀ c : Phases T j, UnitPhases T c → ∀ (σ : LL →+* ℂ) (hσ : Pos T σ), IsoAt T κ c σ (hT.spaceW j hj _ hσ)) ∧
      ∀ (G : Type) [Group G] (red : stabLat (D.sp.W j) →* G) (lev : G → LevEnd T j), IsCover T hj red lev →
        ActLev (Xo := T.Q.Xo j) T.Q.c lev ∧ KsCore.KeepsCu T.toCore j κ lev ∧ KeepsInt T j κ lev ∧
        AllSome (IsChiDet T σ₀ red) fun χ : G →* LLˣ =>
          ∃ c : Phases T j, UnitPhases T c ∧ UnifWith T hT hj κ c red lev χ

def Unif (D : D7) : Prop := ∀ (T : CoreJ D) (hT : LawsJ T), UnifEvery T hT

end GlobalTheory.IndefiniteRowSideFullHecke.LiftedCharacterResidue
