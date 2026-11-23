import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.BaseEmbeddingInclusion
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Side (D : D7) (σ : D.what₂.LL →+* ℂ) : Prop :=
  ∀ x : D.host.K, σ (D.embE (algebraMap D.host.K D.host.E x)) =
    D.what₂.embLL (D.embE (algebraMap D.host.K D.host.E x))

abbrev Emb (D : D7) : Type := {σ : D.what₂.LL →+* ℂ // Side D σ}

def SitsAt (D : D7) (σ : D.what₂.LL →+* ℂ) (τ τ' : D.what₂.Tau) : Prop :=
  ∃ t : D.host.E →+* D.what₂.LL, D.what₂.embLL.comp t = tauE D τ ∧ σ.comp t = tauE D τ'

def IsConjPar (D : D7) (j : ℕ) (σ : D.what₂.LL →+* ℂ) (S : D.what₂.Tau → SPar) : Prop :=
  ∀ τ', ∃ τ, SitsAt D σ τ τ' ∧ S τ' = parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)) τ

variable {D : D7}

def levSet (V : HSp D) (N : ℕ) : Set (GA D V) :=
  {k | k ∈ GfC V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y}

def IsCover (V : HSp D) {G0 : Type} [Group G0] (Lift : G0 → GA D V → Prop) : Prop :=
  (∀ κ, κ ∈ levSet V 1 ↔ ∃ g, Lift g κ) ∧ (∀ g, ∃ κ, Lift g κ) ∧
    (∀ g g' κ, Lift g κ → Lift g' κ → g = g') ∧
    (∀ g g' κ κ', Lift g κ → Lift g' κ' → Lift (g * g') (κ * κ')) ∧
    ∀ κ, Lift 1 κ ↔ κ ∈ levSet V (D.host.g 0 * D.host.g 1)

abbrev MultK (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) : Submodule ℂ (MMap M) :=
  Mult θ M (levSet V (D.host.g 0 * D.host.g 1)) (fun _ => 1)

def UnifCl (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) {WL : Type} [AddCommGroup WL] [Module D.what₂.LL WL] {G0 : Type} [Group G0]
    (Lift : G0 → GA D V → Prop) (ρ : G0 →* (WL →ₗ[D.what₂.LL] WL)) (χ : G0 →* D.what₂.LLˣ) (σ : D.what₂.LL →+* ℂ)
    (J : WL →ₛₗ[σ] MMap M) : Prop :=
  (∀ (n : ℕ) (b : Fin n → WL), LinearIndependent D.what₂.LL b → LinearIndependent ℂ (fun i => J (b i))) ∧
    Submodule.span ℂ (Set.range J) = MultK θ M ∧
    ∀ g κ, Lift g κ → ∀ (x : WL) (v : M.Vec) (h : GA D V),
      J (ρ g x) v h = σ ((χ g : D.what₂.LLˣ) : D.what₂.LL) * J x v (h * κ)

def IsAnSide (j : ℕ) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : Emb D → HSp D)
    (S : Emb D → D.what₂.Tau → SPar) (M : ∀ σ, DSModel (V σ) (S σ)) {G0 : Type} [Group G0]
    (Lift : ∀ σ, G0 → GA D (V σ) → Prop) {W : (D.what₂.LL →+* ℂ) → Type} [∀ σ, AddCommGroup (W σ)]
    [∀ σ, Module ℂ (W σ)] (ev : ∀ σ : Emb D, W σ.1 →ₗ[ℂ] MMap (M σ)) : Prop :=
  InR D j ∧ IsInfFam θ ∧ ∀ σ : Emb D, V σ = D.sp.W j ∧ IsConjPar D j σ.1 (S σ) ∧ IsCover (V σ) (Lift σ) ∧
    Function.Injective (ev σ) ∧ LinearMap.range (ev σ) = MultK θ (M σ)

def UnifEvery (j : ℕ) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : Emb D → HSp D)
    (S : Emb D → D.what₂.Tau → SPar) (M : ∀ σ, DSModel (V σ) (S σ)) {G0 : Type} [Group G0]
    (Lift : ∀ σ, G0 → GA D (V σ) → Prop) {W : (D.what₂.LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)]
    [∀ σ, InnerProductSpace ℂ (W σ)] (ev : ∀ σ : Emb D, W σ.1 →ₗ[ℂ] MMap (M σ))
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {WL : Type} [AddCommGroup WL] [Module D.what₂.LL WL] [Module Ks WL] [IsScalarTower Ks D.what₂.LL WL]
    (A : Formalism.IndefR.Arith.FormsL D.what₂.LL Ks WL W G0) : Prop :=
  IsAnSide j θ V S M Lift ev ∧ ∀ σ : Emb D, UnifCl θ (M σ) (Lift σ) A.ρ A.chi σ.1 ((ev σ).comp (A.j σ.1))

def IsKappa (j : ℕ) (e : D.what₂.Tau → ℤ) (w : WeightFamilies.Wt D j) : Prop :=
  (∀ τ (i : Fin D.R.m), i.1 + 1 = j → (e τ : ℚ) = (D.hc τ).e i) ∧ w.n = D.R.nV ∧
    (∀ τ i, (w.aP τ i : ℤ) + ((w.n / 2 : ℕ) : ℤ) =
      Formalism.L2.NTheta.kapW (D.hc τ) (D.R.sigW j).1 (D.R.sigW j).2 (Sum.inl i) + e τ) ∧
    ∀ τ c, -(w.aM τ (Fin.rev c) : ℤ) - ((w.n / 2 : ℕ) : ℤ) =
      Formalism.L2.NTheta.kapW (D.hc τ) (D.R.sigW j).1 (D.R.sigW j).2 (Sum.inr c) + e τ

def IsLowVec {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (v : M.Vec) : Prop :=
  ∀ τ, (v τ : M.H τ) ≠ 0 ∧ ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    M.rep τ g (v τ) ∈ Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ)

variable (T : CoreJ D) (j : ℕ)

abbrev GLev : Type := LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l

def geoAct (γ : GLev T j) : T.R j →ₗ[T.Q.c.F] T.R j :=
  actLev (Xo := T.Q.Xo j) T.Q.c (fun γ' : GLev T j => (liftLa γ', LinearMap.id)) γ

def Induces (V : HSp D) (γ : GLev T j) (κ : GA D V) : Prop :=
  κ ∈ levSet V 1 ∧ ∃ hr : V.rank = D.R.r, ∀ a : (T.Q.Dw j).La,
    (finHom V κ).1.mulVec (finVec V (T.iota j a ∘ Fin.cast hr)) - finVec V (T.iota j (liftLa γ a) ∘ Fin.cast hr) ∈
      AddSubgroup.closure {u | ∃ b ∈ T.Q.l.Mb, ∃ z ∈ latGHat V 1, u = halfVec V b z}

abbrev Cu (w : WeightFamilies.Wt D j) : Type := T.cuspA j (wtA w) w.n

def rdK (w : WeightFamilies.Wt D j) (s : T.Q.c.F →+* ℂ) (c : (T.U j s).Comp → ℂ) : T.R j →ₛₗ[s] (GA D (T.V j s) → ℂ) :=
  ((lieFac (T.Q.Dw j) (xiR D) (wtA w) : ℂ) •
    adel (T.V j s) (T.dict j s) (muPin (T.V j s) (T.dict j s) (T.mu j s) c)).comp (rdU (T.U j s))

variable [Algebra T.Q.c.F D.what₂.LL]

abbrev res (σ : D.what₂.LL →+* ℂ) : T.Q.c.F →+* ℂ := σ.comp (algebraMap T.Q.c.F D.what₂.LL)

def rdL (w : WeightFamilies.Wt D j) (σ : D.what₂.LL →+* ℂ) (c : (T.U j (res T σ)).Comp → ℂ) :
    D.what₂.LL ⊗[T.Q.c.F] Cu T j w →ₛₗ[σ] (GA D (T.V j (res T σ)) → ℂ) :=
  extJ σ ((rdK T j w (res T σ) c).comp (T.cuspA j (wtA w) w.n).subtype)

def IsConjChar (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (e : D.what₂.Tau → ℤ)
    (χ : GLev T j →* D.what₂.LLˣ) (σ : D.what₂.LL →+* ℂ) : Prop :=
  (∀ τ τ', SitsAt D σ τ τ' → ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D (T.V j (res T σ)) τ'),
    T.mu j (res T σ) (atTau θ (T.V j (res T σ)) τ' h) = h.det ^ (-e τ)) ∧
  ∀ γ κ, Induces T j (T.V j (res T σ)) γ κ →
    T.mu j (res T σ) κ = (σ ((χ γ : D.what₂.LLˣ) : D.what₂.LL))⁻¹

def HidaSetting (w : WeightFamilies.Wt D j) (e : D.what₂.Tau → ℤ) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (χ : GLev T j →* D.what₂.LLˣ) (S : Emb D → D.what₂.Tau → SPar) : Prop :=
  LawsJ T ∧ BaseEmbeddingInclusion T.Q.c.F D.what₂.embLL ∧ InR D j ∧ IsKappa j e w ∧ IsInfFam θ ∧
    ∀ σ : Emb D, IsConjChar T j θ e χ σ.1 ∧ IsConjPar D j σ.1 (S σ)

def FrameEquiv (w : WeightFamilies.Wt D j) (χ : GLev T j →* D.what₂.LLˣ) (σ : D.what₂.LL →+* ℂ)
    (c : (T.U j (res T σ)).Comp → ℂ) : Prop :=
  ∀ γ κ, Induces T j (T.V j (res T σ)) γ κ → ∀ (f : Cu T j w) (h : GA D (T.V j (res T σ))),
    rdK T j w (res T σ) c (geoAct T j γ f.1) h =
      σ ((χ γ : D.what₂.LLˣ) : D.what₂.LL) * rdK T j w (res T σ) c f.1 (h * κ)

def RowGeo : Prop :=
  ∀ (D : D7) (T : CoreJ D) (j : ℕ) [Algebra T.Q.c.F D.what₂.LL] (w : WeightFamilies.Wt D j) (e : D.what₂.Tau → ℤ)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (χ : GLev T j →* D.what₂.LLˣ)
    (S : Emb D → D.what₂.Tau → SPar) (M : ∀ σ : Emb D, DSModel (T.V j (res T σ.1)) (S σ)),
    HidaSetting T j w e θ χ S →
    ∃ ρC : GLev T j →* (Cu T j w →ₗ[T.Q.c.F] Cu T j w),
      (∀ γ f, (ρC γ f).1 = geoAct T j γ f.1) ∧
      (∀ γ (f : Cu T j w), (∀ la y, T.nrmM j la y f.1 ≤ 1) → ∀ la y, T.nrmM j la y (ρC γ f).1 ≤ 1) ∧
      ∀ σ : Emb D, IsCover (T.V j (res T σ.1)) (Induces T j (T.V j (res T σ.1))) ∧
        ∃ (c : (T.U j (res T σ.1)).Comp → ℂ) (v : (M σ).Vec)
          (J : D.what₂.LL ⊗[T.Q.c.F] Cu T j w →ₛₗ[σ.1] MMap (M σ)),
          CUnit c ∧ IsLowVec (M σ) v ∧ (∀ x, J x v = rdL T j w σ.1 c x) ∧
          UnifCl θ (M σ) (Induces T j (T.V j (res T σ.1))) (rhoOf D.what₂.LL ρC) χ σ.1 J

def Tied (w : WeightFamilies.Wt D j) (χ : GLev T j →* D.what₂.LLˣ) {S : Emb D → D.what₂.Tau → SPar}
    (M : ∀ σ : Emb D, DSModel (T.V j (res T σ.1)) (S σ)) {G0 : Type} [Group G0]
    {W : (D.what₂.LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    (ev : ∀ σ : Emb D, W σ.1 →ₗ[ℂ] MMap (M σ))
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {WL : Type} [AddCommGroup WL] [Module D.what₂.LL WL] [Module Ks WL] [IsScalarTower Ks D.what₂.LL WL]
    (A : Formalism.IndefR.Arith.FormsL D.what₂.LL Ks WL W G0) (eW : WL ≃ₗ[D.what₂.LL] D.what₂.LL ⊗[T.Q.c.F] Cu T j w)
    (ℓ : G0 ≃* GLev T j) : Prop :=
  (∀ g (f f' : Cu T j w), f'.1 = geoAct T j (ℓ g) f.1 → eW (A.ρ g (eW.symm (1 ⊗ₜ f))) = 1 ⊗ₜ f') ∧
    (∀ g, A.chi g = χ (ℓ g)) ∧
    ∀ σ : Emb D,
      (∃ v : (M σ).Vec, IsLowVec (M σ) v ∧
        ∀ x, ev σ (A.j σ.1 x) v = rdL T j w σ.1 (T.cE j (res T σ.1)) (eW x)) ∧
      ((∃ c, CUnit c ∧ FrameEquiv T j w χ σ.1 c) → FrameEquiv T j w χ σ.1 (T.cE j (res T σ.1)))

def RowForms : Prop :=
  ∀ (D : D7) (T : CoreJ D) (j : ℕ) [Algebra T.Q.c.F D.what₂.LL] (w : WeightFamilies.Wt D j) (e : D.what₂.Tau → ℤ)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (χ : GLev T j →* D.what₂.LLˣ)
    (S : Emb D → D.what₂.Tau → SPar) (M : ∀ σ : Emb D, DSModel (T.V j (res T σ.1)) (S σ))
    (G0 : Type) [Group G0] (W : (D.what₂.LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)]
    [∀ σ, InnerProductSpace ℂ (W σ)] (ev : ∀ σ : Emb D, W σ.1 →ₗ[ℂ] MMap (M σ))
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (WL : Type) [AddCommGroup WL] [Module D.what₂.LL WL] [Module Ks WL] [IsScalarTower Ks D.what₂.LL WL]
    (A : Formalism.IndefR.Arith.FormsL D.what₂.LL Ks WL W G0) (eW : WL ≃ₗ[D.what₂.LL] D.what₂.LL ⊗[T.Q.c.F] Cu T j w)
    (ℓ : G0 ≃* GLev T j),
    HidaSetting T j w e θ χ S → (∀ σ, Function.Injective (ev σ) ∧ LinearMap.range (ev σ) = MultK θ (M σ)) →
    Tied T j w χ M ev A eW ℓ →
    UnifEvery j θ (fun σ => T.V j (res T σ.1)) S M (fun σ g => Induces T j (T.V j (res T σ.1)) (ℓ g)) ev A

def Row : Prop := RowGeo ∧ RowForms

example (D : D7) : Side D D.what₂.embLL := fun _ => rfl

example (w : WeightFamilies.Wt D j) (s : T.Q.c.F →+* ℂ) (f : T.R j) :
    rdK T j w s (T.cE j s) f = T.phiJ j s (wtA w) f := rfl

example (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)) (h : IsLevelK V N Kf) : (Kf : Set (GA D V)) = levSet V N :=
  Set.ext h

end GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets
