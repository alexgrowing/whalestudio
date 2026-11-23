import Formalism.SharpRestriction.LevelLetterCocycles.MixedPositionHypothesis

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

open Classical in

def valAt (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) (x : W.DD T) : T.V ⊗[Qp] BdR :=
  if h : ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ W.N T then
    ((PowerSeries.coeff 1 (W.lev c ζ W.Q)) ^ Nat.find h)⁻¹ •
      W.levN T c ζ ⟨W.Q ^ Nat.find h • W.φD T x, Nat.find_spec h⟩ (Nat.find h : ℤ)
  else 0

def FilL (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (c : ZMod n)
    (τ : K →ₐ[Qp] LL) (a : ℤ) : Set (W.DD T) :=
  {x | ∀ ζ, Pt c ζ τ → valAt W T c ζ x ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a}

def mkL (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n) (x : W.DD T) (hx : x ∈ NcS W T (c - 1)) :
    LcQ W T π' c :=
  Submodule.Quotient.mk ⟨x, hx⟩

abbrev LA (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n) : Type := W.EE ⊗[O] LcQ W T π' c

def toLA (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    ↥W.AΔ ⊗[O] ↥S →ₗ[O] LA W T π' c :=
  TensorProduct.map ((IsScalarTower.toAlgHom O (LetA O n) W.EE).toLinearMap ∘ₗ
    LinearMap.mulLeft O (letE c : LetA O n) ∘ₗ W.AΔ.val.toLinearMap) S.subtype

def smulLA (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n) (a : LetA O n) :
    LA W T π' c →ₗ[O] LA W T π' c :=
  TensorProduct.map (LinearMap.mulLeft O (algebraMap (LetA O n) W.EE a)) LinearMap.id

def γLA (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n) : LA W T π' c →ₗ[O] LA W T π' c :=
  TensorProduct.map (W.γE W.gamK).toLinearMap LinearMap.id

def LamLA (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)
    (S : Submodule O (LcQ W T π' c)) : Submodule O (LA W T π' c) :=
  (LinearMap.range (toLA W T π' c S)).comap (smulLA W T π' c (Eπ ^ h'))

def IsRepL (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) (x : LA W T π' c) {m : ℕ}
    (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T) : Prop :=
  ∃ hy : ∀ j, y j ∈ NcS W T (c - 1), smulLA W T π' c (Eπ ^ h') x =
    ∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ mkL W T π' c (y j) (hy j)

def serC {V' : Type} [AddCommGroup V'] [Module LL V'] (f : PowerSeries LL) (d : V') : ℤ → V' :=
  fun i => if 0 ≤ i then PowerSeries.coeff i.toNat f • d else 0

def serMul {V' : Type} [AddCommGroup V'] [Module LL V'] (g : PowerSeries LL) (f : ℤ → V') : ℤ → V' :=
  fun i => ∑ᶠ j : ℕ, PowerSeries.coeff j g • f (i - j)

def expS (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) {m : ℕ} (a : Fin m → LetA O n)
    (y : Fin m → W.DD T) : ℤ → T.V ⊗[Qp] BdR :=
  fun i => ∑ j, serC (W.lev c ζ (a j)) (valAt W T c ζ (y j)) i

def NLset (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) : Set (LA W T π' c) :=
  {x | ∃ (m : ℕ) (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T), IsRepL W T π' Eπ h' c x a y ∧
    ∀ τ ζ, Pt c ζ τ → ∀ i : ℤ, expS W T c ζ (fun j => (a j : LetA O n)) y i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (h' - i)}

def NL (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) : Submodule O (LA W T π' c) :=
  Submodule.span O (NLset W T Pt π' Eπ h' c)

def piNL (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) (j : ℕ) : Submodule O (LA W T π' c) :=
  (NL W T Pt π' Eπ h' c).map (smulLA W T π' c (π' ^ j))

def InvL (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) : Submodule O (LA W T π' c) :=
  LamLA W T π' Eπ h' c S ⊓ (piNL W T Pt π' Eπ h' c 1).comap (γLA W T π' c - LinearMap.id)

abbrev IIrest (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) : Type :=
  ↥(InvL W T Pt π' Eπ h' c S) ⧸ (piNL W T Pt π' Eπ h' c 1).comap (InvL W T Pt π' Eπ h' c S).subtype

def JLA (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) : Submodule O (LA W T π' c) :=
  (LinearMap.range (toLA W T π' c ⊤)).map (smulLA W T π' c (π' ^ M * Eπ ^ (3 * h')))

def JP (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) : Submodule O (W.DD T) :=
  (PcS W T c).map ((Formalism.MainNotions.DeltaInvariantLattices.smulA W T (π' ^ M * Eπ ^ (3 * h'))).restrictScalars O)

abbrev QLamLA (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) : Type :=
  ↥(LamLA W T π' Eπ h' c ⊤) ⧸ (JLA W T π' Eπ h' M c).comap (LamLA W T π' Eπ h' c ⊤).subtype

abbrev QLamP (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) : Type :=
  ↥(LamPS W T Eπ h' c) ⧸ (JP W T π' Eπ h' M c).comap (LamPS W T Eπ h' c).subtype

def mkLA (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) (x : LA W T π' c)
    (hx : x ∈ LamLA W T π' Eπ h' c ⊤) : QLamLA W T π' Eπ h' M c :=
  Submodule.Quotient.mk ⟨x, hx⟩

def mkP (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) (y : W.DD T)
    (hy : y ∈ LamPS W T Eπ h' c) : QLamP W T π' Eπ h' M c :=
  Submodule.Quotient.mk ⟨y, hy⟩

def LAover {T₁ T₂ : LocLat G Qp LL O} (f : LatHom T₁.L T₂.L) (π' : LetA O n) (c : ZMod n)
    (x₁ : LA W T₁ π' c) (x₂ : LA W T₂ π' c) : Prop :=
  ∃ (m : ℕ) (e : Fin m → W.EE) (y : Fin m → W.DD T₁) (h₁ : ∀ j, y j ∈ NcS W T₁ (c - 1))
    (h₂ : ∀ j, W.map f (y j) ∈ NcS W T₂ (c - 1)),
    x₁ = ∑ j, e j ⊗ₜ mkL W T₁ π' c (y j) (h₁ j) ∧ x₂ = ∑ j, e j ⊗ₜ mkL W T₂ π' c (W.map f (y j)) (h₂ j)

abbrev FrA (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) : Type 1 :=
  ∀ T : LocLat G Qp LL O, ↥(LamLA W T π' Eπ h' c ⊤) →ₗ[O] QLamP W T π' Eπ h' M c

abbrev FrB (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) : Type 1 :=
  ∀ T : LocLat G Qp LL O, ↥(LamPS W T Eπ h' c) →ₗ[O] QLamLA W T π' Eπ h' M c

def IsFrame (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n) (h' M σ : ℕ) (c : ZMod n)
    (α : FrA W π' Eπ h' M c) (β : FrB W π' Eπ h' M c) : Prop :=
  (∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → (∀ τ, JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
    (∀ x (hx : x ∈ LamLA W T π' Eπ h' c ⊤), x ∈ JLA W T π' Eπ h' M c → α T ⟨x, hx⟩ = 0) ∧
    (∀ y (hy : y ∈ LamPS W T Eπ h' c), y ∈ JP W T π' Eπ h' M c → β T ⟨y, hy⟩ = 0) ∧
    (∀ x hx y hy, α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y hy →
      β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c (((PD.p : ℕ) : O) ^ (2 * σ) • x)
        ((LamLA W T π' Eπ h' c ⊤).smul_mem _ hx)) ∧
    (∀ y hy x hx, β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx →
      α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c (((PD.p : ℕ) : O) ^ (2 * σ) • y)
        ((LamPS W T Eπ h' c).smul_mem _ hy)) ∧
    (∀ a ∈ W.AΔ, ∀ x hx y hy, α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y hy →
      ∀ hax hay, α T ⟨smulLA W T π' c a x, hax⟩ = mkP W T π' Eπ h' M c (a • y) hay) ∧
    (∀ a ∈ W.AΔ, ∀ y hy x hx, β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx →
      ∀ hay hax, β T ⟨a • y, hay⟩ = mkLA W T π' Eπ h' M c (smulLA W T π' c a x) hax) ∧
    (∀ x hx y hy, α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y hy →
      ∀ hgx hgy, α T ⟨γLA W T π' c x, hgx⟩ = mkP W T π' Eπ h' M c (W.γD T W.gamK y) hgy) ∧
    (∀ y hy x hx, β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx →
      ∀ hgy hgx, β T ⟨W.γD T W.gamK y, hgy⟩ = mkLA W T π' Eπ h' M c (γLA W T π' c x) hgx) ∧
    ∀ τ ζ, Pt c ζ τ → ∀ x hx y hy, α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y hy →
      ∀ (m : ℕ) (a : Fin m → ↥W.AΔ) (z : Fin m → W.DD T), IsRepL W T π' Eπ h' c x a z →
      ∀ (k : ℕ) (hk : W.Q ^ k • (Eπ ^ h' • y) ∈ W.N T) (i : ℤ), i < k + 4 * h' →
        W.levN T c ζ ⟨_, hk⟩ i =
          (PD.p ^ σ) • serMul (W.lev c ζ (W.Q ^ k)) (expS W T c ζ (fun j => (a j : LetA O n)) z) i) ∧
  ∀ (T₁ T₂ : LocLat G Qp LL O) (f : LatHom T₁.L T₂.L), IsCrys PD T₁.ρ → IsCrys PD T₂.ρ →
    (∀ τ, JumpsInV PD T₁.ρ τ (Set.Icc (-(h' : ℤ)) h')) → (∀ τ, JumpsInV PD T₂.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
    (∀ x₁ hx₁ x₂ hx₂ y₁ hy₁ hy₂, LAover W f π' c x₁ x₂ → α T₁ ⟨x₁, hx₁⟩ = mkP W T₁ π' Eπ h' M c y₁ hy₁ →
      α T₂ ⟨x₂, hx₂⟩ = mkP W T₂ π' Eπ h' M c (W.map f y₁) hy₂) ∧
    ∀ y₁ hy₁ hy₂ x₁ hx₁ x₂ hx₂, LAover W f π' c x₁ x₂ → β T₁ ⟨y₁, hy₁⟩ = mkLA W T₁ π' Eπ h' M c x₁ hx₁ →
      β T₂ ⟨W.map f y₁, hy₂⟩ = mkLA W T₂ π' Eπ h' M c x₂ hx₂

def HypL {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (S η m h' : ℕ) (up : (K →ₐ[Qp] LL) → Bool)
    (b : (K →ₐ[Qp] LL) → ℕ) : Prop :=
  IsCrys PD T₁.ρ ∧ IsCrys PD T₂.ρ ∧ F.Onto ∧
    (∀ τ, JumpsInV PD T₁.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) ∧
    (∀ τ, JumpsInV PD T₂.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) ∧
    (∀ τ, η < b τ) ∧ (∀ τ, b τ + S ≤ h') ∧ 1 ≤ h' ∧
    (∀ τ, ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV PD T₂.ρ τ a ≤ m) ∧
    (finrank K₀ K = 2 ∨ ∀ τ τ' : K →ₐ[Qp] LL, τ.comp (IsScalarTower.toAlgHom Qp K₀ K) =
      τ'.comp (IsScalarTower.toAlgHom Qp K₀ K) → up τ = up τ')

def IsCoord (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n) (h' S : ℕ)
    (up : (K →ₐ[Qp] LL) → Bool) (b : (K →ₐ[Qp] LL) → ℕ) (c : ZMod n) (f : W.EE) : Prop :=
  ∃ a ∈ W.AΔ, (letE c : LetA O n) * a = a ∧ algebraMap (LetA O n) W.EE (Eπ ^ h') * f = algebraMap (LetA O n) W.EE a ∧
    (∀ τ ζ, Pt c ζ τ → up τ = true → ∀ i : ℕ, i + b τ < h' → PowerSeries.coeff i (W.lev c ζ a) = 0) ∧
    (∀ τ ζ, Pt c ζ τ → up τ = false → ∃ x : LL, ∀ i : ℕ, i < h' + b τ + S →
      PowerSeries.coeff i (W.lev c ζ a) = x * PowerSeries.coeff i (W.lev c ζ (Eπ ^ h'))) ∧
    ∃ g ∈ W.AΔ, algebraMap (LetA O n) W.EE (Eπ ^ h') * (W.γE W.gamK f - f) =
      algebraMap (LetA O n) W.EE (π' * g)

open Classical in

def OmF (c : ZMod n) (S h' : ℕ) (up : (K →ₐ[Qp] LL) → Bool) (b : (K →ₐ[Qp] LL) → ℕ) : Finset ℤ :=
  (Finset.Icc (-(h' : ℤ)) h').filter fun i => ∃ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c ∧
    ((up τ = true ∧ -((b τ : ℤ) + S) ≤ i ∧ i < -(b τ : ℤ)) ∨ (up τ = false ∧ (b τ : ℤ) ≤ i ∧ i < b τ + S))

def piOm1 (c : ZMod n) (S h' : ℕ) (up : (K →ₐ[Qp] LL) → Bool) (b : (K →ₐ[Qp] LL) → ℕ) : O :=
  ∏ i ∈ OmF W c S h' up b, (1 - (((Formalism.MainNotions.DeltaInvariantLattices.uU W) ^ i : Oˣ) : O))

def InvLift (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' M σ : ℕ) (c : ZMod n) : Prop :=
  (∀ w ∈ InvS W T π' Eπ h' 1 c, ∃ wb ∈ InvS W T π' Eπ h' M c,
    ((PD.p : ℕ) : O) ^ σ • w - wb ∈ PiNS W T π' 1) ∧
  ∀ wb ∈ InvS W T π' Eπ h' M c, wb ∈ PiNS W T π' 1 → wb ∈ PiNS W T π' M

def ClassMap (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) : Prop :=
  (∀ w ∈ InvS W T π' Eπ h' M c, ∃ z ∈ PiNS W T π' M, (w, z) ∈ W.wachCocyclesDelta T) ∧
  (∀ pr pr' : ↥(W.wachCocyclesDelta T), pr.1.1 ∈ InvS W T π' Eπ h' M c → pr.1.2 ∈ PiNS W T π' M →
    pr'.1.1 ∈ InvS W T π' Eπ h' M c → pr'.1.2 ∈ PiNS W T π' M → pr.1.1 - pr'.1.1 ∈ PiNS W T π' M →
    W.clK T pr = W.clK T pr') ∧
  ∀ pr : ↥(W.wachCocyclesDelta T), pr.1.1 ∈ InvS W T π' Eπ h' M c → pr.1.2 ∈ PiNS W T π' M →
    ∃ κ ∈ latticeFiniteCocycles PD T.L, ∃ hκ : κ ∈ latticeCocycles T.L,
      Submodule.mkQ ((latticeCoboundaries T.L).comap (latticeCocycles T.L).subtype) (⟨κ, hκ⟩ : ↥(latticeCocycles T.L)) = W.clK T pr

def FrameA (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n) (h' M σ : ℕ) (c : ZMod n) : Prop :=
  ∃ (α : FrA W π' Eπ h' M c) (β : FrB W π' Eπ h' M c), IsFrame W Pt π' Eπ h' M σ c α β

def ModelF (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' M : ℕ) (c : ZMod n) (α : FrA W π' Eπ h' M c) (β : FrB W π' Eπ h' M c) : Prop :=
  (∀ x hx, x ∈ NL W T Pt π' Eπ h' c →
    ∃ y hy, y ∈ NcS W T c ∧ α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y hy) ∧
  (∀ y hy, y ∈ NcS W T c → ∃ x hx, x ∈ NL W T Pt π' Eπ h' c ∧ β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx) ∧
  (∀ j : ℕ, 1 ≤ j → j ≤ M →
    (∀ x hx y hy, α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y hy → x ∈ piNL W T Pt π' Eπ h' c j →
      y ∈ PiNS W T π' j) ∧
    ∀ y hy x hx, β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx → y ∈ PiNS W T π' j →
      x ∈ piNL W T Pt π' Eπ h' c j) ∧
  (∀ x hx y hy, α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y hy → x ∈ InvL W T Pt π' Eπ h' c ⊤ →
    y ∈ InvS W T π' Eπ h' 1 c) ∧
  ∀ y hy x hx, β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx → y ∈ InvS W T π' Eπ h' 1 c →
    x ∈ InvL W T Pt π' Eπ h' c ⊤

def KapPi (c : ZMod n) (S h' κ : ℕ) (up : (K →ₐ[Qp] LL) → Bool) (b : (K →ₐ[Qp] LL) → ℕ) : Prop :=
  ∃ u : O, u * piOm1 W c S h' up b = ((PD.p : ℕ) : O) ^ κ

def FirstPropositionFrame {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) (S η m : ℕ) (up : (K →ₐ[Qp] LL) → Bool)
    (b : (K →ₐ[Qp] LL) → ℕ) (β : FrB W π' Eπ h' M c) : Prop :=
  HypL (PD := PD) F S η m h' up b → ∃ (Lr : Submodule O (LcQ W T₂ π' c)) (k : ℕ) (ell : Fin k → W.DD T₂)
    (hell : ∀ j, ell j ∈ NcS W T₂ (c - 1)),
    finrank O Lr ≤ finrank K₀ K * m ∧
    (∀ j τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c → up τ = true → ell j ∈ FilL W T₂ Pt c τ (b τ)) ∧
    Submodule.span O (Set.range fun j => mkL W T₂ π' c (ell j) (hell j)) ⊔ Lr = ⊤ ∧
    ∀ w (hw : w ∈ InvS W T₂ π' Eπ h' 1 c), ∃ (f : Fin k → W.EE) (x : LA W T₂ π' c)
      (hx : x ∈ LamLA W T₂ π' Eπ h' c ⊤) (xr : LA W T₂ π' c),
      (∀ j, IsCoord W Pt π' Eπ h' S up b c (f j)) ∧
      (∀ j, f j ⊗ₜ mkL W T₂ π' c (ell j) (hell j) ∈ InvL W T₂ Pt π' Eπ h' c ⊤) ∧
      xr ∈ InvL W T₂ Pt π' Eπ h' c Lr ∧
      β T₂ ⟨piOm1 W c S h' up b • w, (LamPS W T₂ Eπ h' c).smul_mem _ (Submodule.mem_inf.mp hw).1⟩ =
        mkLA W T₂ π' Eπ h' M c x hx ∧
      x - ∑ j, f j ⊗ₜ mkL W T₂ π' c (ell j) (hell j) - xr ∈ piNL W T₂ Pt π' Eπ h' c 1

def SecondPropositionFree (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n) (h' : ℕ)
    (c : ZMod n) : Prop :=
  ∀ S : Submodule O (LcQ W T π' c), Module.Finite O (IIrest W T Pt π' Eπ h' c S) ∧
    Module.Free O (IIrest W T Pt π' Eπ h' c S) ∧
    finrank O (IIrest W T Pt π' Eπ h' c S) ≤ (finrank K₀ K + 1) * finrank O S

def LiftsBy {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (π' Eπ : LetA O n) (h' y : ℕ) (c : ZMod n)
    (z : W.DD T₂) : Prop :=
  z ∈ InvS W T₂ π' Eπ h' 1 c ∧ ∃ w₁ ∈ InvS W T₁ π' Eπ h' 1 c,
    ((PD.p : ℕ) : O) ^ y • z - W.map F w₁ ∈ PiNS W T₂ π' 1

def ThirdPropositionSlot {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' M S : ℕ) (up : (K →ₐ[Qp] LL) → Bool) (b : (K →ₐ[Qp] LL) → ℕ) (c : ZMod n)
    (y₁ : ℕ) (α : FrA W π' Eπ h' M c) : Prop :=
  ∀ f, IsCoord W Pt π' Eπ h' S up b c f → ∀ x (hx : x ∈ NcS W T₂ (c - 1)),
    (∀ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c → up τ = true → x ∈ FilL W T₂ Pt c τ (b τ)) →
    ∀ (h1 : f ⊗ₜ mkL W T₂ π' c x hx ∈ LamLA W T₂ π' Eπ h' c ⊤) y hy,
      α T₂ ⟨_, h1⟩ = mkP W T₂ π' Eπ h' M c y hy → LiftsBy W F π' Eπ h' y₁ c y

end Local

section Record

def recU (D : D7) (HW : HWOf D.loc) (P : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (_ : Good K 1 LL),
    LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)) → (ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)) → Prop) :
    Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)),
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E → P l K LL hG π' E

def invLiftR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T.ρ → (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      ∀ c, InvLift ((HW l).W K 1 LL hG) T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') (sigA l (sK l K) h') c

def classMapR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T.ρ → (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      ∀ c, ClassMap ((HW l).W K 1 LL hG) T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') c

def frameR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ h' : ℕ, 1 ≤ h' → ∀ c, FrameA ((HW l).W K 1 LL hG) (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') (sigA l (sK l K) h') c

def modelFR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ h' : ℕ, 1 ≤ h' → ∀ c α β, IsFrame ((HW l).W K 1 LL hG) (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') (sigA l (sK l K) h') c α β →
      ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys ((D.loc l).PD K) T.ρ → (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
        ModelF ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') c α β

def kapPiR (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG _ _ =>
    ∀ (h' S : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) c,
      (∀ τ, 0 < b τ) → (∀ τ, b τ + S ≤ h') → KapPi ((HW l).W K 1 LL hG) c S h' (kapA l (eK K) h' S) up b

def u1R (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (S η m h' : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool)
      (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) c α β, IsFrame ((HW l).W K 1 LL hG) (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') (sigA l (sK l K) h') c α β →
      FirstPropositionFrame ((HW l).W K 1 LL hG) F (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') c S η m up b β

def u2R (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T.ρ → (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
      ∀ c, SecondPropositionFree ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c

def DownSlotProposition (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (S η m h' : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool)
      (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) c α β, IsFrame ((HW l).W K 1 LL hG) (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') (sigA l (sK l K) h') c α β →
      HypN (D.loc l) K LL T₁ T₂ F S η m h' up b → (∀ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c → up τ = false) →
      ThirdPropositionSlot ((HW l).W K 1 LL hG) F (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') S up b c (rhoA l (eK K) h') α

def UpSlotProposition (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (S η m h' : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool)
      (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) c α β, IsFrame ((HW l).W K 1 LL hG) (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') (sigA l (sK l K) h') c α β →
      HypN (D.loc l) K LL T₁ T₂ F S η m h' up b → (∀ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c → up τ = true) →
      ThirdPropositionSlot ((HW l).W K 1 LL hG) F (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') S up b c (rhoA l (eK K) h') α

def MixedSlotProposition (D : D7) (HW : HWOf D.loc) : Prop :=
  recU D HW fun l _ K LL hG π' E =>
    ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (S η m h' : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool)
      (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) c α β, IsFrame ((HW l).W K 1 LL hG) (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') (sigA l (sK l K) h') c α β →
      HypN (D.loc l) K LL T₁ T₂ F S η m h' up b → eK K = 2 →
      ThirdPropositionSlot ((HW l).W K 1 LL hG) F (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') S up b c (rhoA l (eK K) h' + max (2 * sigA l (sK l K) h') (ycA l h' η)) α

end Record

end Formalism.MainNotions.N.Ln34

end
