import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.CompDef

noncomputable section

namespace PositivityTheory.ThK

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Local

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [LocallyCompactSpace k] [Invertible (2 : k)]
  {K : Type} [CommRing K] [Algebra k K] (c : K →ₐ[k] K) {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype ν] [DecidableEq ν] [Fintype κ]

def IsSkewM (J : Matrix β β K) : Prop := (∀ i j, c (J j i) = -J i j) ∧ IsUnit J.det

def IsEv (ψ : AddChar k ℂ) {JA : Matrix α α K} {JB : Matrix β β K} (d : Darboux (symp (R := k) c (-1) JA JB) κ) (Cy : Matrix β ν K)
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  (∃ φ ∈ SB (κ → k), l φ ≠ 0) ∧ ∀ z : Matrix α ν K, ∀ φ ∈ SB (κ → k), l (d.rho ψ (z * Cyᵀ) φ) = l φ

structure IsSplitPair (ψ : AddChar k ℂ) (JA : Matrix α α K) (JB : Matrix β β K) (d : Darboux (symp (R := k) c (-1) JA JB) κ)
    (χ : Kˣ →* Circle) (Cy : Matrix β ν K) (omA : UG c JA →* Module.End ℂ ((κ → k) → ℂ))
    (omB : UG c JB →* Module.End ℂ ((κ → k) → ℂ)) (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) : Prop where
  herm : IsHerm c JA
  skew : IsSkewM c JB
  lagr : IsLagr c JB Cy
  res : ResEtaPow (R := k) ⊥ χ (Fintype.card α)
  splB : IsSplitting (sbClass k) ψ d (actB c) omB
  rule : SiegelRule c (sbClass k) ψ (-1) JA JB d χ Cy omB
  splA : IsSplitting (sbClass k) ψ d (fun (g : UG c JA) x => ((g : GL α K) : Matrix α α K) * x) omA
  ev : IsEv c ψ d Cy l
  fix : ∀ g, ∀ φ ∈ SB (κ → k), l (omA g φ) = l φ

def secOf {G S : Type} [Group G] [AddCommGroup S] [Module ℂ S] (om : G →* Module.End ℂ S) (l : S →ₗ[ℂ] ℂ) : S →ₗ[ℂ] (G → ℂ) :=
  LinearMap.pi fun h => l ∘ₗ om h

def IsAbove {α' : Type} [Fintype α'] [DecidableEq α'] (JA : Matrix α α K) (JA' : Matrix α' α' K) : Prop :=
  ∃ (r : ℕ) (P : Matrix α (α' ⊕ (Fin r ⊕ Fin r)) K) (Q : Matrix (α' ⊕ (Fin r ⊕ Fin r)) α K), P * Q = 1 ∧ Q * P = 1 ∧
    Pᵀ * JA * P.map c = Matrix.fromBlocks JA' 0 0 (Matrix.fromBlocks 0 1 1 0)

end Local

def AllLocal (Q : ∀ (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] [LocallyCompactSpace k] [Invertible (2 : k)]
    (K : Type) [CommRing K] [Algebra k K] [TopologicalSpace K], (K →ₐ[k] K) → AddChar k ℂ → Prop) : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
    (K : Type) [CommRing K] [Algebra k K] [TopologicalSpace K] [IsModuleTopology k K] (c : K →ₐ[k] K) (ψ : AddChar k ℂ),
    IsField K → (∃ ξ, IsQuad c ξ) → Continuous ψ → ψ ≠ 1 → Q k K c ψ

def CoinvHyp : Prop := AllLocal fun k _ _ _ _ _ K _ _ _ c ψ =>
  ∀ (m n : ℕ) (κ : Type) [Fintype κ] (JA : Matrix (Fin m) (Fin m) K) (N : ℕ) (JB : Matrix (Fin N) (Fin N) K)
    (d : Darboux (symp (R := k) c (-1) JA JB) κ) (χ : Kˣ →* Circle) (Cy : Matrix (Fin N) (Fin n) K) omA omB l, Continuous χ →
    IsSplitPair c ψ JA JB d χ Cy omA omB l → ∀ φ ∈ SB (κ → k),
      φ ∈ Submodule.span ℂ {z | ∃ g, ∃ φ₀ ∈ SB (κ → k), z = omA g φ₀ - φ₀} ↔ secOf omB l φ = 0

def KudlaSweetTheorem : Prop := AllLocal fun k _ _ _ _ _ K _ _ _ c ψ =>
  ∀ (m m' n : ℕ) (κ κ' : Type) [Fintype κ] [Fintype κ'] (JA : Matrix (Fin m) (Fin m) K) (JA' : Matrix (Fin m') (Fin m') K) (N : ℕ)
    (JB : Matrix (Fin N) (Fin N) K) (d : Darboux (symp (R := k) c (-1) JA JB) κ) (d' : Darboux (symp (R := k) c (-1) JA' JB) κ')
    (χ : Kˣ →* Circle) (Cy : Matrix (Fin N) (Fin n) K) omA omB l omA' omB' l', Continuous χ → 0 < m' → m' < n → m + m' = 2 * n →
    IsAbove c JA JA' → IsSplitPair c ψ JA JB d χ Cy omA omB l → IsSplitPair c ψ JA' JB d' χ Cy omA' omB' l' →
    (∀ S : Submodule ℂ (UG c JB → ℂ), S ≤ (SB (κ' → k)).map (secOf omB' l') → (∀ f ∈ S, ∀ h, (fun g => f (g * h)) ∈ S) →
      S = ⊥ ∨ S = (SB (κ' → k)).map (secOf omB' l')) ∧
    ∃ T : (UG c JB → ℂ) →ₗ[ℂ] (UG c JB → ℂ), ((SB (κ → k)).map (secOf omB l)).map T = (SB (κ' → k)).map (secOf omB' l') ∧
      ∀ f ∈ (SB (κ → k)).map (secOf omB l), ∀ h, T (fun g => f (g * h)) = fun g => T f (g * h)

def SiegelTransport : Prop := AllLocal fun k _ _ _ _ _ K _ _ _ c ψ =>
  ∀ (m n N : ℕ) (κ : Type) [Fintype κ] (JA : Matrix (Fin m) (Fin m) K) (JB : Matrix (Fin N) (Fin N) K)
    (d : Darboux (symp (R := k) c (-1) JA JB) κ) (χ : Kˣ →* Circle) (Cy : Matrix (Fin N) (Fin n) K) om, IsHerm c JA → IsSkewM c JB →
    IsLagr c JB Cy → IsWeilB c (sbClass k) ψ (-1) JA JB d χ om → SiegelRule c (sbClass k) ψ (-1) JA JB d χ Cy om

def LinearAct : Prop := AllLocal fun k _ _ _ _ _ K _ _ _ c ψ =>
  ∀ (m n N : ℕ) (κ : Type) [Fintype κ] (JA : Matrix (Fin m) (Fin m) K) (JB : Matrix (Fin N) (Fin N) K)
    (d : Darboux (symp (R := k) c (-1) JA JB) κ) (χ : Kˣ →* Circle) (Cy : Matrix (Fin N) (Fin n) K) om l, IsHerm c JA → IsSkewM c JB →
    IsLagr c JB Cy → IsWeilPair c (sbClass k) ψ (-1) JA JB d χ 1 om → IsEv c ψ d Cy l →
    ∀ g, ∀ φ ∈ SB (κ → k), l (om (g, 1) φ) = l φ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

variable (E) in

abbrev Ev (v : Pl F) : Type := Fv F v ⊗[F] E

def cV (σ : E →ₐ[F] E) (v : Pl F) : Ev E v →ₐ[Fv F v] Ev E v := Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ

def locM {a b : Type} (J : Matrix a b E) (v : Pl F) : Matrix a b (Ev E v) := J.map (inclR (F := F) (Fv F v))

def IsLocChar (χ : Chr F E) (v : Pl F) (χv : (Ev E v)ˣ →* Circle) : Prop :=
  ∀ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) → χv (Units.map (compFin F E v).toMonoidHom z) = χ z

structure IsLocPair {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W)
    (v : Pl F) [LocallyCompactSpace (Fv F v)] [Invertible (2 : Fv F v)] (ψv : AddChar (Fv F v) ℂ)
    (dv : Darboux (symp (R := Fv F v) (cV σ v) (-1) (locM X.J v) (locM W.J v)) (Fin n × Fin d)) (χXv χWv : (Ev E v)ˣ →* Circle)
    (omv : UG (cV σ v) (locM X.J v) × UG (cV σ v) (locM W.J v) →* Module.End ℂ (Fn F n d v)) : Prop where
  psi : ∀ x, ψv x = psiLoc ψ v x
  chX : IsLocChar χX v χXv
  chW : IsLocChar χW v χWv
  weil : IsWeilPair (cV σ v) (sbClass (Fv F v)) ψv (-1) (locM X.J v) (locM W.J v) dv χXv χWv omv
  Heisenberg₂ : ∀ u, At (evFin F v) u → ∀ φ ∈ SB _, Acts (evFin F v) (M.co.rho ψ u) φ (dv.rho ψv (u.map (compFin F E v)) φ)
  surjX : ∀ gv : UG (cV σ v) (locM X.J v), ∃ g ∈ UAt σ X (evFin F v), (mat g).map (compFin F E v) = gv.1.1
  surjW : ∀ hv : UG (cV σ v) (locM W.J v), ∃ h ∈ UAt σ W (evFin F v), (mat h).map (compFin F E v) = hv.1.1
  loc : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∃ gv hv, (mat g).map (compFin F E v) = gv.1.1 ∧
    (mat h).map (compFin F E v) = hv.1.1 ∧ ∀ φ ∈ SB _, ∀ φ₁, Acts (evFin F v) (om (g, h)) φ φ₁ ↔ φ₁ = omv (gv, hv) φ

def LocPairEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (B : Base F E)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) (χX χW : Chr F E), PairOK B X W M om →
    M.IsWeil B.ψ χX χW om → ∀ (v : Pl F) [LocallyCompactSpace (Fv F v)] [Invertible (2 : Fv F v)],
      ∃ ψv dv χXv χWv omv, IsLocPair M B.ψ χX χW om v ψv dv χXv χWv omv

def HypothesesAtTriple : Prop :=
  CoinvHyp → KudlaSweetTheorem → LocPairEx → SiegelTransport → LinearAct → Iwasawa → EvVac →
    CoinvEmbeds ∧ CompAtTriple

end PositivityTheory.ThK
