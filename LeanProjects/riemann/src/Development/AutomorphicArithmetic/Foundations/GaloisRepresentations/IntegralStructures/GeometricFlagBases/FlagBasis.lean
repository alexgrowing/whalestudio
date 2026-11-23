import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.AdicTopOf
import Development.EtaleCohomology.WeilConjectures.StabPf
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SplitsSelfOfIso

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N

namespace UpperTheory.Gal.Int.Geo

def cj {Γ k : Type} [Group Γ] [Field k] {d : ℕ} (P : GL (Fin d) k) (ρ : Γ →* GL (Fin d) k) : Γ →* GL (Fin d) k :=
  (MulAut.conj P⁻¹).toMonoidHom.comp ρ

theorem cj_apply {Γ k : Type} [Group Γ] [Field k] {d : ℕ} (P : GL (Fin d) k) (ρ : Γ →* GL (Fin d) k) (g : Γ) :
    cj P ρ g = P⁻¹ * ρ g * P := by simp [cj]

def low (k : Type) [Field k] {d : ℕ} (c : Fin d → ℕ) (i : ℕ) : Submodule k (Fin d → k) where
  carrier := {v | ∀ j, i ≤ c j → v j = 0}
  zero_mem' _ _ := rfl
  add_mem' ha hb j h := by simp [ha j h, hb j h]
  smul_mem' r v hv j h := by simp [hv j h]

def IsJH {Γ k : Type} [Group Γ] [Field k] {d : ℕ} (ρ : Γ →* GL (Fin d) k) (W : ℕ → Submodule k (Fin d → k)) : Prop :=
  (∀ i, IsInv ρ (W i)) ∧ ∀ i U, IsInv ρ U → W i ≤ U → U ≤ W (i + 1) → U = W i ∨ U = W (i + 1)

def FlagEx : Prop := ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ : Γ →* GL (Fin d) k),
  ∃ W : ℕ → Submodule k (Fin d → k), Monotone W ∧ W 0 = ⊥ ∧ W d = ⊤ ∧ IsJH ρ W

def FlagBasis : Prop := ∀ (k : Type) [Field k] (d m : ℕ) (W : ℕ → Submodule k (Fin d → k)), Monotone W → W 0 = ⊥ → W m = ⊤ →
  ∃ (P : GL (Fin d) k) (c : Fin d → ℕ), ∀ i v, v ∈ low k c i ↔ (P : Matrix (Fin d) (Fin d) k).mulVec v ∈ W i

def FlagMove : Prop := ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ : Γ →* GL (Fin d) k) (W : ℕ → Submodule k (Fin d → k))
  (P : GL (Fin d) k) (W' : ℕ → Submodule k (Fin d → k)), (∀ i v, v ∈ W' i ↔ (P : Matrix (Fin d) (Fin d) k).mulVec v ∈ W i) →
  IsJH ρ W → IsJH (cj P ρ) W'

def GrHom : Prop := ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ₀ : Γ →* GL (Fin d) k) (c : Fin d → ℕ),
  (∀ i, IsInv ρ₀ (low k c i)) → (∀ g, (ρ₀ g : Matrix (Fin d) (Fin d) k).BlockTriangular c) ∧
    ∃ ρ : Γ →* GL (Fin d) k, ∀ g i j,
      (ρ g : Matrix (Fin d) (Fin d) k) i j = if c i = c j then (ρ₀ g : Matrix (Fin d) (Fin d) k) i j else 0

def SSOfSum : Prop := ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ : Γ →* GL (Fin d) k) (B : ℕ → Submodule k (Fin d → k)),
  (∀ i, IsInv ρ (B i)) → (∀ i U, IsInv ρ U → U ≤ B i → U = ⊥ ∨ U = B i) → ⨆ i, B i = ⊤ → IsSSRep ρ

def GrSS : Prop := ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ₀ ρ : Γ →* GL (Fin d) k) (c : Fin d → ℕ), IsJH ρ₀ (low k c) →
  (∀ g i j, (ρ g : Matrix (Fin d) (Fin d) k) i j = if c i = c j then (ρ₀ g : Matrix (Fin d) (Fin d) k) i j else 0) → IsSSRep ρ

def GrEx : Prop := ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ₀ : Γ →* GL (Fin d) k),
  ∃ (P : GL (Fin d) k) (ρ : Γ →* GL (Fin d) k), IsGr (cj P ρ₀) ρ ∧ IsSSRep ρ

theorem grEx_of (h1 : FlagEx) (h2 : FlagBasis) (h3 : FlagMove) (h4 : GrHom) (h5 : GrSS) : GrEx := by
  intro Γ k _ _ d ρ₀
  obtain ⟨W, hm, h0, ht, hJ⟩ := h1 Γ k d ρ₀
  obtain ⟨P, c, hP⟩ := h2 k d d W hm h0 ht
  have hJ' := h3 Γ k d ρ₀ W P (low k c) hP hJ
  obtain ⟨htri, ρ, hρ⟩ := h4 Γ k d _ c hJ'.1
  exact ⟨P, ρ, ⟨c, fun g => ⟨htri g, hρ g⟩⟩, h5 Γ k d _ ρ c hJ' hρ⟩

def ContGL : Prop := ∀ (Γ k : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [TopologicalSpace k]
  [IsTopologicalRing k] (d : ℕ) (ρ : Γ →* GL (Fin d) k),
  Continuous ρ ↔ ∀ i j, Continuous fun g => (ρ g : Matrix (Fin d) (Fin d) k) i j

def GrKill : Prop := ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ₀ ρ : Γ →* GL (Fin d) k), IsGr ρ₀ ρ → ∀ g,
  (ρ₀ g = 1 → ρ g = 1) ∧ (∀ Q : k[X], aeval (ρ₀ g : Matrix (Fin d) (Fin d) k) Q = 0 → aeval (ρ g : Matrix (Fin d) (Fin d) k) Q = 0) ∧
    (ρ g : Matrix (Fin d) (Fin d) k).charpoly = (ρ₀ g : Matrix (Fin d) (Fin d) k).charpoly

theorem IsGr.comp {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {d : ℕ} {ρ₀ ρ : Γ →* GL (Fin d) k} (h : IsGr ρ₀ ρ) (f : Γ' →* Γ) :
    IsGr (ρ₀.comp f) (ρ.comp f) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun g => hc (f g)⟩

def MatEx : Prop := ∀ (Γ L : Type) [Group Γ] [Field L] (M : Type 1) [AddCommGroup M] [Module L M] (a : Γ → M →ₗ[L] M),
  a 1 = LinearMap.id → (∀ g h, a (g * h) = a g ∘ₗ a h) → ∀ U : Submodule L M, (∀ g, ∀ x ∈ U, a g x ∈ U) →
  ∀ (d : ℕ) (b : Module.Basis (Fin d) L U), ∃ ρ : Γ →* GL (Fin d) L,
    (∀ g j, a g (b j).1 = ∑ i, (ρ g : Matrix (Fin d) (Fin d) L) i j • (b i).1) ∧
    ∀ i j, ∃ μ : M →ₗ[L] L, ∀ g, (ρ g : Matrix (Fin d) (Fin d) L) i j = μ (a g (b j).1)

def MatConj : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω]
  (L : Type) [Field L] [Algebra ℚ_[l] L] (θ : H.Γ → L) (d : ℕ) (ρ : (Ω ≃ₐ[k] Ω) →* GL (Fin d) L) (P : GL (Fin d) L),
  IsMat l H Ω L θ ρ → IsMat l H Ω L θ (cj P ρ)

def HopGal : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k], (l : k) ≠ 0 → ∀ (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω]
  (g : H.Γ) (d : ℕ), FEt (H.s g) d → ∀ σ : Ω ≃ₐ[k] Ω, hop l H Ω g ∘ₗ galTot l Ω H.q σ = galTot l Ω H.q σ ∘ₗ hop l H Ω g

def OpConj : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω] (g : H.Γ)
  (T : Htot l (sch.obj (H.geomZ Ω)) →ₗ[ℚ_[l]] Htot l (sch.obj (H.geomZ Ω))) (σ : Ω ≃ₐ[k] Ω),
  GlobalTheory.GalV.IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T →
  GlobalTheory.GalV.IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) (galTot l Ω H.q σ ∘ₗ T ∘ₗ galTot l Ω H.q σ⁻¹)

def OpUniq : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k], (l : k) ≠ 0 → ∀ (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω]
  (g : H.Γ) (d : ℕ), FEt (H.s g) d → ∀ T, GlobalTheory.GalV.IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T → T = hop l H Ω g

def PieceStab : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k], (l : k) ≠ 0 → ∀ (H : HTower k), (∀ g, ∃ d, FEt (H.s g) d) →
  ∀ (Ω : Type) [Field Ω] [Algebra k Ω] (L : Type) [Field L] [Algebra ℚ_[l] L] (θ : H.Γ → L) (σ : Ω ≃ₐ[k] Ω),
  ∀ x ∈ piece l H Ω L θ, galV l H Ω L σ x ∈ piece l H Ω L θ

def RelDim : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)), Smooth p → IsIntegral X →
  ∃ d, SmoothOfRelativeDimension d p

def CompSum : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)), Smooth p → IsProper p →
  ∃ (r : ℕ) (Y : Fin r → Scheme.{0}) (j : ∀ s, Y s ⟶ X), CrystallineSemistableComparison.IsSum j ∧ ∀ s, IsIntegral (Y s)

def DegFin : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → ∀ {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)), Smooth p → IsProjOver p →
  (∀ n, FiniteDimensional ℚ_[l] (HQ l (sch.obj X) n 0)) ∧ ∃ N : ℤ, ∀ n, (n < 0 ∨ N < n) → Subsingleton (HQ l (sch.obj X) n 0)

def HtotFin : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → ∀ {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)), Smooth p → IsProjOver p → FiniteDimensional ℚ_[l] (Htot l (sch.obj X))

def HtDesc : Prop := ∀ (q : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)), QuasiCompact p → QuasiSeparated p → ∀ (n i : ℤ) (y : Ht q (sch.obj (geom Ω p)) n i),
  ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L) (z : Ht q (sch.obj (geom L p)) n i),
    pull _ (sch.map (LateralTheory.EWeil.StabPf.proj L p)) _ n z = y

def StabOpen : Prop := ∀ (l : ℕ) [Fact l.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)), QuasiCompact p → QuasiSeparated p → ∀ (n i : ℤ) (x : Hl l (sch.obj (geom Ω p)) n i) (m : ℕ),
  IsOpen {σ : Ω ≃ₐ[k] Ω | (galHl l Ω p n i σ x).1 m = x.1 m}

def DegCont : Prop := ∀ (l : ℕ) [Fact l.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)), QuasiCompact p → QuasiSeparated p → ∀ n i : ℤ,
  Module.Finite ℤ_[l] (Hl l (sch.obj (geom Ω p)) n i) → ∀ (v : HQ l (sch.obj (geom Ω p)) n i)
    (μ : Module.Dual ℚ_[l] (HQ l (sch.obj (geom Ω p)) n i)), Continuous fun σ => μ (galHQ l Ω p n i σ v)

def ExtCont : Prop := ∀ (Γ F L : Type) [TopologicalSpace Γ] [Field F] [TopologicalSpace F] [Field L] [TopologicalSpace L]
  [IsTopologicalRing L] [Algebra F L], Continuous (algebraMap F L) → ∀ (M : Type 1) [AddCommGroup M] [Module F M]
  [FiniteDimensional F M] (a : Γ → M →ₗ[F] M), (∀ (v : M) (μ : Module.Dual F M), Continuous fun g => μ (a g v)) →
  ∀ (v : L ⊗[F] M) (μ : (L ⊗[F] M) →ₗ[L] L), Continuous fun g => μ ((a g).baseChange L v)

def TotCont : Prop := ∀ (l : ℕ) [Fact l.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω], (l : k) ≠ 0 →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)), IsProper p → ∀ (v : Htot l (sch.obj (geom Ω p)))
    (μ : Module.Dual ℚ_[l] (Htot l (sch.obj (geom Ω p)))), Continuous fun σ => μ (galTot l Ω p σ v)

end UpperTheory.Gal.Int.Geo

end
