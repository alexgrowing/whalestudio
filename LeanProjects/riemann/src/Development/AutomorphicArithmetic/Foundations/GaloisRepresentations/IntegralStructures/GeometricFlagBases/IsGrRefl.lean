import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IdTower
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain GlobalTheory.EtC TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois)
open GlobalTheory.HodgeCoh (hodgeH hodgeTrace hodgePull)

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace UpperTheory.Gal.Int.Geo

def FEt {Y X : Scheme.{0}} (f : Y ⟶ X) (d : ℕ) : Prop :=
  IsFinite f ∧ Etale f ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ X),
    Nat.card {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ f = x} = d

theorem fEt_id (X : Scheme.{0}) : FEt (𝟙 X) 1 :=
  ⟨inferInstance, inferInstance, fun K _ _ x => by
    have : Unique {y : Spec (CommRingCat.of K) ⟶ X // y ≫ 𝟙 X = x} :=
      ⟨⟨⟨x, Category.comp_id x⟩⟩, fun a => Subtype.ext ((Category.comp_id a.1).symm.trans a.2)⟩
    exact Nat.card_unique⟩

section Tower

variable {k : Type} [Field k]

def Nice (H : HTower k) : Prop := Smooth H.q ∧ IsProjOver H.q ∧ ∀ g, ∃ d, FEt (H.s g) d

def bc (H : HTower k) (K : Type) [Field K] [Algebra k K] : HTower K where
  Γ := H.Γ
  Z := H.geomZ K
  q := pullback.snd _ _
  Y g := GlobalTheory.Et.geom K (H.s g ≫ H.q)
  s g := H.sΩ K g
  t g := H.tΩ K g
  comm g := by
    simp only [HTower.sΩ, HTower.tΩ, GlobalTheory.Et.geomMap]
    erw [pullback.lift_snd, pullback.lift_snd]

def bcAlong (H : HTower k) {K : Type} [Field K] (τ : k →+* K) : HTower K := letI := τ.toAlgebra; bc H K

def IsHEig (H : HTower k) (θ : H.Γ → k) (a b : ℕ) (x : hodgeH H.q a b) : Prop :=
  ∀ g, ∃ (_ : IsFinite (H.s g)) (_ : Etale (H.s g)),
    hodgeTrace (s := H.q) (s' := H.s g ≫ H.q) (f := H.s g) rfl a b (hodgePull (s := H.q) (s' := H.s g ≫ H.q) (H.comm g) a b x) = θ g • x

def HOcc (H : HTower k) (θ : H.Γ → k) (a : ℕ) : Prop := ∃ (b : ℕ) (x : hodgeH H.q a b), x ≠ 0 ∧ IsHEig H θ a b x

variable (l : ℕ) [Fact l.Prime] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω] (L : Type) [Field L] [Algebra ℚ_[l] L]

def piece (θ : H.Γ → L) : Submodule L (L ⊗[ℚ_[l]] Htot l (sch.obj (H.geomZ Ω))) :=
  ⨅ g, Module.End.eigenspace ((hop l H Ω g).baseChange L) (θ g)

theorem piece_le (θ : H.Γ → L) : piece l H Ω L θ ≤ GlobalTheory.GalV.V l H Ω L id θ :=
  iInf_mono fun _ => Module.End.eigenspace_le_maxGenEigenspace

def IsMat (θ : H.Γ → L) {d : ℕ} (ρ : (Ω ≃ₐ[k] Ω) →* GL (Fin d) L) : Prop :=
  ∃ b : Module.Basis (Fin d) L (piece l H Ω L θ), ∀ σ j,
    galV l H Ω L σ (b j).1 = ∑ i, (ρ σ : Matrix (Fin d) (Fin d) L) i j • (b i).1

end Tower

def IsGr {Γ L : Type} [Group Γ] [Field L] {d : ℕ} (ρ₀ ρ : Γ →* GL (Fin d) L) : Prop :=
  ∃ c : Fin d → ℕ, ∀ g, (ρ₀ g : Matrix (Fin d) (Fin d) L).BlockTriangular c ∧
    ∀ i j, (ρ g : Matrix (Fin d) (Fin d) L) i j = if c i = c j then (ρ₀ g : Matrix (Fin d) (Fin d) L) i j else 0

theorem isGr_refl {Γ L : Type} [Group Γ] [Field L] {d : ℕ} (ρ : Γ →* GL (Fin d) L) : IsGr ρ ρ :=
  ⟨fun _ => 0, fun _ => ⟨fun _ _ h => absurd h (lt_irrefl _), fun _ _ => by simp⟩⟩

section Cover

variable {k : Type} [Field k] {L : Type} [Field L]

abbrev gen (O k : Type) [CommRing O] [Field k] [Algebra O k] : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (algebraMap O k))

structure Cover (H : HTower k) (θ : H.Γ → L) (O : Type) [CommRing O] [Algebra O k] : Type 1 where
  Y : Scheme.{0}
  p : Y ⟶ Spec (CommRingCat.of O)
  smooth : Smooth p
  proj : IsProjOver p
  π : H.Z ⟶ Y
  ov : π ≫ p = H.q ≫ gen O k
  Δ : Type
  [grp : Group Δ]
  [fin : Finite Δ]
  a : Δ → (H.Z ⟶ H.Z)
  finπ : IsFinite (pullback.lift π H.q ov)
  etπ : Etale (pullback.lift π H.q ov)
  one : a 1 = 𝟙 _
  mul : ∀ g h, a (g * h) = a g ≫ a h
  spl : Splits (pullback.lift π H.q ov) (pullback.lift π H.q ov) a
  fix : ∀ δ, ∃ g, IsIso (H.s g) ∧ H.t g = H.s g ≫ a δ ∧ θ g = 1
  dim : ∃ d, SmoothOfRelativeDimension d p

attribute [instance] Cover.grp Cover.fin

variable {H : HTower k} {θ : H.Γ → L} {O : Type} [CommRing O] [Algebra O k]

def Cover.Onto (C : Cover H θ O) : Prop := Surjective (pullback.lift C.π H.q C.ov)

theorem Cover.isGalois (C : Cover H θ O) (h : C.Onto) : IsGalois (pullback.lift C.π H.q C.ov) C.Δ C.a :=
  ⟨C.finπ, C.etπ, h, C.one, C.mul, C.spl⟩

def Cover.Lies (C : Cover H θ O) (g : H.Γ) {T : Scheme.{0}} (s t : T ⟶ C.Y) (m : ℕ) : Prop :=
  0 < m ∧ ∃ (κ : H.Y g ⟶ T) (h : H.s g ≫ C.π = κ ≫ s), κ ≫ t = H.t g ≫ C.π ∧ FEt (pullback.lift (H.s g) κ h) m

def Cover.Good (C : Cover H θ O) : Prop :=
  ∀ g, ∃ (T : Scheme.{0}) (s t : T ⟶ C.Y) (d m : ℕ), FEt s d ∧ t ≫ C.p = s ≫ C.p ∧ C.Lies g s t m

def Cover.Cong (C : Cover H θ O) (p f n : ℕ) (ϑ : ℕ → L) : Prop :=
  ∃ (ϖ : O) (T : Fin (n + 1) → crystallineComparison.Corr p C.Y) (γ : Fin (n + 1) → H.Γ) (m : Fin (n + 1) → ℕ), Irreducible ϖ ∧
    crystallineComparison.PtId p (p ^ f) n (crystallineComparison.fn C.p ϖ) T ∧
    ∀ j, (T j).r ≫ C.p = (T j).p ≫ C.p ∧ C.Lies (γ j) (T j).p (T j).r (m j) ∧ θ (γ j) = m j * ϑ j

end Cover

section Place

variable {E : Type} [Field E] [NumberField E] {L : Type} [Field L]

abbrev Ow (w : HeightOneSpectrum (𝓞 E)) : Type := ↥(w.valuation E).valuationSubring

variable (H : HTower E) (θ : H.Γ → L) (w : HeightOneSpectrum (𝓞 E))

def GoodAt : Prop := ∃ C : Cover H θ (Ow w), C.Onto ∧ C.Good

def GoodAtW : Prop := ∃ C : Cover H θ (Ow w), C.Good

def CongAt (n : ℕ) (ϑ : ℕ → L) : Prop :=
  ∃ (C : Cover H θ (Ow w)) (p f : ℕ), p.Prime ∧ (p : 𝓞 E) ∈ w.asIdeal ∧ Ideal.absNorm w.asIdeal = p ^ f ∧ C.Onto ∧ C.Cong p f n ϑ

def CongAtW (n : ℕ) (ϑ : ℕ → L) : Prop :=
  ∃ (C : Cover H θ (Ow w)) (p f : ℕ), p.Prime ∧ (p : 𝓞 E) ∈ w.asIdeal ∧ Ideal.absNorm w.asIdeal = p ^ f ∧ C.Cong p f n ϑ

end Place

end UpperTheory.Gal.Int.Geo

end
