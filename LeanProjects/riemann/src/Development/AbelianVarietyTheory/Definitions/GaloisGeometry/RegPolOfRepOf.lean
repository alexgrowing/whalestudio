import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsSumOfSelf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AboveL

section Local

variable {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {A : ValuationSubring Ω}
  {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}

def AbW (x : WD h) : Prop :=
  ∀ g g' : Weil h, x.charPol (g * g' * g⁻¹ * g'⁻¹) = (Polynomial.X - 1) ^ x.lpDim

structure Near (x y : WD h) : Prop where
  mono : x.mono0 ↔ y.mono0
  size : ∀ σ : Weil h, (x.eig σ).map (fun z => ‖z‖) = (y.eig σ).map (fun z => ‖z‖)
  eq : ∀ (χ : Weil h →* ℂˣ) (hχ : GlobalTheory.WeilDeligne.IsSmooth χ), IneTriv (y.lpTwist χ hχ) → x = y
  tame : ∀ (χ : Weil h →* ℂˣ) (hχ : GlobalTheory.WeilDeligne.IsSmooth χ), IsTameWD (y.lpTwist χ hχ) →
    ∀ τ : Ine (F := K) A, x.charPol (ineIncl h τ) = y.charPol (ineIncl h τ)

theorem Near.refl (x : WD h) : Near x x := ⟨Iff.rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem Near.of_eq {x y : WD h} (e : x = y) : Near x y := e ▸ Near.refl x

theorem Near.lpDim_eq {x y : WD h} (n : Near x y) : x.lpDim = y.lpDim := by
  have := congrArg Multiset.card (n.size 1)
  simpa only [Multiset.card_map, WD.card_eig] using this

example : ¬ Near (WD.lpZero h) (WD.lpSp h 1) := fun n => by
  have := n.lpDim_eq
  rw [WD.lpDim_lpSp, WD.lpZero, WD.lpDim_mk] at this
  simp at this

end Local

def SolvDisj {K Ω : Type} (M : Type) [Field K] [Field M] [Field Ω] [Algebra K Ω] [Algebra M Ω] [Algebra K M] [IsScalarTower K M Ω]
    (N : Subgroup (G K Ω)) : Prop :=
  IsGalois K M ∧ IsSolvable (M ≃ₐ[K] M) ∧
    ∀ g : G K Ω, ∃ (x : G M Ω) (n : G K Ω), n ∈ N ∧ g = AlgEquiv.restrictScalarsHom K x * n

def BCof (Ω : Type) {K M : Type} [Field Ω] [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] {a : ℕ}
    (π : CuspSub K a) (π' : CuspSub M a) : Prop :=
  RegPol π ∧ RegPol π' ∧
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G K Ω →* GL (Fin a) (Qbar l)), RepOf π ι r → RepOf π' ι (resTo M r)

def AboveNear : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (r : G E Ω →* GL (Fin a) (Qbar l)), RepOf π ι r →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw),
      IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) → ∀ σ, π.IsLocComp w σ → ∀ rc, GlobalTheory.TheRec.IsTheRec h rc →
        Near (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)) (rc (algNorm σ))

section API

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

variable {K M : Type} [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] {a : ℕ}

theorem BCof.repOf {π : CuspSub K a} {π' : CuspSub M a} (hb : BCof Ω π π') {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {r : G K Ω →* GL (Fin a) (Qbar l)} (hr : RepOf π ι r) : RepOf π' ι (resTo M r) := hb.2.2 l ι r hr

end API

end GlobalTheory.AboveL

end
