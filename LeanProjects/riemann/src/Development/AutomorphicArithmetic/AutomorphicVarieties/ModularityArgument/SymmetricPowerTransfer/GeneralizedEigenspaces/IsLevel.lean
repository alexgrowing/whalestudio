import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryDoubleCosetIndicator
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.RepGApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def expo (ψ : Fin n → kˣ →* ℂˣ) (d : Fin n → kˣ) : ℂ :=
  ((torusChar ψ d * ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom d)⁻¹ : ℂˣ) : ℂ)

def Reg (a : kˣ →* ℂˣ) : Prop := (∀ u ∈ Hi.Uo k, a u = 1) ∧ ∀ m : ℤ, |m| ≤ 2 → a ^ 2 ≠ absPow k (m : ℂ)

end Loc

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

abbrev Kw (w : Plc L) : Type := w.adicCompletion L

open Classical in

def secW (n : ℕ) (w : Plc L) : GL (Fin n) (Kw w) →* UA L n :=
  if h : ∃ j : GL (Fin n) (Kw w) →* UA L n, (∀ g, j g ∈ locU n w) ∧ ∀ g, cLoc w (j g) = g then h.choose else 1

variable (L) in

def infC (n : ℕ) : UA L n →* (InfinitePlace L → GL (Fin n) ℂ) := Pi.monoidHom fun v => cEmb v.embedding

variable (L) in

def Kall (n : ℕ) : Subgroup (UA L n) := finU L n ⊓ ⨅ w : Plc L, (GlobalTheory.LFun.KGL w n).comap (cLoc w)

variable {n : ℕ}

def IsLevel (U : Subgroup (UA L n)) : Prop := U ≤ Kall L n ∧ IsOpen {x : finU L n | (x : UA L n) ∈ U}

def lev (U : Subgroup (UA L n)) (S : Finset (Plc L)) (V : ∀ w : Plc L, Sig.Lev (Kw w)) : Subgroup (UA L n) :=
  U ⊓ ⨅ w ∈ S, ((V w).J n).comap (cLoc w)

abbrev iw (w : Plc L) : Sig.Lev (Kw w) := Sig.Lev.iw _

abbrev deep (c : ℕ) (w : Plc L) : Sig.Lev (Kw w) := Sig.Lev.deep _ c

structure Places (S : Set (Plc L)) : Prop where
  split : ∀ w ∈ S, IsSplitAt w
  inj : Set.InjOn (fun w : Plc L => w.under (𝓞 (Lp L))) S

def HasTwo (S : Finset (Plc L)) : Prop :=
  ∀ w : Plc L, (2 : 𝓞 L) ∈ w.asIdeal → ∃ w' ∈ S, w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))

def repE {I : Type} [Fintype I] (j : ℕ) (e : I → ℤ) : Representation ℂ (I → GL (Fin 2) ℂ) (Wt.VD I j) where
  toFun g := ((∏ v, Matrix.GeneralLinearGroup.det (g v) ^ e v : ℂˣ) : ℂ) • Wt.mRep 2 _ g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, smul_mul_smul_comm, ← Units.val_mul, ← Finset.prod_mul_distrib]
    simp [mul_zpow]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

structure IsAF (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V) (U : Subgroup (UA L n)) (φ : UA L n → V) : Prop where
  left : ∀ γ ∈ ratU L n, ∀ g, φ (γ * g) = φ g
  inf : ∀ x ∈ infU L n, ∀ g, φ (g * x) = R (infC L n x⁻¹) (φ g)
  level : ∀ u ∈ U, ∀ g, φ (g * u) = φ g

def EigAt (φ : UA L n → V) (w : Plc L) (W : Sig.Lev (Kw w)) (d : Fin n → (Kw w)ˣ) (c : ℂ) : Prop :=
  Hi.dc ((rightReg ℂ (UA L n) V).comp (secW n w)) (W.J n) (W.J n) (Sig.dg d) φ = c • φ

def EigS (φ : UA L 2 → V) (w : Plc L) (W : Sig.Lev (Kw w)) (a : (Kw w)ˣ →* ℂˣ) : Prop :=
  ∀ t : (Kw w)ˣ, valuation (Kw w) (t : Kw w) < 1 → EigAt φ w W ![t, t⁻¹] (expo ![a, 1] ![t, t⁻¹])

def EigT (φ : UA L n → V) (w : Plc L) (W : Sig.Lev (Kw w)) (ψ : Fin n → (Kw w)ˣ →* ℂˣ) : Prop :=
  ∀ d, Sig.SDom d → EigAt φ w W d (expo ψ d)

def CoefIn (φ : UA L n → V) (π : Submodule ℂ (UA L n → ℂ)) : Prop := ∀ f : V →ₗ[ℂ] ℂ, f ∘ φ ∈ π

abbrev Comp (π : Submodule ℂ (UA L n → ℂ)) (w : Plc L) (τ : SmIrr (GL (Fin n) (Kw w))) : Prop :=
  IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ

def CompSub (π : Submodule ℂ (UA L n → ℂ)) (w : Plc L) (ψ : Fin n → (Kw w)ˣ →* ℂˣ) : Prop :=
  (∀ i, IsSmoothChar (ψ i)) ∧ ∃ τ, Comp π w τ ∧ IsSubquotient τ.ρ (prinSeries ψ)

def CompEq (π : Submodule ℂ (UA L n → ℂ)) (w : Plc L) (ψ : Fin n → (Kw w)ˣ →* ℂˣ) : Prop :=
  (∀ i, IsSmoothChar (ψ i)) ∧ ∃ τ, Comp π w τ ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ))

variable (L) in

abbrev Unr : Prop := ∀ w : Plc L, Algebra.IsUnramifiedAt (𝓞 (Lp L)) w.asIdeal

example (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V) (U : Subgroup (UA L n)) : IsAF R U 0 :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => by simp, fun _ _ _ => rfl⟩

end UpperTheory.V.Z.Sym.Dict

namespace UpperTheory.V.Z.Sym

open Dict

def SpecOut : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ S₀ : Finset (Plc L), Places (S₀ : Set (Plc L)) → HasTwo S₀ →
    ∀ j : ℕ, 1 ≤ j → ∃ c₀ : ℕ, ∀ c ≥ c₀, ∃ U₂ : Subgroup (UA L 2), IsLevel U₂ ∧
    ∀ S₁ : Finset (Plc L), Disjoint S₀ S₁ → Places ((S₀ : Set (Plc L)) ∪ S₁) → (∀ w ∈ S₁, locU 2 w ⊓ Kall L 2 ≤ U₂) →
    ∀ (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (e : InfinitePlace L → ℤ) (φ : UA L 2 → Wt.VD (InfinitePlace L) j), φ ≠ 0 →
      IsAF (repE j e) (lev (lev (Kall L 2) S₀ (deep c)) S₁ iw) φ →
      (∀ w ∈ S₀, EigS φ w (deep c w) (a w)) → (∀ w ∈ S₁, EigS φ w (iw w) (a w)) →
      (∃ φ' : UA L 3 → Wt.VG (InfinitePlace L) j, φ' ≠ 0 ∧ IsAF (Wt.repG _ j) (lev (lev (Kall L 3) S₀ (deep c)) S₁ iw) φ' ∧
        ∀ w ∈ S₁, EigT φ' w (iw w) ![a w, 1, (a w)⁻¹]) ∨
      ∃ φ' : UA L 2 → Wt.VD (InfinitePlace L) (2 * j + 1), φ' ≠ 0 ∧ IsAF (repE (2 * j + 1) 0) (lev U₂ S₁ iw) φ' ∧
        ∀ w ∈ S₁, EigS φ' w (iw w) (a w ^ 2)

def AdLift : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ (S₀ : Finset (Plc L)) (P : Set (Plc L)),
    Disjoint (S₀ : Set (Plc L)) P → Places ((S₀ : Set (Plc L)) ∪ P) → HasTwo S₀ →
    ∀ π : Submodule ℂ (UA L 2 → ℂ), IsAutRepU π → ∀ j : ℕ, 1 ≤ j →
    (∀ v : InfinitePlace L, ∃ lam, HasWeightAt π v.embedding lam ∧ lam.w 0 - lam.w 1 = j) →
    (∀ w : Plc L, (∀ w' ∈ S₀, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) → IsUnramU π w) →
    ∀ ψ : ∀ w : Plc L, Fin 2 → (Kw w)ˣ →* ℂˣ, (∀ w ∈ (S₀ : Set (Plc L)) ∪ P, CompEq π w (ψ w)) →
    (∀ w ∈ P, (∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ w i u = 1) ∧ Reg (ψ w 0 / ψ w 1)) →
    (∃ σ : Submodule ℂ (UA L 3 → ℂ), IsAutRepU σ ∧
      ∀ᶠ w in Filter.cofinite, w ∈ P → CompSub σ w ![ψ w 0 / ψ w 1, 1, (ψ w 0 / ψ w 1)⁻¹]) ∨
    ∃ σ : Submodule ℂ (UA L 2 → ℂ), IsAutRepU σ ∧
      ∀ᶠ w in Filter.cofinite, w ∈ P → ∃ ψ', CompSub σ w ψ' ∧ ψ' 0 / ψ' 1 = (ψ w 0 / ψ w 1) ^ 2

end UpperTheory.V.Z.Sym

end
