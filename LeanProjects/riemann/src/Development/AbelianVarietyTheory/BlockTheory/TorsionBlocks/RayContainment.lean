import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RayContainment

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def conjI (H : Host E) (I : Ideal (𝓞 E)) : Ideal (𝓞 E) := I.map (H.bar : 𝓞 E →+* 𝓞 E)

def modulus (H : Host E) (Q : Finset (Ideal (𝓞 E))) : Ideal (𝓞 E) := ∏ P ∈ Q, P * conjI H P

def primeUnder (Q : Finset (Ideal (𝓞 E))) : ℕ := ∏ q ∈ Q.image Ideal.absNorm, q

def IsPlaceSet (H : Host E) (Q : Finset (Ideal (𝓞 E))) : Prop :=
  ∀ P ∈ Q, P.IsMaximal ∧ (Ideal.absNorm P).Prime ∧ Odd (Ideal.absNorm P) ∧
    ((Ideal.absNorm P : ℕ) : 𝓞 E) ∉ P ^ 2 ∧ conjI H P ∉ Q

def IsTwist (H : Host E) (Q : Finset (Ideal (𝓞 E))) {K : Type} [Field K] (xi : Ideal (𝓞 E) →*₀ K) : Prop :=
  (∀ 𝔞 : Ideal (𝓞 E), 𝔞 ⊔ modulus H Q ≠ ⊤ → xi 𝔞 = 0) ∧
  (∀ a : 𝓞 E, a ≠ 0 → a - 1 ∈ modulus H Q → xi (Ideal.span {a}) = 1) ∧
  ∀ 𝔟 : Ideal (𝓞 (maximalRealSubfield E)), 𝔟 ≠ ⊥ →
    𝔟.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ⊔ modulus H Q = ⊤ →
      xi (𝔟.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))) = 1

def ContainsRay (L : Type) [Field L] [NumberField L] (d m : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra K L),
    Module.finrank ℚ K = 2 ∧ (∃ x : K, x ^ 2 = -(d : K)) ∧
    ∀ 𝔄 : Ideal (𝓞 L), 𝔄 ≠ ⊥ → 𝔄 ⊔ Ideal.span {(m : 𝓞 L)} = ⊤ →
      ∃ a : 𝓞 K, a - 1 ∈ Ideal.span {(m : 𝓞 K)} ∧ Ideal.relNorm (𝓞 K) 𝔄 = Ideal.span {a}

variable {H : Host E} {Dw : Datum H} {l : Level H}

def TupleGuard (c : Coeff l) (Q : Finset (Ideal (𝓞 E))) (xi : Ideal (𝓞 E) →*₀ c.F) : Prop :=
  IsPlaceSet H Q ∧ IsTwist H Q xi ∧ Nat.Coprime (primeUnder Q) l.M ∧
    zeta (Nat.lcm (l.M * primeUnder Q) l.A) ∈ c.F ∧ ContainsRay c.F H.d (l.M * primeUnder Q)

def IsHalf (H : Host E) (N : ℕ) (I : Ideal (𝓞 E)) : Prop :=
  I = Ideal.span {a | a ∈ I ∧ a ∈ Algebra.adjoin ℤ {H.w0}} ∧
    I * conjI H I = Ideal.span {(N : 𝓞 E)} ∧ I ⊔ conjI H I = ⊤

def indexIdeal (D : Datum H) (N : Submodule (𝓞 E) D.La) : Ideal (𝓞 E) :=
  Ideal.span {a | ∃ (ω : D.La [⋀^Fin (D.p + D.q)]→ₗ[𝓞 E] 𝓞 E) (x : Fin (D.p + D.q) → D.La),
    (∀ i, x i ∈ N) ∧ a = ω x}

def DetIdeal (D D' : Datum H) (l₂ : Level H) (t : D.La →ₗ[𝓞 E] D'.La) (𝔣 𝔠 : Ideal (𝓞 E)) : Prop :=
  𝔠 ≠ ⊥ ∧ 𝔠 ⊔ 𝔣 = ⊤ ∧ ∃ (n : ℕ) (ψ : D'.La →ₗ[𝓞 E] D.La),
    0 < n ∧ Nat.Coprime n l₂.M ∧
    (∀ x y, D.EF (ψ x) (ψ y) = (n : ℤ) ^ 2 * D'.EF x y) ∧
    (∀ a ∈ Mfr l₂ • (⊤ : Submodule (𝓞 E) D.La), D.ModN l₂.M (ψ (t a) - n • a)) ∧
    indexIdeal D (LinearMap.range ψ) * conjI H 𝔠 = Ideal.span {(n : 𝓞 E) ^ (D.p + D.q)} * 𝔠

variable {Xo : Moduli Dw l} {c : Coeff l}

def embCov {n : ℕ} (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) : d.c₂.F →+* ℂ :=
  σ.comp (d.eF.symm : d.c₂.F →+* c.F)

def IsCover {n : ℕ} (d : DeltaDat Xo c n) (N : ℕ) (I : Ideal (𝓞 E)) : Prop :=
  d.pd = N ∧ d.I = I ∧ d.l₂.M = l.M * N ∧ d.l₂.Mb = l.Mb * I ∧ d.l₂.A = l.A ∧
  (∃ jK : KA l →+* KA d.l₂, (∀ x, ((jK x : KA d.l₂) : ℂ) = ((x : KA l) : ℂ)) ∧
    d.r ≫ Xo.s = d.Xo₂.s ≫ spMap jK) ∧
  d.EtaOK ∧
  (∃ rF : d.Xo₂.XF d.c₂ ⟶ Xo.XF c,
    rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ d.r ∧
    rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion d.hF.ge).toRingHom ∧
    IsFinite rF ∧ Etale rF ∧ Surjective rF) ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ y : FrPt Xo c k, ∃ y₂ : FrPt d.Xo₂ d.c₂ k, FrOver d y₂ y

def IsXiDet {n : ℕ} (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (𝔣 : Ideal (𝓞 E)) (xi : Ideal (𝓞 E) →*₀ c.F) : Prop :=
  d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 ∧
  (∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H Dw.p Dw.q ty ∧
    Nonempty (FamilyUnif d.Xo₂ ((embCov d σ).comp (IntermediateField.inclusion d.c₂.le).toRingHom) ty)) ∧
  ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H Dw.p Dw.q ty →
    ∀ (U : FamilyUnif d.Xo₂ ((embCov d σ).comp (IntermediateField.inclusion d.c₂.le).toRingHom) ty) (i : Fin U.n),
      (∃ 𝔠, DetIdeal Dw (U.Di i) d.l₂ (U.t i) 𝔣 𝔠) ∧
      ∀ 𝔠, DetIdeal Dw (U.Di i) d.l₂ (U.t i) 𝔣 𝔠 →
        ∀ P, IsPeriod (U.Di i) ty P → ∀ y : FrPt d.Xo₂ d.c₂ (CAt (embCov d σ)), y.x = U.u i P →
          toC (evR d.Xo₂ d.c₂ d.cδ y) = σ (xi 𝔠)

def IsPinnedCover₂ [StarRing (𝓞 E)] {n : ℕ} (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (Q : Finset (Ideal (𝓞 E)))
    (xi : Ideal (𝓞 E) →*₀ c.F) (I : Ideal (𝓞 E)) : Prop :=
  IsCover d (primeUnder Q) I ∧ IsNab d.Xo₂ d.c₂ d.nab₂ ∧ IsXiDet d σ (modulus H Q) xi ∧ d.φδ = fun _ => 1

def CoversExist : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (n : ℕ) (Tup : Type) (Q : Tup → Finset (Ideal (𝓞 E)))
    (xi : Tup → (Ideal (𝓞 E) →*₀ c.F)),
    (∀ a : 𝓞 E, star a = H.bar a) → Odd (Dw.p + Dw.q) → GoodEmb c σ → (∀ t, TupleGuard c (Q t) (xi t)) →
      (∀ t, ∃ I, IsHalf H (primeUnder (Q t)) I) ∧
      ∀ I : Tup → Ideal (𝓞 E), (∀ t, IsHalf H (primeUnder (Q t)) (I t)) →
        ∃ dδ : Tup → DeltaDat Xo c n, ∀ t, IsPinnedCover₂ (dδ t) σ (Q t) (xi t) (I t)

open Classical in

example (H : Host E) (K : Type) [Field K] :
    IsPlaceSet H ∅ ∧ IsTwist H ∅ (1 : Ideal (𝓞 E) →*₀ K) ∧ IsHalf H (primeUnder (∅ : Finset (Ideal (𝓞 E)))) ⊤ := by
  refine ⟨fun P hP => by simp at hP, ⟨fun 𝔞 h => ?_, fun a ha _ => ?_, fun 𝔟 hb _ => ?_⟩, ?_, ?_, by simp⟩
  · simp [modulus] at h
  · apply MonoidWithZeroHom.one_apply_of_ne_zero
    simpa using ha
  · apply MonoidWithZeroHom.one_apply_of_ne_zero
    intro h
    exact hb ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  · symm
    rw [Ideal.eq_top_iff_one]
    exact Ideal.subset_span ⟨trivial, one_mem _⟩
  · simp [conjI, primeUnder, Ideal.map_top]

end GlobalTheory.IndefiniteRowSideFullHecke.RayContainment
