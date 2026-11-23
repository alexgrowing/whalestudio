import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedNoJump

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

section Conj

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {c : Ω ≃+* Ω}

theorem conj_conj (hc : IsCMConjOm E Ω c) (x : Ω) : c (c x) = x := by
  obtain ⟨⟨j, hj⟩, -⟩ := hc
  apply j.injective
  rw [hj, hj]
  simp

theorem conj_symm (hc : IsCMConjOm E Ω c) (x : Ω) : c.symm x = c x := by
  rw [RingEquiv.symm_apply_eq, conj_conj hc]

def conjElt (hc : IsCMConjOm E Ω c) (g : G E Ω) : G E Ω :=
  AlgEquiv.ofRingEquiv (f := (c.symm.trans g.toRingEquiv).trans c) (fun x => by
    obtain ⟨y, hy⟩ := hc.2 x
    change c (g (c.symm (algebraMap E Ω x))) = algebraMap E Ω x
    rw [conj_symm hc, hy, AlgEquiv.commutes, ← hy, conj_conj hc])

theorem conjElt_apply (hc : IsCMConjOm E Ω c) (g : G E Ω) (x : Ω) :
    conjElt hc g x = c (g (c.symm x)) := rfl

def conjHom (hc : IsCMConjOm E Ω c) : G E Ω →* G E Ω where
  toFun := conjElt hc
  map_one' := by
    ext x
    simp [conjElt_apply]
  map_mul' g h := by
    ext x
    simp [conjElt_apply]

end Conj

section Rep

variable {Γ : Type} [Group Γ] {A : Type} [CommRing A] {n : ℕ}

def scalGL : Aˣ →* GL (Fin n) A :=
  Units.map (Matrix.scalar (Fin n) : A →+* Matrix (Fin n) (Fin n) A).toMonoidHom

theorem scalGL_comm (a : Aˣ) (M : GL (Fin n) A) : Commute (scalGL a) M := by
  apply Units.ext
  exact (Matrix.scalar_commute (a : A) (fun b => mul_comm _ b) (M : Matrix (Fin n) (Fin n) A)).eq

def twist (ρ : Γ →* GL (Fin n) A) (χ : Γ →* Aˣ) : Γ →* GL (Fin n) A where
  toFun g := scalGL (χ g) * ρ g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (scalGL (χ h)),
      (scalGL_comm (χ h) (ρ g)).eq, mul_assoc]

def transGL (M : GL (Fin n) A) : GL (Fin n) A where
  val := (M : Matrix (Fin n) (Fin n) A).transpose
  inv := ((M⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A).transpose
  val_inv := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

def dual (ρ : Γ →* GL (Fin n) A) : Γ →* GL (Fin n) A where
  toFun g := transGL (ρ g⁻¹)
  map_one' := by
    apply Units.ext
    simp [transGL]
  map_mul' g h := by
    apply Units.ext
    simp only [transGL, mul_inv_rev, map_mul, Units.val_mul, Matrix.transpose_mul]

def IsoLat (ρ ρ' : Γ →* GL (Fin n) A) : Prop :=
  ∃ P : GL (Fin n) A, ∀ g, P * ρ g = ρ' g * P

example (ρ : Γ →* GL (Fin n) A) : IsoLat (twist ρ 1) ρ := ⟨1, fun g => by simp [twist]⟩

example (ρ : Γ →* GL (Fin n) A) : IsoLat (dual (dual ρ)) ρ :=
  ⟨1, fun g => by apply Units.ext; simp [dual, transGL]⟩

end Rep

variable (D : D7)

def eps (i : D.ntw.Tw) : G D.host.E D.nd.Om →* (D.ntw.O0 i)ˣ :=
  (Units.map (algebraMap ℤ_[D.ntw.l i] (D.ntw.O0 i)).toMonoidHom).comp
    (cycZ (F := D.host.E) (Ω := D.nd.Om) (D.ntw.l i))

def latT (i : D.ntw.Tw) (s : D.ntw.Sig i) : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.ntw.O0 i) :=
  twist (D.ntw.rhoS i s) (D.ntw.chi1 i (D.ntw.jS i s) (D.ntw.side i s))⁻¹

def latDualConjOne (i : D.ntw.Tw) (s : D.ntw.Sig i) :
    G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.ntw.O0 i) :=
  twist ((dual (latT D i s)).comp (conjHom D.ntw.cc_cm)) (eps D i)

def DualLat (i : D.ntw.Tw) (s : D.ntw.Sig i) : Prop :=
  IsoLat (latDualConjOne D i s) (twist (latT D i s) (eps D i ^ D.R.t))

def NoJump (i : D.ntw.Tw) (s : D.ntw.Sig i) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.ntw.l i))
    (τ : ↥(D.ntwbr i w hw).Kw.1 →ₐ[ℚ_[D.ntw.l i]] ↥(D.ntwbr i w hw).LL.1) (a : ℤ),
    -1 ≤ a → a ≤ (D.R.t : ℤ) →
      ¬ (D.ntwbr i w hw).IsJumpW (D.loc (D.ntw.l i))
        ((latT D i s).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ a

def cycField (l : ℕ) : IntermediateField D.host.E D.nd.Om :=
  IntermediateField.adjoin D.host.E {x : D.nd.Om | x ^ l = 1}

def UnramifiedIn (l : ℕ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal ^ 2

def NC (l : ℕ) : Prop :=
  l = 2 ∨ UnramifiedIn D l ∨ D.R.t * D.R.r < Module.finrank D.host.E ↥(cycField D l)

def thEmpty (i : D.ntw.Tw) (lam : D.ntw.abelian₂ i) : FractionRing (D.ntw.O i) :=
  ∑ x : D.ntw.RCG i ∅, D.ntw.th i ∅ lam x

def ConstantTermsFinite (i : D.ntw.Tw) (lam : D.ntw.abelian₂ i) : Prop := thEmpty D i lam ≠ 0

def NCrit (R : Ranks) : ℕ := R.k + R.m * (R.t + (R.r + 6) + 1)

def IntPoint (i : D.ntw.Tw) (lam : D.ntw.abelian₂ i) : Prop :=
  ∃ s : ℤ, D.ntw.s2 i lam = 2 * s ∧ 1 ≤ s ∧ s ≤ (NCrit D.R : ℤ) + 1 ∧
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), P ∉ D.ntw.S0 i →
      D.ntw.qs i lam P = ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (D.ntw.O i)) ^ (-s)

def SettingHypotheses (i : D.ntw.Tw) : Prop :=
  True ∧
  (∀ s : D.ntw.Sig i, DualLat D i s ∧ NoJump D i s) ∧
  (∀ lam : D.ntw.abelian₂ i, ConstantTermsFinite D i lam ∧ IntPoint D i lam) ∧
  100 ≤ D.R.r ∧ ∀ k : Fin 2, 2 * D.R.r ≤ D.host.g k

def Row : Prop := ∀ i : D.ntw.Tw, D.ntw.NonzeroIndexPlace i → SettingHypotheses D i

example : NC D 2 := Or.inl rfl

end GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedNoJump

end
