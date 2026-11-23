import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps

noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace UpperTheory.V.ZK.Cl

variable {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] {J : Type}

abbrev GG (L F : Type) [Field L] [Field F] [Algebra L F] (J : Type) : Type := (J → F) ≃ₗ[L] (J → F)

def InLat (𝔞 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) (x : J → F) : Prop :=
  ∀ j P, P.valuation F (x j) ≤ WithZero.exp (-𝔞 j P)

def InLoc (b : 𝓞 L) (x : J → F) : Prop :=
  ∀ j (P : HeightOneSpectrum (𝓞 F)), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal → P.valuation F (x j) ≤ 1

def StabP (L : Type) [Field L] [Algebra L F] (p : (J → F) → Prop) : Subgroup (GG L F J) where
  carrier := {g | ∀ x, p x ↔ p (g x)}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {g h} hg hh x => (hh x).trans (hg (h x))
  inv_mem' := fun {g} hg x => by
    have := hg (g⁻¹ x)
    rw [show g (g⁻¹ x) = x from g.apply_symm_apply x] at this
    exact this.symm

abbrev GLoc (F : Type) [Field F] [NumberField F] [Algebra L F] (J : Type) (b : 𝓞 L) : Subgroup (GG L F J) :=
  StabP L (InLoc (F := F) (J := J) b)

def diag (L : Type) [Field L] [Algebra L F] : (J → Fˣ) →* GG L F J where
  toFun u := (LinearEquiv.piCongrRight fun j => DistribMulAction.toLinearEquiv L F (u j))
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_smul]

theorem diag_apply (u : J → Fˣ) (x : J → F) (j : J) : diag L u x j = (u j : F) * x j := rfl

def toF (ζ : (𝓞 F)ˣ) : Fˣ := Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) ζ

theorem toF_pow {ζ : (𝓞 F)ˣ} {q : ℕ} (h : ζ ^ q = 1) : toF ζ ^ q = 1 := by rw [toF, ← map_pow, h, map_one]

def repC (L : Type) [Field L] [Algebra L F] (q : ℕ) [NeZero q] (ζ : (𝓞 F)ˣ) (h : ζ ^ q = 1) (χ : J → ZMod q) :
    Cq q →* GG L F J :=
  (diag L).comp (MonoidHom.pi fun j => chi q (toF ζ) (toF_pow h) (χ j).val)

def repD (L : Type) [Field L] [Algebra L F] (q : ℕ) [NeZero q] (ζ : (𝓞 F)ˣ) (h : ζ ^ q = 1) :
    Cq q × Cq q →* GG L F (ZMod q × ZMod q) :=
  (diag L).comp (MonoidHom.pi fun j => (chi q (toF ζ) (toF_pow h) j.1.val).coprod (chi q (toF ζ) (toF_pow h) j.2.val))

def BlockForm {X : Type} (g : GG L F J) (s : J → F ≃ₐ[L] F) (β : J → X)
    (g' : ∀ x : X, ({j // β j = x} → F) ≃ₗ[F] ({j // β j = x} → F)) : Prop :=
  ∀ w j, s j (g w j) = g' (β j) (fun i => s i.1 (w i.1)) ⟨j, rfl⟩

def ResF {k : Type} [Field k] (r : 𝓞 F →+* k) (x : F) (u : k) : Prop :=
  ∃ a b : 𝓞 F, r b ≠ 0 ∧ x * b = a ∧ r a = u * r b

def RedV (L : Type) [Field L] [Algebra L F] {k : Type} [Field k] (r : 𝓞 F →+* k) (x : J → F)
    (v : (F ≃ₐ[L] F) × J → k) : Prop := ∀ σ j, ResF r (σ (x j)) (v (σ, j))

def actO (σ : F ≃ₐ[L] F) : 𝓞 F ≃+* 𝓞 F := RingOfIntegers.mapRingEquiv σ.toRingEquiv

def Split (L : Type) [Field L] [NumberField L] [Algebra L F] {k : Type} [Field k] (r : 𝓞 F →+* k) : Prop :=
  (∀ v : (F ≃ₐ[L] F) → k, ∃ a : 𝓞 F, ∀ σ, r (actO σ a) = v σ) ∧
    ∀ a : 𝓞 F, (∀ σ : F ≃ₐ[L] F, r (actO σ a) = 0) →
      a ∈ (RingHom.ker (r.comp (algebraMap (𝓞 L) (𝓞 F)))).map (algebraMap (𝓞 L) (𝓞 F))

def IsMu {k : Type} [Field k] (r : 𝓞 F →+* k) (b : 𝓞 L)
    (μ : GLoc F J b →* (((F ≃ₐ[L] F) × J → k) ≃ₗ[k] ((F ≃ₐ[L] F) × J → k))) : Prop :=
  ∀ (g : GLoc F J b) x v, InLoc b x → RedV L r x v → RedV L r (g.1 x) (μ g v)

def IsBU (b : 𝓞 L) (α : Fˣ) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal → ordP P α = 0

def pol (κ : ℤ) (M : ℕ) : ℤ[X] := ∏ j ∈ Finset.range M, (X - C (κ ^ j))

def polE (κ : ℤ) (M E : ℕ) : ℤ[X] := ∏ j ∈ (Finset.range M).erase E, (X - C (κ ^ j))

def polAct (γ : F ≃ₐ[L] F) (p : ℤ[X]) (α : Fˣ) : Fˣ :=
  ∏ i ∈ Finset.range (p.natDegree + 1), actU (γ⁻¹ ^ i) α ^ p.coeff i

def Carries (L : Type) [Field L] [Algebra L F] [Fintype J] (q : ℕ) (ζ : (𝓞 F)ˣ) (χ : J → ZMod q)
    (𝔟 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) (δ : ZMod q → Fˣ) (g : GG L F J) : Prop :=
  (∀ x, InLat 0 x ↔ InLat 𝔟 (g x)) ∧
    ∃ (s : J → F ≃ₐ[L] F) (β : J → ZMod q) (g' : ∀ x, ({j // β j = x} → F) ≃ₗ[F] ({j // β j = x} → F)),
      BlockForm g s β g' ∧ (∀ j, actU (s j) (toF ζ) ^ (χ j).val = toF ζ ^ (β j).val) ∧
        ∀ x, LinearEquiv.det (g' x) = δ x

end UpperTheory.V.ZK.Cl

end
