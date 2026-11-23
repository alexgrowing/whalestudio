import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroTypeInertia
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def Narrow : Prop :=
  ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E'] [Algebra E Ω]
    [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 → normV w' = g ^ n →
    ∀ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' →
    ∀ (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K), Function.Surjective red →
      RingHom.ker red = w'.asIdeal →
    ∀ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ →
    ∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character →
      (∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
        τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) →
    ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
      ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        (rc (cls σ)).inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((θ (z ^ g ^ j) : ℂˣ) : ℂ))

theorem narrow_of_field (H : GlobalTheory.Published.DepthZeroTypeInertia) : Narrow :=
  fun E E' Ω _ _ _ _ _ _ _ _ _ _ _ g _ A w h w' h' rc hrc i hi n hn hg hN a' ha' K _ _ red hr hk θ hθ τ hτ hf σ hs =>
    (H E E' Ω g A w h w' h' rc hrc i hi n hn hg hN a' ha' K red hr hk θ hθ τ hτ hf σ hs).2

def LCusp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → ∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character →
    ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ → (cls σ).IsCusp

def LDepth : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, ∀ τ : FDRep ℂ (Gn g n),
    ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
      fixed (cls σ).rep (KOne (w.adicCompletion E) (Fin (cls σ).1)) ≠ ⊥

def LTame : Prop :=
  ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E'] [Algebra E Ω]
    [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 → normV w' = g ^ n →
    ∀ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' →
    ∀ (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K), Function.Surjective red →
      RingHom.ker red = w'.asIdeal →
    ∀ y : WD h, IsIrrWD y → IsTameWD y → y.lpDim = n →
    ∃ ξ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n ξ ∧
      ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        y.inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((ξ (z ^ g ^ j) : ℂˣ) : ℂ))

def LMatch : Prop :=
  ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E'] [Algebra E Ω]
    [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 → normV w' = g ^ n →
    ∀ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' →
    ∀ (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K), Function.Surjective red →
      RingHom.ker red = w'.asIdeal →
    ∀ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ →
    ∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character →
      (∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
        τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) →
    ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
    ∀ ξ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n ξ →
      (∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        (rc (cls σ)).inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((ξ (z ^ g ^ j) : ℂˣ) : ℂ))) →
      ∃ k : ℕ, ∀ z : Kˣ, ξ z = θ (z ^ g ^ k)

theorem prod_shift (f : ℕ → ℂ) (n : ℕ) (hf : ∀ j, f (j + n) = f j) (k : ℕ) :
    ∏ j ∈ Finset.range n, (X - C (f (j + k))) = ∏ j ∈ Finset.range n, (X - C (f j)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← ih]
    have h1 := Finset.prod_range_succ' (fun j => (X - C (f (j + k)) : ℂ[X])) n
    have h2 := Finset.prod_range_succ (fun j => (X - C (f (j + k)) : ℂ[X])) n
    have hper : f (n + k) = f (0 + k) := by rw [Nat.add_comm n k, hf, Nat.zero_add]
    rw [h2, hper] at h1
    have hne : (X - C (f (0 + k)) : ℂ[X]) ≠ 0 := X_sub_C_ne_zero _
    have h3 := mul_right_cancel₀ hne h1
    rw [h3]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Nat.add_right_comm, Nat.add_assoc]

theorem pow_card_units {E' : Type} [Field E'] [NumberField E'] (w' : HeightOneSpectrum (𝓞 E')) (g n : ℕ)
    (hN : normV w' = g ^ n) (K : Type) [Field K] (red : 𝓞 E' →+* K) (hr : Function.Surjective red)
    (hk : RingHom.ker red = w'.asIdeal) (hpos : 0 < g ^ n) (z : Kˣ) : z ^ g ^ n = z := by
  have e : (𝓞 E' ⧸ w'.asIdeal) ≃+* K :=
    (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hr)
  have hc : Nat.card K = g ^ n := by rw [← hN, normV, Nat.card_congr e.toEquiv]
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hc]; exact hpos.ne')
  letI := Fintype.ofFinite K
  have hcard : Fintype.card K = g ^ n := by rw [← Nat.card_eq_fintype_card, hc]
  ext
  rw [Units.val_pow_eq_pow_val, ← hcard, FiniteField.pow_card]

theorem narrow_of_leaves (H1 : LCusp) (H2 : LDepth) (H3 : LTame) (H4 : LMatch) : Narrow := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ _ _ g _ A w h w' h' rc hrc i hi n hn hg hN a' ha' K _ _ red hr hk θ hθ τ hτ hf σ hs
    t x z hxz hv
  obtain ⟨a, ha, ε, hε, hL⟩ := hrc
  have hrc' : IsRec h rc := ⟨a, ha, ε, hε, hL⟩
  have hc : IsIrrWD (rc (cls σ)) := (hL.cusp _).1 (H1 E w g i hi n hn τ hτ σ hs)
  have ht : IsTameWD (rc (cls σ)) := (hL.depth _).1 (H2 E w g i hi n τ σ hs)
  have hd : (rc (cls σ)).lpDim = n := hL.dim _
  obtain ⟨ξ, hξ, hξf⟩ := H3 E E' Ω g A w h w' h' i hi n hn hg hN a' ha' K red hr hk (rc (cls σ)) hc ht hd
  obtain ⟨k, hk'⟩ := H4 E E' Ω g A w h w' h' rc hrc' i hi n hn hg hN a' ha' K red hr hk θ hθ τ hτ hf σ hs ξ hξ hξf
  rw [hξf t x z hxz hv]
  have hpos : 0 < g ^ n := pow_pos (Fact.out : g.Prime).pos n
  have hz := pow_card_units w' g n hN K red hr hk hpos z
  have e1 : ∀ j, ((ξ (z ^ g ^ j) : ℂˣ) : ℂ) = ((θ (z ^ g ^ (j + k)) : ℂˣ) : ℂ) := fun j => by
    rw [hk', ← pow_mul, ← pow_add]
  simp_rw [e1]
  refine prod_shift (fun j => ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) n (fun j => ?_) k
  show ((θ (z ^ g ^ (j + n)) : ℂˣ) : ℂ) = ((θ (z ^ g ^ j) : ℂˣ) : ℂ)
  rw [pow_add, mul_comm, pow_mul, hz]

end DiscreteGroups.sglob.DzType
