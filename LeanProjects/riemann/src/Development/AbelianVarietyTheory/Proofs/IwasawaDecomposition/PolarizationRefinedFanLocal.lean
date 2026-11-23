import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSymmetricFormAlongDvr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizedFanTorsionRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalOrderBoundaryFormEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.CompletionDVR
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.MonoAlongTraits

theorem assoc_prod {W ι : Type} [CommMonoid W] (s : Finset ι) (x : ι → W) (ϖ : W) (n : ι → ℕ)
    (h : ∀ i, Associated (x i) (ϖ ^ n i)) : Associated (∏ i ∈ s, x i) (ϖ ^ ∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, pow_add]
    exact (h a).mul_mul ih

variable {R : Type} [CommRing R]

def numer {X : Type} [AddCommGroup X] {ι : Type} [Fintype ι] (b : ι → X) (r : X → R) (a : ι → ι → ℤ) : R :=
  ∏ i, ∏ j, r (b i + b j) ^ (a i j).toNat * (r (b i) * r (b j)) ^ (-a i j).toNat

def denom {X : Type} [AddCommGroup X] {ι : Type} [Fintype ι] (b : ι → X) (r : X → R) (a : ι → ι → ℤ) : R :=
  ∏ i, ∏ j, (r (b i) * r (b j)) ^ (a i j).toNat * r (b i + b j) ^ (-a i j).toNat

theorem orders {X : Type} [AddCommGroup X] {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ X) (r : X → R)
    (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (a : ι → ι → ℤ)
    (ha : ∀ i j, ℓ ((LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j)) = a i j)
    {W : Type} [CommRing W] (f : R →+* W) (ϖ : W) (be : LinearMap.BilinForm ℤ X) (hs : ∀ y z, be y z = be z y)
    (n : X → ℕ) (hn : ∀ y, be y y = 2 * n y) (hr : ∀ y, Associated (f (r y)) (ϖ ^ n y)) :
    ∃ M N : ℕ, Associated (f (denom b r a)) (ϖ ^ M) ∧ Associated (f (numer b r a)) (ϖ ^ N) ∧
      (N : ℤ) = M + ℓ be := by
  classical
  have hbe2 : ∀ y z, be y z = (n (y + z) : ℤ) - n y - n z := fun y z => by
    have h1 := hn (y + z)
    have h2 := hn y
    have h3 := hn z
    have h4 := hs y z
    simp only [map_add, LinearMap.add_apply] at h1
    linarith
  refine ⟨∑ i, ∑ j, ((n (b i) + n (b j)) * (a i j).toNat + n (b i + b j) * (-a i j).toNat),
    ∑ i, ∑ j, (n (b i + b j) * (a i j).toNat + (n (b i) + n (b j)) * (-a i j).toNat), ?_, ?_, ?_⟩
  · unfold denom
    simp only [map_prod, map_mul, map_pow]
    refine assoc_prod _ _ _ _ fun i => assoc_prod _ _ _ _ fun j => ?_
    have e : ϖ ^ ((n (b i) + n (b j)) * (a i j).toNat + n (b i + b j) * (-a i j).toNat) =
        (ϖ ^ n (b i) * ϖ ^ n (b j)) ^ (a i j).toNat * (ϖ ^ n (b i + b j)) ^ (-a i j).toNat := by ring
    rw [e]
    exact (((hr _).mul_mul (hr _)).pow_pow).mul_mul (hr _).pow_pow
  · unfold numer
    simp only [map_prod, map_mul, map_pow]
    refine assoc_prod _ _ _ _ fun i => assoc_prod _ _ _ _ fun j => ?_
    have e : ϖ ^ (n (b i + b j) * (a i j).toNat + (n (b i) + n (b j)) * (-a i j).toNat) =
        (ϖ ^ n (b i + b j)) ^ (a i j).toNat * (ϖ ^ n (b i) * ϖ ^ n (b j)) ^ (-a i j).toNat := by ring
    rw [e]
    exact ((hr _).pow_pow).mul_mul ((hr _).mul_mul (hr _)).pow_pow
  · have key : ∀ i j, ((n (b i + b j) * (a i j).toNat + (n (b i) + n (b j)) * (-a i j).toNat : ℕ) : ℤ) =
        (((n (b i) + n (b j)) * (a i j).toNat + n (b i + b j) * (-a i j).toNat : ℕ) : ℤ) +
          a i j * be (b i) (b j) := by
      intro i j
      have h := Int.toNat_sub_toNat_neg (a i j)
      rw [hbe2]
      push_cast
      linear_combination ((n (b i + b j) : ℤ) - n (b i) - n (b j)) * h
    rw [GlobalTheory.TorRef.ChartMono.ell_eq_sum b ℓ be]
    simp only [ha]
    simp only [Nat.cast_sum]
    simp only [key]
    simp only [Finset.sum_add_distrib]

theorem dvd_of_map {V Wc : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing Wc] [IsDomain Wc]
    (φ : V →+* Wc) {π : V} (hπ : Irreducible π) (hϖ : Irreducible (φ π)) {x y : V} (hx : x ≠ 0) {M N : ℕ}
    (hM : Associated (φ x) (φ π ^ M)) (hN : Associated (φ y) (φ π ^ N)) (hMN : M ≤ N) : x ∣ y := by
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  have hm : m = M := by
    apply GlobalTheory.TorRef.BalancedTrait.pow_eq_of_associated hϖ
    refine Associated.trans ?_ hM
    rw [map_mul, map_pow]
    exact (associated_unit_mul_left _ _ ((Units.isUnit u).map φ)).symm
  subst hm
  by_cases hy : y = 0
  · rw [hy]; exact dvd_zero _
  obtain ⟨m', u', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hπ
  have hm' : m' = N := by
    apply GlobalTheory.TorRef.BalancedTrait.pow_eq_of_associated hϖ
    refine Associated.trans ?_ hN
    rw [map_mul, map_pow]
    exact (associated_unit_mul_left _ _ ((Units.isUnit u').map φ)).symm
  subst hm'
  refine ⟨((u⁻¹ * u' : Vˣ) : V) * π ^ (m' - m), ?_⟩
  have e : π ^ m' = π ^ m * π ^ (m' - m) := by rw [← pow_add, Nat.add_sub_cancel' hMN]
  have hu : (u : V) * ((u⁻¹ : Vˣ) : V) = 1 := Units.mul_inv u
  rw [e, Units.val_mul]
  linear_combination (-((u' : V) * π ^ m * π ^ (m' - m))) * hu

end GlobalTheory.MonoAlongTraits

namespace GlobalTheory.MonoAlongTraits

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X : GMod Xo c) (d k g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (DX : EffCartierData X.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → HasCones (ConeZ E φs) X → X.N4 → IsPol (comb d (resInt _ φs) 0 φ) k X DX → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X.X) (t : SAB H (Sp R)), SABMap t X.t ξ → ∀ (P : PELUnif (maximalIdeal R) t) (k' : ℕ) (γ : Fin k' → LinearMap.BilinForm ℤ P.D.toPre.X), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso → ConeZ E φs P.D.toPre.X k' γ → InCone P.D.toPre γ → ∀ ℓ : LinearMap.BilinForm ℤ P.D.toPre.X →ₗ[ℤ] ℤ, (∀ β ∈ balForms H.bar P.D.toPre.X, (∀ y, 0 ≤ β y y) → GlobalTheory.ChartMono.InRealCone γ β → 0 ≤ ℓ β) → ∃ h : R, GlobalTheory.ChartMono.TraitMono P.D.toPre ℓ h := by
  intro E _ _ _ H D l Xo c X d k g φs 𝒩 φ DX hg hφs hRef hCones hN4 hPol R _ _ _ ξ t mξ P k' γ hCN hEt hFU hTI hCone hIn
    ℓ hℓ
  classical
  obtain ⟨hNoeth, hIC, -, hChar⟩ := hCN
  haveI := hNoeth
  haveI := hChar
  haveI := hIC
  let b := Module.Free.chooseBasis ℤ P.D.toPre.X
  let a : Module.Free.ChooseBasisIndex ℤ P.D.toPre.X → Module.Free.ChooseBasisIndex ℤ P.D.toPre.X → ℤ :=
    fun i j => ℓ ((LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j))
  choose r hr using fun χ : P.D.toPre.X =>
    (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff P.D.toPre χ).2 (GlobalTheory.PeriodFormCompare.psiIn_top P.D χ)
  have hr0 : ∀ χ, r χ ≠ 0 := fun χ => GlobalTheory.PsiCoordLocal.ne_zero_of_coord (hr χ)
  have hord : ∀ (W : Type) [CommRing W] (f : R →+* W) (ϖ : W) (be : LinearMap.BilinForm ℤ P.D.toPre.X),
      (∀ y z, be y z = be z y) → FormAt P.D.toPre f ϖ be →
      ∃ M N : ℕ, Associated (f (denom b r a)) (ϖ ^ M) ∧ Associated (f (numer b r a)) (ϖ ^ N) ∧
        (N : ℤ) = M + ℓ be := by
    intro W _ f ϖ be hs hF
    choose r' n hr' hn has using hF
    refine orders b r ℓ a (fun _ _ => rfl) f ϖ be hs n hn fun y => ?_
    obtain ⟨u, hu⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord (hr y) (hr' y)
    refine Associated.trans ?_ (has y)
    rw [hu, map_mul]
    exact (associated_unit_mul_left (f (r y)) (f u) ((Units.isUnit u).map f)).symm
  have hden0 : denom b r a ≠ 0 := by
    unfold denom
    exact Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ =>
      mul_ne_zero (pow_ne_zero _ (mul_ne_zero (hr0 _) (hr0 _))) (pow_ne_zero _ (hr0 _))
  have hx0 : algebraMap R (FractionRing R) (denom b r a) ≠ 0 := fun e =>
    hden0 (IsFractionRing.injective R (FractionRing R) (e.trans (map_zero _).symm))
  obtain ⟨h, hh⟩ : ∃ h : R, algebraMap R (FractionRing R) h =
      algebraMap R (FractionRing R) (numer b r a) / algebraMap R (FractionRing R) (denom b r a) := by
    refine GlobalTheory.exists_algebraMap_eq_of_forall_discreteValuationSubring (R := R) (K := FractionRing R)
      fun V hV hRV _ => ?_
    haveI := hV
    let g0 : R →+* V := (algebraMap R (FractionRing R)).codRestrict V hRV
    have hg0 : Function.Injective g0 := fun x y e =>
      IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val e)
    let f : R →+* AdicCompletion (maximalIdeal V) V := (algebraMap V (AdicCompletion (maximalIdeal V) V)).comp g0
    have hf : Function.Injective f := (GlobalTheory.algebraMap_adicCompletion_injective_of_dvr V).comp hg0
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
    have hϖ : Irreducible (algebraMap V (AdicCompletion (maximalIdeal V) V) π) :=
      GlobalTheory.irreducible_algebraMap_adicCompletion_of_dvr hπ
    haveI : CharZero (AdicCompletion (maximalIdeal V) V) := charZero_of_injective_ringHom hf
    have hW : CDvr (AdicCompletion (maximalIdeal V) V) :=
      ⟨inferInstance, (ReciprocityTheory.CA.Pt.completionDVR V).2.1, inferInstance⟩
    obtain ⟨be, hs, hF⟩ := GlobalTheory.PreValForm.main R hIC P.D _ f hf _ hϖ
    have hbal : be ∈ balForms H.bar P.D.toPre.X := by
      letI := H.starRing
      exact ⟨hs, fun x y z => GlobalTheory.TorRef.BalancedTrait.smul_left P.D.toPre P.oD hϖ f be hs hF x y z⟩
    have hpsd : ∀ y, 0 ≤ be y y := fun y => by
      obtain ⟨r₁, n₁, -, h₁, -⟩ := hF y
      rw [h₁]; positivity
    have hcone : GlobalTheory.ChartMono.InRealCone γ be := hIn _ hW _ hϖ f be hs hF
    have h0 := hℓ be hbal hpsd hcone
    obtain ⟨M, N, hM, hN, hMN⟩ := hord _ f _ be hs hF
    have hle : M ≤ N := by omega
    have hxy : g0 (denom b r a) ∣ g0 (numer b r a) :=
      dvd_of_map (algebraMap V (AdicCompletion (maximalIdeal V) V)) hπ hϖ
        (fun e => hden0 (hg0 (e.trans (map_zero g0).symm))) hM hN hle
    obtain ⟨cc, hc⟩ := hxy
    have h2 : ((g0 (numer b r a) : V) : FractionRing R) = ((g0 (denom b r a) * cc : V) : FractionRing R) :=
      congrArg Subtype.val hc
    have e : algebraMap R (FractionRing R) (numer b r a) / algebraMap R (FractionRing R) (denom b r a) =
        (cc : FractionRing R) := by
      rw [div_eq_iff hx0]
      rw [MulMemClass.coe_mul] at h2
      exact h2.trans (mul_comm _ _)
    rw [e]
    exact cc.2
  have hmul : h * denom b r a = numer b r a := IsFractionRing.injective R (FractionRing R) (by
    rw [map_mul, hh, div_mul_cancel₀ _ hx0])
  refine ⟨h, ?_⟩
  intro W _ _ _ hW ϖ hϖ f be hs hF kk hk
  obtain ⟨M, N, hM, hN, hMN⟩ := hord W f ϖ be hs hF
  have hN' : N = M + kk := by
    have : (N : ℤ) = M + kk := by rw [hMN, hk]
    exact_mod_cast this
  have h1 : Associated (f h * f (denom b r a)) (ϖ ^ kk * ϖ ^ M) := by
    rw [← map_mul, hmul, ← pow_add, add_comm, ← hN']
    exact hN
  exact h1.of_mul_right hM (hM.ne_zero_iff.2 (pow_ne_zero _ hϖ.ne_zero))

end GlobalTheory.MonoAlongTraits
