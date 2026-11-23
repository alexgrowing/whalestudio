import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelFormAlongDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCdvrMkLeContinuum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegKrull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationAtPrimeIsDiscreteValuationRingOfHeig

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.TorRef.ChartHFun

variable {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

def elemForm {ι : Type} (b : Module.Basis ι ℤ X) (i j : ι) : LinearMap.BilinForm ℤ X :=
  (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j)

theorem linForm_eq_sum {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ X)
    (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (be : LinearMap.BilinForm ℤ X) :
    ℓ be = ∑ i, ∑ j, ℓ (elemForm b i j) * be (b i) (b j) := by
  have hbe : be = ∑ i, ∑ j, be (b i) (b j) • elemForm b i j := by
    refine LinearMap.ext_basis b b fun k l => ?_
    simp [elemForm, Finsupp.single_apply, Finset.sum_apply, LinearMap.sum_apply]
  conv_lhs => rw [hbe]
  simp only [map_sum, map_zsmul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

end GlobalTheory.TorRef.ChartHFun

namespace GlobalTheory.TorRef.ChartHFun

section Trait

variable {R : Type} [CommRing R] [IsDomain R] (Dg : DegPre R)

def numF {ι : Type} [Fintype ι] (r : Dg.X → R) (b : Module.Basis ι ℤ Dg.X) (c : ι → ι → ℤ) : R :=
  ∏ i, ∏ j, r (b i + b j) ^ (c i j).toNat * (r (b i) * r (b j)) ^ (-c i j).toNat

def denF {ι : Type} [Fintype ι] (r : Dg.X → R) (b : Module.Basis ι ℤ Dg.X) (c : ι → ι → ℤ) : R :=
  ∏ i, ∏ j, (r (b i) * r (b j)) ^ (c i j).toNat * r (b i + b j) ^ (-c i j).toNat

variable {Dg}

theorem coord_assoc {W : Type} [CommRing W] {g : R →+* W} {ϖ : W} {be : LinearMap.BilinForm ℤ Dg.X}
    (hF : FormAt Dg g ϖ be) {y : Dg.X} {s : R} (hs : PsiCoord Dg y s) :
    Associated (g s) (ϖ ^ (be y y / 2).toNat) ∧ be y y = 2 * ((be y y / 2).toNat : ℤ) := by
  obtain ⟨r', n, hr', hn, ha⟩ := hF y
  obtain ⟨u, hu⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord hr' hs
  have hn' : (be y y / 2).toNat = n := by rw [hn]; omega
  rw [hn']
  refine ⟨?_, hn⟩
  rw [hu, map_mul]
  exact (associated_unit_mul_left (g r') (g u) ((Units.map g.toMonoidHom u).isUnit)).trans ha

theorem trait_num_den {ι : Type} [Fintype ι] (r : Dg.X → R) (hr : ∀ y, PsiCoord Dg y (r y))
    (b : Module.Basis ι ℤ Dg.X) (c : ι → ι → ℤ) {W : Type} [CommRing W] {g : R →+* W} {ϖ : W}
    {be : LinearMap.BilinForm ℤ Dg.X} (hsymm : ∀ y z, be y z = be z y) (hF : FormAt Dg g ϖ be) :
    ∃ m d : ℕ, Associated (g (numF Dg r b c)) (ϖ ^ m) ∧ Associated (g (denF Dg r b c)) (ϖ ^ d) ∧
      (m : ℤ) - d = ∑ i, ∑ j, c i j * be (b i) (b j) := by
  set n : Dg.X → ℕ := fun y => (be y y / 2).toNat with hn
  have hA : ∀ y, Associated (g (r y)) (ϖ ^ n y) := fun y => (coord_assoc hF (hr y)).1
  have hN : ∀ y, be y y = 2 * (n y : ℤ) := fun y => (coord_assoc hF (hr y)).2
  refine ⟨∑ i, ∑ j, ((c i j).toNat * n (b i + b j) + (-c i j).toNat * (n (b i) + n (b j))),
    ∑ i, ∑ j, ((c i j).toNat * (n (b i) + n (b j)) + (-c i j).toNat * n (b i + b j)), ?_, ?_, ?_⟩
  · simp only [numF, map_prod, map_mul, map_pow, ← Finset.prod_pow_eq_pow_sum]
    refine Associated.prod _ _ _ fun i _ => Associated.prod _ _ _ fun j _ => ?_
    have := ((hA (b i + b j)).pow_pow (n := (c i j).toNat)).mul_mul
      (((hA (b i)).mul_mul (hA (b j))).pow_pow (n := (-c i j).toNat))
    convert this using 1
    ring
  · simp only [denF, map_prod, map_mul, map_pow, ← Finset.prod_pow_eq_pow_sum]
    refine Associated.prod _ _ _ fun i _ => Associated.prod _ _ _ fun j _ => ?_
    have := (((hA (b i)).mul_mul (hA (b j))).pow_pow (n := (c i j).toNat)).mul_mul
      ((hA (b i + b j)).pow_pow (n := (-c i j).toNat))
    convert this using 1
    ring
  · push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 := hN (b i + b j)
    have h2 := hN (b i)
    have h3 := hN (b j)
    have h4 := hsymm (b j) (b i)
    simp only [map_add, LinearMap.add_apply] at h1
    have he : (n (b i + b j) : ℤ) - n (b i) - n (b j) = be (b i) (b j) := by linarith
    have hc : ((c i j).toNat : ℤ) - ((-c i j).toNat : ℤ) = c i j := by omega
    calc _ = (((c i j).toNat : ℤ) - ((-c i j).toNat : ℤ)) * ((n (b i + b j) : ℤ) - n (b i) - n (b j)) := by ring
      _ = _ := by rw [hc, he]

end Trait

end GlobalTheory.TorRef.ChartHFun

namespace GlobalTheory.TorRef.ChartHFun

theorem dvd_of_map_dvd {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    (i : A →+* B) (hi : Function.Injective i) [IsLocalHom i] {a b : A} (h : i b ∣ i a) : b ∣ a := by
  rcases ValuationRing.dvd_total a b with ⟨w, hw⟩ | hba
  · by_cases ha : a = 0
    · rw [ha]; exact dvd_zero _
    obtain ⟨z, hz⟩ := h
    have hia : i a ≠ 0 := (map_ne_zero_iff i hi).2 ha
    have h1 : i a * 1 = i a * (i w * z) := by
      rw [mul_one, ← mul_assoc, ← map_mul, ← hw]; exact hz
    have hu : IsUnit (i w) := IsUnit.of_mul_eq_one z (mul_left_cancel₀ hia h1).symm
    have hw' : IsUnit w := isUnit_of_map_unit i w hu
    rw [hw]
    exact (associated_mul_unit_right a w hw').symm.dvd
  · exact hba

end GlobalTheory.TorRef.ChartHFun

namespace GlobalTheory.TorRef.ChartHFun

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] [IsDomain R]
  [IsLocalRing R]

theorem exists_mul_den_eq_num (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) {m : ℕ}
    (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X) (ℓ : LinearMap.BilinForm ℤ P.D.toPre.X →ₗ[ℤ] ℤ) (hCN : IsCN R)
    (hIn : InCone P.D.toPre γ)
    (hpos : ∀ be : LinearMap.BilinForm ℤ P.D.toPre.X, (∀ y z, be y z = be z y) → ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) →
      toReal be = ∑ i, c i • toReal (γ i) → 0 ≤ ℓ be)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ P.D.toPre.X) (r : P.D.toPre.X → R)
    (hr : ∀ y, PsiCoord P.D.toPre y (r y) ∧ r y ≠ 0) :
    ∃ h : R, h * denF P.D.toPre r b (fun i j => ℓ (elemForm b i j)) = numF P.D.toPre r b (fun i j => ℓ (elemForm b i j)) := by
  obtain ⟨hNoeth, hIC, hcpl, hch⟩ := id hCN
  haveI := hNoeth
  haveI := hIC
  haveI := hch
  set c : ι → ι → ℤ := fun i j => ℓ (elemForm b i j) with hc
  set num := numF P.D.toPre r b c
  set den := denF P.D.toPre r b c
  have hden : den ≠ 0 := by
    simp only [den, denF, Finset.prod_ne_zero_iff]
    intro i _ j _
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (hr _).2 (hr _).2)) (pow_ne_zero _ (hr _).2)
  let K := FractionRing R
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hdenK : algebraMap R K den ≠ 0 := (map_ne_zero_iff _ hinjK).2 hden
  suffices hloc : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      ∃ a s : R, s ∉ p ∧ algebraMap R K num / algebraMap R K den * algebraMap R K s = algebraMap R K a by
    obtain ⟨h, hh⟩ := ReciprocityTheory.ChartRestriction.G.T0.mem_of_mem_heightOne_localizations (R := R) (K := K)
      (algebraMap R K num / algebraMap R K den) hloc
    refine ⟨h, hinjK ?_⟩
    rw [map_mul, hh, div_mul_cancel₀ _ hdenK]
  intro p hp hp1
  haveI := hp
  let Rp := Localization.AtPrime p
  haveI : IsDiscreteValuationRing Rp := GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one R p hp1
  have hinjp : Function.Injective (algebraMap R Rp) :=
    IsLocalization.injective Rp (Ideal.primeCompl_le_nonZeroDivisors p)
  haveI : CharZero Rp := charZero_of_injective_algebraMap hinjp
  let T := GlobalTheory.CountableCompletion.completionCDVR Rp
  let i : Rp →+* T.V := algebraMap Rp (AdicCompletion (maximalIdeal Rp) Rp)
  have hi : Function.Injective i := GlobalTheory.algebraMap_adicCompletion_injective_of_dvr Rp
  haveI : IsLocalHom i := (inferInstance : IsLocalHom (algebraMap Rp (AdicCompletion (maximalIdeal Rp) Rp)))
  have hCD : CDvr T.V := ⟨T.dvr, T.cpl, T.ch0⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  let ψ : R →+* T.V := i.comp (algebraMap R Rp)
  have hψ : Function.Injective ψ := hi.comp hinjp
  have hgi : Function.Injective ((algebraMap T.V (FractionRing T.V)).comp ψ) :=
    (IsFractionRing.injective T.V (FractionRing T.V)).comp hψ
  obtain ⟨be, hbeL, hF⟩ := GlobalTheory.ChartForm.exists_balanced_formAt E H R t P hCN T.V hCD ϖ hϖ ψ
    (IsFractionRing.lift hgi) (fun x => IsFractionRing.lift_algebraMap hgi x)
  have hsymm := (mem_levelForms.1 hbeL).1
  obtain ⟨cc, hcc0, hcc⟩ := hIn T.V hCD ϖ hϖ ψ be hsymm hF
  have hl := hpos be hsymm cc hcc0 hcc
  obtain ⟨m', d, hm, hd, hmd⟩ := trait_num_den r (fun y => (hr y).1) b c hsymm hF
  have hlin : ∑ i, ∑ j, c i j * be (b i) (b j) = ℓ be := (linForm_eq_sum b ℓ be).symm
  have hdm : d ≤ m' := by
    have : (0 : ℤ) ≤ (m' : ℤ) - d := by rw [hmd, hlin]; exact hl
    omega
  have hdiv : ψ den ∣ ψ num := (hd.dvd_iff_dvd_left).2 ((pow_dvd_pow ϖ hdm).trans hm.symm.dvd)
  obtain ⟨z, hz⟩ := dvd_of_map_dvd i hi hdiv
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
  refine ⟨a, s, s.2, ?_⟩
  have key : num * s = den * a := by
    apply hinjp
    rw [map_mul, map_mul, hz, mul_assoc, IsLocalization.mk'_spec]
  rw [div_mul_eq_mul_div, div_eq_iff hdenK, ← map_mul, ← map_mul, key, mul_comm]

end GlobalTheory.TorRef.ChartHFun

namespace GlobalTheory.TorRef

open ChartHFun in

theorem exists_monomial_order_linForm : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X) (ℓ : LinearMap.BilinForm ℤ P.D.toPre.X →ₗ[ℤ] ℤ), IsCN R → P.TorsionIso → InCone P.D.toPre γ → (∀ be : LinearMap.BilinForm ℤ P.D.toPre.X, (∀ y z, be y z = be z y) → ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal be = ∑ i, c i • toReal (γ i) → 0 ≤ ℓ be) → ∃ h : R, h ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (g : R →+* W) (be : LinearMap.BilinForm ℤ P.D.toPre.X), (∀ y z, be y z = be z y) → FormAt P.D.toPre g ϖ be → ∃ n : ℕ, (n : ℤ) = ℓ be ∧ Associated (g h) (ϖ ^ n) := by
  intro E _ _ _ H R _ _ _ t P m γ ℓ hCN _ hIn hpos
  haveI : CharZero R := hCN.2.2.2
  classical
  let b := Module.Free.chooseBasis ℤ P.D.toPre.X
  choose r hr using fun y => (GlobalTheory.PsiCoordLocal.main R P.D hCN.2.1 y).1
  set c : _ → _ → ℤ := fun i j => ℓ (elemForm b i j) with hc
  obtain ⟨h, hh⟩ := exists_mul_den_eq_num t P γ ℓ hCN hIn hpos b r (fun y => ⟨(hr y).1, (hr y).2.1⟩)
  refine ⟨h, ?_, ?_⟩
  · intro h0
    rw [h0, zero_mul] at hh
    have hnum : numF P.D.toPre r b c ≠ 0 := by
      simp only [numF, Finset.prod_ne_zero_iff]
      intro i _ j _
      exact mul_ne_zero (pow_ne_zero _ (hr _).2.1) (pow_ne_zero _ (mul_ne_zero (hr _).2.1 (hr _).2.1))
    exact hnum hh.symm
  · intro W _ _ _ hW ϖ hϖ g be hsymm hF
    obtain ⟨cc, hcc0, hcc⟩ := hIn W hW ϖ hϖ g be hsymm hF
    have hl := hpos be hsymm cc hcc0 hcc
    obtain ⟨m', d, hm, hd, hmd⟩ := trait_num_den r (fun y => (hr y).1) b c hsymm hF
    have hlin : ∑ i, ∑ j, c i j * be (b i) (b j) = ℓ be := (linForm_eq_sum b ℓ be).symm
    have hdm : d ≤ m' := by
      have : (0 : ℤ) ≤ (m' : ℤ) - d := by rw [hmd, hlin]; exact hl
      omega
    refine ⟨m' - d, by rw [Nat.cast_sub hdm, hmd, hlin], ?_⟩
    have h1 : Associated (g h * g (denF P.D.toPre r b c)) (ϖ ^ (m' - d) * ϖ ^ d) := by
      rw [← map_mul, hh, ← pow_add, Nat.sub_add_cancel hdm]
      exact hm
    exact h1.of_mul_right hd (hd.ne_zero_iff.2 (pow_ne_zero _ hϖ.ne_zero))

end GlobalTheory.TorRef
