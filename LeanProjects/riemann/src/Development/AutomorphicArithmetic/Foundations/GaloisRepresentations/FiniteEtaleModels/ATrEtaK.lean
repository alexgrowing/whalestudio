import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.GalOfKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntIntCast

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.trEtaK_holds :
    TrEtaK := by
  intro p _ D G L R _ _ gb h X s M₁ M₂ o' o ψ hT n κ c₁ c₂ hM1 hM2 x y hxy
  obtain ⟨v, hv, hxv⟩ := hxy
  haveI : IsMonHom ψ := hT.1
  obtain ⟨hM13, hM1c⟩ := M₁.2
  obtain ⟨hM23, hM2c⟩ := M₂.2
  have hne1 : (M₁ : ℕ) ≠ 0 := by omega
  have hne2 : (M₂ : ℕ) ≠ 0 := by omega
  have hne1' := hne1
  have hne2' := hne2
  rw [hM1] at hne1 hM1c
  rw [hM2] at hne2 hM2c
  have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h0 => hne2 (by simp [h0]))
  have hκ0 : 0 < κ := Nat.pos_of_ne_zero (fun h0 => hne1 (by simp [h0]))
  have hc10 : 0 < c₁ := Nat.pos_of_ne_zero (fun h0 => hne1 (by simp [h0]))
  have hc20 : 0 < c₂ := Nat.pos_of_ne_zero (fun h0 => hne2 (by simp [h0]))
  have hnc : n.Coprime p := Nat.Coprime.coprime_dvd_left ⟨c₂, rfl⟩ hM2c
  have hnκc : (n * κ).Coprime p := Nat.Coprime.coprime_dvd_left ⟨c₁, rfl⟩ hM1c
  have hpc : ∀ (f : 𝟙_ (Over X) ⟶ o'.A) (k : ℕ), (f ^ k) ≫ ψ = (f ≫ ψ) ^ k := by
    intro f k
    induction k with
    | zero => rw [_root_.pow_zero, _root_.pow_zero, MonObj.one_comp]
    | succ k ih => rw [_root_.pow_succ, _root_.pow_succ, MonObj.mul_comp, ih]
  set a := o'.eta (c₁ • x) ≫ ψ with ha
  set b := o.eta (c₂ • y) with hb
  have haN : a ^ (M₁ : ℕ) = 1 := by
    rw [ha, ← hpc]
    exact (congrArg (· ≫ ψ) ((GObj.eta_nsmul o' _ _).symm.trans (GObj.eta_ker o' _))).trans
      (MonObj.one_comp ψ)
  have hbN : b ^ (M₂ : ℕ) = 1 := (GObj.eta_nsmul o _ _).symm.trans (GObj.eta_ker o _)
  have hunit : IsUnit (((M₁ : ℕ) * (M₂ : ℕ) : ℕ) : Γ(X, ⊤)) := by
    have hR : IsUnit (((M₁ : ℕ) * (M₂ : ℕ) : ℕ) : R) := by
      rw [← map_natCast (algebraMap ℚ R)]
      refine IsUnit.map (algebraMap ℚ R) (IsUnit.mk0 _ ?_)
      exact_mod_cast Nat.mul_ne_zero hne1' hne2'
    have := hR.map ((s.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    simpa using this
  rw [← _root_.mul_inv_eq_one]
  have hpow : (a * b⁻¹) ^ ((M₁ : ℕ) * (M₂ : ℕ)) = 1 := by
    rw [mul_pow, _root_.inv_pow, _root_.pow_mul, haN, _root_.mul_comm (M₁ : ℕ), _root_.pow_mul, hbN,
      _root_.one_pow, _root_.one_pow, inv_one, _root_.mul_one]
  have := GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points X o.A o.ab _ hunit _ (a * b⁻¹) hpow 1 ?_
  · simpa using this
  intro k _ _ ξ
  rw [_root_.pow_one, MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_inv_eq_one]
  rw [show Over.homMk ξ _ = toUnit (Over.mk (ξ ≫ (𝟙_ (Over X)).hom)) from Subsingleton.elim _ _]
  obtain ⟨β, hβ⟩ := GlobalTheory.UPel.HT.GenCmp.exists_spMap ((ξ ≫ (𝟙_ (Over X)).hom) ≫ s)
  obtain ⟨I', I'', h1, h2, hev⟩ := hT.2.2.2.2 k (ξ ≫ (𝟙_ (Over X)).hom) β hβ
  have e1 : I'.ev (M₁ : ℕ) (c₁ • x) = I'.ev (n * κ) x :=
    (KerBy.ev_nsmul _ (I'.add _) c₁ x).trans
      ((congrArg (fun m => I'.ev m x ^ c₁) hM1).trans (I'.tower (n * κ) c₁ (Nat.mul_pos hn0 hκ0) hc10 x))
  have e2 : I''.ev (M₂ : ℕ) (c₂ • y) = I''.ev n y :=
    (KerBy.ev_nsmul _ (I''.add _) c₂ y).trans
      ((congrArg (fun m => I''.ev m y ^ c₂) hM2).trans (I''.tower n c₂ hn0 hc20 y))
  have e3 : I''.ev (n * κ) (κ • y) = I''.ev n y :=
    (KerBy.ev_nsmul _ (I''.add _) κ y).trans (I''.tower n κ hn0 hκ0 y)
  have e4 : I'.ev (n * κ) x ≫ ψ = I''.ev (n * κ) (κ • y) :=
    (hev (n * κ) (Nat.mul_pos hn0 hκ0) hnκc x (κ • y)).mpr
      ⟨v, hv, by rw [GlobalTheory.HeckeApprox.inAf_nsmul]; exact hxv⟩
  rw [ha, hb, ← Category.assoc]
  exact (congrArg (· ≫ ψ) ((h1 _).trans e1)).trans (e4.trans (e3.trans (e2.symm.trans (h2 _).symm)))
