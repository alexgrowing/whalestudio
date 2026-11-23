import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasPolChartOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalPolChartsKS
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormalisedPolarisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HilbertFunctionEndomorphismGraphOfTorsionAction
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AdjPolLocal
open GlobalTheory.MulPull GlobalTheory.PrimNorm GlobalTheory.PrimNormPol

theorem commGroup_sixTerm_relation_to_zpow_form {G : Type} [CommGroup G] {p q r s t u o : G}
    (h : p * q⁻¹ * r⁻¹ * o = s * t⁻¹ * u⁻¹ * o) :
    p ^ (1 : ℤ) * (q ^ (-1 : ℤ) * (r ^ (-1 : ℤ) * (s ^ (-1 : ℤ) * (t ^ (1 : ℤ) * u ^ (1 : ℤ))))) = 1 := by
  have h' := mul_right_cancel h
  have e : p ^ (1 : ℤ) * (q ^ (-1 : ℤ) * (r ^ (-1 : ℤ) * (s ^ (-1 : ℤ) * (t ^ (1 : ℤ) * u ^ (1 : ℤ))))) =
      (p * q⁻¹ * r⁻¹) * (s * t⁻¹ * u⁻¹)⁻¹ := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  rw [e, h', mul_inv_cancel]

theorem commGroup_sixTerm_zpow_form_to_relation {G : Type} [CommGroup G] {p q r s t u o : G}
    (h : p ^ (1 : ℤ) * (q ^ (-1 : ℤ) * (r ^ (-1 : ℤ) * (s ^ (-1 : ℤ) * (t ^ (1 : ℤ) * u ^ (1 : ℤ))))) = 1) :
    p * q⁻¹ * r⁻¹ * o = s * t⁻¹ * u⁻¹ * o := by
  congr 1
  have e : p ^ (1 : ℤ) * (q ^ (-1 : ℤ) * (r ^ (-1 : ℤ) * (s ^ (-1 : ℤ) * (t ^ (1 : ℤ) * u ^ (1 : ℤ))))) =
      (p * q⁻¹ * r⁻¹) * (s * t⁻¹ * u⁻¹)⁻¹ := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  rw [e, mul_inv_eq_one] at h
  exact h

theorem le_val_one_add_pow_sub {G : Type} [CommGroup G] {D a b : G} (h : 1 = D * (1 * a⁻¹ * b⁻¹ * 1)) : D = a * b := by
  rw [_root_.one_mul, _root_.mul_one, eq_comm, ← mul_inv, mul_inv_eq_one] at h
  exact h

theorem lbIso_of_rosatiAdj_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (M : LB B.left) (f g : B ⟶ B), M.IsLB → RosatiAdj B M f g → LBIso (cubeLB B ![fst B B ≫ f, snd B B] M) (cubeLB B ![fst B B, snd B B ≫ g] M) := by
  intro R _ _ B _ _ M f g hM h
  obtain ⟨U, hU, t, ht⟩ := h (closedPoint R)
  have hall : ∀ p : Sp R, p ∈ U := fun p =>
    Specializes.mem_open ((PrimeSpectrum.le_iff_specializes p (closedPoint R)).1
      (le_maximalIdeal p.2.ne_top)) U.isOpen hU
  have H : KerPow.HasGen M (rosatiφ B f g) rosatiε :=
    KerPow.HasGen.of_range (W := (B ⊗ B).hom ⁻¹ᵁ U) ⟨t, ht⟩ (𝟙 _) (fun y => hall _) (fun k => Category.id_comp _)
  have h6 := (hasGen_iff hM _ _).1 H
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, rosatiφ, rosatiε] at h6
  have ea : (padd B (fst B B ≫ f) (snd B B)).left = ((fst B B ≫ f) * snd B B).left := rfl
  have eb : (padd B (fst B B) (snd B B ≫ g)).left = (fst B B * (snd B B ≫ g)).left := rfl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, ea, eb, _root_.mul_one] at h6
  refine (lbIso_iff hM _ _ _ _).2 ?_
  rw [prod_square_id, prod_square_id]
  simp only [diff₂]
  exact commGroup_sixTerm_zpow_form_to_relation h6

theorem rosatiAdj_of_lbIso : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (M : LB B.left) (f g : B ⟶ B), M.IsLB → LBIso (cubeLB B ![fst B B ≫ f, snd B B] M) (cubeLB B ![fst B B, snd B B ≫ g] M) → RosatiAdj B M f g := by
  intro S B _ _ M f g hM h
  have h1 := (lbIso_iff hM _ _ _ _).1 h
  rw [prod_square_id, prod_square_id] at h1
  have H : KerPow.HasGen M (rosatiφ B f g) rosatiε := by
    refine (hasGen_iff hM _ _).2 ?_
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, rosatiφ, rosatiε]
    simp only [diff₂] at h1
    have ea : (padd B (fst B B ≫ f) (snd B B)).left = ((fst B B ≫ f) * snd B B).left := rfl
    have eb : (padd B (fst B B) (snd B B ≫ g)).left = (fst B B * (snd B B ≫ g)).left := rfl
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, ea, eb, _root_.mul_one]
    exact commGroup_sixTerm_relation_to_zpow_form h1
  intro s
  exact ⟨⊤, trivial, H.pull ((B ⊗ B).hom ⁻¹ᵁ ⊤).ι fun _ => rfl⟩

end GlobalTheory.AdjPolLocal
