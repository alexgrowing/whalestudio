import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulPullSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiRing

theorem exists_thick_eq_closedPoint (R : Type) [CommRing R] [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤) (e : ℕ) :
    ∃ p, thick R I e p = IsLocalRing.closedPoint R := by
  have h : IsLocalRing.closedPoint R ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (e + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus]
    exact fun x hx => IsLocalRing.le_maximalIdeal hI (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
  exact h

theorem exists_unit_term :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α), U.ExpT (𝟙_ _) k σ f → FibNZ (𝟙_ _ ⊗ G).hom σ → ∃ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (α : D.X), Good D.P.L z J ∧ T.hom z = IsLocalRing.closedPoint R ∧ (∀ b ∈ I, Geo.Tor.cst T.hom z b = 0) ∧ IsUnit (sval (f α) (lift (toUnit T) y).left z J) := by
  intro R _ _ _ I hI D A G _ _ U k σ f hE hF
  obtain ⟨z₀, hz₀, hn⟩ := hF (IsLocalRing.closedPoint R)
  obtain ⟨p, hp⟩ := exists_thick_eq_closedPoint R I hI 0
  have h₁ : G.hom ((snd (𝟙_ _) G).left z₀) = thick R I 0 p := by
    rw [hp, ← hz₀, ← Scheme.Hom.comp_apply, Over.w]
  obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback _ _ h₁
  let T : Over (Spec (CommRingCat.of R)) := (Over.map (thick R I 0)).obj (thickObj R I 0 G)
  let y : T ⟶ D.P.A := (U.gt 0).pG
  let x : T ⟶ G := fstG I 0 G
  have hG : (lift (toUnit T) x).left ≫ (snd _ G).left = x.left := by rw [← Over.comp_left, lift_snd]
  have hB : (lift (toUnit T) y).left ≫ (snd _ D.P.A).left = y.left := by rw [← Over.comp_left, lift_snd]
  have hf : (lift (toUnit T) y).left ≫ (fst _ D.P.A).left = (lift (toUnit T) x).left ≫ (fst _ G).left := by
    rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
  have hr : (lift (toUnit T) x).left z = z₀ := by
    have hi : lift (toUnit T) x = x ≫ (λ_ G).inv := by ext1 <;> simp [toUnit_unique]
    have hj : (snd (𝟙_ _) G).left ≫ (λ_ G).inv.left = 𝟙 _ := by
      rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
    have hx : x.left z = (snd (𝟙_ _) G).left z₀ := hz
    rw [hi, Over.comp_left, Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply, hj]
    rfl
  obtain ⟨JG, hJG⟩ := exists_good_pt (Z := T.left) U.P.L.isLB z
  obtain ⟨J, hJ⟩ := exists_good_pt (Z := T.left) D.P.isLB z
  obtain ⟨s, hs⟩ := hE 0
  obtain ⟨-, hsum⟩ := hs T.left (𝟙 _) _ _ (hG.trans (Category.id_comp _).symm) (hB.trans (Category.id_comp _).symm)
    hf z JG J hJG hJ
  have hu : IsUnit (sval σ (lift (toUnit T) x).left z JG) :=
    (MulPullSec.mem_nonzeroLocus_iff σ _ z hJG).1 (hr ▸ hn)
  obtain ⟨α, -, hα⟩ := IsLocalRing.exists_of_isUnit_sum
    ((congrArg IsUnit hsum).mp (((Units.isUnit _).pow k).mul hu))
  refine ⟨T, y, z, J, α, hJ, ?_, fun b hb => ?_, isUnit_of_mul_isUnit_left hα⟩
  · have : T.hom = pullback.snd G.hom (thick R I 0) ≫ thick R I 0 := rfl
    rw [this, Scheme.Hom.comp_apply, hz', hp]
  · refine (Geo.Tor.cst_comp (pullback.snd G.hom (thick R I 0)) (Ideal.Quotient.mk (I ^ (0 + 1))) z b).trans ?_
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using hb), Geo.Tor.cst, map_zero, gs_eq _ _ ⊤ trivial, map_zero,
      map_zero]

end GlobalTheory.PsiRing
