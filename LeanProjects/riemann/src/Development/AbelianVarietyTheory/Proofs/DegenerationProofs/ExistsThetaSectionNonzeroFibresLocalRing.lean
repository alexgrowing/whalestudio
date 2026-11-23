import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsLocalModelOfIntegral
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPsiThetaExpansionPsiRelation

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.PsiRing

theorem basis_prod_famφT_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (U : Type) [CommGroup U] (h : ((T ⊗ D.P.A).left ⟶ D.P.A.left) → U) :
    ∏ k, h (famφT D T 0 k) ^ DegPre.famε 1 k = h (snd T D.P.A).left := by
  have := D.P.isAb.comm
  rw [PsiExists.famφT_eq, PsiExists.cT_zero, _root_.mul_one]
  simp [Fin.prod_univ_four, DegPre.famε]

theorem exists_basis_fibNZ : SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), ∃ th : SecBT D (𝟙_ _) 1 0, FibNZ (𝟙_ _ ⊗ D.P.A).hom th ∧ ∀ g : SecBT D (𝟙_ _) 1 0, ∃ b : R, Mult D th g b := by
  intro hT R _ _ _ D
  have := D.P.isAb.comm
  let T : Over (Spec (CommRingCat.of R)) := 𝟙_ _
  have e : translPt D.P.A (1 : T ⟶ D.P.A) = snd T D.P.A := by
    show (fst T D.P.A ≫ 1) * snd T D.P.A = _
    rw [MonObj.comp_one, _root_.one_mul]
  obtain ⟨⟨b, hb⟩, -⟩ := hT _ D.P 1 le_rfl R (𝟙 _) (1 : T ⟶ D.P.A)
  change Fin (1 ^ D.P.g) → LB.Sec (twistLB D.P.A D.P.L 1 (1 : T ⟶ D.P.A)) at b
  change IsSecBasis (T := T) (A := D.P.A) _ b at hb
  have : Subsingleton (Fin (1 ^ D.P.g)) := by rw [one_pow]; infer_instance
  let i₀ : Fin (1 ^ D.P.g) := ⟨0, by simp⟩
  have H : FormEq (K := Fin 2) ![(snd T D.P.A).left, (translPt D.P.A (1 : T ⟶ D.P.A)).left] ![((1 : ℕ) : ℤ) - 1, 1]
      (famφT D T 0) (DegPre.famε 1) := fun U _ h => by
    rw [basis_prod_famφT_zero, e]
    simp [Fin.prod_univ_two]
  obtain ⟨th, hth⟩ := exists_sec D.P.isLB H (b i₀)
  have hf : (fst T D.P.A).left = (T ⊗ D.P.A).hom :=
    (Category.comp_id _).symm.trans (Over.w (fst T D.P.A))
  have key : ∀ g : SecBT D T 1 0, ∃ c : R, Mult D th g c := fun g => by
    obtain ⟨s, hs⟩ := exists_sec D.P.isLB (fun U _ h => (H U h).symm) g
    obtain ⟨c, hc, -⟩ := hb s
    have hc' := fun j => (hc j).trans (Fintype.sum_subsingleton _ i₀)
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (c i₀), fun Z r z J hJ => ?_⟩
    refine (hs Z r z J hJ).symm.trans (Eq.trans ?_ (congrArg _ (hth Z r z J hJ).symm))
    refine (congrArg (gs r z _) (hc' _)).trans ((gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·)
        ((gs_res r z le_top (hJ.mem _ r) _).trans ((gs_pull r (fst T D.P.A).left z ⊤ trivial _).trans ?_)) rfl))
    exact congrArg₂ (fun (q : Z ⟶ Spec (CommRingCat.of R)) (a : Γ(Spec (CommRingCat.of R), ⊤)) => gs q z ⊤ a)
      (congrArg (r ≫ ·) hf) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply (c i₀)).symm
  refine ⟨th, fun y => ?_, key⟩
  have hp : IsPullback (snd T D.P.A).left (T ⊗ D.P.A).hom D.P.A.hom (𝟙 _) := by
    rw [← hf]
    exact (IsPullback.of_hasPullback T.hom D.P.A.hom).flip
  obtain ⟨t, ht⟩ := KeyPow.exists_sec_fibre_ne_zero hT D.P hp
  obtain ⟨z, hz, hz'⟩ := ht y
  obtain ⟨g, hg⟩ := exists_sec D.P.isLB (K := PUnit) (φ := fun _ => (snd T D.P.A).left) (ε := fun _ => 1)
    (φ' := famφT D T 0) (ε' := DegPre.famε 1) (fun U _ h => by
      rw [basis_prod_famφT_zero]; simp) t
  obtain ⟨c, hc⟩ := key g
  choose J hJ using fun χ : (T ⊗ D.P.A).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  refine ⟨z, hz, (MulPullSec.mem_nonzeroLocus_iff th (𝟙 _) z hJ).2 ?_⟩
  have u := (MulPullSec.mem_nonzeroLocus_iff (K := PUnit) (φ := fun _ => (snd T D.P.A).left) (ε := fun _ => 1)
    t (𝟙 _) z hJ).1 hz'
  rw [← hg _ _ z J hJ, hc _ _ z J hJ] at u
  exact isUnit_of_mul_isUnit_right u

end GlobalTheory.PsiRing
end
