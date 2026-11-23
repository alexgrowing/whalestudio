import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.PsiNormPull

theorem valF_eq_valR' {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valF x U f = valR x U f := by
  rfl

theorem toStk_map_valR {A F : Type} [CommRing A] [Field F] (ψ : A →+* F) {X : Scheme.{0}} (x : Sp A ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (z : Sp F) (a : Γ(X, U)ˣ) :
    toStk z (ψ (valR x U a.val)) = (gm (spMap ψ ≫ x) z U a).val := by
  obtain ⟨h', e⟩ := CrdCalc.valR_spMap ψ x U h
  rw [← e, ← valF_eq_valR']
  exact toStk_valF _ U z (h' trivial) a

theorem norm_eq_one_of_isUnit {A F : Type} [CommRing A] [NormedField F] (ψ : A →+* F) (hψ : ∀ a, ‖ψ a‖ ≤ 1)
    {a : A} (ha : IsUnit a) : ‖ψ a‖ = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have e : ‖ψ u.val‖ * ‖ψ (u⁻¹).val‖ = 1 := by rw [← norm_mul, ← map_mul, u.mul_inv, map_one, norm_one]
  refine le_antisymm (hψ _) ?_
  calc (1 : ℝ) = ‖ψ u.val‖ * ‖ψ (u⁻¹).val‖ := e.symm
    _ ≤ ‖ψ u.val‖ * 1 := mul_le_mul_of_nonneg_left (hψ _) (norm_nonneg _)
    _ = _ := _root_.mul_one _

theorem norm_psi_pull : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)] (φ : V →+* V'), (∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V _ v) = algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ (φ v))) → (∀ v : V', ‖algebraMap (FractionRing V') (PadicAlgCl p) (algebraMap V' _ v)‖ ≤ 1) → ∀ (D : DegPre V) (D' : DegPre V') (hD : IsPullDeg φ D D') (χ : D'.X) (j : D.P.L.ι) (j' : D'.P.L.ι), ⊤ ≤ (D.c (hD.xe χ)).left ⁻¹ᵁ D.P.L.U j → ⊤ ≤ (D'.c χ).left ⁻¹ᵁ D'.P.L.U j' → ‖algebraMap (FractionRing V') (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V'))) _ ((D'.psi χ).s fun _ => j').val)‖ = ‖algebraMap (FractionRing V) (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing V))) _ ((D.psi (hD.xe χ)).s fun _ => j).val)‖ := by
  intro p _ V V' _ _ _ _ _ _ _ _ φ hφ hn D D' hD χ j j' hj hj'
  let F := PadicAlgCl p
  let ψ' : V' →+* F := (algebraMap (FractionRing V') F).comp (algebraMap V' (FractionRing V'))
  have hsq : jFK (R := V') F ≫ jK V' ≫ spMap φ = jFK (R := V) F ≫ jK V := by
    refine ((congrArg (jFK (R := V') F ≫ ·) (spMap_comp φ _).symm).trans (spMap_comp _ _).symm).trans
      ((congrArg spMap ?_).trans (spMap_comp _ _))
    exact RingHom.ext fun v => (hφ v).symm
  have z : Sp F := (default : PrimeSpectrum F)
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  have hΦ : ⊤ ≤ ((D'.c χ).left ≫ Φ) ⁻¹ᵁ D.P.L.U j := by
    rw [show (D'.c χ).left ≫ Φ = _ from hD.c_pr χ]
    exact fun y _ => hj (Set.mem_univ ((specOf φ) y))
  let U := (D.P.L.pull Φ).U (fun _ => j) ⊓ D'.P.L.U j'
  have hU : ⊤ ≤ (D'.c χ).left ⁻¹ᵁ U := fun y _ => ⟨mem_pull.2 (hΦ (Set.mem_univ y)), hj' (Set.mem_univ y)⟩
  have m' : ∀ y, D'.xK χ y ∈ D'.P.L.U j' := fun y => hj' (Set.mem_univ (jK V' y))
  have m : ∀ y, D.xK (hD.xe χ) y ∈ D.P.L.U j := fun y => hj (Set.mem_univ (jK V y))
  have e := pmaps_psi hD F hsq χ _ (𝟙 _) z (fun _ => j) (fun _ => j')
    (fun _ => hΦ (Set.mem_univ (jK V' (jFK (R := V') F z)))) (fun _ => m' _)
  have g₁ := gm_pullGen D.P.L (fun _ : PUnit => D.xK (hD.xe χ)) (fun _ => -1) (D.psi (hD.xe χ)) (jFK (R := V) F)
    (𝟙 _ ≫ 𝟙 _) z (fun _ => j) (Set.mem_iInter.2 fun _ => m _)
  have g₂ := gm_pullGen D'.P.L (fun _ : PUnit => D'.xK χ) (fun _ => -1) (D'.psi χ) (jFK (R := V') F)
    (𝟙 _) z (fun _ => j') (Set.mem_iInter.2 fun _ => m' _)
  rw [Fintype.prod_unique] at e
  replace e := g₁.symm.trans (e.trans (congrArg₂ (· * ·) (zpow_neg_one _) g₂))
  rw [eq_inv_mul_iff_mul_eq] at e
  simp only [Category.id_comp] at e
  have a := toStk_map_valR (algebraMap (FractionRing V) F) (𝟙 _)
    (LB.wchart D.P.L (fun _ : PUnit => D.xK (hD.xe χ)) fun _ => j) (fun y _ => Set.mem_iInter.2 fun _ => m y) z
    ((D.psi (hD.xe χ)).s fun _ => j)
  have a' := toStk_map_valR (algebraMap (FractionRing V') F) (𝟙 _)
    (LB.wchart D'.P.L (fun _ : PUnit => D'.xK χ) fun _ => j') (fun y _ => Set.mem_iInter.2 fun _ => m' y) z
    ((D'.psi χ).s fun _ => j')
  rw [Category.comp_id, ← valF_eq_valR'] at a a'
  have b := toStk_map_valR ψ' (D'.c χ).left U hU z (hD.w.s (fun _ => j, j'))
  have hpt : spMap ψ' ≫ (D'.c χ).left = jFK (R := V') F ≫ D'.xK χ :=
    (congrArg (· ≫ (D'.c χ).left) (spMap_comp _ _)).trans (Category.assoc _ _ _)
  have b' : toStk z (ψ' (valR (D'.c χ).left U (hD.w.s (fun _ => j, j')).val)) =
      (gw hD.w (jFK (R := V') F ≫ D'.xK χ) z j j').val := by
    rw [← hpt]; exact b
  have hu : IsUnit (valR (D'.c χ).left U (hD.w.s (fun _ => j, j')).val) := by
    exact (congrArg IsUnit (CrdCalc.valR_eq (R := V') (D'.c χ).left U hU _)).mpr ((Units.isUnit _).map _)
  have key := (toStk z).injective (a'.trans ((congrArg Units.val e).symm.trans
    ((Units.val_mul _ _).trans ((congrArg₂ (· * ·) b' a).symm.trans (map_mul _ _ _).symm))))
  refine (congrArg norm key).trans ?_
  rw [norm_mul, norm_eq_one_of_isUnit ψ' hn hu, _root_.one_mul]
  rfl

end GlobalTheory.ZH.PsiNormPull
