import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSectionOfChartFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

noncomputable section
namespace GlobalTheory.Ex.AbPartIso
open ThetaInValues

theorem exists_th_scale : AllIso fun {_} _ _ {_} {_} {F} _ _ {N} {N'} ν ν' {_} w f =>
    ∃ lm : F, ∀ x, N'.th (f x) = lm * wVal ν ν' w f x * N.th x := by
  intro R _ _ D D' F _ _ N N' ν ν' φ w f hφ hw hc
  obtain ⟨y⟩ : Nonempty (TF (R := R) F).left := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have hJ := good ν y
  have hJ' := good ν' y
  obtain ⟨th, ρ, hth, vth⟩ := exists_th ν y
  obtain ⟨th', ρ', -, vth'⟩ := exists_th ν' y
  have e : φ.hom.left ≫ (snd (TF (R := R) F) D'.P.A).left = 𝟙 _ ≫ (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left :=
    (Category.id_comp _).symm
  let b := VVRank.pullTo (φ := fun _ : Fin 1 => (snd (TF (R := R) F) D'.P.A).left) (ε := fun _ => 1)
    (φ' := fun _ : Fin 1 => 𝟙 _ ≫ (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left) th' φ.hom.left (fun _ => e)
  obtain ⟨a, ha, -⟩ := (FieldBaseChange.isoRelM_bijective (m := 𝟙 _) (k := 1) (h₁ := 𝟙 _)
    (g₁ := (snd (TF (R := R) F) D.P.A).left) D.P.isLB D'.P.isLB hw rfl (𝟙 _) (Category.id_comp _)
    (Category.id_comp _)).2 b
  obtain ⟨r, hr⟩ := hth a
  obtain ⟨r₀, rfl⟩ : ∃ r₀ : F, r = fnOf r₀ :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom r, (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of F)) r).symm⟩
  refine ⟨r₀ * ρ * ρ'⁻¹.val, fun x => ?_⟩
  have H := BoxExpansion.isoRel_val ha (ptSecT D.P.A (ν.eA x)).left y hJ hJ'
  simp only [Category.comp_id] at H
  have h₁ : sval b (ptSecT D.P.A (ν.eA x)).left y ν'.J = sR y (N'.th (f x) * ρ') := by
    refine (VVRank.sval_pullTo _ _ _ _ y hJ').trans (Eq.trans ?_ (vth' (f x)))
    rw [← Over.comp_left, ptSecT, hc x]
    rfl
  have hm := hJ.mem (fun _ : Fin 1 => (snd (TF (R := R) F) D.P.A).left) (ptSecT D.P.A (ν.eA x)).left
  have h₂ : sval a (ptSecT D.P.A (ν.eA x)).left y ν.J = sR y r₀ * sR y (N.th x * ρ) := by
    refine (congrArg (gs _ y _) (hr _)).trans ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) ?_ (vth x)))
    refine (gs_res _ y _ hm _).trans ((gs_pull _ (fst (TF (R := R) F) D.P.A).left y ⊤ trivial _).trans ?_)
    rw [← Over.comp_left, ptSecT, lift_fst]
    exact gs_fnOf y r₀
  have p₁ : (ptSecT D.P.A (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left = (ν.eA x).left := by
    rw [← Over.comp_left, ptSecT, lift_snd]
  have p₂ : (ptSecT D.P.A (ν.eA x)).left ≫ (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left = (ν'.eA (f x)).left := by
    rw [← Over.comp_left, ptSecT, ← Category.assoc, hc x, lift_snd]
  have h₃ : sR y (wVal ν ν' w f x) = (BoxExpansion.pw w (ptSecT D.P.A (ν.eA x)).left y (ν.J (ν.eA x).left)
      (ν'.J (ν'.eA (f x)).left)).val := by
    have m₁ : (snd (TF (R := R) F) D.P.A).left ((ptSecT D.P.A (ν.eA x)).left y) ∈ D.P.L.U (ν.J (ν.eA x).left) :=
      (congrArg (fun q : (TF (R := R) F).left ⟶ D.P.A.left => q y ∈ D.P.L.U (ν.J (ν.eA x).left)) p₁).mpr (hJ _)
    have m₂ : (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left ((ptSecT D.P.A (ν.eA x)).left y) ∈
        D'.P.L.U (ν'.J (ν'.eA (f x)).left) :=
      (congrArg (fun q : (TF (R := R) F).left ⟶ D'.P.A.left => q y ∈ D'.P.L.U (ν'.J (ν'.eA (f x)).left)) p₂).mpr (hJ' _)
    exact toStk_valF (F := F) (ptSecT D.P.A (ν.eA x)).left
      ((D'.P.L.pull (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left).U (fun _ => ν'.J (ν'.eA (f x)).left) ⊓
        (D.P.L.pull (snd (TF (R := R) F) D.P.A).left).U (fun _ => ν.J (ν.eA x).left)) y
      ⟨mem_pull.2 m₂, mem_pull.2 m₁⟩ _
  have H' : sR y (N'.th (f x) * ρ') = sR y (wVal ν ν' w f x) * (sR y r₀ * sR y (N.th x * ρ)) := by
    refine h₁.symm.trans (H.trans (congrArg₂ (· * ·) ?_ h₂))
    rw [h₃, pow_one, p₁, p₂]
  rw [← map_mul, ← map_mul] at H'
  haveI : Nontrivial ((TF (R := R) F).left.presheaf.stalk y) := inferInstance
  have := (sR (R := R) y).injective H'
  rw [← Units.eq_mul_inv_iff_mul_eq] at this
  rw [this]
  ring

end GlobalTheory.Ex.AbPartIso
end
