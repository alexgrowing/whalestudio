import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EtaKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

section SlopeTestRemainingChoices
open UpperTheory.V.U3 UpperTheory.V.UnitaryThreeInertia

private def eGb {k : Type} [CommRing k] (a : k) : Gb k (-2) :=
  (⟨Matrix.single 2 0 a, by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert h; decide) | simp⟩ : gw k (-2))

private theorem eGb_val {k : Type} [CommRing k] (a : k) : (eGb a).val 2 0 = a := by
  show Matrix.single 2 0 a 2 0 = a
  exact Matrix.single_apply_same _ _ _

private theorem gb_ext {k : Type} [CommRing k] {X Y : Gb k (-2)} (h : X.val 2 0 = Y.val 2 0) : X = Y := by
  have hX : ∀ a b, UpperTheory.V.U3.wt a b ≠ -2 → (X.val : Matrix (Fin 3) (Fin 3) k) a b = 0 := X.2
  have hY : ∀ a b, UpperTheory.V.U3.wt a b ≠ -2 → (Y.val : Matrix (Fin 3) (Fin 3) k) a b = 0 := Y.2
  apply Subtype.ext
  ext a b
  by_cases hab : a = 2 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab
    exact h
  · have hw : UpperTheory.V.U3.wt a b ≠ -2 := by
      revert hab
      fin_cases a <;> fin_cases b <;> first | decide | simp [UpperTheory.V.U3.wt, UpperTheory.V.U3.wt1]
    exact (hX a b hw).trans (hY a b hw).symm

private theorem gb_add {k : Type} [CommRing k] (X Y : Gb k (-2)) : (X + Y).val 2 0 = X.val 2 0 + Y.val 2 0 := rfl
private theorem gb_sub {k : Type} [CommRing k] (X Y : Gb k (-2)) : (X - Y).val 2 0 = X.val 2 0 - Y.val 2 0 := rfl

private theorem gb_rep {k D : Type} [CommRing k] [Group D] (η : D →* ℤˣ) (Ψ : D →* kˣ) (g : D) (X : Gb k (-2))
    (c : k) (hc : c * (Ψ g : k) ^ 2 = ((η g : ℤ) : k)) :
    (gRep η Ψ (-2) g X).val 2 0 = c * X.val 2 0 := by
  rw [gRep_val, adRep_baseLift_apply]
  have hw : UpperTheory.V.U3.wt 2 0 = -2 := by decide
  have r0 : Fin.rev (0 : Fin 3) = 2 := rfl
  have r2 : Fin.rev (2 : Fin 3) = 0 := rfl
  rw [hw, r0, r2, zpow_neg, zpow_ofNat]
  have hc' : c = ((η g : ℤ) : k) * (((Ψ g ^ 2)⁻¹ : kˣ) : k) := by
    have h0 : c * (((Ψ g ^ 2 : kˣ)) : k) * (((Ψ g ^ 2)⁻¹ : kˣ) : k) = c :=
      Units.mul_inv_cancel_right _ _
    rw [Units.val_pow_eq_pow_val, hc] at h0
    exact h0.symm
  rw [hc']
  rcases Int.units_eq_one_or (η g) with h1 | h1
  · rw [if_pos h1, h1]
    simp only [Units.val_one, Int.cast_one]
    ring
  · rw [if_neg (by rw [h1]; decide), h1]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    ring

end SlopeTestRemainingChoices

theorem UpperTheory.V.X.xppOf :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G' Γ ι : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [Group Γ] [TopologicalSpace Γ] (F : UnitaryThreeInertia.Frame O G' Γ ι) (γ : Γ → ResidueField O), (∀ g, γ g * (F.Ψbar g : ResidueField O) ^ 2 = ((F.η g : ℤ) : ResidueField O)) → (∀ z : Γ → ResidueField O, IsLocallyConstant z → (∀ g h, z (g * h) = z g + γ g * z h) → (∀ v, v ≠ F.vl → ∀ s ∈ F.Nv v, z (F.loc v s) = 0) → (∃ m, ∀ s, z (F.loc F.vl s) = γ (F.loc F.vl s) * m - m) → ∃ m, ∀ g, z g = γ g * m - m) → F.Xpp := by
  intro O iR iL G' Γ ι iG iT iTG iΓ iTΓ F γ hγ hmain
  show Subsingleton (F.selmerCohomologyQuotient (-2))
  refine Submodule.Quotient.subsingleton_iff.2 ?_
  rw [eq_top_iff]
  rintro ⟨f, hf⟩ -
  show f ∈ B1 (F.gbar (-2))
  obtain ⟨hZ, hL⟩ := Submodule.mem_inf.1 hf
  obtain ⟨hcont, hcoc⟩ := (mem_Z1_iff_cocycle _ _).1 hZ
  have hZL : ∀ v, F.res1 (-2) v f ∈ Z1 (F.gloc (-2) v) ∧
      (v ≠ F.vl → ∀ s ∈ F.Nv v, F.res1 (-2) v f s = 0) ∧
      (v = F.vl → (-2 : ℤ) < 0 → F.res1 (-2) v f ∈ B1 (F.gloc (-2) v)) ∧
      (v = F.vl → (-2 : ℤ) = 0 → ∀ s ∈ F.Iv v, F.res1 (-2) v f s = 0) :=
    fun v => (Submodule.mem_iInf _).1 hL v
  have hlc : IsLocallyConstant (fun g => (f g).val 2 0) :=
    ((IsLocallyConstant.iff_continuous _).2 hcont).comp
      (fun X : UpperTheory.V.UnitaryThreeInertia.Gb (ResidueField O) (-2) => X.val 2 0)
  obtain ⟨m, hm⟩ := hmain (fun g => (f g).val 2 0) hlc
    (by
      intro g h
      show (f (g * h)).val 2 0 = (f g).val 2 0 + γ g * (f h).val 2 0
      rw [hcoc g h, gb_add, gb_rep F.η F.Ψbar g _ (γ g) (hγ g)])
    (by
      intro v hv s hs
      have h0 : f (F.loc v s) = 0 := (hZL v).2.1 hv s hs
      show (f (F.loc v s)).val 2 0 = 0
      rw [h0]
      rfl)
    (by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((hZL F.vl).2.2.1 rfl (by norm_num))
      refine ⟨m.val 2 0, fun s => ?_⟩
      have h' : f (F.loc F.vl s) = F.gbar (-2) (F.loc F.vl s) m - m := hm s
      show (f (F.loc F.vl s)).val 2 0 = _
      rw [h', gb_sub, gb_rep F.η F.Ψbar _ _ (γ _) (hγ _)])
  rw [mem_coboundaries1]
  refine ⟨eGb m, fun g => gb_ext ?_⟩
  rw [gb_sub, gb_rep F.η F.Ψbar g _ (γ g) (hγ g), eGb_val]
  exact hm g
