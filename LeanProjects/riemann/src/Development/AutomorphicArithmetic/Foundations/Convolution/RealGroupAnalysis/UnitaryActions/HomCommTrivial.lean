import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.CellGeneric
import GroundTheory.HeightsAndTheta.Theta.Weil.Birational

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2

variable {F : Type} [Field F] [NumberField F]

theorem cell_generic (s : Finset (G1 F)) : ∃ t, ∀ g ∈ s, g * t ∈ Cell F := by
  obtain ⟨x, hx⟩ := cellGeneric F s
  exact ⟨nL x, hx⟩
theorem isWeilCell_cell : GroundTheory.Heights₂.Theta.IsWeilCell (Cell F) where
  inv_mem _ h := inv_mem_cell h
  exists_mul_mem_left s := by
    obtain ⟨t, ht⟩ := cell_generic (s.image fun g => g⁻¹)
    exact ⟨t⁻¹, fun g hg => by simpa using inv_mem_cell (ht g⁻¹ (Finset.mem_image_of_mem _ hg))⟩
theorem eq_top_of_nU_nL (H : Subgroup (G1 F)) (hn : ∀ b, nU b ∈ H) (hl : ∀ c, nL c ∈ H) : H = ⊤ := by
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨x, hx⟩ := cellGeneric F {g}
  obtain ⟨b₁, a, b₂, h⟩ := (mem_cell_iff _).1 (hx g (Finset.mem_singleton_self g))
  rw [← H.mul_mem_cancel_right (hl x), h, mul_assoc (nU b₁), mD_mul_wW]
  exact mul_mem (mul_mem (hn _) (mul_mem (mul_mem (hn _) (hl _)) (hn _))) (hn _)
theorem eq_top_of_nU_wW (H : Subgroup (G1 F)) (hn : ∀ b, nU b ∈ H) (hw : wW F ∈ H) : H = ⊤ :=
  eq_top_of_nU_nL H hn fun c => by rw [nL_eq]; exact mul_mem (mul_mem hw (hn _)) (inv_mem hw)
theorem hom_ext_nL {M : Type*} [Monoid M] {Φ Ψ : G1 F →* M} (hn : ∀ b, Φ (nU b) = Ψ (nU b)) (hl : ∀ c, Φ (nL c) = Ψ (nL c)) :
    Φ = Ψ := by
  have h := eq_top_of_nU_nL (Φ.toHomUnits.eqLocus Ψ.toHomUnits) (fun b => Units.ext (hn b)) fun c => Units.ext (hl c)
  ext g
  exact congrArg Units.val (show g ∈ Φ.toHomUnits.eqLocus Ψ.toHomUnits from h ▸ Subgroup.mem_top g)
theorem hom_ext_wW {M : Type*} [Monoid M] {Φ Ψ : G1 F →* M} (hn : ∀ b, Φ (nU b) = Ψ (nU b)) (hw : Φ (wW F) = Ψ (wW F)) :
    Φ = Ψ := by
  have h := eq_top_of_nU_wW (Φ.toHomUnits.eqLocus Ψ.toHomUnits) (fun b => Units.ext (hn b)) (Units.ext hw)
  ext g
  exact congrArg Units.val (show g ∈ Φ.toHomUnits.eqLocus Ψ.toHomUnits from h ▸ Subgroup.mem_top g)

theorem idem_gen (e : A F) (he : e * e = e) (H : Subgroup (G1 F)) (hn : ∀ b, nU (e * b) ∈ H) (hl : ∀ c, nL (e * c) ∈ H)
    (g : G1 F) (hg : ∀ i j, (1 - e) * g i j = (1 - e) * (1 : Matrix (Fin 2) (Fin 2) (A F)) i j) : g ∈ H := by
  have h := eq_top_of_nU_nL (H.comap (cut e he)) (fun b => by rw [Subgroup.mem_comap, cut_nU]; exact hn b)
    fun c => by rw [Subgroup.mem_comap, cut_nL]; exact hl c
  have hc : cut e he g = g := by
    have h00 := hg 0 0
    have h01 := hg 0 1
    have h10 := hg 1 0
    have h11 := hg 1 1
    simp only [Matrix.one_apply_eq, Matrix.one_apply_ne (zero_ne_one), Matrix.one_apply_ne (one_ne_zero)] at h00 h01 h10 h11
    apply specialLinear_ext_entries <;> simp [cut_val]
    exacts [by linear_combination -h00, by linear_combination -h01, by linear_combination -h10, by linear_combination -h11]
  rw [← hc]
  exact (show g ∈ H.comap (cut e he) from h ▸ Subgroup.mem_top g)

theorem at_gen (v : HeightOneSpectrum (𝓞 F)) (H : Subgroup (G1 F)) (hn : ∀ x, nU (sv v x) ∈ H) (hl : ∀ x, nL (sv v x) ∈ H)
    (g : G1 F) (hg : At v g) : g ∈ H := by
  refine idem_gen (sv v 1) (by rw [sv_mul, mul_one]) H (fun b => by rw [sv_mul_left]; exact hn _)
    (fun b => by rw [sv_mul_left]; exact hl _) g fun i j => a_ext ?_ fun w => ?_
  · rw [map_mul, map_mul]; exact congrArg _ (hg.1 i j)
  · rw [map_mul, map_mul]
    by_cases h : w = v
    · subst h; simp
    · exact congrArg _ (hg.2 w h i j)

theorem inf_gen (H : Subgroup (G1 F)) (hn : ∀ b : A F, b.2 = 0 → nU b ∈ H) (hl : ∀ b : A F, b.2 = 0 → nL b ∈ H)
    (g : G1 F) (hg : ∀ i j, (g i j).2 = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).2) : g ∈ H :=
  idem_gen (eInf F) eInf_idem H (fun b => hn _ (by rw [eInf_mul])) (fun b => hl _ (by rw [eInf_mul])) g fun i j =>
    (one_sub_eInf_mul _).trans ((congrArg (Prod.mk 0) (hg i j)).trans (one_sub_eInf_mul _).symm)

theorem fin_gen (H : Subgroup (G1 F)) (hn : ∀ b : A F, b.1 = 0 → nU b ∈ H) (hl : ∀ b : A F, b.1 = 0 → nL b ∈ H)
    (g : G1 F) (hg : InfOne g) : g ∈ H :=
  idem_gen (1 - eInf F) (by linear_combination eInf_idem (F := F)) H (fun b => hn _ (congrArg Prod.fst (one_sub_eInf_mul b)))
    (fun b => hl _ (congrArg Prod.fst (one_sub_eInf_mul b))) g fun i j => by
      rw [sub_sub_cancel]
      exact (eInf_mul _).trans ((congrArg (fun x => Prod.mk x 0) (hg i j)).trans (eInf_mul _).symm)

theorem hom_comm_trivial {C : Type*} [CommGroup C] (Φ : G1 F →* C) (g : G1 F) : Φ g = 1 := by
  have hn : ∀ b, Φ (nU b) = 1 := fun b => by
    have h := congrArg Φ (mD_mul_nU (IdeleGroup.diagonal F (Units.mk0 2 two_ne_zero)) (rt 3⁻¹ * b))
    have e : ((IdeleGroup.diagonal F (Units.mk0 2 two_ne_zero) : (A F)ˣ) : A F) ^ 2 * (rt 3⁻¹ * b) = b + rt 3⁻¹ * b := by
      have h3 : (algebraMap F (A F) 3⁻¹) * 3 = 1 := by
        rw [← map_ofNat (algebraMap F (A F)) 3, ← map_mul, inv_mul_cancel₀ three_ne_zero, map_one]
      rw [coe_diagonal, Units.val_mk0, rt, rt, map_ofNat]
      linear_combination b * h3
    rw [e, nU_add, map_mul, map_mul, map_mul, mul_comm, mul_left_inj] at h
    exact (mul_eq_right.1 h.symm)
  have h := eq_top_of_nU_nL Φ.ker hn fun c => by
    rw [MonoidHom.mem_ker, nL_eq, map_mul, map_mul, hn, map_inv, mul_one, mul_inv_cancel]
  exact (show g ∈ Φ.ker from h ▸ Subgroup.mem_top g)

theorem Gam_le (H : Subgroup (G1 F)) (hn : ∀ b : F, nU (rt b) ∈ H) (hw : wW F ∈ H) : Gam F ≤ H := by
  have hl : ∀ c : F, nL (rt c) ∈ H := fun c => by
    rw [nL_eq, rt, ← map_neg]; exact mul_mem (mul_mem hw (hn _)) (inv_mem hw)
  have key : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) F, γ 1 0 ≠ 0 → ratS F γ ∈ H := fun γ hc => by
    have e : ((IdeleGroup.diagonal F (Units.mk0 _ hc))⁻¹ : (A F)ˣ).val = rt (γ 1 0)⁻¹ := rfl
    have e' : (IdeleGroup.diagonal F (Units.mk0 _ hc) : (A F)ˣ).val = rt (γ 1 0) := rfl
    rw [cell_normal (ratS F γ) (IdeleGroup.diagonal F (Units.mk0 _ hc)) rfl, mul_assoc (nU _), mD_mul_wW, inv_neg, inv_inv,
      Units.val_neg, Units.val_neg, neg_neg, e, e', ratS_apply, ratS_apply]
    simp only [rt, ← map_mul, ← map_neg]
    exact mul_mem (mul_mem (hn _) (mul_mem (mul_mem (hn _) (hl _)) (hn _))) (hn _)
  rintro _ ⟨γ, rfl⟩
  by_cases hc : γ 1 0 = 0
  · obtain ⟨w, hw'⟩ := wW_mem (F := F)
    have h10 : w 1 0 = -1 := by
      haveI := AdeleBaseChange.nontrivial_adeleRing F
      apply (algebraMap F (A F)).injective
      simpa using (ratS_apply w 1 0).symm.trans (congrArg (fun g : G1 F => g 1 0) hw')
    rw [← H.mul_mem_cancel_right hw, ← hw', ← map_mul]
    refine key _ ?_
    have hd := γ.det_coe
    rw [Matrix.det_fin_two, hc] at hd
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hc, h10]
    intro h
    have : γ.1 1 1 = 0 := by simpa using h
    simp [this] at hd
  · exact key γ hc

end UpperTheory.ConvolutionTheory.R2

end
