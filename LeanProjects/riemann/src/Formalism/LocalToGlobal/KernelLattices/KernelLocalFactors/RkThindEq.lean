import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkThind
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.HermitianHalfLattice.MemHalfBOEquiv
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.HermitianHalfLattice.MLConjTranspose
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualFourfoldCurveIdealLattice
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.TripleEighthProof

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H

section SlopeTestRemainingChoices

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem sumU_eq_inter {H : Sesq V} {α : V → ℂ} {Λ₁ Λ₂ : AddSubgroup V} {F : V → ℂ} {S : Finset V} (hH : IsHerm H)
    (hS : IsSemiChar H Λ₂ α) (hF : F ∈ fixedBy H α Λ₁) (hSr : IsReps Λ₁ Λ₂ S) (hidx : relIdx Λ₁ Λ₂ ≠ 0) (z : V) :
    sumU H α S F z = ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ) * inter H α Λ₁ Λ₂ F z := by
  rw [Formalism.L2.Th1.H.interReps V H hH Λ₁ Λ₂ α hS F hF S hSr z]
  have h3 : ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; exact (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hidx))).ne'
  field_simp

end SlopeTestRemainingChoices

section Lift

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E)))
  (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))

theorem homE_zero_of_aa_bot (hLa : A.LaHyp a b S) (hN : IsSdLat N) (hN' : IsSdLat N') (h : A.AA = ⊥) (f : HomE X.E a b) : f = 0 := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · refine LinearMap.ext fun v => ?_
    have hv : v = 0 := funext fun i => (Fin.cast ha i).elim0
    rw [hv, map_zero, LinearMap.zero_apply]
  rcases Nat.eq_zero_or_pos b with hb | hb
  · exact LinearMap.ext fun v => funext fun i => (Fin.cast hb i).elim0
  exfalso
  have hsd := ((hLa.2.2.2.2.2 N N' hN hN').2).1
  obtain ⟨τ⟩ := hLa.2.1
  have hL : LamC (X.embC A.σ₀) A.δ A.AA N N' = ⊥ := by
    unfold LamC laV; rw [h, perO_bot]; simp
  rw [hL] at hsd
  have hv : (show VCx X.Tau a b from fun _ _ _ => (1 : ℂ)) ∈ dualLat (HV A.sc) (⊥ : AddSubgroup (VCx X.Tau a b)) := by
    intro y hy
    rw [AddSubgroup.mem_bot] at hy
    exact ⟨0, by simp [hy, altE]⟩
  unfold IsSelfDual at hsd
  rw [hsd, AddSubgroup.mem_bot] at hv
  have := congrFun (congrFun (congrFun hv τ) ⟨0, hb⟩) ⟨0, ha⟩
  simp at this

theorem exists_isLift (hLa : A.LaHyp a b S) (hN : IsSdLat N) (hN' : IsSdLat N') {c D : ℕ} (hD : 0 < D) (hcD : c ∣ D) {x : HomE X.E a b}
    (hx : x ∈ divLat D (homAt S N N')) : ∃ s, A.IsLift S N N' c x s := by
  by_cases hAA0 : A.AA = ⊥
  · refine ⟨0, ⟨⟨1, one_pos, zero_mem _⟩, ?_⟩⟩
    rw [homE_zero_of_aa_bot A S N N' hLa hN hN' hAA0 x, sub_zero]
    exact zero_mem _
  · obtain ⟨s, hs⟩ := lf_exists_liftS A S hLa.2.2.2.1 hAA0 N N' hN hN' hD hx
    exact ⟨s, lf_isLift_of_liftS A S hLa.2.2.2.1 N N' hD hcD hs⟩

end Lift

theorem theta_coset_indicator_natural : ThIndOfEq := by
  intro X A a b Sall D hst hD hLa hEq
  unfold Amb.ThIndEq
  intro γ γ' N N' c x hR z
  obtain ⟨hN, hN', hc, hcD, hx⟩ := hR
  obtain ⟨w, rfl⟩ := (TI.RV A γ γ').surjective z
  have hgN : IsSdLat (gmap γ.1 N) := isSdLat_gmap hN γ
  have hgN' : IsSdLat (gmap γ'.1 N') := isSdLat_gmap hN' γ'
  have hpull : ∀ v, A.pullV a b γ.1 γ'.1 ((TI.RV A γ γ') v) = v := fun v => by
    rw [← TI.RV_symm_apply, LinearEquiv.symm_apply_apply]

  have hx' : γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap ∈ divLat D (homAt Sall (gmap γ.1 N) (gmap γ'.1 N')) := by
    show ((D : 𝓞 X.E) • (LinearMap.id : HomE X.E a b →ₗ[𝓞 X.E] HomE X.E a b)) (TI.conjH γ.1 γ'.1 x) ∈ homAt Sall (gmap γ.1 N) (gmap γ'.1 N')
    rw [TI.mem_homAt_gmap, LinearMap.smul_apply, LinearMap.id_apply, TI.equiv_osmulW, LinearEquiv.symm_apply_apply]
    exact hx
  obtain ⟨s', hs'⟩ := exists_isLift A Sall (gmap γ.1 N) (gmap γ'.1 N') hLa hgN hgN' hD hcD hx'
  have hs : A.IsLift Sall N N' c x ((TI.conjH γ.1 γ'.1).symm s') := TI.isLift_conj A Sall γ.1 γ'.1 N N' c x s' hs'
  have hemb : embH (X.embC A.σ₀) A.δ s' = (TI.RV A γ γ') (embH (X.embC A.σ₀) A.δ ((TI.conjH γ.1 γ'.1).symm s')) := by
    rw [TI.RV_embH]
    congr 1
    exact ((TI.conjH γ.1 γ'.1).apply_symm_apply s').symm
  rw [thInd_eq_lift' A Sall (gmap γ.1 N) (gmap γ'.1 N') hLa hgN hgN' c hc _ s' hs' _,
    thInd_eq_lift' A Sall N N' hLa hN hN' c hc x _ hs _, hpull]

  have hL : LamC (X.embC A.σ₀) A.δ A.AA (gmap γ.1 N) (gmap γ'.1 N') = imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (LamC (X.embC A.σ₀) A.δ A.AA N N') :=
    (TI.imgLat_laV A γ γ' _ _ fun y => TI.mem_perO_gmap A.AA γ.1 γ'.1 N N' y).symm
  have hAc : AC (X.embC A.σ₀) A.δ A.AA Sall (gmap γ.1 N) (gmap γ'.1 N') c = imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (AC (X.embC A.σ₀) A.δ A.AA Sall N N' c) :=
    (TI.imgLat_laV A γ γ' _ _ fun y => TI.mem_halfAO_equiv (TI.conjH γ.1 γ'.1) (TI.mem_perO_gmap A.AA γ.1 γ'.1 N N') Sall c y).symm
  have hBc : BC (X.embC A.σ₀) A.δ A.AA Sall (gmap γ.1 N) (gmap γ'.1 N') c = imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c) :=
    (TI.imgLat_laV A γ γ' _ _ fun y => TI.mem_halfBO_equiv (TI.conjH γ.1 γ'.1) (TI.mem_perO_gmap A.AA γ.1 γ'.1 N N') Sall c y).symm
  have hI : imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) ((LamC (X.embC A.σ₀) A.δ A.AA N N') ⊓ (AC (X.embC A.σ₀) A.δ A.AA Sall N N' c)) = imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (LamC (X.embC A.σ₀) A.δ A.AA N N') ⊓ imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (AC (X.embC A.σ₀) A.δ A.AA Sall N N' c) := by
    ext y
    rw [AddSubgroup.mem_inf, KS.MM.mem_imgLat, KS.MM.mem_imgLat, KS.MM.mem_imgLat, AddSubgroup.mem_inf]
  rw [hL, hAc, hBc]

  obtain ⟨hθ, hlev⟩ := (heisHyp_of A a b Sall hLa).2.2.2.2 N N' hN hN'
  obtain ⟨hSc, hr1, hr2, -⟩ := hlev c hc
  have hIso : IsIsom (HV A.sc) (HV A.sc) ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) := TI.isIsom_RV A hst γ γ'
  have hα : ∀ v, alV A.d A.sc ((TI.RV A γ γ') v) = alV A.d A.sc v := TI.alV_RV A hst γ γ'

  have hcard : (repsOf (imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c)) (imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (LamC (X.embC A.σ₀) A.δ A.AA N N') ⊓ imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (AC (X.embC A.σ₀) A.δ A.AA Sall N N' c))).card =
      (repsOf (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c) ((LamC (X.embC A.σ₀) A.δ A.AA N N') ⊓ (AC (X.embC A.σ₀) A.δ A.AA Sall N N' c))).card := by
    have hr1' : relIdx (imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c)) (imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (LamC (X.embC A.σ₀) A.δ A.AA N N') ⊓ imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (AC (X.embC A.σ₀) A.δ A.AA Sall N N' c)) ≠ 0 := by
      rw [← hI, KS.MM.relIdx_map]; exact hr1
    rw [Formalism.L2.Th1.H.Tri.card_reps (repsOf_spec _ _ hr1'), Formalism.L2.Th1.H.Tri.card_reps (repsOf_spec _ _ hr1), ← hI]
    exact KS.MM.relIdx_map _ _ _

  have he : ∀ v, A.e a b (gmap γ.1 N) (gmap γ'.1 N') ((TI.RV A γ γ') v) = A.e a b N N' v := fun v => by
    rw [hEq γ γ' N N' hN hN' ((TI.RV A γ γ') v), hpull]
  have hsum : ∀ v, sumU (HV A.sc) (alV A.d A.sc) (repsOf (imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (LamC (X.embC A.σ₀) A.δ A.AA N N')) (imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c))) (A.e a b (gmap γ.1 N) (gmap γ'.1 N')) ((TI.RV A γ γ') v) =
      sumU (HV A.sc) (alV A.d A.sc) (repsOf (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c)) (A.e a b N N') v := by
    intro v
    have hr2' : relIdx (imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (LamC (X.embC A.σ₀) A.δ A.AA N N')) (imgLat ((TI.RV A γ γ' : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c)) ≠ 0 := by
      rw [KS.MM.relIdx_map]; exact hr2
    have hSB' := KS.MM.semiChar_map (HV A.sc) (HV A.sc) (TI.RV A γ γ') hIso (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c) (alV A.d A.sc) (alV A.d A.sc) hα hSc.2.2.1
    have hfix' := KS.MM.fixedBy_map (HV A.sc) (HV A.sc) (TI.RV A γ γ') hIso (LamC (X.embC A.σ₀) A.δ A.AA N N') (alV A.d A.sc) (alV A.d A.sc) hα
      (A.e a b N N') (A.e a b (gmap γ.1 N) (gmap γ'.1 N')) he hθ
    rw [sumU_eq_inter hSc.1 hSB' hfix' (repsOf_spec _ _ hr2') hr2' ((TI.RV A γ γ') v), sumU_eq_inter hSc.1 hSc.2.2.1 hθ (repsOf_spec _ _ hr2) hr2 v,
      KS.MM.inter_map (HV A.sc) (HV A.sc) hSc.1 hSc.1 (TI.RV A γ γ') hIso (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA Sall N N' c) (alV A.d A.sc) (alV A.d A.sc) hα hSc.2.2.1 hr2
        (A.e a b N N') (A.e a b (gmap γ.1 N) (gmap γ'.1 N')) he hθ v, KS.MM.relIdx_map]
  rw [hcard, hemb, hα, ← map_neg (TI.RV A γ γ'),
    KS.MM.opU_map (HV A.sc) (HV A.sc) (TI.RV A γ γ') hIso _ _ hsum]

end Formalism.L2.Ker
