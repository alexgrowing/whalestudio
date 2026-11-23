import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt

noncomputable section

namespace GlobalTheory.LevelSplit

open scoped Matrix
open GlobalTheory.WeilM

section Alg

variable {R : Type} [CommRing R] {B : Type} [Ring B] [Algebra R B]

theorem comp_mul_mid {e : R} (he : e * e = e) (X J Y : B) :
    (e • (X - 1) + 1) * J * (e • (Y - 1) + 1) = e • (X * J * Y - J) + J := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, he, one_mul, mul_one, sub_mul, mul_sub,
    smul_add, smul_sub]
  abel

theorem comp_mul {e : R} (he : e * e = e) (X Y : B) :
    (e • (X - 1) + 1) * (e • (Y - 1) + 1) = e • (X * Y - 1) + 1 := by
  simpa only [mul_one] using comp_mul_mid he X 1 Y

theorem comp_split {e : R} (he : e * e = e) (X : B) : (e • (X - 1) + 1) * ((1 - e) • (X - 1) + 1) = X := by
  have h : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, h, zero_smul, zero_add, mul_one, one_mul,
    ← add_assoc, ← add_smul, add_sub_cancel, one_smul, sub_add_cancel]

theorem comp_comm {e : R} (he : e * e = e) (X Y : B) (hY : e • (Y - 1) = Y - 1) :
    ((1 - e) • (X - 1) + 1) * Y = Y * ((1 - e) • (X - 1) + 1) := by
  have h : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h' : e * (1 - e) = 0 := by rw [mul_comm, h]
  have h1 : ((1 - e) • (X - 1)) * (Y - 1) = 0 := by
    rw [← hY, smul_mul_assoc, mul_smul_comm, smul_smul, h, zero_smul]
  have h2 : (Y - 1) * ((1 - e) • (X - 1)) = 0 := by
    rw [← hY, smul_mul_assoc, mul_smul_comm, smul_smul, h', zero_smul]
  rw [mul_sub, mul_one, sub_eq_zero] at h1
  rw [sub_mul, one_mul, sub_eq_zero] at h2
  rw [add_mul, mul_add, h1, h2, one_mul, mul_one]

end Alg

section Grp

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A] {c : A →ₐ[R] A}
  {ι : Type} [Fintype ι] [DecidableEq ι] {J : Matrix ι ι A}

def comp {e : R} (he : e * e = e) (g : UG c J) : UG c J :=
  ⟨⟨e • ((g.1 : Matrix ι ι A) - 1) + 1, e • (((g.1⁻¹ : GL ι A) : Matrix ι ι A) - 1) + 1,
    by rw [comp_mul he, Units.mul_inv, sub_self, smul_zero, zero_add],
    by rw [comp_mul he, Units.inv_mul, sub_self, smul_zero, zero_add]⟩, by
    have hg : (g.1 : Matrix ι ι A)ᵀ * J * (g.1 : Matrix ι ι A).map c = J := g.2
    show (e • ((g.1 : Matrix ι ι A) - 1) + 1)ᵀ * J * (e • ((g.1 : Matrix ι ι A) - 1) + 1).map c = J
    have h1 : (e • ((g.1 : Matrix ι ι A) - 1) + 1).map c = e • ((g.1 : Matrix ι ι A).map c - 1) + 1 := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [h1, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_one,
      comp_mul_mid he, hg, sub_self, smul_zero, zero_add]⟩

theorem comp_one {e : R} (he : e * e = e) : comp he (1 : UG c J) = 1 :=
  Subtype.ext (Units.ext (show e • ((1 : Matrix ι ι A) - 1) + 1 = 1 by rw [sub_self, smul_zero, zero_add]))

theorem continuous_comp [TopologicalSpace A] [IsTopologicalRing A] {e : R} (he : e * e = e) :
    Continuous (comp (c := c) (J := J) he) := by
  haveI : ContinuousConstSMul R A := ⟨fun r => by
    simpa only [Algebra.smul_def] using continuous_const_mul (algebraMap R A r)⟩
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (((Units.continuous_val.comp continuous_subtype_val).sub continuous_const).const_smul e).add continuous_const
  · exact (((Units.continuous_coe_inv.comp continuous_subtype_val).sub continuous_const).const_smul e).add
      continuous_const

end Grp

end GlobalTheory.LevelSplit

namespace GlobalTheory

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct Topology

theorem isLevel_closure_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (L K : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)), GlobalTheory.ThKAdm.IsLevel W L → (∀ g ∈ K, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (GlobalTheory.AdelicU.evFin F v)) → (∃ O : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J), IsOpen O ∧ (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J) ∈ O ∧ ∀ g ∈ O, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (GlobalTheory.AdelicU.evFin F v) → g ∈ K) → GlobalTheory.ThKAdm.IsLevel W (Subgroup.closure ((K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)) ∪ {l | l ∈ L ∧ ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (GlobalTheory.AdelicU.evFin F v), l * h = h * l})) := by
  intro F E _ _ _ _ _ σ d W v L K hL hK ⟨O, hO, hO1, hOK⟩
  obtain ⟨hLf, U, hU, hU1, hUL⟩ := hL
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  set e : AF F := GlobalTheory.LatVac.liftV v 1 with he_def
  have he : e * e = e := by
    have h := partFin_of_at (at_partFin v (1 : AF F))
    simpa only [partFin, smul_eq_mul, mul_one] using h
  have he' : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  refine ⟨?_, LevelSplit.comp he ⁻¹' O ∩ LevelSplit.comp he' ⁻¹' U, ?_, ⟨?_, ?_⟩, ?_⟩
  · refine (Subgroup.closure_le (UAtSub σ W (fun a : AF F => a.2))).2 ?_
    rintro g (hg | hg)
    · intro u hu
      refine hK g hg u ?_
      show evalV F v u.2 = 0
      rw [show u.2 = 0 from hu, map_zero]
    · exact hLf hg.1
  · exact (hO.preimage (LevelSplit.continuous_comp he)).inter (hU.preimage (LevelSplit.continuous_comp he'))
  · show LevelSplit.comp he 1 ∈ O
    rwa [LevelSplit.comp_one]
  · show LevelSplit.comp he' 1 ∈ U
    rwa [LevelSplit.comp_one]
  · rintro g ⟨⟨hg1, hg2⟩, hg⟩
    have m1 : mat (LevelSplit.comp he g) = e • (mat g - 1) + 1 := rfl
    have m2 : mat (LevelSplit.comp he' g) = (1 - e) • (mat g - 1) + 1 := rfl
    have hs : g = LevelSplit.comp he g * LevelSplit.comp he' g :=
      Subtype.ext (Units.ext (LevelSplit.comp_split he (mat g)).symm)
    rw [hs]
    refine mul_mem (Subgroup.subset_closure (Or.inl (hOK _ hg1 ?_)))
      (Subgroup.subset_closure (Or.inr ⟨hUL ⟨hg2, ?_⟩, fun h hh => ?_⟩))
    · show At (evFin F v) (mat (LevelSplit.comp he g) - 1)
      rw [m1, add_sub_cancel_right]
      exact at_partFin v _
    · intro u hu
      rw [m2, add_sub_cancel_right, smul_comm, hg u hu, smul_zero]
    · exact Subtype.ext (Units.ext (LevelSplit.comp_comm he (mat g) (mat h) (partFin_of_at hh)))

end GlobalTheory

end
