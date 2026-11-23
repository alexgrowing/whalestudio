import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftECompFinOfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLiftV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLiftEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalNormsOfLiftUFEq

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal

theorem locChr_exists (hC : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F), Continuous (GlobalTheory.HoweLocal.liftU (F := F) (E := E) v)) (hN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (z : (Fv F v ⊗[F] E)ˣ), Units.map (Algebra.norm (AF F) : AE F E →* AF F) (GlobalTheory.HoweLocal.liftU v z) = GlobalTheory.HoweLocal.liftUF v (Units.map (Algebra.norm (Fv F v) : Fv F v ⊗[F] E →* Fv F v) z)) (hQ : GlobalTheory.Published.QuadraticClassFieldTheory → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ (v : Pl F) (a : (Fv F v)ˣ) (t : Fˣ) (z : (AE F E)ˣ), GlobalTheory.HoweLocal.liftUF v a = Units.map (algebraMap F (AF F)).toMonoidHom t * Units.map (Algebra.norm (AF F) : AE F E →* AF F) z → a ∈ (Units.map (Algebra.norm (Fv F v) : Fv F v ⊗[F] E →* Fv F v)).range) : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (m : ℕ) (χ : Chr F E), IsHecke F E χ →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
        ∃ χv : (Fv F v ⊗[F] E)ˣ →* Circle, Continuous χv ∧ ResEtaPow (R := Fv F v) ⊥ χv m ∧ GlobalTheory.HoweLocal.IsLocChr χ v χv := by
  intro hP F E _ _ _ _ _ σ hcm m χ hχ hres v _
  refine ⟨locChr χ v, hχ.1.comp (hC F E v), ?_, ?_⟩
  · intro a
    change ((χ (liftU v (Units.map (algebraMap (Fv F v) (Fv F v ⊗[F] E) : Fv F v →* Fv F v ⊗[F] E) a)) : Circle) : ℂ) = _
    rw [liftU_algebraMap]
    have h := hres (liftUF v a)
    simp only [RingHom.toMonoidHom_eq_coe] at h ⊢
    rw [h]
    congr 1
    apply propext
    rw [bot_sup_eq]
    constructor
    · intro hm
      obtain ⟨y, hy, n, hn, hyn⟩ := Subgroup.mem_sup.1 hm
      obtain ⟨t, rfl⟩ := hy
      obtain ⟨z, rfl⟩ := hn
      exact hQ hP.quadraticClassFieldTheory F E hcm.2.2.1 v a t z hyn.symm
    · rintro ⟨z, rfl⟩
      exact Subgroup.mem_sup_right ⟨liftU v z, hN F E v z⟩
  · intro a ha
    change χ (liftU v _) = χ a
    rw [liftU_compFin_of_at v a ha]

theorem exists_locChr_of_resEtaPow : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (m : ℕ) (χ : Chr F E), IsHecke F E χ →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
        ∃ χv : (Fv F v ⊗[F] E)ˣ →* Circle, Continuous χv ∧ ResEtaPow (R := Fv F v) ⊥ χv m ∧ GlobalTheory.HoweLocal.IsLocChr χ v χv :=
  locChr_exists GlobalTheory.HoweLocal.continuous_liftU GlobalTheory.HoweLocal.NormLift.norm_liftU GlobalTheory.HoweLocal.mem_localNorms_of_liftUF_eq

end GlobalTheory.HoweLocal
