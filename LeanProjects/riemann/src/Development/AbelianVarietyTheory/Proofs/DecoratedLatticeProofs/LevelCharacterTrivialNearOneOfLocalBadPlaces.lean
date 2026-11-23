import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

noncomputable section
namespace GlobalTheory.ChiCont

theorem chi_eq_one_of_split {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F)))
    (S : StepLevel F E σ J T f bad) (u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (s : Finset (HeightOneSpectrum (𝓞 F)))
    (H : ∀ v ∈ s, ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := E) v') x.1 = 1) →
      bc (prV (E := E) v) x.1 = bc (prV (E := E) v) u → S.chi x = 1) :
    ∀ κ : S.U, (∀ v ∈ s, bc (prV (E := E) v) κ.1 = bc (prV (E := E) v) u) →
      (∀ v ∈ bad, v ∉ s → bc (prV (E := E) v) κ.1 = 1) → S.chi κ = 1 := by
  induction s using Finset.induction_on with
  | empty =>
    intro κ _ hb
    exact S.chi_triv κ (fun v hv => hb v hv (Finset.notMem_empty v))
  | @insert v s hvs ih =>
    intro κ hu hb
    have hκ := (S.U_eq κ.1).1 κ.2
    set x0 := Formalism.UG.P.afsplitU v (bc (prV (E := E) v) κ.1) 1 with hx0
    have hx0v : bc (prV (E := E) v) x0 = bc (prV (E := E) v) κ.1 := Formalism.UG.P.afsplit_right1 _ _ _
    have hx0w : ∀ w, w ≠ v → bc (prV (E := E) w) x0 = 1 := by
      intro w hw
      apply Units.ext
      rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw]
      simp
    have hx0U : x0 ∈ S.U := by
      rw [S.U_eq]
      refine ⟨Formalism.UG.P.afsplitU_mem v _ _ _ _ (Formalism.UG.P.afsplit_bc_mem _ _ v κ.1 hκ.1) (one_mem _), fun w => ?_⟩
      by_cases hw : w = v
      · subst hw
        rw [hx0v]
        exact hκ.2 w
      · rw [hx0w w hw]
        exact one_mem _
    let x : S.U := ⟨x0, hx0U⟩
    have hchix : S.chi x = 1 :=
      H v (Finset.mem_insert_self v s) x hx0w (by rw [hx0v]; exact hu v (Finset.mem_insert_self v s))
    let κ' : S.U := x⁻¹ * κ
    have hκ'w : ∀ w, w ≠ v → bc (prV (E := E) w) κ'.1 = bc (prV (E := E) w) κ.1 := by
      intro w hw
      show bc (prV (E := E) w) (x0⁻¹ * κ.1) = _
      rw [map_mul, map_inv, hx0w w hw, inv_one, one_mul]
    have hκ'v : bc (prV (E := E) v) κ'.1 = 1 := by
      show bc (prV (E := E) v) (x0⁻¹ * κ.1) = _
      rw [map_mul, map_inv, hx0v, inv_mul_cancel]
    have hchi' : S.chi κ' = 1 := by
      refine ih (fun w hw => H w (Finset.mem_insert_of_mem hw)) κ' ?_ ?_
      · intro w hw
        have hwv : w ≠ v := fun h => hvs (h ▸ hw)
        rw [hκ'w w hwv]
        exact hu w (Finset.mem_insert_of_mem hw)
      · intro w hw hws
        by_cases hwv : w = v
        · subst hwv; exact hκ'v
        · rw [hκ'w w hwv]
          exact hb w hw (by simp [hwv, hws])
    have hk : κ = x * κ' := by rw [mul_inv_cancel_left]
    rw [hk, map_mul, hchix, hchi', one_mul]

theorem main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Vs : Set (HeightOneSpectrum (𝓞 F))), Vs.Finite → (∀ v ∈ bad, v ∈ Vs) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); ∀ v ∈ Vs, ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := E) v') x.1 = 1) → bc (prV (E := E) v) x.1 = bc (prV (E := E) v) u → S.chi x = 1) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ κ : S.U, κ.1 = u → S.chi κ = 1) := by
  intro F E _ _ _ _ _ σ n J T f bad S Vs hVs hbad hloc
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  have hall : ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ v ∈ Vs,
      ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := E) v') x.1 = 1) →
        bc (prV (E := E) v) x.1 = bc (prV (E := E) v) u → S.chi x = 1 :=
    (Filter.eventually_all_finite hVs).2 hloc
  filter_upwards [hall] with u hu κ hκu
  refine chi_eq_one_of_split σ J T f bad S u hVs.toFinset
    (fun v hv => hu v (hVs.mem_toFinset.1 hv)) κ (fun v _ => by rw [hκu]) ?_
  intro v hv hvs
  exact absurd (hVs.mem_toFinset.2 (hbad v hv)) hvs

end GlobalTheory.ChiCont
