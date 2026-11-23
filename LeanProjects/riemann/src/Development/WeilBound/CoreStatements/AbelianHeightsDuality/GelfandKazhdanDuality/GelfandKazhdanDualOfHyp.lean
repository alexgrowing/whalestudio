import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.PairingL2
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotPairedId
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothConjugateInverseMemStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalEqTwistNormalisedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAllStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugateInverseRightActionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormConjugateInverseStatement
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.LieSkew
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.UnitarisableLocalReps.IsUnitarisableLocRep

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open scoped InnerProductSpace

namespace PositivityTheory.PRW.GKD

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

def dualMapC : Sm E a →ₗ⋆[ℂ] Sm E a where
  toFun φ := ⟨fun g => star (φ.1 (invA E a g)), GlobalTheory.T.smooth_conjugate_inverse_mem φ.2⟩
  map_add' φ ψ := Subtype.ext (funext fun g => by simp)
  map_smul' c φ := Subtype.ext (funext fun g => by simp)

theorem dualMapC_dualMapC (φ : Sm E a) : dualMapC E a (dualMapC E a φ) = φ :=
  Subtype.ext (funext fun g => by simp [dualMapC, invA_invA])

theorem act_dualMapC (o : Op E a) (φ : Sm E a) : act o (dualMapC E a φ) = dualMapC E a (act (invTOp o) φ) :=
  GlobalTheory.T.conjugate_inverse_right_action o φ _ _

theorem isCuspForm_dualMapC {φ : Sm E a} (h : IsCuspForm φ) : IsCuspForm (dualMapC E a φ) :=
  GlobalTheory.T.cuspForm_conjugate_inverse φ _ h

theorem dualMapC_injective : Function.Injective (dualMapC E a) := fun φ ψ h => by
  rw [← dualMapC_dualMapC φ, ← dualMapC_dualMapC ψ, h]

theorem dualMapC_surjective : Function.Surjective (dualMapC E a) := fun φ => ⟨dualMapC E a φ, dualMapC_dualMapC φ⟩

def dualSubC (π : CuspSub E a) : CuspSub E a where
  V := π.V.map (dualMapC E a)
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact isCuspForm_dualMapC (π.cusp φ hφ)
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, π.stable (invTOp o) φ hφ, (act_dualMapC o φ).symm⟩
  ne_bot h := π.ne_bot (by
    rw [eq_bot_iff]
    intro φ hφ
    have h1 : dualMapC E a φ ∈ (⊥ : Submodule ℂ (Sm E a)) := h ▸ ⟨φ, hφ, rfl⟩
    rw [Submodule.mem_bot] at h1 ⊢
    exact dualMapC_injective (h1.trans (map_zero _).symm))
  irred W hW hs := by
    have h := π.irred (W.comap (dualMapC E a)) (fun φ hφ => by
        obtain ⟨ψ, h1, h2⟩ := hW hφ
        rwa [← dualMapC_injective h2]) fun o φ hφ => by
      have h1 := hs (invTOp o) _ hφ
      rw [act_dualMapC, GlobalTheory.CsdBack.invTOp_involutive o] at h1
      exact h1
    have e := Submodule.map_comap_eq_of_surjective dualMapC_surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

theorem paired_of_dualSubC_eq (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : IsNormalised π)
    (h : (dualSubC π).V = π.V) : Paired π π invTOp := by
  obtain ⟨μ, hμ⟩ := exists_haar_GA (E := E) (a := a)
  have : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  set hL := memL2_normalised_cusp_form hB μ hπ
  set u := toL2ₗ μ π.V hL
  have hJ : ∀ ψ : π.V, dualMapC E a ψ.1 ∈ π.V := fun ψ => by
    have h1 : dualMapC E a ψ.1 ∈ (dualSubC π).V := ⟨ψ.1, ψ.2, rfl⟩
    rwa [h] at h1
  let J : π.V → π.V := fun ψ => ⟨dualMapC E a ψ.1, hJ ψ⟩
  have JJ : ∀ ψ, J (J ψ) = ψ := fun ψ => Subtype.ext (dualMapC_dualMapC ψ.1)
  have Jadd : ∀ ψ ψ', J (ψ + ψ') = J ψ + J ψ' := fun ψ ψ' => Subtype.ext (map_add (dualMapC E a) ψ.1 ψ'.1)
  have Jsmul : ∀ (c : ℂ) ψ, J (c • ψ) = (starRingEnd ℂ c) • J ψ := fun c ψ =>
    Subtype.ext (LinearMap.map_smulₛₗ (dualMapC E a) c ψ.1)
  have Jop : ∀ o ψ, J (π.op (invTOp o) ψ) = π.op o (J ψ) := fun o ψ =>
    Subtype.ext (act_dualMapC o ψ.1).symm
  have uR : ∀ (g : GA E a) (x : π.V) (hg : rt E a g x.1 ∈ π.V),
      u ⟨_, hg⟩ = R (latticeGL E a) μ g (u x) := fun g x hg => (R_toL2ₗ hL x hg).symm
  have ufin : ∀ (k : GL (Fin a) (Af E)) (x : π.V), u (π.op (.fin k) x) = R (latticeGL E a) μ (finGL E a k) (u x) :=
    fun k x => (R_toL2ₗ hL x (π.stable (.fin k) x.1 x.2)).symm
  have ucpt : ∀ (k : Kinf E a) (x : π.V),
      u (π.op (.cpt k) x) = R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (u x) :=
    fun k x => (R_toL2ₗ hL x (π.stable (.cpt k) x.1 x.2)).symm
  have hinj : Function.Injective u := toL2ₗ_injective hL continuous_of_mem
  let B : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun φ ψ => ⟪u (J ψ), u φ⟫_ℂ)
    (fun φ φ' ψ => by simp only [map_add, inner_add_right])
    (fun c φ ψ => by simp only [map_smul, inner_smul_right, smul_eq_mul])
    (fun φ ψ ψ' => by simp only [Jadd, map_add, inner_add_left])
    (fun c φ ψ => by simp only [Jsmul, map_smul, inner_smul_left, RingHomCompTriple.comp_apply, RingHom.id_apply,
      smul_eq_mul])
  have hB' : ∀ φ ψ, B φ ψ = ⟪u (J ψ), u φ⟫_ℂ := fun _ _ => rfl
  have hself : ∀ x : π.V, ⟪u x, u x⟫_ℂ = 0 → x = 0 := fun x hx =>
    hinj ((inner_self_eq_zero.1 hx).trans (map_zero u).symm)
  refine ⟨B, fun φ hφ => hself φ (by simpa [hB', JJ] using hφ (J φ)), fun ψ hψ => ?_, fun k φ ψ => ?_,
    fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · have h1 := hself (J ψ) (by simpa [hB'] using hψ (J ψ))
    rw [← JJ ψ, h1]
    exact Subtype.ext (by simp [J])
  · rw [hB', hB', Jop, ufin, ufin]
    exact inner_R μ _ _ _
  · rw [hB', hB', Jop, ucpt, ucpt]
    exact inner_R μ _ _ _
  · rw [hB', hB', Jop, add_comm]
    exact inner_lie_skew' hB μ hπ X (J ψ) φ

theorem dualSubC_V_eq (hJ : GlobalTheory.Published.JacquetShalikaRigidity) (hM : GlobalTheory.Published.CuspidalMultiplicityOne)
    (hB : GlobalTheory.Published.CuspFormsBoundedGL) (ha : 1 ≤ a) {π : CuspSub E a} (hπ : IsNormalised π) : (dualSubC π).V = π.V := by
  refine hM E a (dualSubC π) π ?_
  obtain ⟨s, hs⟩ := hJ E Unit Unit (fun _ => a) (fun _ => a) (fun _ => CG.mk (dualSubC π)) (fun _ => CG.mk π)
    (fun _ => ha) (fun _ => ha) (by
      filter_upwards [GlobalTheory.T.cuspidal_satake_almost_all π] with w hw
      obtain ⟨B, hw⟩ := hw
      exact ⟨fun _ => B, fun _ => B, fun _ => PositivityTheory.PRW.SatakeDual.hasSat_dual hB hπ (dualSubC π) (fun ψ => ⟨fun ⟨φ, hφ, e⟩ => ⟨φ, hφ, e ▸ rfl⟩,
        fun ⟨φ, hφ, e⟩ => ⟨φ, hφ, Subtype.ext e.symm⟩⟩) w B hw, fun _ => hw, rfl⟩)
  exact eq_of_heq (Sigma.mk.inj_iff.1 (hs ())).2

theorem gelfandKazhdanDual_of_multiplicityOne (hJ : GlobalTheory.Published.JacquetShalikaRigidity) (hM : GlobalTheory.Published.CuspidalMultiplicityOne)
    (hB : GlobalTheory.Published.CuspFormsBoundedGL) : GlobalTheory.Published.GelfandKazhdanDual := by
  intro E _ _ _ n π
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact GlobalTheory.Published.InvTransposeModel.rank_zero π
  obtain ⟨π₀, χ, h0, rfl⟩ := GlobalTheory.T.cuspidal_eq_twist_normalised π
  exact GlobalTheory.Published.InvTransposeModel.twist (paired_of_dualSubC_eq hB h0 (dualSubC_V_eq hJ hM hB hn h0)) χ

end PositivityTheory.PRW.GKD

end
