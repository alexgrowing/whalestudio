import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAndDecompletion

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.WachKernel

set_option maxHeartbeats 1600000 in

theorem kernel_freeA : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → IsBaseChange W.EE ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))).subtype → FreeA W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))) := by
  intro D HW F l _ K s LL h W T₀ T₁ T₂ ι π h0 h1 h2 hses hbc
  obtain ⟨hinj, hex, -⟩ := GlobalTheory.EtaleExact.DD_exact D HW F
    (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h T₀ T₁ T₂ ι π hses
  obtain ⟨_, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hproj := (HW l).W_proj K s LL h T₁
  set N₀ := (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)) with hN₀
  haveI : Module.Free W.EE (W.DD T₀) := (W.DD_free T₀).1
  haveI : IsNoetherianRing ↥(OL LL) := inferInstance
  haveI : IsNoetherianRing (PowerSeries ↥(OL LL)) := inferInstance
  haveI : IsNoetherianRing (AA K LL) :=
    inferInstanceAs (IsNoetherianRing (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)))
  haveI : Module.Finite (AA K LL) ↥(W.N T₁) := Module.Finite.iff_fg.mpr (W.N_fg T₁)
  have hfin : Module.Finite (AA K LL) ↥N₀ := by
    let g : ↥N₀ →ₗ[AA K LL] ↥(W.N T₁) :=
      ((W.map ι).restrictScalars (AA K LL)).restrict (fun x hx => hx)
    haveI : IsNoetherian (AA K LL) ↥(W.N T₁) := isNoetherian_of_isNoetherianRing_of_finite _ _
    exact Module.Finite.of_injective g fun a b hab =>
      Subtype.ext (hinj (congrArg Subtype.val hab))
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  have hX : IsSMulRegular ↥N₀ (fun _ => X : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) := by
    intro x y hxy
    have h1 : (letπ : AA K LL) • (x : W.DD T₀) = (letπ : AA K LL) • (y : W.DD T₀) :=
      congrArg Subtype.val hxy
    rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE letπ (y : W.DD T₀)] at h1
    exact Subtype.ext (W.EE_π.smul_left_cancel.mp h1)
  have hreg : ∀ x y : ↥N₀,
      (fun _ => C ((l : ℕ) : ↥(OL LL)) : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) • x =
        (fun _ => X : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) • y →
      ∃ z : ↥N₀, x = (fun _ => X : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) • z := by
    intro x y hxy
    have hinj : Function.Injective (W.map ι) := hinj
    have hex : Function.Exact (W.map ι) (W.map π) := hex
    let mA := (W.map ι).restrictScalars (AA K LL)
    let x' : ↥(W.N T₁) := ⟨mA x, x.2⟩
    let y' : ↥(W.N T₁) := ⟨mA y, y.2⟩
    have hxy' : (fun _ => C ((l : ℕ) : ↥(OL LL)) : AA K LL) • x' = (fun _ => X : AA K LL) • y' := by
      apply Subtype.ext
      have := congrArg (fun w : ↥N₀ => mA (w : W.DD T₀)) hxy
      simpa only [Submodule.coe_smul, map_smul] using this
    have e1 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (C ((l : ℕ) : ℤ_[l])) =
        fun _ => C ((l : ℕ) : ↥(OL LL)) := by
      funext i
      simp
    have e2 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X = fun _ => X := by
      funext i
      simp [zlA]
    obtain ⟨z, hz⟩ := @GlobalTheory.WachFree.mem_X_smul_of_projective ℤ_[l] ↥(W.N T₁) _ _ _
      (Module.compHom _ (zlA LL (Module.finrank ℚ_[l] ↥(K0 K)))) hproj ((l : ℕ) : ℤ_[l])
      (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) x' y' (by
        change zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (C ((l : ℕ) : ℤ_[l])) • x' =
          zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X • y'
        rw [e1, e2]
        exact hxy')
    change x' = zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X • z at hz
    rw [e2] at hz
    have hz' : mA x = (fun _ => X : AA K LL) • (z : W.DD T₁) := congrArg Subtype.val hz
    have hπz : W.map π (z : W.DD T₁) = 0 := by
      have h0 : W.map π (mA x) = 0 := (hex _).mpr ⟨(x : W.DD T₀), rfl⟩
      rw [hz'] at h0
      have h0' : (letπ : AA K LL) • W.map π (z : W.DD T₁) = (letπ : AA K LL) • 0 := by
        rw [smul_zero]
        have : W.map π ((letπ : AA K LL) • (z : W.DD T₁)) = (letπ : AA K LL) • W.map π (z : W.DD T₁) :=
          ((W.map π).restrictScalars (AA K LL)).map_smul _ _
        rw [← this]
        exact h0
      rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE letπ (0 : W.DD T₂)] at h0'
      exact W.EE_π.smul_left_cancel.mp h0'
    obtain ⟨w, hw⟩ := (hex (z : W.DD T₁)).mp hπz
    have hwN : w ∈ N₀ := by
      show W.map ι w ∈ W.N T₁
      rw [hw]
      exact z.2
    refine ⟨⟨w, hwN⟩, Subtype.ext (hinj ?_)⟩
    change mA x = W.map ι ((fun _ => X : AA K LL) • w)
    rw [hz', ← hw]
    exact (mA.map_smul _ _).symm
  obtain ⟨b⟩ := GlobalTheory.WachFree.basis_of_regular (ι := ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    (O := ↥(OL LL)) (N := ↥N₀) (E := W.EE) (D := W.DD T₀) W.EE_inj N₀.subtype hbc
    ((l : ℕ) : ↥(OL LL)) hl0 hl hX hreg
  refine ⟨Module.finrank W.EE (W.DD T₀), fun j => (b j : W.DD T₀), fun j => (b j).2, fun x hx => ?_⟩
  refine ⟨fun j => b.repr ⟨x, hx⟩ j, ?_, ?_⟩
  · have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using this.symm
  · intro a ha
    have hx' : (⟨x, hx⟩ : ↥N₀) = ∑ j, a j • b j :=
      Subtype.ext (by simpa only [Submodule.coe_sum, Submodule.coe_smul] using ha)
    funext j
    rw [hx', b.repr_sum_self]

end GlobalTheory.WachKernel
