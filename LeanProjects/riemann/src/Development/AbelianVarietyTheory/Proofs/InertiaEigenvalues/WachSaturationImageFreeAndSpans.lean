import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSatMOfSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAndDecompletion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeFreeOfCrystalline

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.SatFree

theorem isBaseChange_between (A E : Type) [CommRing A] [CommRing E] [Algebra A E]
    [Module.Flat A E] (D₁ D₂ : Type) [AddCommGroup D₁] [AddCommGroup D₂]
    [Module E D₁] [Module E D₂] [Module A D₁] [Module A D₂]
    [IsScalarTower A E D₁] [IsScalarTower A E D₂]
    (q : D₁ →ₗ[E] D₂) (hq : Function.Surjective q) (N₁ : Submodule A D₁) (N₂ : Submodule A D₂)
    (h₁ : IsBaseChange E N₁.subtype) (h₂ : IsBaseChange E N₂.subtype)
    (S : Submodule A D₂) (hS : S ≤ N₂) (hqS : ∀ x ∈ N₁, q x ∈ S) :
    IsBaseChange E S.subtype := by
  let i : S →ₗ[A] N₂ := Submodule.inclusion hS
  have hi : Function.Injective i := Submodule.inclusion_injective hS
  have hiT : Function.Injective (LinearMap.lTensor E i) :=
    Module.Flat.lTensor_preserves_injective_linearMap i hi
  let Φ : E ⊗[A] S →ₗ[E] D₂ := S.subtype.liftBaseChange E
  have hcomm : ∀ t : E ⊗[A] S, Φ t = h₂.equiv (LinearMap.lTensor E i t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [Φ, IsBaseChange.equiv_tmul, i]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hΦi : Function.Injective Φ := by
    intro s t hst
    apply hiT
    apply h₂.equiv.injective
    rw [← hcomm, ← hcomm, hst]
  have hΦs : Function.Surjective Φ := by
    intro d
    obtain ⟨x, rfl⟩ := hq d
    have : q x ∈ LinearMap.range Φ := by
      refine h₁.inductionOn x (fun x => q x ∈ LinearMap.range Φ) (by simp) ?_ ?_ ?_
      · intro m
        refine ⟨1 ⊗ₜ ⟨q m, hqS m m.2⟩, ?_⟩
        simp [Φ, LinearMap.liftBaseChange_tmul]
      · intro e y hy
        rw [map_smul]
        exact (LinearMap.range Φ).smul_mem e hy
      · intro a b ha hb
        rw [map_add]
        exact (LinearMap.range Φ).add_mem ha hb
    exact this
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ ⟨hΦi, hΦs⟩) ?_
  intro x
  show Φ (1 ⊗ₜ x) = x
  simp [Φ, LinearMap.liftBaseChange_tmul]

theorem freeA_of_basis {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp]
    [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T)) {r : ℕ}
    (b : Module.Basis (Fin r) (LetA O n) S) : FreeA W T S := by
  refine ⟨r, fun j => (b j : W.DD T), fun j => (b j).2, fun x hx => ?_⟩
  refine ⟨b.equivFun ⟨x, hx⟩, ?_, ?_⟩
  · have h2 : ((⟨x, hx⟩ : S) : W.DD T) = ((∑ j, b.equivFun ⟨x, hx⟩ j • b j : S) : W.DD T) := by
      rw [b.sum_equivFun]
    rw [Submodule.coe_sum] at h2
    simpa only [Submodule.coe_smul] using h2
  · intro a ha
    have : (⟨x, hx⟩ : S) = ∑ j, a j • b j := by
      apply Subtype.ext
      simpa using ha
    rw [this, ← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.NL.SatFree

namespace GlobalTheory.NL.SatFree

set_option maxHeartbeats 1600000 in

theorem satM_free_loc {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K : FinExt l)
    (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L)
    (c1 : IsCrys (P.PD K) T₁.ρ) (c2 : IsCrys (P.PD K) T₂.ρ)
    (hsurj : Function.Surjective ((H.W K s LL h).map π))
    (hflat : Module.Flat (AA K LL) (H.W K s LL h).EE) :
    FreeA (H.W K s LL h) T₂ (GlobalTheory.NL.Coker.satM l (((H.W K s LL h).N T₁).map (mapA (H.W K s LL h) π))
      ((H.W K s LL h).N T₂)) ∧
    IsBaseChange (H.W K s LL h).EE (GlobalTheory.NL.Coker.satM l (((H.W K s LL h).N T₁).map
      (mapA (H.W K s LL h) π)) ((H.W K s LL h).N T₂)).subtype := by
  obtain ⟨_, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hproj := H.W_proj K s LL h T₂
  generalize H.W K s LL h = W at hproj hsurj hflat ⊢
  set S := GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂) with hSdef
  have hSN : S ≤ W.N T₂ := GlobalTheory.NL.Coker.satM_le _ _ _
  have hbc : IsBaseChange W.EE S.subtype := by
    refine isBaseChange_between (AA K LL) W.EE (W.DD T₁) (W.DD T₂) (W.map π) hsurj (W.N T₁) (W.N T₂)
      (W.N_base T₁ c1) (W.N_base T₂ c2) S hSN ?_
    intro x hx
    exact GlobalTheory.NL.Coker.le_satM l (fun y hy => by
      obtain ⟨z, hz, rfl⟩ := hy
      exact W.map_N π c1 c2 z hz) ⟨x, hx, rfl⟩
  refine ⟨?_, hbc⟩
  obtain ⟨hfree, hrk⟩ := W.DD_free T₂
  haveI : Module.Finite (AA K LL) ↥(W.N T₂) := Module.Finite.iff_fg.mpr (W.N_fg T₂)
  haveI hR : IsNoetherianRing (PowerSeries ↥(OL LL)) := inferInstance
  haveI hA : IsNoetherianRing (AA K LL) :=
    isNoetherian_of_tower (PowerSeries ↥(OL LL)) (isNoetherian_pi' (R := PowerSeries ↥(OL LL)))
  haveI hNn : IsNoetherian (AA K LL) ↥(W.N T₂) :=
    isNoetherian_of_isNoetherianRing_of_finite (AA K LL) ↥(W.N T₂)
  haveI : Module.Finite (AA K LL) ↥S :=
    Module.Finite.iff_fg.mpr (isNoetherian_submodule.mp hNn S hSN)
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  have hreg : ∀ u v : W.DD T₂, (letπ : AA K LL) • u = (letπ : AA K LL) • v → u = v := by
    intro u v h1
    rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE (letπ : AA K LL) v] at h1
    exact W.EE_π.smul_left_cancel.mp h1
  have hlC : ((l : ℕ) : AA K LL) = fun _ => PowerSeries.C ((l : ℕ) : ↥(OL LL)) := by
    funext i
    simp
  have hX : IsSMulRegular ↥S (fun _ => PowerSeries.X : AA K LL) := by
    intro x y hxy
    exact Subtype.ext (hreg _ _ (congrArg Subtype.val hxy))
  have hC : ∀ x y : ↥S, (fun _ => PowerSeries.C ((l : ℕ) : ↥(OL LL)) : AA K LL) • x =
      (fun _ => PowerSeries.X : AA K LL) • y → ∃ z : ↥S, x = (fun _ => PowerSeries.X : AA K LL) • z := by
    intro x y hxy
    have e1 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (PowerSeries.C ((l : ℕ) : ℤ_[l])) =
        fun _ => PowerSeries.C ((l : ℕ) : ↥(OL LL)) := by
      funext i
      simp
    have e2 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) PowerSeries.X = fun _ => PowerSeries.X := by
      funext i
      simp [zlA]
    let x' : ↥(W.N T₂) := ⟨x, hSN x.2⟩
    let y' : ↥(W.N T₂) := ⟨y, hSN y.2⟩
    have hxy' : (fun _ => PowerSeries.C ((l : ℕ) : ↥(OL LL)) : AA K LL) • x' =
        (fun _ => PowerSeries.X : AA K LL) • y' := by
      apply Subtype.ext
      change _ • (x : W.DD T₂) = _ • (y : W.DD T₂)
      exact congrArg Subtype.val hxy
    obtain ⟨z, hz⟩ := GlobalTheory.HWL.mem_smul_of_projective_comp _ hproj ((l : ℕ) : ℤ_[l])
      (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) e1 e2 x' y' hxy'
    have hzx : (letπ : AA K LL) • (z : W.DD T₂) = (x : W.DD T₂) := (congrArg Subtype.val hz).symm
    have hzy : ((l : ℕ) : AA K LL) • (z : W.DD T₂) = (y : W.DD T₂) := by
      apply hreg
      rw [smul_comm, hzx, hlC]
      exact congrArg Subtype.val hxy
    have hzS : (z : W.DD T₂) ∈ S := by
      refine GlobalTheory.NL.Coker.mem_satM_of_smul z.2 ?_ ?_
      · rw [hzy]; exact y.2
      · rw [hzx]; exact x.2
    exact ⟨⟨z, hzS⟩, Subtype.ext hzx.symm⟩
  obtain ⟨b⟩ := GlobalTheory.WachFree.basis_of_regular (ι := ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    (O := ↥(OL LL)) (N := ↥S) (E := W.EE) (D := W.DD T₂) W.EE_inj S.subtype hbc
    ((l : ℕ) : ↥(OL LL)) hl0 hl hX hC
  exact freeA_of_basis W T₂ S b

end GlobalTheory.NL.SatFree

namespace GlobalTheory.NL.SatFree

theorem satM_free_and_spans : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → Module.Flat (AA K LL) W.EE → FreeA W T₂ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧ IsBaseChange W.EE (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).subtype := by
  intro D HW F l _ K s LL h W T₀ T₁ T₂ ι π _ c1 c2 hses hflat
  have hex : Function.Injective (((HW l).W K s LL h).map ι) ∧
      Function.Exact (((HW l).W K s LL h).map ι) (((HW l).W K s LL h).map π) ∧
      Function.Surjective (((HW l).W K s LL h).map π) :=
    GlobalTheory.EtaleExact.DD_exact D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h
      T₀ T₁ T₂ ι π hses
  exact satM_free_loc (HW l) K s LL h T₁ T₂ π c1 c2 hex.2.2 hflat

end GlobalTheory.NL.SatFree
