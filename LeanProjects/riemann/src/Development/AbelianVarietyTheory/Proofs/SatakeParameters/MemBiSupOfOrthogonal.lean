import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaEigenspaceMapping
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaLiftOfEachRow
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.InternalDirectSumOfParts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoLocAppendSingleton

noncomputable section

namespace GlobalTheory.DownMemRoad

open Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceMapping GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftOfEachComponent GlobalTheory.IndefiniteRowSideFullHecke.InternalDirectSumCriteria

theorem mem_biSup_of_orthogonal {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : ι → Submodule ℂ V) (S : Set ι) (htop : ⨆ k, U k = ⊤) (horth : ∀ k k', k ≠ k' → U k ⟂ U k')
    {v : V} (hv : ∀ k ∉ S, v ∈ (U k)ᗮ) : v ∈ ⨆ k ∈ S, U k := by
  have hsup : (⨆ k ∈ S, U k) ⊔ (⨆ k ∈ Sᶜ, U k) = ⊤ := by
    rw [← htop]
    exact (iSup_split U (· ∈ S)).symm
  have ho : (⨆ k ∈ S, U k) ⟂ (⨆ k ∈ Sᶜ, U k) := by
    simp only [Submodule.isOrtho_iSup_left, Submodule.isOrtho_iSup_right]
    intro k hk k' hk'
    refine horth _ _ ?_
    rintro rfl
    exact absurd hk' hk
  have hv' : v ∈ (⨆ k ∈ Sᶜ, U k)ᗮ := by
    have h1 : (ℂ ∙ v) ⟂ (⨆ k ∈ Sᶜ, U k) := by
      simp only [Submodule.isOrtho_iSup_right]
      intro k hk
      exact (Submodule.span_singleton_le_iff_mem _ _).2 (hv k hk)
    exact h1 (Submodule.mem_span_singleton_self v)
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hsup.ge (Submodule.mem_top (x := v)))
  have hb' : b ∈ (⨆ k ∈ Sᶜ, U k)ᗮ := by
    have := Submodule.sub_mem _ hv' (ho ha)
    rwa [add_sub_cancel_left] at this
  have hb0 : b = 0 := inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hb' b hb)
  rw [hb0, add_zero]
  exact ha

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem hasParamW_of_thetaOf (hL : ParamLaws N A) {i : N.Loc} (hS : SplitLift N A i)
    (hloc : LocOfPt N A i) {x : N.X i} {Sig : List (Part A.CG)} (hx : HasParamX N A i x Sig)
    {σ : what₂.FT} {P : A.AV i} (hθ : thetaOf N A i σ P) (hP : A.ptV i P = some x) :
    HasParamW N A i σ Sig := by
  obtain ⟨P', hP', h1, -, h3, h4, -⟩ := hx
  refine ⟨fun p hp => ?_, ?_, fun w hw => ?_⟩
  · have := h1 ⟨p.a, A.tw p.π A.etaTinv, p.d⟩
      (List.mem_map.mpr ⟨p, List.mem_append_left _ hp, rfl⟩)
    exact ⟨this.1, this.2.1⟩
  · have e : rankIso N A Sig + R.t = R.nV := by
      rw [← h3]
      simp [rankIso, twistIso, muPart, Function.comp_def]
    have e' : R.nV = R.r + R.t := rfl
    omega
  · have e := hloc P' P x hP' hP w hw
    rw [← h4 w hw, ParUpRoad.isoLoc_lift N A hL, hS σ P hθ w hw] at e
    exact (hL w).2.2.2.2 _ _ _ ((hL w).2.2.2.1 _ _ _ (A.locG_dim _ w) e)

theorem typeV_isOrtho_eigC {i : N.Loc} (hT : TypeOrth N A i) {x : N.X i} {P : A.AV i}
    (hP : A.ptV i P ≠ some x) : A.typeV i P ⟂ eigC N A i x := by
  unfold eigC
  simp only [Submodule.isOrtho_iSup_right]
  intro P' hP'
  refine hT P P' ?_
  rintro rfl
  exact hP hP'

theorem thetaP_mem (hθ : EachRowHasThetaLift N A) (hL : ParamLaws N A) {i : N.Loc}
    (htop : ⨆ σ, what₂.isot (N.j i) σ = ⊤) (hO : PartOrth N i) (hT : TypeOrth N A i)
    (hS : SplitLift N A i) (hloc : LocOfPt N A i) {x : N.X i} {Sig : List (Part A.CG)}
    (hx : HasParamX N A i x Sig) {F : what₂.Mt (N.mu i) (N.j i)} (hF : F ∈ eigC N A i x) :
    what₂.thetaP (N.mu i) (N.j i) F ∈ MjSig N A i Sig := by
  refine mem_biSup_of_orthogonal (what₂.isot (N.j i)) {σ | HasParamW N A i σ Sig} htop hO
    fun σ hσ => ?_
  by_cases h0 : what₂.isot (N.j i) σ = ⊥
  · rw [h0, Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top
  obtain ⟨P, hP⟩ := hθ i σ h0
  have hne : A.ptV i P ≠ some x := fun h => hσ (hasParamW_of_thetaOf N A hL hS hloc hx hP h)
  rw [Submodule.mem_orthogonal]
  intro f hf
  rw [← LinearMap.adjoint_inner_left]
  exact (typeV_isOrtho_eigC N A hT hne).inner_eq (hP.2 ⟨f, hf, rfl⟩) hF

theorem main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    EachRowHasThetaLift N A → PartsSum R what₂.Mj what₂.isot → (∀ i, PartOrth N i) →
      (∀ i, TypeOrth N A i) → (∀ i, SplitLift N A i) → ParamLaws N A → (∀ i, LocOfPt N A i) →
      ThetaPMapsEigenspaceInto N A :=
  fun _ _ _ N A hθ hsum hO hT hS hL hloc i _ _ _ hx _ hF =>
    thetaP_mem N A hθ hL (hsum _ (N.j_range i).1 (N.j_range i).2).2 (hO i) (hT i) (hS i) (hloc i) hx hF

theorem downMem : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), ThetaOne N A → Rows.IsotInternal what₂ → PartOrth N i → TypeOrth N A i → ParamLaws N A →
      SplitLift N A i → LocOfPt N A i → DownMem N A i := by
  rintro R H what₂ N A i hθ hI hO hT hL hS hloc x - Sig hx _ ⟨F, hF, rfl⟩
  exact thetaP_mem N A hθ hL (hI _ (N.j_range i).1 (N.j_range i).2).submodule_iSup_eq_top hO hT hS hloc hx hF

end GlobalTheory.DownMemRoad
