import Formalism.SharpRestriction.CuspSpanNormBounds.LocSplitType
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfLiftNumberGenus
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual

noncomputable section

namespace Formalism.MainNotions.BridgeRowsGenus

open NumberField Formalism.HermitianLatticesTheory

section Cyc

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

def IsCycT (h : V →ₗ⋆[E] V →ₗ[E] E) (T : ℕ) (L : Submodule (𝓞 E) V) : Prop :=
  Submodule.IsLattice E L ∧ IsIntegralLat h L ∧
    ∃ w₁ ∈ dual h L, (∀ w ∈ dual h L, ∃ a : 𝓞 E, w + a • w₁ ∈ L) ∧
      ∀ a : 𝓞 E, a • w₁ ∈ L ↔ ((T : ℕ) : 𝓞 E) ∣ a

theorem cyc_star_int (o : 𝓞 E) : star (algebraMap (𝓞 E) E o) ∈ Set.range (algebraMap (𝓞 E) E) := by
  have h : IsIntegral ℤ (starRingEnd E (algebraMap (𝓞 E) E o)) :=
    (RingOfIntegers.isIntegral_coe o).map (starRingEnd E).toIntAlgHom
  exact ⟨⟨_, h⟩, rfl⟩

theorem cyc_natCast_mem_hcompl (p : Ideal (𝓞 E)) (T : ℕ) (hT : ((T : ℕ) : 𝓞 E) ∉ p) :
    ((T : ℕ) : 𝓞 E) ∈ hcompl (K := E) p := by
  unfold hcompl
  apply Submonoid.subset_closure
  refine ⟨hT, fun t ht => ?_⟩
  have e : t = ((T : ℕ) : 𝓞 E) := by
    apply IsFractionRing.injective (𝓞 E) E
    rw [ht, map_natCast, star_natCast]
  rw [e]
  exact hT

theorem cyc_unimodAt (h : V →ₗ⋆[E] V →ₗ[E] E) (T : ℕ) (L : Submodule (𝓞 E) V) (hL : IsCycT h T L)
    (p : Ideal (𝓞 E)) (hTp : ((T : ℕ) : 𝓞 E) ∉ p) : IsUnimodularAt h p L := by
  obtain ⟨hlat, hint, w₁, _, hgen, hann⟩ := hL
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := IsFractionRing.injective (𝓞 E) E
  unfold IsUnimodularAt
  rw [locDual_dualAt_loc h hinj cyc_star_int p L]
  apply le_antisymm
  · refine le_trans (locDual_dualAt_le h cyc_star_int p L hlat.fg) ?_
    intro x hx
    obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp hx
    obtain ⟨a, ha⟩ := hgen _ hsx
    refine locBasic_mem_locS.mpr ⟨((T : ℕ) : 𝓞 E) * s, (hcompl (K := E) p).mul_mem (cyc_natCast_mem_hcompl p T hTp) hs, ?_⟩
    have h1 : (((T : ℕ) : 𝓞 E) * a) • w₁ ∈ L := (hann _).2 (dvd_mul_right _ _)
    have h2 : ((T : ℕ) : 𝓞 E) • (s • x + a • w₁) ∈ L := L.smul_mem _ ha
    have e : (((T : ℕ) : 𝓞 E) * s) • x =
        ((T : ℕ) : 𝓞 E) • (s • x + a • w₁) - (((T : ℕ) : 𝓞 E) * a) • w₁ := by
      rw [smul_add, mul_smul, mul_smul]
      abel
    rw [e]
    exact L.sub_mem h2 h1
  · refine le_trans ?_ (locDual_loc_dual_le h p L)
    intro x hx
    obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp hx
    exact locBasic_mem_locS.mpr ⟨s, hs, (dualBasic_mem_dual h L _).2 fun y hy => hint y hy _ hsx⟩

end Cyc

def CycGenus : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (S : Formalism.BasicNotions.HSpace E) (T : ℕ), T.Prime → 3 ≤ T → Formalism.MainNotions.S.SplitsCompl E T →
    ∀ L M : Submodule (𝓞 E) S.V, IsCycT S.hT T L → IsCycT S.hT T M → M ∈ genus S.hT L

def CycSplitAt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (S : Formalism.BasicNotions.HSpace E) (T : ℕ), T.Prime → 3 ≤ T → Formalism.MainNotions.S.SplitsCompl E T →
    ∀ L : Submodule (𝓞 E) S.V, IsCycT S.hT T L →
    ∀ p : Ideal (𝓞 E), p.IsMaximal → ((T : ℕ) : 𝓞 E) ∈ p → conjIdeal (K := E) p ≠ p ∧ LocTypeAt S.hT p L

theorem cycGenus_of (hC : CycSplitAt) (hU : LocUnimod) (hS : LocSplitType) : CycGenus := by
  intro F E _ _ _ _ _ _ hc S T hT hT3 hsp L M hL hM
  refine ⟨hM.1, fun p hp => ?_⟩
  by_cases hTp : ((T : ℕ) : 𝓞 E) ∈ p
  · have a := hC F E hc S T hT hT3 hsp L hL p hp hTp
    have b := hC F E hc S T hT hT3 hsp M hM p hp hTp
    exact hS F E hc S L M hL.1 hM.1 hL.2.1 hM.2.1 p hp a.1 a.2 b.2
  · exact hU F E hc S L M hL.1 hM.1 p hp (cyc_unimodAt S.hT T L hL p hTp) (cyc_unimodAt S.hT T M hM p hTp)

section Rows

open Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem row_lattice_cyclic_type (D : D7) (u : D.what₂.Word) (hT : (Tu D u).Prime)
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)
    (Λ : LatV D) (hΛr : IsRowLat D F0 Λ) :
    IsCycT (D.sp.X 0).hT (Tu D u) (L0X D Λ (lf D F0)) := by
  obtain ⟨hΛ, hu, hlift, hconv⟩ := hΛr.2.1
  obtain ⟨w₁, hw₁, hgen, hann⟩ := dual_orthLattice_quotient_cyclic F0 he hz Λ hΛ hu hlift.1 hconv.2 hT.ne_zero
  exact ⟨orthLattice_isLattice F0 he hz Λ hΛ hu, orthLattice_isIntegral_of_unimodular Λ (lf D F0) hu, w₁, hw₁, hgen, hann⟩

theorem rows_one_genus_of_cyclic (H : CycGenus) (D : D7) (u : D.what₂.Word) : OrthLatticesOneGenus D u := by
  intro hT hT3 hsp F0 he hz Λ hΛ Λ' hΛ'
  exact H D.host.F D.host.E D.sp.cm (D.sp.X 0) (Tu D u) hT hT3 hsp _ _
    (row_lattice_cyclic_type D u hT F0 he hz Λ hΛ) (row_lattice_cyclic_type D u hT F0 he hz Λ' hΛ')

theorem rows_one_genus_of_local (hC : CycSplitAt) (hU : LocUnimod) (hS : LocSplitType) (D : D7) (u : D.what₂.Word) :
    OrthLatticesOneGenus D u :=
  rows_one_genus_of_cyclic (cycGenus_of hC hU hS) D u

end Rows

end Formalism.MainNotions.BridgeRowsGenus

end
