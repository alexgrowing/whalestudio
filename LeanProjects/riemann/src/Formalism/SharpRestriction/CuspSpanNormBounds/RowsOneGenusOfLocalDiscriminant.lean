import Formalism.SharpRestriction.CuspSpanNormBounds.RowsOneGenusOfCyclic

noncomputable section

namespace Formalism.MainNotions.BridgeRowsGenus

open NumberField Formalism.HermitianLatticesTheory

section Conj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem natCast_repr (p : Ideal (𝓞 E)) (T : ℕ) (hT : T.Prime) (hN : Ideal.absNorm p = T) (x : 𝓞 E) :
    ∃ n : ℕ, x - (n : 𝓞 E) ∈ p := by
  have hc : Nat.card (𝓞 E ⧸ p) = T := by rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hN]
  have : Finite (𝓞 E ⧸ p) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hT.ne_zero)
  let _ := Fintype.ofFinite (𝓞 E ⧸ p)
  have : NeZero T := ⟨hT.ne_zero⟩
  have hc' : Fintype.card (𝓞 E ⧸ p) = T := by rw [Fintype.card_eq_nat_card, hc]
  let e := ZMod.ringEquivOfPrime (𝓞 E ⧸ p) hT hc'
  obtain ⟨k, hk⟩ := e.surjective (Ideal.Quotient.mk p x)
  refine ⟨k.val, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_natCast, ← hk, ← map_natCast e k.val,
    ZMod.natCast_zmod_val, sub_self]

theorem split_conj_ne (hc : Formalism.BasicNotions.CMData F E) (T : ℕ) (hT : T.Prime) (hsp : Formalism.MainNotions.S.SplitsCompl E T)
    (p : Ideal (𝓞 E)) (hp : p.IsMaximal) (hTp : ((T : ℕ) : 𝓞 E) ∈ p) : conjIdeal (K := E) p ≠ p := by
  intro hconj
  have hu : IsCMUnram E := hc.cmUnram
  unfold IsCMUnram at hu
  obtain ⟨_, _, h3⟩ := hu
  obtain ⟨θ, t, hθt, hnot⟩ := h3 p hp
  apply hnot
  obtain ⟨n, hn⟩ := natCast_repr p T hT (hsp p hp hTp).1 θ
  let σ : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)
  have hσ : ∀ s : 𝓞 E, algebraMap (𝓞 E) E (σ s) = star (algebraMap (𝓞 E) E s) := fun s => rfl
  have hσp : ∀ s ∈ p, σ s ∈ p := by
    intro s hs
    rw [← hconj]
    unfold conjIdeal
    exact Ideal.subset_span ⟨s, hs, hσ s⟩
  have hσθ : σ θ = t := by
    apply IsFractionRing.injective (𝓞 E) E
    rw [hσ, hθt]
  have h2 : σ (θ - (n : 𝓞 E)) ∈ p := hσp _ hn
  rw [map_sub, map_natCast, hσθ] at h2
  have e : θ - t = (θ - (n : 𝓞 E)) - (t - (n : 𝓞 E)) := by ring
  rw [e]
  exact p.sub_mem hn h2

theorem unimodAt_of_unimod {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (L : Submodule (𝓞 E) V) (hlat : Submodule.IsLattice E L) (hu : IsUnimodular h L)
    (p : Ideal (𝓞 E)) : IsUnimodularAt h p L := by
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := FaithfulSMul.algebraMap_injective _ _
  have hst : ∀ r : 𝓞 E, star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) :=
    fun r => cyc_star_int r
  have hfg : L.FG := Submodule.IsLattice.fg (A := E) (self := hlat)
  unfold IsUnimodularAt
  rw [locDual_dualAt_loc h hinj hst]
  have e1 := locDual_loc_dual_le h p L
  have e2 := locDual_dualAt_le h hst p L hfg
  unfold IsUnimodular at hu
  rw [hu] at e1 e2
  exact le_antisymm e2 e1

theorem unimod_mem_genus (hU : LocUnimod) (hc : Formalism.BasicNotions.CMData F E) (S : Formalism.BasicNotions.HSpace E)
    (L M : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L) (hM : Submodule.IsLattice E M)
    (huL : IsUnimodular S.hT L) (huM : IsUnimodular S.hT M) : M ∈ genus S.hT L :=
  ⟨hM, fun p hp => hU F E hc S L M hL hM p hp (unimodAt_of_unimod S.hT L hL huL p) (unimodAt_of_unimod S.hT M hM huM p)⟩

theorem unimodular_mem_genus (hU : LocUnimod) (hc : Formalism.BasicNotions.CMData F E) (S : Formalism.BasicNotions.HSpace E)
    (M : Submodule (𝓞 E) S.V) (hM : Submodule.IsLattice E M) (huM : IsUnimodular S.hT M) : M ∈ genus S.hT S.L0 :=
  unimod_mem_genus hU hc S S.L0 M S.standardTuple_isLattice hM S.baseLattice_isUnimodular huM

end Conj

def CycLocType : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (S : Formalism.BasicNotions.HSpace E) (T : ℕ), T.Prime → 3 ≤ T → Formalism.MainNotions.S.SplitsCompl E T →
    ∀ L : Submodule (𝓞 E) S.V, IsCycT S.hT T L →
    ∀ p : Ideal (𝓞 E), p.IsMaximal → ((T : ℕ) : 𝓞 E) ∈ p → LocTypeAt S.hT p L

theorem cycSplitAt_of (h : CycLocType) : CycSplitAt :=
  fun F E _ _ _ _ _ _ hc S T hT hT3 hsp L hL p hp hTp =>
    ⟨split_conj_ne hc T hT hsp p hp hTp, h F E hc S T hT hT3 hsp L hL p hp hTp⟩

section Rows

open Formalism.BasicNotions Formalism.MainNotions.BridgeLemma₂

theorem rows_one_genus_of_local_discriminant (hL : CycLocType) (hU : LocUnimod) (hS : LocSplitType) (D : D7) (u : D.what₂.Word) :
    OrthLatticesOneGenus D u :=
  rows_one_genus_of_local (cycSplitAt_of hL) hU hS D u

end Rows

end Formalism.MainNotions.BridgeRowsGenus

end
