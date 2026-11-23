import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HmUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StdStab

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem th_eq_one (hG : Good S) : S.th = 1 := by
  simp [Frames.th, hG.gg]

theorem image_all (g : Fin (r + 1) → S.V) :
    g '' {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.range g := by
  rw [show {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ from
    Set.eq_univ_of_forall fun i => i.is_lt, Set.image_univ]

theorem mem_span_iff (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hg : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) (A : Submodule L.O S.V)
    (hA : S.IsInner g gs A) (x : S.V) :
    x ∈ Submodule.span L.O (Set.range g) ↔ x ∈ S.stdLat g gs A ∧ x ∈ S.spanTo g (r + 1) := by
  rw [← image_all S g]
  exact ((GlobalTheory.HL.StdLat.stdLat_spec L r k S g gs hg A hA).2.1 (r + 1) le_rfl x).symm

theorem inv_apply_apply (h : S.GLV) (x : S.V) : h⁻¹ (h x) = x :=
  h.symm_apply_apply x

end

theorem stab_coordLat : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → S.a = 0 → ∀ d₀, S.IsTermW d₀ (coordLat S) 1 1 → S.St ⊓ MulAction.stabilizer S.GLV (coordLat S) = S.K0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S hG ha d₀ hT
  have hTerm : S.IsTerm d₀ (coordLat S) := ⟨(1, 1), hT⟩
  have hMeq := (GlobalTheory.HL.WitIndep.witness_independence L r k S d₀ (coordLat S) 1 1 hT).2.1
  obtain ⟨hA, hA', -, -, hC1, hC2, -, -⟩ := hT
  rw [one_smul] at hC1 hC2
  have hf : ∀ x, x ∈ Submodule.span L.O (Set.range S.f) ↔
      x ∈ coordLat S ∧ x ∈ S.spanTo S.f (r + 1) := by
    intro x; rw [hC1]; exact mem_span_iff S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hA x
  have hf' : ∀ x, x ∈ Submodule.span L.O (Set.range S.f') ↔
      x ∈ coordLat S ∧ x ∈ S.spanTo S.f' (r + 1) := by
    intro x; rw [hC2]; exact mem_span_iff S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hA' x
  have th1 := th_eq_one S hG

  have key1 : ∀ h ∈ S.St, h • coordLat S = coordLat S → ∀ x,
      (x ∈ Submodule.span L.O (Set.range S.f) → h x ∈ Submodule.span L.O (Set.range S.f)) ∧
      (x ∈ Submodule.span L.O (Set.range S.f') → h x ∈ Submodule.span L.O (Set.range S.f')) := by
    intro h hh hC x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [hf] at hx ⊢
      refine ⟨?_, (GlobalTheory.FrameAct.spanTo_iff S h hh _ x).2 hx.2⟩
      rw [← hC]; exact (GlobalTheory.FrameAct.mem_smul_iff S h _ x).2 hx.1
    · rw [hf'] at hx ⊢
      refine ⟨?_, (GlobalTheory.FrameAct.spanTo_iff' S h hh _ x).2 hx.2⟩
      rw [← hC]; exact (GlobalTheory.FrameAct.mem_smul_iff S h _ x).2 hx.1

  have key2 : ∀ g ∈ S.K0, ∀ x ∈ coordLat S, g x ∈ coordLat S := by
    intro g hg
    obtain ⟨⟨hgSt, hgf⟩, hgf'⟩ := hg
    replace hgf : g • Submodule.span L.O (Set.range S.f) = Submodule.span L.O (Set.range S.f) := hgf
    replace hgf' : g • Submodule.span L.O (Set.range S.f') = Submodule.span L.O (Set.range S.f') := hgf'
    replace hgSt : g ∈ S.St := hgSt
    have gf : ∀ (g : S.GLV), g • Submodule.span L.O (Set.range S.f) = Submodule.span L.O (Set.range S.f) →
        ∀ b, g (S.f b) ∈ coordLat S := by
      intro g hg b
      have h1 : g (S.f b) ∈ Submodule.span L.O (Set.range S.f) := by
        rw [← hg]; exact (GlobalTheory.FrameAct.mem_smul_iff S g _ _).2 (Submodule.subset_span ⟨b, rfl⟩)
      exact ((hf _).1 h1).1
    have gf' : ∀ (g : S.GLV), g • Submodule.span L.O (Set.range S.f') = Submodule.span L.O (Set.range S.f') →
        ∀ b, g (S.f' b) ∈ coordLat S := by
      intro g hg b
      have h1 : g (S.f' b) ∈ Submodule.span L.O (Set.range S.f') := by
        rw [← hg]; exact (GlobalTheory.FrameAct.mem_smul_iff S g _ _).2 (Submodule.subset_span ⟨b, rfl⟩)
      exact ((hf' _).1 h1).1
    have hM : ∀ (g : S.GLV), g • Submodule.span L.O (Set.range S.f) = Submodule.span L.O (Set.range S.f) →
        g • Submodule.span L.O (Set.range S.f') = Submodule.span L.O (Set.range S.f') →
        ∀ m ∈ S.Mof S.f S.f', g m ∈ coordLat S := by
      intro g h1 h2 m hm
      induction hm using Submodule.span_induction with
      | mem y hy =>
        rcases hy with ⟨b, rfl⟩ | ⟨b, rfl⟩
        · exact gf g h1 b
        · simp only [th1, inv_one, map_one, one_smul, map_sub]
          exact (coordLat S).sub_mem (gf' g h2 b) (gf g h1 b)
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact (coordLat S).add_mem hx hy
      | smul c x _ hx =>
        have e : g (c • x) = c • g x := by
          first
            | exact LinearEquiv.map_smul_of_tower g c x
            | exact g.toLinearMap.map_smul_of_tower c x
            | (rw [Subring.smul_def, map_smul, ← Subring.smul_def])
        rw [e]; exact (coordLat S).smul_mem c hx
    intro x hx
    obtain ⟨-, hcompl, -⟩ := GlobalTheory.FrameBasic.main L r k S
    have hx' : x ∈ S.ME ⊔ S.W0 := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
    have hmM : m ∈ S.Mof S.f S.f' := by
      have := GlobalTheory.HL.UnimodTerm.proj_mem S hTerm ha hx hm (by simpa using hw)
      rw [hMeq] at this; exact this
    have hw' : w ∈ coordLat S := by
      have h1 := hM 1 (one_smul _ _) (one_smul _ _) m hmM
      have : w = (m + w) - m := by abel
      rw [this]; exact (coordLat S).sub_mem hx h1
    rw [map_add, (GlobalTheory.HL.FrameStab.stab_eq L r k S).1 g hgSt w hw]
    exact (coordLat S).add_mem (hM g hgf hgf' m hmM) hw'
  ext h
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Frames.K0]
  constructor
  · rintro ⟨hh, hC⟩
    have hC' : h⁻¹ • coordLat S = coordLat S := by rw [inv_smul_eq_iff]; exact hC.symm
    have hhi : h⁻¹ ∈ S.St := inv_mem hh
    refine ⟨⟨hh, ?_⟩, ?_⟩
    · refine (GlobalTheory.FrameAct.eq_smul_of S h _ _ fun x => ⟨fun hx => ?_, (key1 h hh hC x).1⟩).symm
      have := (key1 h⁻¹ hhi hC' (h x)).1 hx
      rwa [inv_apply_apply] at this
    · refine (GlobalTheory.FrameAct.eq_smul_of S h _ _ fun x => ⟨fun hx => ?_, (key1 h hh hC x).2⟩).symm
      have := (key1 h⁻¹ hhi hC' (h x)).2 hx
      rwa [inv_apply_apply] at this
  · rintro ⟨⟨hh, h1⟩, h2⟩
    have hK : h ∈ S.K0 := ⟨⟨hh, h1⟩, h2⟩
    refine ⟨hh, (GlobalTheory.FrameAct.eq_smul_of S h _ _ fun x => ⟨fun hx => ?_, key2 h hK x⟩).symm⟩
    have := key2 h⁻¹ (inv_mem hK) _ hx
    rwa [inv_apply_apply] at this

end GlobalTheory.HL.StdStab
