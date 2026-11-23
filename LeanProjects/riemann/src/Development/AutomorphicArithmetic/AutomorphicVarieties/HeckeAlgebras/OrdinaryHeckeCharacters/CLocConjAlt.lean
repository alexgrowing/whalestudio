import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGLStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem w_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  have h1 := s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)
  have h2 := s.hA v x
  exact h1.symm.trans h2

private theorem l_notMem {l : ℕ} {L : Type} [Field L] [NumberField L] [IsCMField L] {w u : Plc L}
    (h : ((l : ℕ) : 𝓞 (Lp L)) ∉ (w.under (𝓞 (Lp L))).asIdeal) (hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    ((l : ℕ) : 𝓞 L) ∉ u.asIdeal := fun h' => h <| by
  rw [← hu]
  change algebraMap (𝓞 (Lp L)) (𝓞 L) (l : 𝓞 (Lp L)) ∈ u.asIdeal
  rwa [map_natCast]

private theorem cmp_of {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L}
    (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) : cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dif_pos h]
  rfl

private theorem cmp_loc {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w u : Plc L}
    {x : UA L n} (hx : x ∈ locU n w) (hu : u.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) :
    cmp n u ((away l L n).rangeRestrict x) = 1 := by
  by_cases h : ((l : ℕ) : 𝓞 L) ∉ u.asIdeal
  · rw [cmp_of h]
    exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) hu)
  · unfold CaseU.cmp
    rw [dif_neg h]
    rfl

private theorem cLoc_conj {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w u : Plc L} (hw : IsSplitAt w)
    (x : UA L n) (h1 : cLoc w x = 1) (hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) : cLoc u x = 1 := by
  have hw1 : ∀ v, v = w → cLoc v x = 1 := by
    rintro v rfl
    exact h1
  rcases (GlobalTheory.SplitPts.over_split hw).2.2 u hu with rfl | rfl
  · exact h1
  · have hce := GlobalTheory.SplitPts.comp_eq x (conjSrc (GlobalTheory.SplitPts.conjE L) w)
    rw [hw1 _ (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w), Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_one, Matrix.one_mul] at hce
    exact Units.ext hce

theorem UpperTheory.V.Hi.secU :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ w : Plc L, IsSplitAt w → (∃ j : GLw n w →* UA L n, (∀ g, j g ∈ locU n w) ∧ (∀ g, cLoc w (j g) = g) ∧ Continuous j ∧ ∀ x ∈ locU n w, x = j (cLoc w x)) ∧ (w.under (𝓞 (Lp L)) ∉ s.S → Function.Bijective (((cmp n w).comp (Ub n s).subtype).comp (locA n s w).subtype) ∧ (∀ g, cmp n w ((sec n s w g : Ub n s) : Ga l L n) = g) ∧ ∀ g, sec n s w g ∈ locA n s w) := by
  intro l _ L Ω _ _ _ _ _ _ s n _ w hw
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL L n w hw
  have hs : ∀ y, cLoc w (e.symm y : UA L n) = y := fun y => by
    rw [← he, e.apply_symm_apply]
  refine ⟨⟨(locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom, fun g => (e.symm g).2, hs,
    continuous_subtype_val.comp e.symm.continuous, fun x hx => ?_⟩, fun hS => ?_⟩
  · have h1 := he ⟨x, hx⟩
    change x = (e.symm (cLoc w x) : UA L n)
    rw [← h1, e.symm_apply_apply]
  have hl : ((l : ℕ) : 𝓞 (Lp L)) ∉ (w.under (𝓞 (Lp L))).asIdeal := fun h => hS (Or.inl h)
  have hb : Function.Bijective (((cmp n w).comp (Ub n s).subtype).comp (locA n s w).subtype) := by
    refine ⟨(injective_iff_map_eq_one _).2 ?_, fun y => ?_⟩
    · rintro ⟨⟨g, hg⟩, hA⟩ h1
      obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective g
      have h2 : cLoc w x = 1 := (cmp_of (l_notMem hl rfl) x).symm.trans h1
      refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun u => ?_)))
      change cLoc u.1 x = 1
      by_cases hu : u.1.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · exact cLoc_conj hw x h2 hu
      · exact (cmp_of u.2 x).symm.trans
          (MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hA u.1) hu))
    · have hU : (away l L n).rangeRestrict (e.symm y : UA L n) ∈ Ub n s := by
        refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun u => ?_, ?_⟩
        · rw [Subgroup.mem_comap, cmp_loc (e.symm y).2 (by
            rw [w_under]
            exact fun h => hS (Or.inr (Or.inl (h ▸ u.2))))]
          exact one_mem _
        · rw [Subgroup.mem_comap, cmp_loc (e.symm y).2 (by
            rw [w_under]
            exact fun h => hS (Or.inr (Or.inr h.symm)))]
          exact one_mem _
      refine ⟨⟨⟨_, hU⟩, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu =>
        MonoidHom.mem_ker.2 (cmp_loc (e.symm y).2 hu)⟩, ?_⟩
      exact (cmp_of (l_notMem hl rfl) _).trans (hs y)
  refine ⟨hb, fun g => ?_, fun g => ?_⟩
  · unfold CaseU.sec
    rw [dif_pos hb]
    exact (MulEquiv.ofBijective _ hb).apply_symm_apply g
  · unfold CaseU.sec
    rw [dif_pos hb]
    exact ((MulEquiv.ofBijective _ hb).symm g).2
