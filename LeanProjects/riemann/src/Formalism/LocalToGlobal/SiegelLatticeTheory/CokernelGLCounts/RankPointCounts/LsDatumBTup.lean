import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBCut

noncomputable section

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Classical ValuativeRel

section Tup

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {T T' : ℕ}

theorem fL_eq (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) :
    fL M δ T T' p w τ O = hL M δ T T' p w O * kL M δ T T' p w τ O := by
  by_cases h1 : IsLCls M δ T T' p w O <;> simp [fL, hL, kL, h1]

theorem gL_eq (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) :
    gL M δ T T' p w τ O = hL M δ T T' p w O * eL M δ T T' p w τ O := by
  by_cases h1 : IsLCls M δ T T' p w O <;>
    by_cases h2 : thL M δ T T' p w (repL M δ T T' p w O) = τ <;> simp [gL, hL, eL, h1, h2]

theorem eL_zero_or_one (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS))
    (O : Set (MatP D p)) : eL M δ T T' p w τ O = 0 ∨ eL M δ T T' p w τ O = 1 := by
  unfold eL
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem base_factors {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {θ : Option ((M p).Cls D.R.rS)}
    (hf : ∀ τ O, fL M δ T T' p w τ O = if O = x0L M δ T T' p w ∧ τ = θ then 1 else 0)
    (hg : ∀ τ O, gL M δ T T' p w τ O = if O = x0L M δ T T' p w ∧ τ = θ then 1 else 0) :
    hL M δ T T' p w (x0L M δ T T' p w) = 1 ∧ kL M δ T T' p w θ (x0L M δ T T' p w) = 1 ∧
      eL M δ T T' p w θ (x0L M δ T T' p w) = 1 := by
  have g1 := hg θ (x0L M δ T T' p w)
  rw [if_pos ⟨rfl, rfl⟩, gL_eq] at g1
  have he : eL M δ T T' p w θ (x0L M δ T T' p w) = 1 := by
    rcases eL_zero_or_one (M := M) (δ := δ) (T := T) (T' := T') p w θ (x0L M δ T T' p w) with h | h
    · rw [h, mul_zero] at g1
      exact absurd g1 zero_ne_one
    · exact h
  rw [he, mul_one] at g1
  have f1 := hf θ (x0L M δ T T' p w)
  rw [if_pos ⟨rfl, rfl⟩, fL_eq, g1, one_mul] at f1
  exact ⟨g1, f1, he⟩

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem partnerTupleSum_of {θ0 : ∀ p, Option ((M p).Cls D.R.rS)}
    (hU : LocUnram M δ u u' θ0) (hR : ThRestricted M δ u u' F0 what₂ θ0)
    (hC : CoefProd M δ u u' F0 what₂) (hN : PartnerCount M δ u u' F0 what₂) : PartnerTupleSum M δ u u' F0 what₂ := by
  intro γ w hγ w' hG' hk
  obtain ⟨hres, hcnt⟩ := hN γ w hγ w' hG' hk
  refine ⟨hres, fun x => ?_⟩
  obtain ⟨S, hS⟩ := hU w' hG'
  have hRf := hR γ w hγ
  have hone : ∀ p ∉ S ∪ hRf.toFinset ∪ x.2.toFinset,
      hL M δ (D.mem u).A.T (D.mem u').A.T p w' (x.1 p) = 1 ∧
        kL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p) = 1 := by
    intro p hp
    have hpS : p ∉ S := fun h => hp (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hth : thT M δ γ p = θ0 p := by
      by_contra h
      exact hp (Finset.mem_union_left _ (Finset.mem_union_right _ (hRf.mem_toFinset.2 h)))
    have hx : x.1 p = x0L M δ (D.mem u).A.T (D.mem u').A.T p w' := by
      by_contra h
      exact hp (Finset.mem_union_right _ (x.2.mem_toFinset.2 h))
    rw [hx, hth]
    have hb := base_factors (fun τ O => ((hS p hpS).2 τ O).1) (fun τ O => ((hS p hpS).2 τ O).2)
    exact ⟨hb.1, hb.2.1⟩
  have hfunc : (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ //
      (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = x.1} =>
        PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ'.1 w') =
      fun γ' => (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w' (x.1 p)) *
        ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ) := by
    funext γ'
    rw [hC γ'.1 w' γ'.2.1.2, γ'.2.2]
  rw [hfunc]
  have hv : (∏ᶠ p, fL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p)) =
      (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w' (x.1 p)) *
        ∏ᶠ p, kL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p) := by
    rw [← finprod_mul_distrib]
    · exact finprod_congr fun p => fL_eq p w' _ _
    · refine (S ∪ hRf.toFinset ∪ x.2.toFinset).finite_toSet.subset fun p hp => ?_
      by_contra h
      exact (Function.mem_mulSupport.1 hp) (hone p h).1
    · refine (S ∪ hRf.toFinset ∪ x.2.toFinset).finite_toSet.subset fun p hp => ?_
      by_contra h
      exact (Function.mem_mulSupport.1 hp) (hone p h).2
  rw [hv]
  exact (hcnt x).mul_left _

theorem fiberTupleSum_of {L : CntLocal.LocSp D M} {θ0 : ∀ p, Option ((M p).Cls D.R.rS)}
    (hU : LocUnram M δ u u' θ0) (hR : ThRestricted M δ u u' F0 what₂ θ0)
    (hC : CoefProd M δ u u' F0 what₂) (hN : FiberCount M δ L u u' F0 what₂) : FiberTupleSum M δ L u u' F0 what₂ := by
  intro nc hnc ϖ hϖ w hG γ₀ w₀ hγ₀ hk
  obtain ⟨hres, hcnt⟩ := hN nc hnc ϖ hϖ w hG γ₀ w₀ hγ₀ hk
  refine ⟨hres, fun x => ?_⟩
  obtain ⟨S, hS⟩ := hU w hG
  have hRf := hR γ₀ w₀ hγ₀
  have hone : ∀ p ∉ S ∪ hRf.toFinset ∪ x.2.toFinset,
      hL M δ (D.mem u).A.T (D.mem u').A.T p w (x.1 p) = 1 ∧
        eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p) = 1 := by
    intro p hp
    have hpS : p ∉ S := fun h => hp (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hth : thT M δ γ₀ p = θ0 p := by
      by_contra h
      exact hp (Finset.mem_union_left _ (Finset.mem_union_right _ (hRf.mem_toFinset.2 h)))
    have hx : x.1 p = x0L M δ (D.mem u).A.T (D.mem u').A.T p w := by
      by_contra h
      exact hp (Finset.mem_union_right _ (x.2.mem_toFinset.2 h))
    rw [hx, hth]
    have hb := base_factors (fun τ O => ((hS p hpS).2 τ O).1) (fun τ O => ((hS p hpS).2 τ O).2)
    exact ⟨hb.1, hb.2.2⟩
  have hfunc : (fun γ : {γ : TermDef.Term D u u' F0 what₂ //
      (EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀) ∧ locT M δ γ = x.1} =>
        (PairVal.massTerm γ.1 : ℂ) * PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ.1 w) =
      fun γ => (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (x.1 p)) *
        ((PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ)) := by
    funext γ
    rw [hC γ.1 w γ.2.1.1, γ.2.2]
    ring
  rw [hfunc]
  have hv : (n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
      (∏ᶠ p, gL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p)) =
      (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (x.1 p)) *
        ((n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
          ∏ᶠ p, eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p)) := by
    rw [show (∏ᶠ p, gL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p)) =
        (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (x.1 p)) *
          ∏ᶠ p, eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p) from by
      rw [← finprod_mul_distrib]
      · exact finprod_congr fun p => gL_eq p w _ _
      · refine (S ∪ hRf.toFinset ∪ x.2.toFinset).finite_toSet.subset fun p hp => ?_
        by_contra h
        exact (Function.mem_mulSupport.1 hp) (hone p h).1
      · refine (S ∪ hRf.toFinset ∪ x.2.toFinset).finite_toSet.subset fun p hp => ?_
        by_contra h
        exact (Function.mem_mulSupport.1 hp) (hone p h).2]
    ring
  rw [hv]
  exact (hcnt x).mul_left _

end Tup

end Formalism.L2.SG.LsDatumB
