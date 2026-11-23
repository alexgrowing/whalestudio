import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsHasInfCharGL
import GroundTheory.PAdicHodge.AInfGalois

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.SpehInfChar

namespace PositivityTheory.Rg.Rs

namespace InfinitesimalCharacterAscent

theorem spehExp_rev (d : ℕ) (i : Fin d) : spehExp d i.rev = -spehExp d i := by
  have h := i.2
  simp only [spehExp, Fin.val_rev]
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem prod_neg (d : ℕ) (g : ℂ → ℂ) :
    ∏ i : Fin d, g (-(spehExp d i : ℂ)) = ∏ i : Fin d, g (spehExp d i : ℂ) := by
  refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
  simp only [Fin.revPerm_apply, spehExp_rev]
  push_cast
  ring_nf

end InfinitesimalCharacterAscent

open InfinitesimalCharacterAscent in
theorem infAsc_holds : InfAsc := by
  intro E _ _ _ N a d V π hV hemb τ m hm
  obtain ⟨hs, ν, hν, f, hfm, hfi, hfe⟩ := hemb
  have hm0 : π.HasInfChar τ ((CG.mk π).infChar τ) :=
    hasInfChar_infChar_of_commute E a (fun τ u o => cap_commute_act τ u o) (CG.mk π) τ
  set m₀ := (CG.mk π).infChar τ with hm₀
  refine ⟨m₀, hm0, GlobalTheory.BcSpehProof.hasInfCharGL_unique hV.ne_bot hm ⟨?_, fun u φ hφ => ?_⟩⟩
  · rw [← hs, Multiset.card_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Multiset.card_map, hm₀, CG.card_infChar]
  have hI : ∀ X, ∀ φ ∈ indForms hs (fun i => π.twist (ν i)), lie E N X φ ∈ indForms hs (fun i => π.twist (ν i)) :=
    fun X φ hφ => lie_mem_indForms _ hs _ X φ hφ
  have hIV : ∀ X, ∀ φ ∈ V, lie E N X φ ∈ V := fun X φ hφ => hV.stable (.lie X) φ hφ
  have hexpo : ∀ i : Fin d, expo (ν i) τ = ((-spehExp d i + a * spehExp d i : ℝ) : ℂ) := fun i =>
    (GlobalTheory.CuspRep.InfType.expo_of_infType E (ν i)).2.1 _ (hν i) τ
  have hmod : ∀ i : Fin d, ((modExp (fun _ : Fin d => Fin a) i : ℤ) : ℂ) / 2 = ((a * spehExp d i : ℝ) : ℂ) := fun i => by
    rw [mul_spehExp]
    push_cast
    rfl
  have hc := cap_indForms (fun _ : Fin d => a) hs (fun i => π.twist (ν i)) τ (fun i => m₀.map (· + expo (ν i) τ))
    (fun i => hm0.twist (ν i)) u (f φ) (hfm φ hφ)
  have e1 : f (cap τ u φ) = cap τ u (f φ) := cap_comm_quot hIV f hfe τ u φ hφ
  set Q := ((∑ i : Fin d, m₀.map (· + (spehExp d i : ℂ))).map (u + ·)).prod with hQ
  have hQ' : (∏ i : Fin d, ((m₀.map (· + expo (ν i) τ)).map fun x =>
      u + x - (modExp (fun _ : Fin d => Fin a) i : ℂ) / 2).prod) = Q := by
    rw [hQ, prod_map_finset_sum]
    have e : ∀ i : Fin d, ((m₀.map (· + expo (ν i) τ)).map fun x =>
        u + x - (modExp (fun _ : Fin d => Fin a) i : ℂ) / 2).prod =
        (m₀.map fun x => u + x + -(spehExp d i : ℂ)).prod := fun i => by
      rw [Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun x _ => ?_
      simp only [Function.comp_apply]
      rw [hexpo i, hmod i]
      push_cast
      ring
    rw [Finset.prod_congr rfl fun i _ => e i, prod_neg d (fun t => (m₀.map fun x => u + x + t).prod)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    simp only [Function.comp_apply]
    ring
  have hmem : cap τ u φ - Q • φ ∈ V := by
    rw [hm.2 u φ hφ]
    exact V.sub_mem (V.smul_mem _ hφ) (V.smul_mem _ hφ)
  have h0 : f (cap τ u φ - Q • φ) = 0 := by
    rw [map_sub, e1, hc, map_smul, hQ']
    exact sub_self _
  exact sub_eq_zero.1 (hfi _ hmem h0)

end PositivityTheory.Rg.Rs

end
