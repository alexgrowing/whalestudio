import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWPhi
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelAwayAdapted

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.CongW
open GlobalTheory.Cong.AdaptLev

namespace UpperTheory.Gal.Int.Cong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem exists_locLev {U : Submodule ℂ (UA E a → ℂ)} (hU : IsAutRepU U) (w₀ : HeightOneSpectrum (𝓞 E)) :
    ∃ H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a), (∀ w, H w ≤ intU a w) ∧
      (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) ∧ (∀ w u, ¬ Apart w u → H w = H u) ∧
      (∀ w, ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ H w, RU E a x φ = φ) ∧
      (∀ w, (∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ intU a w, RU E a x φ = φ) → H w = intU a w) ∧
      ∀ᶠ w in Filter.cofinite, H w = intU a w := by
  classical
  obtain ⟨φ₀, hφ₀U, hφ₀0⟩ := (Submodule.ne_bot_iff U).1 hU.ne_bot
  have hφ₀aut : IsAutFormU φ₀ := hU.aut φ₀ hφ₀U
  let stab : Subgroup (UA E a) :=
    { carrier := {x | RU E a x φ₀ = φ₀}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at hx hy ⊢
        rw [hy, hx]
      one_mem' := by simp
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        calc RU E a x⁻¹ φ₀ = RU E a x⁻¹ (RU E a x φ₀) := by rw [hx]
          _ = φ₀ := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  let H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a) := fun r =>
    if ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ intU a r, RU E a x φ = φ then intU a r else intU a r ⊓ stab
  have hint : ∀ w, (∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ intU a w, RU E a x φ = φ) → H w = intU a w := fun w h => if_pos h
  refine ⟨H, fun r => ?_, fun r => ?_, fun w u h => ?_, fun r => ?_, hint, ?_⟩
  · simp only [H]
    split_ifs
    exacts [le_rfl, inf_le_left]
  · simp only [H]
    split_ifs
    · exact (GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open E a r).2
    · have e : (((intU a r ⊓ stab).subgroupOf (locU a r)) : Set (locU a r)) =
          (((intU a r).subgroupOf (locU a r)) : Set (locU a r)) ∩
            (fun x : locU a r => (⟨x.1, ((GlobalTheory.Cong.LevelExt.mem_locU_iff x.1).1 x.2).1⟩ : finU E a)) ⁻¹'
              {k : finU E a | RU E a k φ₀ = φ₀} := by
        ext x; exact Iff.rfl
      rw [e]
      exact (GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open E a r).2.inter (hφ₀aut.level.preimage (Continuous.subtype_mk continuous_subtype_val _))
  · simp only [H, intU_congr h]
  · simp only [H]
    split_ifs with h1
    · exact h1
    · exact ⟨φ₀, hφ₀U, hφ₀0, fun x hx => (Subgroup.mem_inf.1 hx).2⟩
  · filter_upwards [GlobalTheory.T.autForm_fixed_by_integralPoints_almostAllPlaces E a φ₀ hφ₀aut] with w hw
    exact hint w ⟨φ₀, hφ₀U, hφ₀0, hw⟩

theorem map_intU {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) : (intU a w).map (cLoc w) = GlobalTheory.LFun.KGL w a := by
  refine le_antisymm ?_ (KGL_le_map hw)
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_intU.1 hx).2 w (not_apart_self w)

theorem open_compact_map {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) {L : Subgroup (UA E a)} (hL : L ≤ intU a w)
    (ho : IsOpen ((L.subgroupOf (locU a w)) : Set (locU a w))) :
    IsOpen ((L.map (cLoc w) : Subgroup _) : Set (GL (Fin a) (w.adicCompletion E))) ∧
      IsCompact ((L.map (cLoc w) : Subgroup _) : Set (GL (Fin a) (w.adicCompletion E))) := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  have hle := hL.trans (intU_le_locU w)
  rw [map_eq_image hle e he]
  refine ⟨e.toHomeomorph.isOpenMap _ ho, IsCompact.image ?_ e.continuous⟩
  rw [Topology.IsInducing.subtypeVal.isCompact_iff]
  convert isCompact_of_le hL ho (GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open E a w).1 using 1
  exact coe_subgroupOf_image hle

theorem exists_level {T : Finset (HeightOneSpectrum (𝓞 E))} {U : Submodule ℂ (UA E a → ℂ)} (hU : AutOffT T U)
    {w₀ v' : HeightOneSpectrum (𝓞 E)} (hw₀ : IsSplitAt w₀) (hv' : IsSplitAt v') (hap : Apart v' w₀) :
    ∃ (K : Subgroup (UA E a)) (Kw : Levels E a) (Kv : Subgroup (GL (Fin a) (v'.adicCompletion E))),
      IsLevelAway w₀ K ∧ IsOpen (Kv : Set (GL (Fin a) (v'.adicCompletion E))) ∧
      (∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K ⊓ Kv.comap (cLoc v'), RU E a x φ = φ) ∧ Kw v' = GlobalTheory.LFun.KGL v' a ∧
      (∀ w, IsSplitAt w → Apart w w₀ → IsOpen (Kw w : Set (GL (Fin a) (w.adicCompletion E))) ∧
        IsCompact (Kw w : Set (GL (Fin a) (w.adicCompletion E)))) ∧
      (∀ w, IsSplitAt w → Apart w v' → (∃ B, SatU U w B) → Kw w = GlobalTheory.LFun.KGL w a) ∧
      (∀ w, ¬ IsSplitAt w → w ∉ T → ∀ x ∈ locU a w, cLoc w x ∈ GlobalTheory.LFun.KGL w a → x ∈ K) ∧
      ∀ w, IsSplitAt w → Apart w w₀ → ∀ x ∈ locU a w, x ∈ K ↔ cLoc w x ∈ Kw w := by
  classical
  obtain ⟨H, hleI, hopen, hfib, hfix, hint, hae⟩ := exists_locLev hU.1 w₀
  have hle : ∀ w, H w ≤ locU a w := fun w => (hleI w).trans (intU_le_locU w)
  have hcpt : ∀ w, IsCompact (H w : Set (UA E a)) := fun w => isCompact_of_le (hleI w) (hopen w) (GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open E a w).1
  obtain ⟨φ, hφU, hφ0, hφH⟩ := GlobalTheory.T.exists_vector_fixed_by_product_localLevels E a U hU.1 w₀ H hle hfib hcpt
    (hae.mono fun w hw x hx => by rw [hw] at hx; exact (mem_intU.1 hx).2 w (not_apart_self w)) hopen (fun w _ => hfix w)
  have hφ := GlobalTheory.T.fixed_of_fixed_by_local_levels E a w₀ H hle hfib hcpt hopen hae φ (hU.1.aut φ hφU) hφH
  let H' : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a) := fun w => if Apart w v' then H w else intU a w
  have h1 : ∀ w, Apart w v' → H' w = H w := fun w h => if_pos h
  have h2 : ∀ w, ¬ Apart w v' → H' w = intU a w := fun w h => if_neg h
  have hleI' : ∀ w, H' w ≤ intU a w := fun w => by
    by_cases h : Apart w v'
    · rw [h1 w h]; exact hleI w
    · rw [h2 w h]
  have hle' : ∀ w, H' w ≤ locU a w := fun w => (hleI' w).trans (intU_le_locU w)
  have hopen' : ∀ w, IsOpen (((H' w).subgroupOf (locU a w)) : Set (locU a w)) := fun w => by
    by_cases h : Apart w v'
    · rw [h1 w h]; exact hopen w
    · rw [h2 w h]; exact (GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open E a w).2
  have hcpt' : ∀ w, IsCompact (H' w : Set (UA E a)) := fun w => isCompact_of_le (hleI' w) (hopen' w) (GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open E a w).1
  have hfib' : ∀ w u, ¬ Apart w u → H' w = H' u := fun w u h => by
    by_cases hw : Apart w v'
    · have hu : Apart u v' := by
        by_contra hu
        exact not_apart_trans h hu hw
      rw [h1 w hw, h1 u hu, hfib w u h]
    · rw [h2 w hw, h2 u (not_apart_trans (not_apart_symm h) hw), intU_congr h]
  have hint' : ∀ w, H w = intU a w → H' w = intU a w := fun w h => by
    by_cases hw : Apart w v'
    · rw [h1 w hw, h]
    · exact h2 w hw
  refine ⟨levelOf a w₀ H', fun w => (H' w).map (cLoc w), (H v').map (cLoc v'),
    GlobalTheory.T.isLevelAway_definiteUnitaryLevelFromLocalLevels E a w₀ H' hle' hfib' hcpt' hopen' (hae.mono hint'), (open_compact_map hv' (hleI v') (hopen v')).1,
    ⟨φ, hφU, hφ0, fun x hx => hφ x ?_⟩, ?_, fun w hw _ => open_compact_map hw (hleI' w) (hopen' w), ?_, ?_, ?_⟩
  · obtain ⟨hx1, y, hy, e⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨g1, g2, g3⟩ := mem_levelOf.1 hx1
    refine mem_levelOf.2 ⟨g1, g2, fun w hw => ?_⟩
    by_cases h : Apart w v'
    · rw [← h1 w h]; exact g3 w hw
    · refine ⟨y, by rw [hfib w v' h]; exact hy, ?_⟩
      have := GlobalTheory.Cong.LevelExt.one_of_cLoc hv' (y * x⁻¹) (by rw [map_mul, map_inv, e, mul_inv_cancel]) w h
      rwa [map_mul, map_inv, mul_inv_eq_one] at this
  · show (H' v').map (cLoc v') = _
    rw [h2 v' (not_apart_self v'), map_intU hv']
  · rintro w hw - ⟨B, σ, hσ, hB⟩
    obtain ⟨φ', hφ'U, hφ'0, hφ'⟩ := fix_of_fixed hw σ hσ hB.1
    show (H' w).map (cLoc w) = _
    rw [hint' w (hint w ⟨φ', hφ'U, hφ'0, fun x hx =>
      hφ' x (mem_intU.1 hx).1 ((mem_intU.1 hx).2 w (not_apart_self w))⟩), map_intU hw]
  · intro w hw hT x hx hk
    have hap : Apart w w₀ := by
      unfold Apart
      intro h
      have := eq_of_not_apart_of_not_split hw (show ¬ Apart w₀ w from fun h' => h' h.symm)
      exact hw (this ▸ hw₀)
    obtain ⟨φ', hφ'U, hφ'0, hφ'⟩ := hU.2 w hw hT
    exact (mem_levelOf_iff_of_locU hle' hfib' hap hx).2 (by
      rw [hint' w (hint w ⟨φ', hφ'U, hφ'0, fun y hy =>
        hφ' y (mem_intU.1 hy).1 ((mem_intU.1 hy).2 w (not_apart_self w))⟩)]
      exact mem_intU_of hx hk)
  · intro w hw hap x hx
    rw [mem_levelOf_iff_of_locU hle' hfib' hap hx]
    show x ∈ H' w ↔ cLoc w x ∈ (H' w).map (cLoc w)
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨y, hy, e⟩
      rw [← eq_of_cLoc_eq (hle' w hy) hx e]
      exact hy

theorem isLevelAway_inf {w₀ : HeightOneSpectrum (𝓞 E)} {K : Subgroup (UA E a)} (hK : IsLevelAway w₀ K)
    (v' : HeightOneSpectrum (𝓞 E)) {Kv : Subgroup (GL (Fin a) (v'.adicCompletion E))}
    (ho : IsOpen (Kv : Set (GL (Fin a) (v'.adicCompletion E)))) : IsLevelAway w₀ (K ⊓ Kv.comap (cLoc v')) := by
  have hc := GlobalTheory.BCT.GlobLev.continuous_cLoc (n := a) v'
  obtain ⟨N, hN, h1, hNK⟩ := hK.isOpen
  refine ⟨inf_le_left.trans hK.fin, fun x hx => hK.one x hx.1, hK.compact.inter_right ((Kv.isClosed_of_isOpen ho).preimage hc),
    N ∩ cLoc v' ⁻¹' Kv, hN.inter (ho.preimage hc), ⟨h1, by simp⟩, fun x hx hf h => ⟨hNK x hx.1 hf h, hx.2⟩⟩

end UpperTheory.Gal.Int.Cong

end
