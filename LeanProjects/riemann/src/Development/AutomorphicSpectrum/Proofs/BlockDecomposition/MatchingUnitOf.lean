import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebra
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSphNe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetSumCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermHeckeFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasCompactSupportTj

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MatchUnit

theorem hint_ind_conv {H : Type} [Group H] (K : Subgroup H) (y : H) :
    hint K (fun z => (K : Set H).indicator (1 : H → ℂ) z * (K : Set H).indicator (1 : H → ℂ) (z⁻¹ * y)) =
      (K : Set H).indicator (1 : H → ℂ) y := by
  by_cases hy : y ∈ K
  · have e : (fun z => (K : Set H).indicator (1 : H → ℂ) z * (K : Set H).indicator (1 : H → ℂ) (z⁻¹ * y)) =
        (K : Set H).indicator (1 : H → ℂ) := by
      funext z
      by_cases hz : z ∈ K
      · have hzy : z⁻¹ * y ∈ K := mul_mem (inv_mem hz) hy
        simp [Set.indicator_of_mem (show z ∈ (K : Set H) from hz),
          Set.indicator_of_mem (show z⁻¹ * y ∈ (K : Set H) from hzy)]
      · simp [Set.indicator_of_notMem (show z ∉ (K : Set H) from hz)]
    rw [e, GlobalTheory.CompanionTheory.FamClP.hint_ind, Set.indicator_of_mem (show y ∈ (K : Set H) from hy)]
    rfl
  · have e : (fun z => (K : Set H).indicator (1 : H → ℂ) z * (K : Set H).indicator (1 : H → ℂ) (z⁻¹ * y)) =
        fun _ => (0 : ℂ) := by
      funext z
      by_cases hz : z ∈ K
      · have hzy : z⁻¹ * y ∉ K := fun h => hy (by simpa using mul_mem hz h)
        simp [Set.indicator_of_notMem (show z⁻¹ * y ∉ (K : Set H) from hzy)]
      · simp [Set.indicator_of_notMem (show z ∉ (K : Set H) from hz)]
    rw [e, GlobalTheory.CompanionTheory.FamClP.hint_zero, Set.indicator_of_notMem (show y ∉ (K : Set H) from hy)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_mem_KGL_iff {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    blk h w m (Multiplicative.toAdd X) ∈ GlobalTheory.LFun.KGL w n ↔ m ∈ K2 a b w ∧ X ∈ intMat a b w := by
  obtain ⟨hN, hM⟩ := GlobalTheory.CompanionTheory.LeviInt.comap_uN_and_map_sM E a b n h w
  have hdiag : ∀ c ∈ K2 a b w, blk h w c 0 ∈ GlobalTheory.LFun.KGL w n := fun c hc => hM ⟨c, hc, rfl⟩
  have hNK : ∀ Z, Z ∈ intMat a b w ↔ blk h w 1 (Multiplicative.toAdd Z) ∈ GlobalTheory.LFun.KGL w n := by
    intro Z
    rw [← hN, Subgroup.mem_comap, Subgroup.mem_subgroupOf, GlobalTheory.LeviFubini.uN_val]
  have hsplit : blk h w m (Multiplicative.toAdd X) = blk h w m 0 * blk h w 1 (Multiplicative.toAdd X) := by
    have := GlobalTheory.CompanionTheory.IntDec.blk_add h w m 0 (Multiplicative.toAdd X)
    simpa using this
  constructor
  · intro hb
    have hm : m ∈ K2 a b w := by
      have h2 := GlobalTheory.LeviFubini.levH_mem_KGL_of_mem E a b n h w
        ⟨blk h w m (Multiplicative.toAdd X), GlobalTheory.LeviFubini.blk_mem h w m _⟩ hb
      rw [GlobalTheory.LeviFubini.levH_blk] at h2
      exact Subgroup.mem_prod.2 h2
    refine ⟨hm, (hNK X).2 ?_⟩
    have e : blk h w 1 (Multiplicative.toAdd X) = (blk h w m 0)⁻¹ * blk h w m (Multiplicative.toAdd X) := by
      rw [hsplit]
      group
    rw [e]
    exact mul_mem (inv_mem (hdiag m hm)) hb
  · rintro ⟨hm, hX⟩
    rw [hsplit]
    exact mul_mem (hdiag m hm) ((hNK X).1 hX)

variable {n : ℕ}

theorem val_toSub {w : Pl E} (hU : UL n w = ⊤) (y : GLw n w) : ((toSub (UL n w) y : UL n w) : GLw n w) = y := by
  have hy : y ∈ UL n w := hU ▸ Subgroup.mem_top y
  simp [toSub, hy]

theorem lone_toSub {w : Pl E} (hU : UL n w = ⊤) (y : GLw n w) :
    lone (KL n w) (toSub (UL n w) y) = if y ∈ GlobalTheory.LFun.KGL w n then 1 else 0 := by
  rw [GlobalTheory.CompanionTheory.UnitaryWord.lone_KL]
  unfold GlobalTheory.CompanionTheory.UnitaryWord.unitFn
  by_cases hy : y ∈ GlobalTheory.LFun.KGL w n
  · have : toSub (UL n w) y ∈ (KL n w : Set (UL n w)) := by
      show toSub (UL n w) y ∈ KL n w
      rw [KL, Subgroup.mem_subgroupOf, val_toSub hU]
      exact hy
    rw [if_pos hy, Set.indicator_of_mem this]
    rfl
  · have : toSub (UL n w) y ∉ (KL n w : Set (UL n w)) := by
      intro h'
      have h'' : toSub (UL n w) y ∈ KL n w := h'
      rw [KL, Subgroup.mem_subgroupOf, val_toSub hU] at h''
      exact hy h''
    rw [if_neg hy, Set.indicator_of_notMem this]

theorem ct_lone {a b : ℕ} (h : a + b = n) {w : Pl E} (hU : UL n w = ⊤) (m : GLw a w × GLw b w) :
    ct h w (fun y => lone (KL n w) (toSub (UL n w) y)) m = if m ∈ K2 a b w then 1 else 0 := by
  have hk : ∀ X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)),
      GlobalTheory.BCT.avg (fun k : GlobalTheory.LFun.KGL w n => lone (KL n w) (toSub (UL n w)
        ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k))) =
      if m ∈ K2 a b w ∧ X ∈ intMat a b w then 1 else 0 := by
    intro X
    have e : (fun k : GlobalTheory.LFun.KGL w n => lone (KL n w) (toSub (UL n w)
        ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k))) =
        fun _ => if m ∈ K2 a b w ∧ X ∈ intMat a b w then (1 : ℂ) else 0 := by
      funext k
      rw [lone_toSub hU]
      have hiff : (k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k ∈ GlobalTheory.LFun.KGL w n ↔
          m ∈ K2 a b w ∧ X ∈ intMat a b w := by
        rw [← blk_mem_KGL_iff h w m X, Subgroup.mul_mem_cancel_right _ k.2,
          Subgroup.mul_mem_cancel_left _ (inv_mem k.2)]
      simp only [hiff]
    rw [e]
    exact GlobalTheory.CompanionTheory.CtS.avg_const _
  unfold ct
  simp only [hk]
  by_cases hm : m ∈ K2 a b w
  · obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hm
    have hv : Valued.v (m.1.val.det ^ b / m.2.val.det ^ a) = 1 := by
      rw [map_div₀, map_pow, map_pow, GlobalTheory.CompanionTheory.CtHecke.v_det h1, GlobalTheory.CompanionTheory.CtHecke.v_det h2]
      simp
    have habs : absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) = 1 := by
      unfold absHalf
      rw [GlobalTheory.CompanionTheory.CtHecke.ordL_eq_zero hv]
      simp
    have e : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        if m ∈ K2 a b w ∧ X ∈ intMat a b w then (1 : ℂ) else 0) =
        (intMat a b w : Set _).indicator 1 := by
      funext X
      by_cases hX : X ∈ intMat a b w
      · simp [hm, hX, Set.indicator_of_mem (show X ∈ (intMat a b w : Set _) from hX)]
      · simp [hX, Set.indicator_of_notMem (show X ∉ (intMat a b w : Set _) from hX)]
    rw [e, GlobalTheory.CompanionTheory.FamClP.hint_ind, habs, if_pos hm, mul_one]
  · have e : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        if m ∈ K2 a b w ∧ X ∈ intMat a b w then (1 : ℂ) else 0) = fun _ => 0 := by
      funext X
      simp [hm]
    rw [e, GlobalTheory.CompanionTheory.FamClP.hint_zero, if_neg hm, mul_zero]

theorem ctMu_lone {a b : ℕ} (h : a + b = n) {w : Pl E} (hU : UL n w = ⊤) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : ∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1) :
    ctMu h w μ (lone (KL n w)) = idem (K2 a b w) := by
  funext m
  unfold ctMu
  rw [ct_lone h hU]
  by_cases hm : m ∈ K2 a b w
  · have h1 : μ (-1) = 1 := by
      refine hμ _ (GlobalTheory.CompanionTheory.CtHecke.ordL_eq_zero ?_)
      simp
    have hu := GlobalTheory.CompanionTheory.CtHecke.mu_unit hμ hm
    have e : μ ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) = 1 := by
      rw [mul_assoc, map_mul, hu, map_pow, h1]
      simp
    rw [e, if_pos hm]
    unfold idem
    rw [Set.indicator_of_mem (show m ∈ (K2 a b w : Set _) from hm), Subgroup.relIndex_self]
    simp
  · rw [if_neg hm, mul_zero]
    unfold idem
    rw [Set.indicator_of_notMem (show m ∉ (K2 a b w : Set _) from hm)]

theorem lpow_lone_one {w : Pl E} : lpow (KL n w) (lone (KL n w)) 1 = (KL n w : Set (UL n w)).indicator 1 := by
  funext y
  show lconv (lone (KL n w)) (lone (KL n w)) y = _
  rw [GlobalTheory.CompanionTheory.UnitaryWord.lone_KL]
  exact hint_ind_conv (KL n w) y

theorem isHecke_lone_KL (hE : Unr E) {w : Pl E} : IsHecke (KL n w) (lone (KL n w)) := by
  rw [GlobalTheory.CompanionTheory.UnitaryWord.lone_KL]
  refine ⟨HasCompactSupport.intro (GlobalTheory.CompanionTheory.SphLine.isCompact_KL hE n w) fun x hx =>
    Set.indicator_of_notMem hx _, fun k hk x => ?_⟩
  have h1 : k * x ∈ KL n w ↔ x ∈ KL n w := Subgroup.mul_mem_cancel_left _ hk
  have h2 : x * k ∈ KL n w ↔ x ∈ KL n w := Subgroup.mul_mem_cancel_right _ hk
  unfold GlobalTheory.CompanionTheory.UnitaryWord.unitFn
  by_cases hx : x ∈ KL n w
  · exact ⟨by rw [Set.indicator_of_mem (show k * x ∈ (KL n w : Set _) from h1.2 hx),
      Set.indicator_of_mem (show x ∈ (KL n w : Set _) from hx)]; rfl,
      by rw [Set.indicator_of_mem (show x * k ∈ (KL n w : Set _) from h2.2 hx),
      Set.indicator_of_mem (show x ∈ (KL n w : Set _) from hx)]; rfl⟩
  · exact ⟨by rw [Set.indicator_of_notMem (show k * x ∉ (KL n w : Set _) from fun h => hx (h1.1 h)),
      Set.indicator_of_notMem (show x ∉ (KL n w : Set _) from hx)],
      by rw [Set.indicator_of_notMem (show x * k ∉ (KL n w : Set _) from fun h => hx (h2.1 h)),
      Set.indicator_of_notMem (show x ∉ (KL n w : Set _) from hx)]⟩

theorem isOpen_levelSubgroup' (a b : ℕ) (w : Pl E) : IsOpen (K2 a b w : Set (GLw a w × GLw b w)) := by
  have e : (K2 a b w : Set (GLw a w × GLw b w)) =
      (GlobalTheory.LFun.KGL w a : Set (GLw a w)) ×ˢ (GlobalTheory.LFun.KGL w b : Set (GLw b w)) := rfl
  rw [e]
  exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1

theorem matchLMUnitOf : PositivityTheory.Rg.BcB.F.MLM.MatchLMUnitOf := by
  intro hI hS hId E _ _ _ hE n d _ a ha w hwB hgood
  have hT : w ∉ d.T := fun h => hwB (by simp [LocData.B, h])
  have hS₀ : w ∉ d.S₀ := fun h => hwB (by simp [LocData.B, h])
  have hBad : w ∉ d.Bad := fun h => hwB (by simp [LocData.B, h])
  have hP : w ∉ d.P := by simp [LocData.P, hT, hS₀]
  have hlev : d.lev a w = K2 a (n - a) w := by
    unfold LocData.lev
    rw [if_neg hT, if_neg (by simp [hS₀, hBad])]
  have htr : (d.eL a).tr d.P d.one w = idem (K2 a (n - a) w) := by
    unfold LM.tr
    rw [if_neg hP]
    show idem (d.lev a w) = _
    rw [hlev]
  rw [htr]
  by_cases hw : IsSplitAt w
  · rw [if_pos hw]
    obtain ⟨-, -, -, -, hμ⟩ := hgood hw
    have hU : UL n w = ⊤ := if_pos hw
    have hc := ctMu_lone (Nat.add_sub_cancel' ha) hU (d.μ w) hμ
    have h : Match n a (n - a) w (d.μ w) (lpow (KL n w) (lone (KL n w)) 1)
        (mconv (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (lone (KL n w)))
          (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (lone (KL n w)))) :=
      hS E n a ha w hw (d.μ w) hμ (lone (KL n w)) (isHecke_lone_KL hE) 1 le_rfl
    obtain ⟨hH, -, hU'⟩ := hId E a (n - a) w (K2 a (n - a) w) (isOpen_levelSubgroup' a (n - a) w) le_rfl
    rw [hc, (hU' _ hH).1, lpow_lone_one] at h
    exact h
  · rw [if_neg hw]
    exact hI E hE w hw n a ha

end GlobalTheory.CompanionTheory.MatchUnit

end
