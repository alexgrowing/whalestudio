import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

open Formalism.L2.Host (HChar)

namespace GlobalTheory.TopFlipNu

theorem exists_pow_close {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x c : w.adicCompletion E)
    (hx : Valued.v x = 1) (hc : c ≠ 0) : ∃ k : ℕ, 0 < k ∧ Valued.v (x ^ k - 1) ≤ Valued.v c := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have hK : IsCompact {y : w.adicCompletion E | Valued.v y ≤ 1} := by
    have := IsNonarchimedeanLocalField.isCompact_closedBall (w.adicCompletion E) 1
    convert this using 1
    ext y
    exact e.le_one_iff_le_one.symm
  have hv0 : Valued.v c ≠ 0 := by simpa using hc
  obtain ⟨s, -, hs⟩ := hK.elim_nhds_subcover (fun y => {z | (z - y) * c⁻¹ ∈ w.adicCompletionIntegers E}) fun y _ =>
    ((Valued.isOpen_valuationSubring _).preimage ((continuous_id.sub continuous_const).mul continuous_const)).mem_nhds
      (by simp)
  have h1 : ∀ n : ℕ, ∃ y : s, Valued.v (x ^ n - y) ≤ Valued.v c := fun n => by
    have : x ^ n ∈ {y : w.adicCompletion E | Valued.v y ≤ 1} := by simp [hx]
    obtain ⟨y, hy, h⟩ := Set.mem_iUnion₂.1 (hs this)
    refine ⟨⟨y, hy⟩, ?_⟩
    have h2 : Valued.v ((x ^ n - y) * c⁻¹) ≤ 1 := h
    rwa [map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 hv0), one_mul] at h2
  choose f hf using h1
  have key : ∀ a b : ℕ, a < b → f a = f b → ∃ k : ℕ, 0 < k ∧ Valued.v (x ^ k - 1) ≤ Valued.v c := fun a b hab h => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
    refine ⟨k + 1, by omega, ?_⟩
    have h3 := Valuation.map_sub_le _ (hf (a + k + 1)) (h ▸ hf a)
    have h4 : x ^ (a + k + 1) - f (a + k + 1) - (x ^ a - f (a + k + 1)) = x ^ a * (x ^ (k + 1) - 1) := by ring
    rwa [h4, map_mul, map_pow, hx, one_pow, one_mul] at h3
  obtain ⟨a, b, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hne with h' | h'
  exacts [key a b h' h, key b a h' h.symm]

theorem exists_pow_eq_one {E : Type} [Field E] [NumberField E] {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    (h : χ.LevelLe w n) (x : (w.adicCompletion E)ˣ) (hx : Valued.v (x : w.adicCompletion E) = 1) :
    ∃ k : ℕ, 0 < k ∧ χ.loc w x ^ k = 1 := by
  have hu := Formalism.L2.Host.unif_spec w
  unfold Formalism.L2.Host.IsUnifAt at hu
  obtain ⟨k, hk, h1⟩ := exists_pow_close w x
    (((Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) ^ n) hx
    (pow_ne_zero _ (Units.ne_zero _))
  refine ⟨k, hk, ?_⟩
  rw [← map_pow]
  refine h _ ?_ ?_
  · show Valued.v _ = 1
    rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]
  · rw [map_pow, hu, ← WithZero.exp_nsmul] at h1
    rw [Units.val_pow_eq_pow_val]
    simpa using h1

theorem awayIm_unit {D : D7} {χ : HChar D.host.E} (hχ : LocIn D.what₂.embLL χ) {w : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ}
    (h : χ.LevelLe w n) (x : (w.adicCompletion D.host.E)ˣ) (hx : Valued.v (x : w.adicCompletion D.host.E) = 1) (m : ℕ) :
    GlobalTheory.KappaArith.AwayIm D m (χ.loc w x : ℂ) := by
  obtain ⟨k, hk, h1⟩ := exists_pow_eq_one h x hx
  obtain ⟨ζ, hζ⟩ := hχ w x
  have h2 : ζ ^ k = 1 := D.what₂.embLL.injective (by rw [map_pow, hζ, map_one, ← Units.val_pow_eq_pow_val, h1, Units.val_one])
  exact ⟨ζ, GlobalTheory.KappaArith.isAwayUnit_of_pow_eq_one m hk h2, hζ⟩

theorem chi_levelLe {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {i : ℕ} (h1 : 1 ≤ i)
    (h2 : i ≤ D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)) : (G.ch.chiH i).LevelLe w 2 := by
  by_cases h : w.under (𝓞 D.host.F) ∈ G.pl.S0
  · rcases G.pl.mem_S0_of_sum_eq.1 h with h | h
    · exact fun x hx h3 => (G.ch.lev0 i h1 h2 w h).1 x hx (h3.trans (WithZero.exp_le_exp.2 (by omega)))
    · exact (G.ch.lev1 i h1 h2 w h).1
  · exact fun x hx _ => G.ch.unr i h1 h2 w h x hx

theorem nu_arith : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → CharsIn G D.what₂.embLL → ∀ (i j : Fin D.R.m) (x : ∀ w : Pl D.host.E, (Kw w)ˣ) (t : T),
      (∀ w ∈ locPl G t, ValuativeRel.valuation (Kw w) (x w : Kw w) = 1) →
      ∃ z : ℂ, GlobalTheory.KappaArith.AwayIm D (Qn G t) z ∧ ∏ w ∈ locPl G t, (((locGrid G t w).nu i j (x w) : ℂˣ) : ℂ) =
        z * ∏ w ∈ locPl G μ₀, (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ) := by
  classical
  intro D T L sc G μ₀ hL hC i j x t hx
  have hQ : L.Q μ₀ = ∅ := Finset.eq_empty_of_forall_notMem fun w hw =>
    (hL.Q_ram μ₀ w).2 (Or.inl hw) (by rw [hL.xi_base]; intro x _; rfl)
  have h0 : locPl G μ₀ = G.pl.W0 := by rw [locPl, hQ]; simp
  have hsub : G.pl.W0 ⊆ locPl G t := fun w hw => by unfold locPl; simp [hw]
  have hf : ∀ w, (((locGrid G t w).nu i j (x w) : ℂˣ) : ℂ) =
      ((L.xiH t).loc w (x w) : ℂ) * (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ) := fun w => by
    simp only [Grid.nu, locGrid, MonoidHom.div_apply, Formalism.L2.Host.HChar.loc_mul, hL.xi_base, Formalism.L2.Host.HChar.loc_one,
      Units.val_div_eq_div_val, Units.val_mul, Units.val_one]
    ring
  have hb : ∀ w ∈ locPl G t, GlobalTheory.KappaArith.AwayIm D (Qn G t) (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ) := fun w hw => by
    haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
    have e := ValuativeRel.isEquiv (ValuativeRel.valuation (Kw w)) (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ)))
    have hv : Valued.v (x w : Kw w) = 1 := e.eq_one_iff_eq_one.1 (hx w hw)
    have hv' : Valued.v (((x w)⁻¹ : (Kw w)ˣ) : Kw w) = 1 := by rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
    have h1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
    have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
    have a := awayIm_unit (hC.mu0 j) ((L.C.isMu0 j).tame w) (x w) hv (Qn G t)
    have b := awayIm_unit (hC.chi _ h1 h2) (chi_levelLe G h1 h2 w) (x w)⁻¹ hv' (Qn G t)
    have hm : muBase L (j + 1) = L.C.mu0 j := by rw [muBase, dif_pos j.2]
    convert a.mul b using 1
    simp only [Grid.nu, locGrid, MonoidHom.div_apply, hL.xi_base, mul_one, hm, map_inv,
      Units.val_div_eq_div_val, Units.val_inv_eq_inv_val]
    exact div_eq_mul_inv _ _
  refine ⟨(∏ w ∈ locPl G t, ((L.xiH t).loc w (x w) : ℂ)) *
    ∏ w ∈ locPl G t \ G.pl.W0, (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ), ?_, ?_⟩
  · exact (GlobalTheory.KappaArith.AwayIm.prod _ _ fun w _ => GlobalTheory.KappaArith.awayIm_val hL (hC.xi t) _ w (x w)).mul
      (GlobalTheory.KappaArith.AwayIm.prod _ _ fun w hw => hb w (Finset.mem_sdiff.1 hw).1)
  · rw [h0, mul_assoc, Finset.prod_sdiff hsub, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w _ => hf w

end GlobalTheory.TopFlipNu
