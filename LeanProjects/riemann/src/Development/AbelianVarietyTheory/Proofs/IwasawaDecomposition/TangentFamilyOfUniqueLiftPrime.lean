import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatDRSubsetLatHT
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.GrNormPos

theorem sInf_pos {C M : Type} [NontriviallyNormedField C] [AddCommGroup M] [Module C M] {g m : ℕ} (V : Fin g → M)
    (U : Fin m → M) (hU : LinearIndependent C U) (L : Set M) (a : C) (ha : a ≠ 0)
    (h1 : ∀ w, ∃ c : Fin g → C, w = ∑ j, c j • V j)
    (h2 : ∀ c : Fin g → C, (∀ j, ‖c j‖ ≤ 1) → ∑ j, c j • V j ∈ L)
    (h3 : ∀ w ∈ L, ∃ c : Fin g → C, (∀ j, ‖c j‖ ≤ 1) ∧ a • w = ∑ j, c j • V j) (i : Fin m) :
    0 < sInf {r | ∃ cf : Fin m → C, cf i ≠ 0 ∧ (∀ k, i < k → cf k = 0) ∧ (∑ k, cf k • U k ∈ L) ∧
      r = ‖cf i‖⁻¹} := by
  classical
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination C U)
    (LinearMap.ker_eq_bot.2 (linearIndependent_iff_injective_fintypeLinearCombination.1 hU))
  have hl' : ∀ cf : Fin m → C, l (∑ k, cf k • U k) = cf := fun cf => by
    have := LinearMap.congr_fun hl cf
    rwa [LinearMap.comp_apply, Fintype.linearCombination_apply] at this
  set B : ℝ := ∑ j, ‖l (V j) i‖ + 1 with hB
  have hB0 : 0 < B := by positivity
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha
  refine lt_of_lt_of_le (div_pos ha0 hB0) (le_csInf ?_ ?_)
  · obtain ⟨c, hc⟩ := h1 (U i)
    obtain ⟨e, he⟩ := NormedField.exists_lt_norm C ‖c‖
    have he0 : 0 < ‖e‖ := (norm_nonneg c).trans_lt he
    have he1 : e ≠ 0 := norm_pos_iff.1 he0
    refine ⟨_, Pi.single i e⁻¹, by simpa using he1, fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_, rfl⟩
    have : ∑ k, (Pi.single i e⁻¹ : Fin m → C) k • U k = ∑ j, (e⁻¹ * c j) • V j := by
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp), Pi.single_eq_same, hc,
        Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_smul _ _ _
    rw [this]
    refine h2 _ fun j => ?_
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ he0, mul_one]
    exact (norm_le_pi_norm c j).trans he.le
  · rintro r ⟨cf, h0, -, hL, rfl⟩
    obtain ⟨c, hc, e⟩ := h3 _ hL
    have e2 : a * cf i = ∑ j, c j * l (V j) i := by
      have := congrArg (fun z => l z i) e
      simpa [map_smul, hl', map_sum, Finset.sum_apply] using this
    have e3 : ‖a‖ * ‖cf i‖ ≤ B := by
      rw [← norm_mul, e2]
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ => ?_).trans (le_add_of_nonneg_right zero_le_one))
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hc j)
    have h0' : 0 < ‖cf i‖ := norm_pos_iff.2 h0
    rw [div_le_iff₀ hB0, le_inv_mul_iff₀ h0', mul_comm]
    exact e3

open GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections MonObj

attribute [local instance] Over.cartesianMonoidalCategory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X}

theorem isComb_iff_eq {m : ℕ} {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hu : ∀ i, IsTanAtG t x (u i))
    (a : Fin m → S) (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x u a w ↔ w = (tv (∑ i, a i • tanOf (hu i))).left := by
  have h0 : IsCombAtG t x u a (tv (∑ i, a i • tanOf (hu i))).left := (isComb_iff (fun i => tanOf (hu i)) a _).2 rfl
  refine ⟨fun h => ?_, fun h => h ▸ h0⟩
  obtain ⟨v, hv, e⟩ := h
  obtain ⟨v', hv', e'⟩ := h0
  have : v = v' := funext fun i => Over.OverMorphism.ext ((hv i).trans (hv' i).symm)
  rw [← e, ← e', this]

end

theorem grNorm_pos : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (p : ℕ) (C : Formalism.MainNotions.DIV.Cons.SCF p) (b : Bool) (xO : Sp ↥(intO ↥C.S) ⟶ X), p.Prime → (∀ y : Sp ↥(intO ↥C.S) ⟶ X, spMap (intO ↥C.S).subtype ≫ y = spMap (intO ↥C.S).subtype ≫ xO → y = xO) → ∀ (m : ℕ) (u : Fin m → (Sp (DualNumber ↥C.S) ⟶ t.G.left)), (∀ i, IsTanAtG t (spMap (intO ↥C.S).subtype ≫ xO) (u i)) → (∀ cf cf' w, IsCombAtG t (spMap (intO ↥C.S).subtype ≫ xO) u cf w → IsCombAtG t (spMap (intO ↥C.S).subtype ≫ xO) u cf' w → cf = cf') → ∀ i, 0 < GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ↥C.S).subtype ≫ xO) (lat t p (spMap (intO ↥C.S).subtype ≫ xO) b) u i := by
  intro hHT E _ _ _ H X t p C b xO hp huniq m u hu hinj i
  haveI : Fact p.Prime := Fact.mk hp
  obtain ⟨g, v, hv, hb, hL⟩ := GlobalTheory.LatDRFree.latDR_free E H X t C.S xO huniq
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.2 hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpa : ‖(p : C.S)‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by
    rw [C.norm_p, ← Real.rpow_neg_one]
    refine Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg ?_)
    rw [div_le_one (by linarith)]
    linarith
  have hsub : latDR t (spMap (intO ↥C.S).subtype ≫ xO) ⊆ lat t p (spMap (intO ↥C.S).subtype ≫ xO) b := by
    cases b
    · exact subset_rfl
    · exact latDR_subset_latHT E H X t C.S p _
  have hsup : lat t p (spMap (intO ↥C.S).subtype ≫ xO) b ⊆ latHT t p (spMap (intO ↥C.S).subtype ≫ xO) := by
    cases b
    · exact latDR_subset_latHT E H X t C.S p _
    · exact subset_rfl
  have h1 : ∀ w : TanM (spMap (intO ↥C.S).subtype ≫ xO) t.G, ∃ c : Fin g → C.S, w = ∑ j, c j • tanOf (hv j) :=
    fun w => by
      obtain ⟨c, hc, -⟩ := hb _ (isTan_tv w)
      exact ⟨c, tan_ext ((isComb_iff_eq hv c _).1 hc)⟩
  have key := sInf_pos (fun j => tanOf (hv j)) (fun k => tanOf (hu k)) ?_
    {w | (tv w).left ∈ lat t p (spMap (intO ↥C.S).subtype ≫ xO) b} (p : C.S) (Nat.cast_ne_zero.2 hp.ne_zero) h1
    ?_ ?_ i
  · unfold GlobalTheory.ShFam.Pad.grNorm
    refine key.trans_eq (congrArg sInf (Set.ext fun r => exists_congr fun cf => and_congr_right fun _ =>
      and_congr_right fun _ => and_congr_left fun _ => Iff.symm ?_))
    refine ⟨?_, fun h => ⟨_, h, (isComb_iff_eq hu cf _).2 rfl⟩⟩
    rintro ⟨w, hw, hc⟩
    rw [(isComb_iff_eq hu cf _).1 hc] at hw
    exact hw
  · refine Fintype.linearIndependent_iff.2 fun c hc k => ?_
    have := hinj c 0 _ ((isComb_iff_eq hu c _).2 rfl) ((isComb_iff_eq hu 0 _).2 (by rw [hc]; simp))
    exact congrFun this k
  · intro c hc
    exact hsub ((hL c _ ((isComb_iff_eq hv c _).2 rfl)).2 hc)
  · intro w hw
    have h := hHT E H X t p C.S C.norm_p xO huniq _ (hsup hw) (p : C.S) hpa
    obtain ⟨c, hc⟩ := h1 ((p : C.S) • w)
    refine ⟨c, (hL c _ ((isComb_iff_eq hv c _).2 rfl)).1 ?_, hc⟩
    rw [← hc]
    exact h

end GlobalTheory.GrNormPos
