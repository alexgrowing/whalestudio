import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.SeenShapeHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PConvRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSatVecUOfDiag

noncomputable section

open Formalism.UG (Hecke conv dosetInd IsCommensurated)
open UpperTheory.Gal.W2.Seed

namespace UpperTheory.Gal.Spc

variable {X M M' : Type} [Group X] [Group M] [Group M']

private theorem fin_out {K : Subgroup X} (hK : IsCommensurated K) {f : X → ℂ} (hf : f ∈ Hecke ℂ K) (c : X ⧸ K → ℂ) :
    (Function.support fun q : X ⧸ K => f q.out * c q).Finite := by
  refine (GlobalTheory.LFun.finite_heckeVec hK hf (1 : Representation ℂ X ℂ) 1).subset fun q hq => ?_
  simpa using left_ne_zero_of_mul hq

private theorem conv_add {K : Subgroup X} (hK : IsCommensurated K) {f f' : X → ℂ} (hf : f ∈ Hecke ℂ K) (hf' : f' ∈ Hecke ℂ K)
    (y : X → ℂ) (g : X) : conv K (f + f') y g = conv K f y g + conv K f' y g := by
  simp only [conv, Pi.add_apply, add_mul]
  exact finsum_add_distrib (fin_out hK hf _) (fin_out hK hf' _)

private theorem conv_smul (K : Subgroup X) (r : ℂ) (f y : X → ℂ) (g : X) : conv K (r • f) y g = r * conv K f y g := by
  simp only [conv, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_finsum]

private theorem ind_one (K : Subgroup X) (g : X) : conv K (dosetInd ℂ K 1) (dosetInd ℂ K 1) g = dosetInd ℂ K 1 g := by
  have h1 : ∀ x, x ∈ DoubleCoset.doubleCoset (1 : X) (K : Set X) K ↔ x ∈ K := fun x => by
    rw [DoubleCoset.mem_doubleCoset]
    exact ⟨by rintro ⟨a, ha, b, hb, rfl⟩; exact mul_mem (mul_mem ha (one_mem K)) hb, fun h => ⟨x, h, 1, one_mem K, by simp⟩⟩
  have h0 : ((1 : X) : X ⧸ K).out ∈ K := by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (1 : X)
    rw [hk, one_mul]
    exact k.2
  rw [conv, finsum_eq_single _ ((1 : X) : X ⧸ K) fun q hq => ?_]
  · rw [dosetInd, Set.indicator_of_mem ((h1 _).2 h0), Pi.one_apply, one_mul]
    by_cases hg : g ∈ K
    · rw [Set.indicator_of_mem ((h1 _).2 hg), Set.indicator_of_mem ((h1 _).2 (mul_mem (inv_mem h0) hg))]
      rfl
    · rw [Set.indicator_of_notMem (mt (h1 _).1 hg), Set.indicator_of_notMem fun h => hg ?_]
      simpa using mul_mem h0 ((h1 _).1 h)
  · rw [dosetInd, Set.indicator_of_notMem fun h => hq ?_, zero_mul]
    rw [← q.out_eq', QuotientGroup.eq]
    simpa using (h1 _).1 h

private theorem lift_ex (T : TyLev X M) (L : Loc X M') (I : Subgroup M') (h1 : L.Fact T.K I) (h2 : T.L.Apart L) (hI : IsCommensurated I)
    (t : M') {φ : M' → ℂ} (hφ : φ ∈ Hecke ℂ I) : ∃ v ∈ Hecke ℂ T.K₀, ∀ g, conv T.K₀ v (T.tf (L.loc t)) g =
      T.tf 1 (g * (L.loc (L.pr g))⁻¹) * conv I φ (dosetInd ℂ I t) (L.pr g) := by
  refine GlobalTheory.LFun.hecke_induction (p := fun φ => ∃ v ∈ Hecke ℂ T.K₀, ∀ g, conv T.K₀ v (T.tf (L.loc t)) g =
      T.tf 1 (g * (L.loc (L.pr g))⁻¹) * conv I φ (dosetInd ℂ I t) (L.pr g)) ⟨0, zero_mem _, fun g => by simp [conv]⟩ ?_ ?_ hφ
  · rintro f hf f' hf' ⟨v, hv, e⟩ ⟨v', hv', e'⟩
    exact ⟨v + v', add_mem hv hv', fun g => by rw [conv_add T.cms hv hv', conv_add hI hf hf', e, e', mul_add]⟩
  · intro r s
    refine ⟨r • T.tf (L.loc s), Submodule.smul_mem _ _ (pTfAdm X M T _ (h2.1 s)).1.1, fun g => ?_⟩
    rw [conv_smul, conv_smul, tfLoc_holds X M M' T L I h1 h2, mul_left_comm]

private theorem inv_ex (T : TyLev X M) (L : Loc X M') (I : Subgroup M') (h1 : L.Fact T.K I) (h2 : T.L.Apart L) (hI : IsCommensurated I)
    (t : M') {φ : M' → ℂ} (hφ : φ ∈ Hecke ℂ I) (e : conv I φ (dosetInd ℂ I t) = dosetInd ℂ I 1) :
    ∃ v ∈ Hecke ℂ T.K₀, conv T.K₀ v (T.tf (L.loc t)) = T.tf 1 := by
  obtain ⟨v, hv, h⟩ := lift_ex T L I h1 h2 hI t hφ
  refine ⟨v, hv, funext fun g => ?_⟩
  have h3 := tfLoc_holds X M M' T L I h1 h2 1 1 g
  rw [map_one, (tfIdem_holds X M T 1 (map_one _)).2.1, ind_one] at h3
  rw [h, e, ← h3]

theorem exists_invertible_hecke_function_at_finite_places : ∀ (X M : Type) [Group X] [Group M] (T : TyLev X M) (ι : Type) (M' : ι → Type) [∀ w, Group (M' w)] (L : ∀ w, Loc X (M' w))
    (I : ∀ w, Subgroup (M' w)) (t : ∀ w, M' w) (W : Finset ι),
    (∀ w ∈ W, (L w).Fact T.K (I w) ∧ T.L.Apart (L w) ∧ ∀ w' ∈ W, w ≠ w' → (L w).Apart (L w')) →
    (∀ w ∈ W, IsCommensurated (I w) ∧ ∃ φ ∈ Hecke ℂ (I w), conv (I w) φ (dosetInd ℂ (I w) (t w)) = dosetInd ℂ (I w) 1) →
    ∃ τ ∈ Subgroup.closure {y | ∃ w ∈ W, y = (L w).loc (t w)}, T.L.pr τ = 1 ∧ (∀ w ∈ W, (L w).pr τ = t w) ∧
      (∀ h, T.L.pr h = 1 → (∀ w ∈ W, (L w).pr h = 1) → conv T.K₀ (T.tf τ) (T.tf h) = conv T.K₀ (T.tf h) (T.tf τ)) ∧
      ∃ u' ∈ Hecke ℂ T.K₀, conv T.K₀ u' (T.tf τ) = T.tf 1 := by
  intro X M _ _ T ι M' _ L I t W
  classical
  induction W using Finset.induction_on with
  | empty =>
    refine fun _ _ => ⟨1, one_mem _, map_one _, by simp, fun h hh _ => ?_, T.tf 1, (pTfAdm X M T 1 (map_one _)).1.1,
      (tfIdem_holds X M T 1 (map_one _)).2.1⟩
    rw [(tfIdem_holds X M T h hh).2.1, (tfIdem_holds X M T h hh).2.2]
  | insert w W hw ih =>
    intro h1 h2
    obtain ⟨τ, m, p0, p1, c, u, hu, e⟩ := ih
      (fun x hx => ⟨(h1 x (Finset.mem_insert_of_mem hx)).1, (h1 x (Finset.mem_insert_of_mem hx)).2.1,
        fun y hy => (h1 x (Finset.mem_insert_of_mem hx)).2.2 y (Finset.mem_insert_of_mem hy)⟩)
      fun x hx => h2 x (Finset.mem_insert_of_mem hx)
    obtain ⟨f1, f2, f3⟩ := h1 w (Finset.mem_insert_self w W)
    obtain ⟨g1, φ, g2, g3⟩ := h2 w (Finset.mem_insert_self w W)
    have ap : ∀ x ∈ W, (L w).Apart (L x) := fun x hx => f3 x (Finset.mem_insert_of_mem hx) fun h => hw (h ▸ hx)
    have q : (L w).pr τ = 1 := (Subgroup.closure_le (L w).pr.ker).2 (by rintro _ ⟨x, hx, rfl⟩; exact (ap x hx).1 _) m
    obtain ⟨v, hv, ev⟩ := inv_ex T (L w) (I w) f1 f2 g1 (t w) g2 g3
    have a1 := (pTfAdm X M T _ (f2.1 (t w))).1.1
    have a2 := (pTfAdm X M T τ p0).1.1
    have R := pConvRing X T.K₀ T.cms
    have e1 := tfMulL_holds X M _ T (L w) (I w) f1 f2 (t w) τ p0 q
    refine ⟨(L w).loc (t w) * τ, mul_mem (Subgroup.subset_closure ⟨w, Finset.mem_insert_self w W, rfl⟩)
      (Subgroup.closure_mono (by rintro _ ⟨x, hx, rfl⟩; exact ⟨x, Finset.mem_insert_of_mem hx, rfl⟩) m),
      by rw [map_mul, f2.1, p0, one_mul], fun x hx => ?_, fun h hh hW => ?_, conv T.K₀ u v, (R u hu v hv).1, ?_⟩
    · rcases Finset.mem_insert.1 hx with rfl | hx
      · rw [map_mul, (L x).pr_loc, q, mul_one]
      · rw [map_mul, (ap x hx).2, p1 x hx, one_mul]
    · have a3 := (pTfAdm X M T h hh).1.1
      have hw1 := hW w (Finset.mem_insert_self w W)
      rw [← e1, (R _ a1 _ a2).2 _ a3, c h hh fun x hx => hW x (Finset.mem_insert_of_mem hx), ← (R _ a1 _ a3).2 _ a2,
        tfMulL_holds X M _ T (L w) (I w) f1 f2 (t w) h hh hw1, ← tfMulR_holds X M _ T (L w) (I w) f1 f2 (t w) h hh hw1,
        (R _ a3 _ a1).2 _ a2]
    · rw [← e1, (R u hu v hv).2 _ (R _ a1 _ a2).1, ← (R v hv _ a1).2 _ a2, ev, (tfIdem_holds X M T τ p0).2.2, e]

end UpperTheory.Gal.Spc
