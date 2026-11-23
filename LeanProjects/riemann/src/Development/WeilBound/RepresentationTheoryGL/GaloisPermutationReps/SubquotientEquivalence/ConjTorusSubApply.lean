import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCommensuratedKO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount.B

namespace TorusConjugationFixed

open GlobalTheory.IwahoriInj GlobalTheory.DepthZeroJac

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem range_le_fixed {τ : Representation ℂ (GL (Fin n) 𝓀[k]) W}
    {π : Representation ℂ (GL (Fin n) k) V} {j : W →ₗ[ℂ] V} (hj : IsTypeMap τ π j) :
    LinearMap.range j ≤ fixed π (KOne k (Fin n)) := by
  rintro _ ⟨w, rfl⟩
  refine GlobalTheory.IwahoriInj.mem_fixed.2 fun g hg => ?_
  have h1 := hj.2 ⟨g, GlobalTheory.StepData.KOne_le_KO hg⟩ w
  rw [(redK_eq_one_iff ⟨g, GlobalTheory.StepData.KOne_le_KO hg⟩).2 hg, map_one, Module.End.one_apply] at h1
  exact h1.symm

theorem redK_incl (a : GL (Fin n) 𝒪[k]) :
    redK k (Fin n) ⟨incl k n a, incl_mem_KO a⟩ = red k n a := by
  ext i l
  rw [redK_apply]
  rfl

theorem inv_val_torusElt (ϖ : kˣ) (a : Fin n → ℤ) :
    ((GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ a)⁻¹).val = diagonal fun i => ((ϖ : k) ^ a i)⁻¹ := by
  set t := GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ a
  have h1 : t.val * diagonal (fun i => ((ϖ : k) ^ a i)⁻¹) = 1 := by
    rw [GlobalTheory.GLDoubling.val_torusElt, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (zpow_ne_zero _ (Units.ne_zero ϖ))
  calc (t⁻¹).val = (t⁻¹).val * (t.val * diagonal (fun i => ((ϖ : k) ^ a i)⁻¹)) := by rw [h1, mul_one]
    _ = _ := by rw [← mul_assoc, Units.inv_mul, one_mul]

theorem conj_torus_sub_apply (ϖ : kˣ) (a : Fin n → ℤ) (g : GL (Fin n) k) (i l : Fin n) :
    ((GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ a * g * (GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ a)⁻¹).val - 1) i l =
      (ϖ : k) ^ a i * (g.val - 1) i l * ((ϖ : k) ^ a l)⁻¹ := by
  set t := GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ a
  have : (t * g * t⁻¹).val - 1 = t.val * (g.val - 1) * (t⁻¹).val := by
    simp [mul_sub, sub_mul]
  rw [this, inv_val_torusElt, GlobalTheory.GLDoubling.val_torusElt, mul_diagonal, diagonal_mul]

theorem torusElt_const (ϖ : kˣ) (c : ℤ) :
    GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ (fun _ => c) = GeneralLinearGroup.scalar (Fin n) (ϖ ^ c) := by
  ext i l
  rw [GlobalTheory.GLDoubling.val_torusElt, GeneralLinearGroup.coe_scalar]
  simp [Matrix.diagonal_apply, Matrix.scalar_apply, Units.val_zpow_eq_zpow_val]

def side (a : Fin n → ℤ) (i : Fin n) : Fin 2 := if ∀ l, a l ≤ a i then 0 else 1

def bl (a : Fin n → ℤ) : (Σ b : Fin 2, Fin (Fintype.card {x // side a x = b})) ≃ Fin n :=
  (Equiv.sigmaCongrRight fun b => (Fintype.equivFin {x // side a x = b}).symm).trans (Equiv.sigmaFiberEquiv (side a))

theorem blk_bl (a : Fin n → ℤ) (i : Fin n) : blk (bl a) i = side a i := rfl

theorem blk_lt_iff (a : Fin n → ℤ) (i l : Fin n) :
    blk (bl a) i < blk (bl a) l ↔ (∀ x, a x ≤ a i) ∧ ¬ ∀ x, a x ≤ a l := by
  rw [blk_bl, blk_bl]
  unfold side
  by_cases h1 : ∀ x, a x ≤ a i <;> by_cases h2 : ∀ x, a x ≤ a l <;> simp [h1, h2]

theorem deep_zpow {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (m : ℤ) : Deep m ((ϖ : k) ^ m) := by
  unfold Deep
  rw [map_zpow₀, hϖ]

theorem deep_inv_zpow {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (m : ℤ) :
    Deep (-m) (((ϖ : k) ^ m)⁻¹) := by
  unfold Deep
  rw [map_inv₀, map_zpow₀, hϖ, _root_.zpow_neg]

theorem torus_mem_twKer {τ : Representation ℂ (GL (Fin n) 𝓀[k]) W} (hτ : FinCusp τ)
    {π : Representation ℂ (GL (Fin n) k) V} {j : W →ₗ[ℂ] V} (hj : IsTypeMap τ π j)
    {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (a : Fin n → ℤ) (ha : ∃ i l, a i ≠ a l) (w : W) :
    π (GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ a) (j w) ∈ twKer π (KOne k (Fin n)) 1 := by
  classical
  set t := GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ a with ht
  set e := bl a
  obtain ⟨i1, l1, h1⟩ := ha
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ a ⟨i1, Finset.mem_univ _⟩
  have hmax : ∀ x, a x ≤ a i0 := fun x => hi0 x (Finset.mem_univ _)
  have hj0 : ∃ l0, ¬ ∀ x, a x ≤ a l0 := by
    rcases lt_or_gt_of_ne h1 with h | h
    · exact ⟨i1, fun hh => absurd (hh l1) (not_le.2 h)⟩
    · exact ⟨l1, fun hh => absurd (hh i1) (not_le.2 h)⟩
  obtain ⟨l0, hl0⟩ := hj0
  have hne : unipRad 𝓀[k] e ≠ ⊥ :=
    GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.2 ⟨i0, l0, (blk_lt_iff a i0 l0).2 ⟨hmax, hl0⟩⟩
  haveI := Fintype.ofFinite (unipRad 𝓀[k] e)

  have hsum : ∑ u : unipRad 𝓀[k] e, τ u w = 0 := by
    refine hτ 2 _ e hne _ fun x hx => ?_
    rw [map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨x, hx⟩ : unipRad 𝓀[k] e)) _ _ fun u => ?_
    rw [Equiv.coe_mulLeft]
    show _ = τ (x * (u : GL (Fin n) 𝓀[k])) w
    rw [map_mul, Module.End.mul_apply]

  have hterm : ∀ u : unipRad 𝓀[k] e, π t (j w) - π t (j (τ u w)) ∈ twKer π (KOne k (Fin n)) 1 := by
    intro u
    obtain ⟨b, hb, hb1, -⟩ := exists_lift (k := k) (Z := fun i l => (∀ x, a x ≤ a i) ∧ ¬ ∀ x, a x ≤ a l)
      (fun i m l h1 h2 => h1.2 h2.1) (u : GL (Fin n) 𝓀[k]) (fun i l h => by
        have := (GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries.1 u.2) i l (fun h' => h ((blk_lt_iff a i l).1 h'))
        rw [Matrix.sub_apply, this, sub_self])
    have hred : τ u w = τ (redK k (Fin n) ⟨incl k n b, incl_mem_KO b⟩) w := by rw [redK_incl, hb]
    rw [hred, hj.2]
    have hK : t * incl k n b * t⁻¹ ∈ KOne k (Fin n) := by
      refine GlobalTheory.StepData.mem_KOne.2 fun i l => ?_
      rw [conj_torus_sub_apply]
      by_cases hZ : (∀ x, a x ≤ a i) ∧ ¬ ∀ x, a x ≤ a l
      · have hil : a l < a i := by
          obtain ⟨x, hx⟩ := not_forall.1 hZ.2
          exact lt_of_lt_of_le (not_le.1 hx) (hZ.1 x)
        have hint : Deep 0 (((incl k n b).val - 1) i l) := deep_sub_one_of_intM (intM_incl b) i l
        have := ((deep_zpow hϖ (a i)).mul hint).mul (deep_inv_zpow hϖ (a l))
        exact deep_one_iff.1 (this.mono (by omega))
      · rw [hb1 i l hZ]
        simp
    have : π t (π (incl k n b) (j w)) = π (t * incl k n b * t⁻¹) (π t (j w)) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    rw [this, ← neg_sub]
    exact neg_mem (sub_mem_twKer hK _)
  have hcard : (Fintype.card (unipRad 𝓀[k] e) : ℂ) • π t (j w) ∈ twKer π (KOne k (Fin n)) 1 := by
    have h2 := Submodule.sum_mem (twKer π (KOne k (Fin n)) 1) fun u (_ : u ∈ Finset.univ) => hterm u
    have h3 : ∑ u : unipRad 𝓀[k] e, π t (j (τ u w)) = 0 := by
      rw [← map_sum (π t), ← map_sum j, hsum, map_zero, map_zero]
    rw [Finset.sum_sub_distrib, h3, sub_zero, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ] at h2
    exact h2
  have hc : (Fintype.card (unipRad 𝓀[k] e) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have := Submodule.smul_mem _ (Fintype.card (unipRad 𝓀[k] e) : ℂ)⁻¹ hcard
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

theorem apply_mem_sup {τ : Representation ℂ (GL (Fin n) 𝓀[k]) W} (hτ : FinCusp τ)
    {π : Representation ℂ (GL (Fin n) k) V} {ω : kˣ →* ℂˣ} (hω : HasCentralChar π ω) {j : W →ₗ[ℂ] V}
    (hj : IsTypeMap τ π j) (g : GL (Fin n) k) (w : W) :
    π g (j w) ∈ LinearMap.range j ⊔ twKer π (KOne k (Fin n)) 1 := by
  classical
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  obtain ⟨⟨a, _ha⟩, hg⟩ := GlobalTheory.UnramDoublingProof.exists_cell hϖ g
  obtain ⟨k1, h1, k2, h2, hg'⟩ := DoubleCoset.mem_doubleCoset.1 hg
  rw [hg', map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← hj.2 ⟨k2, h2⟩]
  set w' := τ (redK k (Fin n) ⟨k2, h2⟩) w
  have hmid : π (GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ a) (j w') ∈
      LinearMap.range j ⊔ twKer π (KOne k (Fin n)) 1 := by
    by_cases ha : ∃ i l, a i ≠ a l
    · exact Submodule.mem_sup_right (torus_mem_twKer hτ hj hϖ a ha w')
    · push_neg at ha
      obtain ⟨c, hc⟩ : ∃ c, a = fun _ => c := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn; exact ⟨0, funext fun i => i.elim0⟩
        · exact ⟨a ⟨0, hn⟩, funext fun i => ha i _⟩
      rw [hc, torusElt_const, hω]
      exact Submodule.mem_sup_left (Submodule.smul_mem _ _ ⟨w', rfl⟩)
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmid
  rw [← hyz, map_add]
  obtain ⟨w'', rfl⟩ := hy
  refine add_mem (Submodule.mem_sup_left ⟨_, hj.2 ⟨k1, h1⟩ w''⟩) (Submodule.mem_sup_right ?_)
  exact apply_mem_twKer_of_normalizer (mem_normalizer_KOne h1) hz

end TorusConjugationFixed

open TorusConjugationFixed in
theorem st6 : St6 := by
  intro k W _ _ _ _ _ _ _ n τ hτ π ω hω j hj
  refine le_antisymm ?_ (range_le_fixed hj)
  let S : Submodule ℂ π.V := Submodule.span ℂ {x | ∃ g w, x = π.ρ g (j w)}
  have hS : ∀ g, ∀ x ∈ S, π.ρ g x ∈ S := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, w, rfl⟩ := hx
      refine Submodule.subset_span ⟨g * h, w, ?_⟩
      rw [map_mul, Module.End.mul_apply]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  let U : Subrepresentation π.ρ := ⟨S, fun g _ hx => hS g _ hx⟩
  obtain ⟨w0, hw0⟩ := exists_ne (0 : W)
  have hj0 : j w0 ∈ S := Submodule.subset_span ⟨1, w0, by rw [map_one, Module.End.one_apply]⟩
  haveI := π.irr
  have hU : U = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top U with h | h
    · exfalso
      have h0 : j w0 ∈ U.toSubmodule := hj0
      rw [h] at h0
      have h0' : j w0 = 0 := (Submodule.mem_bot ℂ).1 h0
      exact hw0 (hj.1 (by rw [h0', map_zero]))
    · exact h
  have hle : S ≤ LinearMap.range j ⊔ twKer π.ρ (KOne k (Fin n)) 1 :=
    Submodule.span_le.2 (by rintro _ ⟨g, w, rfl⟩; exact apply_mem_sup hτ hω hj g w)
  intro v hv
  have hvS : v ∈ S := by
    have h0 : v ∈ U.toSubmodule := by rw [hU]; exact Submodule.mem_top
    exact h0
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hle hvS)
  obtain ⟨w, rfl⟩ := hy
  have hzf : z ∈ fixed π.ρ (KOne k (Fin n)) := by
    have := sub_mem hv (range_le_fixed hj ⟨w, rfl⟩)
    simpa using this
  have h0 := GlobalTheory.IwahoriInj.eq_zero_of_fixed π.smooth GlobalTheory.DepthZeroJac.isCompact_KOne hzf hz
  subst h0
  rw [add_zero]
  exact ⟨w, rfl⟩

end PositivityTheory.Rg.DzCount.B
