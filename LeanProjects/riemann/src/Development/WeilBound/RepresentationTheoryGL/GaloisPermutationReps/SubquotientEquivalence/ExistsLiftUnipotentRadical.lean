import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

namespace L5

section Entries

variable {R : Type} [CommRing R] {s N : ℕ} {d : Fin s → ℕ} {e : (Σ a, Fin (d a)) ≃ Fin N}

theorem mem_unipotent_radical_iff_alt {u : GL (Fin N) R} :
    u ∈ unipRad R e ↔
      ∀ i j, ¬ blk e i < blk e j → (u : Matrix (Fin N) (Fin N) R) i j = (1 : Matrix (Fin N) (Fin N) R) i j := by
  rw [mem_unipRad, mem_parab]
  constructor
  · rintro ⟨hP, hD⟩ i j hij
    rcases lt_or_eq_of_le (not_lt.1 hij) with h | h
    · rw [hP i j h, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ h
    · obtain ⟨⟨a, p⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨b, q⟩, rfl⟩ := e.surjective j
      simp only [blk_apply] at h
      subst h
      rw [hD, Matrix.one_apply, Matrix.one_apply]
      simp [e.apply_eq_iff_eq]
  · intro h
    refine ⟨fun i j hij => ?_, fun a p q => ?_⟩
    · rw [h i j (not_lt.2 hij.le), Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hij
    · rw [h _ _ (by simp), Matrix.one_apply, Matrix.one_apply]
      simp [e.apply_eq_iff_eq]

theorem exists_block_lt_of_ne_bot (h : unipRad R e ≠ ⊥) : ∃ i j, blk e i < blk e j := by
  by_contra hc
  push Not at hc
  apply h
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Units.val_one]
  exact (mem_unipotent_radical_iff_alt.1 hu) i j (not_lt.2 (hc i j))

theorem unipotent_radical_ne_bot {K : Type} [Field K] (h : ∃ i j, blk e i < blk e j) : unipRad K e ≠ ⊥ := by
  obtain ⟨i, j, hij⟩ := h
  have hne : i ≠ j := by
    rintro rfl
    exact lt_irrefl _ hij
  let t : GL (Fin N) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j 1)
    (by rw [Matrix.det_transvection_of_ne _ _ hne]; exact one_ne_zero)
  have ht : t ∈ unipRad K e := by
    rw [mem_unipotent_radical_iff_alt]
    intro a b hab
    show (1 + Matrix.single i j (1 : K)) a b = _
    rw [Matrix.add_apply, Matrix.single_apply, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact hab hij
  intro hb
  rw [hb, Subgroup.mem_bot] at ht
  have h1 := congrArg (fun x : GL (Fin N) K => (x : Matrix (Fin N) (Fin N) K) i j) ht
  simp only [t, Matrix.GeneralLinearGroup.mkOfDetNeZero, Units.val_one] at h1
  change (1 + Matrix.single i j (1 : K)) i j = (1 : Matrix (Fin N) (Fin N) K) i j at h1
  rw [Matrix.add_apply, Matrix.single_apply_same, Matrix.one_apply_ne hne, zero_add] at h1
  exact one_ne_zero h1

end Entries

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {s N : ℕ} {d : Fin s → ℕ} {e : (Σ a, Fin (d a)) ≃ Fin N}

theorem exists_lift_unipotent_radical (u : GL (Fin N) 𝓀[k]) (hu : u ∈ unipRad 𝓀[k] e) :
    ∃ g : KO k (Fin N), redK k (Fin N) g = u ∧ (g : GL (Fin N) k) ∈ unipRad k e := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : 𝓀[k] → 𝒪[k], ∀ x, IsLocalRing.residue 𝒪[k] (r x) = x :=
    ⟨Function.surjInv IsLocalRing.residue_surjective, Function.surjInv_eq IsLocalRing.residue_surjective⟩
  let M : Matrix (Fin N) (Fin N) 𝒪[k] := fun a b =>
    if blk e a < blk e b then r ((u : Matrix (Fin N) (Fin N) 𝓀[k]) a b)
    else (1 : Matrix (Fin N) (Fin N) 𝒪[k]) a b
  have hM : ∀ a b, ¬ blk e a < blk e b → M a b = (1 : Matrix (Fin N) (Fin N) 𝒪[k]) a b := fun a b h => by
    simp only [M, if_neg h]
  have hT : M.BlockTriangular (blk e) := fun a b hab => by
    rw [hM a b (not_lt.2 hab.le), Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hab
  have hdet : M.det = 1 := by
    rw [hT.det_fintype]
    refine Finset.prod_eq_one fun c _ => ?_
    have : M.toSquareBlock (blk e) c = 1 := by
      refine Matrix.ext fun ⟨x, hx⟩ ⟨y, hy⟩ => ?_
      show M x y = _
      rw [hM x y (by rw [hx, hy]; exact lt_irrefl _), Matrix.one_apply, Matrix.one_apply]
      simp [Subtype.ext_iff]
    rw [this, Matrix.det_one]
  have hU : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (by rw [hdet]; exact isUnit_one)
  let g : GL (Fin N) k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) hU.unit
  have hgK : g ∈ KO k (Fin N) := MonoidHom.mem_range.2 ⟨hU.unit, rfl⟩
  refine ⟨⟨g, hgK⟩, ?_, ?_⟩
  · refine Units.ext (Matrix.ext fun a b => ?_)
    rw [redK_apply]
    show IsLocalRing.residue 𝒪[k] (M a b) = _
    by_cases h : blk e a < blk e b
    · simp only [M, if_pos h, hr]
    · rw [hM a b h, (mem_unipotent_radical_iff_alt.1 hu) a b h, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
  · rw [mem_unipotent_radical_iff_alt]
    intro a b h
    show algebraMap 𝒪[k] k (M a b) = _
    rw [hM a b h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem lift_mem_twisted_kernel {W V : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin N) 𝓀[k]) W) (ρ : Representation ℂ (GL (Fin N) k) V) (j : W →ₗ[ℂ] V)
    (hj : ∀ (g : KO k (Fin N)) (v : W), j (τ (redK k (Fin N) g) v) = ρ (g : GL (Fin N) k) (j v))
    (hCF : ∀ v : W, (∀ u ∈ unipRad 𝓀[k] e, τ u v = v) → v = 0) (x : W) :
    j x ∈ twKer ρ (unipRad k e) 1 := by
  classical
  have : Finite (GL (Fin N) 𝓀[k]) :=
    Finite.of_injective (fun g : GL (Fin N) 𝓀[k] => fun i j => (g : Matrix (Fin N) (Fin N) 𝓀[k]) i j)
      (fun a b h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j))
  let _ : Fintype (unipRad 𝓀[k] e) := Fintype.ofFinite _
  let y : W := ∑ u : unipRad 𝓀[k] e, τ u x
  have hy : y = 0 := by
    apply hCF
    intro u hu
    simp only [y, map_sum]
    rw [show (∑ v : unipRad 𝓀[k] e, τ u (τ v x)) =
        ∑ v : unipRad 𝓀[k] e, τ ((⟨u, hu⟩ * v : unipRad 𝓀[k] e) : GL (Fin N) 𝓀[k]) x from
      Finset.sum_congr rfl fun v _ => by rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨u, hu⟩ : unipRad 𝓀[k] e)) _ _ fun v => rfl
  choose lf hlf using fun u : unipRad 𝓀[k] e => exists_lift_unipotent_radical (e := e) u.1 u.2
  have hsum : ∑ u : unipRad 𝓀[k] e, (j x - ρ ((lf u : KO k (Fin N)) : GL (Fin N) k) (j x)) ∈
      twKer ρ (unipRad k e) 1 := by
    refine Submodule.sum_mem _ fun u _ => ?_
    have : ρ ((lf u : KO k (Fin N)) : GL (Fin N) k) (j x) - j x ∈ twKer ρ (unipRad k e) 1 :=
      Submodule.subset_span ⟨⟨_, (hlf u).2⟩, j x, by simp⟩
    rw [← neg_sub]
    exact neg_mem this
  have h2 : ∑ u : unipRad 𝓀[k] e, (j x - ρ ((lf u : KO k (Fin N)) : GL (Fin N) k) (j x)) =
      (Fintype.card (unipRad 𝓀[k] e) : ℂ) • j x := by
    rw [Finset.sum_sub_distrib]
    have : ∑ u : unipRad 𝓀[k] e, ρ ((lf u : KO k (Fin N)) : GL (Fin N) k) (j x) = j y := by
      simp only [y, map_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← hj, (hlf u).1]
    rw [this, hy, map_zero, sub_zero, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  rw [h2] at hsum
  have hc : (Fintype.card (unipRad 𝓀[k] e) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have := (twKer ρ (unipRad k e) 1).smul_mem (Fintype.card (unipRad 𝓀[k] e) : ℂ)⁻¹ hsum
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

end Local

end L5

open L5 in

theorem st5 : St5 := by
  intro k W _ _ _ _ _ _ _ n τ hτ π j hj
  refine ⟨π.smooth, fun s d e hne => ?_⟩
  have hCF := hτ s d e (unipotent_radical_ne_bot (exists_block_lt_of_ne_bot hne))
  let S : Submodule ℂ π.V := Submodule.span ℂ {v | ∃ h x, v = π.ρ h (j x)}
  have hSst : ∀ h v, v ∈ S → π.ρ h v ∈ S := by
    intro h v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨h', x, rfl⟩ := hv
      exact Submodule.subset_span ⟨h * h', x, by rw [map_mul, Module.End.mul_apply]⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have hS0 : S ≠ ⊥ := by
    obtain ⟨x, hx⟩ := exists_ne (0 : W)
    intro hb
    have hm : j x ∈ S := Submodule.subset_span ⟨1, x, by simp⟩
    rw [hb, Submodule.mem_bot] at hm
    exact hx (hj.1 (hm.trans (map_zero j).symm))
  have hST : S ≤ twKer π.ρ (unipRad k e) 1 := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, x, rfl⟩
    obtain ⟨p, w, hw, rfl⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul e h
    rw [map_mul, Module.End.mul_apply,
      show π.ρ w (j x) = j (τ (redK k (Fin n) ⟨w, hw⟩) x) from (hj.2 ⟨w, hw⟩ x).symm]
    exact twKer_le_comap π.ρ _ p (parab_le_normalizer k e p.2) (lift_mem_twisted_kernel τ π.ρ j hj.2 hCF _)
  have htop : S = ⊤ := by
    let S' : Subrepresentation π.ρ := ⟨S, fun x v hv => hSst x v hv⟩
    rcases π.irr.eq_bot_or_eq_top S' with h | h
    · exact absurd (congrArg Subrepresentation.toSubmodule h) hS0
    · exact congrArg Subrepresentation.toSubmodule h
  rw [htop, top_le_iff] at hST
  show Subsingleton (_ ⧸ twKer π.ρ (unipRad k e) 1)
  rw [Submodule.Quotient.subsingleton_iff]
  exact hST

end PositivityTheory.Rg.DzCount

end
