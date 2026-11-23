import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSplit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SphAvg

open GlobalTheory.SplitWeil

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem exists_lift {n : ℕ} (s : SplitPlace L)
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hi : Continuous i)
    (y : GL (Fin n) (s.w.adicCompletion L)) (hy : y ∈ KO (s.w.adicCompletion L) (Fin n)) :
    ∃ κ : GAf L n, κ ∈ Umax L n ∧ TrivOutside {s.v} κ ∧
      Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n κ) = y := by
  have hE := GlobalTheory.ConjParahoric.isEquiv_of_continuous i hi
  have hle : ∀ x, ValuativeRel.valuation (s.w.adicCompletion L) x ≤ 1 → Valued.v (i.symm x) ≤ 1 :=
    fun x hx => (Valuation.isEquiv_iff_val_le_one.1 hE).2 hx
  obtain ⟨u, rfl⟩ := hy
  set M := Matrix.GeneralLinearGroup.map i.symm.toRingHom
    (Matrix.GeneralLinearGroup.map (algebraMap _ (s.w.adicCompletion L)) u) with hM
  obtain ⟨κ, hκ, hloc⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s M
  refine ⟨κ, GlobalTheory.HeckeStdFacts.mem_Umax_of_loc s κ hκ ?_ ?_, hκ, ?_⟩
  · intro a b
    rw [hloc]
    exact hle _ (u.val a b).2
  · intro a b
    rw [map_inv, hloc, hM, ← map_inv, ← map_inv]
    exact hle _ ((u⁻¹).val a b).2
  · rw [hloc, hM]
    ext a b
    simp

theorem exists_fixed_of_sum {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hi : Continuous i)
    {ι : Type} [Fintype ι] (T : ι → σ.V →ₗ[ℂ] (GAf L n → W))
    (hT : ∀ j, GlobalTheory.HeckeFrob.IsLocMap s σ i (T j)) (u : ι → σ.V) (f : GAf L n → W)
    (hf : f = ∑ j, T j (u j)) (hfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) :
    ∃ e : ι → σ.V, (∀ j, e j ∈ GlobalTheory.PRep.fixed σ.ρ (KO (s.w.adicCompletion L) (Fin n))) ∧
      f = ∑ j, T j (e j) := by
  classical
  let H : Subgroup (GL (Fin n) (s.w.adicCompletion L)) :=
    { carrier := {g | ∀ j, σ.ρ g (u j) = u j}
      mul_mem' := fun {a b} ha hb j => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb j, ha j]
      one_mem' := fun j => by simp
      inv_mem' := fun {a} ha j => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        conv_lhs => rw [← ha j]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hHo : IsOpen (H : Set (GL (Fin n) (s.w.adicCompletion L))) := by
    have : (H : Set (GL (Fin n) (s.w.adicCompletion L))) = ⋂ j, {g | σ.ρ g (u j) = u j} := by
      ext g; simp [H]
    rw [this]
    exact isOpen_iInter_of_finite fun j => σ.smooth (u j)
  set K := KO (s.w.adicCompletion L) (Fin n) with hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp GlobalTheory.SplitFlip.isCompact_KO
  haveI : Finite (K ⧸ H.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hHo.preimage continuous_subtype_val)
  letI : Fintype (K ⧸ H.subgroupOf K) := Fintype.ofFinite _
  set N : ℂ := (Fintype.card (K ⧸ H.subgroupOf K) : ℂ) with hNdef
  have hN : N ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let e : ι → σ.V := fun j => N⁻¹ • ∑ q : K ⧸ H.subgroupOf K, σ.ρ ((q.out : K) : GL (Fin n) _) (u j)
  refine ⟨e, fun j => ?_, ?_⟩
  · intro k
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    simp only [e, map_smul, map_sum]
    congr 1
    have hstep : ∀ q : K ⧸ H.subgroupOf K, σ.ρ (k : GL (Fin n) _) (σ.ρ ((q.out : K) : GL (Fin n) _) (u j)) =
        σ.ρ (((k • q).out : K) : GL (Fin n) _) (u j) := by
      intro q
      have hq : (QuotientGroup.mk ((k • q).out) : K ⧸ H.subgroupOf K) = QuotientGroup.mk (k * q.out) := by
        rw [QuotientGroup.out_eq']
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have hmem := QuotientGroup.eq.1 hq
      rw [Subgroup.mem_subgroupOf] at hmem
      have h1 : ((k * q.out : K) : GL (Fin n) (s.w.adicCompletion L)) =
          (((k • q).out : K) : GL (Fin n) (s.w.adicCompletion L)) *
            ((((k • q).out)⁻¹ * (k * q.out) : K) : GL (Fin n) (s.w.adicCompletion L)) := by
        rw [← Subgroup.coe_mul, mul_inv_cancel_left]
      rw [← Module.End.mul_apply, ← map_mul]
      change σ.ρ ((k * q.out : K) : GL (Fin n) _) (u j) = _
      rw [h1, map_mul, Module.End.mul_apply, hmem j]
    simp_rw [hstep]
    exact Equiv.sum_comp (MulAction.toPerm k) (fun (q : K ⧸ H.subgroupOf K) => σ.ρ ((q.out : K) : GL (Fin n) (s.w.adicCompletion L)) (u j))
  · choose κ hκU hκT hκ using fun (q : K ⧸ H.subgroupOf K) => exists_lift s i hi ((q.out : K) : GL (Fin n) _) q.out.2
    have key : ∀ q : K ⧸ H.subgroupOf K, ∑ j, T j (σ.ρ ((q.out : K) : GL (Fin n) _) (u j)) = f := by
      intro q
      rw [← hκ q]
      simp_rw [hT _ (κ q) (hκT q)]
      rw [← map_sum, ← hf, hfix _ (hκU q) (hκT q)]
    calc f = N⁻¹ • ∑ _q : K ⧸ H.subgroupOf K, f := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← hNdef,
            inv_mul_cancel₀ hN, one_smul]
      _ = N⁻¹ • ∑ q : K ⧸ H.subgroupOf K, ∑ j, T j (σ.ρ ((q.out : K) : GL (Fin n) _) (u j)) := by
          simp_rw [key]
      _ = ∑ j, T j (e j) := by
          simp only [e, map_smul, map_sum, ← Finset.smul_sum]
          rw [Finset.sum_comm]

end GlobalTheory.SphAvg

namespace GlobalTheory.SphAvg

theorem exists_sum_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i →
    (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) →
    ∀ f, f ∈ ⨆ (T' : {T' : σ.V →ₗ[ℂ] (GAf L n → π.W) // (∀ a, T' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'}),
      LinearMap.range T'.1 →
    (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
    ∃ (m : ℕ) (T : Fin m → σ.V →ₗ[ℂ] (GAf L n → π.W)) (e : Fin m → σ.V),
      (∀ j, GlobalTheory.HeckeFrob.IsLocMap s σ i (T j)) ∧
      (∀ j, e j ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n))) ∧ f = ∑ j, T j (e j) := by
  intro L _ _ _ n π s σ i hi _ f hf hfix
  classical
  obtain ⟨c, hc, hcf⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ f).1 hf
  choose u hu using hc
  have hsum : f = ∑ t : c.support, t.1.1 (u t.1) := by
    rw [← hcf, Finsupp.sum, ← Finset.sum_coe_sort]
    exact Finset.sum_congr rfl fun t _ => (hu t.1).symm
  obtain ⟨e, he, hfe⟩ := exists_fixed_of_sum s σ i hi (ι := c.support) (fun t => t.1.1)
    (fun t => t.1.2.2) (fun t => u t.1) f hsum hfix
  · refine ⟨c.support.card, fun j => (c.support.equivFin.symm j).1.1,
      fun j => e (c.support.equivFin.symm j), fun j => (c.support.equivFin.symm j).1.2.2,
      fun j => he _, ?_⟩
    rw [hfe]
    exact (Equiv.sum_comp c.support.equivFin.symm (fun t => t.1.1 (e t))).symm

end GlobalTheory.SphAvg
