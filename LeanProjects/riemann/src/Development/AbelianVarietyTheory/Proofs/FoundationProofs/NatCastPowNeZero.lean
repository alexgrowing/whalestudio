import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerRankVanishing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.LengthValuationTwists

namespace GlobalTheory.BlochKatoRank

theorem rank_subquotient_eq {O K X Y : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module K Y] [Module O Y]
    [IsScalarTower O K Y] (φ : X →ₗ[O] Y) (Z B A : Submodule O X) (Zf BV : Submodule K Y)
    (h1 : ∀ a ∈ A, φ a ∈ Zf) (h2 : ∀ b ∈ B, φ b ∈ BV)
    (h3 : ∀ a, φ a ∈ BV → ∃ m : O, m ≠ 0 ∧ m • a ∈ B)
    (h4 : ∀ y ∈ Zf, ∃ m : O, m ≠ 0 ∧ ∃ a ∈ Z, a ∈ A ∧ φ a = m • y) :
    Module.rank O ((A.comap Z.subtype).map (Submodule.mkQ (B.comap Z.subtype))) =
      Module.rank K (Zf ⧸ BV.comap Zf.subtype) := by
  let A' := A.comap Z.subtype
  let g : A' →ₗ[O] (Z ⧸ B.comap Z.subtype) := (Submodule.mkQ _).comp A'.subtype
  have hg : LinearMap.range g = A'.map (Submodule.mkQ (B.comap Z.subtype)) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  let f0 : A' →ₗ[O] Zf :=
    { toFun := fun a => ⟨φ a.1.1, h1 _ a.2⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun c a => Subtype.ext (by simp) }
  let f : A' →ₗ[O] (Zf ⧸ BV.comap Zf.subtype) :=
    ((Submodule.mkQ (BV.comap Zf.subtype)).restrictScalars O).comp f0
  have hgk : ∀ a : A', g a = 0 ↔ a.1.1 ∈ B := fun a => Submodule.Quotient.mk_eq_zero _
  have hfk : ∀ a : A', f a = 0 ↔ φ a.1.1 ∈ BV := fun a => Submodule.Quotient.mk_eq_zero _
  have hle : LinearMap.ker g ≤ LinearMap.ker f := fun a ha =>
    (hfk a).2 (h2 _ ((hgk a).1 ha))
  let F := (LinearMap.ker g).liftQ f hle
  haveI : IsLocalizedModule (nonZeroDivisors O) F := by
    refine ⟨fun s => ?_, fun y => ?_, fun {x y} h => ?_⟩
    · have hs : algebraMap O K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
      rw [Module.End.isUnit_iff]
      refine ⟨fun a b h => ?_, fun a => ⟨(algebraMap O K s)⁻¹ • a, ?_⟩⟩
      · simp only [Module.algebraMap_end_apply] at h
        rw [← algebraMap_smul K, ← algebraMap_smul K (s : O) b] at h
        exact smul_right_injective _ hs h
      · rw [Module.algebraMap_end_apply, ← algebraMap_smul K, smul_inv_smul₀ hs]
    · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨m, hm, a, haZ, haA, ha⟩ := h4 y.1 y.2
      refine ⟨(Submodule.Quotient.mk ⟨⟨a, haZ⟩, haA⟩, ⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩), ?_⟩
      have : f0 ⟨⟨a, haZ⟩, haA⟩ = m • y := Subtype.ext ha
      change m • ((BV.comap Zf.subtype).mkQ.restrictScalars O) y =
        ((BV.comap Zf.subtype).mkQ.restrictScalars O) (f0 ⟨⟨a, haZ⟩, haA⟩)
      rw [this, map_smul]
    · rw [← sub_eq_zero, ← map_sub] at h
      suffices H : ∃ m : O, m ≠ 0 ∧ m • (x - y) = 0 by
        obtain ⟨m, hm, H⟩ := H
        exact ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩, by
          rw [smul_sub, sub_eq_zero] at H; exact H⟩
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x - y)
      rw [← ha] at h ⊢
      obtain ⟨m, hm, H⟩ := h3 _ ((hfk a).1 h)
      refine ⟨m, hm, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact (hgk _).2 H
  rw [← hg, ← (LinearMap.quotKerEquivRange g).rank_eq,
    IsLocalization.rank_eq K (nonZeroDivisors O) le_rfl,
    IsLocalizedModule.rank_eq (nonZeroDivisors O) le_rfl F]

section Bridge

open GlobalTheory.BlochKatoIntegralScalars

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

include Bw in
theorem natCast_pow_ne_zero (N : ℕ) : (l : O₀) ^ N ≠ 0 := by
  intro h
  have := congrArg Bw.toLL h
  rw [map_pow, map_natCast, map_zero] at this
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast (eq_zero_of_pow_eq_zero this))

theorem exists_integral {X : Type} [TopologicalSpace X] [CompactSpace X]
    (c : X → Fin m → ↥Bw.LL.1) (hc : Continuous c) :
    ∃ d : O₀, d ≠ 0 ∧ ∃ f : X → Fin m → O₀, Continuous f ∧
      ∀ g j, Bw.toLL (f g j) = Bw.toLL d * c g j := by
  obtain ⟨N, hN⟩ := exists_pow_mul_mem_OL Bw.LL c hc
  refine ⟨(l : O₀) ^ N, natCast_pow_ne_zero Bw N, fun g j => Bw.eO.symm ⟨_, hN g j⟩, ?_, ?_⟩
  · refine continuous_pi fun j => Bw.eO_symm_cont.comp ?_
    exact Continuous.subtype_mk (continuous_const.mul ((continuous_apply j).comp hc)) _
  · intro g j
    show ((Bw.eO (Bw.eO.symm _) : Loc.OL Bw.LL) : Bw.LL.1) = _
    rw [RingEquiv.apply_symm_apply, map_pow, map_natCast]

end Bridge

end GlobalTheory.BlochKatoRank
