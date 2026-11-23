import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
import Formalism.LocalToGlobal.ProjectiveLattices.FullXi
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleQuadraticExistsUnitEqMulSg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneRootCongruentOddHostField
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdeleNinety

theorem fixed_baseChange {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (c : E →ₐ[F] E) (hcc : ∀ x, c (c x) = x)
    (hfix : ∀ x, c x = x → ∃ t : F, x = algebraMap F E t) (y : R ⊗[F] E)
    (hy : Algebra.TensorProduct.map (AlgHom.id F R) c y = y) : ∃ a : R, y = a ⊗ₜ 1 := by
  have hT : ∀ z : R ⊗[F] E, ∃ t : R, z + Algebra.TensorProduct.map (AlgHom.id F R) c z = t ⊗ₜ 1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a x =>
      obtain ⟨t, ht⟩ := hfix (x + c x) (by rw [map_add, hcc, add_comm])
      refine ⟨t • a, ?_⟩
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ← TensorProduct.tmul_add, ht,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨t, ht⟩ := hx
      obtain ⟨t', ht'⟩ := hy
      refine ⟨t + t', ?_⟩
      rw [map_add, TensorProduct.add_tmul, ← ht, ← ht']; ring
  obtain ⟨t, ht⟩ := hT y
  refine ⟨(2 : F)⁻¹ • t, ?_⟩
  rw [← TensorProduct.smul_tmul', ← ht, hy, ← two_smul F y, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem conj_ne_one (D : D7) : cF D ≠ 1 := by
  intro h
  obtain ⟨P, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
  obtain ⟨t, s, hs, hts⟩ := D.sp.cm.cmUnram.2.2 P hM
  have hs' : (s : D.host.E) = cF D (t : D.host.E) := hs
  rw [h] at hs'
  have : s = t := Subtype.ext hs'
  rw [this, sub_self] at hts
  exact hts P.zero_mem

theorem fixed_conj (D : D7) (x : D.host.E) (hx : cF D x = x) : ∃ t : D.host.F, x = algebraMap D.host.F D.host.E t := by
  have : Algebra.IsQuadraticExtension D.host.F D.host.E := { finrank_eq_two' := D.sp.cm.deg2 }
  have hcard : Nat.card (D.host.E ≃ₐ[D.host.F] D.host.E) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, D.sp.cm.deg2]
  obtain ⟨g, -, hg⟩ := (Nat.card_eq_two_iff' (1 : D.host.E ≃ₐ[D.host.F] D.host.E)).1 hcard
  obtain ⟨t, ht⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := D.host.F) x).2 fun f => by
    by_cases hf : f = 1
    · rw [hf]; rfl
    · rw [hg f hf, ← hg _ (conj_ne_one D), hx]
  exact ⟨t, ht.symm⟩

theorem coe_cjFin (D : D7) (y : (AfE D)ˣ) : ((cjFin D y : (AfE D)ˣ) : AfE D) = barF D (y : AfE D) := by
  have h : D.conjF = (cF D : D.host.E →ₐ[D.host.F] D.host.E) :=
    AlgHom.ext fun x => (D.conjF_eq x).trans (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm
  unfold cjFin barF
  rw [h]
  rfl

theorem finiteIdeles_normOne_eq_div_conj_with_congruence : ∀ (D : D7), (∀ x : (AfE D)ˣ, NormOne x → ∃ y, x = y / cjFin D y) ∧ (∀ y : (AfE D)ˣ, cjFin D y = y → ∃ a : Af D.host.F, (y : AfE D) = a ⊗ₜ 1) ∧ ∀ (p N : ℕ) (x : (AfE D)ˣ), p.Prime → p ≠ 2 → p ∣ N → 0 < N → NormOne x → CongOne N x → ∃ y, IntUnit y ∧ CongOne p y ∧ x = y / cjFin D y := by
  intro D
  have hcc : ∀ x, cF D (cF D x) = x := fun x => star_star x
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun p N x hp h2 hpN _ hx hc => ?_⟩
  · obtain ⟨y, hy⟩ := GlobalTheory.UCls.NormOne.finiteAdele_quadratic_exists_unit_eq_mul_sg (cF D) hcc (fixed_conj D) (conj_ne_one D) (x : AfE D) hx
    refine ⟨y, ?_⟩
    rw [eq_div_iff_mul_eq']
    exact Units.ext (by rw [Units.val_mul, coe_cjFin]; exact hy.symm)
  · exact fixed_baseChange (Af D.host.F) (cF D : D.host.E →ₐ[D.host.F] D.host.E) hcc (fixed_conj D) _
      ((coe_cjFin D y).symm.trans (congrArg Units.val hy))
  · obtain ⟨w, hw, hwe⟩ := hc
    obtain ⟨k, rfl⟩ := hpN
    obtain ⟨y, y', hy, hy', hyy, hroot, hq⟩ := GlobalTheory.OddRoot.exists_root_odd D p (hp.odd_of_ne_two h2) (x : AfE D)
      (k • w) (nsmul_mem hw k) (by rw [hwe, mul_smul]) hx
    refine ⟨Units.mkOfMulEqOne y y' hyy, ⟨hy, hy'⟩, hq, ?_⟩
    rw [eq_div_iff_mul_eq']
    exact Units.ext (by rw [Units.val_mul, coe_cjFin]; exact hroot.symm)

end GlobalTheory.IdeleNinety
