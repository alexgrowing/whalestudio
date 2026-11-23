import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PSurjSk
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UJClassMassOfDeep

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Basic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem mem_loc_iff (p : Ideal (𝓞 E)) (L : Submodule (𝓞 E) V) (x : V) :
    x ∈ loc (K := E) p L ↔ ∃ s ∈ hcompl (K := E) p, s • x ∈ L := Iff.rfl

theorem mem_gmap_iff (u : V ≃ₗ[E] V) (L : Submodule (𝓞 E) V) (x : V) :
    x ∈ gmap u L ↔ ∃ y ∈ L, u y = x := Iff.rfl

theorem equiv_smul_O (u : V ≃ₗ[E] V) (s : 𝓞 E) (v : V) : u (s • v) = s • u v := by
  rw [← algebraMap_smul E s v, LinearEquiv.map_smul, algebraMap_smul]

theorem hcompl_le_primeCompl (p : Ideal (𝓞 E)) [p.IsPrime] : hcompl (K := E) p ≤ p.primeCompl := by
  refine Submonoid.closure_le.2 fun s hs => ?_
  exact Ideal.mem_primeCompl_iff.2 hs.1

end Basic

theorem linOf_one_apply {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V] {M : ℕ}
    (b : Module.Basis (Fin M) E V) (v : V) : linOf b (1 : GL (Fin M) E) v = v := by
  simp [linOf]

theorem locGmapStep : LocGmapStep := by
  intro E _ _ _ V _ _ _ _ u p L
  ext x
  rw [mem_loc_iff, mem_gmap_iff]
  constructor
  · rintro ⟨s, hs, hsx⟩
    rw [mem_gmap_iff] at hsx
    obtain ⟨y, hy, hyx⟩ := hsx
    refine ⟨u.symm x, ?_, u.apply_symm_apply x⟩
    rw [mem_loc_iff]
    refine ⟨s, hs, ?_⟩
    have h3 : s • u.symm x = y := by
      apply u.injective
      rw [equiv_smul_O, u.apply_symm_apply, hyx]
    rw [h3]
    exact hy
  · rintro ⟨y, hy, rfl⟩
    rw [mem_loc_iff] at hy
    obtain ⟨s, hs, hsy⟩ := hy
    refine ⟨s, hs, ?_⟩
    rw [mem_gmap_iff]
    exact ⟨s • y, hsy, equiv_smul_O u s y⟩

theorem cofin1 {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (L N : Submodule (𝓞 E) V)
    (hL : L.FG) (hN : Submodule.span E (N : Set V) = ⊤) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ v ∈ L, (y : 𝓞 E) • v ∈ N := by
  classical
  let b := Module.finBasis E V
  obtain ⟨y1, hy1, h1⟩ := crd_upper b L hL
  obtain ⟨y2, hy2, h2⟩ := crd_lower b N hN
  refine ⟨y1 * y2, mul_ne_zero hy1 hy2, fun v hv => ?_⟩
  have hx : b.equivFun v ∈ crdOf b L := by
    show ∑ i, b.equivFun v i • b i ∈ L
    rw [b.sum_equivFun]
    exact hv
  have e : ((y1 * y2 : ℤ) : 𝓞 E) • v = ∑ i, (y1 • b.equivFun v i) • (y2 • b i) := by
    conv_lhs => rw [← b.sum_equivFun v]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← algebraMap_smul E ((y1 * y2 : ℤ) : 𝓞 E), map_intCast, zsmul_eq_mul,
      ← Int.cast_smul_eq_zsmul E y2 (b i), smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  rw [e]
  exact Submodule.sum_mem _ (fun i _ => int_smul_mem N (h1 _ hx i) (h2 i))

theorem cofinStep : CofinStep := by
  intro E _ _ V _ _ _ _ _ L N hL hN
  obtain ⟨y1, hy1, h1⟩ := cofin1 L N hL.fg hN.span_eq_top
  obtain ⟨y2, hy2, h2⟩ := cofin1 N L hN.fg hL.span_eq_top
  refine ⟨y1 * y2, mul_ne_zero hy1 hy2, fun v hv => ?_, fun v hv => ?_⟩
  · have h3 := N.smul_mem (y2 : 𝓞 E) (h1 v hv)
    rw [← mul_smul] at h3
    rwa [Int.cast_mul, mul_comm]
  · have h3 := L.smul_mem (y1 : 𝓞 E) (h2 v hv)
    rw [← mul_smul] at h3
    rwa [Int.cast_mul]

end PI.UnitaryGroupMassFormula.UJClassMass

end
