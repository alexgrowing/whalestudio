import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.MemClosureOfMemSS
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.Imports

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem exists_basis_mem_intOE :
    ∃ n : ℕ, ∃ b : Module.Basis (Fin n) F E, ∀ i, b i ∈ intOE E := by
  classical
  let c := Module.finBasis F E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image c)
  have hyF : IsUnit ((y : ℤ) : F) := (Int.cast_ne_zero.mpr hy0).isUnit
  refine ⟨_, c.isUnitSMul (w := fun _ => ((y : ℤ) : F)) (fun _ => hyF), fun i => ?_⟩
  rw [Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul F]
  exact ⟨⟨_, (mem_integralClosure_iff ℤ E).mpr (hy _ (Finset.mem_image_of_mem c (Finset.mem_univ i)))⟩, rfl⟩

theorem exists_sub_mem (x : AE F E) : ∃ e : E, x - inclE (F := F) (AF F) e ∈ SS F E := by
  obtain ⟨n, b, hb⟩ := exists_basis_mem_intOE (F := F) (E := E)
  choose u hu using fun i => exists_sub_mem_intAd (F := F) (coord b i x)
  refine ⟨∑ i, u i • b i, mem_SS_of_coord b hb _ fun i => ?_⟩
  have h1 : inclE (F := F) (AF F) (∑ j, u j • b j) = (∑ j, u j • b j) ⊗ₜ[F] (1 : AF F) := rfl
  rw [map_sub, h1, coord_tmul, b.repr_sum_self, ← Algebra.algebraMap_eq_smul_one]
  exact hu i

private theorem exists_int_ne_zero_mul_repr_mem_range {n : ℕ} (b : Module.Basis (Fin n) F E) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ e ∈ intOE E, ∀ i, (y : F) * b.repr e i ∈ (algebraMap (𝓞 F) F).range := by
  classical
  let g := NumberField.RingOfIntegers.basis E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin n =>
      b.repr (algebraMap (𝓞 E) E (g p.1)) p.2))
  refine ⟨y, hy0, ?_⟩
  rintro _ ⟨z, rfl⟩ i
  have hz : algebraMap (𝓞 E) E z = ∑ j, g.repr z j • algebraMap (𝓞 E) E (g j) := by
    conv_lhs => rw [← g.sum_repr z]
    simp only [map_sum, map_zsmul]
  have key : (y : F) * b.repr (algebraMap (𝓞 E) E z) i
      = ∑ j, g.repr z j • ((y : F) * b.repr (algebraMap (𝓞 E) E (g j)) i) := by
    rw [hz, map_sum, Finsupp.finset_sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, mul_smul_comm]
  rw [key]
  refine sum_mem fun j _ => zsmul_mem ?_ _
  have h2 : IsIntegral ℤ ((y : F) * b.repr (algebraMap (𝓞 E) E (g j)) i) := by
    have h := hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ (j, i)))
    rw [zsmul_eq_mul] at h
    exact h
  exact ⟨⟨_, (mem_integralClosure_iff ℤ F).mpr h2⟩, rfl⟩

theorem exists_den_of_incl (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] :
    ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ e : E, inclE (F := F) (AF F) e ∈ SS F E → (D : F) • e ∈ intOE E := by
  obtain ⟨n, b, hb⟩ := exists_basis_mem_intOE (F := F) (E := E)
  obtain ⟨y, hy0, hy⟩ := exists_int_ne_zero_mul_repr_mem_range b
  have hyF : ((y : 𝓞 F) : F) = (y : F) := by
    rw [show ((y : 𝓞 F) : F) = algebraMap (𝓞 F) F (y : 𝓞 F) from rfl, map_intCast]
  refine ⟨(y : 𝓞 F), fun h => hy0 ?_, fun e he => ?_⟩
  · have h' := congrArg (algebraMap (𝓞 F) F) h
    rw [map_intCast, map_zero] at h'
    exact_mod_cast h'
  have hc : ∀ i, (y : F) * b.repr e i ∈ (algebraMap (𝓞 F) F).range := by
    intro i
    have h := coord_mem_of_mem_SS b (y : 𝓞 F) (by rw [hyF]; exact hy) he i
    rw [hyF, show inclE (F := F) (AF F) e = e ⊗ₜ[F] (1 : AF F) from rfl, coord_tmul,
      smul_smul, ← Algebra.algebraMap_eq_smul_one] at h
    exact mem_range_of_mem_intAd _ h
  rw [hyF, ← b.sum_repr e, Finset.smul_sum]
  refine sum_mem fun i _ => ?_
  rw [smul_smul]
  obtain ⟨r, hr⟩ := hc i
  rw [← hr, Algebra.smul_def]
  refine mul_mem ?_ (hb i)
  exact ⟨⟨_, (mem_integralClosure_iff ℤ E).mpr ((r.isIntegral_coe).map (IsScalarTower.toAlgHom ℤ F E))⟩, rfl⟩

theorem exists_den_of_isCompact :
    letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ C : Set (AE F E), IsCompact C → ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ x ∈ C, (d : F) • x ∈ SS F E := by
  classical
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  intro C hC
  obtain ⟨n, b, hb⟩ := exists_basis_mem_intOE (F := F) (E := E)
  have hsm : ∀ (r : 𝓞 F) (a : AF F), a ∈ intAd F → algebraMap (𝓞 F) F r • a ∈ intAd F := by
    intro r a ha
    rw [Algebra.smul_def]
    exact mul_mem (algebraMap_mem_intAd r) ha
  have pt : ∀ a : AF F, ∃ d : 𝓞 F, d ≠ 0 ∧ algebraMap (𝓞 F) F d • a ∈ intAd F := by
    intro a
    obtain ⟨u, hu⟩ := exists_sub_mem_intAd (F := F) a
    obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ ({u} : Finset F)
    have hyu : IsIntegral ℤ ((y : F) * u) := by
      have h := hy u (Finset.mem_singleton_self u)
      rw [zsmul_eq_mul] at h
      exact h
    let m : 𝓞 F := ⟨(y : F) * u, (mem_integralClosure_iff ℤ F).mpr hyu⟩
    have hm : algebraMap (𝓞 F) F m = (y : F) * u := rfl
    refine ⟨(y : 𝓞 F), fun h => hy0 ?_, ?_⟩
    · have h' := congrArg (algebraMap (𝓞 F) F) h
      rw [map_intCast, map_zero] at h'
      exact_mod_cast h'
    · have e : algebraMap (𝓞 F) F (y : 𝓞 F) • a
          = algebraMap F (AF F) (algebraMap (𝓞 F) F (y : 𝓞 F)) * (a - algebraMap F (AF F) u)
            + algebraMap F (AF F) (algebraMap (𝓞 F) F m) := by
        rw [hm, map_intCast, Algebra.smul_def, map_mul]
        ring
      rw [e]
      exact add_mem (mul_mem (algebraMap_mem_intAd _) hu) (algebraMap_mem_intAd m)
  have den : ∀ K : Set (AF F), IsCompact K →
      ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ a ∈ K, algebraMap (𝓞 F) F d • a ∈ intAd F := by
    intro K hK
    choose dp hdp0 hdp using pt
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover
      (fun a : AF F => (fun z => z - a) ⁻¹' (intAd F : Set (AF F)))
      (fun a => (isOpen_intAd (F := F)).preimage (continuous_id.sub continuous_const))
      (fun z _ => Set.mem_iUnion.mpr ⟨z, by
        show z - z ∈ intAd F
        rw [sub_self]
        exact zero_mem _⟩)
    refine ⟨∏ c ∈ t, dp c, Finset.prod_ne_zero_iff.mpr fun c _ => hdp0 c, fun z hz => ?_⟩
    have hz' := ht hz
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at hz'
    obtain ⟨c, hct, hzc⟩ := hz'
    rw [← Finset.mul_prod_erase t dp hct]
    have e : algebraMap (𝓞 F) F (dp c * ∏ c' ∈ t.erase c, dp c') • z
        = algebraMap (𝓞 F) F (dp c * ∏ c' ∈ t.erase c, dp c') • (z - c)
          + algebraMap (𝓞 F) F (∏ c' ∈ t.erase c, dp c') • (algebraMap (𝓞 F) F (dp c) • c) := by
      rw [map_mul, mul_comm]
      simp only [smul_sub, mul_smul]
      abel
    rw [e]
    exact add_mem (hsm _ _ hzc) (hsm _ _ (hdp c))
  have hK : ∀ i, IsCompact (coord b i '' C) := fun i => hC.image (continuous_coord b i)
  choose d hd0 hd using fun i => den _ (hK i)
  refine ⟨∏ i, d i, Finset.prod_ne_zero_iff.mpr fun i _ => hd0 i, fun x hx => ?_⟩
  refine mem_SS_of_coord b hb _ fun i => ?_
  rw [map_smul, ← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)]
  show algebraMap (𝓞 F) F (d i * ∏ j ∈ Finset.univ.erase i, d j) • coord b i x ∈ intAd F
  rw [map_mul, mul_comm, mul_smul]
  exact hsm _ _ (hd i _ ⟨x, hx, rfl⟩)

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

end
