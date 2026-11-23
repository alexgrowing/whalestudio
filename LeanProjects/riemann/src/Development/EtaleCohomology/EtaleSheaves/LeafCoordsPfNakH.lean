import Development.EtaleCohomology.EtaleSheaves.LeafCoordsPf

noncomputable section

namespace LateralTheory.E.LeafCoordsPf.NakH

open scoped Pointwise
open Polynomial

theorem eval_notMem {B : Type} [CommRing B] {P : Ideal B} (hP : P.IsPrime) (p : B[X]) (hm : p.Monic)
    (hc : ∀ k, p.coeff k ∈ P ^ (p.natDegree - k)) {h : B} (hh : h ∉ P) : p.eval h ∉ P := by
  intro H
  have hsum : ∑ i ∈ Finset.range p.natDegree, p.coeff i * h ^ i ∈ P := by
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ ?_
    have hi' : p.natDegree - i ≠ 0 := by
      have := Finset.mem_range.mp hi
      omega
    exact Ideal.pow_le_self hi' (hc i)
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, one_mul] at H
  have : h ^ p.natDegree ∈ P := by
    have := P.sub_mem H hsum
    simpa using this
  exact hh (hP.mem_of_pow_mem _ this)

theorem nakH : LeafNakH := by
  intro B M _ _ _ P hP N N' hfg h hh hle
  have : Module.Finite B N' := Module.Finite.iff_fg.mpr hfg
  let Q := N' ⧸ N.comap N'.subtype
  let f : Module.End B Q := algebraMap B (Module.End B Q) h
  have hr : LinearMap.range f ≤ P • ⊤ := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨⟨n, hn⟩, rfl⟩ := Submodule.mkQ_surjective _ q
    have hhn : h • n ∈ N ⊔ P • N' := hle (Submodule.smul_mem_pointwise_smul n h N' hn)
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hhn
    have hb' : b ∈ (P • (⊤ : Submodule B N')).map N'.subtype := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top]
      exact hb
    obtain ⟨b', hb'1, hb'2⟩ := hb'
    have heq : f ((N.comap N'.subtype).mkQ ⟨n, hn⟩) = (N.comap N'.subtype).mkQ b' := by
      simp only [f, Module.algebraMap_end_apply, Submodule.mkQ_apply]
      show (Submodule.Quotient.mk (h • (⟨n, hn⟩ : N')) : N' ⧸ N.comap N'.subtype) = Submodule.Quotient.mk b'
      rw [Submodule.Quotient.eq, Submodule.mem_comap]
      simp only [Submodule.subtype_apply, SetLike.val_smul, Submodule.coe_sub, hb'2]
      convert ha using 1
      rw [← hab]
      have hb3 : (b' : M) = b := hb'2
      rw [hb3]
      abel
    rw [heq]
    have : (P • (⊤ : Submodule B N')).map (N.comap N'.subtype).mkQ ≤ P • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact this ⟨b', hb'1, rfl⟩
  obtain ⟨p, hm, -, hc, hp⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero B f P hr
  refine ⟨p.eval h, eval_notMem hP p hm hc hh, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have := LinearMap.congr_fun hp (Submodule.Quotient.mk ⟨x, hx⟩)
  rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, Module.algebraMap_end_apply, LinearMap.zero_apply,
    ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
  simpa using this

theorem LeafCoords_of_point (hPt : LeafCoordsPoint) : LateralTheory.E.LeafChartRingPf.LeafCoords :=
  LeafCoords_of hPt nakH

end LateralTheory.E.LeafCoordsPf.NakH
