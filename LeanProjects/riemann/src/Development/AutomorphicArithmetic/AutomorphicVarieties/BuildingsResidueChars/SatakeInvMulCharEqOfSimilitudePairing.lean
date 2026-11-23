import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAveragingProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af
open GlobalTheory.CuspRep (SmIrr Af invT finId pFin)
open scoped Matrix

section General

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
  {h : G → ℂ} {x y : V}

private theorem pair_heckeVec_comp (hK : IsCommensurated K) (hh : h ∈ Hecke ℂ K) (hx : x ∈ fixed ρ K)
    (hy : y ∈ fixed ρ K) (β : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (d : G → ℂ) (hd : ∀ k ∈ K, d k = 1)
    (hi : ∀ g v w, β (ρ g v) (ρ g w) = d g * β v w) (θ : G →* G) (hθ : ∀ k ∈ K, θ k ∈ K) (z : ℂ)
    (ht : ∀ g, h g ≠ 0 → ∃ a ∈ K, ∃ b ∈ K, ∃ t, θ t = t⁻¹ ∧ g = a * t * b ∧ d t = z) :
    z * β (heckeVec (ρ.comp θ) K h x) y = β x (heckeVec ρ K h y) := by
  have hf := GlobalTheory.LGrp.mem_fixed.1 hx
  have hg := GlobalTheory.LGrp.mem_fixed.1 hy
  have bi : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β (ρ (a * t * b) x) y = β (ρ t x) y := fun a ha b hb t => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hf b hb]
    exact (congrArg (β _) (hg a ha).symm).trans ((hi a _ _).trans (by rw [hd a ha, one_mul]))
  have bi' : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β x (ρ (a * t * b) y) = β x (ρ t y) := fun a ha b hb t => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg b hb]
    exact (congrArg (fun u => β u _) (hf a ha).symm).trans ((hi a _ _).trans (by rw [hd a ha, one_mul]))
  have inv : ∀ t, d t * β (ρ t⁻¹ x) y = β x (ρ t y) := fun t => by
    rw [← hi t]; simp
  have e1 := (z • β.flip y).toAddMonoidHom.map_finsum (finite_heckeVec hK hh (ρ.comp θ) x)
  have e2 := (β x).toAddMonoidHom.map_finsum (finite_heckeVec hK hh ρ y)
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  change z * β (h c.out • ρ (θ c.out) x) y = β x (h c.out • ρ c.out y)
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases h0 : h c.out = 0
  · simp [h0]
  obtain ⟨a, ha, b, hb, t, htt, e, hz⟩ := ht _ h0
  rw [mul_left_comm]
  congr 1
  rw [e, map_mul θ, map_mul θ, bi _ (hθ a ha) _ (hθ b hb), bi' _ ha _ hb, htt, ← hz, inv]

private theorem exists_fixed_pair [TopologicalSpace G] [IsTopologicalGroup G] (hρ : IsSmooth ρ)
    (hK : IsCompact (K : Set G)) (l : V →ₗ[ℂ] ℂ) (hl : ∀ k ∈ K, ∀ v, l (ρ k v) = l v) (y : V) :
    ∃ y' ∈ fixed ρ K, l y' = l y := by
  classical
  open GlobalTheory.OrbitAvg in
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hfi : (GlobalTheory.OrbitAvg.stab ρ K y).FiniteIndex := by
    have ho : IsOpen (GlobalTheory.OrbitAvg.stab ρ K y : Set K) := (hρ y).preimage continuous_subtype_val
    haveI := (GlobalTheory.OrbitAvg.stab ρ K y).quotient_finite_of_isOpen ho
    exact Subgroup.finiteIndex_of_finite_quotient
  refine ⟨GlobalTheory.OrbitAvg.avg ρ K y,
    GlobalTheory.LGrp.mem_fixed.2 fun u hu => GlobalTheory.OrbitAvg.avg_invariant ρ K hfi ⟨u, hu⟩, ?_⟩
  haveI := Fintype.ofFinite (K ⧸ GlobalTheory.OrbitAvg.stab ρ K y)
  have hc : ((GlobalTheory.OrbitAvg.stab ρ K y).index : ℂ) ≠ 0 := by exact_mod_cast hfi.index_ne_zero
  have h1 : ∀ q : K ⧸ GlobalTheory.OrbitAvg.stab ρ K y, l (ρ (q.out : K) y) = l y := fun q => hl _ q.out.2 y
  simp only [GlobalTheory.OrbitAvg.avg, GlobalTheory.OrbitAvg.avgH, GlobalTheory.OrbitAvg.cv, finsum_eq_sum_of_fintype, map_smul, map_sum]
  rw [Finset.sum_congr rfl fun q _ => h1 q, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Subgroup.index, nsmul_eq_mul, smul_eq_mul, inv_mul_cancel_left₀ hc]

end General

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.ConjPlace in
theorem UpperTheory.satake_inv_mul_char_eq_of_similitude_pairing :
    ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (w : HeightOneSpectrum (𝓞 F)) (V : Type) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion F)) V), GlobalTheory.PRep.IsSmooth ρ → ∀ (χ : HChar F), χ.UnrAt w →
        ∀ (β : V →ₗ[ℂ] V →ₗ[ℂ] ℂ), (∀ x, (∀ y, β x y = 0) → x = 0) →
        (∀ g x y, β (ρ g x) (ρ g y) = ((χ.loc w (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * β x y) →
        ∀ B : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w ρ B → (B.map (·⁻¹)).map (· * χ.val w) = B := by
  intro E _ _ n w V _ _ ρ hρ χ hχ β hβ hi B hB
  classical
  obtain ⟨x, hx⟩ := hB.exists_vec
  have hd : ∀ k ∈ KGL w n, ((χ.loc w (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) = 1 := fun k hk => by
    rw [hχ _ (GlobalTheory.SphGal.isUnitAt_det_of_mem hk), Units.val_one]
  have hKc : IsCompact (KGL w n : Set (GL (Fin n) (w.adicCompletion E))) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w)
  obtain ⟨y₀, hy₀⟩ : ∃ y, β x y ≠ 0 := by
    by_contra hn
    exact hx.1 (hβ x fun y => by_contra fun h => hn ⟨y, h⟩)
  obtain ⟨y, hyK, hy⟩ := exists_fixed_pair hρ hKc (β x) (fun k hk v => by
    have := hi k x v
    rwa [GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk, hd k hk, one_mul] at this) y₀
  have hne : β x y ≠ 0 := hy ▸ hy₀
  have hy' := hB.2 y hyK fun h0 => hne (by rw [h0, map_zero])
  let c := RingEquiv.refl (w.adicCompletion E)
  have hc : ∀ a, Valued.v (c a) = Valued.v a := fun _ => rfl
  have hx' := isSatVecGL_invT c hc rfl hx
  have hK := mem_iff_invT (n := n) c (map_mem_Ov_iff c hc)
  obtain ⟨p, hp⟩ := exists_isUnifV w
  obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p :=
    ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
  refine eq_of_satEig_eq (qV_ne_zero w) (by simpa using hx.2.2.1) hx.2.2.1 fun j hj => ?_
  have key := pair_heckeVec_comp (Final.GLintComm E w n) (Tj_mem_hecke hp j) hx.2.1 hyK β _ hd hi
    (GlobalTheory.LFun.ConjPlace.invT c n).symm.toMonoidHom (fun k hk => (hK _).2 (by simpa using hk))
    ((χ.val w : ℂ) ^ j)
    (fun g hg => by
      rw [Tj_apply] at hg
      obtain ⟨a, ha, b, hb, e⟩ : ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
          g = a * dGL n ϖ j * b := by
        by_contra hn
        exact hg (if_neg hn)
      refine ⟨a, ha, b, hb, _, (GlobalTheory.LFun.ConjPlace.invT c n).symm_apply_eq.2 (invT_dGL c ϖ j).symm, e, ?_⟩
      rw [GlobalTheory.SphGal.loc_det_of_Tj hχ hp hj, Units.val_pow_eq_pow_val]
      rw [Tj_apply, if_pos ⟨1, one_mem _, 1, one_mem _, by rw [one_mul, mul_one]; rfl⟩]
      exact one_ne_zero)
  rw [hx'.2.2.2 _ hp j hj, hy'.2.2.2 _ hp j hj, map_smul, map_smul, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul, ← mul_assoc] at key
  rw [GlobalTheory.SphGal.satEig_map_mul]
  exact mul_right_cancel₀ hne key
