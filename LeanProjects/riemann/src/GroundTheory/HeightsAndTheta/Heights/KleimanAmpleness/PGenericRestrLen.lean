import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsGenericRestrLen
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExtendTwist
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PFiniteSections
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PFibreSectionsFlat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Localisation

variable {S : Type u} [CommRing S] {F : Type u} [Field F] [Algebra S F] [IsFractionRing S F]
  {Ω : Type w} [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]

theorem exists_smul_mem_of_mem_span (P : Submodule S Ω) {z : Ω}
    (hz : z ∈ Submodule.span F (P : Set Ω)) : ∃ t ∈ nonZeroDivisors S, t • z ∈ P := by
  refine Submodule.span_induction (p := fun z _ => ∃ t ∈ nonZeroDivisors S, t • z ∈ P)
    (fun z hz => ⟨1, one_mem _, by rwa [one_smul]⟩)
    ⟨1, one_mem _, by rw [smul_zero]; exact P.zero_mem⟩ ?_ ?_ hz
  · rintro a b _ _ ⟨t, ht, ha⟩ ⟨t', ht', hb⟩
    refine ⟨t * t', mul_mem ht ht', ?_⟩
    rw [smul_add]
    refine P.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact P.smul_mem t' ha
    · rw [mul_smul]; exact P.smul_mem t hb
  · rintro c z _ ⟨t, ht, hz⟩
    obtain ⟨⟨a, s⟩, hc⟩ := IsLocalization.surj (nonZeroDivisors S) c
    refine ⟨s * t, mul_mem s.2 ht, ?_⟩
    have key : ((s : S) * t) • (c • z) = a • (t • z) := by
      simp only [Algebra.smul_def, IsScalarTower.algebraMap_apply S F Ω, map_mul] at hc ⊢
      rw [← hc, map_mul]
      ring
    rw [key]
    exact P.smul_mem a hz

variable (F) in

def spanQuotMap (A B : Submodule S Ω) :
    (A ⧸ B.comap A.subtype) →ₗ[S]
      (Submodule.span F (A : Set Ω) ⧸
        (Submodule.span F (B : Set Ω)).comap (Submodule.span F (A : Set Ω)).subtype) :=
  (B.comap A.subtype).liftQ
    ((((Submodule.span F (B : Set Ω)).comap (Submodule.span F (A : Set Ω)).subtype).mkQ.restrictScalars S) ∘ₗ
      { toFun := fun a => ⟨a, Submodule.subset_span a.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl })
    (fun _a ha => LinearMap.mem_ker.mpr ((Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ha)))

theorem isLocalizedModule_spanQuotMap (A B : Submodule S Ω) :
    IsLocalizedModule (nonZeroDivisors S) (spanQuotMap F A B) where
  map_units s := by
    rw [← (Algebra.lsmul S (A := F) S _).commutes]; exact (IsLocalization.map_units F s).map _
  surj y := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨t, ht, hz⟩ := exists_smul_mem_of_mem_span A z.2
    exact ⟨(Submodule.Quotient.mk ⟨t • (z : Ω), hz⟩, ⟨t, ht⟩), rfl⟩
  exists_of_eq {a₁ a₂} h := by
    obtain ⟨a₁, rfl⟩ := Submodule.Quotient.mk_surjective _ a₁
    obtain ⟨a₂, rfl⟩ := Submodule.Quotient.mk_surjective _ a₂
    have hB : (a₁ : Ω) - a₂ ∈ Submodule.span F (B : Set Ω) := (Submodule.Quotient.eq
      ((Submodule.span F (B : Set Ω)).comap (Submodule.span F (A : Set Ω)).subtype)).mp h
    obtain ⟨t, ht, htB⟩ := exists_smul_mem_of_mem_span B hB
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.eq]
    change t • (a₁ : Ω) - t • (a₂ : Ω) ∈ B
    rwa [← smul_sub]

theorem length_spanQuot_toNat (A B : Submodule S Ω) :
    (Module.length F (Submodule.span F (A : Set Ω) ⧸
        (Submodule.span F (B : Set Ω)).comap (Submodule.span F (A : Set Ω)).subtype)).toNat =
      Module.finrank S (A ⧸ B.comap A.subtype) := by
  have := isLocalizedModule_spanQuotMap (F := F) A B
  rw [Module.length_eq_rank, Cardinal.toNat_toENat]
  change Module.finrank F _ = _
  rw [IsLocalization.finrank_eq F (nonZeroDivisors S) le_rfl]
  exact IsLocalizedModule.finrank_eq (p := nonZeroDivisors S) (f := spanQuotMap F A B) (hp := le_rfl)

end Localisation

section Ideal

variable {S : Type u} [CommRing S] {F : Type u} [Field F] [Algebra S F] {N : ℕ}

theorem mem_span_of_mem_map (qq : Ideal (Poly S N)) {f : Poly F N}
    (hf : f ∈ qq.map (MvPolynomial.map (algebraMap S F))) :
    f ∈ Submodule.span F (MvPolynomial.map (algebraMap S F) '' (qq : Set (Poly S N))) := by
  set T := Submodule.span F (MvPolynomial.map (algebraMap S F) '' (qq : Set (Poly S N)))
  have hX : ∀ (i : Fin (N + 1)) (g : Poly F N), g ∈ T → X i * g ∈ T := fun i g hg => by
    refine Submodule.span_induction (p := fun g _ => X i * g ∈ T) ?_
      (by rw [mul_zero]; exact T.zero_mem)
      (fun a b _ _ ha hb => by rw [mul_add]; exact T.add_mem ha hb)
      (fun c g _ hg => by rw [mul_smul_comm]; exact T.smul_mem c hg) hg
    rintro _ ⟨p, hp, rfl⟩
    exact Submodule.subset_span ⟨X i * p, qq.mul_mem_left _ hp, by rw [map_mul, map_X]⟩
  have hmul : ∀ (c g : Poly F N), g ∈ T → c * g ∈ T := fun c => by
    induction c using MvPolynomial.induction_on with
    | C a => intro g hg; rw [← smul_eq_C_mul]; exact T.smul_mem a hg
    | add p q hp hq => intro g hg; rw [add_mul]; exact T.add_mem (hp g hg) (hq g hg)
    | mul_X p i hp => intro g hg; rw [mul_assoc]; exact hp _ (hX i g hg)
  refine Submodule.span_induction (p := fun g _ => g ∈ T) (fun g hg => Submodule.subset_span hg)
    T.zero_mem (fun a b _ _ ha hb => T.add_mem ha hb) (fun c g _ hg => hmul c g hg) hf

variable [IsFractionRing S F] {Ω : Type w} [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]

theorem idealSys_map_eq_extend (x : Fin (N + 1) → Ω) (qq : Ideal (Poly S N))
    (hq : ∀ p ∈ qq, ∀ d : ℕ, homogeneousComponent d p ∈ qq) :
    idealSys x (qq.map (MvPolynomial.map (algebraMap S F))) = (idealSys x qq).extend F := by
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · change idealMod _ I ≤ Submodule.span (chartRing F x I) (idealMod qq I : Set Ω)
    unfold idealMod
    rw [span_extend_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    obtain ⟨s', hs', rfl⟩ := exists_monos_map (S := S) hs
    have hinj : Function.Injective (algebraMap S F) := IsFractionRing.injective S F
    have hse' : s'.IsHomogeneous e := fun d hd => hse (by
      rw [coeff_map]; exact fun h => hd (hinj (h.trans (map_zero _).symm)))
    rw [SetLike.mem_coe, ← homogeneousComponent_eq_self hfe, aeval_map_algebraMap]
    refine Submodule.span_induction (p := fun g _ => aeval x (homogeneousComponent e g) / aeval x s' ∈
      Submodule.span (chartRing F x I) {a | ∃ (f s : Poly S N) (e : ℕ), f ∈ qq ∧ s ∈ monos I.1 ∧
        f.IsHomogeneous e ∧ s.IsHomogeneous e ∧ a = aeval x f / aeval x s}) ?_ ?_ ?_ ?_
      (mem_span_of_mem_map qq hf)
    · rintro _ ⟨p, hp, rfl⟩
      rw [homogeneousComponent_map_eq, aeval_map_algebraMap]
      exact Submodule.subset_span ⟨_, s', e, hq p hp e, hs', homogeneousComponent_isHomogeneous e p, hse', rfl⟩
    · rw [map_zero, map_zero, zero_div]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      rw [map_add, map_add, add_div]; exact Submodule.add_mem _ ha hb
    · intro c g _ hg
      rw [map_smul, map_smul, smul_div_assoc]
      exact Submodule.smul_of_tower_mem _ c hg
  · change Submodule.span (chartRing F x I) (idealMod qq I : Set Ω) ≤ idealMod _ I
    unfold idealMod
    rw [span_extend_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    exact ⟨map (algebraMap S F) f, map (algebraMap S F) s, e, Ideal.mem_map_of_mem _ hf, map_mem_monos hs,
      hfe.map _, hse.map _, by rw [aeval_map_algebraMap, aeval_map_algebraMap]⟩

end Ideal

theorem GenericRestrLen.proof : GenericRestrLen.Statement.{u, w} := by
  intro S _ _ F _ _ _ Ω _ _ _ _ N x Q qq hq
  unfold restrLen
  rw [idealSys_map_eq_extend x qq hq, ← SubSystem.extend_twist, ← span_secs_eq_secs_extend,
    ← span_secs_eq_secs_extend, length_spanQuot_toNat]

end

end GroundTheory.Heights₂.Heights.Kleiman
