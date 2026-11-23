import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.LevelComponentsSurjective
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.LocRed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxGroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.LocKMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.CstNatCastApply

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct Matrix

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E) (Λ : Set (Fin n → E))

theorem kgv_conj (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) (a y : HA (Fv F v) σ J) (ha : a ∈ Kv σ J Λ v)
    (hy : y ∈ Kgv σ J Λ g v) : a⁻¹ * y * a ∈ Kgv σ J Λ g v := by
  unfold Kgv Kv Kloc at *
  obtain ⟨hy1, hy2⟩ := hy
  simp only [Set.mem_setOf_eq] at ha hy1 ⊢
  have hm : HA.mat (Fv F v) σ J (a⁻¹ * y * a) =
      (HA.mat (Fv F v) σ J a)⁻¹ * HA.mat (Fv F v) σ J y * HA.mat (Fv F v) σ J a := rfl
  rw [hm]
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hy1) ha, fun y0 hy0 => ?_⟩
  set A := HA.mat (Fv F v) σ J a
  set Y := HA.mat (Fv F v) σ J y
  have ha' : ∀ x, x ∈ latLoc v Λ ↔ (A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x ∈ latLoc v Λ := ha
  obtain ⟨z1, hz1, hz1e⟩ := hy2 ((A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ y0) ((ha' y0).mp hy0)
  refine ⟨((A⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ z1, ?_, ?_⟩
  · rw [ha', Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    exact hz1
  · have key : ((A⁻¹ * Y * A : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) - 1 =
        ((A⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *
          ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) - 1) * (A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := by
      rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]
    rw [key, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz1e, Matrix.mulVec_smul]

end Gen

theorem isUnit_natCast_of_not_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (m : ℕ)
    (hm : (m : 𝓞 F) ∉ v.asIdeal) : IsUnit ((m : v.adicCompletionIntegers F)) := by
  rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one,
    ← map_natCast (algebraMap (𝓞 F) (v.adicCompletionIntegers F)) m,
    IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact le_antisymm (IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v _)
    (not_lt.1 fun h => hm ((IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem v _).1 h))

variable {D : D7}

theorem g_eq_gOf_mul_unit (X : HidaSetting D) (p : TypX X) :
    ∃ w : (p.1.adicCompletionIntegers X.B.I.F)ˣ,
      ((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F) =
        ((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) * (w : p.1.adicCompletionIntegers X.B.I.F) := by
  have hg := X.g_eq
  have hp0 := D.host.g_prime 0
  have hp1 := D.host.g_prime 1
  have hne := D.host.g_ne
  unfold Formalism.L2.SG.TypedSets.gOf
  split_ifs with h0
  · have h1 : ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∉ p.1.asIdeal := by
      intro h1
      have hcop : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) := by
        have h := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp0 hp1).2 hne)
        simpa using h.map (Int.castRingHom (𝓞 X.B.I.F))
      obtain ⟨a, b, hab⟩ := hcop
      have h1mem : (1 : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
        rw [← hab]
        exact p.1.asIdeal.add_mem (p.1.asIdeal.mul_mem_left a h0) (p.1.asIdeal.mul_mem_left b h1)
      exact p.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1mem)
    refine ⟨(isUnit_natCast_of_not_mem p.1 _ h1).unit, ?_⟩
    rw [IsUnit.unit_spec, hg, Nat.cast_mul]
  · refine ⟨(isUnit_natCast_of_not_mem p.1 _ h0).unit, ?_⟩
    rw [IsUnit.unit_spec, hg, Nat.cast_mul, mul_comm]

theorem kgv_of_gOf (X : HidaSetting D) (p : TypX X) (y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)
    (hy : y ∈ Kgv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (gOf p) p.1) :
    y ∈ Kgv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) X.B.g p.1 := by
  obtain ⟨w, hw⟩ := g_eq_gOf_mul_unit X p
  simp only [Formalism.L2.SG.TypedSets.Kgv, Set.mem_setOf_eq] at hy ⊢
  obtain ⟨hKv, h⟩ := hy
  refine ⟨hKv, fun y' hy' => ?_⟩
  obtain ⟨z, hz, e⟩ := h y' hy'
  refine ⟨((w⁻¹ : (p.1.adicCompletionIntegers X.B.I.F)ˣ) : p.1.adicCompletionIntegers X.B.I.F) • z,
    Submodule.smul_mem _ _ hz, ?_⟩
  rw [e, smul_smul, hw, mul_assoc, Units.mul_inv, mul_one]

theorem coe_K2Hg (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word) :
    (unitaryLevelClosureSubgroup X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) = Subtype.val ⁻¹' K2u X hb u := by
  obtain ⟨h1, hmul, hinv, -, -⟩ := hK
  have fmul : ∀ a b : X.B.I.Gf, finHA X hb (a * b) = finHA X hb a * finHA X hb b := by
    intro a b
    unfold finHA
    rw [← Prod.snd_mul, ← map_mul, ← map_mul, Prod.mk_mul_mk, mul_one]
  have finv : ∀ a : X.B.I.Gf, finHA X hb a⁻¹ = (finHA X hb a)⁻¹ := by
    intro a
    unfold finHA
    rw [← Prod.snd_inv, ← map_inv, ← map_inv, Prod.inv_mk, inv_one]
  have fone : finHA X hb 1 = 1 := by
    unfold finHA
    show ((splitA X.B.I.cm.sig X.B.I.J) ((toHA X.B.I hb) 1)).2 = 1
    rw [map_one, map_one, Prod.snd_one]
  let S : Subgroup (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) :=
    { carrier := Subtype.val ⁻¹' K2u X hb u
      mul_mem' := by
        rintro x y ⟨_, ⟨k1, hk1, rfl⟩, hx⟩ ⟨_, ⟨k2, hk2, rfl⟩, hy⟩
        refine ⟨finHA X hb (k1 * k2), ⟨k1 * k2, hmul k1 hk1 k2 hk2, rfl⟩, ?_⟩
        simp only [Subgroup.coe_mul, ← hx, ← hy, fmul]
        group
      one_mem' := ⟨finHA X hb 1, ⟨1, h1, rfl⟩, by simp [fone]⟩
      inv_mem' := by
        rintro x ⟨_, ⟨k, hk, rfl⟩, hx⟩
        refine ⟨finHA X hb k⁻¹, ⟨k⁻¹, hinv k hk, rfl⟩, ?_⟩
        simp only [Subgroup.coe_inv, ← hx, finv]
        group }
  unfold unitaryLevelClosureSubgroup
  exact congrArg (fun H : Subgroup (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) =>
    (H : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))) (Subgroup.closure_eq S)

theorem mem_conjugate_level_of_local (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized)
    (u : D.what₂.Word) (z : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)
    (hz : z ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
    (hloc : ∀ p : TypX X, ∃ k ∈ X.K2, PI.MassDataKppVolLemmas.piV X.B.I p.1 (finHA X hb k) =
      PI.MassDataKppVolLemmas.piV X.B.I p.1 ((finHA X hb (X.xu u))⁻¹ * z * finHA X hb (X.xu u))) :
    z ∈ K2u X hb u := by
  classical
  have ha : finHA X hb (X.xu u) ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    (PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb (X.xu u)).2 (X.xu_K u)
  obtain ⟨y, hy⟩ := PI.MassDataKppVolLemmas.Bridge_tf_surjective X.B.I hb
    ((finHA X hb (X.xu u))⁻¹ * z * finHA X hb (X.xu u))
  have hyK : y ∈ X.B.I.Kset := by
    rw [← PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb, hy]
    exact mul_mem (mul_mem (inv_mem ha) hz) ha
  have hgc := PI.MassDataKppVolLemmas.Cst_gc X.B.I (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero
    (D.host.g_prime 1).ne_zero
  rw [← X.g_eq] at hgc
  have hy2 : y ∈ X.K2 := by
    refine PI.MassDataKppVolLemmas.LocK_mem X.B.I X.K2 hK.1 hK.2.1 X.B.g (fun x hx => (hL.1 x hx).1) Finset.univ
      (fun p : TypX X => PI.MassDataKppVolLemmas.chi X.B.I p.1) (fun p => PI.MassDataKppVolLemmas.Comp_chi_idem X.B.I p.1)
      (fun p q hpq => PI.MassDataKppVolLemmas.Comp_chi_orth X.B.I p.1 q.1 fun h => hpq (Subtype.ext h))
      (PI.MassDataKppVolLemmas.cElt X.B.I (D.host.g 0) (D.host.g 1)) (PI.MassDataKppVolLemmas.Cst_int X.B.I _ _) hgc y hyK ?_
    intro p _
    obtain ⟨k, hk, hkz⟩ := hloc p
    rw [PI.MassDataKppVolLemmas.Comp_sep X.B.I hb p.1 y k (by rw [hy]; exact hkz.symm)]
    exact PI.MassDataKppVolLemmas.LocB_K2set X.B.I _ _ _ _ _ (PI.MassDataKppVolLemmas.Comp_chi_idem X.B.I p.1)
      (PI.MassDataKppVolLemmas.Comp_chi_int X.B.I p.1) k hk
  rw [mem_conjugate_level_iff]
  refine ⟨y, hy2, ?_⟩
  have e : finHA X hb y = (finHA X hb (X.xu u))⁻¹ * z * finHA X hb (X.xu u) := hy
  rw [e]
  group

theorem level_membership_local : LocH := by
  intro D X hb hK u hMT hL z hz hloc
  have hc := coe_K2Hg X hb hK u
  have hmem : (z : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ K2u X hb u := by
    refine mem_conjugate_level_of_local X hb hK hL u z (Subgroup.mem_subgroupOf.mp hz) ?_
    intro p
    obtain ⟨w, hw, hwe⟩ := hloc p
    have hw' : (w : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ K2u X hb u := by
      have h2 : w ∈ (unitaryLevelClosureSubgroup X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) := hw
      rw [hc] at h2
      exact h2
    obtain ⟨_, ⟨k, hk, rfl⟩, hwk⟩ := hw'
    refine ⟨k, hk, ?_⟩
    have hv : haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F ↑p) (w : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) =
        haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F ↑p) (z : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
      congrArg Subtype.val hwe
    unfold PI.MassDataKppVolLemmas.piV
    simp only [map_mul, map_inv, ← hv, ← hwk]
    group
  have h3 : z ∈ (unitaryLevelClosureSubgroup X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) := by
    rw [hc]
    exact hmem
  exact h3

theorem hKerIn_of_levelSubgroupCharacter_of_normalized (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized)
    (u : D.what₂.Word) (p : TypX X) : HKerIn X hb u p := by
  intro x hx
  set y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J :=
    ((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)
    with hy_def
  have hyK : y ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 := x.2
  have hyg : y ∈ Kgv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (gOf p) p.1 := hx
  obtain ⟨h, hKf, h1, h2⟩ := PI.MassDataKppVolLemmas.single_component_surjective X.B.I p.1 y hyK
  have hH : h ∈ Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) := by
    apply mem_stabT_of_comp X.B.I h
    intro v
    by_cases hv : v = p.1
    · subst hv; rw [h1]; exact (x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)).2
    · rw [h2 v hv]; exact one_mem _
  have ha : finHA X hb (X.xu u) ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    (PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb (X.xu u)).2 (X.xu_K u)
  have hK2u : h ∈ K2u X hb u := by
    apply mem_conjugate_level_of_local X hb hK hL u h hKf
    intro q
    by_cases hq : q = p
    · subst hq
      have hap : PI.MassDataKppVolLemmas.piV X.B.I q.1 (finHA X hb (X.xu u)) ∈
          Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) q.1 := by
        have := ha
        rw [Kf, Subgroup.mem_iInf] at this
        exact this q.1
      have hmem : PI.MassDataKppVolLemmas.piV X.B.I q.1 ((finHA X hb (X.xu u))⁻¹ * h * finHA X hb (X.xu u)) ∈
          Kgv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) X.B.g q.1 := by
        rw [map_mul, map_mul, map_inv, h1]
        exact kgv_of_gOf X q _ (kgv_conj X.B.I.cm.sig X.B.I.J _ q.1 (gOf q) _ _ hap hyg)
      have hg0 : X.B.g ≠ 0 := by
        rw [X.g_eq]; exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
      obtain ⟨k, hk, hkc⟩ := PI.MassDataKppVolLemmas.LocIdxLift_Kg X.B.I hb q.1 X.B.g hg0 _ hmem
      exact ⟨k, (hL.1 k hk).1, hkc⟩
    · refine ⟨1, hK.1, ?_⟩
      have hq1 : q.1 ≠ p.1 := fun e => hq (Subtype.ext e)
      rw [finHA_one, map_one, map_mul, map_mul, map_inv, h2 q.1 hq1, mul_one, inv_mul_cancel]
  rw [Subgroup.mem_subgroupOf]
  refine ⟨⟨h, hH⟩, ?_, ?_⟩
  · apply Subgroup.subset_closure
    exact hK2u
  · apply Subtype.ext
    exact h1

end PIW.MassDataColumns
