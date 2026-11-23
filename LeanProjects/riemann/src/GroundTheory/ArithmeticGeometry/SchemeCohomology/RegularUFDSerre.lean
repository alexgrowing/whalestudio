import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularLocalDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open IsLocalRing Ideal RingTheory.Sequence

universe u

variable {R : Type u} [CommRing R]

theorem exists_isRegular_ofList_eq_maximalIdeal [IsRegularLocalRing R] :
    ∃ rs : List R, IsRegular R rs ∧ ofList rs = maximalIdeal R ∧
      (rs.length : WithBot ℕ∞) = ringKrullDim R := by
  suffices H : ∀ n : ℕ, ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      (maximalIdeal S).spanFinrank = n → ∃ rs : List S, IsRegular S rs ∧
        ofList rs = maximalIdeal S ∧ (rs.length : WithBot ℕ∞) = ringKrullDim S from H _ R rfl
  intro n
  induction n with
  | zero =>
    intro S _ _ hn
    have hfg : (maximalIdeal S).FG := (maximalIdeal S).fg_of_isNoetherianRing
    have hbot : maximalIdeal S = ⊥ := (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mp hn
    refine ⟨[], IsRegular.nil S S, by simp [hbot], ?_⟩
    rw [← (isRegularLocalRing_iff S).mp inferInstance, hn]
    simp
  | succ n ih =>
    intro S _ _ hn
    have := IsRegularLocalRing.isDomain (R := S)
    have hfg : (maximalIdeal S).FG := (maximalIdeal S).fg_of_isNoetherianRing
    have hjac : maximalIdeal S ≤ jacobson ⊥ :=
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    have hsq : ¬ maximalIdeal S ≤ maximalIdeal S ^ 2 := by
      intro hle
      have : maximalIdeal S = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg
        (by simpa [pow_two, smul_eq_mul] using hle) hjac
      rw [this] at hn; simp at hn
    obtain ⟨x, hx, hx2⟩ := Set.not_subset.mp hsq
    have hx0 : x ≠ 0 := fun h ↦ hx2 (h ▸ zero_mem _)
    have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
      (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
    have : Nontrivial (S ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (S ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
    obtain ⟨hreg, hdim⟩ := isRegularLocalRing_quotient hx hx2
    have hlt := spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
    have hB : (maximalIdeal (S ⧸ span {x})).spanFinrank = n := by
      have h1 := (isRegularLocalRing_iff S).mp inferInstance
      have h2 := (isRegularLocalRing_iff (S ⧸ span {x})).mp hreg
      rw [← h1, ← h2, hn] at hdim
      have : ((maximalIdeal (S ⧸ span {x})).spanFinrank + 1 : ℕ) = n + 1 := by exact_mod_cast hdim
      omega
    obtain ⟨rsB, hrsB, hofB, hlenB⟩ := ih (S ⧸ span {x}) hB
    let lift : S ⧸ span {x} → S := Function.surjInv Ideal.Quotient.mk_surjective
    have hlift : ∀ b, Ideal.Quotient.mk (span {x}) (lift b) = b :=
      Function.surjInv_eq Ideal.Quotient.mk_surjective
    let rs' := rsB.map lift
    have hmap : rs'.map (Ideal.Quotient.mk (span {x})) = rsB := by
      simp [rs', List.map_map, Function.comp_def, hlift]
    refine ⟨x :: rs', ?_, ?_, ?_⟩
    · rw [isRegular_cons_iff']
      refine ⟨?_, ?_⟩
      · exact fun a b h ↦ mul_left_cancel₀ hx0 h
      · rw [hmap]
        have e0 : QuotSMulTop x S ≃ₗ[S] S ⧸ span {x} :=
          Submodule.quotEquivOfEq _ _ (by
            rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])
        let e : QuotSMulTop x S ≃ₗ[S ⧸ span {x}] S ⧸ span {x} :=
          LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective e0
        exact (e.isRegular_congr rsB).mpr hrsB
    · have h1 : (ofList rs').map (Ideal.Quotient.mk (span {x})) =
          (maximalIdeal S).map (Ideal.Quotient.mk (span {x})) := by
        rw [Ideal.map_ofList, hmap, hofB,
          map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
      have h2 := congrArg (Ideal.comap (Ideal.Quotient.mk (span {x}))) h1
      simp only [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker] at h2
      rw [ofList_cons, sup_comm, h2, sup_eq_left.mpr ((span_singleton_le_iff_mem _).mpr hx)]
    · rw [List.length_cons, List.length_map, ← hdim, ← hlenB]
      push_cast
      rfl

open CategoryTheory Abelian

theorem hasProjectiveDimensionLT_of_forall_prime [IsNoetherianRing R] (n : ℕ) (I : Ideal R)
    (hI : ∀ q : Ideal R, q.IsPrime → I ≤ q →
      HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ q)) n)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : ∀ a ∈ I, ∀ m : M, a • m = 0) :
    HasProjectiveDimensionLT (ModuleCat.of R M) n := by
  revert hM
  induction ‹Module.Finite R M› using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime
    with
  | subsingleton N =>
    intro _
    have : Limits.IsZero (ModuleCat.of R N) := ModuleCat.isZero_of_subsingleton _
    have := this.hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge _ 0 n (Nat.zero_le _)
  | quotient N p e =>
    intro hN
    have hle : I ≤ p.1 := by
      intro a ha
      have h := congrArg e (hN a ha (e.symm 1))
      rw [map_smul, LinearEquiv.apply_symm_apply, map_zero, Algebra.smul_def, mul_one,
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at h
      exact h
    have := hI p.1 p.2 hle
    exact hasProjectiveDimensionLT_of_iso e.symm.toModuleIso n
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    intro hN
    have k₁ : ∀ a ∈ I, ∀ m : N₁, a • m = 0 := fun a ha m ↦ hf (by rw [map_smul, hN a ha, map_zero])
    have k₃ : ∀ a ∈ I, ∀ m : N₃, a • m = 0 := fun a ha m ↦ by
      obtain ⟨m, rfl⟩ := hg m
      rw [← map_smul, hN a ha, map_zero]
    have hS := ModuleCat.shortComplex_shortExact
      (ModuleCat.shortComplexOfCompEqZero f g (LinearMap.ext fun x ↦ hfg.apply_apply_eq_zero x))
      hfg hf hg
    exact hS.hasProjectiveDimensionLT_X₂ n (h₁ k₁) (h₃ k₃)

theorem hasProjectiveDimensionLT_residueField [IsRegularLocalRing R] {d : ℕ}
    (hd : ringKrullDim R = d) :
    HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) (d + 1) := by
  obtain ⟨rs, hreg, hof, hlen⟩ := exists_isRegular_ofList_eq_maximalIdeal (R := R)
  have hrs : rs.length = d := by rw [hd] at hlen; exact_mod_cast hlen
  have h := ModuleCat.projectiveDimension_quotient_eq_length.{u} (R := R) rs hreg
  have h' : HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{u} (R ⧸ ofList rs))) d :=
    (projectiveDimension_le_iff _ d).mp (by rw [h, hrs])
  let e : Shrink.{u} (R ⧸ ofList rs) ≃ₗ[R] R ⧸ maximalIdeal R :=
    (Shrink.linearEquiv R _).trans (Submodule.quotEquivOfEq _ _ hof)
  exact hasProjectiveDimensionLT_of_iso e.toModuleIso (d + 1)

set_option backward.isDefEq.respectTransparency false in

theorem hasProjectiveDimensionLT_of_residueField [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)
    (hk : HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) (n + 1))
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    HasProjectiveDimensionLT (ModuleCat.of R M) (n + 1) := by
  have hprime : ∀ p : Ideal R, p.IsPrime →
      HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ p)) (n + 1) := by
    intro p
    induction p using WellFoundedGT.induction with
    | _ p ih =>
    intro hp
    by_cases hpm : p = maximalIdeal R
    · subst hpm; exact hk
    · have hlt : p < maximalIdeal R := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hp.ne_top) hpm
      obtain ⟨x, hxm, hxp⟩ := Set.exists_of_ssubset hlt
      let N := R ⧸ p
      have hx0 : Ideal.Quotient.mk p x ≠ 0 := by
        rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      have reg : IsSMulRegular N x := by
        intro a b h
        simp only [Algebra.smul_def] at h
        exact mul_left_cancel₀ hx0 h
      have hS := IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R N) reg
      have h3 : HasProjectiveDimensionLT (ModuleCat.of R (QuotSMulTop x N)) (n + 1) := by
        refine hasProjectiveDimensionLT_of_forall_prime (n + 1) (p ⊔ span {x}) ?_ _ ?_
        · intro q hq hle
          exact ih q (lt_of_le_of_ne (le_sup_left.trans hle) (fun h ↦ hxp (h ▸
            hle (le_sup_right (a := p) ((span_singleton_le_iff_mem _).mp le_rfl))))) hq
        · intro a ha m
          have hann : p ⊔ span {x} ≤ Module.annihilator R (QuotSMulTop x N) := by
            refine sup_le ?_ ((span_singleton_le_iff_mem _).mpr (QuotSMulTop.mem_annihilator N x))
            intro b hb
            rw [Module.mem_annihilator]
            intro m
            obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ m
            obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
            rw [← map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
              Ideal.Quotient.eq_zero_iff_mem.mpr (p.mul_mem_right m hb), map_zero]
          exact Module.mem_annihilator.mp (hann ha) m
      apply ModuleCat.hasProjectiveDimensionLT_of_forall_finite
      intro L _
      have zero := HasProjectiveDimensionLT.subsingleton
        (ModuleCat.of R (QuotSMulTop x N)) (n + 1) (n + 2) (by omega) L
      have exac := Ext.contravariant_sequence_exact₁' hS L (n + 1) (n + 2) (add_comm 1 (n + 1))
      have epi := exac.epi_f ((@AddCommGrpCat.isZero_of_subsingleton _ zero).eq_zero_of_tgt _)
      have : (ModuleCat.smulShortComplex (ModuleCat.of R N) x).f = x • 𝟙 (ModuleCat.of R N) := rfl
      simp only [this, AddCommGrpCat.epi_iff_surjective, AddCommGrpCat.hom_ofHom] at epi
      by_contra! ntr
      have : x ∈ (Module.annihilator R (Ext (ModuleCat.of R N) L (n + 1))).jacobson :=
        (IsLocalRing.maximalIdeal_le_jacobson _) hxm
      absurd Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator this
      rw [eq_comm, eq_top_iff]
      intro y hy
      rcases epi y with ⟨z, hz⟩
      simp only [ModuleCat.smulShortComplex, Ext.mk₀_smul,
        Ext.bilinearComp_apply_apply, Ext.smul_comp, Ext.mk₀_id_comp] at hz
      simpa [← hz] using Submodule.smul_mem_pointwise_smul _ _ ⊤ trivial
  exact hasProjectiveDimensionLT_of_forall_prime (n + 1) ⊥ (fun q hq _ ↦ hprime q hq) M
    (fun a ha m ↦ by rw [(Submodule.mem_bot R).mp ha, zero_smul])

theorem hasProjectiveDimensionLT_of_isRegularLocalRing [IsRegularLocalRing R] {d : ℕ}
    (hd : ringKrullDim R = d) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    HasProjectiveDimensionLT (ModuleCat.of R M) (d + 1) :=
  hasProjectiveDimensionLT_of_residueField d (hasProjectiveDimensionLT_residueField hd) M

end GroundTheory.Arith.SchemeCoh
