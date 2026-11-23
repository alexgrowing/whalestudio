import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FinrankHostDivTwo

namespace GlobalTheory.SecCount

open MvPolynomial

theorem injective_of_indep_image {K Γ L ι : Type} [Field K] [CommRing Γ] [IsDomain Γ] [Algebra K Γ] [CommRing L]
    [Algebra K L] [Finite ι] (b : ι → Γ) (hΓ : Algebra.trdeg K Γ ≤ Cardinal.mk ι) (ψ : Γ →ₐ[K] L)
    (hb' : AlgebraicIndependent K (ψ ∘ b)) : Function.Injective ψ := by
  have hb : AlgebraicIndependent K b := AlgebraicIndependent.of_comp ψ hb'
  have hB := hb.isTranscendenceBasis_of_trdeg_le_of_finite hΓ
  have halg := hB.isAlgebraic
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hne
  obtain ⟨r, hr0, c, hc⟩ := (halg.isAlgebraic a).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hne)
  obtain ⟨r, hr⟩ := r
  have hr' := hr
  rw [Algebra.adjoin_range_eq_range_aeval] at hr'
  obtain ⟨q, rfl⟩ := hr'
  have hc' : aeval b q = a * c := hc
  have h1 : aeval (ψ ∘ b) q = ψ (aeval b q) := (MvPolynomial.comp_aeval_apply b ψ q).symm
  have hq : q = 0 := hb' (by rw [h1, hc', map_mul, ha, zero_mul, map_zero])
  exact hr0 (Subtype.ext (by simp [hq]))

theorem injective_of_relations {K Γ L : Type} [Field K] [CommRing Γ] [IsDomain Γ] [Algebra K Γ] [Field L]
    [Algebra K L] {D N : ℕ} (hΓ : Algebra.trdeg K Γ ≤ D) (ψ : Γ →ₐ[K] L) (t : Fin D × Fin N → L)
    (ht : AlgebraicIndependent K t) (y : Fin N → Γ) (k₁ : Fin N) (hy : ψ (y k₁) = 1)
    (hrel : ∀ i, ∑ k, t (i, k) * ψ (y k) = 0) : Function.Injective ψ := by
  classical
  let M := AlgebraicIndependent.matroid K L
  obtain ⟨B, hB⟩ := M.exists_isBasis (Set.range ψ) (Set.subset_univ _)
  let U : Set (Fin D × Fin N) := {p | p.2 = k₁}
  let S : Set L := B ∪ t '' Uᶜ
  have hcl : ∀ x, x ∈ M.closure S ↔ x ∈ Subalgebra.algebraicClosure (Algebra.adjoin K S) L := fun x => by
    rw [AlgebraicIndependent.matroid_closure_eq]; rfl
  have hψ : ∀ g, ψ g ∈ Subalgebra.algebraicClosure (Algebra.adjoin K S) L := fun g =>
    (hcl _).1 (M.closure_subset_closure Set.subset_union_left (hB.subset_closure ⟨g, rfl⟩))
  have hV : ∀ p : Fin D × Fin N, p.2 ≠ k₁ → t p ∈ Subalgebra.algebraicClosure (Algebra.adjoin K S) L := fun p hp =>
    (hcl _).1 (M.subset_closure S (Set.subset_univ _) (Or.inr ⟨p, hp, rfl⟩))
  have hsub : Set.range t ⊆ M.closure S := by
    rintro _ ⟨⟨i, k⟩, rfl⟩
    rw [hcl]
    by_cases hk : k = k₁
    · subst hk
      have h := hrel i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hy, mul_one] at h
      rw [eq_neg_of_add_eq_zero_left h]
      exact neg_mem (sum_mem fun k' hk' => mul_mem (hV (i, k') (Finset.ne_of_mem_erase hk')) (hψ _))
    · exact hV _ hk
  have hind : M.Indep (Set.range t) := ht.coe_range
  have h1 : (Set.range t).encard ≤ B.encard + (t '' Uᶜ).encard := by
    calc (Set.range t).encard = M.eRk (Set.range t) := hind.eRk_eq_encard.symm
      _ ≤ M.eRk (M.closure S) := M.eRk_mono hsub
      _ = M.eRk S := M.eRk_closure_eq S
      _ ≤ S.encard := M.eRk_le_encard S
      _ ≤ _ := Set.encard_union_le _ _
  have h2 : (Set.range t).encard = D + (t '' Uᶜ).encard := by
    rw [← Set.image_univ, ← Set.union_compl_self U, Set.image_union,
      Set.encard_union_eq ((Set.disjoint_image_iff ht.injective).2 disjoint_compl_right)]
    congr 1
    rw [ht.injective.encard_image]
    have : U = Set.range fun i : Fin D => (i, k₁) := by
      ext ⟨i, k⟩
      simp [U, eq_comm]
    rw [this, ← Set.image_univ, Function.Injective.encard_image (fun a b h => congrArg Prod.fst h)]
    simp
  have h3 : (D : ℕ∞) ≤ B.encard := by
    rw [h2] at h1
    exact (ENat.add_le_add_iff_right (Set.toFinite _).encard_lt_top.ne).1 h1
  obtain ⟨B', hB'B, hB'⟩ := Set.exists_subset_encard_eq h3
  have hfin : B'.Finite := Set.finite_of_encard_eq_coe hB'
  have : Finite B' := hfin
  have hlift : ∀ x : B', ∃ g, ψ g = x := fun x => hB.subset (hB'B x.2)
  choose b hb using hlift
  refine injective_of_indep_image b ?_ ψ ?_
  · rw [← Set.cast_ncard hfin, Set.ncard, hB']
    simpa using hΓ
  · have : ψ ∘ b = ((↑) : B' → L) := funext hb
    rw [this]
    exact hB.indep.subset hB'B

theorem val_ne_zero {K Φ Ω L : Type} [Field K] [CommRing Φ] [Algebra K Φ] [Field Ω] [Algebra K Ω] [Field L]
    [Algebra K L] {D N : ℕ} (htr : Algebra.trdeg K Ω ≤ D) (g : Φ →ₐ[K] Ω) (S : ℕ → Φ → Prop) (val : ℕ → Φ → L)
    (hadd : ∀ k F G, S k F → S k G → S k (F + G) ∧ val k (F + G) = val k F + val k G)
    (hsmul : ∀ k (c : K) F, S k F → S k (c • F) ∧ val k (c • F) = algebraMap K L c * val k F)
    (hmul : ∀ k l F G, S k F → S l G → S (k + l) (F * G) ∧ val (k + l) (F * G) = val k F * val l G)
    (hker : ∀ k F, S k F → g F = 0 → val k F = 0)
    (w : Fin N → Φ) (hw : ∀ k, S 1 (w k)) (t : Fin (D + 1) × Fin N → L) (ht : AlgebraicIndependent K t)
    (h0 : ∑ k, t (0, k) * val 1 (w k) = 1) (hrel : ∀ i : Fin D, ∑ k, t (i.succ, k) * val 1 (w k) = 0)
    (k : ℕ) (F : Φ) (hF : S k F) (hg : g F ≠ 0) : val k F ≠ 0 := by
  obtain ⟨k₁, hu⟩ : ∃ k₁, val 1 (w k₁) ≠ 0 := by
    by_contra hc
    push Not at hc
    simp [hc] at h0
  have hv : g (w k₁) ≠ 0 := fun h => hu (hker _ _ (hw k₁) h)
  set u := val 1 (w k₁) with hudef
  set v := g (w k₁) with hvdef
  have hpow : ∀ m a G, S a G → S (a + m) (G * w k₁ ^ m) ∧ val (a + m) (G * w k₁ ^ m) = val a G * u ^ m := by
    intro m a G hG
    induction m with
    | zero => simpa using hG
    | succ m ih =>
      have h := hmul _ _ _ _ ih.1 (hw k₁)
      rw [ih.2, mul_assoc, ← pow_succ, mul_assoc, ← pow_succ, add_assoc] at h
      exact h
  let Γ : Subalgebra K (Ω × L) :=
    { carrier := {z | ∃ a G, S a G ∧ z = (g G / v ^ a, val a G / u ^ a)}
      mul_mem' := by
        rintro _ _ ⟨a, G, hG, rfl⟩ ⟨b, H, hH, rfl⟩
        obtain ⟨h1, h2⟩ := hmul _ _ _ _ hG hH
        refine ⟨a + b, G * H, h1, ?_⟩
        rw [h2, map_mul, Prod.mk_mul_mk, div_mul_div_comm, div_mul_div_comm, pow_add, pow_add]
      add_mem' := by
        rintro _ _ ⟨a, G, hG, rfl⟩ ⟨b, H, hH, rfl⟩
        obtain ⟨h1, h2⟩ := hpow b a G hG
        obtain ⟨h3, h4⟩ := hpow a b H hH
        rw [add_comm b a] at h3 h4
        obtain ⟨h5, h6⟩ := hadd _ _ _ h1 h3
        refine ⟨a + b, _, h5, ?_⟩
        rw [h6, h2, h4, Prod.mk_add_mk]
        simp only [map_add, map_mul, map_pow, ← hvdef, pow_add]
        congr 1 <;> field_simp
      algebraMap_mem' := by
        intro c
        obtain ⟨h1, h2⟩ := hsmul 1 c _ (hw k₁)
        refine ⟨1, _, h1, ?_⟩
        rw [h2, map_smul, Algebra.smul_def, pow_one, pow_one, mul_div_cancel_right₀ _ hv,
          mul_div_cancel_right₀ _ hu]
        rfl }
  let p : Γ →ₐ[K] Ω := (AlgHom.fst K Ω L).comp Γ.val
  let ψ : Γ →ₐ[K] L := (AlgHom.snd K Ω L).comp Γ.val
  have hp : Function.Injective p := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨_, a, G, hG, rfl⟩ h
    have h' : g G / v ^ a = 0 := h
    have hG0 : g G = 0 := by simpa [hv] using h'
    apply Subtype.ext
    show (g G / v ^ a, val a G / u ^ a) = 0
    rw [hG0, hker _ _ hG hG0, zero_div, zero_div]
    rfl
  have : IsDomain Γ := hp.isDomain p.toRingHom
  have hinj : Function.Injective ψ := by
    refine injective_of_relations ((trdeg_le_of_injective p hp).trans htr) ψ (fun q => t (q.1.succ, q.2))
      (ht.comp (fun q : Fin D × Fin N => (q.1.succ, q.2)) ?_)
      (fun k => ⟨_, 1, w k, hw k, rfl⟩) k₁ ?_ ?_
    · rintro ⟨a, b⟩ ⟨c, d⟩ h
      simpa using h
    · show u / u ^ 1 = 1
      rw [pow_one, div_self hu]
    · intro i
      show ∑ k, t (i.succ, k) * (val 1 (w k) / u ^ 1) = 0
      simp only [← mul_div_assoc]
      rw [← Finset.sum_div, hrel, zero_div]
  intro hz
  have h1 : (⟨_, k, F, hF, rfl⟩ : Γ) = 0 := hinj (by
    rw [map_zero]
    show val k F / u ^ k = 0
    rw [hz, zero_div])
  have h2 : g F / v ^ k = 0 := congrArg (fun z : Γ => (z : Ω × L).1) h1
  exact hg (by simpa [hv] using h2)

theorem exists_field_point {A : Type} [CommRing A] (𝔮 : Ideal A) (h : 𝔮.IsPrime) :
    ∃ (L : Type) (_ : Field L) (ρ : A →+* L), ∀ x ∈ 𝔮, ρ x = 0 :=
  ⟨FractionRing (A ⧸ 𝔮), inferInstance, (algebraMap (A ⧸ 𝔮) _).comp (Ideal.Quotient.mk 𝔮), fun x hx => by
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]⟩

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ)

set_option maxHeartbeats 1000000 in

theorem variables_indep :
    AlgebraicIndependent (X.Kl la) (fun p : Idx D j N => algebraMap (Op X la N) (Kp X la N) (Tv X la N p)) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom (X.Ol la) (Pol X la N) (Op X la N)) :=
    IsLocalization.injective (Op X la N) (Ideal.primeCompl_le_nonZeroDivisors (gI X la N))
  have h0 := (MvPolynomial.algebraicIndependent_X (Idx D j N) (X.Ol la)).map' hinj
  have h1 := h0.map' (f := IsScalarTower.toAlgHom (X.Ol la) (Op X la N) (Kp X la N))
    (IsFractionRing.injective (Op X la N) (Kp X la N))
  have : Algebra.IsAlgebraic (X.Ol la) (X.Kl la) := IsLocalization.isAlgebraic _ (nonZeroDivisors (X.Ol la))
  have h2 := (Algebra.IsAlgebraic.algebraicIndependent_iff (X.Ol la) (X.Kl la)).mp h1
  have hfun : (fun p : Idx D j N => algebraMap (Op X la N) (Kp X la N) (Tv X la N p)) =
      ⇑(IsScalarTower.toAlgHom (X.Ol la) (Op X la N) (Kp X la N)) ∘
        (⇑(IsScalarTower.toAlgHom (X.Ol la) (Pol X la N) (Op X la N)) ∘ MvPolynomial.X) := by
    funext p
    rw [Function.comp_apply, Function.comp_apply, IsScalarTower.toAlgHom_apply, IsScalarTower.toAlgHom_apply, Tv]
  rw [hfun]
  exact h2

variable {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem mem_one (k : Fin N) : emb X la N (X.inc wL (w k)) ∈ Vw X la N (addL (wt0 D j) wL 1) := by
  rw [add_zero_weight_one_eq]; exact emb_mem_Vw X la N wL (w k)

theorem sfr_eq_sum (i : Fin (WeightFamilies.dimY D j + 1)) :
    sfr X la w i = ∑ k, algebraMap (Kp X la N) ↥(Frac0 X la w) (algebraMap (Op X la N) (Kp X la N) (Tv X la N (i, k))) *
      CurveLoc.fr0 X la N w 1 (X.inc wL (w k)) (mem_one X la N w k) := by
  apply Subtype.ext
  rw [coe_sfr, Formalism.MainNotions.Gaps.EtaleWeightGaps.sec, map_sum, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, ← Algebra.smul_def]
  rfl

theorem sfr_zero : sfr X la w 0 = 1 := by
  apply Subtype.ext
  rw [coe_sfr, frac_apply, pow_one, section_mul_inverse_eq_one]
  rfl

set_option maxHeartbeats 1000000 in

theorem frobenius_zero_not_mem_of_trdeg {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)
    (htr : Algebra.trdeg B.KO Ω ≤ WeightFamilies.dimY D j) (𝔮 : Ideal ↥(Frac0 X la w)) (h𝔮 : 𝔮.IsPrime) (hJ : Jid X la w ≤ 𝔮)
    (hK : RingHom.ker (phiZ X la N Ω gF w) ≤ 𝔮) (k : ℕ) (F : X.Forms)
    (hF : emb X la N F ∈ Vw X la N (addL (wt0 D j) wL k)) (hg : gF F ≠ 0) : CurveLoc.fr0 X la N w k F hF ∉ 𝔮 := by
  classical
  intro hmem
  obtain ⟨L, _, ρ, hρ⟩ := exists_field_point 𝔮 h𝔮
  let σ : Kp X la N →+* L := ρ.comp (algebraMap (Kp X la N) ↥(Frac0 X la w))
  let τ : B.KO →+* Kp X la N := (algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la))
  have ht : letI : Algebra B.KO L := (σ.comp τ).toAlgebra
      AlgebraicIndependent B.KO
        (fun p : Idx D j N => σ (algebraMap (Op X la N) (Kp X la N) (Tv X la N p))) := by
    letI : Algebra B.KO (Kp X la N) := τ.toAlgebra
    letI : Algebra B.KO L := (σ.comp τ).toAlgebra
    have : IsScalarTower B.KO (X.Kl la) (Kp X la N) := IsScalarTower.of_algebraMap_eq' rfl
    have h1 := (variables_indep X la N).restrictScalars (R := B.KO) (algebraMap B.KO (X.Kl la)).injective
    exact h1.map' (f := ({ toRingHom := σ, commutes' := fun _ => rfl } : Kp X la N →ₐ[B.KO] L)) σ.injective
  letI : Algebra B.KO L := (σ.comp τ).toAlgebra
  let S : ℕ → X.Forms → Prop := fun k F => emb X la N F ∈ Vw X la N (addL (wt0 D j) wL k)
  let val : ℕ → X.Forms → L := fun k F => if h : S k F then ρ (CurveLoc.fr0 X la N w k F h) else 0
  have hval : ∀ k F (h : S k F), val k F = ρ (CurveLoc.fr0 X la N w k F h) := fun k F h => dif_pos h
  refine val_ne_zero htr gF S val ?_ ?_ ?_ ?_ (fun k => X.inc wL (w k)) (mem_one X la N w) _ ht ?_ ?_ k F hF hg ?_
  · intro k F G h1 h2
    have h3 : S k (F + G) := by
      show emb X la N (F + G) ∈ _
      rw [map_add]; exact Submodule.add_mem _ h1 h2
    refine ⟨h3, ?_⟩
    rw [hval _ _ h1, hval _ _ h2, hval _ _ h3, ← map_add]
    congr 1
    apply Subtype.ext
    show frac X la w k (emb X la N (F + G)) = frac X la w k (emb X la N F) + frac X la w k (emb X la N G)
    rw [map_add, map_add]
  · intro k c F h1
    have e : emb X la N (c • F) = τ c • emb X la N F := by
      rw [emb_smul, ← algebraMap_smul (Kp X la N)]
      rfl
    have h3 : S k (c • F) := by
      show emb X la N (c • F) ∈ _
      rw [e]; exact Submodule.smul_mem _ _ h1
    refine ⟨h3, ?_⟩
    rw [hval _ _ h1, hval _ _ h3]
    show _ = ρ (algebraMap (Kp X la N) ↥(Frac0 X la w) (τ c)) * _
    rw [← map_mul, ← Algebra.smul_def]
    congr 1
    apply Subtype.ext
    show frac X la w k (emb X la N (c • F)) = τ c • frac X la w k (emb X la N F)
    rw [e, map_smul]
  · intro k l F G h1 h2
    have h3 : S (k + l) (F * G) := by
      have h := mul_mem_Vw X la N h1 h2
      rw [wadd_addL_addL, zero_weight_add, ← map_mul] at h
      exact h
    refine ⟨h3, ?_⟩
    rw [hval _ _ h1, hval _ _ h2, hval _ _ h3, ← map_mul]
    congr 1
    apply Subtype.ext
    show frac X la w (k + l) (emb X la N (F * G)) = frac X la w k (emb X la N F) * frac X la w l (emb X la N G)
    rw [frac_mul, map_mul]
  · intro k F h1 h2
    rw [hval _ _ h1]
    refine hρ _ (hK ?_)
    rw [RingHom.mem_ker, CurveLoc.phiZ_fraction_base, h2, map_zero, zero_mul]
  · have h := congrArg ρ (sfr_eq_sum X la N w 0)
    rw [sfr_zero, map_one, map_sum] at h
    rw [h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hval _ _ (mem_one X la N w k)]
    rfl
  · intro i
    have h := congrArg ρ (sfr_eq_sum X la N w i.succ)
    rw [hρ _ (hJ (sfr_succ_mem_Jid X la w i)), map_sum] at h
    rw [h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hval _ _ (mem_one X la N w k)]
    rfl
  · rw [hval _ _ hF]
    exact hρ _ hmem

set_option maxHeartbeats 1000000 in

theorem countQAt_of_trdeg_le {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)
    (htr : Algebra.trdeg B.KO Ω ≤ WeightFamilies.dimY D j) : CurveLoc.CountQAt X la N w gF := by
  by_cases h0 : ∃ a, gF (X.inc wL (w a)) ≠ 0
  · obtain ⟨a, ha⟩ := h0
    exact CurveLoc.countQAt_of X la N w gF (fun i => gF (X.inc wL (w i))) (fun _ => rfl)
      ⟨a, ha, (trdeg_le_of_injective (IntermediateField.val _) Subtype.val_injective).trans htr⟩
  · intro 𝔮 h𝔮 _ hK
    exfalso
    push Not at h0
    refine h𝔮.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← sfr_zero X la N w, sfr_eq_sum X la N w 0]
    refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hK ?_)
    rw [RingHom.mem_ker, CurveLoc.phiZ_fraction_base, h0, map_zero, zero_mul]

end Rec

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem frobenius_zero_not_mem_prime (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j)
    (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (N : ℕ) {wL : WeightFamilies.Wt D j}
    (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Z : Comp (T.Q.Xo j) T.Q.c)
    (𝔮 : Ideal ↥(Frac0 (recPlus h j hj) la w)) (h𝔮 : 𝔮.IsPrime) (hJ : Jid (recPlus h j hj) la w ≤ 𝔮)
    (hK : RingHom.ker (phiZ (recPlus h j hj) la N (Om Z) (formsEvR j hG hT Z) w) ≤ 𝔮) (k : ℕ)
    (F : (recPlus h j hj).Forms)
    (hF : emb (recPlus h j hj) la N F ∈ Vw (recPlus h j hj) la N (addL (wt0 D j) wL k))
    (hg : formsEvR j hG hT Z F ≠ 0) : CurveLoc.fr0 (recPlus h j hj) la N w k F hF ∉ 𝔮 :=
  frobenius_zero_not_mem_of_trdeg (recPlus h j hj) la N w (formsEvR j hG hT Z)
    ((GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q h.pins.2.2.2 j hj).2 Z).le 𝔮 h𝔮 hJ hK k F hF hg

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem countQAtSt : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG), CountQAtSt h j hj hG hT := by
  intro D T h j hj hG hT ka wL wF G S g0 la _ Z
  exact countQAt_of_trdeg_le (recPlus h j hj) la G.N G.w (formsEvR j hG hT Z)
    ((GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q h.pins.2.2.2 j hj).2 Z).le

end GlobalTheory.SecCount
