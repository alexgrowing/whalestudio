import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropFiltSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropFiltKernelSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropFiltStepSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropFiltFiniteSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationExists
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSubvarDrop
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.QuotGraded
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace SectionCount.Drop.Filt

section Ideals

variable {S : Type u} [CommRing S] {N : ℕ}

theorem homogeneousComponent_mul_mem_span {g : Poly S N} {e : ℕ} (hg : g.IsHomogeneous e)
    (r : Poly S N) (d : ℕ) : homogeneousComponent d (r * g) ∈ Ideal.span {g} := by
  classical
  rw [← sum_homogeneousComponent r, Finset.sum_mul, map_sum]
  refine Ideal.sum_mem _ fun m _ => ?_
  rw [homogeneousComponent_of_mem
    ((mem_homogeneousSubmodule _ _).mpr ((homogeneousComponent_isHomogeneous m r).mul hg))]
  split_ifs
  · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)
  · exact zero_mem _

theorem hom_span {T : Set (Poly S N)} (hT : ∀ g ∈ T, ∃ e, g.IsHomogeneous e) :
    ∀ f ∈ Ideal.span T, ∀ d : ℕ, homogeneousComponent d f ∈ Ideal.span T := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    intro d
    obtain ⟨e, he⟩ := hT g hg
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr he)]
    split_ifs
    · exact Ideal.subset_span hg
    · exact zero_mem _
  | zero => intro d; simp
  | add a b _ _ ha hb => intro d; rw [map_add]; exact add_mem (ha d) (hb d)
  | smul r a _ ha =>
    intro d
    classical
    change homogeneousComponent d (r * a) ∈ _
    rw [← sum_homogeneousComponent a, Finset.mul_sum, map_sum]
    refine Ideal.sum_mem _ fun m _ => ?_
    exact (Ideal.span_singleton_le_iff_mem _).mpr (ha m)
      (homogeneousComponent_mul_mem_span (homogeneousComponent_isHomogeneous m a) r d)

theorem hom_sup {I I' : Ideal (Poly S N)} (h : ∀ f ∈ I, ∀ d : ℕ, homogeneousComponent d f ∈ I)
    (h' : ∀ f ∈ I', ∀ d : ℕ, homogeneousComponent d f ∈ I') :
    ∀ f ∈ I ⊔ I', ∀ d : ℕ, homogeneousComponent d f ∈ I ⊔ I' := by
  intro f hf d
  obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add]
  exact add_mem (Ideal.mem_sup_left (h a ha d)) (Ideal.mem_sup_right (h' a' ha' d))

end Ideals

section Charts

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem mem_secs_iff {F : SubSystem S x Ω} {y : Ω} : y ∈ F.secs ↔ ∀ I, y ∈ F.sub I := by
  simp [SubSystem.secs, Submodule.mem_iInf]

theorem mem_chartRing_of_mem_idealMod {J : Ideal (Poly S N)} {I : Chart x} {q : Ω}
    (hq : q ∈ idealMod J I) : q ∈ chartRing S x I := by
  refine Submodule.span_induction (p := fun z _ => z ∈ chartRing S x I) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨f, s, e, _, hs, hf, hse, rfl⟩
    exact ⟨f, s, e, hs, hf, hse, rfl⟩
  · exact zero_mem _
  · intro a b _ _ ha hb; exact add_mem ha hb
  · intro a z _ hz
    rw [chartRing_smul_def]
    exact mul_mem a.2 hz

theorem twist_idealSys_sub_le (F : SubSystem S x Ω) (J : Ideal (Poly S N)) (I : Chart x) :
    (F.twist (idealSys x J)).sub I ≤ F.sub I := by
  rw [SubSystem.twist_sub_eq_mul_of_line]
  refine Submodule.mul_le.mpr fun q hq y hy => ?_
  have h := (F.sub I).smul_mem (⟨q, mem_chartRing_of_mem_idealMod hq⟩ : chartRing S x I) hy
  rwa [chartRing_smul_def] at h

theorem secs_twist_idealSys_le (F : SubSystem S x Ω) (J : Ideal (Poly S N)) :
    (F.twist (idealSys x J)).secs ≤ F.secs := fun _ hy =>
  mem_secs_iff.mpr fun I => twist_idealSys_sub_le F J I (mem_secs_iff.mp hy I)

theorem secs_le_twist_idealSys_top (F : SubSystem S x Ω) :
    F.secs ≤ (F.twist (idealSys x (⊤ : Ideal (Poly S N)))).secs := by
  intro y hy
  refine mem_secs_iff.mpr fun I => ?_
  rw [SubSystem.twist_sub_eq_mul_of_line]
  have h1 : (1 : Ω) ∈ (idealSys x (⊤ : Ideal (Poly S N))).sub I :=
    Submodule.subset_span ⟨1, 1, 0, Submodule.mem_top, one_mem _, isHomogeneous_one _ _,
      isHomogeneous_one _ _, by simp⟩
  simpa using Submodule.mul_mem_mul h1 (mem_secs_iff.mp hy I)

theorem idealMod_primeOf (I : Chart x) : idealMod (primeOf (S := S) x) I = ⊥ := by
  refine Submodule.span_eq_bot.mpr ?_
  rintro _ ⟨f, s, e, hf, _, hfe, _, rfl⟩
  rw [(mem_primeOf_of_isHomogeneous x hfe).mp hf, zero_div]

end Charts

section FieldCharts

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem finrank_quotH_irrelevant (F : SubSystem k x Ω) (pp : Ideal (Poly k N))
    (hpp : ∀ i, (X i : Poly k N) ∈ pp) :
    Module.finrank k (SubSystem.quotH F (F.twist (idealSys x pp)) 0) = 0 := by
  have hsub : ∀ I : Chart x,
      Subsingleton (F.sub I ⧸ SubSystem.quotSub F (F.twist (idealSys x pp)) I) := by
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Submodule.Quotient.eq]
    change ((a - b : F.sub I) : Ω) ∈ (F.twist (idealSys x pp)).sub I
    rw [SubSystem.twist_sub_eq_mul_of_line]
    have h1 : (1 : Ω) ∈ (idealSys x pp).sub I :=
      Submodule.subset_span ⟨X i, X i, 1, hpp i, X_mem_monos hi, isHomogeneous_X _ _,
        isHomogeneous_X _ _, by rw [aeval_X, div_self hxi]⟩
    simpa using Submodule.mul_mem_mul h1 (a - b).2
  have hC : Subsingleton (Cech.Cochain (fun I : Chart x =>
      F.sub I ⧸ SubSystem.quotSub F (F.twist (idealSys x pp)) I) 0) := by
    unfold Cech.Cochain
    exact ⟨fun a b => funext fun I => (hsub I.1).elim _ _⟩
  have hH : Subsingleton (SubSystem.quotH F (F.twist (idealSys x pp)) 0) := by
    unfold SubSystem.quotH Cech.H
    infer_instance
  exact Module.finrank_zero_of_subsingleton

end FieldCharts

theorem finrank_le_of_step {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] [Module.Finite K W] {V₁ V₂ : Submodule K V} [FiniteDimensional K V₁]
    [FiniteDimensional K V₂] (φ : V₂ →ₗ[K] W) (hker : ∀ s, φ s = 0 → (s : V) ∈ V₁) :
    Module.finrank K V₂ ≤ Module.finrank K V₁ + Module.finrank K W := by
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 : Module.finrank K (LinearMap.range φ) ≤ Module.finrank K W := Submodule.finrank_le _
  have h3 : Module.finrank K (LinearMap.ker φ) ≤ Module.finrank K V₁ := by
    refine LinearMap.finrank_le_finrank_of_injective
      (f := LinearMap.codRestrict V₁ (V₂.subtype.comp (LinearMap.ker φ).subtype)
        fun s => hker s.1 s.2) ?_
    intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h)
  omega

end SectionCount.Drop.Filt

open SectionCount.Drop.Filt in

theorem SectionCount.Drop.Filt.proof (hK : SectionCount.Drop.Filt.Kernel.Statement.{u, w})
    (hS : SectionCount.Drop.Filt.Step.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Finite.Statement.{u, w}) :
    SectionCount.Drop.Filt.Statement.{u, w} := by
  classical
  intro k _ Ω _ _ N x d Nb b hZ hb

  obtain ⟨j, hj⟩ := hZ.relevant
  have hxj : x j ≠ 0 := by
    intro h; apply hj
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j), aeval_X, h]
  have hβ : x j ^ b ≠ 0 := pow_ne_zero b hxj
  set J := primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) (x j ^ b) with hJdef
  have hXJ : (X j ^ b : Poly k N) ∈ J := Ideal.mem_sup_right (Ideal.subset_span
    ⟨b, isHomogeneous_X_pow j b, fun I δ hδ => ⟨δ, hδ, by simp [aeval_X]⟩⟩)
  have hXnot : (X j ^ b : Poly k N) ∉ primeOf (S := k) x := by
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X_pow j b)]; simpa using hβ
  have hJhom : ∀ f ∈ J, ∀ d : ℕ, homogeneousComponent d f ∈ J :=
    hom_sup (fun f hf d => homogeneousComponent_mem_primeOf x hf d)
      (hom_span fun g ⟨c, hc, _⟩ => ⟨c, hc⟩)

  have hkill : ∀ p ∈ primeOf (S := k) x, ∀ m : Poly k N ⧸ J, p • m = 0 := by
    intro p hp m
    obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
    change Ideal.Quotient.mk J (p * m) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (J.mul_mem_right m (Ideal.mem_sup_left hp))
  obtain ⟨⟨Fl⟩, hcount⟩ := PrimeFiltration.Exists.proof.{u, u, w} k Ω N x (Poly k N ⧸ J)
    (quotGraded J hJhom) (finite_quot J) hkill
  rw [Ideal.annihilator_quotient] at hcount
  have hann : ∀ l, J ≤ Fl.prime l := fun l => by
    have := Fl.ann_le l; rwa [Ideal.annihilator_quotient] at this

  have hlift : ∀ l : Fin Fl.n, ∃ (g : Poly k N) (e : ℕ), g.IsHomogeneous e ∧
      Ideal.Quotient.mk J g = Fl.gen l := by
    intro l
    obtain ⟨g, hg, hgm⟩ := mem_quotGraded_piece.mp (Fl.gen_mem l)
    by_cases h0 : 0 ≤ Fl.deg l
    · refine ⟨g, (Fl.deg l).toNat, isHomogeneous_of_isWeightedHomogeneous_one ?_, hgm⟩
      rwa [Int.toNat_of_nonneg h0]
    · refine ⟨0, 0, isHomogeneous_zero _ _ _, ?_⟩
      have hg0 : g = 0 := by
        ext m
        by_contra hne
        have h1 := hg hne
        rw [weight_one_int] at h1
        omega
      rw [← hgm, hg0]
  choose g eK hgH hgm using hlift

  let Jk : Fin (Fl.n + 1) → Ideal (Poly k N) := fun l => (Fl.step l).comap J.mkQ
  have hJ0 : Jk 0 = J := by
    simp only [Jk, Fl.step_zero, Submodule.comap_bot, Submodule.ker_mkQ]
  have hJlast : Jk (Fin.last _) = ⊤ := by
    simp only [Jk, Fl.step_last, Submodule.comap_top]
  have hmkQ : ∀ (c : Poly k N) (l : Fin Fl.n), J.mkQ (c * g l) = c • Fl.gen l := by
    intro c l
    rw [← hgm l]
    rfl
  have hJsucc : ∀ l : Fin Fl.n, Jk l.succ = Jk l.castSucc ⊔ Ideal.span {g l} := by
    intro l
    ext f
    simp only [Jk, Fl.step_succ, Submodule.mem_comap]
    constructor
    · intro hf
      obtain ⟨a, ha, y, hy, hay⟩ := Submodule.mem_sup.mp hf
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      have h1 : f - c * g l ∈ (Fl.step l.castSucc).comap J.mkQ := by
        rw [Submodule.mem_comap, map_sub, hmkQ, ← hay, add_sub_cancel_right]
        exact ha
      have h2 := Submodule.add_mem_sup h1 (Ideal.mul_mem_left _ c (Ideal.mem_span_singleton_self (g l)))
      rwa [sub_add_cancel] at h2
    · intro hf
      obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      rw [map_add, hmkQ]
      exact Submodule.add_mem_sup ha (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hJkp : ∀ (l : Fin Fl.n) (f : Poly k N), f ∈ Fl.prime l ↔ f * g l ∈ Jk l.castSucc := by
    intro l f
    rw [Fl.mem_prime, ← hgm l]
    exact Iff.rfl
  have hJk_ge : ∀ l, J ≤ Jk l := fun l f hf => by
    simp only [Jk, Submodule.mem_comap, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero J).mpr hf, zero_mem]
  have hJk_hom : ∀ l, ∀ f ∈ Jk l, ∀ d : ℕ, homogeneousComponent d f ∈ Jk l := by
    intro l
    induction l using Fin.induction with
    | zero => rw [hJ0]; exact hJhom
    | succ l ih =>
      rw [hJsucc l]
      exact hom_sup ih (hom_span fun g' hg' => ⟨eK l, by rw [Set.mem_singleton_iff.mp hg']; exact hgH l⟩)

  have hprimeZ : ∀ l, primeOf (S := k) x ≤ Fl.prime l := fun l => le_sup_left.trans (hann l)
  have hsv : ∀ l, (∃ i, (X i : Poly k N) ∉ Fl.prime l) → ∃ e ≤ d, IsSubvar x (Fl.prime l) e :=
    fun l hl => SubvarDrop.proof k Ω N x d (Fl.prime l) hZ (Fl.isPrime l) (Fl.isHomogeneous l)
      (hprimeZ l) hl ⟨X j ^ b, hann l hXJ, hXnot⟩
  choose! eS heS heSv using hsv
  let kept : Finset (Fin Fl.n) := Finset.univ.filter fun l => ∃ i, (X i : Poly k N) ∉ Fl.prime l
  let σ : Fin kept.card ≃ kept := kept.equivFin.symm
  let emb : Fin kept.card → Fin Fl.n := fun a => (σ a).1
  have hemb : ∀ a, ∃ i, (X i : Poly k N) ∉ Fl.prime (emb a) := fun a =>
    (Finset.mem_filter.mp (σ a).2).2

  have hdim_inj : ∀ {q : Ideal (Poly k N)} {e e' : ℕ}, IsSubvar x q e → IsSubvar x q e' → e = e' := by
    intro q e e' h h'
    have h2 := h.dim.symm.trans h'.dim
    rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, WithBot.coe_inj, Nat.cast_inj] at h2
    omega

  have hmin : ∀ q : Ideal (Poly k N), J ≤ q → IsSubvar x q d → q ∈ J.minimalPrimes := by
    intro q hJq hq
    have := hq.isPrime
    refine ⟨⟨hq.isPrime, hJq⟩, fun q' ⟨hq'p, hJq'⟩ hq'q => ?_⟩
    by_contra hne
    obtain ⟨f, hfq, hfq'⟩ := Set.not_subset.mp hne
    have := hq'p
    have hle : primeOf (S := k) x ≤ q' := le_sup_left.trans hJq'
    have h1 : ringKrullDim (Poly k N ⧸ q') + 1 ≤ ringKrullDim (Poly k N ⧸ primeOf (S := k) x) := by
      refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
        (Ideal.Quotient.factor_surjective hle) (r := Ideal.Quotient.mk _ (X j ^ b)) ?_ ?_
      · apply mem_nonZeroDivisors_of_ne_zero
        rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact hJq' hXJ
    have h2 : ringKrullDim (Poly k N ⧸ q) + 1 ≤ ringKrullDim (Poly k N ⧸ q') := by
      refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hq'q)
        (Ideal.Quotient.factor_surjective hq'q) (r := Ideal.Quotient.mk _ f) ?_ ?_
      · apply mem_nonZeroDivisors_of_ne_zero
        rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact hfq
    rw [hq.dim] at h2
    rw [hZ.dim] at h1
    have h3 := (add_le_add h2 (le_refl 1)).trans h1
    have h4 : ((d + 1 + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + 1 + 1 : ℕ) : WithBot ℕ∞) := by
      simpa only [Nat.cast_succ] using h3
    rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, WithBot.coe_le_coe, Nat.cast_le] at h4
    omega

  have hc1 : ∀ qq : Ideal (Poly k N),
      (Finset.univ.filter fun a : Fin kept.card => eS (emb a) = d ∧ Fl.prime (emb a) = qq).card =
        (kept.filter fun l => eS l = d ∧ Fl.prime l = qq).card := by
    intro qq
    refine Finset.card_bij (fun a _ => emb a) ?_ ?_ ?_
    · intro a ha
      exact Finset.mem_filter.mpr ⟨(σ a).2, (Finset.mem_filter.mp ha).2⟩
    · intro a _ a' _ h
      exact σ.injective (Subtype.ext h)
    · intro l hl
      refine ⟨σ.symm ⟨l, (Finset.mem_filter.mp hl).1⟩, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simp only [emb, Equiv.apply_symm_apply]
        exact (Finset.mem_filter.mp hl).2
      · simp only [emb, Equiv.apply_symm_apply]

  have hβsecs : x j ^ b ∈ (twistSys k x (b : ℤ)).secs := by
    refine mem_secs_iff.mpr fun I => ?_
    exact Submodule.subset_span ⟨X j ^ b, 1, 0, b, one_mem _, isHomogeneous_X_pow j b,
      isHomogeneous_one _ _, by simp, by simp [aeval_X]⟩
  have hβnz : x j ^ b ∉ ((twistSys k x (b : ℤ)).twist (idealSys x (primeOf (S := k) x))).sub
      (singleChart hxj) := by
    rw [SubSystem.twist_sub_eq_mul_of_line]
    change x j ^ b ∉ idealMod (primeOf (S := k) x) (singleChart hxj) * _
    rw [idealMod_primeOf, Submodule.bot_mul, Submodule.mem_bot]
    exact hβ
  refine ⟨x j ^ b, hβsecs, ⟨singleChart hxj, hβnz⟩, kept.card, fun a => Fl.prime (emb a),
    fun a => eS (emb a), fun a => -((eK (emb a) : ℕ) : ℤ),
    fun a => ⟨heSv _ (hemb a), heS _ (hemb a), hann _⟩, fun qq => ?_, fun n i => ?_⟩
  ·
    by_cases h : qq ∈ J.minimalPrimes ∧ IsSubvar x qq d
    · rw [dif_pos h, hc1 qq]
      have hset : kept.filter (fun l => eS l = d ∧ Fl.prime l = qq) =
          Finset.univ.filter (fun l => Fl.prime l = qq) := by
        ext l
        simp only [kept, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, _, h2⟩; exact h2
        · intro h2
          have hrel : ∃ i, (X i : Poly k N) ∉ Fl.prime l := h2 ▸ h.2.relevant
          exact ⟨hrel, hdim_inj (heSv l hrel) (h2 ▸ h.2), h2⟩
      rw [hset]
      have : qq.IsPrime := h.1.1.1
      have hq := hcount Fl qq h.1
      unfold cutMult
      rw [← hq, ENat.toNat_natCast]
    · rw [dif_neg h, hc1 qq, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro l hl ⟨hed, hpq⟩
      have hrel := (Finset.mem_filter.mp hl).2
      have hsub : IsSubvar x qq d := hpq ▸ hed ▸ heSv l hrel
      exact h ⟨hmin qq (hpq ▸ hann l) hsub, hsub⟩
  ·
    set Fs := twistMul Nb.toSubSystem n (-((i : ℤ) * b)) with hFs
    obtain ⟨L, hL⟩ := exists_lineBundle_twistMul Nb n (-((i : ℤ) * b))
    have hFB : Fs.twist (twistSys k x (-(b : ℤ))) =
        twistMul Nb.toSubSystem n (-(((i + 1 : ℕ) : ℤ) * b)) := by
      rw [hFs, twistMul, twistMul, SubSystem.twist_assoc, twistSys_twist_eq_add]
      congr 2
      push_cast
      ring
    rw [← hFB]
    let T : Fin Fl.n → ℕ := fun l => Module.finrank k (SubSystem.quotH
      (Fs.twist (twistSys k x (-((eK l : ℕ) : ℤ))))
      ((Fs.twist (twistSys k x (-((eK l : ℕ) : ℤ)))).twist (idealSys x (Fl.prime l))) 0)
    have hsum : ∑ l : Fin Fl.n, T l = ∑ a : Fin kept.card, T (emb a) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun l => ∃ i, (X i : Poly k N) ∉ Fl.prime l)]
      rw [Finset.sum_eq_zero (s := Finset.univ.filter fun l => ¬ ∃ i, (X i : Poly k N) ∉ Fl.prime l),
        add_zero]
      · rw [← Finset.sum_coe_sort]
        exact (Equiv.sum_comp σ (fun l => T l.1)).symm
      · intro l hl
        have hirr := (Finset.mem_filter.mp hl).2
        simp only [not_exists, not_not] at hirr
        exact finrank_quotH_irrelevant _ _ hirr
    have hR : (∑ a : Fin kept.card, ((T (emb a) : ℕ) : ℤ)) = ((∑ l, T l : ℕ) : ℤ) := by
      rw [hsum, Nat.cast_sum]
    suffices hmain : (Module.finrank k Fs.secs : ℤ) -
        Module.finrank k (Fs.twist (twistSys k x (-(b : ℤ)))).secs ≤ ((∑ l, T l : ℕ) : ℤ) by
      rw [← hR] at hmain
      exact hmain
    by_cases hfd : Module.Finite k Fs.secs
    swap
    · rw [Module.finrank_of_not_finite hfd]
      omega

    let V : Fin (Fl.n + 1) → Submodule k Ω := fun l => (Fs.twist (idealSys x (Jk l))).secs
    have hVfin : ∀ l, FiniteDimensional k (V l) := fun l =>
      Submodule.finiteDimensional_of_le (secs_twist_idealSys_le Fs (Jk l))
    have hstep : ∀ l : Fin Fl.n,
        Module.finrank k (V l.succ) ≤ Module.finrank k (V l.castSucc) + T l := by
      intro l
      have hS' := hS k Ω N x L (Jk l.castSucc) (Fl.prime l) (g l) (eK l) (hJk_hom _)
        (le_sup_left.trans (hJk_ge _)) (hgH l) (hJkp l)
      have hF' := hF k Ω N x L (Fl.prime l) (-((eK l : ℕ) : ℤ)) (Fl.isPrime l) (Fl.isHomogeneous l)
        (hprimeZ l)
      rw [← hJsucc l, hL] at hS'
      rw [hL] at hF'
      obtain ⟨φ, hφ⟩ := hS'
      have := hVfin l.succ
      have := hVfin l.castSucc
      exact finrank_le_of_step φ hφ
    have htel : ∀ r (hr : r ≤ Fl.n), Module.finrank k (V ⟨r, by omega⟩) ≤
        Module.finrank k (V 0) + ∑ s ∈ Finset.range r, (if h : s < Fl.n then T ⟨s, h⟩ else 0) := by
      intro r
      induction r with
      | zero =>
        intro _
        rw [Finset.sum_range_zero, add_zero, Fin.mk_zero]
      | succ r ih =>
        intro hr
        have hr' : r < Fl.n := by omega
        rw [Finset.sum_range_succ, dif_pos hr']
        have h1 := hstep ⟨r, hr'⟩
        have h2 := ih (by omega)
        rw [Fin.succ_mk, Fin.castSucc_mk] at h1
        omega
    have hlast : V (Fin.last Fl.n) = Fs.secs := le_antisymm (secs_twist_idealSys_le Fs _)
      (by have h := secs_le_twist_idealSys_top (N := N) Fs; rwa [← hJlast] at h)
    have htop := htel Fl.n le_rfl
    rw [show (⟨Fl.n, by omega⟩ : Fin (Fl.n + 1)) = Fin.last Fl.n from rfl, hlast,
      Finset.sum_range] at htop
    simp only [Fin.is_lt, dif_pos, Fin.eta] at htop

    have hker := hK k Ω N x j b Fs hxj
    let mulβ : (Fs.twist (twistSys k x (-(b : ℤ)))).secs →ₗ[k] Fs.secs :=
      { toFun := fun t => ⟨x j ^ b * t, hker.1 t t.2⟩
        map_add' := fun t t' => Subtype.ext (mul_add _ _ _)
        map_smul' := fun c t => Subtype.ext (mul_smul_comm c _ _) }
    have hfinB : Module.Finite k (Fs.twist (twistSys k x (-(b : ℤ)))).secs :=
      Module.Finite.of_injective mulβ fun t t' h =>
        Subtype.ext (mul_left_cancel₀ hβ (congrArg Subtype.val h))
    have hV0 : ∀ s : V 0, (x j ^ b)⁻¹ * (s : Ω) ∈ (Fs.twist (twistSys k x (-(b : ℤ)))).secs := by
      intro s
      have hV : ∀ y : Ω, y ∈ V 0 → y ∈ (Fs.twist (idealSys x J)).secs := by
        intro y hy
        simp only [V] at hy
        rwa [hJ0] at hy
      have hs := hV s s.2
      obtain ⟨t, ht, hst⟩ := hker.2 s hs
      rw [hst, ← mul_assoc, inv_mul_cancel₀ hβ, one_mul]
      exact ht
    let divβ : V 0 →ₗ[k] (Fs.twist (twistSys k x (-(b : ℤ)))).secs :=
      { toFun := fun s => ⟨(x j ^ b)⁻¹ * s, hV0 s⟩
        map_add' := fun s s' => Subtype.ext (mul_add _ _ _)
        map_smul' := fun c s => Subtype.ext (mul_smul_comm c _ _) }
    have h0 : Module.finrank k (V 0) ≤ Module.finrank k (Fs.twist (twistSys k x (-(b : ℤ)))).secs :=
      LinearMap.finrank_le_finrank_of_injective (f := divβ) fun s s' h =>
        Subtype.ext (mul_left_cancel₀ (inv_ne_zero hβ) (congrArg Subtype.val h))
    have h0' := Nat.cast_le (α := ℤ) |>.mpr h0
    have htop' := Nat.cast_le (α := ℤ) |>.mpr htop
    push_cast at htop' ⊢
    linarith
