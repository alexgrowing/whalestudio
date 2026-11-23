import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.CvGelfandAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.CvHecke
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexProd

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

open GlobalTheory.BCT UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

private theorem out_val {G : Type} [Group G] (K : Subgroup G) (u : G → ℂ)
    (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) (x : G) : u (x : G ⧸ K).out = u x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
  rw [hh, hu _ h.2]

private theorem cv_sum {G : Type} [Group G] (K : Subgroup G) (f g : G → ℂ)
    (hf : ∀ k ∈ K, ∀ x, f (x * k) = f x) (hg : ∀ k ∈ K, ∀ x, g (k * x) = g x) (y : G) :
    cv K f g y = ∑ᶠ q : G ⧸ K, f q.out * g (q.out⁻¹ * y) := by
  refine hintSph G K (fun z => f z * g (z⁻¹ * y)) ?_
  intro k hk x
  have e : (x * k)⁻¹ * y = k⁻¹ * (x⁻¹ * y) := by group
  simp only [e, hf k hk x, hg k⁻¹ (K.inv_mem hk)]

private theorem sum_translate {G : Type} [Group G] (K : Subgroup G) (A : G → ℂ)
    (hA : ∀ k ∈ K, ∀ x, A (x * k) = A x) (x : G) :
    ∑ᶠ q : G ⧸ K, A (x * q.out) = ∑ᶠ r : G ⧸ K, A r.out := by
  have hterm : ∀ q : G ⧸ K, A (x * q.out) =
      (fun p : G ⧸ K => A p.out) (MulAction.toPerm x q) := by
    intro q
    have e1 : MulAction.toPerm x q = ((x * q.out : G) : G ⧸ K) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    simp only [e1]
    rw [out_val K A hA]
  rw [finsum_congr hterm]
  exact finsum_comp_equiv (f := fun p : G ⧸ K => A p.out)
    (MulAction.toPerm x : Equiv.Perm (G ⧸ K))

private theorem exch {A B : Type} (Φ : A → B → ℂ) (S : Set A) (T : Set B)
    (hS : S.Finite) (hT : T.Finite)
    (h1 : ∀ a b, Φ a b ≠ 0 → a ∈ S) (h2 : ∀ a b, Φ a b ≠ 0 → b ∈ T) :
    ∑ᶠ a, ∑ᶠ b, Φ a b = ∑ᶠ b, ∑ᶠ a, Φ a b := by
  have e1 : ∀ a, ∑ᶠ b, Φ a b = ∑ b ∈ hT.toFinset, Φ a b := fun a =>
    finsum_eq_sum_of_support_subset _ (fun b hb => by simpa using h2 a b hb)
  have e2 : ∀ b, ∑ᶠ a, Φ a b = ∑ a ∈ hS.toFinset, Φ a b := fun b =>
    finsum_eq_sum_of_support_subset _ (fun a ha => by simpa using h1 a b ha)
  simp only [e1, e2]
  rw [finsum_eq_sum_of_support_subset (s := hS.toFinset),
    finsum_eq_sum_of_support_subset (s := hT.toFinset), Finset.sum_comm]
  · intro b hb
    by_contra hbT
    apply hb
    refine Finset.sum_eq_zero fun a _ => ?_
    by_contra h
    exact hbT (by simpa using h2 a b h)
  · intro a ha
    by_contra haS
    apply ha
    refine Finset.sum_eq_zero fun b _ => ?_
    by_contra h
    exact haS (by simpa using h1 a b h)

theorem cvRing : CvRing := by
  intro G _ _ _ K hKo hKc f g h hf hg hh
  have hfl : ∀ k ∈ K, ∀ x, f (k * x) = f x := fun k hk x => (hf.2 k hk x).1
  have hfr : ∀ k ∈ K, ∀ x, f (x * k) = f x := fun k hk x => (hf.2 k hk x).2
  have hgl : ∀ k ∈ K, ∀ x, g (k * x) = g x := fun k hk x => (hg.2 k hk x).1
  have hgr : ∀ k ∈ K, ∀ x, g (x * k) = g x := fun k hk x => (hg.2 k hk x).2
  have hhl : ∀ k ∈ K, ∀ x, h (k * x) = h x := fun k hk x => (hh.2 k hk x).1
  have hhr : ∀ k ∈ K, ∀ x, h (x * k) = h x := fun k hk x => (hh.2 k hk x).2
  have finf : {q : G ⧸ K | f q.out ≠ 0}.Finite := LevOpTmul.finite_supp hKo hf.1
  have hir : ∀ k ∈ K, ∀ x, ((K : Set G).indicator (1 : G → ℂ)) (x * k) =
      (K : Set G).indicator (1 : G → ℂ) x := by
    intro k hk x
    classical
    simp only [Set.indicator_apply, SetLike.mem_coe, K.mul_mem_cancel_right hk, Pi.one_apply]
  have hil : ∀ k ∈ K, ∀ x, ((K : Set G).indicator (1 : G → ℂ)) (k * x) =
      (K : Set G).indicator (1 : G → ℂ) x := by
    intro k hk x
    classical
    simp only [Set.indicator_apply, SetLike.mem_coe, K.mul_mem_cancel_left hk, Pi.one_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext y
    have hfg := cvHecke G K hKo hKc f g hf hg
    have hgh := cvHecke G K hKo hKc g h hg hh
    have hy : HasCompactSupport fun z : G => h (z⁻¹ * y) :=
      hh.1.comp_homeomorph ((Homeomorph.inv G).trans (Homeomorph.mulRight y))
    have finh : {q : G ⧸ K | h (q.out⁻¹ * y) ≠ 0}.Finite := LevOpTmul.finite_supp hKo hy
    have A₁ : cv K (cv K f g) h y = ∑ᶠ q : G ⧸ K, cv K f g q.out * h (q.out⁻¹ * y) :=
      cv_sum K _ h (fun k hk x => (hfg.2 k hk x).2) hhl y
    have A₂ : cv K f (cv K g h) y = ∑ᶠ p : G ⧸ K, f p.out * cv K g h (p.out⁻¹ * y) :=
      cv_sum K f _ hfr (fun k hk x => (hgh.2 k hk x).1) y
    have B₁ : ∀ q : G ⧸ K, cv K f g q.out * h (q.out⁻¹ * y) =
        ∑ᶠ p : G ⧸ K, f p.out * g (p.out⁻¹ * q.out) * h (q.out⁻¹ * y) := by
      intro q
      rw [cv_sum K f g hfr hgl,
        finsum_mul]
    have B₂ : ∀ p : G ⧸ K, f p.out * cv K g h (p.out⁻¹ * y) =
        ∑ᶠ q : G ⧸ K, f p.out * g (p.out⁻¹ * q.out) * h (q.out⁻¹ * y) := by
      intro p
      have hA : ∀ k ∈ K, ∀ x, (fun z => g z * h (z⁻¹ * (p.out⁻¹ * y))) (x * k) =
          (fun z => g z * h (z⁻¹ * (p.out⁻¹ * y))) x := by
        intro k hk x
        have e : (x * k)⁻¹ * (p.out⁻¹ * y) = k⁻¹ * (x⁻¹ * (p.out⁻¹ * y)) := by group
        simp only [e, hgr k hk x, hhl k⁻¹ (K.inv_mem hk)]
      have T : ∑ᶠ r : G ⧸ K, g r.out * h (r.out⁻¹ * (p.out⁻¹ * y)) =
          ∑ᶠ q : G ⧸ K, g (p.out⁻¹ * q.out) * h (q.out⁻¹ * y) := by
        refine (sum_translate K (fun z => g z * h (z⁻¹ * (p.out⁻¹ * y))) hA p.out⁻¹).symm.trans
          (finsum_congr fun q => ?_)
        have e : (p.out⁻¹ * q.out)⁻¹ * (p.out⁻¹ * y) = q.out⁻¹ * y := by group
        show g (p.out⁻¹ * q.out) * h ((p.out⁻¹ * q.out)⁻¹ * (p.out⁻¹ * y)) = _
        rw [e]
      rw [cv_sum K g h hgr hhl, T,
        mul_finsum]
      exact finsum_congr fun q => (mul_assoc _ _ _).symm
    rw [A₁, A₂, finsum_congr B₁, finsum_congr B₂]
    refine exch (fun (q p : G ⧸ K) => f p.out * g (p.out⁻¹ * q.out) * h (q.out⁻¹ * y))
      _ _ finh finf ?_ ?_
    · intro q p hne
      exact right_ne_zero_of_mul hne
    · intro q p hne
      exact left_ne_zero_of_mul (left_ne_zero_of_mul hne)
  · funext y
    rw [cv_sum K f _ hfr hil y, finsum_eq_single _ (y : G ⧸ K)]
    · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K y
      have hm : (y : G ⧸ K).out⁻¹ * y ∈ K := by
        have e : (y : G ⧸ K).out⁻¹ * y = (k : G)⁻¹ := by rw [hk]; group
        rw [e]
        exact K.inv_mem k.2
      rw [out_val K f hfr, Set.indicator_of_mem (SetLike.mem_coe.2 hm)]
      simp
    · intro q hq
      have hm : q.out⁻¹ * y ∉ K := fun hm =>
        hq ((QuotientGroup.out_eq' q).symm.trans (QuotientGroup.eq.2 hm))
      rw [Set.indicator_of_notMem (fun h' => hm (SetLike.mem_coe.1 h')), mul_zero]
  · funext y
    rw [cv_sum K _ f hir hfl y, finsum_eq_single _ ((1 : G) : G ⧸ K)]
    · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (1 : G)
      have hm : ((1 : G) : G ⧸ K).out ∈ K := by
        rw [hk, one_mul]
        exact k.2
      rw [Set.indicator_of_mem (SetLike.mem_coe.2 hm), Pi.one_apply, one_mul,
        hfl _ (K.inv_mem hm)]
    · intro q hq
      have hm : q.out ∉ K := fun hm =>
        hq ((QuotientGroup.out_eq' q).symm.trans
          (QuotientGroup.eq.2 (by simpa using K.inv_mem hm)))
      rw [Set.indicator_of_notMem (fun h' => hm (SetLike.mem_coe.1 h')), zero_mul]
  · intro c d
    funext y
    have hl : ∀ k ∈ K, ∀ x, (fun y => c * g y + d * h y) (k * x) =
        (fun y => c * g y + d * h y) x := by
      intro k hk x
      simp only [hgl k hk x, hhl k hk x]
    show cv K f (fun y => c * g y + d * h y) y = c * cv K f g y + d * cv K f h y
    have s₁ : (Function.support fun q : G ⧸ K => f q.out * g (q.out⁻¹ * y)).Finite :=
      finf.subset fun q hq => left_ne_zero_of_mul hq
    have s₂ : (Function.support fun q : G ⧸ K => f q.out * h (q.out⁻¹ * y)).Finite :=
      finf.subset fun q hq => left_ne_zero_of_mul hq
    have t₁ : (Function.support fun q : G ⧸ K => c * (f q.out * g (q.out⁻¹ * y))).Finite :=
      s₁.subset fun q hq => right_ne_zero_of_mul hq
    have t₂ : (Function.support fun q : G ⧸ K => d * (f q.out * h (q.out⁻¹ * y))).Finite :=
      s₂.subset fun q hq => right_ne_zero_of_mul hq
    rw [cv_sum K f _ hfr hl y, cv_sum K f g hfr hgl y, cv_sum K f h hfr hhl y,
      mul_finsum, mul_finsum, ← finsum_add_distrib t₁ t₂]
    refine finsum_congr fun q => ?_
    ring

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Th
