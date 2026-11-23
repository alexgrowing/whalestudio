import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.CvGelfandAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.CvHecke
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

open GlobalTheory.BCT UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open scoped Pointwise

section SlopeTestRemainingChoices

variable {G : Type} [Group G]

private theorem avg_const {H : Type} [Group H] (u : H → ℂ) (c : ℂ) (hu : ∀ h, u h = c) : avg u = c := by
  have e : u = fun _ => c := funext hu
  subst e
  have hs : rStab (fun _ : H => c) = ⊤ := by
    ext k
    simp [rStab]
  unfold avg
  rw [hs]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := Unique.mk' _
  simp [finsum_unique]

private theorem cv_sum (K : Subgroup G) (f g : G → ℂ)
    (hf : ∀ k ∈ K, ∀ x, f (x * k) = f x) (hg : ∀ k ∈ K, ∀ x, g (k * x) = g x) (y : G) :
    cv K f g y = ∑ᶠ q : G ⧸ K, f q.out * g (q.out⁻¹ * y) := by
  refine hintSph G K (fun z => f z * g (z⁻¹ * y)) fun k hk x => ?_
  have e : (x * k)⁻¹ * y = k⁻¹ * (x⁻¹ * y) := by group
  simp only [e, hf k hk x, hg k⁻¹ (K.inv_mem hk)]

private theorem orb_iff (T K : Subgroup G) (a b : G ⧸ K) :
    (Quotient.mk'' a : MulAction.orbitRel.Quotient T (G ⧸ K)) = Quotient.mk'' b ↔ ∃ t : T, t • b = a := by
  rw [Quotient.eq'']
  exact MulAction.orbitRel_apply.trans MulAction.mem_orbit_iff

private theorem smul_mk (T K : Subgroup G) (t : T) (a : G) :
    t • (a : G ⧸ K) = (((t : G) * a : G) : G ⧸ K) := rfl

private noncomputable def orbOf (T K : Subgroup G) (d : DoubleCoset.Quotient (T : Set G) (K : Set G)) :
    MulAction.orbitRel.Quotient T (G ⧸ K) := Quotient.mk'' ((Quotient.out d : G) : G ⧸ K)

private theorem orbOf_mk (T K : Subgroup G) (x : G) :
    orbOf T K (DoubleCoset.mk T K x) = Quotient.mk'' (x : G ⧸ K) := by
  obtain ⟨t, k, ht, hk, h⟩ := DoubleCoset.mk_out_eq_mul T K x
  unfold orbOf
  rw [h, orb_iff]
  refine ⟨⟨t, ht⟩, ?_⟩
  rw [smul_mk, QuotientGroup.eq]
  simpa [mul_assoc] using hk

private theorem orbOf_bij (T K : Subgroup G) : Function.Bijective (orbOf T K) := by
  refine ⟨fun d d' h => ?_, fun o => ⟨DoubleCoset.mk T K (Quotient.out o : G ⧸ K).out, ?_⟩⟩
  · obtain ⟨t, ht⟩ := (orb_iff T K _ _).1 h
    rw [smul_mk, QuotientGroup.eq] at ht
    have e : DoubleCoset.mk T K (Quotient.out d') = DoubleCoset.mk T K (Quotient.out d) :=
      (DoubleCoset.eq T K _ _).2 ⟨t, t.2, _, ht, by group⟩
    rw [DoubleCoset.out_eq', DoubleCoset.out_eq'] at e
    exact e.symm
  · rw [orbOf_mk, QuotientGroup.out_eq', Quotient.out_eq']

private theorem sum_orb (T K : Subgroup G) (Φ : G ⧸ K → ℂ) (hΦ : ∀ (t : T) q, Φ (t • q) = Φ q) :
    ∑ᶠ o : MulAction.orbitRel.Quotient T (G ⧸ K), Φ (Quotient.out o) =
      ∑ᶠ d : DoubleCoset.Quotient (T : Set G) (K : Set G), Φ ((Quotient.out d : G) : G ⧸ K) := by
  symm
  refine finsum_eq_of_bijective (orbOf T K) (orbOf_bij T K) fun d => ?_
  obtain ⟨t, ht⟩ := (orb_iff T K _ _).1
    (show Quotient.mk'' (Quotient.out (orbOf T K d)) = Quotient.mk'' ((Quotient.out d : G) : G ⧸ K) from
      Quotient.out_eq' _)
  rw [← ht, hΦ]

private theorem closure_cpt [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (x t : G)
    (ht : t ∈ K.map (MulAut.conj x).toMonoidHom) :
    IsCompact (closure (Subgroup.zpowers t : Set G)) := by
  let h : G ≃ₜ G := (Homeomorph.mulLeft x).trans (Homeomorph.mulRight x⁻¹)
  have hL : ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) = h '' (K : Set G) := by
    rw [Subgroup.coe_map]
    refine Set.image_congr fun a _ => ?_
    simp [h, MulAut.conj_apply]
  have hLc : IsCompact ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
    rw [hL]; exact hKc.image h.continuous
  have hLcl : IsClosed ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
    rw [hL]; exact h.isClosed_image.2 (Subgroup.isClosed_of_isOpen K hKo)
  exact hLc.of_isClosed_subset isClosed_closure
    (closure_minimal (Subgroup.zpowers_le.2 ht) hLcl)

private theorem mem_stab (T K : Subgroup G) (x : G) (t : T) :
    t ∈ MulAction.stabilizer T (x : G ⧸ K) ↔ (t : G) ∈ K.map (MulAut.conj x).toMonoidHom := by
  rw [MulAction.mem_stabilizer_iff, smul_mk, QuotientGroup.eq]
  have e : (MulAut.conj x).toMonoidHom = ((MulAut.conj x : G ≃* G) : G →* G) := rfl
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, ← K.inv_mem_iff]
  have e2 : ((t : G) * x)⁻¹ * x = (x⁻¹ * (t : G) * x)⁻¹ := by group
  rw [e2, inv_inv]

private theorem finite_cosets [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) {S : Set G} (hS : IsCompact S) :
    ((fun s : G => (s : G ⧸ K)) '' S).Finite := by
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun s : G => {y : G | s⁻¹ * y ∈ K})
    (fun s => hKo.preimage (continuous_const.mul continuous_id))
    (fun s _ => Set.mem_iUnion.2 ⟨s, by simp [K.one_mem]⟩)
  refine (t.finite_toSet.image fun s : G => (s : G ⧸ K)).subset ?_
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨u, hu, hus⟩ := Set.mem_iUnion₂.1 (ht hs)
  exact ⟨u, hu, QuotientGroup.eq.2 hus⟩

private noncomputable def Fk (K : Subgroup G) (θ : G →* G) (δ : G) (f g : G → ℂ) (q q' : G ⧸ K) : ℂ :=
  f (q.out⁻¹ * q'.out) * g (q'.out⁻¹ * δ * θ q.out)

private theorem Fk_mk (K : Subgroup G) (θ : G →* G) (δ : G) (f g : G → ℂ)
    (hθK : ∀ k ∈ K, θ k ∈ K)
    (hf : ∀ k ∈ K, ∀ x, f (k * x) = f x ∧ f (x * k) = f x)
    (hg : ∀ k ∈ K, ∀ x, g (k * x) = g x ∧ g (x * k) = g x) (a b : G) :
    Fk K θ δ f g (a : G ⧸ K) (b : G ⧸ K) = f (a⁻¹ * b) * g (b⁻¹ * δ * θ a) := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K a
  obtain ⟨h', hh'⟩ := QuotientGroup.mk_out_eq_mul K b
  unfold Fk
  rw [hh, hh']
  have e1 : (a * (h : G))⁻¹ * (b * (h' : G)) = (h : G)⁻¹ * ((a⁻¹ * b) * h') := by group
  have e2 : (b * (h' : G))⁻¹ * δ * θ (a * h) = (h' : G)⁻¹ * ((b⁻¹ * δ * θ a) * θ h) := by
    rw [map_mul]; group
  rw [e1, e2, (hf _ (K.inv_mem h.2) _).1, (hf _ h'.2 _).2, (hg _ (K.inv_mem h'.2) _).1,
    (hg _ (hθK _ h.2) _).2]

private theorem Fk_inv (K : Subgroup G) (θ : G →* G) (δ : G) (f g : G → ℂ)
    (hθK : ∀ k ∈ K, θ k ∈ K)
    (hf : ∀ k ∈ K, ∀ x, f (k * x) = f x ∧ f (x * k) = f x)
    (hg : ∀ k ∈ K, ∀ x, g (k * x) = g x ∧ g (x * k) = g x) (t : twCent θ δ) (q q' : G ⧸ K) :
    Fk K θ δ f g (t • q) (t • q') = Fk K θ δ f g q q' := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q'
  rw [smul_mk, smul_mk, Fk_mk K θ δ f g hθK hf hg, Fk_mk K θ δ f g hθK hf hg]
  have ht : (t : G) * δ = δ * θ t := t.2
  have e1 : ((t : G) * a)⁻¹ * ((t : G) * b) = a⁻¹ * b := by group
  have e2 : ((t : G) * b)⁻¹ * δ * θ ((t : G) * a) = b⁻¹ * δ * θ a := by
    calc ((t : G) * b)⁻¹ * δ * θ ((t : G) * a) = b⁻¹ * (t : G)⁻¹ * (δ * θ t) * θ a := by
          rw [map_mul]; group
      _ = b⁻¹ * δ * θ a := by rw [← ht]; group
  rw [e1, e2]

private theorem sum_left (K : Subgroup G) (θ : G →* G) (δ : G) (f g : G → ℂ)
    (hθK : ∀ k ∈ K, θ k ∈ K)
    (hf : ∀ k ∈ K, ∀ x, f (k * x) = f x ∧ f (x * k) = f x)
    (hg : ∀ k ∈ K, ∀ x, g (k * x) = g x ∧ g (x * k) = g x) (x : G) :
    ∑ᶠ y, Fk K θ δ f g (x : G ⧸ K) y = cv K f g (x⁻¹ * δ * θ x) := by
  rw [cv_sum K f g (fun k hk y => (hf k hk y).2) (fun k hk y => (hg k hk y).1),
    ← finsum_comp_equiv (MulAction.toPerm x : Equiv.Perm (G ⧸ K))]
  refine finsum_congr fun q => ?_
  have e : (MulAction.toPerm x : Equiv.Perm (G ⧸ K)) q = ((x * q.out : G) : G ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [e, Fk_mk K θ δ f g hθK hf hg]
  have e1 : x⁻¹ * (x * q.out) = q.out := by group
  have e2 : (x * q.out)⁻¹ * δ * θ x = q.out⁻¹ * (x⁻¹ * δ * θ x) := by group
  rw [e1, e2]

private theorem sum_right (K : Subgroup G) (θ : G →* G) (δ : G) (f g : G → ℂ)
    (hθ2 : ∀ x, θ (θ x) = x) (hθK : ∀ k ∈ K, θ k ∈ K)
    (hf : ∀ k ∈ K, ∀ x, f (k * x) = f x ∧ f (x * k) = f x)
    (hg : ∀ k ∈ K, ∀ x, g (k * x) = g x ∧ g (x * k) = g x)
    (hfθ : ∀ k ∈ K, ∀ x, (f ∘ θ) (k * x) = (f ∘ θ) x) (x' : G) :
    ∑ᶠ x, Fk K θ δ f g x (x' : G ⧸ K) = cv K g (f ∘ θ) (x'⁻¹ * δ * θ x') := by
  rw [cv_sum K g (f ∘ θ) (fun k hk y => (hg k hk y).2) hfθ]
  symm
  refine finsum_eq_of_bijective
    (fun u : G ⧸ K => ((θ (δ⁻¹ * x' * u.out) : G) : G ⧸ K)) ⟨fun u v h => ?_, fun q => ?_⟩ fun u => ?_
  · have h1 := QuotientGroup.eq.1 h
    rw [← map_inv, ← map_mul] at h1
    have h2 := hθK _ h1
    rw [hθ2] at h2
    have e : (δ⁻¹ * x' * u.out)⁻¹ * (δ⁻¹ * x' * v.out) = u.out⁻¹ * v.out := by group
    rw [e] at h2
    rw [← QuotientGroup.out_eq' u, ← QuotientGroup.out_eq' v]
    exact QuotientGroup.eq.2 h2
  · refine ⟨((x'⁻¹ * δ * θ q.out : G) : G ⧸ K), ?_⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K (x'⁻¹ * δ * θ q.out)
    have e : δ⁻¹ * x' * (x'⁻¹ * δ * θ q.out * (h : G)) = θ q.out * h := by group
    show ((θ (δ⁻¹ * x' * (((x'⁻¹ * δ * θ q.out : G) : G ⧸ K)).out) : G) : G ⧸ K) = q
    rw [hh, e, map_mul, hθ2]
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    refine QuotientGroup.eq.2 ?_
    have e3 : (q.out * θ (h : G))⁻¹ * q.out = (θ (h : G))⁻¹ := by group
    rw [e3]
    exact K.inv_mem (hθK _ h.2)
  · show g u.out * f (θ (u.out⁻¹ * (x'⁻¹ * δ * θ x'))) = _
    rw [Fk_mk K θ δ f g hθK hf hg]
    have e1 : x'⁻¹ * δ * θ (θ (δ⁻¹ * x' * u.out)) = u.out := by rw [hθ2]; group
    have e2 : (θ (δ⁻¹ * x' * u.out))⁻¹ * x' = θ (u.out⁻¹ * (x'⁻¹ * δ * θ x')) := by
      simp only [map_mul, map_inv, hθ2]
      group
    rw [e1, e2, mul_comm]

private theorem avg_hecke (K : Subgroup G) (θ : G →* G) (δ : G) (h : G → ℂ)
    (hθK : ∀ k ∈ K, θ k ∈ K)
    (hh : ∀ k ∈ K, ∀ x, h (k * x) = h x ∧ h (x * k) = h x) (x : G) :
    avg (fun k : K => h ((x * k)⁻¹ * δ * θ (x * k))) = h (x⁻¹ * δ * θ x) := by
  refine avg_const _ _ fun k => ?_
  have e : (x * (k : G))⁻¹ * δ * θ (x * k) = (k : G)⁻¹ * ((x⁻¹ * δ * θ x) * θ k) := by
    rw [map_mul]; group
  rw [e, (hh _ (K.inv_mem k.2) _).1, (hh _ (hθK _ k.2) _).2]

end SlopeTestRemainingChoices

theorem twSwap : OrbFub → TwSwap := by
  intro hFub G _ _ _ K hKo hKc θ hθc hθ2 hθK δ hfin f g hf hg
  have hfθ : IsHecke K (f ∘ θ) := by
    let φ : G ≃ₜ G := ⟨⟨θ, θ, hθ2, hθ2⟩, hθc, hθc⟩
    refine ⟨hf.1.comp_homeomorph φ, fun k hk x => ?_⟩
    simp only [Function.comp, map_mul]
    exact ⟨(hf.2 _ (hθK k hk) _).1, (hf.2 _ (hθK k hk) _).2⟩
  refine ⟨hfθ, ?_⟩
  have hfb := hf.2
  have hgb := hg.2
  have hfθl : ∀ k ∈ K, ∀ x, (f ∘ θ) (k * x) = (f ∘ θ) x := fun k hk x => (hfθ.2 k hk x).1
  set T := twCent θ δ with hTdef
  have hCle : cptPart T ≤ T := by
    unfold cptPart
    rw [Subgroup.closure_le]
    intro t ht
    exact ht.1
  let C : Subgroup T := (cptPart T).subgroupOf T
  have hNorm : ∀ g' ∈ T, ∀ n ∈ cptPart T, g' * n * g'⁻¹ ∈ cptPart T := by
    intro g' hg' n hn
    have h := GlobalTheory.TwOrbConj.cptPart_map g' T
    rw [GlobalTheory.TwOrbConj.map_conj_self T hg'] at h
    rw [h]
    exact ⟨n, hn, by simp [MulAut.conj_apply]⟩
  haveI : C.Normal := ⟨fun n hn g' => by
    have hn' : (n : G) ∈ cptPart T := Subgroup.mem_subgroupOf.1 hn
    exact Subgroup.mem_subgroupOf.2 (by simpa using hNorm g' g'.2 n hn')⟩
  have hidx : ∀ x : G, (MulAction.stabilizer T (x : G ⧸ K)).relIndex C =
      (T ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart T) := by
    intro x
    have e : MulAction.stabilizer T (x : G ⧸ K) =
        (T ⊓ K.map (MulAut.conj x).toMonoidHom).comap T.subtype := by
      ext t
      rw [mem_stab]
      exact ⟨fun h => ⟨t.2, h⟩, fun h => h.2⟩
    have e2 : C.map T.subtype = cptPart T := by
      show ((cptPart T).subgroupOf T).map T.subtype = cptPart T
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.2 hCle
    rw [e, Subgroup.relIndex_comap, e2]
  have hstab : ∀ q : G ⧸ K, MulAction.stabilizer T q ≤ C := by
    intro q t ht
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    have hm := (mem_stab T K a t).1 ht
    exact Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure ⟨t.2, closure_cpt K hKo hKc a _ hm⟩)
  have hSf : IsCompact (tsupport f) := hf.1.isCompact
  have hSg : IsCompact (tsupport g) := hg.1.isCompact
  have hfx : ∀ x : G ⧸ K, {y | Fk K θ δ f g x y ≠ 0}.Finite := by
    intro x
    have hc : Continuous fun s : G => x.out * s := by fun_prop
    refine (finite_cosets K hKo (hSf.image hc)).subset ?_
    intro y hy
    have h1 : f (x.out⁻¹ * y.out) ≠ 0 := left_ne_zero_of_mul hy
    exact ⟨y.out, ⟨_, subset_tsupport f h1, by group⟩, QuotientGroup.out_eq' y⟩
  have hfy : ∀ y : G ⧸ K, {x | Fk K θ δ f g x y ≠ 0}.Finite := by
    intro y
    have hc : Continuous fun s : G => y.out * s⁻¹ := by fun_prop
    refine (finite_cosets K hKo (hSf.image hc)).subset ?_
    intro x hx
    have h1 : f (x.out⁻¹ * y.out) ≠ 0 := left_ne_zero_of_mul hx
    exact ⟨x.out, ⟨_, subset_tsupport f h1, by group⟩, QuotientGroup.out_eq' x⟩
  have hfo : {o : MulAction.orbitRel.Quotient T (G ⧸ K) |
      ∃ y, Fk K θ δ f g (Quotient.out o) y ≠ 0}.Finite := by
    have hCc : IsCompact ((K : Set G) * (tsupport f * tsupport g) * (K : Set G)) :=
      (hKc.mul (hSf.mul hSg)).mul hKc
    refine ((hfin _ hCc).image (orbOf T K)).subset ?_
    rintro o ⟨y, hy⟩
    have h1 : f ((Quotient.out o : G ⧸ K).out⁻¹ * y.out) ≠ 0 := left_ne_zero_of_mul hy
    have h2 : g (y.out⁻¹ * δ * θ (Quotient.out o : G ⧸ K).out) ≠ 0 := right_ne_zero_of_mul hy
    obtain ⟨t, k, ht, hk, hd⟩ := DoubleCoset.mk_out_eq_mul T K (Quotient.out o : G ⧸ K).out
    refine ⟨DoubleCoset.mk T K (Quotient.out o : G ⧸ K).out, ?_, ?_⟩
    · rw [Set.mem_setOf_eq, hd]
      generalize (Quotient.out o : G ⧸ K).out = x at h1 h2
      have htδ : t * δ = δ * θ t := ht
      have e : (t * x * k)⁻¹ * δ * θ (t * x * k) =
          k⁻¹ * ((x⁻¹ * y.out) * (y.out⁻¹ * δ * θ x)) * θ k := by
        calc (t * x * k)⁻¹ * δ * θ (t * x * k)
            = k⁻¹ * x⁻¹ * t⁻¹ * (δ * θ t) * θ x * θ k := by simp only [map_mul]; group
          _ = k⁻¹ * x⁻¹ * t⁻¹ * (t * δ) * θ x * θ k := by rw [htδ]
          _ = k⁻¹ * ((x⁻¹ * y.out) * (y.out⁻¹ * δ * θ x)) * θ k := by group
      rw [e]
      exact Set.mul_mem_mul (Set.mul_mem_mul (K.inv_mem hk)
        (Set.mul_mem_mul (subset_tsupport f h1) (subset_tsupport g h2))) (hθK k hk)
    · rw [orbOf_mk, QuotientGroup.out_eq', Quotient.out_eq']
  have key := hFub T (G ⧸ K) (G ⧸ K) C hstab hstab (Fk K θ δ f g)
    (Fk_inv K θ δ f g hθK hfb hgb) hfx hfy hfo
  have hidxI : ∀ (t : T) (q : G ⧸ K), (MulAction.stabilizer T (t • q)).relIndex C =
      (MulAction.stabilizer T q).relIndex C := by
    intro t q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    rw [smul_mk, hidx, hidx]
    exact GlobalTheory.TwOrbConj.relIndex_conj (t : G) T T _ _ (GlobalTheory.TwOrbConj.map_conj_self T t.2).symm
      (GlobalTheory.TwOrbConj.map_conj_mul K t a)
  have hL := sum_orb T K
    (fun q => (((MulAction.stabilizer T q).relIndex C : ℕ) : ℂ) * ∑ᶠ y, Fk K θ δ f g q y)
    (fun t q => by
      show (((MulAction.stabilizer T (t • q)).relIndex C : ℕ) : ℂ) * ∑ᶠ y, Fk K θ δ f g (t • q) y = _
      rw [hidxI, ← finsum_comp_equiv (f := fun y => Fk K θ δ f g (t • q) y)
        (MulAction.toPerm t : Equiv.Perm (G ⧸ K))]
      congr 1
      exact finsum_congr fun y => Fk_inv K θ δ f g hθK hfb hgb t q y)
  have hR := sum_orb T K
    (fun q => (((MulAction.stabilizer T q).relIndex C : ℕ) : ℂ) * ∑ᶠ x, Fk K θ δ f g x q)
    (fun t q => by
      show (((MulAction.stabilizer T (t • q)).relIndex C : ℕ) : ℂ) * ∑ᶠ x, Fk K θ δ f g x (t • q) = _
      rw [hidxI, ← finsum_comp_equiv (f := fun x => Fk K θ δ f g x (t • q))
        (MulAction.toPerm t : Equiv.Perm (G ⧸ K))]
      congr 1
      exact finsum_congr fun x => Fk_inv K θ δ f g hθK hfb hgb t x q)
  have hcf := cvHecke G K hKo hKc f g hf hg
  have hcg := cvHecke G K hKo hKc g (f ∘ θ) hg hfθ
  calc twOrb θ K δ (cv K f g)
      = ∑ᶠ d : DoubleCoset.Quotient (T : Set G) (K : Set G),
          (((MulAction.stabilizer T ((Quotient.out d : G) : G ⧸ K)).relIndex C : ℕ) : ℂ) *
            ∑ᶠ y, Fk K θ δ f g ((Quotient.out d : G) : G ⧸ K) y := by
        unfold twOrb
        refine finsum_congr fun d => ?_
        rw [avg_hecke K θ δ _ hθK hcf.2, hidx, sum_left K θ δ f g hθK hfb hgb]
    _ = ∑ᶠ d : DoubleCoset.Quotient (T : Set G) (K : Set G),
          (((MulAction.stabilizer T ((Quotient.out d : G) : G ⧸ K)).relIndex C : ℕ) : ℂ) *
            ∑ᶠ x, Fk K θ δ f g x ((Quotient.out d : G) : G ⧸ K) := hL.symm.trans (key.trans hR)
    _ = twOrb θ K δ (cv K g (f ∘ θ)) := by
        unfold twOrb
        refine finsum_congr fun d => ?_
        rw [avg_hecke K θ δ _ hθK hcg.2, hidx, sum_right K θ δ f g hθ2 hθK hfb hgb hfθl]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Th
