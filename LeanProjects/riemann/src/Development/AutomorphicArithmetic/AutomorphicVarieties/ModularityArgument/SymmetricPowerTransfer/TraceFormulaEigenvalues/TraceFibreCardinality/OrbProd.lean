import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.OrbReps

noncomputable section

namespace UpperTheory.V.Z.Sym.Tf

open MulAction

private lemma thin {T G : Type} [Group T] [Group G] (ι : T →* G) (θ : G →* G) (U : Subgroup G) (f : G → ℂ) (δ : G)
    (h : FinOrb ι θ U f δ) : ∃ R : Finset G, (∀ a ∈ R, ∀ b ∈ R, ∀ t, ∀ u ∈ U, b = ι t * a * u → a = b) ∧
      ∀ y, f (y⁻¹ * δ * θ y) ≠ 0 → ∃ t, ∃ s ∈ R, ∃ u ∈ U, y = ι t * s * u := by
  classical
  obtain ⟨S, hS⟩ := h
  let r : Setoid G :=
    { r := fun a b => ∃ t, ∃ u ∈ U, b = ι t * a * u
      iseqv := ⟨fun a => ⟨1, 1, U.one_mem, by simp⟩,
        fun {a b} ⟨t, u, hu, e⟩ => ⟨t⁻¹, u⁻¹, U.inv_mem hu, by rw [e]; simp [mul_assoc]⟩,
        fun {a b c} ⟨t, u, hu, e⟩ ⟨t', u', hu', e'⟩ =>
          ⟨t' * t, u * u', U.mul_mem hu hu', by rw [e', e]; simp [mul_assoc]⟩⟩ }
  refine ⟨(S.image (fun s => Quotient.mk r s)).image Quotient.out, ?_, ?_⟩
  · intro a ha b hb t u hu e
    simp only [Finset.mem_image] at ha hb
    obtain ⟨q, -, rfl⟩ := ha
    obtain ⟨q', -, rfl⟩ := hb
    have hr : r q.out q'.out := ⟨t, u, hu, e⟩
    have := Quotient.sound (s := r) hr
    simp only [Quotient.out_eq] at this
    rw [this]
  · intro y hy
    obtain ⟨t, s, hs, u, hu, rfl⟩ := hS y hy
    obtain ⟨t', u', hu', e⟩ : ∃ t', ∃ u' ∈ U, s = ι t' * (Quotient.mk r s).out * u' :=
      Quotient.mk_out (s := r) s
    refine ⟨t * t', _, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hs), u' * u,
      U.mul_mem hu' hu, ?_⟩
    conv_lhs => rw [e]
    simp [mul_assoc]

private lemma glue {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)} (P : RPG G Gv K)
    (S : Finset I) (j : ∀ v : S, Gv v) : ∃ g, (∀ v : S, P.p v g = j v) ∧ ∀ v ∉ S, P.p v g = 1 := by
  classical
  obtain ⟨g, hg⟩ := P.surj (fun v => if h : v ∈ S then j ⟨v, h⟩ else 1) (by
    rw [Filter.eventually_cofinite]
    refine S.finite_toSet.subset ?_
    intro v hv
    by_contra hvS
    rw [Finset.mem_coe] at hvS
    exact hv (by simp only [dif_neg hvS]; exact (K v).one_mem))
  refine ⟨g, fun v => ?_, fun v hv => ?_⟩
  · rw [hg, dif_pos v.2]
  · rw [hg, dif_neg hv]

private lemma mem_box {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)} (P : RPG G Gv K)
    (U : ∀ v, Subgroup (Gv v)) (g : G) : g ∈ P.box U ↔ ∀ v, P.p v g ∈ U v := by
  simp [RPG.box, Subgroup.mem_iInf]

private lemma index_pi' {J : Type} [Fintype J] {G : J → Type} [∀ j, Group (G j)] (H : ∀ j, Subgroup (G j)) :
    (Subgroup.pi Set.univ H).index = ∏ j, (H j).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y => ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

private lemma relIndex_box {I T : Type} [Group T] {Tv : I → Type} [∀ v, Group (Tv v)] {C₀ : ∀ v, Subgroup (Tv v)}
    (Q : RPG T Tv C₀) (A C : ∀ v, Subgroup (Tv v)) (S : Finset I) (h : ∀ v ∉ S, C v ≤ A v) :
    (Q.box A).relIndex (Q.box C) = ∏ v : S, (A v).relIndex (C v) := by
  classical
  let φ : Q.box C →* ((v : S) → C v) := Pi.monoidHom fun v =>
    ((Q.p v).comp (Q.box C).subtype).codRestrict (C v) (fun x => (mem_box Q C x).1 x.2 v)
  have hφ : Function.Surjective φ := by
    intro j
    obtain ⟨g, hg1, hg2⟩ := glue Q S (fun v => (j v : Tv v))
    have hg : g ∈ Q.box C := by
      rw [mem_box]
      intro v
      by_cases hv : v ∈ S
      · rw [hg1 ⟨v, hv⟩]
        exact (j ⟨v, hv⟩).2
      · rw [hg2 v hv]
        exact (C v).one_mem
    refine ⟨⟨g, hg⟩, ?_⟩
    funext v
    apply Subtype.ext
    exact hg1 v
  have hcomap : (Q.box A).subgroupOf (Q.box C) =
      (Subgroup.pi Set.univ fun v : S => (A v).subgroupOf (C v)).comap φ := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ,
      true_implies]
    rw [mem_box]
    constructor
    · intro hx v
      exact hx v
    · intro hx v
      by_cases hv : v ∈ S
      · exact hx ⟨v, hv⟩
      · exact h v hv ((mem_box Q C x).1 x.2 v)
  unfold Subgroup.relIndex
  rw [hcomap]
  exact (Subgroup.index_comap_of_surjective _ hφ).trans (index_pi' _)

private lemma mem_stab {G : Type} [Group G] (U : Subgroup G) (x g : G) :
    g ∈ stabilizer G (x : G ⧸ U) ↔ x⁻¹ * g * x ∈ U := by
  rw [mem_stabilizer_iff, MulAction.Quotient.smul_mk, QuotientGroup.eq, ← U.inv_mem_iff]
  simp [mul_assoc]

set_option maxHeartbeats 800000 in
theorem orbProd : OrbProd := by
  intro I G T _ _ Gv Tv _ _ K U C₀ C P Q ι ιv θ θv f fv δ hι hθ hf hinv hδ S hS hout
  classical
  have hR : ∀ v : S, ∃ R : Finset (Gv v),
      (∀ a ∈ R, ∀ b ∈ R, ∀ t, ∀ u ∈ U v, b = ιv v t * a * u → a = b) ∧
      ∀ y, fv v (y⁻¹ * P.p v δ * θv v y) ≠ 0 → ∃ t, ∃ s ∈ R, ∃ u ∈ U v, y = ιv v t * s * u :=
    fun v => thin (ιv v) (θv v) (U v) (fv v) (P.p v δ) (hS v v.2)
  choose R hRd hRc using hR
  choose x hx1 hx2 using fun c : ((v : S) → Gv v) => glue P S c
  have hsupp : ∀ y, (Function.mulSupport fun v => fv v (P.p v (y⁻¹ * δ * θ y))).Finite := by
    intro y
    have hae := P.ae y
    rw [Filter.eventually_cofinite] at hae
    refine (hae.union S.finite_toSet).subset ?_
    intro v hv
    by_contra hvn
    simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, not_or, not_not] at hvn
    rw [Function.mem_mulSupport] at hv
    apply hv
    obtain ⟨hK, -, -, h1, -⟩ := hout v hvn.2
    simp only [map_mul, map_inv, hθ]
    rw [hinv v _ (hK hvn.1), h1]
  have hcov : ∀ y, f (y⁻¹ * δ * θ y) ≠ 0 →
      ∃ t, ∃ c ∈ Fintype.piFinset R, ∃ u ∈ P.box U, y = ι t * x c * u := by
    intro y hy
    have hloc : ∀ v, fv v ((P.p v y)⁻¹ * P.p v δ * θv v (P.p v y)) ≠ 0 := by
      intro v h0
      apply hy
      rw [hf]
      refine finprod_eq_zero _ v ?_ (hsupp y)
      simpa only [map_mul, map_inv, hθ] using h0
    have hA : ∀ v : S, ∃ tv, ∃ s ∈ R v, ∃ uv ∈ U v, P.p v y = ιv v tv * s * uv :=
      fun v => hRc v (P.p v y) (hloc v)
    choose tS c hc uS huS heS using hA
    have hB : ∀ v, v ∉ S → ∃ tv, ∃ uv ∈ U v, P.p v y = ιv v tv * uv :=
      fun v hv => (hout v hv).2.2.2.2 _ (hloc v)
    let tv : (v : I) → Tv v := fun v =>
      if hv : v ∈ S then tS ⟨v, hv⟩ else if P.p v y ∈ K v then 1 else (hB v hv).choose
    obtain ⟨t, ht⟩ := Q.surj tv (by
      have hae := P.ae y
      rw [Filter.eventually_cofinite] at hae ⊢
      refine (hae.union S.finite_toSet).subset ?_
      intro v hv
      by_contra hvn
      simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, not_or, not_not] at hvn
      apply hv
      simp only [tv, dif_neg hvn.2, if_pos hvn.1]
      exact (C₀ v).one_mem)
    refine ⟨t, c, Fintype.mem_piFinset.2 hc, (ι t * x c)⁻¹ * y, ?_, by group⟩
    rw [mem_box]
    intro v
    rw [map_mul, map_inv, map_mul, hι, ht]
    by_cases hv : v ∈ S
    · have e1 : P.p v (x c) = c ⟨v, hv⟩ := hx1 c ⟨v, hv⟩
      have e2 : P.p v y = ιv v (tS ⟨v, hv⟩) * c ⟨v, hv⟩ * uS ⟨v, hv⟩ := heS ⟨v, hv⟩
      simp only [tv, dif_pos hv, e1, e2]
      simpa [mul_assoc] using huS ⟨v, hv⟩
    · rw [hx2 c v hv]
      by_cases hK : P.p v y ∈ K v
      · simp only [tv, dif_neg hv, if_pos hK, map_one, mul_one, inv_one, one_mul]
        exact (hout v hv).1 hK
      · simp only [tv, dif_neg hv, if_neg hK, mul_one]
        obtain ⟨uv, huv, euv⟩ := (hB v hv).choose_spec
        have e3 : (ιv v (hB v hv).choose)⁻¹ * P.p v y = uv := by
          rw [inv_mul_eq_iff_eq_mul]
          exact euv
        rw [e3]
        exact huv
  have hdist : ∀ c ∈ Fintype.piFinset R, ∀ c' ∈ Fintype.piFinset R, ∀ t, ∀ u ∈ P.box U,
      x c' = ι t * x c * u → c = c' := by
    intro c hc c' hc' t u hu e
    funext v
    have e' := congrArg (P.p v) e
    rw [map_mul, map_mul, hι, hx1, hx1] at e'
    exact hRd v (c v) (Fintype.mem_piFinset.1 hc v) (c' v) (Fintype.mem_piFinset.1 hc' v)
      (Q.p v t) (P.p v u) ((mem_box P U u).1 hu v) e'
  have hfinv : ∀ u ∈ P.box U, ∀ g, f (u⁻¹ * g * θ u) = f g := by
    intro u hu g
    rw [hf, hf]
    refine finprod_congr (fun v => ?_)
    simp only [map_mul, map_inv, hθ]
    exact hinv v _ ((mem_box P U u).1 hu v) _
  have hδg : ∀ t, (ι t)⁻¹ * δ * θ (ι t) = δ := by
    intro t
    have h1 := P.inj ((ι t)⁻¹ * δ * θ (ι t) * δ⁻¹) (fun v => by
      simp only [map_mul, map_inv, hθ, hι]
      rw [hδ v (Q.p v t)]
      simp)
    exact mul_inv_eq_one.1 h1
  have hglob := orbReps T G ι (Q.box C) θ (P.box U) f δ hfinv hδg _ (Fintype.piFinset R) x
    hdist hcov
  refine ⟨?_, ?_⟩
  · unfold FinOrb
    refine ⟨(Fintype.piFinset R).image x, fun y hy => ?_⟩
    obtain ⟨t, c, hc, u, hu, e⟩ := hcov y hy
    exact ⟨t, x c, Finset.mem_image_of_mem _ hc, u, hu, e⟩
  · rw [hglob]
    have hloc : ∏ v ∈ S, orb (ιv v) (C v) (θv v) (U v) (fv v) (P.p v δ) =
        ∏ v : S, ∑ s ∈ R v, ((Subgroup.comap (ιv v)
          (stabilizer (Gv v) (s : Gv v ⧸ U v))).relIndex (C v) : ℂ) *
            fv v (s⁻¹ * P.p v δ * θv v s) := by
      rw [← Finset.prod_coe_sort]
      refine Finset.prod_congr rfl (fun v _ => ?_)
      exact orbReps (Tv v) (Gv v) (ιv v) (C v) (θv v) (U v) (fv v) (P.p v δ) (hinv v) (hδ v)
        (Gv v) (R v) id (hRd v) (hRc v)
    rw [hloc, Finset.prod_univ_sum]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [Finset.prod_mul_distrib]
    congr 1
    · have hA : Subgroup.comap ι (stabilizer G ((x c : G) : G ⧸ P.box U)) =
          Q.box (fun v => Subgroup.comap (ιv v)
            (stabilizer (Gv v) ((P.p v (x c) : Gv v) : Gv v ⧸ U v))) := by
        ext t
        rw [Subgroup.mem_comap, mem_stab, mem_box, mem_box]
        refine forall_congr' (fun v => ?_)
        rw [Subgroup.mem_comap, mem_stab, map_mul, map_mul, map_inv, hι]
      have hCA : ∀ v ∉ S, C v ≤ Subgroup.comap (ιv v)
          (stabilizer (Gv v) ((P.p v (x c) : Gv v) : Gv v ⧸ U v)) := by
        intro v hv a ha
        rw [Subgroup.mem_comap, mem_stab, hx2 c v hv]
        simpa using (hout v hv).2.2.1 (Subgroup.mem_map_of_mem _ ha)
      rw [hA, relIndex_box Q _ C S hCA, Nat.cast_prod]
      refine Finset.prod_congr rfl (fun v _ => ?_)
      rw [hx1 c v]
    · rw [hf, finprod_eq_prod_of_mulSupport_subset (s := S) _ ?_, ← Finset.prod_coe_sort]
      · refine Finset.prod_congr rfl (fun v _ => ?_)
        simp only [map_mul, map_inv, hθ, hx1 c v]
      · intro v hv
        rw [Finset.mem_coe]
        by_contra hvS
        rw [Function.mem_mulSupport] at hv
        apply hv
        simp only [map_mul, map_inv, hθ, hx2 c v hvS, inv_one, one_mul, map_one, mul_one]
        exact (hout v hvS).2.2.2.1

end UpperTheory.V.Z.Sym.Tf
