import Mathlib
import Formalism.PolynomialDimension.DigitClassSize

noncomputable section

open Module

namespace Formalism.CountingSumsFrames

namespace GoodRankMultinomialDepth

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def GR {A B : Type} [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B]
    (ι : Type) (π : O) (f : A →ₗ[O] B) (D : ℕ) : Prop :=
  ∃ (u : (ι → O) →ₗ[O] A) (v : B →ₗ[O] (ι → O)), v ∘ₗ f ∘ₗ u = (π ^ D) • LinearMap.id

theorem gr_comp {A A' B ι : Type} [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O A']
    [AddCommGroup B] [Module O B] {π : O} {f : A →ₗ[O] B} {D : ℕ} (w : A' →ₗ[O] A)
    (h : GR ι π (f ∘ₗ w) D) : GR ι π f D := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨w ∘ₗ u, v, by rw [← huv]; rfl⟩

theorem gr_goodRank {A B ι : Type} [Fintype ι] [AddCommGroup A] [Module O A] [AddCommGroup B]
    [Module O B] {π : O} {f : A →ₗ[O] B} {D : ℕ} (h : GR ι π f D) :
    Formalism.G0.GoodRank π f (Fintype.card ι) D := by
  obtain ⟨u, v, huv⟩ := h
  let e : (Fin (Fintype.card ι) → O) ≃ₗ[O] (ι → O) :=
    LinearEquiv.funCongrLeft O O (Fintype.equivFin ι)
  refine ⟨u ∘ₗ e.toLinearMap, e.symm.toLinearMap ∘ₗ v, ?_⟩
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun huv (e x)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
  change e.symm (v (f (u (e x)))) = _
  rw [hx, map_smul, LinearEquiv.symm_apply_apply]

theorem goodRank_mono {A B : Type} [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B]
    {π : O} {f : A →ₗ[O] B} {n m D : ℕ} (h : Formalism.G0.GoodRank π f n D) (hmn : m ≤ n) :
    Formalism.G0.GoodRank π f m D := by
  classical
  obtain ⟨u, v, huv⟩ := h
  let i : (Fin m → O) →ₗ[O] (Fin n → O) :=
    LinearMap.pi (fun k => if hk : k.val < m then LinearMap.proj ⟨k.val, hk⟩ else 0)
  let p : (Fin n → O) →ₗ[O] (Fin m → O) := LinearMap.funLeft O O (Fin.castLE hmn)
  have hpi : ∀ x, p (i x) = x := by
    intro x
    funext k
    simp [p, i, LinearMap.funLeft_apply, Fin.castLE, k.isLt]
  refine ⟨u ∘ₗ i, p ∘ₗ v, ?_⟩
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun huv (i x)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
  rw [hx, map_smul, hpi]

theorem pow_succ_dvd_of_not_dvd {π : O} (hπ : Irreducible π) {a : O} {E : ℕ}
    (h : ¬ a ∣ π ^ E) : π ^ (E + 1) ∣ a := by
  by_cases ha : a = 0
  · simp [ha]
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  by_contra hc
  apply h
  have hk : k ≤ E := by
    by_contra hk
    apply hc
    rw [hu]
    exact Dvd.dvd.mul_left (pow_dvd_pow π (not_le.mp hk)) _
  rw [hu]
  exact (Units.mul_left_dvd).mpr (pow_dvd_pow π hk)

theorem gr_of_primitive {B ι : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup B] [Module O B]
    [Module.Free O B] [Module.Finite O B] {π : O} (hπ : Irreducible π) (E : ℕ)
    (h : (ι → O) →ₗ[O] B) (hp : ∀ x z, h x = π ^ (E + 1) • z → ∀ i, π ∣ x i) :
    GR ι π h E := by
  classical
  have hx' : ∀ x z, h x = π ^ (E + 1) • z → ∃ x', x = π • x' := by
    intro x z hxz
    refine ⟨fun i => (hp x z hxz i).choose, funext fun i => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul]
    exact (hp x z hxz i).choose_spec
  have hker : LinearMap.ker h = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {π}) _
      (IsNoetherian.noetherian _)
    · intro x hx
      rw [LinearMap.mem_ker] at hx
      obtain ⟨x', rfl⟩ := hx' x 0 (by rw [hx, smul_zero])
      have : h x' = 0 := by
        rw [map_smul] at hx
        exact (smul_eq_zero.mp hx).resolve_left hπ.ne_zero
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self π) this
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le,
        Set.singleton_subset_iff]
      exact hπ.not_isUnit
  obtain ⟨n, snf⟩ := Submodule.smithNormalForm (Module.Free.chooseBasis O B) (LinearMap.range h)
  let eH : (ι → O) ≃ₗ[O] LinearMap.range h :=
    LinearEquiv.ofInjective h (LinearMap.ker_eq_bot.mp hker)
  have heH : ∀ x, ((eH x : LinearMap.range h) : B) = h x := fun x => rfl
  have hdvd : ∀ i, snf.a i ∣ π ^ E := by
    intro i
    by_contra hnd
    obtain ⟨c, hc⟩ := pow_succ_dvd_of_not_dvd hπ hnd
    have hy : h (eH.symm (snf.bN i)) = (snf.bN i : B) := by
      rw [← heH, LinearEquiv.apply_symm_apply]
    obtain ⟨y', hy'⟩ := hx' (eH.symm (snf.bN i)) (c • snf.bM (snf.f i))
      (by rw [hy, snf.snf i, hc, smul_smul])
    have hb : snf.bN i = π • eH y' := by
      rw [← map_smul, ← hy', LinearEquiv.apply_symm_apply]
    have h1 := congrArg (fun m => snf.bN.repr m i) hb
    simp only [Basis.repr_self, Finsupp.single_eq_same, map_smul, Finsupp.smul_apply,
      smul_eq_mul] at h1
    exact hπ.not_isUnit (isUnit_of_dvd_one ⟨_, h1⟩)
  choose c hc using hdvd
  let w : B →ₗ[O] (Fin n → O) := LinearMap.pi (fun i => c i • snf.bM.coord (snf.f i))
  have key : w ∘ₗ (LinearMap.range h).subtype = (π ^ E) • snf.bN.equivFun.toLinearMap := by
    apply snf.bN.ext
    intro i
    funext j
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, snf.snf i, map_smul,
      LinearMap.smul_apply, LinearEquiv.coe_coe, Basis.equivFun_self, w, LinearMap.pi_apply,
      Basis.coord_apply, Basis.repr_self, Pi.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp [hc i, mul_comm]
    · have : snf.f i ≠ snf.f j := fun h => hij (snf.f.injective h)
      simp [this, hij]
  refine ⟨LinearMap.id, eH.symm.toLinearMap ∘ₗ snf.bN.equivFun.symm.toLinearMap ∘ₗ w, ?_⟩
  apply LinearMap.ext
  intro x
  have hk := LinearMap.congr_fun key (eH x)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, heH, LinearMap.smul_apply,
    LinearEquiv.coe_coe] at hk
  simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
    hk, map_smul, LinearEquiv.symm_apply_apply]

theorem split {B : Type} [AddCommGroup B] [Module O B] {π : O} (hπ : Irreducible π) (E σ : ℕ)
    (g : (Fin σ → O) →ₗ[O] B) :
    ∃ (p : Fin σ → Prop) (j0 : ({k // p k} → O) →ₗ[O] (Fin σ → O))
      (j1 : ({k // ¬ p k} → O) →ₗ[O] (Fin σ → O)),
      (∀ x, ∃ z, g (j0 x) = π ^ (E + 1) • z) ∧
      (∀ x y, j0 x = π • y → ∀ i, π ∣ x i) ∧
      (∀ x z, g (j1 x) = π ^ (E + 1) • z → ∀ i, π ∣ x i) := by
  classical
  let Z0 : Submodule O (Fin σ → O) :=
    { carrier := {x | ∃ z, g x = π ^ (E + 1) • z}
      add_mem' := by
        rintro a b ⟨z1, h1⟩ ⟨z2, h2⟩
        exact ⟨z1 + z2, by rw [map_add, h1, h2, smul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r a ⟨z, hz⟩
        exact ⟨r • z, by rw [map_smul, hz, smul_comm]⟩ }
  have hZ : ∀ x, x ∈ Z0 ↔ ∃ z, g x = π ^ (E + 1) • z := fun x => Iff.rfl
  obtain ⟨n, snf⟩ := Submodule.smithNormalForm (Pi.basisFun O (Fin σ)) Z0
  let p : Fin σ → Prop := fun k => ∃ i, snf.f i = k ∧ IsUnit (snf.a i)
  let e0 : ({k // p k} → O) →ₗ[O] (Fin σ → O) :=
    LinearMap.pi (fun k => if hk : p k then LinearMap.proj (⟨k, hk⟩ : {k // p k}) else 0)
  let e1 : ({k // ¬ p k} → O) →ₗ[O] (Fin σ → O) :=
    LinearMap.pi (fun k => if hk : ¬ p k then LinearMap.proj (⟨k, hk⟩ : {k // ¬ p k}) else 0)
  have he0 : ∀ x (i : {k // p k}), e0 x i.1 = x i := by
    intro x i
    simp [e0, i.2]
  have he0' : ∀ x (k : Fin σ), ¬ p k → e0 x k = 0 := by
    intro x k hk
    simp [e0, hk]
  have he1 : ∀ x (i : {k // ¬ p k}), e1 x i.1 = x i := by
    intro x i
    simp [e1, i.2]
  have hcoef : ∀ F k, snf.bM.repr (snf.bM.equivFun.symm F) k = F k := by
    intro F k
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  refine ⟨p, snf.bM.equivFun.symm.toLinearMap ∘ₗ e0,
    snf.bM.equivFun.symm.toLinearMap ∘ₗ e1, ?_, ?_, ?_⟩
  · intro x
    rw [← hZ]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.equivFun_symm_apply]
    refine Submodule.sum_mem _ (fun k _ => ?_)
    by_cases hk : p k
    · obtain ⟨i, rfl, u, hu⟩ := hk
      have hmem : snf.bM (snf.f i) ∈ Z0 := by
        have hb : snf.bM (snf.f i) = ((u⁻¹ : Oˣ) : O) • (snf.bN i : Fin σ → O) := by
          rw [snf.snf i, smul_smul, ← hu, Units.inv_mul, one_smul]
        rw [hb]
        exact Z0.smul_mem _ (snf.bN i).2
      exact Z0.smul_mem _ hmem
    · rw [he0' x k hk, zero_smul]
      exact Z0.zero_mem
  · intro x y hxy i
    have h1 := congrArg (fun m => snf.bM.repr m i.1) hxy
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hcoef, he0, map_smul,
      Finsupp.smul_apply, smul_eq_mul] at h1
    exact ⟨_, h1⟩
  · intro x z hxz i
    have hm : (snf.bM.equivFun.symm.toLinearMap ∘ₗ e1) x ∈ Z0 := (hZ _).mpr ⟨z, hxz⟩
    have hc : snf.bM.repr ((snf.bM.equivFun.symm.toLinearMap ∘ₗ e1) x) i.1 = x i := by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hcoef, he1]
    by_cases hr : i.1 ∈ Set.range snf.f
    · obtain ⟨j, hj⟩ := hr
      have h2 : snf.bM.repr ((snf.bM.equivFun.symm.toLinearMap ∘ₗ e1) x) (snf.f j) =
          snf.bN.repr (snf.a j • (⟨_, hm⟩ : Z0)) j :=
        snf.repr_apply_embedding_eq_repr_smul (⟨_, hm⟩ : Z0) (i := j)
      rw [hj, map_smul, Finsupp.smul_apply, smul_eq_mul, hc] at h2
      have hnu : ¬ IsUnit (snf.a j) := fun hu => i.2 ⟨j, hj, hu⟩
      have hπa : π ∣ snf.a j := by
        have hmax : snf.a j ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hnu
        rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
          Ideal.mem_span_singleton] at hmax
        exact hmax
      rw [h2]
      exact Dvd.dvd.mul_right hπa _
    · have h3 : snf.bM.repr ((snf.bM.equivFun.symm.toLinearMap ∘ₗ e1) x) i.1 = 0 :=
        snf.repr_eq_zero_of_notMem_range ⟨_, hm⟩ hr
      rw [hc] at h3
      rw [h3]
      exact dvd_zero π

end GoodRankMultinomialDepth

open GoodRankMultinomialDepth in

theorem wach_cohomology_top_S : LemmaS := by
  intro O _ _ _ π hπ C Cp R R'' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ io ph ps D ρp σ np h1 h2 h3
  classical
  obtain ⟨u1, v1, huv1⟩ := h1
  obtain ⟨u2, v2, huv2⟩ := h2
  have e1 : ∀ y, v1 (ps (ph (u1 y))) = π ^ D • y := fun y => LinearMap.congr_fun huv1 y
  have e2 : ∀ x, v2 (ph (io (u2 x))) = π ^ D • x := fun x => LinearMap.congr_fun huv2 x
  obtain ⟨p, j0, j1, hi, hii, hiii⟩ := split hπ (2 * D) σ (ps ∘ₗ ph ∘ₗ io ∘ₗ u2)
  have hgood : GR {k // ¬ p k} π (ps ∘ₗ ph ∘ₗ io) (2 * D) :=
    gr_comp (u2 ∘ₗ j1) (gr_of_primitive hπ (2 * D) _ (fun x z hxz => hiii x z hxz))
  let hmap : ({k // p k} ⊕ Fin ρp → O) →ₗ[O] Cp :=
    io ∘ₗ u2 ∘ₗ j0 ∘ₗ LinearMap.funLeft O O Sum.inl + u1 ∘ₗ LinearMap.funLeft O O Sum.inr
  have hbad : GR ({k // p k} ⊕ Fin ρp) π ph (2 * D) := by
    refine gr_comp hmap (gr_of_primitive hπ (2 * D) _ ?_)
    intro w z hwz
    have hw : ph (io (u2 (j0 (fun k => w (Sum.inl k))))) + ph (u1 (fun k => w (Sum.inr k))) =
        π ^ (2 * D + 1) • z := by
      rw [← map_add]
      exact hwz
    suffices H : ∀ (x : {k // p k} → O) (y : Fin ρp → O),
        ph (io (u2 (j0 x))) + ph (u1 y) = π ^ (2 * D + 1) • z →
        (∀ k, π ∣ x k) ∧ ∀ k, π ∣ y k by
      obtain ⟨hx, hy⟩ := H _ _ hw
      rintro (k | k)
      · exact hx k
      · exact hy k
    intro x y hw
    obtain ⟨z0, hz0⟩ := hi x
    have hz0' : ps (ph (io (u2 (j0 x)))) = π ^ (2 * D + 1) • z0 := hz0
    have hy1 : ps (ph (u1 y)) = π ^ (2 * D + 1) • (ps z - z0) := by
      have := congrArg ps hw
      rw [map_add, map_smul] at this
      rw [smul_sub, ← this, ← hz0']
      abel
    have hy2 : π ^ D • y = π ^ D • (π ^ (D + 1) • v1 (ps z - z0)) := by
      rw [← e1, hy1, map_smul, smul_smul, ← pow_add, show D + (D + 1) = 2 * D + 1 by ring]
    have hy : y = π ^ (D + 1) • v1 (ps z - z0) :=
      smul_right_injective _ (pow_ne_zero D hπ.ne_zero) hy2
    have hw' : ph (io (u2 (j0 x))) + ph (u1 y) = π ^ (2 * D + 1) • z := hw
    have hx1 : ph (io (u2 (j0 x))) = π ^ (D + 1) • (π ^ D • z - ph (u1 (v1 (ps z - z0)))) := by
      rw [smul_sub, smul_smul, ← pow_add, show D + 1 + D = 2 * D + 1 by ring, ← hw', hy,
        map_smul, map_smul]
      abel
    have hjx : j0 x = π • v2 (π ^ D • z - ph (u1 (v1 (ps z - z0)))) := by
      have := e2 (j0 x)
      rw [hx1, map_smul, pow_succ, mul_smul] at this
      exact (smul_right_injective _ (pow_ne_zero D hπ.ne_zero) this).symm
    refine ⟨hii x _ hjx, fun k => ?_⟩
    rw [hy, Pi.smul_apply, smul_eq_mul]
    exact Dvd.dvd.mul_right (dvd_pow_self π (Nat.succ_ne_zero D)) _
  have hcard := h3 _ (gr_goodRank hbad)
  rw [Fintype.card_sum, Fintype.card_fin] at hcard
  have hle := Fintype.card_subtype_le p
  have hsum := Fintype.card_subtype_compl p
  rw [Fintype.card_fin] at hle hsum
  apply goodRank_mono (gr_goodRank hgood)
  omega

end Formalism.CountingSumsFrames
