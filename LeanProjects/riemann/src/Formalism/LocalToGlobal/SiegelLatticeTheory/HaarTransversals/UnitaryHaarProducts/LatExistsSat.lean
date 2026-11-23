import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsDefs
import Lemmata.MiscLemmasD.Imports

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.SG.Pf.LatEx

section Sat

variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]

local notation "𝓕" => FractionalIdeal (nonZeroDivisors (𝓞 E)) E

def lineV (c : 𝓕) (v : V) : Submodule (𝓞 E) V :=
  Submodule.span (𝓞 E) {y | ∃ x : E, x ∈ c ∧ y = x • v}

lemma mem_lineV (c : 𝓕) (v : V) {x : E} (hx : x ∈ c) : x • v ∈ lineV c v := Submodule.subset_span ⟨x, hx, rfl⟩

lemma latSpanV_succ {n : ℕ} (c : Fin (n + 1) → 𝓕) (v : Fin (n + 1) → V) :
    latSpanV c v = latSpanV (Fin.init c) (Fin.init v) ⊔ lineV (c (Fin.last n)) (v (Fin.last n)) := by
  unfold latSpanV lineV
  rw [← Submodule.span_union]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_union, Fin.exists_fin_succ', Fin.init]

lemma latSpanV_zero (c : Fin 0 → 𝓕) (v : Fin 0 → V) : latSpanV c v = ⊥ := by
  unfold latSpanV
  rw [Submodule.span_eq_bot]
  rintro _ ⟨i, -⟩
  exact i.elim0

lemma fi_neg_mem {I : 𝓕} {x : E} (h : x ∈ I) : -x ∈ I := FractionalIdeal.mem_coe.1 (Submodule.neg_mem _ (FractionalIdeal.mem_coe.2 h))

lemma fi_mul_mem {I J K : 𝓕} (hIJ : I * J = K) {x y : E} (hx : x ∈ I) (hy : y ∈ J) :
    x * y ∈ K := hIJ ▸ FractionalIdeal.mul_mem_mul hx hy

lemma exists_smul_mem_of_mem_span {Λ : Submodule (𝓞 E) V} {v : V}
    (hv : v ∈ Submodule.span E (Λ : Set V)) : ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by
  first | exact Bl.SecondBlockLemmaE.goal1 .. | (apply Bl.SecondBlockLemmaE.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaE.goal1 <;> assumption)

lemma sub_smul_mem_span_init {n : ℕ} (w : Fin (n + 1) → V) (f : V →ₗ[E] E)
    (hf1 : f (w (Fin.last n)) = 1) (hf0 : ∀ i : Fin n, f (w i.castSucc) = 0) {x : V}
    (hx : x ∈ Submodule.span E (Set.range w)) :
    x - f x • w (Fin.last n) ∈ Submodule.span E (Set.range (Fin.init w)) := by
  obtain ⟨k, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
  rw [Fin.sum_univ_castSucc]
  have hfx : f (∑ i : Fin n, k i.castSucc • w i.castSucc + k (Fin.last n) • w (Fin.last n)) =
      k (Fin.last n) := by
    simp [map_sum, hf0, hf1]
  rw [hfx, add_sub_cancel_right]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

lemma exists_coord {n : ℕ} (w : Fin (n + 1) → V) (hw : LinearIndependent E w) :
    ∃ f : V →ₗ[E] E, f (w (Fin.last n)) = 1 ∧ ∀ i : Fin n, f (w i.castSucc) = 0 := by
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Finsupp.lapply (Fin.last n)).comp hw.repr)
  refine ⟨g, ?_, fun i => ?_⟩
  · have h := congrArg (fun h => h ⟨w (Fin.last n), Submodule.subset_span ⟨_, rfl⟩⟩) hg
    simpa [hw.repr_eq_single (Fin.last n) ⟨w (Fin.last n), Submodule.subset_span ⟨_, rfl⟩⟩ rfl] using h
  · have hne := (Fin.castSucc_lt_last i).ne
    have h := congrArg (fun h => h ⟨w i.castSucc, Submodule.subset_span ⟨_, rfl⟩⟩) hg
    simpa [hw.repr_eq_single i.castSucc ⟨w i.castSucc, Submodule.subset_span ⟨_, rfl⟩⟩ rfl, Finsupp.single_apply, hne] using h

lemma peel {n : ℕ} (w : Fin (n + 1) → V) (hw : LinearIndependent E w) (M : Submodule (𝓞 E) V)
    (hM : M.FG) (hMX : M ≤ (Submodule.span E (Set.range w)).restrictScalars (𝓞 E))
    {d : 𝓞 E} (hd : d ≠ 0) (hdw : d • w (Fin.last n) ∈ M) :
    ∃ (b : 𝓕) (u : V), b ≠ 0 ∧
      M = M ⊓ (Submodule.span E (Set.range (Fin.init w))).restrictScalars (𝓞 E) ⊔ lineV b u := by
  classical
  obtain ⟨f, hf1, hf0⟩ := exists_coord w hw
  let g : V →ₗ[𝓞 E] E := f.restrictScalars (𝓞 E)
  let b : 𝓕 := ⟨M.map g, FractionalIdeal.isFractional_of_fg (hM.map g)⟩
  have hmemb : ∀ x : E, x ∈ b ↔ ∃ m ∈ M, f m = x := fun x => Submodule.mem_map
  have hsmul : ∀ (r : 𝓞 E) (v : V), f (r • v) = algebraMap (𝓞 E) E r * f v := fun r v => by
    rw [← algebraMap_smul E r v, map_smul, smul_eq_mul]
  have hdb : algebraMap (𝓞 E) E d ∈ b := (hmemb _).2 ⟨_, hdw, by rw [hsmul, hf1, mul_one]⟩
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at hdb
    exact hd (IsFractionRing.injective (𝓞 E) E (by rw [hdb, map_zero]))
  have key : ∀ z ∈ b * b⁻¹, ∃ u ∈ Submodule.span E (Set.range w),
      (∀ x ∈ b, x • u ∈ M) ∧ f u = z := by
    intro z hz
    refine FractionalIdeal.mul_induction_on hz ?_ ?_
    · intro i hi j hj
      obtain ⟨m, hmM, rfl⟩ := (hmemb i).1 hi
      refine ⟨j • m, Submodule.smul_mem _ _ (hMX hmM), fun x hx => ?_, ?_⟩
      · have hxj : x * j ∈ (1 : 𝓕) := by
          rw [← mul_inv_cancel₀ hb0]
          exact FractionalIdeal.mul_mem_mul hx hj
        obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hxj
        rw [smul_smul, ← hr, algebraMap_smul]
        exact M.smul_mem r hmM
      · rw [map_smul, smul_eq_mul, mul_comm]
    · rintro _ _ ⟨u1, hu1, h1, rfl⟩ ⟨u2, hu2, h2, rfl⟩
      refine ⟨u1 + u2, add_mem hu1 hu2, fun x hx => ?_, map_add f u1 u2⟩
      rw [smul_add]
      exact add_mem (h1 x hx) (h2 x hx)
  obtain ⟨u, huW, huM, hfu⟩ := key 1 (by
    rw [mul_inv_cancel₀ hb0]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩)
  refine ⟨b, u, hb0, le_antisymm ?_ ?_⟩
  · intro m hm
    have hfm : f m ∈ b := (hmemb _).2 ⟨m, hm, rfl⟩
    have hyW : m - f m • u ∈ Submodule.span E (Set.range w) :=
      sub_mem (hMX hm) (Submodule.smul_mem _ _ huW)
    have hfy : f (m - f m • u) = 0 := by
      rw [map_sub, map_smul, hfu, smul_eq_mul, mul_one, sub_self]
    have hy := sub_smul_mem_span_init w f hf1 hf0 hyW
    rw [hfy, zero_smul, sub_zero] at hy
    rw [show m = (m - f m • u) + f m • u by abel]
    exact Submodule.add_mem_sup ⟨sub_mem hm (huM _ hfm), hy⟩ (mem_lineV b u hfm)
  · refine sup_le inf_le_left (Submodule.span_le.2 ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact huM x hx

lemma coeffs (c1 c2 a : 𝓕) (h1 : c1 ≠ 0) (h2 : c2 ≠ 0) (ha : a ≠ 0) :
    ∃ α β γ δ : E, α ∈ a⁻¹ * c1 ∧ β ∈ a⁻¹ * c2 ∧ γ ∈ a * c2⁻¹ ∧ δ ∈ a * c1⁻¹ ∧
      α * δ - β * γ = 1 := by
  classical
  have hI0 : a⁻¹ * c1 ≠ 0 := mul_ne_zero (inv_ne_zero ha) h1
  have hJ0 : a⁻¹ * c2 ≠ 0 := mul_ne_zero (inv_ne_zero ha) h2
  obtain ⟨s, I0, hs, hIs⟩ := FractionalIdeal.exists_eq_spanSingleton_mul (a⁻¹ * c1)⁻¹
  obtain ⟨t, J0, ht, hJt⟩ := FractionalIdeal.exists_eq_spanSingleton_mul (a⁻¹ * c2)
  have hinj := IsFractionRing.injective (𝓞 E) E
  have hs' : algebraMap (𝓞 E) E s ≠ 0 := fun h => hs (hinj (by rw [h, map_zero]))
  have ht' : algebraMap (𝓞 E) E t ≠ 0 := fun h => ht (hinj (by rw [h, map_zero]))
  have hI0c : (I0 : 𝓕) ≠ 0 := right_ne_zero_of_mul (hIs ▸ inv_ne_zero hI0)
  have hJ0c : (J0 : 𝓕) ≠ 0 := right_ne_zero_of_mul (hJt ▸ hJ0)
  have hI0b : I0 ≠ ⊥ := fun h => hI0c (by rw [h]; exact FractionalIdeal.coeIdeal_bot)
  have hIJ : I0 * J0 ≠ 0 := by
    intro h
    apply mul_ne_zero hI0c hJ0c
    rw [← FractionalIdeal.coeIdeal_mul, h]
    exact FractionalIdeal.coeIdeal_bot
  obtain ⟨g, hg⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.mul_le_inf.trans inf_le_right : I0 * J0 ≤ J0) hIJ
  have hgJ : g ∈ J0 := hg ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)
  have hg' : (I0 : 𝓕) * (J0 : 𝓕) + FractionalIdeal.spanSingleton _ (algebraMap (𝓞 E) E g) = (J0 : 𝓕) := by
    rw [← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_span_singleton,
      ← FractionalIdeal.coeIdeal_sup, hg]
  have hsum : (I0 : 𝓕) + FractionalIdeal.spanSingleton _ (algebraMap (𝓞 E) E g) * (J0 : 𝓕)⁻¹ = 1 := by
    calc _ = ((I0 : 𝓕) * (J0 : 𝓕) + FractionalIdeal.spanSingleton _ (algebraMap (𝓞 E) E g)) * (J0 : 𝓕)⁻¹ := by
          rw [add_mul, mul_assoc, mul_inv_cancel₀ hJ0c, mul_one]
      _ = 1 := by rw [hg', mul_inv_cancel₀ hJ0c]
  have h1' : (1 : E) ∈ ((I0 : 𝓕) : Submodule (𝓞 E) E) ⊔
      ((FractionalIdeal.spanSingleton _ (algebraMap (𝓞 E) E g) * (J0 : 𝓕)⁻¹ : 𝓕) : Submodule (𝓞 E) E) := by
    rw [← Submodule.add_eq_sup, ← FractionalIdeal.coe_add, hsum]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1'
  obtain ⟨z', hz', rfl⟩ := FractionalIdeal.mem_singleton_mul.1 (FractionalIdeal.mem_coe.1 hz)
  have e1 : algebraMap (𝓞 E) E s * (algebraMap (𝓞 E) E s)⁻¹ = 1 := mul_inv_cancel₀ hs'
  have e2 : (algebraMap (𝓞 E) E t)⁻¹ * algebraMap (𝓞 E) E t = 1 := inv_mul_cancel₀ ht'
  refine ⟨algebraMap (𝓞 E) E s, (algebraMap (𝓞 E) E t)⁻¹ * algebraMap (𝓞 E) E g,
    -(algebraMap (𝓞 E) E t * z'), (algebraMap (𝓞 E) E s)⁻¹ * y, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← inv_inv (a⁻¹ * c1), hIs, mul_inv, FractionalIdeal.spanSingleton_inv, inv_inv,
      FractionalIdeal.mem_singleton_mul]
    exact ⟨1, FractionalIdeal.one_mem_inv_coe_ideal hI0b, (mul_one _).symm⟩
  · rw [hJt, FractionalIdeal.mem_singleton_mul]
    exact ⟨_, (FractionalIdeal.mem_coeIdeal _).2 ⟨g, hgJ, rfl⟩, rfl⟩
  · apply fi_neg_mem
    rw [show a * c2⁻¹ = (a⁻¹ * c2)⁻¹ by rw [mul_inv, inv_inv], hJt, mul_inv,
      FractionalIdeal.spanSingleton_inv, inv_inv, FractionalIdeal.mem_singleton_mul]
    exact ⟨z', hz', rfl⟩
  · rw [show a * c1⁻¹ = (a⁻¹ * c1)⁻¹ by rw [mul_inv, inv_inv], hIs, FractionalIdeal.mem_singleton_mul]
    exact ⟨y, FractionalIdeal.mem_coe.1 hy, rfl⟩
  · linear_combination hyz + y * e1 + algebraMap (𝓞 E) E g * z' * e2

lemma rebase (c1 c2 a : 𝓕) (h1 : c1 ≠ 0) (h2 : c2 ≠ 0) (ha : a ≠ 0) (p q : V) :
    ∃ u1 u2 : V, lineV c1 p ⊔ lineV c2 q = lineV a u1 ⊔ lineV (c1 * c2 * a⁻¹) u2 := by
  obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, hdet⟩ := coeffs c1 c2 a h1 h2 ha
  have E1 : a * (a⁻¹ * c1) = c1 := mul_inv_cancel_left₀ ha c1
  have E2 : a * (a⁻¹ * c2) = c2 := mul_inv_cancel_left₀ ha c2
  have E3 : c1 * c2 * a⁻¹ * (a * c2⁻¹) = c1 := by
    rw [show c1 * c2 * a⁻¹ * (a * c2⁻¹) = c1 * (c2 * c2⁻¹) * (a⁻¹ * a) by ac_rfl,
      mul_inv_cancel₀ h2, inv_mul_cancel₀ ha, mul_one, mul_one]
  have E4 : c1 * c2 * a⁻¹ * (a * c1⁻¹) = c2 := by
    rw [show c1 * c2 * a⁻¹ * (a * c1⁻¹) = c2 * (c1 * c1⁻¹) * (a⁻¹ * a) by ac_rfl,
      mul_inv_cancel₀ h1, inv_mul_cancel₀ ha, mul_one, mul_one]
  have E5 : c1 * (a * c1⁻¹) = a := by
    rw [show c1 * (a * c1⁻¹) = a * (c1 * c1⁻¹) by ac_rfl, mul_inv_cancel₀ h1, mul_one]
  have E6 : c1 * (a⁻¹ * c2) = c1 * c2 * a⁻¹ := by ac_rfl
  have E7 : c2 * (a * c2⁻¹) = a := by
    rw [show c2 * (a * c2⁻¹) = a * (c2 * c2⁻¹) by ac_rfl, mul_inv_cancel₀ h2, mul_one]
  have E8 : c2 * (a⁻¹ * c1) = c1 * c2 * a⁻¹ := by ac_rfl
  refine ⟨α • p + β • q, γ • p + δ • q, le_antisymm (sup_le ?_ ?_) (sup_le ?_ ?_)⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    have key : (x * (α * δ - β * γ)) • p =
        (x * δ) • (α • p + β • q) - (x * β) • (γ • p + δ • q) := by module
    rw [hdet, mul_one] at key
    rw [SetLike.mem_coe, key]
    exact sub_mem (Submodule.mem_sup_left (mem_lineV _ _ (fi_mul_mem E5 hx hδ)))
      (Submodule.mem_sup_right (mem_lineV _ _ (fi_mul_mem E6 hx hβ)))
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    have key : (x * (α * δ - β * γ)) • q =
        (-(x * γ)) • (α • p + β • q) + (x * α) • (γ • p + δ • q) := by module
    rw [hdet, mul_one] at key
    rw [SetLike.mem_coe, key]
    exact add_mem (Submodule.mem_sup_left (mem_lineV _ _ (fi_neg_mem (fi_mul_mem E7 hx hγ))))
      (Submodule.mem_sup_right (mem_lineV _ _ (fi_mul_mem E8 hx hα)))
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, smul_add, smul_smul, smul_smul]
    exact add_mem (Submodule.mem_sup_left (mem_lineV _ _ (fi_mul_mem E1 hx hα)))
      (Submodule.mem_sup_right (mem_lineV _ _ (fi_mul_mem E2 hx hβ)))
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, smul_add, smul_smul, smul_smul]
    exact add_mem (Submodule.mem_sup_left (mem_lineV _ _ (fi_mul_mem E3 hx hγ)))
      (Submodule.mem_sup_right (mem_lineV _ _ (fi_mul_mem E4 hx hδ)))

private lemma fg_of_le_lemma {M N : Submodule (𝓞 E) V} (hM : M.FG) (h : N ≤ M) : N.FG := by
  haveI := isNoetherian_of_fg_of_noetherian M hM
  have h1 : (Submodule.comap M.subtype N).FG := IsNoetherian.noetherian _
  have h2 := h1.map M.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.2 h] at h2

theorem adapted_basis (n : ℕ) : ∀ (w : Fin (n + 1) → V), LinearIndependent E w →
    ∀ (M : Submodule (𝓞 E) V), M.FG →
    M ≤ (Submodule.span E (Set.range w)).restrictScalars (𝓞 E) →
    (∀ i, ∃ d : 𝓞 E, d ≠ 0 ∧ d • w i ∈ M) →
    ∀ a : Fin n → 𝓕, (∀ i, a i ≠ 0) →
    ∃ (e : Fin (n + 1) → V) (c : 𝓕), c ≠ 0 ∧
      M = latSpanV (Fin.snoc (α := fun _ => 𝓕) a c) e := by
  induction n with
  | zero =>
    intro w hw M hM hMX hd a ha
    obtain ⟨d, hd0, hdw⟩ := hd (Fin.last 0)
    obtain ⟨b, u, hb, hMe⟩ := peel w hw M hM hMX hd0 hdw
    refine ⟨fun _ => u, b, hb, ?_⟩
    rw [latSpanV_succ, Fin.init_snoc, Fin.snoc_last, latSpanV_zero, bot_sup_eq]
    have hW : Submodule.span E (Set.range (Fin.init w)) = ⊥ := by
      rw [Set.range_eq_empty, Submodule.span_empty]
    rw [hW, Submodule.restrictScalars_bot, inf_bot_eq, bot_sup_eq] at hMe
    exact hMe
  | succ n ih =>
    intro w hw M hM hMX hd a ha
    obtain ⟨d, hd0, hdw⟩ := hd (Fin.last (n + 1))
    obtain ⟨b, u, hb, hMe⟩ := peel w hw M hM hMX hd0 hdw
    have hM'fg : (M ⊓ (Submodule.span E (Set.range (Fin.init w))).restrictScalars (𝓞 E)).FG :=
      fg_of_le_lemma hM inf_le_left
    have hind : LinearIndependent E (Fin.init w) := hw.comp _ (Fin.castSucc_injective _)
    have hd' : ∀ i, ∃ d : 𝓞 E, d ≠ 0 ∧ d • Fin.init w i ∈
        M ⊓ (Submodule.span E (Set.range (Fin.init w))).restrictScalars (𝓞 E) := by
      intro i
      obtain ⟨d, hd0, hdw⟩ := hd i.castSucc
      exact ⟨d, hd0, hdw, Submodule.smul_of_tower_mem _ d (Submodule.subset_span ⟨i, rfl⟩)⟩
    obtain ⟨e', c', hc', hM'⟩ := ih (Fin.init w) hind _ hM'fg inf_le_right hd' (Fin.init a)
      (fun i => ha _)
    obtain ⟨u1, u2, hre⟩ := rebase c' b (a (Fin.last n)) hc' hb (ha _) (e' (Fin.last n)) u
    refine ⟨Fin.snoc (Fin.snoc (Fin.init e') u1) u2, c' * b * (a (Fin.last n))⁻¹,
      mul_ne_zero (mul_ne_zero hc' hb) (inv_ne_zero (ha _)), ?_⟩
    rw [latSpanV_succ, Fin.init_snoc, Fin.init_snoc, Fin.snoc_last, Fin.snoc_last, latSpanV_succ,
      Fin.init_snoc, Fin.snoc_last]
    rw [hMe, hM', latSpanV_succ, Fin.init_snoc, Fin.snoc_last, sup_assoc, hre, ← sup_assoc]

lemma spanE_of_lat {ι : Type} (N : Submodule (𝓞 E) V) (g : ι → V) (Y : Submodule E V)
    (hNY : N ≤ Y.restrictScalars (𝓞 E)) (hY : Y ≤ Submodule.span E (Set.range g))
    (hg : ∀ i, ∃ t : E, t ≠ 0 ∧ t • g i ∈ N) : Submodule.span E (N : Set V) = Y := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact hNY hx
  · refine hY.trans ?_
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨t, ht, hti⟩ := hg i
    have h : g i = t⁻¹ • (t • g i) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [SetLike.mem_coe, h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hti)

end Sat

private lemma fi_exists_ne_lemma {R K : Type} [CommRing R] [Field K] [Algebra R K] {S : Submonoid R}
    {I : FractionalIdeal S K} (hI : I ≠ 0) : ∃ x ∈ I, x ≠ 0 := by
  by_contra h
  push_neg at h
  apply hI
  ext x
  rw [FractionalIdeal.mem_zero_iff]
  exact ⟨h x, fun hx => hx ▸ FractionalIdeal.mem_coe.1 (Submodule.zero_mem _)⟩

theorem satBasisV_holds : SatBasisV := by
  intro E V _ _ _ _ _ _ _ Λ hΛ n w hw a ha
  have hMfg : (Λ ⊓ (Submodule.span E (Set.range w)).restrictScalars (𝓞 E)).FG :=
    fg_of_le_lemma hΛ.fg inf_le_left
  have hd : ∀ i, ∃ d : 𝓞 E, d ≠ 0 ∧
      d • w i ∈ Λ ⊓ (Submodule.span E (Set.range w)).restrictScalars (𝓞 E) := by
    intro i
    have hwi : w i ∈ Submodule.span E (Λ : Set V) := by
      rw [hΛ.span_eq_top]; exact Submodule.mem_top
    obtain ⟨d, hd0, hdΛ⟩ := exists_smul_mem_of_mem_span hwi
    exact ⟨d, hd0, hdΛ, Submodule.smul_of_tower_mem _ d (Submodule.subset_span ⟨i, rfl⟩)⟩
  obtain ⟨e, c, hc, hMe⟩ := adapted_basis n w hw _ hMfg inf_le_right hd a ha
  have hinj := IsFractionRing.injective (𝓞 E) E
  have hspw : Submodule.span E ((Λ ⊓ (Submodule.span E (Set.range w)).restrictScalars (𝓞 E) :
      Submodule (𝓞 E) V) : Set V) = Submodule.span E (Set.range w) := by
    refine spanE_of_lat _ w _ inf_le_right le_rfl fun i => ?_
    obtain ⟨d, hd0, hdM⟩ := hd i
    exact ⟨algebraMap (𝓞 E) E d, fun h => hd0 (hinj (by rw [h, map_zero])),
      by rw [algebraMap_smul]; exact hdM⟩
  have hspe : Submodule.span E ((Λ ⊓ (Submodule.span E (Set.range w)).restrictScalars (𝓞 E) :
      Submodule (𝓞 E) V) : Set V) = Submodule.span E (Set.range e) := by
    refine spanE_of_lat _ e _ ?_ le_rfl fun i => ?_
    · rw [hMe]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, x, hx, rfl⟩
      exact Submodule.smul_mem _ x (Submodule.subset_span ⟨i, rfl⟩)
    · have hne : Fin.snoc (α := fun _ => FractionalIdeal (nonZeroDivisors (𝓞 E)) E) a c i ≠ 0 := by
        induction i using Fin.lastCases with
        | last => rw [Fin.snoc_last]; exact hc
        | cast j => rw [Fin.snoc_castSucc]; exact ha j
      obtain ⟨x, hx, hx0⟩ := fi_exists_ne_lemma hne
      exact ⟨x, hx0, by rw [hMe]; exact Submodule.subset_span ⟨i, x, hx, rfl⟩⟩
  have hew : Submodule.span E (Set.range e) = Submodule.span E (Set.range w) := hspe.symm.trans hspw
  refine ⟨e, c, ?_, hew, hc, hMe⟩
  rw [linearIndependent_iff_card_eq_finrank_span]
  unfold Set.finrank
  rw [hew, finrank_span_eq_card hw]

end Formalism.L2.SG.Pf.LatEx
