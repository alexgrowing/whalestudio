import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LinearIndependentOfCommSmul

namespace GlobalTheory.UU.SchurComp

theorem commutant_eq_sum {F : Type} [Field F] {A : Type} [CommGroup A] [Finite A] {E : Type} [AddCommGroup E]
    [Module F E] [FiniteDimensional F E] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E))
    (hdim : Module.finrank F E ^ 2 = Nat.card A)
    (hmul : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hcomm : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (hnd : ∀ a, (∀ b, e a b = 1) → a = 1)
    {H K : Type} [Fintype K] (m : H → A) (hm : Function.Injective m)
    (hc : Nat.card A ≤ Fintype.card K * Nat.card H) (P : K → E →ₗ[F] E) (hP0 : ∀ k, P k ≠ 0)
    (hP1 : ∀ k v, P k (P k v) = P k v) (hP2 : ∀ k l v, k ≠ l → P k (P l v) = 0)
    (hPΦ : ∀ k h v, P k (Φ (m h) v) = Φ (m h) (P k v)) (φ : E →ₗ[F] E)
    (hφ : ∀ h v, φ (Φ (m h) v) = Φ (m h) (φ v)) : ∃ c : K → F, ∑ k, c k • P k = φ := by
  classical
  have hApos : 0 < Nat.card A := Nat.card_pos
  haveI : Nontrivial E := by
    rw [← Module.finrank_pos_iff (R := F)]
    rcases Nat.eq_zero_or_pos (Module.finrank F E) with h | h
    · rw [h] at hdim; omega
    · exact h
  obtain ⟨u, hu0⟩ := exists_ne (0 : E)
  have hel : ∀ a b c, e (a * b) c = e a c * e b c := by
    intro a b c
    obtain ⟨k, hk⟩ := hmul a b
    have h1 := hcomm (a * b) c u
    rw [hk, hk, hcomm b c u, map_smul, hcomm a c, map_smul, smul_smul, smul_smul, smul_smul] at h1
    have h2 : Φ c (Φ a (Φ b u)) ≠ 0 := fun h => hu0 (by simpa using h)
    have h3 := smul_left_injective F h2 h1
    apply Units.ext
    have hk0 : (k : F) ≠ 0 := k.ne_zero
    apply mul_left_cancel₀ hk0
    rw [Units.val_mul]
    linear_combination -h3
  have hsk : ∀ a b, e a b * e b a = 1 := by
    intro a b
    have h1 := hcomm a b u
    rw [hcomm b a u, smul_smul] at h1
    have h2 : Φ a (Φ b u) ≠ 0 := fun h => hu0 (by simpa using h)
    have h3 := smul_left_injective F h2 ((one_smul F _).trans h1)
    exact Units.ext h3.symm
  have hinj : Function.Injective fun a b => (e a b : F) := by
    intro a a' h
    have he1 : ∀ c, e 1 c = 1 := by
      intro c
      have := hel 1 1 c
      rw [mul_one] at this
      exact (mul_eq_left.mp this.symm)
    have : a * a'⁻¹ = 1 := by
      apply hnd
      intro b
      have hb : e a b = e a' b := Units.ext (congrFun h b)
      rw [hel, hb, ← hel, mul_inv_cancel, he1]
    exact mul_inv_eq_one.mp this
  have hli : LinearIndependent F fun a => (Φ a : E →ₗ[F] E) :=
    linearIndependent_of_comm_smul _ _ (fun a => (Φ a).injective) (fun a b v => hcomm a b v) hinj
  haveI := Fintype.ofFinite A
  have hspan : Submodule.span F (Set.range fun a => (Φ a : E →ₗ[F] E)) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    rw [Module.finrank_linearMap, ← sq, hdim, Nat.card_eq_fintype_card]
  let C : Submodule F (E →ₗ[F] E) :=
    Submodule.span F (Set.range fun a : {a : A // ∀ h, e (m h) a = 1} => (Φ a.1 : E →ₗ[F] E))
  have hC : ∀ ψ : E →ₗ[F] E, (∀ h v, ψ (Φ (m h) v) = Φ (m h) (ψ v)) → ψ ∈ C := by
    intro ψ hψ
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp
      (hspan ▸ Submodule.mem_top : ψ ∈ Submodule.span F (Set.range fun a => (Φ a : E →ₗ[F] E)))
    rw [← hc]
    refine C.sum_mem fun a _ => ?_
    by_cases ha : ∀ h, e (m h) a = 1
    · exact C.smul_mem _ (Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩)
    · obtain ⟨h, hh⟩ := not_forall.1 ha
      have h0 : ∑ a, (c a * ((e (m h) a : F) - 1)) • (Φ a : E →ₗ[F] E) = 0 := by
        ext v
        obtain ⟨v, rfl⟩ := (Φ (m h)).surjective v
        have h1 := hψ h v
        rw [← hc] at h1
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, map_sum, map_smul,
          LinearMap.zero_apply] at h1 ⊢
        simp only [mul_sub, sub_smul, Finset.sum_sub_distrib, mul_one, h1]
        rw [sub_eq_zero]
        exact Finset.sum_congr rfl fun a _ => by rw [hcomm (m h) a, smul_smul]
      have h2 := Fintype.linearIndependent_iff.1 hli _ h0 a
      rcases mul_eq_zero.1 h2 with h3 | h3
      · rw [h3, zero_smul]; exact C.zero_mem
      · exact absurd (Units.ext (sub_eq_zero.1 h3)) hh

  let S : Subgroup A := Subgroup.closure (Set.range m)
  let χ : A → A →* Fˣ := fun a => MonoidHom.mk' (fun b => e b a) fun b b' => hel b b' a
  have hS : ∀ a : {a : A // ∀ h, e (m h) a = 1}, S ≤ (χ a.1).ker := fun a =>
    (Subgroup.closure_le _).2 (by rintro _ ⟨h, rfl⟩; exact a.2 h)
  let ω : {a : A // ∀ h, e (m h) a = 1} → (A ⧸ S →* F) := fun a =>
    (Units.coeHom F).comp (QuotientGroup.lift S (χ a.1) fun x hx => hS a hx)
  have hω : Function.Injective ω := fun a a' h => Subtype.ext (hinj (funext fun b => by
    have h1 : e b a.1 = e b a'.1 := Units.ext (DFunLike.congr_fun h (QuotientGroup.mk b))
    have h2 := hsk a.1 b
    rw [h1] at h2
    exact congrArg Units.val (mul_right_cancel (h2.trans (hsk a'.1 b).symm))))
  have hcard : Fintype.card {a : A // ∀ h, e (m h) a = 1} ≤ Fintype.card K := by
    have h1 := ((linearIndependent_monoidHom (A ⧸ S) F).comp ω hω).fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card (α := A ⧸ S)] at h1
    have h2 : Nat.card H ≤ Nat.card S := Nat.card_le_card_of_injective
      (fun h => (⟨m h, Subgroup.subset_closure ⟨h, rfl⟩⟩ : S)) fun a b h => hm (congrArg Subtype.val h)
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup S
    have h4 : 0 < Nat.card S := Nat.card_pos
    refine h1.trans (Nat.le_of_mul_le_mul_right ?_ h4)
    rw [← h3]
    exact hc.trans (Nat.mul_le_mul_left _ h2)
  have hPli : LinearIndependent F P := by
    refine Fintype.linearIndependent_iff.2 fun c hc k => ?_
    by_contra h0
    refine hP0 k (LinearMap.ext fun v => ?_)
    have h1 := congrArg (P k) (LinearMap.congr_fun hc v)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, LinearMap.zero_apply, map_zero] at h1
    rw [Finset.sum_eq_single k (fun l _ hl => by rw [hP2 k l v hl.symm, smul_zero]) (by simp), hP1] at h1
    exact (smul_eq_zero.1 h1).resolve_left h0
  have hle : Submodule.span F (Set.range P) ≤ C :=
    Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hC _ (hPΦ k))
  have heq : Submodule.span F (Set.range P) = C :=
    Submodule.eq_of_le_of_finrank_le hle (by
      rw [finrank_span_eq_card hPli]
      exact (finrank_range_le_card _).trans hcard)
  exact (Submodule.mem_span_range_iff_exists_fun F).mp (heq ▸ hC φ hφ)

theorem finrank_le_of_inj {F E Q : Type} [Field F] [AddCommGroup E] [Module F E] [AddCommGroup Q] [Module F Q]
    (W : Submodule F E) (f : E →ₗ[F] Q) (hf : ∀ v ∈ W, f v = 0 → v = 0) {n : ℕ} (b : Fin n → Q)
    (hb : ∀ v, f v ∈ Submodule.span F (Set.range b)) : Module.finrank F W ≤ n ∧
      (n ≤ Module.finrank F W → ∀ q ∈ Submodule.span F (Set.range b), ∃ v ∈ W, f v = q) := by
  haveI : FiniteDimensional F (Submodule.span F (Set.range b)) :=
    FiniteDimensional.span_of_finite F (Set.finite_range b)
  have h1 : Module.finrank F (Submodule.span F (Set.range b)) ≤ n :=
    (finrank_range_le_card b).trans (Fintype.card_fin n).le
  have hi : Function.Injective (f.domRestrict W) :=
    (injective_iff_map_eq_zero _).2 fun v hv => Subtype.ext (hf v.1 v.2 hv)
  have h2 := LinearMap.finrank_range_of_inj hi
  have hle : LinearMap.range (f.domRestrict W) ≤ Submodule.span F (Set.range b) := by
    rintro _ ⟨v, rfl⟩; exact hb v.1
  refine ⟨h2 ▸ (Submodule.finrank_mono hle).trans h1, fun hn q hq => ?_⟩
  rw [← Submodule.eq_of_le_of_finrank_le hle (h1.trans (h2 ▸ hn))] at hq
  obtain ⟨v, hv⟩ := hq
  exact ⟨v.1, v.2, hv⟩

theorem proportional_field {F : Type} [Field F] {A : Type} [CommGroup A] [Finite A] {E : Type} [AddCommGroup E]
    [Module F E] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E))
    (hdim : Module.finrank F E ^ 2 = Nat.card A)
    (hmul : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hcomm : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (hnd : ∀ a, (∀ b, e a b = 1) → a = 1)
    {H K : Type} [Finite K] (m : H → A) (hm : Function.Injective m)
    (hc : Nat.card A ≤ Nat.card K * Nat.card H) {n : ℕ} (hn : Nat.card K * n ≤ Module.finrank F E)
    {X Q : Type} [AddCommGroup Q] [Module F Q] (cl : X → K) (ex : X → E →ₗ[F] Q)
    (hinj : ∀ v, (∀ β, ex β v = 0) → v = 0)
    (hP : ∀ k v, ∃ v', ∀ β, (cl β = k → ex β v' = ex β v) ∧ (cl β ≠ k → ex β v' = 0))
    (hne : ∀ k, ∃ β, cl β = k ∧ ∃ v, ex β v ≠ 0)
    (h3 : ∀ β, (∃ v, ex β v ≠ 0) → ∀ v, (∀ γ, cl γ ≠ cl β → ex γ v = 0) → ex β v = 0 → v = 0)
    (hb : ∀ β, ∃ b : Fin n → Q, ∀ v, ex β v ∈ Submodule.span F (Set.range b))
    (hΦ : ∀ h β v, ex β v = 0 → ex β (Φ (m h) v) = 0)
    (α : X) (hα : ∃ v, ex α v ≠ 0) (f₁ f₂ : E →ₗ[F] Q) (hk : ∀ v, f₁ v = 0 ↔ ex α v = 0)
    (b : Fin n → Q) (hb₁ : ∀ v, f₁ v ∈ Submodule.span F (Set.range b))
    (hb₂ : ∀ v, f₂ v ∈ Submodule.span F (Set.range b))
    (hint : ∀ h v v', f₂ v = f₁ v' → f₂ (Φ (m h) v) = f₁ (Φ (m h) v')) : ∃ a : F, ∀ v, f₂ v = a • f₁ v := by
  classical
  haveI := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card (α := K)] at hc hn
  have hApos : 0 < Nat.card A := Nat.card_pos
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by
    rcases Nat.eq_zero_or_pos (Module.finrank F E) with h | h
    · rw [h] at hdim; omega
    · exact h)
  have hext : ∀ v v', (∀ β, ex β v = ex β v') → v = v' := fun v v' h =>
    sub_eq_zero.1 (hinj _ fun β => by rw [map_sub, h, sub_self])
  choose p hp using hP
  have hp' : ∀ k v β, ex β (p k v) = if cl β = k then ex β v else 0 := fun k v β => by
    split_ifs with h
    exacts [(hp k v β).1 h, (hp k v β).2 h]
  let P : K → E →ₗ[F] E := fun k =>
    { toFun := p k
      map_add' := fun v v' => hext _ _ fun β => by
        rw [map_add, hp', hp', hp']; split_ifs <;> simp
      map_smul' := fun c v => hext _ _ fun β => by
        rw [map_smul, hp', hp']; split_ifs <;> simp }
  have hP : ∀ k v β, ex β (P k v) = if cl β = k then ex β v else 0 := hp'
  have hP0 : ∀ k, P k ≠ 0 := fun k h => by
    obtain ⟨β, hβ, v, hv⟩ := hne k
    have := hP k v β
    rw [h, if_pos hβ] at this
    exact hv (this.symm.trans (map_zero _))
  have hP1 : ∀ k v, P k (P k v) = P k v := fun k v => hext _ _ fun β => by
    rw [hP, hP]; split_ifs <;> rfl
  have hP2 : ∀ k l v, k ≠ l → P k (P l v) = 0 := fun k l v hkl => hinj _ fun β => by
    rw [hP, hP]; split_ifs with h h'
    exacts [absurd (h.symm.trans h') hkl, rfl, rfl]
  have hPΦ : ∀ k h v, P k (Φ (m h) v) = Φ (m h) (P k v) := fun k h v => hext _ _ fun β => by
    rw [hP]
    split_ifs with hβ
    · have := hΦ h β (v - P k v) (by rw [map_sub, hP, if_pos hβ, sub_self])
      rwa [map_sub, map_sub, sub_eq_zero] at this
    · exact (hΦ h β _ (by rw [hP, if_neg hβ])).symm
  have hW : ∀ β, (∃ v, ex β v ≠ 0) → ∀ v ∈ LinearMap.range (P (cl β)), ex β v = 0 → v = 0 := by
    rintro β hβ _ ⟨v, rfl⟩
    exact h3 β hβ _ fun γ hγ => by rw [hP, if_neg hγ]
  have hle : ∀ k, Module.finrank F (LinearMap.range (P k)) ≤ n := fun k => by
    obtain ⟨β, rfl, hβ⟩ := hne k
    obtain ⟨b, hb⟩ := hb β
    exact (finrank_le_of_inj _ _ (hW β hβ) b hb).1
  have hge : n ≤ Module.finrank F (LinearMap.range (P (cl α))) := by
    have hi : Function.Injective (LinearMap.pi fun k => (P k).rangeRestrict) :=
      (injective_iff_map_eq_zero _).2 fun v hv => hinj _ fun β => by
        have h1 : P (cl β) v = 0 := congrArg Subtype.val (congrFun hv (cl β))
        have h2 := hP (cl β) v β
        rw [h1, if_pos rfl] at h2
        exact h2.symm.trans (map_zero _)
    have h1 := LinearMap.finrank_le_finrank_of_injective hi
    rw [Module.finrank_pi_fintype] at h1
    by_contra hlt
    have h2 : ∑ k, Module.finrank F (LinearMap.range (P k)) < ∑ _k : K, n :=
      Finset.sum_lt_sum (fun k _ => hle k) ⟨cl α, Finset.mem_univ _, not_le.1 hlt⟩
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h2
    omega
  have hW₁ : ∀ v ∈ LinearMap.range (P (cl α)), f₁ v = 0 → v = 0 := fun v hv h => hW α hα v hv ((hk v).1 h)
  have hext₁ : ∀ v ∈ LinearMap.range (P (cl α)), ∀ v' ∈ LinearMap.range (P (cl α)), f₁ v = f₁ v' → v = v' :=
    fun v hv v' hv' h => sub_eq_zero.1 (hW₁ _ (sub_mem hv hv') (by rw [map_sub, h, sub_self]))
  choose q hq hq' using fun v => (finrank_le_of_inj _ f₁ hW₁ b hb₁).2 hge _ (hb₂ v)
  let φ : E →ₗ[F] E :=
    { toFun := q
      map_add' := fun v v' => hext₁ _ (hq _) _ (add_mem (hq _) (hq _)) (by rw [map_add, hq', hq', hq', map_add])
      map_smul' := fun c v => hext₁ _ (hq _) _ (Submodule.smul_mem _ _ (hq _)) (by
        rw [map_smul, hq', hq', map_smul]; rfl) }
  obtain ⟨c, hc⟩ := commutant_eq_sum e Φ hdim hmul hcomm hnd m hm hc P hP0 hP1 hP2 hPΦ φ fun h v =>
    hext₁ _ (hq _) _ (by
      obtain ⟨x, hx⟩ := hq v
      exact ⟨Φ (m h) x, (hPΦ _ _ _).trans (congrArg _ hx)⟩) ((hq' _).trans (hint h v (q v) (hq' v).symm))
  refine ⟨c (cl α), fun v => ?_⟩
  rw [← hq' v]
  show f₁ (φ v) = _
  rw [← hc, LinearMap.sum_apply, map_sum, Finset.sum_eq_single (cl α) (fun l _ hl => by
    rw [LinearMap.smul_apply, map_smul, (hk _).2 (by rw [hP, if_neg hl.symm]), smul_zero]) (by simp),
    LinearMap.smul_apply, map_smul]
  congr 1
  have := (hk (P (cl α) v - v)).2 (by rw [map_sub, hP, if_pos rfl, sub_self])
  rwa [map_sub, sub_eq_zero] at this

theorem proportional {F : Type} [CommRing F] (hF : IsField F) {A : Type} [CommGroup A] [Finite A] {E : Type}
    [AddCommGroup E] [Module F E] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E))
    (hdim : Module.finrank F E ^ 2 = Nat.card A)
    (hmul : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hcomm : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (hnd : ∀ a, (∀ b, e a b = 1) → a = 1)
    {H K : Type} [Finite K] (m : H → A) (hm : Function.Injective m)
    (hc : Nat.card A ≤ Nat.card K * Nat.card H) {n : ℕ} (hn : Nat.card K * n ≤ Module.finrank F E)
    {X Q : Type} [CommRing Q] (ι : F →+* Q) (cl : X → K) (ex : X → E → Q)
    (hex : ∀ β c v v', ex β (c • v + v') = ι c * ex β v + ex β v')
    (hinj : ∀ v, (∀ β, ex β v = 0) → v = 0)
    (hP : ∀ k v, ∃ v', ∀ β, (cl β = k → ex β v' = ex β v) ∧ (cl β ≠ k → ex β v' = 0))
    (hne : ∀ k, ∃ β, cl β = k ∧ ∃ v, ex β v ≠ 0)
    (h3 : ∀ β, (∃ v, ex β v ≠ 0) → ∀ v, (∀ γ, cl γ ≠ cl β → ex γ v = 0) → ex β v = 0 → v = 0)
    (hb : ∀ β, ∃ b : Fin n → Q, ∀ v, ∃ c : Fin n → F, ex β v = ∑ i, ι (c i) * b i)
    (hΦ : ∀ h β v, ex β v = 0 → ex β (Φ (m h) v) = 0)
    (α α' : X) (hα : ∃ v, ex α v ≠ 0) (f₁ : E → Q) (hf₁ : ∀ c v v', f₁ (c • v + v') = ι c * f₁ v + f₁ v')
    (hk : ∀ v, f₁ v = 0 ↔ ex α v = 0)
    (b : Fin n → Q) (hb₁ : ∀ v, ∃ c : Fin n → F, f₁ v = ∑ i, ι (c i) * b i)
    (hb₂ : ∀ v, ∃ c : Fin n → F, ex α' v = ∑ i, ι (c i) * b i)
    (hint : ∀ h v v', ex α' v = f₁ v' → ex α' (Φ (m h) v) = f₁ (Φ (m h) v')) :
    ∃ a : F, ∀ v, ex α' v = ι a * f₁ v := by
  letI := hF.toField
  letI : Algebra F Q := ι.toAlgebra
  have mk : ∀ f : E → Q, (∀ c v v', f (c • v + v') = ι c * f v + f v') → ∃ g : E →ₗ[F] Q, ⇑g = f := fun f hf => by
    have h0 : f 0 = 0 := by
      have := hf 1 0 0
      rw [map_one, one_mul, one_smul, add_zero] at this
      exact left_eq_add.1 this
    exact ⟨⟨⟨f, fun v v' => by have := hf 1 v v'; rwa [map_one, one_mul, one_smul] at this⟩,
      fun c v => by have := hf c v 0; rwa [h0, add_zero, add_zero] at this⟩, rfl⟩
  have sp : ∀ (b : Fin n → Q) (q : Q), (∃ c : Fin n → F, q = ∑ i, ι (c i) * b i) →
      q ∈ Submodule.span F (Set.range b) := fun b q ⟨c, hc⟩ =>
    (Submodule.mem_span_range_iff_exists_fun F).2 ⟨c, hc.symm⟩
  choose ex' hex' using fun β => mk (ex β) (hex β)
  obtain rfl : ex = fun β => ⇑(ex' β) := funext fun β => (hex' β).symm
  obtain ⟨g₁, rfl⟩ := mk f₁ hf₁
  exact proportional_field e Φ hdim hmul hcomm hnd m hm hc hn cl ex' hinj hP hne h3
    (fun β => (hb β).imp fun b hb v => sp b _ (hb v)) hΦ α hα g₁ (ex' α') hk b (fun v => sp b _ (hb₁ v))
    (fun v => sp b _ (hb₂ v)) hint

end GlobalTheory.UU.SchurComp
