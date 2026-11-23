import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PClassD

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P

namespace Formalism.L2.Geo.Def.PC

section LG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

theorem lg (Λ : Submodule (𝓞 E) (n → E)) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤)
    (y : n → 𝒜) (hy : ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (y i)) ∈ latV v Λ) :
    y ∈ latA (F := F) Λ := by
  classical
  obtain ⟨c₁, hc₁, h₁⟩ := adelstabL_lower (F := F) Λ hspan
  choose d0 hd0 hd0m using fun i => levelaf_denom (F := F) (E := E) (y i)
  have hE : ∀ v, (fun i => afsplitEps E v * y i) ∈ latA (F := F) Λ := by
    intro v
    have := ie_lat v Λ _ (hy v)
    simpa only [afsplit_decomp] using this
  have h3 : ∀ i, levelafC E (∏ j, d0 j) * y i ∈ 𝒮 := by
    intro i
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm (d0 i), levelafC_mul, mul_assoc]
    exact mul_mem (levelafC_mem _) (hd0m i)
  have h4 := h₁ _ h3
  obtain ⟨T, u, hu, h1⟩ := unit_away (c₁ * ∏ j, d0 j)
    (mul_ne_zero hc₁ (Finset.prod_ne_zero_iff.2 fun j _ => hd0 j))
  have hu' : (1 : E) ⊗ₜ[F] u ∈ 𝒮 := Subring.subset_closure (Or.inr ⟨⟨u, hu⟩, rfl⟩)
  have hone : (1 : 𝒜) = ((1 : E) ⊗ₜ[F] u) * levelafC E (c₁ * ∏ j, d0 j) + ∑ v ∈ T, afsplitEps E v := by
    rw [Algebra.TensorProduct.one_def]
    conv_lhs => rw [h1]
    rw [TensorProduct.tmul_add, TensorProduct.tmul_sum]
    congr 1
    rw [levelafC, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm u]
  have hy' : y = (⟨_, hu'⟩ : 𝒮) • (fun i => levelafC E c₁ * (levelafC E (∏ j, d0 j) * y i)) +
      ∑ v ∈ T, (fun i => afsplitEps E v * y i) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Subring.smul_def, smul_eq_mul]
    conv_lhs => rw [← one_mul (y i), hone]
    rw [levelafC_mul, add_mul, Finset.sum_mul]
    ring
  rw [hy']
  exact add_mem (Submodule.smul_mem _ _ h4) (sum_mem fun v _ => hE v)

omit [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
theorem mem_stab_of {A R : Type} [CommRing A] [CommRing R] [Algebra R A] (Λ : Submodule R (n → A)) (g : GL n A)
    (h1 : ∀ x ∈ Λ, (g : Matrix n n A) *ᵥ x ∈ Λ)
    (h2 : ∀ x ∈ Λ, ((g⁻¹ : GL n A) : Matrix n n A) *ᵥ x ∈ Λ) : g ∈ stabGL Λ := by
  unfold stabGL
  refine fun x => ⟨h1 x, fun hx => ?_⟩
  have h3 := h2 _ hx
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h3

theorem pr_mulVec (v : HeightOneSpectrum (𝓞 F)) (x : GL n 𝒜) (y : n → 𝒜) :
    (fun i => prV (E := E) v (((x : Matrix n n 𝒜) *ᵥ y) i)) =
      ((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ
        (fun i => prV (E := E) v (y i)) := by
  unfold prV bc
  funext i
  rw [Units.coe_map]
  exact RingHom.map_mulVec _ _ _ i

private theorem prV_inclE' (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV (E := E) v (inclE (F := F) 𝔸 e) = inclE (F := F) (v.adicCompletion F) e := by
  simp [prV, inclE, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul]

private theorem stabGL_latA_pr_of_mem (Λ : Submodule (𝓞 E) (n → E)) (x : GL n 𝒜)
    (hx : x ∈ stabGL (latA (F := F) Λ)) (v : HeightOneSpectrum (𝓞 F)) (z : n → E ⊗[F] v.adicCompletion F)
    (hz : z ∈ latV v Λ) :
    ((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈
      latV v Λ := by
  have hx' : ∀ y : n → 𝒜, y ∈ latA (F := F) Λ ↔ (x : Matrix n n 𝒜) *ᵥ y ∈ latA (F := F) Λ := hx
  unfold latV latS at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have hmem : (fun i => inclE (F := F) 𝔸 (l i)) ∈ latA (F := F) Λ :=
      Submodule.subset_span ⟨l, hl, rfl⟩
    have h2 := pr_lat (F := F) v Λ _ ((hx' _).1 hmem)
    rw [pr_mulVec] at h2
    have e : (fun i => prV (E := E) v (inclE (F := F) 𝔸 (l i))) =
        (fun i => inclE (F := F) (v.adicCompletion F) (l i)) := funext fun i => prV_inclE' v (l i)
    rw [e] at h2
    exact h2
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul s a _ ha =>
    have e : ((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) :
          Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ (s • a) =
        s • (((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) :
          Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ a) := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e]
    exact Submodule.smul_mem _ s ha

theorem stab_pr (Λ : Submodule (𝓞 E) (n → E)) (x : GL n 𝒜) (hx : x ∈ stabGL (latA (F := F) Λ))
    (v : HeightOneSpectrum (𝓞 F)) : bc (prV (E := E) v) x ∈ stabGL (latV v Λ) := by
  have hxi : x⁻¹ ∈ stabGL (latA (F := F) Λ) := inv_mem hx
  have key : ∀ z : n → E ⊗[F] v.adicCompletion F, z ∈ latV v Λ ↔
      ((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) :
        Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈ latV v Λ := by
    intro z
    refine ⟨stabGL_latA_pr_of_mem Λ x hx v z, fun hz => ?_⟩
    have h := stabGL_latA_pr_of_mem Λ x⁻¹ hxi v _ hz
    rwa [map_inv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at h
  exact key

theorem stab_of_loc (Λ : Submodule (𝓞 E) (n → E)) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤)
    (x : GL n 𝒜) (hx : ∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) x ∈ stabGL (latV v Λ)) :
    x ∈ stabGL (latA (F := F) Λ) := by
  have fwd : ∀ g : GL n 𝒜, (∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) g ∈ stabGL (latV v Λ)) →
      ∀ y ∈ latA (F := F) Λ, (g : Matrix n n 𝒜) *ᵥ y ∈ latA (F := F) Λ := by
    intro g hg y hy
    refine lg (F := F) Λ hspan _ fun v => ?_
    rw [pr_mulVec]
    have hgv : ∀ z : n → E ⊗[F] v.adicCompletion F, z ∈ latV v Λ ↔
        ((bc (prV (E := E) v) g : GL n (E ⊗[F] v.adicCompletion F)) :
          Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈ latV v Λ := hg v
    exact (hgv _).1 (pr_lat (F := F) v Λ y hy)
  refine mem_stab_of (latA (F := F) Λ) x (fwd x hx) (fwd x⁻¹ fun v => ?_)
  rw [map_inv]
  exact inv_mem (hx v)

theorem kstLoc (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E))
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (x : GL n 𝒜) :
    x ∈ levelAfL σ J Λ ↔ x ∈ UPts σ J 𝔸 ∧ ∀ v, bc (prV (E := E) v) x ∈ levelVL σ J v Λ := by
  simp only [levelAfL, levelVL, level, Subgroup.mem_inf]
  constructor
  · rintro ⟨hU, hS⟩
    refine ⟨hU, fun v => ⟨?_, stab_pr Λ x hS v⟩⟩
    have hU' : cT (sigR σ 𝔸) (x : Matrix n n 𝒜) * J.map (inclE (F := F) 𝔸) * (x : Matrix n n 𝒜) =
        J.map (inclE (F := F) 𝔸) := hU
    have hcomm : ∀ a : 𝒜, prV (E := E) v (sigR σ 𝔸 a) = sigR σ (v.adicCompletion F) (prV (E := E) v a) := by
      intro a
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul e r => simp [prV, sigR, Algebra.TensorProduct.map_tmul]
      | add a b ha hb => simp only [map_add, ha, hb]
    have eJ : J.map (inclE (F := F) (v.adicCompletion F)) =
        (J.map (inclE (F := F) 𝔸)).map (prV (E := E) v) := by
      ext i j
      simp [Matrix.map_apply, prV_inclE']
    have eC : cT (sigR σ (v.adicCompletion F)) ((x : Matrix n n 𝒜).map (prV (E := E) v)) =
        (cT (sigR σ 𝔸) (x : Matrix n n 𝒜)).map (prV (E := E) v) := by
      ext i j
      simp [cT, Matrix.map_apply, Matrix.transpose_apply, hcomm]
    show cT (sigR σ (v.adicCompletion F)) ((x : Matrix n n 𝒜).map (prV (E := E) v)) *
        J.map (inclE (F := F) (v.adicCompletion F)) * (x : Matrix n n 𝒜).map (prV (E := E) v) =
      J.map (inclE (F := F) (v.adicCompletion F))
    rw [eC, eJ, ← Matrix.map_mul, ← Matrix.map_mul, hU']
  · rintro ⟨hU, hV⟩
    exact ⟨hU, stab_of_loc Λ hspan x fun v => (hV v).2⟩

theorem levelafC_nat (N : ℕ) : levelafC E ((N : ℕ) : 𝓞 F) = (N : 𝒜) := by
  unfold levelafC
  rw [map_natCast]
  first
    | (rw [← Algebra.TensorProduct.includeRight_apply, map_natCast])
    | simp
    | norm_cast

theorem gen_lat (Λ : Submodule (𝓞 E) (n → E)) {p : ℕ} (w : Fin p → Λ)
    (hw : Submodule.span (𝓞 E) (Set.range w) = ⊤) (y : n → 𝒜) (hy : y ∈ latA (F := F) Λ) :
    ∃ s : Fin p → 𝒮, y = ∑ l, s l • (fun i => inclE (F := F) 𝔸 ((w l : n → E) i)) := by
  unfold latA latS at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨lam, hlam, rfl⟩ := hz
    have hmem : (⟨lam, hlam⟩ : Λ) ∈ Submodule.span (𝓞 E) (Set.range w) := by
      rw [hw]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hmem
    have hs : ∀ l, inclE (F := F) 𝔸 (algebraMap (𝓞 E) E (c l)) ∈ 𝒮 := by
      intro l
      unfold tensInt
      apply Subring.subset_closure
      left
      exact ⟨⟨algebraMap (𝓞 E) E (c l), RingHom.mem_range.2 ⟨c l, rfl⟩⟩, rfl⟩
    refine ⟨fun l => ⟨_, hs l⟩, ?_⟩
    have hl : lam = ∑ l, c l • (w l : n → E) := by
      have := congrArg Subtype.val hc
      simpa using this.symm
    funext i
    show inclE (F := F) 𝔸 (lam i) = _
    rw [hl]
    simp [Finset.sum_apply, Subring.smul_def, Algebra.smul_def, map_sum, map_mul]
    exact Finset.sum_congr rfl fun l _ => rfl
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨t, rfl⟩ := hb
    exact ⟨s + t, by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul r a _ ha =>
    obtain ⟨s, rfl⟩ := ha
    exact ⟨fun l => r * s l, by simp [Finset.smul_sum, mul_smul]⟩

end LG

end Formalism.L2.Geo.Def.PC
