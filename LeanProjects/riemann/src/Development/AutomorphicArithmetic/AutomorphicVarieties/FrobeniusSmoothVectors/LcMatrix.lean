import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section LC

variable {T A C : Type} [TopologicalSpace T] [CommRing A] [CommRing C] {n : ℕ}

private theorem lc_matrix {B : Type} {f : T → Matrix (Fin n) (Fin n) B}
    (h : ∀ a b, IsLocallyConstant fun s => f s a b) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hall : ∀ᶠ y in nhds x, ∀ a b, f y a b = f x a b :=
    Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b =>
      (IsLocallyConstant.iff_eventually_eq _).1 (h a b) x
  filter_upwards [hall] with y hy
  ext a b
  exact hy a b

private theorem lc_gl {I : Ideal A} {f : T → GL (Fin n) A} (h : ∀ a b, AdicCont I fun s => f s a b) (N : ℕ) :
    IsLocallyConstant fun s => GeneralLinearGroup.map (Ideal.Quotient.mk (I ^ N)) (f s) := by
  apply IsLocallyConstant.desc _ (fun u : GL (Fin n) (A ⧸ I ^ N) => (u : Matrix (Fin n) (Fin n) (A ⧸ I ^ N)))
  · apply lc_matrix
    intro a b
    simpa [Function.comp_def] using h a b N
  · exact fun u v huv => Units.ext huv

private theorem mem_ker (p : A →+* C) {u : GL (Fin n) A} (h : GeneralLinearGroup.map p u = 1) (i j : Fin n) :
    ((u : Matrix (Fin n) (Fin n) A) - 1) i j ∈ RingHom.ker p := by
  rw [RingHom.mem_ker]
  have he := congrArg (fun v : GL (Fin n) C => (v : Matrix (Fin n) (Fin n) C) i j) h
  simp only [GeneralLinearGroup.map_apply, Units.val_one] at he
  rw [Matrix.sub_apply, map_sub, he, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem lc_ker [IsNoetherianRing A] {I K : Ideal A} (hs : I * K = ⊥) {f : T → GL (Fin n) A}
    (hf : ∀ s a b, ((f s : Matrix (Fin n) (Fin n) A) - 1) a b ∈ K)
    (h : ∀ N, IsLocallyConstant fun s => GeneralLinearGroup.map (Ideal.Quotient.mk (I ^ N)) (f s)) :
    IsLocallyConstant fun s => (f s : Matrix (Fin n) (Fin n) A) - 1 := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (K : Submodule A A)
  have h0 : ∀ x ∈ I ^ (k + 1), x ∈ K → x = 0 := by
    intro x hxm hxK
    have hx : x ∈ I ^ (k + 1) • (⊤ : Submodule A A) ⊓ (K : Submodule A A) := by
      refine ⟨?_, hxK⟩
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
      exact hxm
    rw [hk (k + 1) (by omega), Nat.add_sub_cancel_left, pow_one] at hx
    have hle : I • (I ^ k • (⊤ : Submodule A A) ⊓ (K : Submodule A A)) ≤ I • (K : Submodule A A) :=
      Submodule.smul_mono le_rfl inf_le_right
    have hx' := hle hx
    rw [Ideal.smul_eq_mul, hs] at hx'
    exact (Submodule.mem_bot A).1 hx'
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (h (k + 1)) s] with s' hs'
  ext a b
  have he := congrArg
    (fun v : GL (Fin n) (A ⧸ I ^ (k + 1)) => (v : Matrix (Fin n) (Fin n) (A ⧸ I ^ (k + 1))) a b) hs'
  simp only [GeneralLinearGroup.map_apply] at he
  have hd := Ideal.Quotient.eq.1 he
  have hK : (f s' : Matrix (Fin n) (Fin n) A) a b - (f s : Matrix (Fin n) (Fin n) A) a b ∈ K := by
    have := sub_mem (hf s' a b) (hf s a b)
    simpa [Matrix.sub_apply] using this
  rw [Matrix.sub_apply, Matrix.sub_apply, sub_eq_zero.1 (h0 _ hd hK)]

private theorem map_sgn (f : A →+* C) (s : ℤˣ) (g : GL (Fin n) A) :
    GeneralLinearGroup.map f (sgnAct n A s g) = sgnAct n C s (GeneralLinearGroup.map f g) := by
  by_cases hs : s = 1
  · subst hs
    simp
  · have hA : sgnAct n A s = thetaAut n A := by
      simp [sgnAct, hs]
    have hC : sgnAct n C s = thetaAut n C := by
      simp [sgnAct, hs]
    rw [hA, hC]
    exact map_theta f g

private theorem lc_hom {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (φ : G →* H) (h : IsOpen (φ.ker : Set G)) : IsLocallyConstant φ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h1 : ∀ᶠ z in nhds (1 : G), z ∈ (φ.ker : Set G) := h.mem_nhds (one_mem _)
  have hc : Filter.Tendsto (fun y => x⁻¹ * y) (nhds x) (nhds 1) := by
    have := (continuous_mul_left x⁻¹).tendsto x
    rwa [inv_mul_cancel] at this
  filter_upwards [hc.eventually h1] with y hy
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hy
  exact hy.symm

end LC

theorem UpperTheory.V.Fr.pr_omk :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C) (D : SetLift p B), maximalIdeal C' * RingHom.ker p = ⊥ → (∀ x i j, D.om x i j ∈ RingHom.ker p) ∧ (∀ v s i j, D.a v s i j ∈ RingHom.ker p) ∧ IsLocallyConstant D.om ∧ ∀ v, IsLocallyConstant (D.a v) := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B D hker
  have hgrp : ∀ s t, (B.r (s * t)).left = (B.r s).left * sgnAct n C (F.del s) (B.r t).left := by
    intro s t
    rw [map_mul, SemidirectProduct.mul_left, B.nu]
  have hom1 : ∀ x : F.Γ × F.Γ, GeneralLinearGroup.map (p : C' →+* C)
      (D.r x.1 * sgnAct n C' (F.del x.1) (D.r x.2) * (D.r (x.1 * x.2))⁻¹) = 1 := by
    intro x
    rw [map_mul, map_mul, map_inv, map_sgn, D.r_map, D.r_map, D.r_map, hgrp, mul_inv_cancel]
  have ha1 : ∀ v s, GeneralLinearGroup.map (p : C' →+* C)
      (D.r (F.loc v s) * ((D.g v)⁻¹ * D.t v s * D.g v)⁻¹) = 1 := by
    intro v s
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, D.r_map, D.g_map, D.t_map]
    group
  haveI : IsNoetherianRing C' := IsCO.toIsNoetherian O
  have hrc : ∀ N, IsLocallyConstant fun s : F.Γ =>
      GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal C' ^ N)) (D.r s) :=
    fun N => lc_gl (fun a b => D.r_cont a b) N
  have hdel : IsLocallyConstant F.del := lc_hom F.del hF.del_open
  refine ⟨fun x i j => mem_ker _ (hom1 x) i j, fun v s i j => mem_ker _ (ha1 v s) i j, ?_, ?_⟩
  · have := lc_ker hker
      (f := fun x : F.Γ × F.Γ => D.r x.1 * sgnAct n C' (F.del x.1) (D.r x.2) * (D.r (x.1 * x.2))⁻¹)
      (fun x a b => mem_ker _ (hom1 x) a b) (by
        intro N
        have e1 := (hrc N).comp_continuous (continuous_fst (X := F.Γ) (Y := F.Γ))
        have e2 := (hrc N).comp_continuous (continuous_snd (X := F.Γ) (Y := F.Γ))
        have e3 := (hrc N).comp_continuous (continuous_mul (M := F.Γ))
        have e4 := hdel.comp_continuous (continuous_fst (X := F.Γ) (Y := F.Γ))
        have := IsLocallyConstant.comp₂
          (IsLocallyConstant.comp₂ e1 (IsLocallyConstant.comp₂ e4 e2
            fun s g => sgnAct n (C' ⧸ maximalIdeal C' ^ N) s g) (· * ·)) e3 (fun a b => a * b⁻¹)
        convert this using 1
        funext x
        simp [Function.comp, map_sgn])
    exact this
  · intro v
    have hloc : Continuous (F.loc v) := continuous_subtype_val.comp (hF.loc_cont v)
    have := lc_ker hker
      (f := fun s : F.Gv v => D.r (F.loc v s) * ((D.g v)⁻¹ * D.t v s * D.g v)⁻¹)
      (fun s a b => mem_ker _ (ha1 v s) a b) (by
        intro N
        have e1 := (hrc N).comp_continuous hloc
        have e2 := lc_gl (fun a b => D.t_cont v a b) N
        have := IsLocallyConstant.comp₂ e1 e2 (fun a b => a *
          ((GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal C' ^ N)) (D.g v))⁻¹ * b *
            GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal C' ^ N)) (D.g v))⁻¹)
        convert this using 1
        funext s
        simp [Function.comp])
    exact this
