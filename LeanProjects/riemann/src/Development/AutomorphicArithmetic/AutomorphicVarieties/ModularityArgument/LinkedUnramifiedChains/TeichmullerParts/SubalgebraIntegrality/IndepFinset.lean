import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType

open scoped TensorProduct

namespace UpperTheory.V.Z.J.D

section SlopeTestRemainingChoices

variable {G W W' : Type} [Group G] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

private lemma stable_eq {τ : Representation ℂ G W'} (hτ : τ.IsIrreducible) (P : Submodule ℂ W')
    (hP : ∀ g, ∀ v ∈ P, τ g v ∈ P) : P = ⊥ ∨ P = ⊤ := by
  haveI : IsSimpleOrder (Subrepresentation τ) := hτ
  rcases eq_bot_or_eq_top (⟨P, fun g _ hv => hP g _ hv⟩ : Subrepresentation τ) with h | h
  · left
    exact congrArg Subrepresentation.toSubmodule h
  · right
    exact congrArg Subrepresentation.toSubmodule h

private lemma indep_fin {τ : Representation ℂ G W'} {ρ : Representation ℂ G W} (hτ : AbsIrr τ) :
    ∀ (n : ℕ) (b : Fin n → (W' →ₗ[ℂ] W)), (∀ i, Intw τ ρ (b i)) → LinearIndependent ℂ b →
      ∀ u : Fin n → W', ∑ i, b i (u i) = 0 → u = 0 := by
  intro n
  induction n with
  | zero => intro b _ _ u _; exact Subsingleton.elim _ _
  | succ n ih =>
    intro b hb hli u hu
    have hli' : LinearIndependent ℂ fun i : Fin n => b i.succ :=
      hli.comp _ (Fin.succ_injective n)
    have ih' := ih (fun i => b i.succ) (fun i => hb i.succ) hli'
    let A : (Fin n → W') →ₗ[ℂ] W := ∑ i, (b i.succ) ∘ₗ LinearMap.proj i
    have hA : ∀ v, A v = ∑ i, b i.succ (v i) := fun v => by simp [A, LinearMap.sum_apply]
    have hAinj : Function.Injective A := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      exact ih' v (by rw [← hA]; exact hv)
    have hAeq : ∀ g v, A (fun i => τ g (v i)) = ρ g (A v) := fun g v => by
      rw [hA, hA, map_sum]
      exact Finset.sum_congr rfl fun i _ => hb i.succ g (v i)
    have hsum : b 0 (u 0) + A (fun i => u i.succ) = 0 := by
      rw [hA, ← hu, Fin.sum_univ_succ]
    let P : Submodule ℂ W' := (LinearMap.range A).comap (b 0)
    have hP : ∀ g, ∀ v ∈ P, τ g v ∈ P := by
      rintro g v ⟨y, hy⟩
      refine ⟨fun i => τ g (y i), ?_⟩
      rw [hAeq, hy]
      exact (hb 0 g v).symm
    rcases stable_eq hτ.1 P hP with h | h
    · have h0 : u 0 = 0 := by
        have : u 0 ∈ P := ⟨-fun i => u i.succ, by
          rw [map_neg]; exact (eq_neg_of_add_eq_zero_left hsum |>.symm ▸ rfl)⟩
        rw [h] at this
        simpa using this
      have h1 : (fun i : Fin n => u i.succ) = 0 := by
        apply ih'
        rw [← hA, ← hsum, h0]
        simp
      funext i
      refine Fin.cases h0 (fun j => ?_) i
      exact congrFun h1 j
    · exfalso
      have hall : ∀ v, ∃ y, A y = b 0 v := fun v => by
        have : v ∈ P := h ▸ Submodule.mem_top
        exact this
      choose T hT using hall
      have hTadd : ∀ v v', T (v + v') = T v + T v' := fun v v' =>
        hAinj (by rw [map_add, hT, hT, hT, map_add])
      have hTsmul : ∀ (a : ℂ) v, T (a • v) = a • T v := fun a v =>
        hAinj (by rw [map_smul, hT, hT, map_smul])
      have hTg : ∀ g v i, T (τ g v) i = τ g (T v i) := fun g v i => by
        have : T (τ g v) = fun i => τ g (T v i) :=
          hAinj (by rw [hAeq, hT, hT]; exact hb 0 g v)
        exact congrFun this i
      have hc : ∀ i : Fin n, ∃ a : ℂ, ∀ v, T v i = a • v := fun i => by
        obtain ⟨a, ha⟩ := hτ.2
          { toFun := fun v => T v i
            map_add' := fun v v' => by rw [hTadd]; rfl
            map_smul' := fun a v => by rw [hTsmul]; rfl } (fun g v => hTg g v i)
        exact ⟨a, fun v => by simpa using LinearMap.congr_fun ha v⟩
      choose c hc using hc
      have hrel : ∑ i, (Fin.cons (1 : ℂ) (fun j => -c j) : Fin (n + 1) → ℂ) i • b i = 0 := by
        rw [Fin.sum_univ_succ]
        ext v
        simp only [Fin.cons_zero, Fin.cons_succ, one_smul, LinearMap.add_apply, LinearMap.sum_apply,
          LinearMap.smul_apply, LinearMap.zero_apply, neg_smul, Finset.sum_neg_distrib]
        rw [← hT v, hA]
        simp only [hc, map_smul]
        simp
      have := Fintype.linearIndependent_iff.1 hli _ hrel 0
      simp at this

private lemma indep_finset {τ : Representation ℂ G W'} {ρ : Representation ℂ G W} (hτ : AbsIrr τ)
    {κ : Type} (b : κ → (W' →ₗ[ℂ] W)) (hb : ∀ i, Intw τ ρ (b i)) (hli : LinearIndependent ℂ b)
    (s : Finset κ) (u : κ → W') (hu : ∑ i ∈ s, b i (u i) = 0) : ∀ i ∈ s, u i = 0 := by
  let e : Fin s.card ≃ s := s.equivFin.symm
  have h := indep_fin hτ s.card (fun j => b (e j)) (fun j => hb _)
    (hli.comp _ (Subtype.val_injective.comp e.injective)) (fun j => u (e j)) (by
      rw [e.sum_comp (fun i : s => b i (u i)), Finset.sum_coe_sort s fun i => b i (u i)]
      exact hu)
  intro i hi
  have := congrFun h (e.symm ⟨i, hi⟩)
  simpa using this

end SlopeTestRemainingChoices

section Main

variable {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

private def intwSub (τ : Representation ℂ G W') (ρ : Representation ℂ G W) : Submodule ℂ (W' →ₗ[ℂ] W) where
  carrier := {f | Intw τ ρ f}
  add_mem' {f f'} h h' g v := by simp [h g v, h' g v]
  zero_mem' g v := by simp
  smul_mem' a f h g v := by simp [h g v]

private lemma comm_inl (ρ : Representation ℂ (G × H) W) (g : G) (h : H) (w : W) :
    ρ (g, 1) (ρ (1, h) w) = ρ (1, h) (ρ (g, 1) w) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  simp

private def kap (ρ : Representation ℂ (G × H) W) (τ : Representation ℂ G W') :
    Representation ℂ H (intwSub τ (ρ.comp (MonoidHom.inl G H))) where
  toFun h :=
    { toFun := fun φ => ⟨ρ (1, h) ∘ₗ φ.1, fun g v => by
        have := φ.2 g v
        simp only [LinearMap.comp_apply, MonoidHom.comp_apply, MonoidHom.inl_apply] at this ⊢
        rw [this, comm_inl]⟩
      map_add' := fun φ φ' => by ext; simp
      map_smul' := fun a φ => by ext; simp }
  map_one' := by
    ext φ v
    show ρ (1, 1) (φ.1 v) = φ.1 v
    rw [Prod.mk_one_one, map_one]
    rfl
  map_mul' h h' := by
    ext φ v
    show ρ (1, h * h') (φ.1 v) = ρ (1, h) (ρ (1, h') (φ.1 v))
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]

private def evl (τ : Representation ℂ G W') (ρ : Representation ℂ G W) :
    W' ⊗[ℂ] intwSub τ ρ →ₗ[ℂ] W :=
  TensorProduct.lift (LinearMap.flip (Submodule.subtype (intwSub τ ρ)))

private lemma evl_tmul (τ : Representation ℂ G W') (ρ : Representation ℂ G W) (w : W') (φ : intwSub τ ρ) :
    evl τ ρ (w ⊗ₜ φ) = φ.1 w := by
  simp [evl]

private lemma evl_inj {τ : Representation ℂ G W'} {ρ : Representation ℂ G W} (hτ : AbsIrr τ) :
    Function.Injective (evl τ ρ) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  let B := Module.Basis.ofVectorSpace ℂ (intwSub τ ρ)
  let e := TensorProduct.equivFinsuppOfBasisRight (M := W') B
  have hz' : z = (e z).sum fun i w => w ⊗ₜ B i := by
    have := TensorProduct.equivFinsuppOfBasisRight_symm_apply B (e z)
    rw [← this, e.symm_apply_apply]
  have hsum : ∑ i ∈ (e z).support, (B i).1 (e z i) = 0 := by
    rw [← hz]
    conv_rhs => rw [hz']
    rw [Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => (evl_tmul τ ρ _ _).symm
  have hli : LinearIndependent ℂ fun i => (B i).1 :=
    B.linearIndependent.map' (intwSub τ ρ).subtype (Submodule.ker_subtype _)
  have h0 := indep_finset hτ (fun i => (B i).1) (fun i => (B i).2) hli _ (e z) hsum
  have : e z = 0 := by
    ext i
    by_cases hi : i ∈ (e z).support
    · simpa using h0 i hi
    · simpa using hi
  simpa using this

private lemma evl_surj {τ : Representation ℂ G W'} {ρ : Representation ℂ G W} (hI : Isot ρ τ) :
    Function.Surjective (evl τ ρ) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  refine hI.trans (iSup_le fun f => ?_)
  rintro _ ⟨w, rfl⟩
  exact ⟨w ⊗ₜ ⟨f.1, f.2⟩, evl_tmul τ ρ w ⟨f.1, f.2⟩⟩

end Main

theorem step :
    Step := by
  intro G H W W' _ _ _ _ _ _ ρ τ hτ hI
  refine ⟨intwSub τ (ρ.comp (MonoidHom.inl G H)), inferInstance, inferInstance, kap ρ τ,
    LinearEquiv.ofBijective (evl τ _) ⟨evl_inj hτ, evl_surj hI⟩, ?_⟩
  rintro ⟨g, h⟩ z
  show evl τ _ (box τ (kap ρ τ) (g, h) z) = ρ (g, h) (evl τ _ z)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul w φ =>
    have := φ.2 g w
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply] at this
    show evl τ _ (τ g w ⊗ₜ kap ρ τ h φ) = _
    rw [evl_tmul, evl_tmul]
    show ρ (1, h) (φ.1 (τ g w)) = _
    rw [this, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

end UpperTheory.V.Z.J.D
