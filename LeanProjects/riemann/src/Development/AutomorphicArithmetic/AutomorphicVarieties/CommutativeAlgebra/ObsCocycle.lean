import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HhGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HhSmall
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

section Co

variable {A k ι : Type} [CommRing A] [CommRing k] [Fintype ι] [DecidableEq ι] {K : Ideal A} {σ co : A → k}

private theorem co_zero (h1 : ∀ x ∈ K, ∀ y ∈ K, co (x + y) = co x + co y) : co 0 = 0 := by
  have := h1 0 K.zero_mem 0 K.zero_mem
  rw [add_zero] at this
  exact left_eq_add.1 this

private theorem co_sum (h1 : ∀ x ∈ K, ∀ y ∈ K, co (x + y) = co x + co y) (S : Finset ι) (f : ι → A)
    (hf : ∀ c, f c ∈ K) : co (∑ c ∈ S, f c) = ∑ c ∈ S, co (f c) := by
  induction S using Finset.induction_on with
  | empty => simpa using co_zero h1
  | insert c S hc ih =>
    rw [Finset.sum_insert hc, Finset.sum_insert hc, h1 _ (hf c) _ (K.sum_mem fun c _ => hf c), ih]

omit [DecidableEq ι] in
private theorem mem_left (M : Matrix ι ι A) {Z : Matrix ι ι A} (hZ : ∀ a b, Z a b ∈ K) (a b : ι) : (M * Z) a b ∈ K := by
  rw [Matrix.mul_apply]
  exact K.sum_mem fun c _ => K.mul_mem_left _ (hZ _ _)

omit [DecidableEq ι] in
private theorem mem_right (M : Matrix ι ι A) {Z : Matrix ι ι A} (hZ : ∀ a b, Z a b ∈ K) (a b : ι) :
    (Z * M) a b ∈ K := by
  rw [Matrix.mul_apply]
  exact K.sum_mem fun c _ => K.mul_mem_right _ (hZ _ _)

private theorem co_left (h1 : ∀ x ∈ K, ∀ y ∈ K, co (x + y) = co x + co y) (h2 : ∀ a, ∀ x ∈ K, co (a * x) = σ a * co x)
    (M : Matrix ι ι A) {Z : Matrix ι ι A} (hZ : ∀ a b, Z a b ∈ K) : (M * Z).map co = M.map σ * Z.map co := by
  ext a b
  simp only [Matrix.map_apply, Matrix.mul_apply]
  rw [co_sum h1 _ _ fun c => K.mul_mem_left _ (hZ _ _)]
  exact Finset.sum_congr rfl fun c _ => h2 _ _ (hZ _ _)

private theorem co_right (h1 : ∀ x ∈ K, ∀ y ∈ K, co (x + y) = co x + co y) (h2 : ∀ a, ∀ x ∈ K, co (a * x) = σ a * co x)
    (M : Matrix ι ι A) {Z : Matrix ι ι A} (hZ : ∀ a b, Z a b ∈ K) : (Z * M).map co = Z.map co * M.map σ := by
  ext a b
  simp only [Matrix.map_apply, Matrix.mul_apply]
  rw [co_sum h1 _ _ fun c => K.mul_mem_right _ (hZ _ _)]
  exact Finset.sum_congr rfl fun c _ => by rw [mul_comm, h2 _ _ (hZ _ _), mul_comm]

omit [Fintype ι] [DecidableEq ι] in
private theorem co_add (h1 : ∀ x ∈ K, ∀ y ∈ K, co (x + y) = co x + co y)
    {Z Z' : Matrix ι ι A} (hZ : ∀ a b, Z a b ∈ K) (hZ' : ∀ a b, Z' a b ∈ K) :
    (Z + Z').map co = Z.map co + Z'.map co := by
  ext a b
  exact h1 _ (hZ _ _) _ (hZ' _ _)

end Co

section LC

variable {T A ι : Type} [TopologicalSpace T] [CommRing A] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem lc_matrix {B : Type} {f : T → Matrix ι ι B} (h : ∀ a b, IsLocallyConstant fun s => f s a b) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have : ∀ᶠ y in nhds x, ∀ a b, f y a b = f x a b :=
    Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => (h a b).eventually_eq x
  exact this.mono fun y hy => Matrix.ext hy

omit [DecidableEq ι] in
private theorem lc_ac {I : Ideal A} {f : T → Matrix ι ι A} (h : ∀ a b, AdicCont I fun s => f s a b) (N : ℕ) :
    IsLocallyConstant fun s => (f s).map (Ideal.Quotient.mk (I ^ N)) :=
  lc_matrix fun a b => h a b N

omit [Fintype ι] [DecidableEq ι] in
private theorem lc_ker [IsNoetherianRing A] {I K : Ideal A} (hs : I * K = ⊥) {f : T → Matrix ι ι A}
    (hf : ∀ s a b, f s a b ∈ K) (h : ∀ N, IsLocallyConstant fun s => (f s).map (Ideal.Quotient.mk (I ^ N))) :
    IsLocallyConstant f := by
  obtain ⟨n, hn⟩ := Ideal.exists_pow_inf_eq_pow_smul I (K : Submodule A A)
  have e := hn (n + 1) (Nat.le_succ n)
  have e2 : ∀ x ∈ K, x ∈ I ^ (n + 1) → x = 0 := fun x hx hx' => by
    have m : x ∈ (I ^ (n + 1) • (⊤ : Submodule A A)) ⊓ K := ⟨by simpa using hx', hx⟩
    rw [e, Nat.add_sub_cancel_left, pow_one] at m
    have : x ∈ I * K := Submodule.smul_mono le_rfl inf_le_right m
    rwa [hs, Ideal.mem_bot] at this
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  refine ((h (n + 1)).eventually_eq x).mono fun y hy => ?_
  ext a b
  have := congrFun (congrFun hy a) b
  exact sub_eq_zero.1 (e2 _ (K.sub_mem (hf _ _ _) (hf _ _ _)) (Ideal.Quotient.eq.1 this))

end LC

section G

variable {O : Type} [CommRing O] [IsLocalRing O] {ι X : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X] {w : ι → X}
  {A : Type} [CommRing A] [Algebra O A]

omit [IsLocalRing O] [DecidableEq ι] in
private theorem part_mul (W : WPres O X A) {M M' : Matrix ι ι A} (h : ∀ a b, M a b ∈ W.part (w a - w b))
    (h' : ∀ a b, M' a b ∈ W.part (w a - w b)) (a b : ι) : (M * M') a b ∈ W.part (w a - w b) := by
  rw [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun c _ => ?_
  have := SetLike.GradedMul.mul_mem (h a c) (h' c b)
  rwa [sub_add_sub_cancel] at this

omit [IsLocalRing O] [DecidableEq ι] [Fintype ι] in
private theorem part_alg (W : WPres O X A) {M : Matrix ι ι O} (h : ∀ a b, w a ≠ w b → M a b = 0) (a b : ι) :
    (M.map (algebraMap O A)) a b ∈ W.part (w a - w b) := by
  rw [Matrix.map_apply]
  by_cases e : w a = w b
  · rw [e, sub_self, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ SetLike.GradedOne.one_mem
  · rw [h a b e, map_zero]
    exact Submodule.zero_mem _

private theorem co_gw [IsCO O A] (Φ : FormData O w) (W : WPres O X A) {K : Ideal A} {j : X} {co : A → ResidueField O}
    (h1 : ∀ x ∈ K, ∀ y ∈ K, co (x + y) = co x + co y) (h2 : ∀ a, ∀ x ∈ K, co (a * x) = res O A a * co x)
    (h3 : ∀ j', j' ≠ j → ∀ x ∈ K, x ∈ W.part j' → co x = 0) {Y : Matrix ι ι A} (hK : ∀ a b, Y a b ∈ K)
    (hW : ∀ a b, Y a b ∈ W.part (w a - w b)) (hY : Y ∈ Φ.g A) : Y.map co ∈ Φ.gw (ResidueField O) j := by
  obtain ⟨y1, y2⟩ := hY
  have hJ : (Φ.JR A).map (res O A) = Φ.JR (ResidueField O) := by
    ext a b
    simp [FormData.JR]
  have hK' : ∀ a b, Y.transpose a b ∈ K := fun a b => hK b a
  refine ⟨⟨?_, fun a b e => ?_⟩, fun a b e => h3 _ e _ (hK a b) (hW a b)⟩
  · have := congrArg (fun M : Matrix ι ι A => M.map co) y1
    rw [co_add h1 (mem_right _ hK') (mem_left _ hK), co_left h1 h2 _ hK, co_right h1 h2 _ hK', hJ,
      Matrix.transpose_map] at this
    rw [this]
    ext a b
    exact co_zero h1
  · rw [Matrix.map_apply, y2 a b e, co_zero h1]

private theorem map_mul_alg {O R S ι : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    [Fintype ι] [DecidableEq ι] (f : R →ₐ[O] S) (A B : Matrix ι ι R) : (A * B).map f = A.map f * B.map f :=
  Matrix.map_mul (f := (f : R →+* S))

end G

theorem UpperTheory.V.Alg.obs_cocycle :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (F : Frame Γ) (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (p : A →ₐ[O] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (W : WPres O X A) (j : X) (co : A → ResidueField O),
          (∀ x ∈ RingHom.ker p, ∀ y ∈ RingHom.ker p, co (x + y) = co x + co y) → (∀ (a : A), ∀ x ∈ RingHom.ker p, co (a * x) = res O A a * co x) → (∀ j', j' ≠ j → ∀ x ∈ RingHom.ker p, x ∈ W.part j' → co x = 0) →
          ∀ (rt : Γ → Matrix ι ι A), (∀ s, Φ.HH (rt s * (r0.hom s⁻¹).map (algebraMap O A))) → (∀ a b, AdicCont (maximalIdeal A) fun s => rt s a b) → (∀ s a b, rt s a b ∈ W.part (w a - w b)) → (∀ s t, (rt s * rt t).map p = (rt (s * t)).map p) →
          ∀ (α : F.T → Matrix ι ι A) (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) A), (∀ v, Φ.HH (α v)) → (∀ v a b, α v a b ∈ W.part (w a - w b)) → (∀ v, Φ.InH (r0.hom.comp (F.φ v)) A (ρ v)) → (∀ v s a b, (ρ v).hom s a b ∈ W.part (w a - w b)) → (∀ v s, (rt (F.φ v s) * α v).map p = (α v * (ρ v).hom s).map p) →
          ∀ (rq : ∀ q, Lift O (rbar.comp (F.ψ q)) A), (∀ q, Φ.InH (r0.hom.comp (F.ψ q)) A (rq q)) → (∀ q s a b, (rq q).hom s a b ∈ W.part (w a - w b)) → (∀ q s, (rt (F.ψ q s)).map p = ((rq q).hom s).map p) →
          ∃ z ∈ F.framedTwoCocycles (FormData.adRep hbar j), (∀ s t, (z.1 (s, t)).1 * rbar (s * t) = (rt s * rt t - rt (s * t)).map co) ∧ (∀ v s, (z.2.1 v s).1 * rbar (F.φ v s) = (rt (F.φ v s) * α v - α v * (ρ v).hom s).map co) ∧ ∀ q s, (z.2.2 q s).1 * rbar (F.ψ q s) = (rt (F.ψ q s) - (rq q).hom s).map co := by
  intro O _ _ _ _ ι X _ _ _ w Φ h2 Γ _ _ _ rbar r0 hbar h0 F A _ _ _ R _ _ _ p hp hs W j co c1 c2 c3 rt t1 t2 t3 t4
    α ρ a1 a2 a3 a4 a5 rq q1 q2 q3
  obtain ⟨g1, g2, -, -, g5, -⟩ := hh_group O ι X w Φ A
  have g6 := g5 Γ r0.hom h0
  obtain ⟨-, s2, -⟩ := hh_small O ι X w Φ h2 A R p hp hs
  have r0res : ∀ s, ((r0.hom s).map (algebraMap O A)).map (res O A) = rbar s := fun s => by
    ext a b
    rw [Matrix.map_apply, Matrix.map_apply, AlgHom.commutes, ← r0.red, ← (res O O).commutes]
    rfl
  have r0inv : ∀ s, (r0.hom s⁻¹).map (algebraMap O A) * (r0.hom s).map (algebraMap O A) = 1 := fun s => by
    rw [← Matrix.map_mul, ← map_mul, inv_mul_cancel, map_one]; simp
  have rinv : ∀ s, rbar s⁻¹ * rbar s = 1 := fun s => by rw [← map_mul, inv_mul_cancel, map_one]
  have rtres : ∀ s, (rt s).map (res O A) = rbar s := fun s => by
    have := (t1 s).2.2
    rw [map_mul_alg, r0res] at this
    calc (rt s).map (res O A) = (rt s).map (res O A) * rbar s⁻¹ * rbar s := by rw [mul_assoc, rinv, mul_one]
      _ = rbar s := by rw [this, one_mul]
  have hker : ∀ {Z Z' : Matrix ι ι A}, Z.map p = Z'.map p → ∀ a b, (Z - Z') a b ∈ RingHom.ker p := by
    intro Z Z' e a b
    have := congrFun (congrFun e a) b
    rw [RingHom.mem_ker, Matrix.sub_apply, map_sub]
    exact sub_eq_zero.2 this
  have key : ∀ (s : Γ) (Z Z' : Matrix ι ι A), Φ.HH (Z * (r0.hom s⁻¹).map (algebraMap O A)) →
      Φ.HH (Z' * (r0.hom s⁻¹).map (algebraMap O A)) → Z.map p = Z'.map p →
      (∀ a b, Z a b ∈ W.part (w a - w b)) → (∀ a b, Z' a b ∈ W.part (w a - w b)) →
      (Z - Z').map co * rbar s⁻¹ ∈ Φ.gw (ResidueField O) j := by
    intro s Z Z' k1 k2 e w1 w2
    rw [← r0res, ← co_right c1 c2 _ (hker e)]
    refine co_gw Φ W c1 c2 c3 (mem_right _ (hker e))
      (part_mul W (fun a b => Submodule.sub_mem _ (w1 a b) (w2 a b)) (part_alg W (h0.2.2 _))) ?_
    rw [sub_mul]
    exact s2 _ _ k2 k1 (by rw [map_mul_alg, map_mul_alg, e])
  have lcbar : IsLocallyConstant rbar := by
    refine lc_matrix fun a b => ?_
    have := (r0.cont a b 1).comp (Ideal.Quotient.lift (maximalIdeal O ^ 1) (res O O : O →+* ResidueField O)
      fun x hx => (res_eq_zero_iff O O x).2 (by rwa [pow_one] at hx))
    convert this using 1
    funext s
    exact (r0.red s a b).symm
  have lcinv : IsLocallyConstant fun s : Γ => rbar s⁻¹ := lcbar.comp_continuous continuous_inv
  have lct := lc_ac t2
  have mD : ∀ x : Γ × Γ, (rt x.1 * rt x.2 - rt (x.1 * x.2)).map co * rbar (x.1 * x.2)⁻¹ ∈
      Φ.gw (ResidueField O) j := by
    rintro ⟨s, t⟩
    refine key _ _ _ ?_ (t1 _) (t4 s t) (part_mul W (t3 s) (t3 t)) (t3 _)
    convert g2 _ _ (t1 s) (g6 s _ (t1 t)) using 1
    simp only [mul_inv_rev, map_mul, Matrix.map_mul, mul_assoc]
    rw [← mul_assoc _ ((r0.hom s).map _), r0inv, one_mul]
  have lD : IsLocallyConstant fun x : Γ × Γ => (⟨_, mD x⟩ : Φ.gw (ResidueField O) j) := by
    refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
    have l1 : IsLocallyConstant fun x : Γ × Γ => rt x.1 * rt x.2 - rt (x.1 * x.2) := by
      refine lc_ker hs (fun x => hker (t4 x.1 x.2)) fun N => ?_
      simp only [Matrix.map_sub _ (map_sub (Ideal.Quotient.mk _)), Matrix.map_mul]
      exact (((lct N).comp_continuous continuous_fst).mul ((lct N).comp_continuous continuous_snd)).sub
        ((lct N).comp_continuous continuous_mul)
    exact (l1.comp (fun M => M.map co)).mul (lcinv.comp_continuous continuous_mul)
  have loc : ∀ (G : Type) [Group G] [TopologicalSpace G] (φ : G →* Γ), Continuous φ → ∀ (β : Matrix ι ι A)
      (τ : Lift O (rbar.comp φ) A), Φ.HH β → (∀ a b, β a b ∈ W.part (w a - w b)) → Φ.InH (r0.hom.comp φ) A τ →
      (∀ s a b, τ.hom s a b ∈ W.part (w a - w b)) → (∀ s, (rt (φ s) * β).map p = (β * τ.hom s).map p) →
      ∃ y : G → Φ.gw (ResidueField O) j, IsLocallyConstant y ∧
        (∀ s t, (⟨_, mD (φ s, φ t)⟩ : Φ.gw (ResidueField O) j) =
          dOne ((FormData.adRep hbar j).comp φ) y (s, t)) ∧
        ∀ s, (y s).1 * rbar (φ s) = (rt (φ s) * β - β * τ.hom s).map co := by
    intro G _ _ φ hφ β τ b1 b2 b3 b4 b5
    have mE : ∀ s, (rt (φ s) * β - β * τ.hom s).map co * rbar (φ s)⁻¹ ∈ Φ.gw (ResidueField O) j := by
      intro s
      refine key _ _ _ ?_ ?_ (b5 s) (part_mul W (t3 _) b2) (part_mul W b2 (b4 s))
      · convert g2 _ _ (t1 (φ s)) (g6 (φ s) _ b1) using 1
        simp only [mul_assoc]
        rw [← mul_assoc _ ((r0.hom (φ s)).map _), r0inv, one_mul]
      · have := g2 _ _ b1 (b3 s)
        rwa [MonoidHom.comp_apply, map_inv, ← mul_assoc] at this
    refine ⟨fun s => ⟨_, mE s⟩, ?_, fun s t => Subtype.ext ?_, fun s => ?_⟩
    · refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
      have l1 : IsLocallyConstant fun s => rt (φ s) * β - β * τ.hom s := by
        refine lc_ker hs (fun s => hker (b5 s)) fun N => ?_
        simp only [Matrix.map_sub _ (map_sub (Ideal.Quotient.mk _)), Matrix.map_mul]
        exact (((lct N).comp_continuous hφ).mul (IsLocallyConstant.const _)).sub
          ((IsLocallyConstant.const _).mul (lc_ac τ.cont N))
      exact (l1.comp (fun M => M.map co)).mul (lcinv.comp_continuous hφ)
    · have e : (rt (φ s) * β - β * τ.hom s) * τ.hom t + rt (φ s) * (rt (φ t) * β - β * τ.hom t) =
          (rt (φ s) * rt (φ t) - rt (φ s * φ t)) * β + (rt (φ (s * t)) * β - β * τ.hom (s * t)) := by
        simp only [map_mul]
        noncomm_ring
      have e' := congrArg (fun M : Matrix ι ι A => M.map co) e
      have τres : (τ.hom t).map (res O A) = rbar (φ t) := Matrix.ext fun a b => τ.red t a b
      rw [co_add c1 (mem_right _ (hker (b5 s))) (mem_left _ (hker (b5 t))),
        co_add c1 (mem_right _ (hker (t4 _ _))) (hker (b5 _)), co_right c1 c2 _ (hker (b5 s)),
        co_left c1 c2 _ (hker (b5 t)), co_right c1 c2 _ (hker (t4 _ _)), b1.2.2, τres, rtres, mul_one] at e'
      show (rt (φ s) * rt (φ t) - rt (φ s * φ t)).map co * rbar (φ s * φ t)⁻¹ =
        (rt (φ s) * β - β * τ.hom s).map co * rbar (φ s)⁻¹ +
        rbar (φ s) * ((rt (φ t) * β - β * τ.hom t).map co * rbar (φ t)⁻¹) * rbar (φ s)⁻¹ -
        (rt (φ (s * t)) * β - β * τ.hom (s * t)).map co * rbar (φ (s * t))⁻¹
      rw [eq_sub_iff_add_eq, map_mul φ s t]
      rw [map_mul φ s t] at e'
      rw [← add_mul, ← e', mul_inv_rev, map_mul, add_mul]
      simp only [mul_assoc]
      rw [← mul_assoc (rbar (φ t)), ← map_mul rbar (φ t), mul_inv_cancel, map_one, one_mul]
    · show _ * rbar (φ s)⁻¹ * _ = _
      rw [mul_assoc, rinv, mul_one]
  have one_part : ∀ a b, (1 : Matrix ι ι A) a b ∈ W.part (w a - w b) := fun a b => by
    have := part_alg W (w := w) (M := 1) (fun a b e => Matrix.one_apply_ne fun h => e (by rw [h])) a b
    rwa [Matrix.map_one _ (map_zero _) (map_one _)] at this
  choose y y1 y2 y3 using fun v => loc _ (F.φ v) (F.hφ v) (α v) (ρ v) (a1 v) (a2 v) (a3 v) (a4 v) (a5 v)
  choose x x1 x2 x3 using fun q => loc _ (F.ψ q) (F.hψ q) 1 (rq q) g1 one_part (q1 q) (q2 q)
    (fun s => by rw [mul_one, one_mul, q3])
  refine ⟨(fun x => ⟨_, mD x⟩, y, x), ⟨lD, y1, x1, fun s t u => Subtype.ext ?_, y2, x2⟩, fun s t => ?_, y3,
    fun q s => ?_⟩
  · have e : rt s * (rt t * rt u - rt (t * u)) + (rt s * rt (t * u) - rt (s * (t * u))) =
        (rt (s * t) * rt u - rt (s * t * u)) + (rt s * rt t - rt (s * t)) * rt u := by
      rw [mul_assoc s t u]
      noncomm_ring
    have e' := congrArg (fun M : Matrix ι ι A => M.map co) e
    rw [co_add c1 (mem_left _ (hker (t4 _ _))) (hker (t4 _ _)), co_add c1 (hker (t4 _ _)) (mem_right _ (hker (t4 _ _))),
      co_left c1 c2 _ (hker (t4 _ _)), co_right c1 c2 _ (hker (t4 _ _)), rtres, rtres] at e'
    show rbar s * ((rt t * rt u - rt (t * u)).map co * rbar (t * u)⁻¹) * rbar s⁻¹ +
      (rt s * rt (t * u) - rt (s * (t * u))).map co * rbar (s * (t * u))⁻¹ =
      (rt (s * t) * rt u - rt (s * t * u)).map co * rbar (s * t * u)⁻¹ +
      (rt s * rt t - rt (s * t)).map co * rbar (s * t)⁻¹
    have e2 := congrArg (fun M => M * rbar (s * t * u)⁻¹) e'
    simp only [add_mul, mul_assoc, ← map_mul] at e2 ⊢
    have n1 : (t * u)⁻¹ * s⁻¹ = (s * (t * u))⁻¹ := by group
    have n2 : u * (s * (t * u))⁻¹ = (s * t)⁻¹ := by group
    rw [n2] at e2
    rw [n1]
    exact e2
  · show _ * rbar (s * t)⁻¹ * _ = _
    rw [mul_assoc, rinv, mul_one]
  · have := x3 q s
    rwa [mul_one, one_mul] at this
