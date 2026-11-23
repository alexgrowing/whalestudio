import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ContLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

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

private theorem map_mul_alg {O R S ι : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    [Fintype ι] [DecidableEq ι] (f : R →ₐ[O] S) (A B : Matrix ι ι R) : (A * B).map f = A.map f * B.map f :=
  Matrix.map_mul (f := (f : R →+* S))

private theorem map_adj_alg {O R S : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (X : M4 R) : (adj X).map f = adj (X.map f) := by
  ext i j
  simp only [adj_apply, Matrix.map_apply, map_zsmul]

private theorem up_mul {R : Type} [CommRing R] {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rcases lt_or_ge c i with hc | hc
  · rw [hX i c hc, zero_mul]
  · rw [hY c j (lt_of_lt_of_le h hc), mul_zero]

private theorem sp_inv {R : Type} [CommRing R] {X : M4 R} (h : IsGSp 1 X) : adj X * X = 1 ∧ X * adj X = 1 := by
  have e : adj X * X = 1 := by
    unfold IsGSp at h
    rwa [one_smul] at h
  exact ⟨e, mul_eq_one_comm.1 e⟩

private theorem key_sp {A k : Type} [CommRing A] [CommRing k] {K : Ideal A} (σ : A →+* k) {co : A → k}
    (h1 : ∀ x ∈ K, ∀ y ∈ K, co (x + y) = co x + co y) (h2 : ∀ a, ∀ x ∈ K, co (a * x) = σ a * co x)
    {x : A} {Z Z' : M4 A} (hZ : IsGSp x Z) (hZ' : IsGSp x Z') (hK : ∀ a b, (Z - Z') a b ∈ K) {g g' : M4 k}
    (e : Z.map σ = g) (e' : Z'.map σ = g) (hg : g * g' = 1) : (Z - Z').map co * g' ∈ sp4 k := by
  obtain ⟨hmul, -, hadd, -, hone, -⟩ := grp k
  obtain ⟨-, -, hadd', -, -, hmap, -⟩ := grp A
  have hK' : ∀ a b, adj (Z - Z') a b ∈ K := fun a b => by
    rw [adj_apply]
    exact zsmul_mem (hK _ _) _
  have hc : (adj (Z - Z')).map co = adj ((Z - Z').map co) := by
    ext i j
    rw [Matrix.map_apply, adj_apply, adj_apply, Matrix.map_apply, zsmul_eq_mul, h2 _ _ (hK _ _), map_intCast,
      zsmul_eq_mul]
  have e0 : adj (Z - Z') * Z' + adj Z * (Z - Z') = 0 := by
    have : adj (Z - Z') = adj Z - adj Z' := by
      rw [eq_sub_iff_add_eq, ← hadd', sub_add_cancel]
    unfold IsGSp at hZ hZ'
    rw [this, sub_mul, mul_sub, hZ, hZ']
    abel
  have e1 := congrArg (fun M : M4 A => M.map co) e0
  rw [co_add h1 (mem_right _ hK') (mem_left _ hK), co_right h1 h2 _ hK', co_left h1 h2 _ hK, hc, ← hmap, e, e'] at e1
  have e2 : adj ((Z - Z').map co) * g + adj g * (Z - Z').map co = 0 := by
    rw [e1]
    ext a b
    exact co_zero h1
  show adj _ = -_
  have e3 := congrArg (fun M => adj g' * M * g') e2
  simp only [mul_add, add_mul, mul_zero, zero_mul] at e3
  rw [← mul_assoc (adj g') (adj g), ← hmul g g', hg, hone, one_mul, ← mul_assoc, mul_assoc _ g g', hg, mul_one] at e3
  rw [hmul]
  exact eq_neg_of_add_eq_zero_left e3

end G

theorem UpperTheory.V.Ws.X1.obCoc :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {Γ V : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Gv : V → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →* Γ), (∀ v, Continuous (loc v)) → ∀ {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (ν : Γ →* Λˣ) (r : Γ →* M4 R) (n : V → M4 R), AdicCont (maximalIdeal Λ) (fun g => (ν g : Λ)) → WP loc (fun g => algebraMap Λ R (ν g)) r n → (∀ i j, AdicCont (maximalIdeal R) fun g => r g i j) → ∀ (rb : Γ →* M4 (ResidueField Λ)) (nb : V → M4 (ResidueField Λ)) (hb : ∀ g, ∃ x, IsGSp x (rb g)), (∀ g, (r g).map (res Λ R) = rb g) → (∀ v, (n v).map (res Λ R) = nb v) → ∀ (D : SL loc ν r n p) (co : A → ResidueField Λ), (∀ x ∈ RingHom.ker p, ∀ y ∈ RingHom.ker p, co (x + y) = co x + co y) → (∀ (a : A), ∀ x ∈ RingHom.ker p, co (a * x) = res Λ A a * co x) → ∃ z ∈ Fr.continuousCocycles2 loc (adSp rb hb) (fun v => bor (nb v)), (∀ s t, (z.1 (s, t)).1 * rb (s * t) = (D.om s t).map co) ∧ ∀ v s, (z.2 v s).1 * rb (loc v s) = (D.de v s).map co := by
  intro Λ _ _ _ _ Γ V _ _ _ Gv _ _ _ loc hloc A R _ _ _ _ _ _ p hp hs ν r n _ hW hr rb nb hb hrb hnb D co c1 c2
  obtain ⟨-, hadj, -, -, -, -, -, hgs, -⟩ := grp A
  have resp : ∀ Z : M4 A, Z.map (res Λ A) = (Z.map p).map (res Λ R) := fun Z => by
    ext a b
    exact (res_map p _).symm
  have rinv : ∀ s, rb s⁻¹ * rb s = 1 := fun s => by rw [← map_mul, inv_mul_cancel, map_one]
  have rinv' : ∀ s, rb s * rb s⁻¹ = 1 := fun s => by rw [← map_mul, mul_inv_cancel, map_one]
  have rtres : ∀ s, (D.rt s).map (res Λ A) = rb s := fun s => by rw [resp, D.rt_map, hrb]
  have hker : ∀ {Z Z' : M4 A}, Z.map p = Z'.map p → ∀ a b, (Z - Z') a b ∈ RingHom.ker p := by
    intro Z Z' e a b
    have := congrFun (congrFun e a) b
    rw [RingHom.mem_ker, Matrix.sub_apply, map_sub]
    exact sub_eq_zero.2 this
  have key : ∀ (s : Γ) (Z Z' : M4 A), IsGSp (algebraMap Λ A (ν s)) Z → IsGSp (algebraMap Λ A (ν s)) Z' →
      Z.map p = r s → Z'.map p = r s → (Z - Z').map co * rb s⁻¹ ∈ sp4 (ResidueField Λ) := by
    intro s Z Z' k1 k2 e1 e2
    exact key_sp (res Λ A : A →+* ResidueField Λ) c1 c2 k1 k2 (hker (e1.trans e2.symm))
      ((resp Z).trans (by rw [e1, hrb])) ((resp Z').trans (by rw [e2, hrb])) (rinv' s)
  have lcbar : IsLocallyConstant rb := by
    refine lc_matrix fun a b => ?_
    have := (hr a b 1).comp (Ideal.Quotient.lift (maximalIdeal R ^ 1) (res Λ R : R →+* ResidueField Λ)
      fun x hx => (res_eq_zero_iff Λ R x).2 (by rwa [pow_one] at hx))
    convert this using 1
    funext s
    rw [← hrb]
    rfl
  have lcinv : IsLocallyConstant fun s : Γ => rb s⁻¹ := lcbar.comp_continuous continuous_inv
  have lct := lc_ac D.rt_cont
  have t4 : ∀ s t, (D.rt s * D.rt t).map p = r (s * t) := fun s t => by
    rw [map_mul_alg, D.rt_map, D.rt_map, map_mul]
  have k4 : ∀ s t a b, D.om s t a b ∈ RingHom.ker p := fun s t => hker ((t4 s t).trans (D.rt_map _).symm)
  have mD : ∀ x : Γ × Γ, (D.om x.1 x.2).map co * rb (x.1 * x.2)⁻¹ ∈ sp4 (ResidueField Λ) := by
    rintro ⟨s, t⟩
    refine key _ _ _ ?_ (D.rt_mult _) (t4 s t) (D.rt_map _)
    simp only [map_mul, Units.val_mul]
    exact hgs _ _ _ _ (D.rt_mult s) (D.rt_mult t)
  have lD : IsLocallyConstant fun x : Γ × Γ => (⟨_, mD x⟩ : sp4 (ResidueField Λ)) := by
    refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
    have l1 : IsLocallyConstant fun x : Γ × Γ => D.om x.1 x.2 := by
      refine lc_ker hs (fun x => k4 x.1 x.2) fun N => ?_
      simp only [SL.om, Matrix.map_sub _ (map_sub (Ideal.Quotient.mk _)), Matrix.map_mul]
      exact (((lct N).comp_continuous continuous_fst).mul ((lct N).comp_continuous continuous_snd)).sub
        ((lct N).comp_continuous continuous_mul)
    exact (l1.comp (fun M => M.map co)).mul (lcinv.comp_continuous continuous_mul)
  have u4 : ∀ v s, (D.nt v * D.t v s * adj (D.nt v)).map p = r (loc v s) := fun v s => by
    rw [map_mul_alg, map_mul_alg, map_adj_alg, D.nt_map, D.t_map]
    simp only [← mul_assoc]
    rw [(sp_inv (hW.sp v)).2, one_mul, mul_assoc, (sp_inv (hW.sp v)).2, mul_one]
  have k5 : ∀ v s a b, D.de v s a b ∈ RingHom.ker p := fun v s => hker ((D.rt_map _).trans (u4 v s).symm)
  have mE : ∀ v s, (D.de v s).map co * rb (loc v s)⁻¹ ∈ sp4 (ResidueField Λ) := by
    intro v s
    refine key _ _ _ (D.rt_mult _) ?_ (D.rt_map _) (u4 v s)
    have h1 : IsGSp 1 (adj (D.nt v)) := by
      unfold IsGSp
      rw [hadj, one_smul, (sp_inv (D.nt_sp v)).2]
    have := hgs _ _ _ _ (hgs _ _ _ _ (D.nt_sp v) (D.t_mult v s)) h1
    rwa [one_mul, mul_one] at this
  refine ⟨(fun x => ⟨_, mD x⟩, fun v s => ⟨_, mE v s⟩), ⟨lD, fun v => ?_, fun s t u => Subtype.ext ?_,
    fun v s t => ?_⟩, fun s t => ?_, fun v s => ?_⟩
  · refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
    have l1 : IsLocallyConstant fun s => D.de v s := by
      refine lc_ker hs (k5 v) fun N => ?_
      simp only [SL.de, Matrix.map_sub _ (map_sub (Ideal.Quotient.mk _)), Matrix.map_mul]
      exact ((lct N).comp_continuous (hloc v)).sub
        (((IsLocallyConstant.const _).mul (lc_ac (D.t_cont v) N)).mul (IsLocallyConstant.const _))
    exact (l1.comp (fun M => M.map co)).mul (lcinv.comp_continuous (hloc v))
  · have e : D.rt s * D.om t u + D.om s (t * u) = D.om (s * t) u + D.om s t * D.rt u := by
      simp only [SL.om]
      rw [mul_assoc s t u]
      noncomm_ring
    have e' := congrArg (fun M : M4 A => M.map co) e
    rw [co_add c1 (mem_left _ (k4 _ _)) (k4 _ _), co_add c1 (k4 _ _) (mem_right _ (k4 _ _)),
      co_left c1 c2 _ (k4 _ _), co_right c1 c2 _ (k4 _ _), rtres, rtres] at e'
    show rb s * ((D.om t u).map co * rb (t * u)⁻¹) * rb s⁻¹ + (D.om s (t * u)).map co * rb (s * (t * u))⁻¹ =
      (D.om (s * t) u).map co * rb (s * t * u)⁻¹ + (D.om s t).map co * rb (s * t)⁻¹
    have e2 := congrArg (fun M => M * rb (s * t * u)⁻¹) e'
    simp only [add_mul, mul_assoc, ← map_mul] at e2 ⊢
    have n1 : (t * u)⁻¹ * s⁻¹ = (s * (t * u))⁻¹ := by group
    have n2 : u * (s * (t * u))⁻¹ = (s * t)⁻¹ := by group
    rw [n2] at e2
    rw [n1]
    exact e2
  · have k6 : ∀ a b, (D.t v s * D.t v t - D.t v (s * t)) a b ∈ RingHom.ker p := by
      refine hker ?_
      rw [map_mul_alg, D.t_map, D.t_map, D.t_map, map_mul, map_mul]
      simp only [mul_assoc]
      rw [← mul_assoc (n v), (sp_inv (hW.sp v)).2, one_mul]
    have e : D.om (loc v s) (loc v t) + D.de v (s * t) =
        D.de v s * D.rt (loc v t) + D.nt v * D.t v s * adj (D.nt v) * D.de v t +
          D.nt v * (D.t v s * D.t v t - D.t v (s * t)) * adj (D.nt v) := by
      have e1 : D.nt v * D.t v s * adj (D.nt v) * (D.nt v * D.t v t * adj (D.nt v)) =
          D.nt v * (D.t v s * D.t v t) * adj (D.nt v) := by
        simp only [mul_assoc]
        rw [← mul_assoc (adj (D.nt v)), (sp_inv (D.nt_sp v)).1, one_mul]
      simp only [SL.om, SL.de, map_mul, mul_sub, sub_mul]
      rw [e1]
      abel
    have e' := congrArg (fun M : M4 A => M.map co) e
    have k7 : ∀ a b, (D.de v s * D.rt (loc v t) + D.nt v * D.t v s * adj (D.nt v) * D.de v t) a b ∈ RingHom.ker p :=
      fun a b => add_mem (mem_right _ (k5 _ _) a b) (mem_left _ (k5 _ _) a b)
    have ntres : (D.nt v).map (res Λ A) = nb v := by rw [resp, D.nt_map, hnb]
    rw [co_add c1 (k4 _ _) (k5 _ _),
      co_add c1 k7 (mem_right _ (mem_left _ k6)),
      co_add c1 (mem_right _ (k5 _ _)) (mem_left _ (k5 _ _)), co_right c1 c2 _ (k5 _ _), co_left c1 c2 _ (k5 _ _),
      co_right c1 c2 _ (mem_left _ k6), co_left c1 c2 _ k6, rtres, resp (_ * _), u4, hrb, map_adj_alg, ntres] at e'
    have nbi : adj (nb v) * nb v = 1 := by
      rw [← ntres, ← map_adj_alg, ← map_mul_alg, (sp_inv (D.nt_sp v)).1]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have up1 : IsUp ((D.t v s * D.t v t - D.t v (s * t)).map co) := fun i j h => by
      rw [Matrix.map_apply, Matrix.sub_apply, up_mul (D.t_up v s) (D.t_up v t) i j h, D.t_up v _ i j h, sub_zero,
        co_zero c1]
    have up2 : IsUp (adj (nb v) * rb (loc v (s * t))⁻¹ * nb v) := fun i j h => by
      rw [← map_inv, ← hnb, ← hrb, ← map_adj_alg, ← map_mul_alg, ← map_mul_alg, Matrix.map_apply,
        hW.flag v _ i j h, map_zero]
    show IsUp (adj (nb v) * ((D.om (loc v s) (loc v t)).map co * rb (loc v s * loc v t)⁻¹ -
      ((D.de v s).map co * rb (loc v s)⁻¹ + rb (loc v s) * ((D.de v t).map co * rb (loc v t)⁻¹) * rb (loc v s)⁻¹ -
        (D.de v (s * t)).map co * rb (loc v (s * t))⁻¹)) * nb v)
    convert up_mul up1 up2 using 1
    rw [eq_sub_of_add_eq e', map_mul (loc v) s t, mul_inv_rev, map_mul rb]
    simp only [add_mul, sub_mul, mul_add, mul_sub, mul_assoc]
    rw [← mul_assoc (rb (loc v t)), rinv', one_mul, ← mul_assoc (adj (nb v)) (nb v), nbi, one_mul]
    abel
  · show _ * rb (s * t)⁻¹ * _ = _
    rw [mul_assoc, rinv, mul_one]
  · show _ * rb (loc v s)⁻¹ * _ = _
    rw [mul_assoc, rinv, mul_one]
