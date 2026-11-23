import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AbsInvOf

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry CrystallineSemistableComparison TensorProduct

namespace UpperTheory.Ru.crystallineComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
  {R : Per l K} {G : Model l K → Prop} {D : Dat R}

private theorem smul_toV {M : Model l K} {n : ℕ} (a : ℚ_[l]) (v : M.T n) :
    a • M.toV n v = (a ⊗ₜ[ℤ_[l]] v : ℚ_[l] ⊗[ℤ_[l]] M.T n) := by
  show a • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] v : ℚ_[l] ⊗[ℤ_[l]] M.T n) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem V_induction {M : Model l K} {n : ℕ} {P : M.V n → Prop} (h0 : P 0)
    (h1 : ∀ (a : ℚ_[l]) (v : M.T n), P (a • M.toV n v)) (h2 : ∀ x y, P x → P y → P (x + y)) (w : M.V n) : P w := by
  refine TensorProduct.induction_on (motive := fun w : ℚ_[l] ⊗[ℤ_[l]] M.T n => P w) (show ℚ_[l] ⊗[ℤ_[l]] M.T n from w) h0 ?_ h2
  intro a v
  have := h1 a v
  rw [smul_toV] at this
  exact this

private structure IsVal (e : EMap G D) (b : BMap G D) (p : PMap G D) {M : Model l K} (a : D.Ch M) (n : ℕ)
    (C : M.V n →+ (Module.Dual K (HdR M.q n) → R.B)) : Prop where
  smul : ∀ (z : ℚ_[l]) (w : M.V n) φ, C (z • w) φ = R.q z * C w φ
  spec : ∀ (c : R.A) (v : M.T n) (x : (D.H a).N n), b.β a n x = c • e.e a n v →
    ∀ φ, p.κ a n x φ = R.i c * C (M.toV n v) φ

private theorem tB_pow_ne (hF : R.Facts) (m : ℕ) : R.i (R.t ^ m) ≠ 0 := by
  rw [map_pow]; exact pow_ne_zero _ hF.t_ne

private theorem exists_val (hF : R.Facts) (e : EMap G D) (b : BMap G D) (p : PMap G D) {M : Model l K} (hM : G M)
    (a : D.Ch M) (n : ℕ) : ∃ C, IsVal e b p a n C := by
  obtain ⟨N, hN⟩ := b.surj a hM n
  obtain ⟨m, hm⟩ := b.inj a hM n
  have hx : ∀ v, ∃ x, b.β a n x = R.t ^ N • e.e a n v := fun v => let ⟨x, _, h⟩ := hN (e.e a n v); ⟨x, h⟩
  choose xs hxs using hx
  have hκ : ∀ x x' : (D.H a).N n, b.β a n x = b.β a n x' → ∀ φ, p.κ a n x φ = p.κ a n x' φ := by
    intro x x' h φ
    have h1 := hm (x - x') (by rw [map_sub, h, sub_self])
    have h2 := congrArg (fun y => p.κ a n y φ) h1
    simp only [p.lin a hM, map_zero, AddMonoidHom.zero_apply, map_sub, AddMonoidHom.sub_apply] at h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (tB_pow_ne hF m))
  have hu := tB_pow_ne hF (R := R) N
  let c0 : M.T n → Module.Dual K (HdR M.q n) → R.B := fun v φ => (R.i (R.t ^ N))⁻¹ * p.κ a n (xs v) φ
  have spec0 : ∀ (c : R.A) (v : M.T n) (x : (D.H a).N n), b.β a n x = c • e.e a n v →
      ∀ φ, p.κ a n x φ = R.i c * c0 v φ := by
    intro c v x h φ
    have h1 := hκ (R.t ^ N • x) (c • xs v) (by
      rw [map_smul, map_smul, h, hxs, smul_smul, smul_smul, mul_comm]) φ
    rw [p.lin a hM, p.lin a hM] at h1
    simp only [c0]
    field_simp
    linear_combination h1
  have add0 : ∀ v v' φ, c0 (v + v') φ = c0 v φ + c0 v' φ := by
    intro v v' φ
    have := spec0 (R.t ^ N) (v + v') (xs v + xs v') (by rw [map_add, hxs, hxs, map_add, smul_add]) φ
    rw [map_add, AddMonoidHom.add_apply] at this
    simp only [c0]
    field_simp
    rw [this]; simp only [c0]; field_simp
  have sm0 : ∀ (z : ℤ_[l]) v φ, c0 (z • v) φ = R.q z * c0 v φ := by
    intro z v φ
    have := spec0 (R.t ^ N) (z • v) (R.z z • xs v) (by
      rw [map_smul, hxs, e.lin a hM, smul_smul, smul_smul, mul_comm]) φ
    rw [p.lin a hM, hF.thetaSetup_structureMap_comp] at this
    have h3 : c0 (z • v) φ = (R.i (R.t ^ N))⁻¹ * (R.q z * p.κ a n (xs v) φ) := by rw [this]; field_simp
    rw [h3]; simp only [c0]; ring
  let f : ℚ_[l] →+ M.T n →+ (Module.Dual K (HdR M.q n) → R.B) :=
    AddMonoidHom.mk' (fun s => AddMonoidHom.mk' (fun v φ => R.q s * c0 v φ)
      (by intro v v'; funext φ; simp only [add0, Pi.add_apply, mul_add])) (by
        intro s s'; ext v φ; simp [add_mul])
  let C : M.V n →+ (Module.Dual K (HdR M.q n) → R.B) := TensorProduct.liftAddHom f (by
    intro r s v; funext φ
    show R.q (r • s) * c0 v φ = R.q s * c0 (r • v) φ
    rw [sm0, Algebra.smul_def, map_mul]
    show R.q (r : ℚ_[l]) * _ * _ = _
    ring)
  have hC : ∀ (s : ℚ_[l]) (v : M.T n) φ, C (s • M.toV n v) φ = R.q s * c0 v φ := by
    intro s v φ
    rw [smul_toV]
    show (TensorProduct.liftAddHom f _ (s ⊗ₜ v)) φ = _
    rw [TensorProduct.liftAddHom_tmul]
    rfl
  have hC1 : ∀ (v : M.T n) φ, C (M.toV n v) φ = c0 v φ := by
    intro v φ
    have := hC 1 v φ
    rwa [one_smul, map_one, one_mul] at this
  refine ⟨C, ?_, ?_⟩
  · intro z w φ
    refine V_induction (P := fun w => C (z • w) φ = R.q z * C w φ) ?_ ?_ ?_ w
    · simp
    · intro s v
      rw [smul_smul, hC, hC, map_mul]; ring
    · intro x y hx hy
      rw [smul_add, map_add, map_add, Pi.add_apply, Pi.add_apply, hx, hy, mul_add]
  · intro c v x h φ
    rw [hC1]; exact spec0 c v x h φ

private theorem exists_rep (e : EMap G D) (b : BMap G D) {M : Model l K} (hM : G M) (a : D.Ch M) (n : ℕ) :
    ∃ N : ℕ, ∀ v, ∃ x, b.β a n x = R.t ^ N • e.e a n v := by
  obtain ⟨N, hN⟩ := b.surj a hM n
  exact ⟨N, fun v => let ⟨x, _, h⟩ := hN (e.e a n v); ⟨x, h⟩⟩

private theorem act_toV {M : Model l K} {n : ℕ} (σ : K.fixingSubgroup) (v : M.T n) :
    M.act n σ (M.toV n v) = M.toV n (M.actT n σ v) := rfl

variable {e : EMap G D} {b : BMap G D} {p : PMap G D} {M : Model l K} {a : D.Ch M}

private theorem IsVal.equi {n : ℕ} {C : M.V n →+ (Module.Dual K (HdR M.q n) → R.B)} (hC : IsVal e b p a n C)
    (hF : R.Facts) (hL : D.Laws G) (hM : G M) (σ : K.fixingSubgroup) (w : M.V n) (φ) :
    C (M.act n σ w) φ = R.σ σ (C w φ) := by
  refine V_induction (P := fun w => C (M.act n σ w) φ = R.σ σ (C w φ)) (by simp) ?_ ?_ w
  · intro s v
    rw [map_smul, hC.smul, hC.smul, map_mul, hF.σ_q, act_toV]
    congr 1
    obtain ⟨N, hN⟩ := exists_rep e b hM a n
    obtain ⟨x, hx⟩ := hN v
    have h1 := hC.spec (R.σA σ (R.t ^ N)) (M.actT n σ v) ((D.H a).act n σ x) (by
      rw [b.act a hM, hx, hL.act_smul, e.act a hM]) φ
    rw [p.act a hM, hC.spec _ _ _ hx, map_mul, hF.i_σ] at h1
    exact (mul_left_cancel₀ ((map_ne_zero _).mpr (tB_pow_ne hF N)) h1).symm
  · intro x y hx hy
    rw [map_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, map_add]

private theorem IsVal.cup {i j : ℕ} {Ci : M.V i →+ (Module.Dual K (HdR M.q i) → R.B)}
    {Cj : M.V j →+ (Module.Dual K (HdR M.q j) → R.B)} {Cij : M.V (i + j) →+ (Module.Dual K (HdR M.q (i + j)) → R.B)}
    (hi : IsVal e b p a i Ci) (hj : IsVal e b p a j Cj) (hij : IsVal e b p a (i + j) Cij)
    (hF : R.Facts) (hL : D.Laws G) (hM : G M) (x : M.T i) (y : M.T j) (z : M.T (i + j)) (h : M.CupT x y z)
    {m m' : ℕ} (bb : Module.Basis (Fin m) K (HdR M.q i)) (bb' : Module.Basis (Fin m') K (HdR M.q j)) (φ) :
    Cij (M.toV _ z) φ = ∑ s, ∑ s', Ci (M.toV _ x) (bb.coord s) * Cj (M.toV _ y) (bb'.coord s') *
      R.o (φ (p.cupR M i j (bb s) (bb' s'))) := by
  obtain ⟨N, hN⟩ := exists_rep e b hM a i
  obtain ⟨N', hN'⟩ := exists_rep e b hM a j
  obtain ⟨X, hX⟩ := hN x
  obtain ⟨Y, hY⟩ := hN' y
  obtain ⟨Z, hZ⟩ := hL.cup_ex a X Y
  have h1 := b.cup a hM X Y Z hZ
  rw [hX, hY] at h1
  have h2 := hL.cup_uniq a _ _ _ _ h1 (hL.cup_smul a _ _ _ _ _ (e.cup a hM x y z h))
  have h3 := p.cup a hM X Y Z hZ bb bb' φ
  rw [hij.spec _ _ _ h2] at h3
  simp only [hi.spec _ _ _ hX, hj.spec _ _ _ hY] at h3
  rw [map_mul] at h3
  refine mul_left_cancel₀ (mul_ne_zero (tB_pow_ne hF N) (tB_pow_ne hF N')) (h3.trans ?_)
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem pow_rep (hS : EtSide G) (hL : D.Laws G) (hM : G M) (x : (D.H a).N 2) (v : M.T 2)
    (hx : b.β a 2 x = R.t • e.e a 2 v) (k : ℕ) (z : (D.H a).N (2 * k))
    (hz : IsPow (N := (D.H a).N) (D.H a).one (D.H a).cup x k z) :
    ∃ w : M.T (2 * k), b.β a (2 * k) z = R.t ^ k • e.e a (2 * k) w := by
  induction k with
  | zero =>
    obtain ⟨w, hw⟩ := e.one a hM
    exact ⟨w, by rw [pow_zero, one_smul]; exact hL.one_uniq a _ _ (b.one a hM z hz) hw⟩
  | succ k ih =>
    obtain ⟨y, hy, hc⟩ := hz
    obtain ⟨w, hw⟩ := ih y hy
    obtain ⟨w', hw'⟩ := hS.cup_ex M w v
    have h1 := b.cup a hM y x z hc
    rw [hw, hx] at h1
    refine ⟨w', ?_⟩
    have h2 := hL.cup_uniq a _ _ _ _ h1 (hL.cup_smul a _ _ _ _ _ (e.cup a hM w v w' hw'))
    rw [pow_succ]
    exact h2

private theorem IsVal.top {d : ℕ} {C : M.V (2 * d) →+ (Module.Dual K (HdR M.q (2 * d)) → R.B)} (hC : IsVal e b p a (2 * d) C)
    (hF : R.Facts) (hS : EtSide G) (hL : D.Laws G) (hM : G M) (hd : M.Conn d) : ∃ w φ, C w φ ≠ 0 := by
  obtain ⟨x, z, φ, hx, hz, hU⟩ := p.c1 a hM d hd
  obtain ⟨v, hv⟩ := e.c1 a hM
  have h1 := hL.first_chern_class_unique a _ _ (b.c1 a hM x hx) hv
  obtain ⟨w, hw⟩ := pow_rep hS hL hM x v h1 d z hz
  refine ⟨M.toV _ w, φ, fun h0 => ?_⟩
  obtain ⟨_, y, _, hy⟩ := hU
  rw [hC.spec _ _ _ hw, h0, mul_zero, zero_mul] at hy
  exact zero_ne_one hy

private theorem IsVal.van {n : ℕ} {C : M.V n →+ (Module.Dual K (HdR M.q n) → R.B)} (hC : IsVal e b p a n C)
    (hF : R.Facts) (hM : G M) {ι : Type} [Fintype ι] (v : ι → M.T n) (c : ι → R.A) (u : ℕ)
    (h : R.t ^ u • ∑ k, c k • e.e a n (v k) = 0) (ψ) : ∑ k, R.i (c k) * C (M.toV n (v k)) ψ = 0 := by
  obtain ⟨N, hN⟩ := exists_rep e b hM a n
  obtain ⟨m, hm⟩ := b.inj a hM n
  choose xs hxs using fun k => hN (v k)
  have h1 := hm (R.t ^ u • ∑ k, (c k • xs k)) (by
    simp only [map_smul, map_sum, hxs]
    simp only [smul_comm (c _) (R.t ^ N), ← Finset.smul_sum]
    rw [smul_comm, h, smul_zero])
  have h2 := congrArg (fun y => p.κ a n y ψ) h1
  simp only [p.lin a hM, map_zero, AddMonoidHom.zero_apply, map_sum, AddMonoidHom.finset_sum_apply,
    hC.spec _ _ _ (hxs _)] at h2
  have h3 := (mul_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (tB_pow_ne hF m))).resolve_left (tB_pow_ne hF u)
  have h4 : R.i (R.t ^ N) * ∑ k, R.i (c k) * C (M.toV n (v k)) ψ = 0 := by
    rw [Finset.mul_sum, ← h3]
    exact Finset.sum_congr rfl fun _ _ => by ring
  exact (mul_eq_zero.mp h4).resolve_left (tB_pow_ne hF N)

private theorem inj_conn (hF : R.Facts) (hS : EtSide G) (hL : D.Laws G) (e : EMap G D) (b : BMap G D) (p : PMap G D)
    {M : Model l K} (hM : G M) {d : ℕ} (hd : M.Conn d) (a : D.Ch M) (j : ℕ) {ι : Type} [Fintype ι]
    (v : ι → M.T j) (c : ι → R.A) (u : ℕ) (h : R.t ^ u • ∑ k, c k • e.e a j (v k) = 0)
    (f : Module.Dual ℚ_[l] (M.V j)) : ∑ k, R.q (f (M.toV j (v k))) * R.i (c k) = 0 := by
  obtain ⟨hsub, hdual⟩ := hS.dual M hM d hd
  by_cases hj : 2 * d < j
  · have := hsub j hj
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Subsingleton.elim (M.toV j (v k)) 0, map_zero, map_zero, zero_mul]
  obtain ⟨j', hj'⟩ : ∃ j', j + j' = 2 * d := ⟨2 * d - j, by omega⟩
  obtain ⟨r, g, hspan, htrans, hfun⟩ := hdual j j' hj'
  choose C hC using fun n => exists_val hF e b p hM a n
  have htop : ∀ N, N = 2 * d → ∃ w φ, C N w φ ≠ 0 := by
    rintro _ rfl; exact (hC _).top hF hS hL hM hd
  obtain ⟨w, φ, hw⟩ := htop _ hj'
  have hg : ∃ s, C (j + j') (g s) φ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hw' : w ∈ Submodule.span ℚ_[l] (Set.range g) := by rw [hspan]; trivial
    refine hw (Submodule.span_induction (p := fun w _ => C (j + j') w φ = 0) ?_ (by simp) ?_ ?_ hw')
    · rintro _ ⟨s, rfl⟩; exact hcon s
    · intro x y _ _ hx hy; rw [map_add, Pi.add_apply, hx, hy, add_zero]
    · intro z x _ hx; rw [(hC _).smul, hx, mul_zero]
  obtain ⟨s₀, hs₀⟩ := hg
  have hall : ∀ s, C (j + j') (g s) φ ≠ 0 := by
    intro s h0
    obtain ⟨σ, z, hz, hact⟩ := htrans s s₀
    have h1 := (hC _).equi hF hL hM σ (g s) φ
    rw [hact, (hC _).smul, h0, map_zero] at h1
    exact (mul_ne_zero ((map_ne_zero _).mpr hz) hs₀) h1
  haveI := (p.fin M hM j).1
  haveI := (p.fin M hM j').1
  let bb := Module.finBasis K (HdR M.q j)
  let bb' := Module.finBasis K (HdR M.q j')
  have hf : f ∈ Submodule.span ℚ_[l] {f : Module.Dual ℚ_[l] (M.V j) | ∃ (s : Fin r) (y : M.T j'),
      ∀ x : M.T j, ∃ z, M.CupT x y z ∧ M.toV (j + j') z = f (M.toV j x) • g s} := by rw [hfun]; trivial
  refine Submodule.span_induction (p := fun f _ => ∑ k, R.q (f (M.toV j (v k))) * R.i (c k) = 0) ?_ (by simp) ?_ ?_ hf
  · rintro f ⟨s, y, hy⟩
    choose zs hz1 hz2 using fun k => hy (v k)
    have h1 : ∑ k, R.i (c k) * C (j + j') (M.toV _ (zs k)) φ = 0 := by
      simp only [fun k => (hC j).cup (hC j') (hC (j + j')) hF hL hM _ y _ (hz1 k) bb bb' φ, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun s₁ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun s₂ _ => ?_
      have h2 := (hC j).van hF hM v c u h (bb.coord s₁)
      calc _ = (∑ k, R.i (c k) * C j (M.toV j (v k)) (bb.coord s₁)) * (C j' (M.toV j' y) (bb'.coord s₂) *
              R.o (φ (p.cupR M j j' (bb s₁) (bb' s₂)))) := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
        _ = 0 := by rw [h2, zero_mul]
    simp only [hz2, (hC _).smul] at h1
    have h3 : (∑ k, R.q (f (M.toV j (v k))) * R.i (c k)) * C (j + j') (g s) φ = 0 := by
      rw [Finset.sum_mul, ← h1]; exact Finset.sum_congr rfl fun _ _ => by ring
    exact (mul_eq_zero.mp h3).resolve_right (hall s)
  · intro x y _ _ hx hy
    simp only [LinearMap.add_apply, map_add, add_mul, Finset.sum_add_distrib, hx, hy, add_zero]
  · intro z x _ hx
    simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum, hx, mul_zero]

private theorem toV_pullT {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) (v : N.T n) :
    M.toV n (Model.pullT u hu n v) = Model.pullV u hu n (N.toV n v) := rfl

theorem injAbs : UpperTheory.Ru.crystallineComparison.InjAbs := by
  intro l _ K R G D hF hS hL e b p M hM a j ι _ v c u h f
  obtain ⟨r, P, d, uu, hu, hP, hinj⟩ := hS.comp M hM
  have hs : ∀ s (f' : Module.Dual ℚ_[l] ((P s).V j)),
      ∑ k, R.q (f' (Model.pullV (uu s) (hu s) j (M.toV j (v k)))) * R.i (c k) = 0 := by
    intro s f'
    obtain ⟨a₀⟩ := hL.ch (P s) (hP s).1
    obtain ⟨a', _, ⟨m⟩⟩ := hL.refine (P s) M (uu s) (hu s) (hP s).1 hM a₀ a
    have := inj_conn hF hS hL e b p (hP s).1 (hP s).2 a' j (fun k => Model.pullT (uu s) (hu s) j (v k)) c u (by
      have h1 := congrArg (D.pullA m j) h
      simpa only [map_smul, map_sum, map_zero, ← e.nat m (hP s).1 hM] using h1) f'
    simpa only [toV_pullT] using this
  let L : M.V j →ₗ[ℚ_[l]] ∀ s, (P s).V j := LinearMap.pi fun s => Model.pullV (uu s) (hu s) j
  have hk : LinearMap.ker L = ⊥ := LinearMap.ker_eq_bot'.2 fun w hw => hinj j w fun s => congrFun hw s
  obtain ⟨g, hg⟩ := L.exists_leftInverse_of_injective hk
  let f' : ∀ s, Module.Dual ℚ_[l] ((P s).V j) := fun s => (f ∘ₗ g) ∘ₗ LinearMap.single ℚ_[l] (fun s => (P s).V j) s
  have hf : ∀ w, f w = ∑ s, f' s (Model.pullV (uu s) (hu s) j w) := by
    intro w
    have h1 : g (L w) = w := LinearMap.congr_fun hg w
    conv_lhs => rw [← h1, ← Finset.univ_sum_single (L w), map_sum, map_sum]
    rfl
  simp only [hf, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun s _ => hs s (f' s)

end UpperTheory.Ru.crystallineComparison
