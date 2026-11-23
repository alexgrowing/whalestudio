import ReciprocityTheory.DualLattices.ExistsLimTensor

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

lemma ATower.char_R {p : ℕ} (Tw : ATower R₀ p) (n : ℕ) : ((p ^ (n + 1) : ℕ) : (Tw.R n : Type u)) = 0 := by
  have h := congrArg (Tw.π n).1 (Tw.char n)
  rwa [map_natCast, map_zero] at h

theorem lim (B : BX R₀) (hB1 : PairingPropertiesStatement B) {p : ℕ} (Tw : ATowerL R₀ p) (Dt : DualTower Tw) :
    LimStatement B Tw Dt := by
  intro ι τ hτ hc
  have hN : ∀ n, ((p ^ (n + 1) : ℕ) : (Tw.R n : Type u)) = 0 := fun n => Tw.toATower.char_R n
  have hy : ∀ i n, (p ^ (n + 1)) • B.map (Tw.q n) (τ i n) = 0 := fun i n => by
    rw [← map_nsmul, hτ i n, map_zero]
  have hex : ∀ i n, ∃ h, B.IsHeight (Dt.Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n)) h :=
    fun i n => BX.isHeight_exists (B := B) hB1 (Dt.Dp n) _ (hN n) _ (hy i n)
  choose h hh using hex
  have hcomp : ∀ i n, (Tw.r n).1.toLinearMap ∘ₗ h i (n + 1) = h i n := by
    intro i n
    have H1 := BX.isHeight_map (B := B) hB1 (Dt.Dp (n + 1)) (Dt.Dp n) (Tw.r n) (Dt.d n) (Dt.d_π n)
      (Dt.d_σ n) (Dt.d_η n) _ _ _ (hh i (n + 1))
    rw [← B.map_comp, BX.tw_qr Tw n, pow_succ] at H1
    have hy1 : (p ^ (n + 1) * p) • B.map (Tw.q n) (τ i (n + 1)) = 0 := by
      rw [← pow_succ, ← map_nsmul, hτ i (n + 1), map_zero]
    have H2 := BX.isHeight_mul_p (B := B) hB1 (Dt.Dp n) (p ^ (n + 1)) p (hN n) _ hy1 _ H1
    rw [← map_nsmul, ← hc i n] at H2
    exact BX.isHeight_unique (B := B) hB1 (Dt.Dp n) _ (hN n) _ (hy i n) _ _ H2 (hh i n)
  have hlimv : ∀ i (v : B.gg), ∃ a : (Tw.O : Type u), ∀ n, (Tw.q n).1 a = h i n v := fun i v =>
    Tw.complete (fun n => h i n v) (fun n => by
      have := LinearMap.congr_fun (hcomp i n) v
      simpa using this)
  choose hta hta_spec using hlimv
  have hsep : ∀ a b : (Tw.O : Type u), (∀ n, (Tw.q n).1 a = (Tw.q n).1 b) → a = b := fun a b hab =>
    sub_eq_zero.mp (Tw.sep _ (fun n => by rw [map_sub, hab n, sub_self]))
  let ht : ι → B.gg →ₗ[R₀] (Tw.O : Type u) := fun i =>
    { toFun := hta i
      map_add' := fun v w => hsep _ _ (fun n => by simp only [map_add, hta_spec])
      map_smul' := fun c v => hsep _ _ (fun n => by simp only [map_smul, hta_spec, RingHom.id_apply]) }
  have hlift : ∀ i n, ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)),
      B.map (Tw.π n) th = B.map (Tw.q n) (τ i n) ∧
      (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
        (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) :=
    fun i n => BX.exists_lift (B := B) Tw.toATower n _ (hy i n)
  choose th w hthw using hlift
  have hwb : ∀ i n, LinearMap.lTensor B.gg (Tw.r n).1.toLinearMap
      (LinearMap.lTensor B.gg (Tw.π (n + 1)).1.toLinearMap (w i (n + 1))) =
      LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap (w i n) := by
    intro i n
    obtain ⟨d1, d2, d3⟩ := BX.lift_down (B := B) Tw n (τ i (n + 1)) (th i (n + 1)) (w i (n + 1))
      (hthw i (n + 1)).1 (hthw i (n + 1)).2
    rw [← d3]
    apply BX.lift_indep (B := B) Tw.toATower n _ _ _ _ ?_ d2 (hthw i n).2
    rw [d1, ← hc i n, (hthw i n).1]
  have hbt : ∀ i, ∃ bt : B.gg ⊗[R₀] (Tw.O : Type u), ∀ n,
      LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap bt =
        LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap (w i n) := fun i =>
    BX.exists_lim_tensor (B := B) Tw (fun n => LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap (w i n))
      (hwb i)
  choose bt hbt using hbt
  refine ⟨ht, bt, fun i n => ?_, fun i n => ⟨th i n, w i n, (hthw i n).1, (hthw i n).2, (hbt i n).symm⟩⟩
  have hq : (Tw.q n).1.toLinearMap ∘ₗ ht i = h i n := by
    ext v
    simp [ht, hta_spec]
  rw [hq]
  exact hh i n

theorem htLin (B : BX R₀) (hB1 : PairingPropertiesStatement B) {p : ℕ} (Tw : ATower R₀ p) (Dp : ∀ n, DualPair (Tw.R n)) :
    HtLinStatement B Tw Dp := by
  intro ι _ τ ht a α hτ hH hα n
  have hN := Tw.char_R n
  have hy : ∀ i, (p ^ (n + 1)) • B.map (Tw.q n) (τ i n) = 0 := fun i => by
    rw [← map_nsmul, hτ i n, map_zero]
  have hlin : (Tw.q n).1.toLinearMap ∘ₗ ∑ i, α i • ht i =
      ∑ i, a i n • ((Tw.q n).1.toLinearMap ∘ₗ ht i) := by
    ext v
    simp [LinearMap.sum_apply, map_sum, map_mul, hα, zsmul_eq_mul]
  rw [map_sum, hlin]
  simp only [map_zsmul]
  exact BX.isHeight_sum (B := B) hB1 (Dp n) (p ^ (n + 1)) hN Finset.univ
    (fun i => a i n • B.map (Tw.q n) (τ i n)) (fun i => by rw [smul_comm, hy i, smul_zero])
    (fun i => a i n • ((Tw.q n).1.toLinearMap ∘ₗ ht i))
    (fun i => BX.isHeight_zsmul (B := B) hB1 (Dp n) (p ^ (n + 1)) hN (hy i) (hH i n) (a i n))

end ReciprocityTheory.PGsh
