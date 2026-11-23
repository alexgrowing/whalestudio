import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.IsPairingValueAddRight

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace OAdj

variable {B : BX R₀} {O : LAlg R₀} (A : OAdj B O) {R : LAlg R₀} (s : LHom O R)

lemma e_hcongr {x₁ x₂ z₁ z₂ : B.G R} (hx : x₁ = x₂) (hz : z₁ = z₂)
    {u₁ : B.P R (A.a.f s x₁) z₁} {u₂ : B.P R (A.a.f s x₂) z₂} (hu : HEq u₁ u₂) :
    HEq (A.e s x₁ z₁ u₁) (A.e s x₂ z₂ u₂) := by
  subst hx hz; cases eq_of_heq hu; rfl

lemma e_zero1 (z : B.G R) :
    HEq (A.e s 0 z (B.tr1 (map_zero (A.a.f s)).symm (B.zero1 z))) (B.zero1 (A.ab.f s z)) := by
  set w0 := B.tr1 (map_zero (A.a.f s)).symm (B.zero1 z) with hw0
  have hw : HEq w0 (B.zero1 z) := B.castFst_heq _ _
  have h1 := A.equiv_addFst s 0 0 z w0 w0
  have h2 : HEq (A.e s (0 + 0) z (B.tr1 (map_add (A.a.f s) 0 0).symm (B.add1 w0 w0)))
      (A.e s 0 z w0) := by
    refine A.e_hcongr s (add_zero 0) rfl ?_
    refine (B.castFst_heq _ _).trans ?_
    refine (B.addFst_hcongr (map_zero _) (map_zero _) rfl hw hw).trans ?_
    exact (B.zeroFst_add (B.zero1 z)).trans hw.symm
  have hid : B.S1mk (A.e s 0 z w0) + B.S1mk (A.e s 0 z w0) = B.S1mk (A.e s 0 z w0) :=
    Sigma.ext (add_zero (0 : B.G R)) ((heq_of_eq h1.symm).trans h2)
  exact (Sigma.ext_iff.1 (B.fibreFst_idem _ hid)).2

lemma e_zero2 (x : B.G R) : HEq (A.e s x 0 (B.zero2 (A.a.f s x))) (B.zero2 x) := by
  set w0 := B.zero2 (A.a.f s x) with hw0
  have h1 := A.equiv_addSnd s x 0 0 w0 w0
  have h2 : HEq (A.e s x (0 + 0) (B.add2 w0 w0)) (A.e s x 0 w0) :=
    A.e_hcongr s rfl (add_zero 0) (B.zeroSnd_add w0)
  have hz : A.ab.f s 0 + A.ab.f s 0 = A.ab.f s 0 := by rw [map_zero, add_zero]
  have hid : B.S2mk (A.e s x 0 w0) + B.S2mk (A.e s x 0 w0) = B.S2mk (A.e s x 0 w0) :=
    Sigma.ext hz ((B.castSnd_heq _ _).symm.trans ((heq_of_eq h1).symm.trans h2))
  exact (Sigma.ext_iff.1 (B.fibreSnd_idem _ hid)).2

lemma e_nsmul1 (x z : B.G R) (u : B.P R (A.a.f s x) z) (n : ℕ)
    (w : B.P R (A.a.f s (n • x)) z) (hw : HEq w (B.nsmul1 u n)) :
    HEq (A.e s (n • x) z w) (B.nsmul1 (A.e s x z u) n) := by
  induction n with
  | zero =>
    refine (A.e_hcongr s (zero_nsmul x) rfl
      (u₂ := B.tr1 (map_zero (A.a.f s)).symm (B.zero1 z)) ?_).trans ?_
    · exact hw.trans ((B.castFst_heq _ _).trans (B.castFst_heq _ _).symm)
    · exact (A.e_zero1 s z).trans (B.castFst_heq _ _).symm
  | succ n ih =>
    have hn : A.a.f s (n • x) = n • A.a.f s x := map_nsmul _ n x
    have h1 := ih (B.tr1 hn.symm (B.nsmul1 u n)) (B.castFst_heq _ _)
    refine (A.e_hcongr s (succ_nsmul x n) rfl
      (u₂ := B.tr1 (map_add (A.a.f s) (n • x) x).symm (B.add1 (B.tr1 hn.symm (B.nsmul1 u n)) u))
      ?_).trans ?_
    · refine hw.trans ((B.castFst_heq _ _).trans ?_)
      exact (B.addFst_hcongr hn.symm rfl rfl (B.castFst_heq _ _).symm HEq.rfl).trans (B.castFst_heq _ _).symm
    · rw [A.equiv_addFst]
      exact (B.addFst_hcongr rfl rfl rfl h1 HEq.rfl).trans (B.castFst_heq _ _).symm

lemma e_nsmul2 (x z : B.G R) (u : B.P R (A.a.f s x) z) (n : ℕ) :
    HEq (A.e s x (n • z) (B.nsmul2 u n)) (B.nsmul2 (A.e s x z u) n) := by
  induction n with
  | zero =>
    exact (A.e_hcongr s rfl (zero_nsmul z) (B.castSnd_heq _ _)).trans
      ((A.e_zero2 s x).trans (B.castSnd_heq _ _).symm)
  | succ n ih =>
    refine (A.e_hcongr s rfl (succ_nsmul z n) (B.castSnd_heq _ _)).trans ?_
    rw [A.equiv_addSnd]
    refine (B.castSnd_heq _ _).trans ?_
    exact (B.addSnd_hcongr rfl (map_nsmul _ n z) rfl ih HEq.rfl).trans (B.castSnd_heq _ _).symm

theorem pairing_of (N : ℕ) (x z : B.G R) (w : (R : Type u)ˣ) (hx : N • x = 0)
    (h : B.IsPairing N (A.a.f s x) z w) : B.IsPairing N x (A.ab.f s z) w := by
  obtain ⟨hax, hz, u, l₁, l₂, h1, h2, rfl⟩ := h
  have hbz : N • A.ab.f s z = 0 := by rw [← map_nsmul, hz, map_zero]
  refine ⟨hx, hbz, A.e s x z u, l₁, l₂, ?_, ?_, rfl⟩
  · have hn : A.a.f s (N • x) = N • A.a.f s x := map_nsmul _ N x
    have k1 := A.e_nsmul1 s x z u N (B.tr1 hn.symm (B.nsmul1 u N)) (B.castFst_heq _ _)
    have k2 : HEq (A.e s (N • x) z (B.tr1 hn.symm (B.nsmul1 u N)))
        (A.e s 0 z (B.tr1 (map_zero (A.a.f s)).symm (B.smul l₁ (B.zero1 z)))) := by
      refine A.e_hcongr s hx rfl ?_
      refine (B.castFst_heq _ _).trans ?_
      exact ((B.castFst_heq hax _).symm.trans (heq_of_eq h1)).trans (B.castFst_heq _ _).symm
    rw [B.castFst_smul, A.e_smul] at k2
    apply eq_of_heq
    refine (B.castFst_heq _ _).trans (k1.symm.trans (k2.trans ?_))
    exact B.smul_hcongr rfl rfl l₁ (A.e_zero1 s z)
  · have k1 := A.e_nsmul2 s x z u N
    have k2 : HEq (A.e s x (N • z) (B.nsmul2 u N))
        (A.e s x 0 (B.smul l₂ (B.zero2 (A.a.f s x)))) :=
      A.e_hcongr s rfl hz ((B.castSnd_heq hz _).symm.trans (heq_of_eq h2))
    rw [A.e_smul] at k2
    apply eq_of_heq
    refine (B.castSnd_heq _ _).trans (k1.symm.trans (k2.trans ?_))
    exact B.smul_hcongr rfl (map_zero _) l₂ (A.e_zero2 s x)

theorem pairing_iff (N : ℕ) (x z : B.G R) (w : (R : Type u)ˣ) (hx : N • x = 0) (hz : N • z = 0) :
    B.IsPairing N (A.a.f s x) z w ↔ B.IsPairing N x (A.ab.f s z) w := by
  refine ⟨A.pairing_of s N x z w hx, fun h => ?_⟩
  have hax : N • A.a.f s x = 0 := by rw [← map_nsmul, hx, map_zero]
  obtain ⟨w', hw'⟩ := B.pairing_exists N _ z hax hz
  rwa [B.pairing_unique N x _ _ _ (A.pairing_of s N x z w' hx hw') h] at hw'

end OAdj

namespace DualPair

variable {R : LAlg R₀} (Dp : DualPair R)

lemma π_η : Dp.π.1 Dp.η = 0 := by
  have h := Dp.η_mem
  rwa [Submodule.restrictScalars_mem, RingHom.mem_ker] at h

lemma sub_mem_span (d : (Dp.D : Type u)) : d - Dp.σ.1 (Dp.π.1 d) ∈ Ideal.span {Dp.η} := by
  rw [← Dp.ker_eq, RingHom.mem_ker, map_sub, Dp.sect, sub_self]

lemma mul_span (a b : (Dp.D : Type u)) (ha : a ∈ Ideal.span {Dp.η}) (hb : b ∈ Ideal.span {Dp.η}) :
    a * b = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hb
  calc c * Dp.η * (d * Dp.η) = c * d * (Dp.η * Dp.η) := by ring
    _ = 0 := by rw [Dp.η_sq, mul_zero]

def mr (r : (R : Type u)) : LHom Dp.D Dp.D :=
  ⟨{ toFun := fun d => Dp.σ.1 (Dp.π.1 d) + Dp.σ.1 r * (d - Dp.σ.1 (Dp.π.1 d))
     map_one' := by simp
     map_mul' := fun d e => by
       have hk := Dp.mul_span _ _ (Dp.sub_mem_span d) (Dp.sub_mem_span e)
       simp only [map_mul]
       linear_combination (Dp.σ.1 r - Dp.σ.1 r * Dp.σ.1 r) * hk
     map_zero' := by simp
     map_add' := fun d e => by simp only [map_add]; ring
     commutes' := fun c => by simp },
   ⟨fun d hd => by
     have h1 := hd.map Dp.π.1
     have e : Dp.π.1 (Dp.σ.1 (Dp.π.1 d) + Dp.σ.1 r * (d - Dp.σ.1 (Dp.π.1 d))) = Dp.π.1 d := by
       simp [Dp.sect]
     refine Dp.π.2.map_nonunit d ?_
     convert h1 using 1
     exact e.symm⟩⟩

lemma mr_apply (r : (R : Type u)) (d : (Dp.D : Type u)) :
    (Dp.mr r).1 d = Dp.σ.1 (Dp.π.1 d) + Dp.σ.1 r * (d - Dp.σ.1 (Dp.π.1 d)) := rfl

lemma mr_π (r : (R : Type u)) (d : (Dp.D : Type u)) : Dp.π.1 ((Dp.mr r).1 d) = Dp.π.1 d := by
  simp [mr_apply, Dp.sect]

lemma mr_comp_σ (r : (R : Type u)) : (Dp.mr r).comp Dp.σ = Dp.σ :=
  Subtype.ext (AlgHom.ext fun t => by
    show (Dp.mr r).1 (Dp.σ.1 t) = Dp.σ.1 t
    simp [mr_apply, Dp.sect])

lemma mr_ση (r t : (R : Type u)) :
    (Dp.mr r).1 (Dp.σ.1 t * Dp.η) = Dp.σ.1 r * (Dp.σ.1 t * Dp.η) := by
  simp [mr_apply, Dp.π_η]

lemma mr_ker (r : (R : Type u)) :
    ∀ a ∈ Dp.π.ker, (Dp.mr r).1.toLinearMap a ∈ Dp.π.ker := by
  intro a ha
  rw [Submodule.restrictScalars_mem, RingHom.mem_ker] at ha ⊢
  rw [AlgHom.toLinearMap_apply, Dp.mr_π, ha]

end DualPair

lemma hext_tmul (B : BX R₀) {R : LAlg R₀} (h : B.gg →ₗ[R₀] (R : Type u)) (w : B.gg) (r : (R : Type u)) :
    hext B h (w ⊗ₜ r) = h w * r := by
  simp [hext]

theorem ht_ext (B : BX R₀) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ) (y : B.G R)
    (h : B.gg →ₗ[R₀] (R : Type u)) (hy : N • y = 0) (hH : B.IsHeight Dp N y h)
    (V : B.gg ⊗[R₀] (R : Type u)) :
    ∃ z : (Dp.D : Type u)ˣ,
      B.IsPairing N (B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg Dp.ηmap V)) (B.map Dp.σ y) z ∧
        (z : (Dp.D : Type u)) = 1 + Dp.σ.1 (hext B h V) * Dp.η := by
  induction V using TensorProduct.induction_on with
  | zero =>
    have hY : N • B.map Dp.σ y = 0 := by rw [← map_nsmul, hy, map_zero]
    obtain ⟨z, hz⟩ := B.pairing_exists N (0 : B.G Dp.D) _ (smul_zero N) hY
    have h2 := B.isPairingValue_add_left N 0 0 _ z z hz hz
    rw [add_zero] at h2
    have hzz : z * z = z * 1 := by rw [mul_one]; exact (B.pairing_unique N _ _ _ _ hz h2).symm
    have h1 : z = 1 := mul_left_cancel hzz
    subst h1
    refine ⟨1, by simpa using hz, by simp⟩
  | tmul w r =>
    obtain ⟨z, hz, ez⟩ := hH w
    have k := B.pairing_map (Dp.mr r) N _ _ z hz
    have e1 : B.map (Dp.mr r) (B.tg Dp.π Dp.sqZero (w ⊗ₜ Dp.ηk)) =
        B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg Dp.ηmap (w ⊗ₜ r)) := by
      rw [← B.tg_nat Dp.π Dp.π Dp.sqZero Dp.sqZero (Dp.mr r) (Dp.mr_ker r),
        LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
      congr 2
      exact Subtype.ext (by simp [DualPair.ηk, DualPair.ηmap, DualPair.mr_apply, Dp.π_η, LinearMap.restrict_apply])
    have e2 : B.map (Dp.mr r) (B.map Dp.σ y) = B.map Dp.σ y := by
      rw [← B.map_comp, Dp.mr_comp_σ]
    rw [e1, e2] at k
    refine ⟨_, k, ?_⟩
    simp only [Units.coe_map, MonoidHom.coe_coe]
    rw [ez, map_add, map_one, Dp.mr_ση, hext_tmul, map_mul]
    ring
  | add V V' ihV ihV' =>
    obtain ⟨z, hz, ez⟩ := ihV
    obtain ⟨z', hz', ez'⟩ := ihV'
    refine ⟨z * z', ?_, ?_⟩
    · rw [map_add, map_add]
      exact B.isPairingValue_add_left N _ _ _ z z' hz hz'
    · rw [Units.val_mul, ez, ez', map_add, map_add]
      linear_combination (Dp.σ.1 (hext B h V) * Dp.σ.1 (hext B h V')) * Dp.η_sq

namespace OAdj

variable {B : BX R₀} {O : LAlg R₀} (A : OAdj B O) {R : LAlg R₀} (s : LHom O R)

theorem ht_a (Dp : DualPair R) (N : ℕ) (y : B.G R) (h : B.gg →ₗ[R₀] (R : Type u))
    (δ : B.gg →ₗ[R₀] B.gg ⊗[R₀] (R : Type u)) (hy : N • y = 0) (hH : B.IsHeight Dp N y h)
    (hδ : ∀ v, A.ab.f (Dp.σ.comp s) (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) =
      B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg Dp.ηmap (δ v))) :
    B.IsHeight Dp N (A.a.f s y) (hext B h ∘ₗ δ) := by
  intro v
  obtain ⟨z, hz, ez⟩ := ht_ext B Dp N y h hy hH (δ v)
  rw [← hδ v] at hz
  obtain ⟨z0, hz0, -⟩ := hH v
  obtain ⟨hX, hY, -⟩ := hz0
  have k1 := B.pairing_sw N _ _ z hz
  have k2 := (A.pairing_iff (Dp.σ.comp s) N _ _ z⁻¹ hY hX).2 k1
  have k3 := B.pairing_sw N _ _ _ k2
  rw [inv_inv, A.a.nat] at k3
  exact ⟨z, k3, by rw [ez]; rfl⟩

end OAdj

theorem linHt (B : BX R₀) (O : LAlg R₀) : LinHtStatement B O :=
  fun A _ s Dp N y h δ hy hH hδ => A.ht_a s Dp N y h δ hy hH hδ

end ReciprocityTheory.PGsh
