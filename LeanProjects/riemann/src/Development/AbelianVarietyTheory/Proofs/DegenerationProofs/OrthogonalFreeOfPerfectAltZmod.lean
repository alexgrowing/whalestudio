import Mathlib

open Module TensorProduct

namespace GlobalTheory.ZModPerp

theorem exists_eq_nsmul_zmod {n r N : ℕ} [NeZero n] (h : r * N = n) (y : ZMod n)
    (hy : N • y = 0) : ∃ z : ZMod n, y = r • z := by
  have hN : N ≠ 0 := by
    rintro rfl
    exact NeZero.ne n (by simpa using h.symm)
  have h1 : ((N * y.val : ℕ) : ZMod n) = 0 := by
    simpa [nsmul_eq_mul] using hy
  rw [ZMod.natCast_eq_zero_iff] at h1
  replace h1 : N * r ∣ N * y.val := by rwa [mul_comm N r, h]
  obtain ⟨k, hk⟩ := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hN) h1
  refine ⟨(k : ZMod n), ?_⟩
  rw [← ZMod.natCast_zmod_val y, hk]
  simp [nsmul_eq_mul]

theorem dvd_of_forall_mul_eq_zero {n : ℕ} [NeZero n] (x y : ZMod n)
    (h : ∀ a : ZMod n, a * x = 0 → a * y = 0) : x ∣ y := by
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_right x.val n
  obtain ⟨k, hk⟩ := Nat.gcd_dvd_left x.val n
  have h1 : (m : ZMod n) * x = 0 := by
    have : ((m * x.val : ℕ) : ZMod n) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      refine ⟨k, ?_⟩
      calc m * x.val = m * (Nat.gcd x.val n * k) := by rw [← hk]
        _ = (Nat.gcd x.val n * m) * k := by ring
        _ = n * k := by rw [← hm]
    simpa using this
  obtain ⟨z, hz⟩ := exists_eq_nsmul_zmod hm.symm y (by simpa [nsmul_eq_mul] using h _ h1)
  have h2 := congrArg (Int.cast : ℤ → ZMod n) (Nat.gcd_eq_gcd_ab x.val n)
  simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
    ZMod.natCast_zmod_val] at h2
  rw [hz, nsmul_eq_mul, h2, mul_assoc]
  exact dvd_mul_right _ _

theorem isPrincipalIdealRing_zmod (n : ℕ) : IsPrincipalIdealRing (ZMod n) :=
  IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod n)) (ZMod.ringHom_surjective _)

theorem baer_zmod (n : ℕ) [NeZero n] : Module.Baer (ZMod n) (ZMod n) := by
  intro I g
  obtain ⟨x, rfl⟩ := ((isPrincipalIdealRing_zmod n).principal I).principal
  have hx : x ∈ Submodule.span (ZMod n) {x} := Submodule.mem_span_singleton_self x
  obtain ⟨c, hc⟩ := dvd_of_forall_mul_eq_zero x (g ⟨x, hx⟩) fun a ha => by
    rw [← smul_eq_mul, ← map_smul]
    have : a • (⟨x, hx⟩ : Submodule.span (ZMod n) {x}) = 0 := Subtype.ext ha
    rw [this, map_zero]
  refine ⟨LinearMap.toSpanSingleton _ _ c, fun y hy => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have : (⟨a • x, hy⟩ : Submodule.span (ZMod n) {x}) = a • ⟨x, hx⟩ := rfl
  rw [this, map_smul g, hc]
  simp [mul_assoc]

theorem exists_dual_ne_zero {n : ℕ} [NeZero n] {M : Type*} [AddCommGroup M] [Module (ZMod n) M]
    {q : M} (hq : q ≠ 0) : ∃ f : Dual (ZMod n) M, f q ≠ 0 := by
  obtain ⟨x, hx⟩ := ((isPrincipalIdealRing_zmod n).principal
    (LinearMap.ker (LinearMap.toSpanSingleton (ZMod n) M q))).principal
  have hx' : ∀ a : ZMod n, a • q = 0 ↔ x ∣ a := fun a => by
    rw [← Ideal.mem_span_singleton, ← Ideal.submodule_span_eq, ← hx]
    simp
  obtain ⟨c, hc, hc0⟩ : ∃ c : ZMod n, c * x = 0 ∧ c ≠ 0 := by
    by_contra! H
    have := dvd_of_forall_mul_eq_zero x 1 fun a ha => by simp [H a ha]
    exact hq (by simpa using (hx' 1).mpr this)
  have H : ∀ a : ZMod n, a • q = 0 → (RingHom.id (ZMod n)) a • c = 0 := fun a ha => by
    obtain ⟨b, rfl⟩ := (hx' a).mp ha
    simp only [RingHom.id_apply, smul_eq_mul]
    linear_combination b * hc
  let φ := LinearPMap.mkSpanSingleton' q c H
  obtain ⟨f, hf⟩ := (baer_zmod n).extension_property φ.domain.subtype
    φ.domain.subtype_injective φ.toFun
  refine ⟨f, ?_⟩
  have := LinearMap.congr_fun hf ⟨q, Submodule.mem_span_singleton_self q⟩
  have h2 := LinearPMap.mkSpanSingleton'_apply_self q c H (Submodule.mem_span_singleton_self q)
  have h3 : f q = c := this.trans h2
  rwa [h3]

theorem baer_of_free {n : ℕ} [NeZero n] (M : Type*) [AddCommGroup M] [Module (ZMod n) M]
    [Module.Free (ZMod n) M] [Module.Finite (ZMod n) M] : Module.Baer (ZMod n) M := by
  let b := Module.Free.chooseBasis (ZMod n) M
  refine Module.Baer.of_equiv b.equivFun.symm fun I g => ?_
  choose l hl using fun i => baer_zmod n I ((LinearMap.proj i).comp g)
  exact ⟨LinearMap.pi l, fun x hx => funext fun i => hl i x hx⟩

theorem exists_eq_nsmul_of_free {n r N : ℕ} [NeZero n] (h : r * N = n) {M : Type*}
    [AddCommGroup M] [Module (ZMod n) M] [Module.Free (ZMod n) M] [Module.Finite (ZMod n) M]
    (y : M) (hy : N • y = 0) : ∃ z : M, y = r • z := by
  let b := Module.Free.chooseBasis (ZMod n) M
  choose z hz using fun i => exists_eq_nsmul_zmod h (b.equivFun y i) (by
    rw [← Pi.smul_apply, ← map_nsmul, hy, map_zero, Pi.zero_apply])
  refine ⟨b.equivFun.symm z, b.equivFun.injective ?_⟩
  rw [map_nsmul, LinearEquiv.apply_symm_apply]
  exact funext hz

theorem free_of_isCompl {R M : Type*} [CommRing R] [Finite (MaximalSpectrum R)] [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] {T T' : Submodule R M} [Module.Free R T]
    (h : IsCompl T T') : Module.Free R T' := by
  let e := Submodule.prodEquivOfIsCompl T T' h
  have : Module.Finite R T := Module.Finite.of_surjective (T.projectionOnto T' h)
    (Submodule.projectionOnto_surjective h)
  have : Module.Finite R T' := Module.Finite.of_surjective (T'.projectionOnto T h.symm)
    (Submodule.projectionOnto_surjective h.symm)
  have : Module.Projective R T' :=
    Module.Projective.of_split T'.subtype (T'.projectionOnto T h.symm) (by ext; simp)
  refine Module.free_of_flat_of_finrank_eq R T' (finrank R M - finrank R T) fun P => ?_
  let := P.isMaximal
  let := Ideal.Quotient.field P.asIdeal
  have : Nontrivial R := (Ideal.Quotient.mk P.asIdeal).domain_nontrivial
  have e' : ((R ⧸ P.1) ⊗[R] M) ≃ₗ[R ⧸ P.1] ((R ⧸ P.1) ⊗[R] T) × ((R ⧸ P.1) ⊗[R] T') :=
    (e.symm.baseChange R (R ⧸ P.1) _ _).trans (TensorProduct.prodRight R (R ⧸ P.1) _ _ _)
  have := e'.finrank_eq
  rw [finrank_prod, finrank_baseChange, finrank_baseChange] at this
  omega

end GlobalTheory.ZModPerp

namespace GlobalTheory

open ZModPerp

theorem orthogonal_free_of_perfect_alt_zmod :
    ∀ (N r : ℕ) [NeZero (r * N)] (Γ : Type) [AddCommGroup Γ] [Module (ZMod (r * N)) Γ]
      [Module.Free (ZMod (r * N)) Γ] [Module.Finite (ZMod (r * N)) Γ]
      (e : LinearMap.BilinForm (ZMod (r * N)) Γ), e.IsAlt → Function.Bijective e →
      (∀ H : Submodule (ZMod (r * N)) Γ, e.orthogonal (e.orthogonal H) = H) ∧
      ∀ T : Submodule (ZMod (r * N)) Γ, Module.Free (ZMod (r * N)) T →
        (∃ T', IsCompl T T') ∧ Module.Free (ZMod (r * N)) (e.orthogonal T) ∧
        (∀ t ∈ T, N • t = 0 ↔ ∃ t' ∈ T, t = r • t') ∧
        ∀ a : Γ, (∀ t ∈ T, r • e a t = 0) ↔ ∃ h ∈ e.orthogonal T, r • a = r • h := by
  intro N r _ Γ _ _ _ _ e halt hbij
  have hmem : ∀ (H : Submodule (ZMod (r * N)) Γ) (x : Γ),
      x ∈ e.orthogonal H ↔ ∀ y ∈ H, e x y = 0 := fun H x => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    exact forall₂_congr fun y _ => ⟨halt.isRefl _ _, halt.isRefl _ _⟩
  have hkill : ∀ x : Γ, (r * N) • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod (r * N)), ZMod.natCast_self, zero_smul]
  refine ⟨fun H => le_antisymm (fun x hx => ?_) (fun x hx => ?_), fun T hT => ?_⟩
  · by_contra hxH
    obtain ⟨f, hf⟩ := exists_dual_ne_zero (n := r * N) (q := H.mkQ x)
      (by simpa using hxH)
    obtain ⟨b, hb⟩ := hbij.2 (f ∘ₗ H.mkQ)
    have hb' : b ∈ e.orthogonal H := (hmem _ _).mpr fun y hy => by
      rw [hb, LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero H).mpr hy,
        map_zero]
    have := halt.isRefl _ _ ((hmem _ _).mp hx b hb')
    rw [hb] at this
    exact hf this
  · exact (hmem _ _).mpr fun y hy => halt.isRefl _ _ ((hmem _ _).mp hy x hx)
  · obtain ⟨p, hp⟩ := (baer_of_free (n := r * N) T).extension_property T.subtype
      T.subtype_injective LinearMap.id
    have hp' : ∀ t : T, p t = t := fun t => LinearMap.congr_fun hp t
    have hc : IsCompl T (LinearMap.ker p) := LinearMap.isCompl_of_proj hp'
    refine ⟨⟨_, hc⟩, ?_, fun t ht => ⟨fun h => ?_, ?_⟩, fun a => ⟨fun h => ?_, ?_⟩⟩
    · have := free_of_isCompl hc
      have : Module.Free (ZMod (r * N)) (Γ ⧸ T) :=
        Module.Free.of_equiv (Submodule.quotientEquivOfIsCompl T _ hc).symm
      have E : e.orthogonal T ≃ₗ[ZMod (r * N)] T.dualAnnihilator :=
        (LinearEquiv.ofBijective e hbij).ofSubmodules _ _ (by
          ext f
          obtain ⟨b, rfl⟩ := hbij.2 f
          simp only [Submodule.mem_map, Submodule.mem_dualAnnihilator, hmem]
          constructor
          · rintro ⟨x, hx, hxb⟩
            rw [← hxb]
            exact hx
          · exact fun h => ⟨b, h, rfl⟩)
      exact Module.Free.of_equiv (E.trans T.dualQuotEquivDualAnnihilator.symm).symm
    · obtain ⟨z, hz⟩ := exists_eq_nsmul_of_free (n := r * N) rfl (⟨t, ht⟩ : T) (Subtype.ext h)
      exact ⟨z, z.2, congrArg Subtype.val hz⟩
    · rintro ⟨t', -, rfl⟩
      rw [← mul_smul, mul_comm, hkill]
    · obtain ⟨l, hl⟩ := exists_eq_nsmul_of_free (n := r * N) (mul_comm N r)
        (M := Dual (ZMod (r * N)) T) (e a ∘ₗ T.subtype) (LinearMap.ext fun t => h t t.2)
      obtain ⟨b, hb⟩ := hbij.2 (l ∘ₗ p)
      refine ⟨a - N • b, (hmem _ _).mpr fun y hy => ?_, ?_⟩
      · have h1 : e a y = N • l ⟨y, hy⟩ := LinearMap.congr_fun hl ⟨y, hy⟩
        have h2 : e b y = l ⟨y, hy⟩ := by
          rw [hb, LinearMap.comp_apply, hp' ⟨y, hy⟩]
        rw [map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, h1, h2, sub_self]
      · rw [smul_sub, ← mul_smul, hkill, sub_zero]
    · rintro ⟨h, hh, hah⟩ t ht
      rw [← LinearMap.smul_apply, ← map_nsmul, hah, map_nsmul, LinearMap.smul_apply,
        (hmem _ _).mp hh t ht, smul_zero]

end GlobalTheory
