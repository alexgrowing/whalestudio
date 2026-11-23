import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsoDifferBySimilitude

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

abbrev Mc (l : Level H) : Ideal (𝓞 E) := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)

theorem exists_idem (l : Level H) : ∃ e ∈ Mc l, 1 - e ∈ l.Mb := by
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.coprime]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  exact ⟨y, hy, by rw [← hxy, add_sub_cancel_right]; exact hx⟩

theorem M_pos (l : Level H) : 0 < l.M := by
  have := l.three_le
  omega

theorem modN_of_mem_span {n : ℕ} {a : D.La}
    (h : a ∈ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN n a := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨b, -, hb⟩ := h
  exact ⟨b, by rw [← hb, Nat.cast_smul_eq_nsmul]⟩

theorem modN_smul_Mb (l : Level H) {c : 𝓞 E} (hc : c ∈ Mc l) {a : D.La}
    (ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN l.M (c • a) := by
  apply modN_of_mem_span
  have h1 : c • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • l.Mb • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul hc ha
  rwa [← Submodule.mul_smul, mul_comm, l.prod] at h1

theorem modN_smul_Mc (l : Level H) {c : 𝓞 E} (hc : c ∈ l.Mb) {a : D.La}
    (ha : a ∈ Mc l • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN l.M (c • a) := by
  apply modN_of_mem_span
  have h1 : c • a ∈ l.Mb • l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul hc ha
  rwa [← Submodule.mul_smul, l.prod] at h1

theorem modN_of_mem_both (l : Level H) {a : D.La} (ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La))
    (ha' : a ∈ Mc l • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN l.M a := by
  obtain ⟨e, he, he'⟩ := exists_idem l
  obtain ⟨b₁, hb₁⟩ := modN_smul_Mb l he ha
  obtain ⟨b₂, hb₂⟩ := modN_smul_Mc l he' ha'
  refine ⟨b₁ + b₂, ?_⟩
  rw [smul_add, ← hb₁, ← hb₂, ← add_smul]
  simp

theorem nsmul_M_mem (l : Level H) (a : D.La) : l.M • a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  have hM : (l.M : 𝓞 E) ∈ l.Mb := by
    have h1 : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf.trans inf_le_left) h1
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul hM Submodule.mem_top

theorem add_map_zero {M Q : Type} [AddCommGroup M] [Group Q] {f : M → Q} (hf : ∀ a c, f (a + c) = f a * f c) :
    f 0 = 1 := by
  have h := hf 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := f 0) (by rw [_root_.mul_one]; exact h.symm)

theorem add_map_nsmul {M Q : Type} [AddCommGroup M] [Group Q] {f : M → Q} (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : M) : f (n • a) = f a ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero]; exact add_map_zero hf
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_pow_div (I : TateIso D k Q act e) {n N : ℕ} (hN : 0 < N) (h : n ∣ N) (a : D.La) :
    I.ev N a ^ (N / n) = I.ev n a := by
  have hn : 0 < n := Nat.pos_of_dvd_of_pos h hN
  have hq : 0 < N / n := Nat.div_pos (Nat.le_of_dvd hN h) hn
  have := I.tower n (N / n) hn hq a
  rwa [Nat.mul_div_cancel' h] at this

theorem zeta_pow_div (I : TateIso D k Q act e) {n N : ℕ} (hN : 0 < N) (h : n ∣ N) :
    I.ζ N ^ (N / n) = I.ζ n := by
  have hn : 0 < n := Nat.pos_of_dvd_of_pos h hN
  have hq : 0 < N / n := Nat.div_pos (Nat.le_of_dvd hN h) hn
  have := I.ζ_pow n (N / n) hn hq
  rwa [Nat.mul_div_cancel' h] at this

theorem exists_coprime_zpow {N : ℕ} (hN : 0 < N) {ζ ξ : kˣ} (hζ : IsPrimitiveRoot ζ N) (hξ : IsPrimitiveRoot ξ N) :
    ∃ ν : ℤ, IsCoprime ν (N : ℤ) ∧ ξ = ζ ^ ν := by
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨i, -, hi⟩ := (IsPrimitiveRoot.coe_units_iff.2 hζ).eq_pow_of_pow_eq_one (ξ := (ξ : k))
    (by rw [← Units.val_pow_eq_pow_val, hξ.pow_eq_one, Units.val_one])
  have hξi : ξ = ζ ^ i := Units.ext (by rw [Units.val_pow_eq_pow_val, hi])
  have hcop : i.Coprime N := (hζ.pow_iff_coprime hN i).1 (by rw [← hξi]; exact hξ)
  exact ⟨i, Nat.isCoprime_iff_coprime.2 hcop, by rw [hξi, zpow_natCast]⟩

theorem exists_adjust
    (hν : ∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ))
    (l : Level H) (N : ℕ)
    (hM : ∀ ν : ℤ, 0 < N → IsCoprime ν (N : ℤ) → (l.A : ℤ) ∣ ν - 1 → ∃ g : Sim D, (N : ℤ) ∣ g.ν N - ν ∧
      (l.A : ℤ) ∣ g.ν l.A - 1 ∧ (∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧
      ∀ a, D.ModN l.A (g.f l.A a - a))
    (I : TateIso D k Q act e) (hN : 0 < N) (hA : l.A ∣ N) {ξ : kˣ} (hξ : IsPrimitiveRoot ξ N)
    (h : ξ ^ (N / l.A) = I.ζ l.A) :
    ∃ I' : TateIso D k Q act e, I'.ζ N = ξ ∧ (∀ a, I'.ev l.A a = I.ev l.A a) ∧
      ∀ a ∈ Mc l • (⊤ : Submodule (𝓞 E) D.La), I'.ev l.M a = I.ev l.M a := by
  obtain ⟨ν, hνc, hξν⟩ := exists_coprime_zpow hN (I.ζ_prim N hN) hξ
  have hA0 := l.A_pos
  have h1 : I.ζ l.A ^ ν = I.ζ l.A := by
    calc I.ζ l.A ^ ν = ((I.ζ N) ^ (N / l.A)) ^ ν := by rw [zeta_pow_div I hN hA]
      _ = ((I.ζ N) ^ ν) ^ (N / l.A) := by simp only [← zpow_natCast, ← zpow_mul, mul_comm]
      _ = I.ζ l.A := by rw [← hξν, h]
  have hA1 : (l.A : ℤ) ∣ ν - 1 := by
    refine ((I.ζ_prim l.A hA0).zpow_eq_one_iff_dvd _).1 ?_
    rw [zpow_sub, zpow_one, h1, mul_inv_cancel]
  obtain ⟨g, hgN, -, hgM, hgA⟩ := hM ν hN hνc hA1
  refine ⟨LevelTwist.twist I g (hν g), ?_, fun a => ?_, fun a ha => ?_⟩
  · rw [LevelTwist.twist_ζ, hξν]
    exact LevelTwist.zeta_zpow_congr I hN hgN
  · rw [LevelTwist.twist_ev]
    exact LevelTwist.ev_congr I hA0 (hgA a)
  · rw [LevelTwist.twist_ev]
    refine LevelTwist.ev_congr I (M_pos l) (modN_of_mem_both l (hgM a) ?_)
    exact Submodule.sub_mem _ (LevelTwist.map_mem_smul_top _ _ ha) ha

theorem exists_of_level
    (hν : ∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ))
    (N : ℕ)
    (hL : ∀ (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) →
      (∀ a b, (N : ℤ) ∣ D.EF (f a) (f b) - ν * D.EF a b) →
      ∃ g : Sim D, (∀ a, D.ModN N (g.f N a - f a)) ∧ (N : ℤ) ∣ g.ν N - ν)
    (he : ∀ x y c c', e N x y c → e N x y c' → c = c')
    (I : TateIso D k Q act e) (hN : 0 < N) {ξ : kˣ} (hξ : IsPrimitiveRoot ξ N) (α : D.La → Q)
    (hadd : ∀ a c, α (a + c) = α a * α c) (hpow : ∀ a, α a ^ N = 1) (hlin : ∀ c a, α (c • a) = act c (α a))
    (hiso : ∀ a b, e N (α a) (α b) (ξ ^ D.EF a b)) :
    ∃ I' : TateIso D k Q act e, I'.ζ N = ξ ∧ ∀ a, I'.ev N a = α a := by
  classical
  choose b hb using fun a => (I.onto N hN (α a)).1 (hpow a)
  let K : Submodule (𝓞 E) D.La := LinearMap.range ((N : 𝓞 E) • LinearMap.id)
  have memK : ∀ x y, I.ev N x = I.ev N y → x - y ∈ K := by
    intro x y hxy
    obtain ⟨z, hz⟩ := (tateIso_ev_eq_iff I hN x y).1 hxy
    exact LinearMap.mem_range.2
      ⟨z, by rw [hz, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul]⟩
  let β : D.La →ₗ[𝓞 E] D.La ⧸ K :=
    { toFun := fun a => Submodule.Quotient.mk (b a)
      map_add' := fun a c => by
        rw [← Submodule.Quotient.mk_add]
        refine (Submodule.Quotient.eq K).2 (memK _ _ ?_)
        rw [hb, I.add, hb, hb, hadd]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
        refine (Submodule.Quotient.eq K).2 (memK _ _ ?_)
        rw [hb, I.lin, hb, hlin] }
  have := D.proj
  obtain ⟨f, hf⟩ := Module.projective_lifting_property K.mkQ β K.mkQ_surjective
  have hfα : ∀ a, I.ev N (f a) = α a := by
    intro a
    have h1 : (Submodule.Quotient.mk (f a) : D.La ⧸ K) = Submodule.Quotient.mk (b a) :=
      LinearMap.congr_fun hf a
    obtain ⟨z, hz⟩ := LinearMap.mem_range.1 ((Submodule.Quotient.eq K).1 h1)
    rw [← hb a]
    exact (tateIso_ev_eq_iff I hN _ _).2
      ⟨z, by rw [← hz, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul]⟩
  obtain ⟨ν, hνc, hξν⟩ := exists_coprime_zpow hN (I.ζ_prim N hN) hξ
  have hEF : ∀ a c, (N : ℤ) ∣ D.EF (f a) (f c) - ν * D.EF a c := by
    intro a c
    have h1 := I.isom N hN (f a) (f c)
    rw [hfα, hfα] at h1
    have h2 := he _ _ _ _ (hiso a c) h1
    rw [hξν, ← zpow_mul] at h2
    refine ((I.ζ_prim N hN).zpow_eq_one_iff_dvd _).1 ?_
    rw [zpow_sub, ← h2, mul_inv_cancel]
  obtain ⟨g, hgf, hgν⟩ := hL f ν hN hνc hEF
  refine ⟨LevelTwist.twist I g (hν g), ?_, fun a => ?_⟩
  · rw [LevelTwist.twist_ζ, hξν]
    exact LevelTwist.zeta_zpow_congr I hN hgν
  · rw [LevelTwist.twist_ev, ← hfα a]
    exact LevelTwist.ev_congr I hN (hgf a)

theorem exists_root_ext (B : Type) [Field B] [CharZero B] {A N : ℕ} (hN : 0 < N) (hA : A ∣ N) {ζ : B}
    (hζ : IsPrimitiveRoot ζ A) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra B L) (ξ : Lˣ), FiniteDimensional B L ∧ IsPrimitiveRoot ξ N ∧
      (ξ : L) ^ (N / A) = algebraMap B L ζ := by
  classical
  have : NeZero N := ⟨hN.ne'⟩
  have hA0 : 0 < A := Nat.pos_of_dvd_of_pos hA hN
  have : NeZero A := ⟨hA0.ne'⟩
  have hω := IsCyclotomicExtension.zeta_spec N B (CyclotomicField N B)
  set ω := IsCyclotomicExtension.zeta N B (CyclotomicField N B)
  have hq : 0 < N / A := Nat.div_pos (Nat.le_of_dvd hN hA) hA0
  have hω' : IsPrimitiveRoot (ω ^ (N / A)) A := by
    have := hω.pow_of_dvd hq.ne' (Nat.div_dvd_of_dvd hA)
    rwa [Nat.div_div_self hA hN.ne'] at this
  have hη : IsPrimitiveRoot (algebraMap B (CyclotomicField N B) ζ) A :=
    hζ.map_of_injective (algebraMap B (CyclotomicField N B)).injective
  obtain ⟨i, hiA, hi⟩ := hω'.eq_pow_of_pow_eq_one hη.pow_eq_one
  have hic : i.Coprime A := (hω'.pow_iff_coprime hA0 i).1 (by rw [hi]; exact hη)
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hA (ZMod.unitOfCoprime i hic)
  have hji : (v : ZMod N).val % A = i % A := by
    have h1 := congrArg (fun u : (ZMod A)ˣ => (u : ZMod A)) hv
    simp only [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime] at h1
    rw [← ZMod.natCast_val] at h1
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).1 h1
  have hξ : IsPrimitiveRoot (ω ^ (v : ZMod N).val) N := hω.pow_of_coprime _ (ZMod.val_coe_unit_coprime v)
  refine ⟨CyclotomicField N B, inferInstance, inferInstance, (hξ.isUnit hN.ne').unit, ?_, ?_, ?_⟩
  · exact IsCyclotomicExtension.finiteDimensional {N} B (CyclotomicField N B)
  · exact IsPrimitiveRoot.coe_units_iff.1 (by rw [IsUnit.unit_spec]; exact hξ)
  · rw [IsUnit.unit_spec, ← pow_mul, mul_comm, pow_mul, pow_eq_pow_mod _ hω'.pow_eq_one, hji,
      Nat.mod_eq_of_lt hiA, hi]

end GlobalTheory.LevCover
