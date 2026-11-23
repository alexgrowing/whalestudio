import Mathlib

namespace GlobalTheory.DualParts

theorem card_le_of_injective_chars (G H : Type) [CommGroup G] [Finite G] (U : Type) [CommRing U]
    [IsDomain U] (f : H → (G →* Uˣ)) (hf : Function.Injective f) :
    Finite H ∧ Nat.card H ≤ Nat.card G := by
  classical
  haveI := Fintype.ofFinite G
  let g : H → (G →* U) := fun h => (Units.coeHom U).comp (f h)
  have hg : Function.Injective g := by
    intro a b hab
    apply hf
    refine MonoidHom.ext fun x => Units.ext ?_
    have := congrArg (fun χ : G →* U => χ x) hab
    simpa [g] using this
  have hli : LinearIndependent U (fun h => (g h : G → U)) :=
    (linearIndependent_monoidHom G U).comp g hg
  haveI : Finite H := hli.finite
  haveI := Fintype.ofFinite H
  refine ⟨inferInstance, ?_⟩
  have := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at this
  simpa [Nat.card_eq_fintype_card] using this

theorem conj_dual_parts : ∀ (O : Type) [CommRing O] (bar : O →+* O) (U : Type) [CommRing U] [IsDomain U] (M M' : Type) [CommGroup M] [CommGroup M'] (α : O → M →* M) (α' : O → M' →* M'), (∀ y, α 1 y = y) → (∀ a b y, α (a * b) y = α a (α b y)) → (∀ a b y, α (a + b) y = α a y * α b y) → (∀ x, α' 1 x = x) → (∀ a b x, α' (a * b) x = α' a (α' b x)) → (∀ a b x, α' (a + b) x = α' a x * α' b x) → (∀ a, bar (bar a) = a) → ∀ (e : M' →* M →* Uˣ) (e' : M →* M' →* Uˣ), Function.Injective e → Function.Injective e' → (∀ a x y, e (α' a x) y = e x (α (bar a) y)) → (∀ a y x, e' (α a y) x = e' y (α' (bar a) x)) → ∀ (u w : Ideal O) (n : ℕ), u ≤ w → u ⊔ u.map bar = ⊤ → (∀ a ∈ (u * u.map bar) ^ n, (∀ y, α a y = 1) ∧ ∀ x, α' a x = 1) → (∀ y, (∃ m : ℕ, ∀ a ∈ u ^ m, α a y = 1) → ∀ a ∈ w, α a y = 1) → Finite {y : M // ∀ a ∈ w, α a y = 1} → (∀ x, (∃ m : ℕ, ∀ a ∈ (u.map bar) ^ m, α' a x = 1) → ∀ a ∈ w.map bar, α' a x = 1) ∧ Nat.card {x : M' // ∀ a ∈ w.map bar, α' a x = 1} = Nat.card {y : M // ∀ a ∈ w, α a y = 1} := by
  intro O _ bar U _ _ M M' _ _ α α' h1 hmul hadd h1' hmul' hadd' hbb e e' he he' hee hee' u w n huw hcop
    hkill hw hfin
  have hsurj : Function.Surjective bar := fun a => ⟨bar a, hbb a⟩
  have hbarbar : (u.map bar).map bar = u := by
    rw [Ideal.map_map]
    have : bar.comp bar = RingHom.id O := RingHom.ext hbb
    rw [this, Ideal.map_id]
  have hsplit : ∀ k : ℕ, ∃ a₀ ∈ u ^ k, ∃ b₀ ∈ (u.map bar) ^ k, a₀ + b₀ = 1 := by
    intro k
    have hc : IsCoprime u (u.map bar) := Ideal.isCoprime_iff_sup_eq.2 hcop
    have hs : u ^ k ⊔ (u.map bar) ^ k = ⊤ := Ideal.isCoprime_iff_sup_eq.1 (hc.pow)
    have h1mem : (1 : O) ∈ u ^ k ⊔ (u.map bar) ^ k := by rw [hs]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1mem
    exact ⟨a, ha, b, hb, hab⟩
  have hbar1 : ∀ k, ∀ a ∈ u ^ k, bar a ∈ (u.map bar) ^ k := by
    intro k a ha
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem bar ha
  have hbar2 : ∀ k, ∀ b ∈ (u.map bar) ^ k, bar b ∈ u ^ k := by
    intro k b hb
    have := Ideal.mem_map_of_mem bar hb
    rwa [Ideal.map_pow, hbarbar] at this
  have hprod : ∀ k, n ≤ k → ∀ a ∈ u ^ k, ∀ b ∈ (u.map bar) ^ k, a * b ∈ (u * u.map bar) ^ n := by
    intro k hk a ha b hb
    have : a * b ∈ (u * u.map bar) ^ k := by rw [mul_pow]; exact Ideal.mul_mem_mul ha hb
    exact Ideal.pow_le_pow_right hk this
  have hpowle : ∀ (I : Ideal O) (k m : ℕ), m ≤ k → I ^ k ≤ I ^ m := fun I k m h =>
    Ideal.pow_le_pow_right h

  have part1 : ∀ x, (∃ m : ℕ, ∀ a ∈ (u.map bar) ^ m, α' a x = 1) → ∀ a ∈ w.map bar, α' a x = 1 := by
    rintro x ⟨m, hm⟩ c hc
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective bar hsurj).1 hc
    apply he
    rw [map_one]
    refine MonoidHom.ext fun y => ?_
    rw [MonoidHom.one_apply, hee, hbb]
    obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := hsplit (m + n)
    have hy : y = α a₀ y * α b₀ y := by rw [← hadd, hab, h1]
    rw [hy, map_mul, map_mul]
    have t1 : e x (α a (α a₀ y)) = 1 := by
      rw [← hmul, ← hbb (a * a₀), ← hee, map_mul bar, hmul',
        hm (bar a₀) (hpowle _ (m + n) m (by omega) (hbar1 _ a₀ ha₀))]
      simp
    have t2 : α a (α b₀ y) = 1 := by
      refine hw (α b₀ y) ⟨m + n, fun c hc => ?_⟩ a ha
      rw [← hmul]; exact (hkill _ (hprod (m + n) (by omega) c hc b₀ hb₀)).1 y
    rw [t1, t2, map_one, one_mul]
  refine ⟨part1, ?_⟩

  obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := hsplit (n + 1)
  let A : Subgroup M :=
    { carrier := {y | ∀ a ∈ w, α a y = 1}
      one_mem' := fun a _ => map_one (α a)
      mul_mem' := fun {y z} hy hz a ha => by
        rw [map_mul, (show ∀ a ∈ w, α a y = 1 from hy) a ha,
          (show ∀ a ∈ w, α a z = 1 from hz) a ha, one_mul]
      inv_mem' := fun {y} hy a ha => by
        rw [map_inv, (show ∀ a ∈ w, α a y = 1 from hy) a ha, inv_one] }
  let B : Subgroup M' :=
    { carrier := {x | ∀ a ∈ w.map bar, α' a x = 1}
      one_mem' := fun a _ => map_one (α' a)
      mul_mem' := fun {y z} hy hz a ha => by
        rw [map_mul, (show ∀ a ∈ w.map bar, α' a y = 1 from hy) a ha,
          (show ∀ a ∈ w.map bar, α' a z = 1 from hz) a ha, one_mul]
      inv_mem' := fun {y} hy a ha => by
        rw [map_inv, (show ∀ a ∈ w.map bar, α' a y = 1 from hy) a ha, inv_one] }
  have hu1 : u ^ (n + 1) ≤ u := Ideal.pow_le_self (by omega)
  have hub1 : (u.map bar) ^ (n + 1) ≤ u.map bar := Ideal.pow_le_self (by omega)

  have F1 : ∀ y, α b₀ y ∈ A := by
    intro y
    refine hw (α b₀ y) ⟨n + 1, fun c hc => ?_⟩
    rw [← hmul]; exact (hkill _ (hprod (n + 1) (by omega) c hc b₀ hb₀)).1 y
  have F2 : ∀ x ∈ B, α' (bar a₀) x = 1 := fun x hx =>
    hx _ (Ideal.map_mono huw (hub1 (hbar1 _ a₀ ha₀)))
  have E1 : ∀ x ∈ B, ∀ y, e x y = e x (α b₀ y) := by
    intro x hx y
    conv_lhs => rw [← h1 y, ← hab, hadd, map_mul]
    rw [← hbb a₀, ← hee, F2 x hx]
    simp
  have F3 : ∀ x, α' a₀ x ∈ B := by
    intro x
    refine part1 (α' a₀ x) ⟨n + 1, fun c hc => ?_⟩
    rw [← hmul', mul_comm]; exact (hkill _ (hprod (n + 1) (by omega) a₀ ha₀ c hc)).2 x
  have F4 : ∀ y ∈ A, α (bar b₀) y = 1 := fun y hy => hy _ (huw (hu1 (hbar2 _ b₀ hb₀)))
  have E2 : ∀ y ∈ A, ∀ x, e' y x = e' y (α' a₀ x) := by
    intro y hy x
    conv_lhs => rw [← h1' x, ← hab, hadd', map_mul]
    rw [← hbb b₀, ← hee', F4 y hy]
    simp
  haveI : Finite A := hfin
  have hAB : Finite B ∧ Nat.card B ≤ Nat.card A := by
    refine card_le_of_injective_chars A B U (fun x => (e x.1).comp A.subtype) ?_
    intro x₁ x₂ h
    apply Subtype.ext
    apply he
    refine MonoidHom.ext fun y => ?_
    rw [E1 x₁.1 x₁.2, E1 x₂.1 x₂.2]
    exact congrArg (fun χ : A →* Uˣ => χ ⟨α b₀ y, F1 y⟩) h
  haveI : Finite B := hAB.1
  have hBA : Finite A ∧ Nat.card A ≤ Nat.card B := by
    refine card_le_of_injective_chars B A U (fun y => (e' y.1).comp B.subtype) ?_
    intro y₁ y₂ h
    apply Subtype.ext
    apply he'
    refine MonoidHom.ext fun x => ?_
    rw [E2 y₁.1 y₁.2, E2 y₂.1 y₂.2]
    exact congrArg (fun χ : B →* Uˣ => χ ⟨α' a₀ x, F3 x⟩) h
  exact le_antisymm hAB.2 hBA.2

end GlobalTheory.DualParts
