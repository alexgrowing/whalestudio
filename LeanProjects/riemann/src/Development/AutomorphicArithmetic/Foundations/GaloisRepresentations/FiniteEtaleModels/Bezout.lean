import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit

set_option autoImplicit false

namespace UpperTheory.Gal.FiniteEtaleModels.O

section Form

variable {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M)

private lemma skew (alt : ∀ x, B x x = 0) (x y : M) : B x y = - B y x := by
  have h := alt (x + y)
  simp only [map_add, LinearMap.add_apply, alt x, alt y, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

private lemma bezout {e n : ℕ} (hc : e.Coprime n) : ∃ a b : ℤ, a * e + b * n = 1 :=
  Nat.isCoprime_iff_coprime.2 hc

private lemma first {n e : ℕ} (hn : 0 < n) (hc : e.Coprime n) (nd : Function.Injective B)
    (perf : ∀ f : M →ₗ[ℤ] ℤ, ∃ x, B x = e • f) (x : M) (h : ∀ y, (n : ℤ) ∣ B x y) :
    ∃ z, x = n • z := by
  obtain ⟨a, b, hab⟩ := bezout hc
  let f : M →ₗ[ℤ] ℤ :=
    { toFun := fun y => B x y / n
      map_add' := fun y y' => by
        simp only [map_add]
        exact Int.add_ediv_of_dvd_right (h y')
      map_smul' := fun c y => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (h y) }
  have hf : ∀ y, (n : ℤ) * f y = B x y := fun y => Int.mul_ediv_cancel' (h y)
  obtain ⟨w, hw⟩ := perf f
  have key : n • w = e • x := by
    apply nd
    ext y
    simp only [map_nsmul, LinearMap.smul_apply, hw, nsmul_eq_mul, ← hf]
    ring
  have key' : (e : ℤ) • x = (n : ℤ) • w := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, key]
  refine ⟨a • w + b • x, ?_⟩
  calc x = ((a * e + b * n : ℤ)) • x := by rw [hab, one_smul]
    _ = a • ((e : ℤ) • x) + b • ((n : ℤ) • x) := by rw [add_smul, mul_smul, mul_smul]
    _ = n • (a • w + b • x) := by
      rw [key', ← Nat.cast_smul_eq_nsmul ℤ n, smul_add, smul_comm a, smul_comm b]

private lemma second {n e : ℕ} (hc : e.Coprime n) (nd : Function.Injective B)
    (alt : ∀ x, B x x = 0) (perf : ∀ f : M →ₗ[ℤ] ℤ, ∃ x, B x = e • f) (h : M →+ M) :
    ∃ k : M →+ M, ∀ x y, (n : ℤ) ∣ B (h x) y - B x (k y) := by
  obtain ⟨a, b, hab⟩ := bezout hc
  let F : M → M →ₗ[ℤ] ℤ := fun y => (B.flip y) ∘ₗ h.toIntLinearMap
  have hF : ∀ y x, F y x = B (h x) y := fun y x => rfl
  choose w hw using fun y => perf (F y)
  have wadd : ∀ y y', w (y + y') = w y + w y' := by
    intro y y'
    apply nd
    ext x
    simp only [map_add, LinearMap.add_apply, hw, LinearMap.smul_apply, hF, smul_add]
  let k : M →+ M := AddMonoidHom.mk' (fun y => -(a • w y)) (by
    intro y y'
    simp only [wadd, smul_add, neg_add])
  refine ⟨k, fun x y => ?_⟩
  have h1 : B x (k y) = a * (e * B (h x) y) := by
    simp only [k, AddMonoidHom.mk'_apply, map_neg, map_zsmul, smul_eq_mul, skew B alt x (w y), hw,
      LinearMap.smul_apply, hF, nsmul_eq_mul]
    ring
  rw [h1]
  exact ⟨b * B (h x) y, by linear_combination (-(B (h x) y)) * hab⟩

private lemma third {n : ℕ} (hn : 0 < n) [Module.Finite ℤ M] (g : M →+ M)
    (inj : ∀ x z, g x = n • z → ∃ w, x = n • w) (x : M) : ∃ y z, g y = x + n • z := by
  classical
  let N : AddSubgroup M := (nsmulAddMonoidHom n).range
  have memN : ∀ y, y ∈ N ↔ ∃ z, n • z = y := fun y => by
    simp [N, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  have hle : N ≤ N.comap g := by
    intro y hy
    obtain ⟨z, rfl⟩ := (memN y).1 hy
    exact (memN _).2 ⟨g z, (map_nsmul g n z).symm⟩
  let G := QuotientAddGroup.map N N g hle
  haveI : AddGroup.FG M := Module.Finite.iff_addGroup_fg.1 inferInstance
  haveI : Finite (M ⧸ N) := by
    apply AddCommGroup.finite_of_fg_torsion
    intro u
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective u
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨n, hn, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact (memN _).2 ⟨y, rfl⟩
  have ginj : Function.Injective G := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective u
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff] at hu
    obtain ⟨z, hz⟩ := (memN _).1 hu
    obtain ⟨w, hw⟩ := inj y z hz.symm
    rw [QuotientAddGroup.eq_zero_iff]
    exact (memN _).2 ⟨w, hw.symm⟩
  obtain ⟨u, hu⟩ := Finite.injective_iff_surjective.1 ginj (QuotientAddGroup.mk x)
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective u
  rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq] at hu
  obtain ⟨z, hz⟩ := (memN _).1 hu
  exact ⟨y, -z, by rw [smul_neg, hz]; abel⟩

end Form

theorem adj : UpperTheory.Gal.FiniteEtaleModels.O.Adj := by
  intro q _ D e
  haveI := D.finLa
  obtain ⟨e', he', perf⟩ := D.perfP
  have hc : e'.Coprime (q ^ e) := Nat.Coprime.pow_right e he'
  have hn : 0 < q ^ e := pow_pos (Fact.out : Nat.Prime q).pos e
  have fst : ∀ x : D.La, (∀ y, ((q ^ e : ℕ) : ℤ) ∣ D.EF x y) → Cg (q ^ e) x 0 := by
    intro x hx
    obtain ⟨z, hz⟩ := first D.EF hn hc D.nondeg perf x hx
    exact ⟨z, by rw [zero_add]; exact hz⟩
  refine ⟨fst, ?_, ?_⟩
  · intro h
    obtain ⟨k, hk⟩ := second D.EF hc D.nondeg D.alt perf h.toAddMonoidHom
    refine ⟨k, hk, ?_⟩
    intro c y
    obtain ⟨z, hz⟩ := fst (k (c • y) - c • k y) (by
      intro x
      obtain ⟨b', hb'⟩ : ∃ b', MulOpposite.unop (D.star b') = c := ⟨_, D.star_star c⟩
      have e1 := hk x (c • y)
      have e2 := hk (b' • x) y
      have a1 : D.EF (h.toAddMonoidHom (b' • x)) y = D.EF (h.toAddMonoidHom x) (c • y) := by
        rw [LinearMap.toAddMonoidHom_coe, map_smul, D.adj, hb']
      have a2 : D.EF (b' • x) (k y) = D.EF x (c • k y) := by rw [D.adj, hb']
      rw [a1, a2] at e2
      rw [skew D.EF D.alt, map_sub, dvd_neg]
      have h5 := dvd_sub e2 e1
      rwa [sub_sub_sub_cancel_left] at h5)
    exact ⟨z, by rw [zero_add, sub_eq_iff_eq_add'] at hz; exact hz⟩
  · intro g hg
    have ginj : ∀ x z, g x = (q ^ e) • z → ∃ w, x = (q ^ e) • w := by
      intro x z hz
      apply first D.EF hn hc D.nondeg perf x
      intro y
      have h3 := hg x y
      rw [hz, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h3
      have h2 : ((q ^ e : ℕ) : ℤ) ∣ ((q ^ e : ℕ) : ℤ) * D.EF z (g y) := dvd_mul_right _ _
      have h4 := dvd_sub h2 h3
      rwa [sub_sub_cancel] at h4
    refine ⟨fun x ⟨z, hz⟩ => ?_, fun x => ?_⟩
    · obtain ⟨w, hw⟩ := ginj x z (by rw [hz, zero_add])
      exact ⟨w, by rw [zero_add]; exact hw⟩
    · obtain ⟨y, z, hyz⟩ := third hn g ginj x
      exact ⟨y, z, hyz⟩

end UpperTheory.Gal.FiniteEtaleModels.O
