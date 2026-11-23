import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem rt_val {O Γ k : Type} [CommRing O] [Group Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k) (w : ℤ × ℤ) (g : Γ) :
    a (Φ.rt w g) = (a (Φ.χ 0 g) * (a (Φ.χ 1 g))⁻¹) ^ w.1 * (a (Φ.χ 0 g) * (a (Φ.χ 2 g))⁻¹) ^ w.2 := by
  have h : ∀ u : Oˣ, a (u : O) = ((Units.map (a : O →* k) u : kˣ) : k) := fun _ => rfl
  have e : Φ.rt w g = (Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ w.1 * (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ w.2 := rfl
  rw [e, h, h (Φ.χ 0 g), h (Φ.χ 1 g), h (Φ.χ 2 g)]
  simp only [map_mul, map_zpow, map_inv, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val]

private theorem rt_lc {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k)
    (h : Φ.Ok a) (w : ℤ × ℤ) : IsLocallyConstant fun g => a (Φ.rt w g) := by
  simp only [rt_val]
  exact (((h.lc 0).mul ((h.lc 1).comp (·⁻¹))).comp (· ^ w.1)).mul (((h.lc 0).mul ((h.lc 2).comp (·⁻¹))).comp (· ^ w.2))

private theorem rt_kill {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k)
    (h : Φ.Ok a) (w : ℤ × ℤ) (g : Γ) (hg : g ∈ Φ.N) : a (Φ.rt w g) = 1 := by
  simp [rt_val, h.kill g hg]

theorem UpperTheory.V.Ws.Gys.cupNorm :
    ∀ {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k), Φ.Ok a → ∀ (w w' : ℤ × ℤ), a (Φ.rt w Φ.g0) ≠ 1 → a (Φ.rt (w + w') Φ.g0) ≠ 1 → ∀ (J : Type) (y : J → Γ → k), (∀ j, Φ.Coc a w' (y j) ∧ y j Φ.g0 = 0) →
      ∀ (x : Γ → k) (m : Φ.ι → k), Φ.Coc a w x → Φ.LocTriv a w x m → (∀ j, ∃ z, Φ.Cup a w w' x (y j) z m) →
        ∃ (x' : Γ → k) (m' : Φ.ι → k), Φ.Coc a w x' ∧ x' Φ.g0 = 0 ∧ Φ.LocTriv a w x' m' ∧ (∀ g, a (Φ.rt w g) = 1 → x' g = x g) ∧
          ∀ j, ∃ z, Φ.Cup a w w' x' (y j) z m' ∧ z Φ.g0 = 0 := by
  intro O Γ k _ _ _ _ Φ a hok w w' h1 h2 J y hy x m hx hm hz
  have n1 : 1 - a (Φ.rt w Φ.g0) ≠ 0 := sub_ne_zero.2 h1.symm
  have n2 : 1 - a (Φ.rt (w + w') Φ.g0) ≠ 0 := sub_ne_zero.2 h2.symm
  have hmul : ∀ (u : ℤ × ℤ) (g h : Γ), a (Φ.rt u (g * h)) = a (Φ.rt u g) * a (Φ.rt u h) := fun u g h => by
    rw [map_mul, Units.val_mul, map_mul]
  have hadd : ∀ g : Γ, a (Φ.rt (w + w') g) = a (Φ.rt w g) * a (Φ.rt w' g) := fun g => by
    rw [Fr.rt_add, Units.val_mul, map_mul]
  obtain ⟨m1, hm1⟩ : ∃ m1 : k, x Φ.g0 = m1 - a (Φ.rt w Φ.g0) * m1 :=
    ⟨x Φ.g0 / (1 - a (Φ.rt w Φ.g0)), by field_simp⟩
  have c := fun t : k => (IsLocallyConstant.const t : IsLocallyConstant fun _ : Γ => t)
  refine ⟨fun g => x g - (m1 - a (Φ.rt w g) * m1), fun v => m v - m1, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, fun j => ?_⟩
  · exact hx.lc.sub ((c m1).sub ((rt_lc Φ a hok w).mul (c m1)))
  · intro g h
    rw [hx.coc, hmul]; ring
  · intro g hg
    rw [hx.kill g hg, rt_kill Φ a hok w g hg]; ring
  · exact sub_eq_zero.2 hm1
  · intro v s hs
    beta_reduce
    rw [hm v s hs]; ring
  · intro g hg
    beta_reduce
    rw [hg]; ring
  · obtain ⟨z, hz⟩ := hz j
    obtain ⟨hyj, hy0⟩ := hy j
    obtain ⟨o1, ho1⟩ : ∃ o1 : k, z Φ.g0 = o1 - a (Φ.rt (w + w') Φ.g0) * o1 :=
      ⟨z Φ.g0 / (1 - a (Φ.rt (w + w') Φ.g0)), by field_simp⟩
    refine ⟨fun g => z g - (o1 - a (Φ.rt (w + w') g) * o1 - y j g * a (Φ.rt w g) * m1), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · exact hz.lc.sub (((c o1).sub ((rt_lc Φ a hok _).mul (c o1))).sub ((hyj.lc.mul (rt_lc Φ a hok w)).mul (c m1)))
    · intro g h
      rw [hz.coc, hyj.coc, hmul, hmul, hadd g, hadd h]; ring
    · intro g hg
      rw [hz.kill g hg, hyj.kill g hg, rt_kill Φ a hok _ g hg]; ring
    · intro v
      obtain ⟨o, ho⟩ := hz.loc v
      refine ⟨o - o1, fun s hs => ?_⟩
      rw [ho s hs]; ring
    · beta_reduce
      rw [ho1, hy0]; ring
