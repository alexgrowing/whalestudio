import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lc_of_cont {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {f : Γ → R} (h : UpperTheory.V.Alg.AdicCont ⊥ f) :
    IsLocallyConstant f := by
  refine IsLocallyConstant.desc _ _ (h 1) ?_
  intro x y hxy
  rw [Ideal.Quotient.eq, pow_one, Ideal.mem_bot, sub_eq_zero] at hxy
  exact hxy

theorem UpperTheory.V.Ws.Gys.dataPs :
    ∀ {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R) (p : PD Φ.ι Γ R), Φ.IsRes a p → Supp nP p.r →
      ∃ y : Γ → R, Φ.Coc a (-wPs) y ∧ y Φ.g0 = 0 ∧ Φ.LocTriv a (-wPs) y (fun v => p.n v 2 0) ∧ ∀ g, p.r g 2 0 = y g * a (Φ.χ 0 g) := by
  intro O Γ R _ _ _ _ Φ a p hR hS
  have hc : ∀ i j, IsLocallyConstant fun g => p.r g i j := fun i j => lc_of_cont (hR.cont i j)
  have hd := hR.res.diag
  have hinv : ∀ g, Ring.inverse (p.r g 0 0) = a ↑((Φ.χ 0 g)⁻¹) := by
    intro g
    rw [hd g 0]
    have hu : a ↑(Φ.χ 0 g) = ↑(Units.map a.toMonoidHom (Φ.χ 0 g)) := rfl
    rw [hu, Ring.inverse_unit]
    rfl
  have hone : ∀ g, a ↑(Φ.χ 0 g) * a ↑((Φ.χ 0 g)⁻¹) = 1 := by
    intro g
    rw [← map_mul, Units.mul_inv, map_one]
  have he : ∀ g, Φ.rt (-wPs) g = Φ.χ 2 g * (Φ.χ 0 g)⁻¹ := by
    intro g
    simp [Fr.rt, wPs]
  refine ⟨fun g => p.r g 2 0 * Ring.inverse (p.r g 0 0), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (hc 2 0).mul ((hc 0 0).comp Ring.inverse)
  · intro g h
    have z1 : p.r g 2 1 = 0 := hS g 2 1 (by decide) (by decide)
    have z3 : p.r g 2 3 = 0 := hS g 2 3 (by decide) (by decide)
    show p.r (g * h) 2 0 * Ring.inverse (p.r (g * h) 0 0) =
      p.r g 2 0 * Ring.inverse (p.r g 0 0) + a ↑(Φ.rt (-wPs) g) * (p.r h 2 0 * Ring.inverse (p.r h 0 0))
    rw [hinv (g * h), hinv g, hinv h, he g]
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_four, z1, z3, zero_mul, add_zero, hd, mul_inv,
      Units.val_mul]
    linear_combination (p.r g 2 0 * a ↑((Φ.χ 0 g)⁻¹)) * hone h
  · intro g hg
    show p.r g 2 0 * Ring.inverse (p.r g 0 0) = 0
    rw [hR.pair.kill g hg, Matrix.one_apply_ne (by decide), zero_mul]
  · show p.r Φ.g0 2 0 * Ring.inverse (p.r Φ.g0 0 0) = 0
    rw [hR.pair.nrm (by decide : (2 : Fin 4) ≠ 0), zero_mul]
  · intro v s hs
    have hn := hR.pair.low v
    have hna0 : adj (p.n v) * p.n v = 1 := by
      have h1 := hn.1
      simpa [IsGSp] using h1
    have hna : p.n v * adj (p.n v) = 1 := mul_eq_one_comm.mp hna0
    have hX := hR.pair.flag v s hs
    have hch : (adj (p.n v) * p.r s * p.n v) 0 0 = a ↑(Φ.χ 0 s) := hR.res.char v s hs 0
    have key : p.r s * p.n v = p.n v * (adj (p.n v) * p.r s * p.n v) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hna, Matrix.one_mul]
    have k20 := congrFun (congrFun key 2) 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at k20
    rw [hS s 2 1 (by decide) (by decide), hS s 2 3 (by decide) (by decide), hd s 2, hn.2.1 0,
      hX 1 0 (by decide), hX 2 0 (by decide), hX 3 0 (by decide), hch] at k20
    show p.r s 2 0 * Ring.inverse (p.r s 0 0) = p.n v 2 0 - a ↑(Φ.rt (-wPs) s) * p.n v 2 0
    rw [hinv, he s, Units.val_mul, map_mul]
    linear_combination (a ↑((Φ.χ 0 s)⁻¹)) * k20 + (p.n v 2 0) * hone s
  · intro g
    show p.r g 2 0 = p.r g 2 0 * Ring.inverse (p.r g 0 0) * a ↑(Φ.χ 0 g)
    rw [hinv]
    linear_combination (-(p.r g 2 0)) * hone g
