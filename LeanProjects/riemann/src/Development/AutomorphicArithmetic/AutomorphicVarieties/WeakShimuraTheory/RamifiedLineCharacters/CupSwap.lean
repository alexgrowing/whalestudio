import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.cupSwap :
    ∀ {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R) (w w' : ℤ × ℤ) (x y z : Γ → R) (m n : Φ.ι → R), Φ.Coc a w x → Φ.LocTriv a w x m → Φ.Coc a w' y → Φ.LocTriv a w' y n →
      Φ.Cup a w w' x y z m → Φ.Cup a w' w y x (x * y - z) n := by
  intro O Γ R _ _ _ _ Φ a w w' x y z m n hx hm hy hn hz
  have e : ∀ g, a (Φ.rt (w + w') g) = a (Φ.rt w g) * a (Φ.rt w' g) := fun g => by
    rw [Fr.rt_add, Units.val_mul, map_mul]
  refine ⟨?_, fun g h => ?_, fun g hg => ?_, fun v => ?_⟩
  · exact (hx.lc.comp₂ hy.lc (· * ·)).comp₂ hz.lc (· - ·)
  · simp only [Pi.sub_apply, Pi.mul_apply]
    rw [add_comm w' w, hx.coc, hy.coc, hz.coc, e]
    ring
  · simp only [Pi.sub_apply, Pi.mul_apply]
    rw [hx.kill g hg, hz.kill g hg, zero_mul, sub_zero]
  · obtain ⟨o, ho⟩ := hz.loc v
    refine ⟨m v * n v - o, fun s hs => ?_⟩
    simp only [Pi.sub_apply, Pi.mul_apply]
    rw [add_comm w' w, ho s hs, e, hm v s hs, hn v s hs]
    ring
