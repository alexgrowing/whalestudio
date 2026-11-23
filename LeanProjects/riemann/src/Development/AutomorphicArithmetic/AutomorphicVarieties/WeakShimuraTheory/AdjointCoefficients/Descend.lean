import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem gen {Γ Γb M R κ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group Γb]
    [TopologicalSpace Γb] [Monoid M] [CommRing R] (I : Ideal R) [IsHausdorff I R] (N : Set Γ) (π : Γ →* Γb)
    (hq : Topology.IsQuotientMap π) (hk : π.ker = (Subgroup.normalClosure N).topologicalClosure)
    (e : κ → M → R) (he : ∀ x y, (∀ k, e k x = e k y) → x = y) (r : Γ →* M) (hN : ∀ g ∈ N, r g = 1)
    (hc : ∀ k, AdicCont I fun g => e k (r g)) :
    ∃ rb : Γb →* M, rb.comp π = r ∧ ∀ k, AdicCont I fun g => e k (rb g) := by
  have hcl : IsClosed (r.ker : Set Γ) := by
    have : (r.ker : Set Γ) = ⋂ k, ⋂ n : ℕ,
        {g | Ideal.Quotient.mk (I ^ n) (e k (r g)) = Ideal.Quotient.mk (I ^ n) (e k 1)} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
      refine ⟨fun h k n => by rw [h], fun h => he _ _ fun k => ?_⟩
      rw [← sub_eq_zero]
      refine IsHausdorff.haus (I := I) inferInstance _ fun n => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
      exact h k n
    rw [this]
    exact isClosed_iInter fun k => isClosed_iInter fun n => (hc k n).isClosed_fiber _
  have hle : π.ker ≤ r.ker := by
    rw [hk]
    exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun g hg => hN g hg) hcl
  have hle' : π.ker ≤ r.toHomUnits.ker := fun g hg => Units.ext (hle hg)
  have hs := hq.surjective
  let φ := π.liftOfRightInverse (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨r.toHomUnits, hle'⟩
  have hφ : ∀ g, ((Units.coeHom M).comp φ) (π g) = r g := fun g =>
    congrArg Units.val (π.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hs) ⟨r.toHomUnits, hle'⟩ g)
  refine ⟨(Units.coeHom M).comp φ, MonoidHom.ext hφ, fun k n s => ?_⟩
  rw [← hq.isOpen_preimage]
  have := hc k n s
  simp only [← hφ] at this
  exact this

theorem UpperTheory.V.Ws.X1.descend :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (Φ : Fr O Γ) , ∀ {Γb : Type} [Group Γb] [TopologicalSpace Γb] [IsTopologicalGroup Γb] [T2Space Γb] (π : Γ →* Γb), Φ.Quo π → ∀ {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R], (∀ (r : Γ →* M4 R), (∀ g ∈ Φ.N, r g = 1) → (∀ i j, AdicCont I fun g => r g i j) → ∃ rb : Γb →* M4 R, rb.comp π = r ∧ ∀ i j, AdicCont I fun g => rb g i j) ∧ ∀ (ν : Γ →* Rˣ), (∀ g ∈ Φ.N, ν g = 1) → AdicCont I (fun g => (ν g : R)) → ∃ νb : Γb →* Rˣ, νb.comp π = ν ∧ AdicCont I fun g => (νb g : R) := by
  intro O Γ _ _ _ _ _ Φ Γb _ _ _ _ π hπ R _ I _
  have hq : Topology.IsQuotientMap π := hπ.cont.isClosedMap.isQuotientMap hπ.cont hπ.onto
  refine ⟨fun r hN hc => ?_, fun ν hN hc => ?_⟩
  · obtain ⟨rb, h1, h2⟩ := gen I Φ.N π hq hπ.ker (fun (k : Fin 4 × Fin 4) (x : M4 R) => x k.1 k.2)
      (fun x y h => Matrix.ext fun i j => h (i, j)) r hN fun k => hc k.1 k.2
    exact ⟨rb, h1, fun i j => h2 (i, j)⟩
  · obtain ⟨rb, h1, h2⟩ := gen I Φ.N π hq hπ.ker (fun (_ : Unit) (x : Rˣ) => (x : R))
      (fun x y h => Units.ext (h ())) ν hN fun _ => hc
    exact ⟨rb, h1, h2 ()⟩
