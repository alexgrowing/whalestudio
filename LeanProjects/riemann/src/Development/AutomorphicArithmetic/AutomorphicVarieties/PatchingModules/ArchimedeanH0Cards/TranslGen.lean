import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.PushforwardPreservesSelmerCocycles

open ReciprocityTheory.Gal

namespace UpperTheory.V.Pa.B2

variable {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

theorem continuous_differential_one (M : FRep A Γ) {x : Γ → M.X} (hx : Continuous x) : Continuous (d1 M.ρ x) :=
  ((M.cont.comp (continuous_fst.prodMk (hx.comp continuous_snd))).sub (hx.comp continuous_mul)).add
    (hx.comp continuous_fst)

theorem urLift {l : ℕ} {J : Subgroup Γ} (H : UrAx l J) (M : FRep A Γ) (hl : ∀ m : M.X, l • m = 0)
    (hJ : ∀ g ∈ J, ∀ m, M.ρ g m = m) (S : Submodule A M.X) (hS : ∀ g, S ≤ S.comap (M.ρ g)) (x : Γ → M.X)
    (hx : Continuous x) (hd : ∀ s, d1 M.ρ x s ∈ S) (h0 : ∀ g ∈ J, x g ∈ S) :
    ∃ b ∈ Z1 M.ρ, (∀ g ∈ J, b g = 0) ∧ ∀ g, x g - b g ∈ S := by
  letI : TopologicalSpace (M.X ⧸ S) := ⊥
  haveI : DiscreteTopology (M.X ⧸ S) := ⟨rfl⟩
  haveI : Finite (M.X ⧸ S) := Finite.of_surjective _ S.mkQ_surjective
  let M' : FRep A Γ :=
    { X := M.X ⧸ S
      ρ := Representation.quotient M.ρ S hS
      cont := by
        refine continuous_prod_of_discrete_right.2 fun q => ?_
        obtain ⟨m, rfl⟩ := S.mkQ_surjective q
        exact (continuous_of_discreteTopology (f := S.mkQ)).comp
          (M.cont.comp (continuous_id.prodMk continuous_const)) }
  obtain ⟨b, hb, h1, h2⟩ := (H A M hl hJ).2 M' S.mkQ (fun _ _ => rfl) S.mkQ_surjective (fun g => S.mkQ (x g))
    ⟨(continuous_of_discreteTopology (f := S.mkQ)).comp hx, fun g h => by
      show S.mkQ (x (g * h)) = S.mkQ (x g) + S.mkQ (M.ρ g (x h))
      rw [← map_add]
      refine (Submodule.Quotient.eq S).2 ?_
      convert S.neg_mem (hd (g, h)) using 1
      rw [d1_apply]; abel⟩
    (fun g hg => (Submodule.Quotient.mk_eq_zero S).2 (h0 g hg))
  exact ⟨b, hb, h1, fun g => (Submodule.Quotient.eq S).1 (h2 g).symm⟩

theorem translGen {P : Pl Γ} (D : Dat A P) (M : FRep A Γ) (ι : D.M.X →ₗ[A] M.X) (hi : Function.Injective ι)
    (he : ∀ g m, ι (D.M.ρ g m) = M.ρ g (ι m)) (N : P.ι → Submodule A M.X)
    (hN : ∀ w g, ∀ m ∈ N w, M.ρ (P.φ w g) m ∈ N w) (hk : ∀ w m, D.π w m = 0 ↔ ι m ∈ N w) (c0 : Γ)
    (hc : c0 * c0 = 1) (h2 : IsUnit (2 : A)) {e : ℕ} (x : Fin e → Γ → M.X) (hx : ∀ i, Continuous (x i))
    (hd : ∀ i s, d1 M.ρ (x i) s ∈ LinearMap.range ι) (hxc : ∀ i, x i c0 ∈ LinearMap.range ι)
    (b : Fin e → ∀ w, P.G w → M.X) (hb : ∀ i w, Continuous (b i w))
    (hb' : ∀ i w g h, b i w (g * h) = b i w g + M.ρ (P.φ w g) (b i w h))
    (hxb : ∀ i w g, ∃ m, x i (P.φ w g) - b i w g - ι m ∈ N w) :
    ∃ ξ : Fin e → D.selmerSecondCocycles, ∀ c : Fin e → A, ((∑ i, c i • ξ i : D.selmerSecondCocycles) : D.C2) ∈ D.selmerSecondCoboundaries →
      ∃ Ψ ∈ Z1 M.ρ, Ψ c0 = 0 ∧ (∀ γ, Ψ γ - ∑ i, c i • x i γ ∈ LinearMap.range ι) ∧
        ∀ w, ∃ m, ∀ g ∈ P.J w, Ψ (P.φ w g) - ∑ i, c i • b i w g - (M.ρ (P.φ w g) (ι m) - ι m) ∈ N w := by
  classical
  obtain ⟨r, hr⟩ := hi.hasLeftInverse
  have hr' : ∀ i s, ι (r (d1 M.ρ (x i) s)) = d1 M.ρ (x i) s := fun i s => by
    obtain ⟨m, hm⟩ := hd i s
    rw [← hm, hr]
  let σ : P.ι → M.X → D.M.X := fun w s => Classical.epsilon fun m => s - ι m ∈ N w
  let τ : Fin e → ∀ w, P.G w → D.M.X := fun i w g => σ w (x i (P.φ w g) - b i w g)
  have hτ : ∀ i w g, x i (P.φ w g) - b i w g - ι (τ i w g) ∈ N w := fun i w g =>
    Classical.epsilon_spec (hxb i w g)
  have mem : ∀ i, ((fun s => r (d1 M.ρ (x i) s), fun w g => D.π w (τ i w g)) : D.C2) ∈ D.selmerSecondCocycles := by
    intro i
    refine ⟨⟨(continuous_of_discreteTopology (f := r)).comp (continuous_differential_one M (hx i)), fun g h k => hi ?_⟩,
      fun w => ⟨?_, fun g h => ?_⟩⟩
    · simp only [map_add, map_sub, map_zero, he, hr']
      simp only [d1_apply, map_add, map_sub, map_mul, Module.End.mul_apply, mul_assoc]
      abel
    · exact (continuous_of_discreteTopology (f := fun s => D.π w (σ w s))).comp
        (((hx i).comp (P.cont w)).sub (hb i w))
    · simp only [d1_apply (D.Q w).ρ, ← D.equiv]
      rw [← map_sub, ← map_add, ← sub_eq_zero, ← map_sub, hk]
      simp only [map_add, map_sub, he, hr']
      convert add_mem (sub_mem (hN w g _ (hτ i w h)) (hτ i w (g * h))) (hτ i w g) using 1
      simp only [d1_apply, map_add, map_sub, map_mul, hb']
      abel
  refine ⟨fun i => ⟨_, mem i⟩, fun c hB => ?_⟩
  obtain ⟨x0, c1, e1, e2⟩ := hB
  have e1' : ∀ s, ∑ i, c i • d1 M.ρ (x i) s = ι (d1 D.M.ρ x0 s) := fun s => by
    rw [← e1]
    simp [Prod.fst_sum, Finset.sum_apply, hr']
  have hΨ : (fun γ => ∑ i, c i • x i γ - ι (x0 γ)) ∈ Z1 M.ρ := by
    refine ⟨(continuous_finset_sum _ fun i _ => (hx i).const_smul _).sub
      ((continuous_of_discreteTopology (f := ι)).comp c1), fun g h => ?_⟩
    have := e1' (g, h)
    simp only [d1_apply, map_add, map_sub, he, smul_add, smul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib] at this
    simp only [map_sub, map_sum, map_smul]
    rw [← sub_eq_zero] at this ⊢
    rw [← neg_eq_zero, ← this]
    abel
  obtain ⟨m0, hm0⟩ : ∑ i, c i • x i c0 - ι (x0 c0) ∈ LinearMap.range ι :=
    sub_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hxc i)) ⟨_, rfl⟩
  have hneg : M.ρ c0 (ι m0) = -ι m0 := by
    have a1 := hΨ.2 1 1
    have a2 := hΨ.2 c0 c0
    simp only [mul_one, map_one, Module.End.one_apply, left_eq_add] at a1
    simp only [hc, a1, ← hm0] at a2
    exact eq_neg_of_add_eq_zero_right a2.symm
  obtain ⟨t, ht⟩ := h2.exists_left_inv
  refine ⟨(fun γ => ∑ i, c i • x i γ - ι (x0 γ)) + d0 M.ρ (ι (t • m0)), add_mem hΨ ⟨?_, fun g h => ?_⟩, ?_,
    fun γ => ?_, fun w => ?_⟩
  · exact (M.cont.comp (continuous_id.prodMk continuous_const)).sub continuous_const
  · simp only [amitsur_d0_apply, map_mul, map_sub, Module.End.mul_apply]; abel
  · simp only [Pi.add_apply, amitsur_d0_apply, ← hm0]
    rw [map_smul, map_smul, hneg, ← smul_sub, ← neg_add', ← two_smul A, smul_neg, smul_smul, ht, one_smul, add_neg_cancel]
  · refine ⟨D.M.ρ γ (t • m0) - t • m0 - x0 γ, ?_⟩
    simp only [Pi.add_apply, amitsur_d0_apply, map_sub, he]
    abel
  · obtain ⟨-, Y, hY⟩ := e2 w
    obtain ⟨m, rfl⟩ := D.surj w Y
    refine ⟨m + t • m0, fun g hg => ?_⟩
    have a1 : D.π w (∑ i, c i • τ i w g - x0 (P.φ w g) - (D.M.ρ (P.φ w g) m - m)) = 0 := by
      have := hY g hg
      simp only [map_sub, D.equiv, ← this]
      simp [Prod.snd_sum, Finset.sum_apply]
    rw [hk] at a1
    convert add_mem a1 (Submodule.sum_mem _ fun i (_ : i ∈ Finset.univ) => (N w).smul_mem (c i) (hτ i w g)) using 1
    simp only [Pi.add_apply, amitsur_d0_apply, map_sub, map_add, map_sum, he, smul_sub, Finset.sum_sub_distrib, map_smul ι (c _)]
    abel

end UpperTheory.V.Pa.B2
