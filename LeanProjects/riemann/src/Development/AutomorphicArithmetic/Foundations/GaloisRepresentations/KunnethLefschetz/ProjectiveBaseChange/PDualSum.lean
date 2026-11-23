import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.AdicTopOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

private theorem dualSum_abs {F : Type*} [Field F] {r : ℕ} {A B C : Type*}
    [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B] [AddCommGroup C] [Module F C]
    {A' B' C' : Fin r → Type*} [∀ s, AddCommGroup (A' s)] [∀ s, Module F (A' s)]
    [∀ s, AddCommGroup (B' s)] [∀ s, Module F (B' s)] [∀ s, AddCommGroup (C' s)] [∀ s, Module F (C' s)]
    (pa : ∀ s, A →ₗ[F] A' s) (pe : ∀ s, B →ₗ[F] B' s) (pc : ∀ s, C →ₗ[F] C' s)
    (ha : Function.Bijective fun (x : A) s => pa s x) (hb : Function.Bijective fun (x : B) s => pe s x)
    (hc : Function.Bijective fun (x : C) s => pc s x)
    (cup : A →ₗ[F] B →ₗ[F] C) (cup' : ∀ s, A' s →ₗ[F] B' s →ₗ[F] C' s)
    (nat : ∀ s x y, pc s (cup x y) = cup' s (pa s x) (pe s y))
    (tr : ∀ s, C' s ≃ₗ[F] F)
    (hd : ∀ s, Function.Bijective ((cup' s).compr₂ (tr s).toLinearMap).flip) :
    ∃ g : Fin r → C, (∀ s, pc s (g s) ≠ 0) ∧ (∀ s (v : C' s), ∃ z : F, v = z • pc s (g s)) ∧
      (∀ s t, s ≠ t → pc t (g s) = 0) ∧ Submodule.span F (Set.range g) = ⊤ ∧
      Submodule.span F {f : Module.Dual F A | ∃ (s : Fin r) (y : B), ∀ x, cup x y = f x • g s} = ⊤ := by
  classical
  let eA := LinearEquiv.ofBijective (LinearMap.pi pa) ha
  let eB := LinearEquiv.ofBijective (LinearMap.pi pe) hb
  let eC := LinearEquiv.ofBijective (LinearMap.pi pc) hc
  have kB : ∀ (x : ∀ s, B' s) t, pe t (eB.symm x) = x t := fun x t =>
    congrFun (eB.apply_symm_apply x) t
  have kC : ∀ (x : ∀ s, C' s) t, pc t (eC.symm x) = x t := fun x t =>
    congrFun (eC.apply_symm_apply x) t
  let g : Fin r → C := fun s => eC.symm (Pi.single (M := C') s ((tr s).symm 1))
  have hg : ∀ s t, pc t (g s) = Pi.single (M := C') s ((tr s).symm 1) t := fun s t => kC _ t
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · intro s h0
    rw [hg, Pi.single_eq_same] at h0
    have := congrArg (tr s) h0
    simp at this
  · intro s v
    refine ⟨tr s v, ?_⟩
    rw [hg, Pi.single_eq_same]
    apply (tr s).injective
    simp
  · intro s t hst
    rw [hg, Pi.single_eq_of_ne (Ne.symm hst)]
  · rw [eq_top_iff]
    intro c _
    have hc' : c = ∑ s, tr s (pc s c) • g s := by
      apply hc.1
      funext t
      simp only [map_sum, map_smul, hg]
      rw [Finset.sum_eq_single t]
      · rw [Pi.single_eq_same]
        apply (tr t).injective
        simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
      · intro ht
        exact absurd (Finset.mem_univ t) ht
    rw [hc']
    exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · rw [eq_top_iff]
    intro f _
    have hy : ∀ s, ∃ y' : B' s, ∀ a', tr s (cup' s a' y') = f (eA.symm (Pi.single s a')) := by
      intro s
      obtain ⟨y', hy'⟩ := (hd s).2 (f ∘ₗ eA.symm.toLinearMap ∘ₗ LinearMap.single F A' s)
      refine ⟨y', fun a' => ?_⟩
      have := LinearMap.congr_fun hy' a'
      simpa using this
    choose y' hy' using hy
    let φ : Fin r → Module.Dual F A := fun s =>
      f ∘ₗ eA.symm.toLinearMap ∘ₗ LinearMap.single F A' s ∘ₗ pa s
    have memS : ∀ s, φ s ∈ {f : Module.Dual F A | ∃ (s : Fin r) (y : B), ∀ x, cup x y = f x • g s} := by
      intro s
      refine ⟨s, eB.symm (Pi.single s (y' s)), fun x => ?_⟩
      apply hc.1
      funext t
      simp only [map_smul, nat, kB, hg]
      by_cases hts : t = s
      · subst hts
        simp only [Pi.single_eq_same]
        apply (tr t).injective
        rw [hy']
        simp [φ]
      · rw [Pi.single_eq_of_ne hts, Pi.single_eq_of_ne hts]
        simp
    have hf : f = ∑ s, φ s := by
      ext x
      have e1 : (∑ s, Pi.single s (pa s x) : ∀ s, A' s) = eA x := Finset.univ_sum_single _
      rw [LinearMap.sum_apply]
      calc f x = f (eA.symm (eA x)) := by rw [eA.symm_apply_apply]
        _ = f (eA.symm (∑ s, Pi.single s (pa s x))) := by rw [e1]
        _ = ∑ s, φ s x := by simp only [map_sum]; rfl
    rw [hf]
    exact Submodule.sum_mem _ fun s _ => Submodule.subset_span (memS s)

theorem dualSum_holds : DualSum := by
  unfold DualSum
  intro l _ hR X r Y j d hb hD a b w h hw
  subst hw
  have hD' : ∀ s, ∃ tr : V l (Y s) (2 * (d : ℤ)) ≃ₗ[ℚ_[l]] ℚ_[l], ∀ (n m : ℤ) (h : n + m = 2 * d),
      Function.Bijective ((cupV l (Y s) h).compr₂ tr.toLinearMap).flip := fun s => (hD s).2.2
  choose tr htr using hD'
  obtain ⟨g, h1, h2, h3, h4, h5⟩ := dualSum_abs (fun s => pb l (j s) a) (fun s => pb l (j s) b)
    (fun s => pb l (j s) (2 * (d : ℤ))) (hb a) (hb b) (hb _) (cupV l X h) (fun s => cupV l (Y s) h)
    (fun s x y => hR.nat (j s) a b _ h x y) tr (fun s => htr s a b h)
  exact ⟨g, ⟨h1, h2, h3⟩, h4, h5⟩

end UpperTheory.Gal.KunnethLefschetz
