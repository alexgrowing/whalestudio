import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.PerfCard

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.dualZ :
    ∀ (N : ℕ) [NeZero N] (V : Type) [AddCommGroup V] [Module (ZMod N) V] [Finite V], Nat.card (Module.Dual (ZMod N) V) = Nat.card V ∧ (∀ v : V, (∀ f : Module.Dual (ZMod N) V, f v = 0) → v = 0) ∧ ∀ (V' : Type) [AddCommGroup V'] [Module (ZMod N) V'] [Finite V'] (b : V →+ V' →+ ZMod N), (∀ x, (∀ y, b x y = 0) → x = 0) → (∀ y, (∀ x, b x y = 0) → y = 0) → Function.Bijective fun y : V' => ((b.flip y).toZModLinearMap N : Module.Dual (ZMod N) V) := by
  intro N _ V _ _ _
  have sep : ∀ {W : Type} [AddCommGroup W] [Module (ZMod N) W] (w : W),
      (∀ f : Module.Dual (ZMod N) W, f w = 0) → w = 0 := by
    intro W _ _ w hw
    by_contra hne
    obtain ⟨f, -, hf⟩ := KStar.Selmer.exists_form_ne_zero (⊥ : Submodule (ZMod N) W)
      (z := w) (by simpa using hne)
    exact hf (hw f)
  have fin : ∀ {W : Type} [AddCommGroup W] [Module (ZMod N) W] [Finite W],
      Finite (Module.Dual (ZMod N) W) := by
    intro W _ _ _
    apply Nat.finite_of_card_ne_zero
    rw [KStar.Selmer.card_dual]
    exact Nat.card_pos.ne'
  refine ⟨KStar.Selmer.card_dual, fun v hv => sep v hv, ?_⟩
  intro V' _ _ _ b hl hr
  haveI := fin (W := V)
  haveI := fin (W := V')
  have inj : Function.Injective fun y : V' =>
      ((b.flip y).toZModLinearMap N : Module.Dual (ZMod N) V) := by
    intro y y' h
    have h' : ∀ x, b x (y - y') = 0 := by
      intro x
      have := LinearMap.congr_fun h x
      simp only [AddMonoidHom.coe_toZModLinearMap, AddMonoidHom.flip_apply] at this
      rw [map_sub, this, sub_self]
    exact sub_eq_zero.mp (hr _ h')
  have inj' : Function.Injective fun x : V =>
      ((b x).toZModLinearMap N : Module.Dual (ZMod N) V') := by
    intro x x' h
    have h' : ∀ y, b (x - x') y = 0 := by
      intro y
      have := LinearMap.congr_fun h y
      simp only [AddMonoidHom.coe_toZModLinearMap] at this
      rw [map_sub, AddMonoidHom.sub_apply, this, sub_self]
    exact sub_eq_zero.mp (hl _ h')
  have c2 := Nat.card_le_card_of_injective _ inj'
  rw [KStar.Selmer.card_dual] at c2
  refine inj.bijective_of_nat_card_le ?_
  rw [KStar.Selmer.card_dual]
  exact c2
