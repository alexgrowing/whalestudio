import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CyclotomicTwistFiniteModuleCocycleStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

theorem GlobalTheory.CompanionTheory.LocDual.cup_flip_cob {G W W' R : Type} [Group G] [TopologicalSpace G] [AddCommGroup W]
    [AddCommGroup W'] [CommRing R] (χ : G → R) (a : G → W →+ W) (a' : G → W' →+ W') (P : W →+ W' →+ R)
    (hP : ∀ g x y, P (a g x) (a' g y) = χ g * P x y) (y : G → W) (x : G → W')
    (hy : IsLocallyConstant y ∧ ∀ g h, y (g * h) = y g + a g (y h))
    (hx : IsLocallyConstant x ∧ ∀ g h, x (g * h) = x g + a' g (x h)) (z z' : G × G → R)
    (hz : (z = (fun p => P (y p.1) (a' p.1 (x p.2))) ∧ z' = (fun p => P (a p.1 (y p.2)) (x p.1))) ∨
      (z' = (fun p => P (y p.1) (a' p.1 (x p.2))) ∧ z = (fun p => P (a p.1 (y p.2)) (x p.1))))
    (h : ∃ f : G → R, IsLocallyConstant f ∧ ∀ g h, χ g * f h - f (g * h) + f g = z (g, h)) :
    ∃ f : G → R, IsLocallyConstant f ∧ ∀ g h, χ g * f h - f (g * h) + f g = z' (g, h) := by
  obtain ⟨f, hf, hfd⟩ := h
  have hlc : IsLocallyConstant fun g => P (y g) (x g) :=
    IsLocallyConstant.comp₂ hy.1 hx.1 fun u v => P u v
  have hid : ∀ g h, χ g * P (y h) (x h) - P (y (g * h)) (x (g * h)) + P (y g) (x g) =
      -P (y g) (a' g (x h)) - P (a g (y h)) (x g) := by
    intro g h
    rw [hy.2, hx.2, ← hP]
    simp only [map_add, AddMonoidHom.add_apply]
    abel
  refine ⟨fun g => -P (y g) (x g) - f g, (hlc.neg).sub hf, fun g h => ?_⟩
  have h1 := hid g h
  have h2 := hfd g h
  rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only at h2 ⊢ <;> linear_combination -h1 - h2

theorem GlobalTheory.CompanionTheory.LocDual.doubleAnn_right : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (n : ℕ) (χ : ↥(GK K) →* (ZMod (l ^ n))ˣ), 0 < n → (∀ g, ∃ u : ℤ_[l], (u : ℚ_[l]) = ((((D.loc l).PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) ∧ PadicInt.toZModPow n u = (χ g : ZMod (l ^ n))) → ∀ (W : Type) [AddCommGroup W] [Finite W] (a : ↥(GK K) → W →+ W), (∀ m, a 1 m = m) → (∀ g h m, a (g * h) m = a g (a h m)) → (∀ m, IsLocallyConstant fun g => a g m) → ∀ (W' : Type) [AddCommGroup W'] [Finite W'] (a' : ↥(GK K) → W' →+ W'), (∀ m, a' 1 m = m) → (∀ g h m, a' (g * h) m = a' g (a' h m)) → (∀ m, IsLocallyConstant fun g => a' g m) → ∀ P : W →+ W' →+ ZMod (l ^ n), (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (a g x) (a' g y) = (χ g : ZMod (l ^ n)) * P x y) → ∀ S : AddSubgroup (↥(GK K) → W'), (∀ m : W', (fun g => a' g m - m) ∈ S) → (∀ s ∈ S, (IsLocallyConstant s ∧ ∀ g h, s (g * h) = s g + a' g (s h))) → ∀ c' : ↥(GK K) → W', (IsLocallyConstant c' ∧ ∀ g h, c' (g * h) = c' g + a' g (c' h)) → (∀ c : ↥(GK K) → W, (IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)) → (∀ s ∈ S, (∃ f : ↥(GK K) → ZMod (l ^ n), IsLocallyConstant f ∧ ∀ g h, (χ g : ZMod (l ^ n)) * f h - f (g * h) + f g = P (c g) (a' g (s h)))) → (∃ f : ↥(GK K) → ZMod (l ^ n), IsLocallyConstant f ∧ ∀ g h, (χ g : ZMod (l ^ n)) * f h - f (g * h) + f g = P (c g) (a' g (c' h)))) → c' ∈ S := by
  intro hT D l _ K n χ hn hχ W _ _ a a1 amul alc W' _ _ a' a1' amul' alc' P hl hr hP S hcob hS c' hc' H
  have hP' : ∀ g x y, P (a g x) (a' g y) = ((χ g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y := hP
  refine GlobalTheory.T.cyclotomic_twist_finite_module_cocycle hT D l K n χ hn hχ W' a' a1' amul' alc' W a a1 amul alc P.flip
    (fun y h => hr y fun x => h x) (fun x h => hl x fun y => h y)
    (fun g x y => hP g y x) S hcob hS c' hc' ?_
  intro c hc hs
  have hAll := H c hc fun s hsS =>
    GlobalTheory.CompanionTheory.LocDual.cup_flip_cob (fun g => ((χ g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) a a' P hP' c s hc (hS s hsS) _ _
      (Or.inr ⟨rfl, rfl⟩) (hs s hsS)
  exact GlobalTheory.CompanionTheory.LocDual.cup_flip_cob (fun g => ((χ g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) a a' P hP' c c' hc hc' _ _
    (Or.inl ⟨rfl, rfl⟩) hAll
