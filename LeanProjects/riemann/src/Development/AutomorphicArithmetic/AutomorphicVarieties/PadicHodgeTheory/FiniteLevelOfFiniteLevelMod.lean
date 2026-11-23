import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
import ReciprocityTheory.GroupCohomology.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NonemptyCohomologyRestrictScalarsLinearEquiv
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.CardCokernelTransposeEqCardKernel
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.ZModInj
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Killed
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem killed (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] [Finite M] :
    ∃ r : ℕ, 0 < r ∧ ∀ x : M, (l : ℤ_[l]) ^ r • x = 0 :=
  _root_.UpperTheory.Reformulated.B.Qe12.killed l M

private theorem H0dual_eq {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V] (χ : G →* Aˣ)
    (ρ : Representation A G V) : H0dual χ ρ = (coSub χ ρ).dualAnnihilator := by
  ext f
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro hf
    have : coSub χ ρ ≤ LinearMap.ker f := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, x, rfl⟩
      have := hf g x
      simp [this]
    exact fun w hw => this hw
  · intro hf g x
    have := hf _ (Submodule.subset_span ⟨g, x, rfl⟩)
    rw [map_sub, map_smul, sub_eq_zero] at this
    exact this

private theorem card_co {G Q A V : Type} [Group G] [CommRing Q] [CommRing A] [Algebra Q A] [AddCommGroup V]
    [Module A V] [Module Q V] [IsScalarTower Q A V] (hs : Function.Surjective (algebraMap Q A)) (χ : G →* Qˣ)
    (χ' : G →* Aˣ) (h : ∀ g, ((χ' g : Aˣ) : A) = algebraMap Q A (χ g : Qˣ))
    (ρ : Representation A G V) : Nat.card (V ⧸ coSub χ' ρ) = Nat.card (V ⧸ coSub χ (resCoef Q ρ)) := by
  have e : coSub χ (resCoef Q ρ) = (coSub χ' ρ).restrictScalars Q := by
    unfold coSub
    rw [Submodule.restrictScalars_span Q A hs]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, h, algebraMap_smul]
    rfl
  rw [e]
  exact Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv Q (coSub χ' ρ)).toEquiv.symm

private def modRep (n : ℕ) {G Q V : Type} [Group G] [CommRing Q] [AddCommGroup V] [Module Q V] [Module (ZMod n) V]
    (ρ : Representation Q G V) : Representation (ZMod n) G V where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap n
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem UpperTheory.finite_level_of_finite_level_mod :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (χ : G →* ℤ_[l]ˣ) (d : ℕ), FinLevelMod l G χ d → FinLevel l G χ d := by
  intro l _ G _ _ χ d h M _ _ _ _ _ ρ hρ
  obtain ⟨r, hr, hk⟩ := killed l M
  have hk' : ∀ x : M, (l ^ r) • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow]; exact hk x
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ r)) M) := ⟨AddCommGroup.zmodModule hk'⟩
  letI : Algebra ℤ_[l] (ZMod (l ^ r)) := (PadicInt.toZModPow r).toAlgebra
  have hs : Function.Surjective (algebraMap ℤ_[l] (ZMod (l ^ r))) := ZMod.ringHom_surjective _
  haveI : IsScalarTower ℤ_[l] (ZMod (l ^ r)) M := by
    refine IsScalarTower.of_algebraMap_smul fun a x => ?_
    obtain ⟨k, hk2⟩ := ZMod.natCast_zmod_surjective (PadicInt.toZModPow r a)
    have h0 : a - k ∈ RingHom.ker (PadicInt.toZModPow (p := l) r) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, hk2, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at h0
    obtain ⟨b, hb⟩ := h0
    change PadicInt.toZModPow r a • x = a • x
    rw [← hk2, Nat.cast_smul_eq_nsmul, eq_add_of_sub_eq hb.symm, add_smul, mul_smul, hk, smul_zero, zero_add,
      Nat.cast_smul_eq_nsmul]
  let ρ' : Representation (ZMod (l ^ r)) G M := modRep (l ^ r) ρ
  have e : resCoef ℤ_[l] ρ' = ρ := by ext; rfl
  obtain ⟨a1, a2, a3, a4, a5⟩ := h r hr M ρ' hρ
  obtain ⟨⟨e0⟩, ⟨e1⟩, ⟨e2⟩, en⟩ := UpperTheory.nonempty_cohomology_restrictScalars_linearEquiv ℤ_[l] ρ'
  rw [← e]
  refine ⟨Finite.of_equiv _ e1.toEquiv.symm, Finite.of_equiv _ e2.toEquiv.symm, fun n hn => ?_, ?_, ?_⟩
  · obtain ⟨e'⟩ := en n
    have := a3 n hn
    exact e'.toEquiv.subsingleton
  · rw [Nat.card_congr e0.toEquiv, Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv, a4]
  · rw [Nat.card_congr e2.toEquiv, a5, H0dual_eq,
      ← Nat.card_congr (Submodule.dualQuotEquivDualAnnihilator _).toEquiv]
    have : Finite (M ⧸ coSub ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ) ρ') :=
      Finite.of_surjective _ (Submodule.mkQ_surjective _)
    rw [KStar.Selmer.card_dual_of_baer KStar.Selmer.zmod_baer]
    exact card_co hs χ _ (fun g => rfl) ρ'
