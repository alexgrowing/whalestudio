import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityFiniteDiscreteModules

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.LocalPair

theorem exists_dual_equiv {n : ℕ} [NeZero n] {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    {M' : Type} [AddCommGroup M'] [Module (ZMod n) M'] [Finite M'] (P : M →+ M' →+ ZMod n)
    (h1 : ∀ x, (∀ y, P x y = 0) → x = 0) (h2 : ∀ y, (∀ x, P x y = 0) → y = 0) :
    ∃ e : M' ≃+ TDual (ZMod n) M, ∀ y x, e y x = P x y := by
  let f : M' →+ TDual (ZMod n) M := AddMonoidHom.mk'
    (fun y => TDual.mk ((P.flip y).toZModLinearMap n)) (fun y y' => by ext x; simp)
  have hf : ∀ y x, f y x = P x y := fun _ _ => rfl
  have inj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    refine h2 y fun x => ?_
    rw [← hf, hy]
    rfl
  have c1 : Nat.card (TDual (ZMod n) M) = Nat.card M := GlobalTheory.ZModDual.card_dual_eq n M
  have : Finite (TDual (ZMod n) M) := Nat.finite_of_card_ne_zero (by rw [c1]; exact Nat.card_pos.ne')
  have c2 : Nat.card (Module.Dual (ZMod n) M') = Nat.card M' := GlobalTheory.ZModDual.card_dual_eq n M'
  have : Finite (Module.Dual (ZMod n) M') := Nat.finite_of_card_ne_zero (by rw [c2]; exact Nat.card_pos.ne')
  have c3 : Nat.card M ≤ Nat.card M' := by
    rw [← c2]
    refine Nat.card_le_card_of_injective (fun x => ((P x).toZModLinearMap n : Module.Dual (ZMod n) M')) ?_
    intro x x' hx
    rw [← sub_eq_zero]
    refine h1 _ fun y => ?_
    rw [map_sub, AddMonoidHom.sub_apply, sub_eq_zero]
    exact DFunLike.congr_fun hx y
  exact ⟨AddEquiv.ofBijective f (inj.bijective_of_nat_card_le (c1 ▸ c3)), hf⟩

theorem dual_equivariant {n : ℕ} {Λ D : Type} [CommRing Λ] [Group D]
    {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Module Λ M] {M' : Type} [AddCommGroup M'] [Module Λ M']
    (ρ : Representation Λ D M) (ρ' : Representation Λ D M') (P : M →+ M' →+ ZMod n) (χ : D →* (ZMod n)ˣ)
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = (χ g : ZMod n) * P x y) (e : M' ≃+ TDual (ZMod n) M)
    (he : ∀ y x, e y x = P x y) (g : D) (y : M') : e (ρ' g y) = twDual χ (zmodRep n ρ) g (e y) := by
  ext x
  rw [twDual_apply, he, he]
  change _ = _ * P (ρ g⁻¹ x) y
  rw [← hP, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

section Transport

variable {R R' : Type} [CommRing R] [CommRing R'] {D : Type} [Group D] [TopologicalSpace D]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [DiscreteTopology M']
  (ρ : Representation R D M) (ρ' : Representation R' D M') (e : M ≃+ M')
  (he : ∀ g m, e (ρ g m) = ρ' g (e m))

private def cocycleTransport : Z1 ρ ≃+ Z1 ρ' where
  toFun z := ⟨fun g => e (z.1 g), continuous_of_discreteTopology.comp z.2.1, fun g h => by
    beta_reduce
    rw [z.2.2, map_add, he]⟩
  invFun z := ⟨fun g => e.symm (z.1 g), continuous_of_discreteTopology.comp z.2.1, fun g h => by
    apply e.injective
    rw [map_add, he]
    simp only [AddEquiv.apply_symm_apply]
    exact z.2.2 g h⟩
  left_inv z := Subtype.ext (funext fun g => e.symm_apply_apply _)
  right_inv z := Subtype.ext (funext fun g => e.apply_symm_apply _)
  map_add' z w := Subtype.ext (funext fun g => map_add e _ _)

include he in

private theorem exists_H1_transport : ∃ T : H1 ρ ≃+ H1 ρ', ∀ (z : Z1 ρ) (z' : Z1 ρ'),
    (∀ g, z'.1 g = e (z.1 g)) → T (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' := by
  refine ⟨QuotientAddGroup.congr ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup
    ((B1 ρ').comap (Z1 ρ').subtype).toAddSubgroup (cocycleTransport ρ ρ' e he) ?_, fun z z' h => ?_⟩
  · ext z'
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ _).1 hz
      refine (mem_coboundaries1 ρ' _).2 ⟨e m, fun g => ?_⟩
      change e (z.1 g) = _
      rw [← he, ← map_sub]
      exact congrArg e (hm g)
    · intro hz
      obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ' _).1 hz
      refine ⟨(cocycleTransport ρ ρ' e he).symm z', (mem_coboundaries1 ρ _).2 ⟨e.symm m, fun g => ?_⟩,
        (cocycleTransport ρ ρ' e he).apply_symm_apply z'⟩
      apply e.injective
      change e (e.symm (z'.1 g)) = _
      rw [map_sub, he, e.apply_symm_apply, e.apply_symm_apply]
      exact hm g
  · obtain rfl : z' = cocycleTransport ρ ρ' e he z := Subtype.ext (funext h)
    rfl

end Transport

private theorem card_H0_transport {R R' : Type} [CommRing R] [CommRing R'] {D D' : Type} [Group D] [Group D']
    {M : Type} [AddCommGroup M] [Module R M] {M' : Type} [AddCommGroup M'] [Module R' M']
    (ρ : Representation R D M) (ρ' : Representation R' D' M') (φ : D → D')
    (hφ : Function.Surjective φ) (e : M ≃+ M') (he : ∀ g m, e (ρ g m) = ρ' (φ g) (e m)) :
    Nat.card (H0 ρ') = Nat.card (H0 ρ) := by
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun m => ?_)).symm
  change (∀ g, ρ g m = m) ↔ ∀ g, ρ' g (e m) = e m
  rw [hφ.forall]
  refine forall_congr' fun g => ?_
  rw [← he, e.injective.eq_iff]

theorem local_pair : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (Λ : Type) [CommRing Λ] (W : Type) [AddCommGroup W] [Module Λ W] [TopologicalSpace W] [DiscreteTopology W] [Finite W] (W' : Type) [AddCommGroup W'] [Module Λ W'] [TopologicalSpace W'] [DiscreteTopology W'] [Finite W'] (ρ : Representation Λ (Dec (F := F) A) W) (ρ' : Representation Λ (Dec (F := F) A) W') (P : W →+ W' →+ ZMod (l ^ n)), 0 < n → ContAction ρ → ContAction ρ' → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y) → (∀ y : Z1 ρ', (∀ x : Z1 ρ, CupB (fun g : Dec (F := F) A => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) (fun g m => ρ' g m) P x.1 y.1) ↔ Cob ρ' y.1) ∧ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H0 ρ')) := by
  intro hLF hLD hLE F Ω _ _ _ _ _ l _ n A v hA Λ _ W _ _ _ _ _ W' _ _ _ _ _ ρ ρ' P hn hρ hρ' h1 h2 hP
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : Module (ZMod (l ^ n)) W := AddCommGroup.zmodModule fun x => h1 _ fun y => by
    rw [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have : Module (ZMod (l ^ n)) W' := AddCommGroup.zmodModule fun y => h2 _ fun x => by
    rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  let χ := (cycMod F Ω l n).comp (Dec (F := F) A).subtype
  refine ⟨fun y => ⟨fun H => ?_, ?_⟩, fun hv => ?_⟩
  · obtain ⟨e, he⟩ := exists_dual_equiv P.flip h2 h1
    have hee := dual_equivariant ρ' ρ P.flip χ (fun g y x => hP g x y) e he
    have hinj := (hLD F Ω l n W' A (zmodRep (l ^ n) ρ') v hn hA hρ').2.2.2.1.1
    rw [injective_iff_map_eq_zero] at hinj
    let y' : Z1 ((zmodRep (l ^ n) ρ').comp (MonoidHom.id _)) := ⟨y.1, y.2.1, y.2.2⟩
    have h0 := hinj (Submodule.Quotient.mk y') (by
      refine LinearMap.ext fun x => ?_
      induction x using Submodule.Quotient.induction_on with | H x =>
      obtain ⟨x, rfl⟩ := (cocycleTransport ρ ((twDual χ (zmodRep (l ^ n) ρ')).comp (MonoidHom.id _)) e hee).surjective x
      obtain ⟨f, hf1, hf2⟩ := H x
      refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨f, hf1.continuous, funext fun p => ?_⟩)
      exact (hf2 p.1 p.2).symm.trans (he _ _).symm)
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
    exact ⟨m, hm⟩
  · rintro ⟨m, hm⟩ x
    refine ⟨fun g => -P (x.1 g) (ρ' g m), (IsLocallyConstant.iff_continuous _).2 ?_, fun g h => ?_⟩
    · exact ((continuous_of_discreteTopology (f := fun p : W × W' => P p.1 p.2)).comp
        (x.2.1.prodMk (hρ'.comp (continuous_id.prodMk continuous_const)))).neg
    · beta_reduce
      rw [mul_neg, ← hP, x.2.2, hm, map_mul, Module.End.mul_apply]
      simp only [map_add, map_sub, AddMonoidHom.add_apply]
      ring
  · obtain ⟨e, he⟩ := exists_dual_equiv P h1 h2
    have hee := dual_equivariant ρ ρ' P χ hP e he
    obtain ⟨⟨j⟩, -, -, -, hb⟩ := hLD F Ω l n W A (zmodRep (l ^ n) ρ) v hn hA hρ
    have hE := (hLE F Ω l n W A (zmodRep (l ^ n) ρ) v hn hA hρ).2 hv
    obtain ⟨T, -⟩ := exists_H1_transport ρ (zmodRep (l ^ n) ρ) (AddEquiv.refl W) fun _ _ => rfl
    have c0 := card_H0_transport ρ (zmodRep (l ^ n) ρ) id Function.surjective_id (AddEquiv.refl W) fun _ _ => rfl
    have c0' := card_H0_transport ρ' ((twDual χ (zmodRep (l ^ n) ρ)).comp (MonoidHom.id _)) id Function.surjective_id e hee
    have : Finite (TDual (ZMod (l ^ n)) W) := Finite.of_equiv _ e.toEquiv
    rw [Nat.card_congr T.toEquiv, hE, c0, ← c0']
    congr 1
    refine (Nat.card_eq_of_bijective _ hb).trans ?_
    exact (Nat.card_congr (LinearEquiv.congrRight j).toEquiv).trans (GlobalTheory.ZModDual.card_dual_eq _ _)

end GlobalTheory.LocalPair
