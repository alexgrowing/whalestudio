import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenbergWilesTotallyComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelAllEquivSel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFieldExistsTraceFormDualBasesPowOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFCocIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

namespace GlobalTheory.DualPairFormula

section Transport

variable {R R' : Type} [CommRing R] [CommRing R'] {D : Type} [Group D] [TopologicalSpace D]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [DiscreteTopology M']
  (ρ : Representation R D M) (ρ' : Representation R' D M') (e : M ≃+ M')
  (he : ∀ g m, e (ρ g m) = ρ' g (e m))

def cocycleEquiv : Z1 ρ ≃+ Z1 ρ' where
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

theorem exists_H1_equiv_of_equivariant_equiv : ∃ T : H1 ρ ≃+ H1 ρ', ∀ (z : Z1 ρ) (z' : Z1 ρ'),
    (∀ g, z'.1 g = e (z.1 g)) → T (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' := by
  refine ⟨QuotientAddGroup.congr ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup
    ((B1 ρ').comap (Z1 ρ').subtype).toAddSubgroup (cocycleEquiv ρ ρ' e he) ?_, fun z z' h => ?_⟩
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
      refine ⟨(cocycleEquiv ρ ρ' e he).symm z', (mem_coboundaries1 ρ _).2 ⟨e.symm m, fun g => ?_⟩,
        (cocycleEquiv ρ ρ' e he).apply_symm_apply z'⟩
      apply e.injective
      change e (e.symm (z'.1 g)) = _
      rw [map_sub, he, e.apply_symm_apply, e.apply_symm_apply]
      exact hm g
  · obtain rfl : z' = cocycleEquiv ρ ρ' e he z := Subtype.ext (funext h)
    rfl

end Transport

theorem exists_transport_cond {R : Type} [CommRing R] {n : ℕ} {D : Type} [Group D]
    [TopologicalSpace D] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [DiscreteTopology M] {M' : Type} [AddCommGroup M'] [Module (ZMod n) M'] [TopologicalSpace M']
    [DiscreteTopology M'] (ρ : Representation R D M) (ρ' : Representation (ZMod n) D M')
    (e : M ≃+ M') (he : ∀ g m, e (ρ g m) = ρ' g (e m)) (L : Submodule R (H1 ρ)) :
    ∃ L' : Submodule (ZMod n) (H1 ρ'), Nat.card L' = Nat.card L ∧ ∀ (z : Z1 ρ) (z' : Z1 ρ'),
      (∀ g, z'.1 g = e (z.1 g)) → (Submodule.Quotient.mk z ∈ L ↔ Submodule.Quotient.mk z' ∈ L') := by
  obtain ⟨T, hT⟩ := exists_H1_equiv_of_equivariant_equiv ρ ρ' e he
  refine ⟨AddSubgroup.toZModSubmodule n (L.toAddSubgroup.comap T.symm.toAddMonoidHom), ?_,
    fun z z' h => ?_⟩
  · exact Nat.card_congr (T.symm.toEquiv.subtypeEquiv fun _ => Iff.rfl)
  · rw [← hT z z' h]
    change _ ↔ T.symm (T _) ∈ L
    rw [T.symm_apply_apply]

theorem card_H0_eq_of_equivariant_equiv {R R' : Type} [CommRing R] [CommRing R'] {D D' : Type} [Group D] [Group D']
    {M : Type} [AddCommGroup M] [Module R M] {M' : Type} [AddCommGroup M'] [Module R' M']
    (ρ : Representation R D M) (ρ' : Representation R' D' M') (φ : D → D')
    (hφ : Function.Surjective φ) (e : M ≃+ M') (he : ∀ g m, e (ρ g m) = ρ' (φ g) (e m)) :
    Nat.card (H0 ρ') = Nat.card (H0 ρ) := by
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun m => ?_)).symm
  change (∀ g, ρ g m = m) ↔ ∀ g, ρ' g (e m) = e m
  rw [hφ.forall]
  refine forall_congr' fun g => ?_
  rw [← he, e.injective.eq_iff]

theorem exists_dual_equiv {n : ℕ} [NeZero n] {k : Type} [Field k] [Finite k]
    {M : Type} [AddCommGroup M] [Module k M] [Module (ZMod n) M] [Finite M]
    {M' : Type} [AddCommGroup M'] [Module k M'] [Finite M'] (P : M →ₗ[k] M' →ₗ[k] k)
    (h1 : ∀ x, (∀ y, P x y = 0) → x = 0) (h2 : ∀ y, (∀ x, P x y = 0) → y = 0)
    (t : k →+ ZMod n) (ht : ∀ b, (∀ a, t (a * b) = 0) → b = 0) :
    ∃ e : M' ≃+ TDual (ZMod n) M, ∀ y x, e y x = t (P x y) := by
  let f : M' →+ TDual (ZMod n) M := AddMonoidHom.mk'
    (fun y => TDual.mk ((t.comp (P.flip y).toAddMonoidHom).toZModLinearMap n))
    (fun y y' => by ext x; simp)
  have hf : ∀ y x, f y x = t (P x y) := fun _ _ => rfl
  have inj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    refine h2 y fun x => ht _ fun a => ?_
    have := hf y (a • x)
    rw [hy, map_smul P, LinearMap.smul_apply, smul_eq_mul] at this
    exact this.symm
  have c1 : Nat.card (TDual (ZMod n) M) = Nat.card M := GlobalTheory.ZModDual.card_dual_eq n M
  have : Finite (TDual (ZMod n) M) := Nat.finite_of_card_ne_zero (by rw [c1]; exact Nat.card_pos.ne')
  have c2 : Nat.card (Module.Dual k M') = Nat.card M' :=
    Nat.card_congr (Module.finBasis k M').toDualEquiv.symm.toEquiv
  have : Finite (Module.Dual k M') := Nat.finite_of_card_ne_zero (by rw [c2]; exact Nat.card_pos.ne')
  have c3 : Nat.card M ≤ Nat.card M' := by
    rw [← c2]
    refine Nat.card_le_card_of_injective (P : M → Module.Dual k M') ?_
    rw [injective_iff_map_eq_zero]
    exact fun x hx => h1 x fun y => by rw [hx]; rfl
  exact ⟨AddEquiv.ofBijective f (inj.bijective_of_nat_card_le (c1 ▸ c3)), hf⟩

theorem form_val_mul {n : ℕ} [NeZero n] {k : Type} [Field k] (t : k →+ ZMod n) (c : ZMod n) (a : k) :
    t ((c.val : k) * a) = c * t a := by
  rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem perp_iff {n : ℕ} [NeZero n] {k : Type} [Field k] (ι : ZMod n →+* k)
    {M : Type} [AddCommGroup M] [Module k M] [Module (ZMod n) M] [TopologicalSpace M]
    [DiscreteTopology M] {M' : Type} [AddCommGroup M'] [Module k M'] [TopologicalSpace M']
    [DiscreteTopology M'] {D Γ : Type} [Group D] [TopologicalSpace D] [Group Γ]
    (ρ : Representation k D M) (ρ' : Representation k D M') (P : M →ₗ[k] M' →ₗ[k] k)
    (μ : Γ →* (ZMod n)ˣ) (ρS : Representation (ZMod n) Γ M) (φ : D →* Γ)
    (hρ : ∀ g m, ρ g m = ρS (φ g) m) (hc : ContAction (ρS.comp φ)) (χ : D → k)
    (hχ : ∀ g, χ g = (((μ (φ g) : (ZMod n)ˣ) : ZMod n).val : k))
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y)
    (t : k →+ ZMod n) {m : ℕ} (a b : Fin m → k) (hab : ∀ z, z = ∑ j, ((t (a j * z)).val : k) * b j)
    (L : Submodule k (H1 ρ)) (LS : Submodule (ZMod n) (H1 (ρS.comp φ)))
    (hL : ∀ (z : Z1 ρ) (z' : Z1 (ρS.comp φ)), (∀ g, z'.1 g = z.1 g) →
      (Submodule.Quotient.mk z ∈ L ↔ Submodule.Quotient.mk z' ∈ LS))
    (y : Z1 ρ') (y' : Z1 ((twDual μ ρS).comp φ)) (hy : ∀ g x, y'.1 g x = t (P x (y.1 g))) :
    (∀ x ∈ LS, cupH1H1TwistedDual μ ρS φ hc (Submodule.Quotient.mk y') x = 0) ↔
      ∀ x : Z1 ρ, Submodule.Quotient.mk x ∈ L → CupCob χ ρ' P x.1 y.1 := by
  have hι : ∀ c : ZMod n, ι c = (c.val : k) := fun c => by
    conv_lhs => rw [← ZMod.natCast_zmod_val c, map_natCast]
  have ht : ∀ g z, t (χ g * z) = ((μ (φ g) : (ZMod n)ˣ) : ZMod n) * t z := fun g z => by
    rw [hχ, form_val_mul]
  let E := cocycleEquiv ρ (ρS.comp φ) (AddEquiv.refl M) hρ
  have hE : ∀ x g, (E x).1 g = x.1 g := fun _ _ => rfl
  have key : ∀ (x : Z1 ρ) g h, t (P (x.1 (g * h)) (y.1 (g * h))) = t (P (x.1 g) (y.1 g)) +
      t (P (x.1 g) (ρ' g (y.1 h))) + t (P (ρ g (x.1 h)) (y.1 g)) +
      ((μ (φ g) : (ZMod n)ˣ) : ZMod n) * t (P (x.1 h) (y.1 h)) := fun x g h => by
    rw [x.2.2, y.2.2, ← ht, ← hP]
    simp only [map_add, LinearMap.add_apply]
    ring
  have cb : ∀ x : Z1 ρ, Continuous fun g => t (P (x.1 g) (y.1 g)) := fun x =>
    (continuous_of_discreteTopology (f := fun p : M × M' => t (P p.1 p.2))).comp
      (x.2.1.prodMk y.2.1)
  have hcup : ∀ x : Z1 ρ, cupH1H1TwistedDual μ ρS φ hc (Submodule.Quotient.mk y') (Submodule.Quotient.mk (E x)) = 0 ↔
      ∃ c : D → ZMod n, Continuous c ∧ ∀ g h, t (P (x.1 g) (ρ' g (y.1 h))) =
        ((μ (φ g) : (ZMod n)ˣ) : ZMod n) * c h - c (g * h) + c g := fun x => by
    have e0 : cupH1H1TwistedDual μ ρS φ hc (Submodule.Quotient.mk y') (Submodule.Quotient.mk (E x)) = 0 ↔
      ∃ c : D → ZMod n, Continuous c ∧ ∀ g h,
        ((μ (φ g) : (ZMod n)ˣ) : ZMod n) * c h - c (g * h) + c g = t (P (ρ g (x.1 h)) (y.1 g)) := by
      refine (Submodule.Quotient.mk_eq_zero _).trans ((separated_dvr_second_cohomology_mem _ _).trans ?_)
      refine exists_congr fun c => and_congr_right fun _ => ?_
      rw [funext_iff, Prod.forall]
      refine forall_congr' fun g => forall_congr' fun h => ?_
      rw [← hy, hρ]
      exact Iff.rfl
    rw [e0]
    constructor
    · rintro ⟨c, hc1, hc2⟩
      refine ⟨fun g => -c g - t (P (x.1 g) (y.1 g)), hc1.neg.sub (cb x), fun g h => ?_⟩
      linear_combination hc2 g h - key x g h
    · rintro ⟨c, hc1, hc2⟩
      refine ⟨fun g => -c g - t (P (x.1 g) (y.1 g)), hc1.neg.sub (cb x), fun g h => ?_⟩
      linear_combination hc2 g h + key x g h
  constructor
  · intro H x hx
    have H2 := fun j => (hcup (a j • x)).1 (H _ ((hL _ _ (hE _)).1 (by
      rw [Submodule.Quotient.mk_smul]; exact L.smul_mem _ hx)))
    choose c hc1 hc2 using H2
    refine ⟨fun g => ∑ j, ι (c j g) * b j, ?_, fun g h => ?_⟩
    · exact ((IsLocallyConstant.iff_continuous _).2 (continuous_pi hc1)).comp
        (fun w : Fin m → ZMod n => ∑ j, ι (w j) * b j)
    · rw [hab (P (x.1 g) (ρ' g (y.1 h))), Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e1 := hc2 j g h
      have e2 : P ((a j • x).1 g) (ρ' g (y.1 h)) = a j * P (x.1 g) (ρ' g (y.1 h)) := by
        change P (a j • x.1 g) _ = _
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [e2] at e1
      rw [e1, hχ, ← hι, ← hι, map_add, map_sub, map_mul]
      ring
  · intro H x hx
    induction x using Submodule.Quotient.induction_on with | H x =>
    obtain ⟨x, rfl⟩ := E.surjective x
    obtain ⟨f, hf1, hf2⟩ := H x ((hL _ _ (hE _)).2 hx)
    refine (hcup x).2 ⟨fun g => t (f g), (hf1.comp t).continuous, fun g h => ?_⟩
    rw [hf2, map_add, map_sub, ht]

theorem exists_descent {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M) (hρ : ContAction ρ)
    (S : Set (HeightOneSpectrum (𝓞 F)))
    (h : ∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ σ ∈ Ine (F := F) B, ρ σ = 1) :
    ∃ ρS : Representation R (GS Ω S) M, ContAction ρS ∧ ∀ g m, ρ g m = ρS (toGS Ω S g) m := by
  have hk : NS Ω S ≤ MonoidHom.ker ρ := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) ?_
    · intro τ hτ
      simp only [Set.mem_iUnion] at hτ
      obtain ⟨v, hv, A, hA, hτ⟩ := hτ
      exact h v hv A hA τ hτ
    · have : (MonoidHom.ker ρ : Set (G F Ω)) = ⋂ m, {g | ρ g m = m} := by
        ext g
        simp [LinearMap.ext_iff]
      rw [this]
      exact isClosed_iInter fun m =>
        isClosed_eq (hρ.comp (continuous_id.prodMk continuous_const)) continuous_const
  refine ⟨QuotientGroup.lift _ ρ hk, ?_, fun _ _ => rfl⟩
  unfold ReciprocityTheory.Gal.ContAction
  rw [continuous_prod_of_discrete_right]
  intro m
  rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
  exact hρ.comp (continuous_id.prodMk continuous_const)

theorem greenbergWiles_dualPair : PoitouTateTotallyComplex → LocalFiniteness → GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M] [Finite M] (M' : Type) [AddCommGroup M'] [Module k M'] [TopologicalSpace M'] [DiscreteTopology M'] [Finite M'] (ρ : Representation k (G F Ω) M) (ρ' : Representation k (G F Ω) M') (χ : G F Ω → k) (P : M →ₗ[k] M' →ₗ[k] k), ContAction ρ → ContAction ρ' → (∀ g, χ g = (((cycMod F Ω l 1 g : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)).val : k)) → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Formalism.GaloisCohomology.Places F Ω), ContainsAbove S l → (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ σ ∈ Ine (F := F) B, ρ σ = 1) → ∀ (L : ∀ v, Submodule k (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) (L' : ∀ v, Submodule k (H1 (ρ'.comp (Dec (F := F) (A.1 v)).subtype))), (∀ v ∉ S, L v = Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → (∀ v ∉ S, L' v = Formalism.GaloisCohomology.unrAt ρ' (A.1 v)) → (∀ v ∈ S, ∀ y : Z1 (ρ'.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk y ∈ L' v ↔ ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk x ∈ L v → CupCob (fun g : Dec (F := F) (A.1 v) => χ g.1) (ρ'.comp (Dec (F := F) (A.1 v)).subtype) P x.1 y.1) → Finite (Formalism.GaloisCohomology.SelAll ρ A L) ∧ Finite (Formalism.GaloisCohomology.SelAll ρ' A L') ∧ Nat.card (Formalism.GaloisCohomology.SelAll ρ A L) * Nat.card (H0 ρ') * (∏ v ∈ S, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) * Nat.card M ^ InfinitePlace.nrComplexPlaces F = Nat.card (Formalism.GaloisCohomology.SelAll ρ' A L') * Nat.card (H0 ρ) * ∏ v ∈ S, Nat.card (L v) := by
  intro hPT hLF hGF hEC F Ω _ _ _ _ _ _ l _ k _ _ _ M _ _ _ _ _ M' _ _ _ _ _ ρ ρ' χ P hρ hρ' hχ h1 h2
    hP S A hS hur L L' hL hL' hperp
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨t, ht, m, a, b, hab⟩ := GlobalTheory.finiteField_exists_traceForm_dualBases_pow_one l k
  haveI : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule fun x => by
    rw [pow_one, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  obtain ⟨ρS, hρS, hd⟩ := exists_descent (zmodRep (l ^ 1) ρ) hρ (S : Set _) fun v hv B hB σ hσ => by
    ext x
    change ρ σ x = x
    rw [hur v hv B hB σ hσ]
    rfl
  replace hd : ∀ (g : G F Ω) (x : M), ρ g x = ρS (toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) g) x := hd
  obtain ⟨μ, hμ⟩ := PoitouTate.exists_lift_cycMod (Ω := Ω) (r := 1) hS
  have hχ' : ∀ g, χ g = (((μ (toGS Ω _ g) : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)).val : k) := fun g => by
    rw [hχ, ← hμ]
    rfl
  obtain ⟨e, he⟩ := exists_dual_equiv P h1 h2 t ht
  have hee : ∀ g y, e (ρ' g y) = twDual μ ρS (toGS Ω _ g) (e y) := fun g y => by
    ext x
    rw [twDual_apply, he, he, ← map_inv, ← hd, ← form_val_mul, ← hχ', ← hP,
      ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hex := fun v : S => exists_transport_cond (ρ.comp (Dec (F := F) (A.1 v.1)).subtype)
    (ρS.comp (locFam S (fun v => A.1 v.1) v)) (AddEquiv.refl M) (fun g x => hd g x) (L v.1)
  choose LS hLS1 hLS2 using hex
  obtain ⟨f1, f2, hmain⟩ := GlobalTheory.GWComplex.greenbergWiles_totallyComplex hPT hLF hGF hEC F Ω l 1 M S ρS one_pos hS hρS μ hμ
    (fun v => A.1 v.1) (fun v => A.2 v.1) LS
  obtain ⟨E1⟩ := GlobalTheory.SelInf.selAll_equiv_sel F Ω k (ZMod (l ^ 1)) M M S A ρ ρS (AddEquiv.refl M) hρ hd L LS hL hLS2
  obtain ⟨E2⟩ := GlobalTheory.SelInf.selAll_equiv_sel F Ω k (ZMod (l ^ 1)) M' _ S A ρ' (twDual μ ρS) e hρ' hee L'
    (perpCond μ ρS (locFam S fun v => A.1 v.1) (fun v => hρS.comp' (continuous_locFam S _ v)) LS) hL'
    fun v y y' hy => by
      rw [hperp v.1 v.2 y, mem_perpCond]
      exact (perp_iff (ZMod.castHom (by rw [pow_one]) k) (ρ.comp (Dec (F := F) (A.1 v.1)).subtype)
        (ρ'.comp (Dec (F := F) (A.1 v.1)).subtype) P μ ρS (locFam S (fun v => A.1 v.1) v)
        (fun g x => hd g x) _ (fun g => χ g.1) (fun g => hχ' g) (fun g => hP g) t a b hab (L v.1)
        (LS v) (hLS2 v) y y' (fun g x => by rw [hy, he])).symm
  have hs : Function.Surjective (toGS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) :=
    QuotientGroup.mk'_surjective _
  refine ⟨Finite.of_equiv _ E1.symm, Finite.of_equiv _ E2.symm, ?_⟩
  rw [Nat.card_congr E1, Nat.card_congr E2, ← card_H0_eq_of_equivariant_equiv ρ' _ _ hs e hee,
    ← card_H0_eq_of_equivariant_equiv ρ ρS _ hs (AddEquiv.refl M) hd, ← Finset.prod_coe_sort S, ← Finset.prod_coe_sort S]
  simp only [← hLS1]
  rw [← hmain]
  congr 2
  refine Finset.prod_congr rfl fun v _ => ?_
  exact (card_H0_eq_of_equivariant_equiv (ρ.comp (Dec (F := F) (A.1 v.1)).subtype)
    (ρS.comp (locFam S (fun v => A.1 v.1) v)) id Function.surjective_id (AddEquiv.refl M)
    (fun g x => hd g x)).symm

end GlobalTheory.DualPairFormula
