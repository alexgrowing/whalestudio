import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TwistedDualFrobeniusCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeParametersComplexConjugate
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ContinuousEntryPairings.ExConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ContinuousEntryPairings.IsPairingOfIsAutCsd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
open scoped Matrix
open scoped Pointwise

namespace UpperTheory.V.Z.Ord.CU

section Abs

variable {H H' k : Type} [Group H] [Group H'] [Field k] {n : ℕ}

private theorem trace_of_flag {r : H →* GL (Fin n) k} {ψ : Fin n → H →* kˣ} (h : W.HasFlag r ψ) (s : H) :
    (r s : Matrix (Fin n) (Fin n) k).trace = ∑ i, (ψ i s : k) := by
  obtain ⟨g, hg⟩ := h
  have e : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = (r s : Matrix (Fin n) (Fin n) k).trace := by
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [← e]
  exact Finset.sum_congr rfl fun i _ => (hg s).2 i

private theorem mem_range_of_sum [CharZero k] (a b : Fin n → H →* kˣ) (h : ∀ s, ∑ i, (a i s : k) = ∑ i, (b i s : k)) (i : Fin n) :
    ∃ j, a i = b j := by
  classical
  by_contra hne
  push_neg at hne
  let c : (H →* kˣ) → (H →* k) := fun x => (Units.coeHom k).comp x
  have hc : Function.Injective c := fun x y e => MonoidHom.ext fun s => Units.ext (DFunLike.congr_fun e s)
  let L : (H →* k) →₀ k := ∑ j, Finsupp.single (c (a j)) 1 - ∑ j, Finsupp.single (c (b j)) 1
  have h0 : Finsupp.linearCombination k (fun f : H →* k => (f : H → k)) L = 0 := by
    funext s
    simp only [L, map_sub, map_sum, Finsupp.linearCombination_single, one_smul, Pi.sub_apply, Finset.sum_apply, Pi.zero_apply]
    exact sub_eq_zero.2 (h s)
  have hL := (linearIndependent_iff.1 (linearIndependent_monoidHom H k)) L h0
  have hv : L (c (a i)) = 0 := by rw [hL]; rfl
  have h2 : ∑ j, (Finsupp.single (c (b j)) (1 : k)) (c (a i)) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [Finsupp.single_apply, if_neg fun e => hne j (hc e).symm]
  have h1 : ∑ j, (Finsupp.single (c (a j)) (1 : k)) (c (a i)) = ((Finset.univ.filter fun j => a j = a i).card : k) := by
    simp only [Finsupp.single_apply, hc.eq_iff, Finset.sum_boole]
  have h3 : (Finset.univ.filter fun j => a j = a i).card ≠ 0 :=
    Finset.card_ne_zero.2 ⟨i, by simp⟩
  simp only [L, Finsupp.coe_sub, Finsupp.coe_finset_sum, Pi.sub_apply, Finset.sum_apply, h1, h2, sub_zero] at hv
  exact h3 (by exact_mod_cast hv)

private theorem flag_range [CharZero k] {r : H →* GL (Fin n) k} {a b : Fin n → H →* kˣ} (ha : W.HasFlag r a) (hb : W.HasFlag r b)
    (i : Fin n) : ∃ j, a i = b j :=
  mem_range_of_sum a b (fun s => by rw [← trace_of_flag ha, ← trace_of_flag hb]) i

private theorem flag_comp {r₁ : H →* GL (Fin n) k} {r₂ : H' →* GL (Fin n) k} {f : H' →* H} {N : GL (Fin n) k}
    (hN : ∀ t, r₂ t = N * r₁ (f t) * N⁻¹) {ψ : Fin n → H →* kˣ} (h : W.HasFlag r₁ ψ) :
    W.HasFlag r₂ fun i => (ψ i).comp f := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g * N⁻¹, fun t => ?_⟩
  have e : g * N⁻¹ * r₂ t * (g * N⁻¹)⁻¹ = g * r₁ (f t) * g⁻¹ := by rw [hN]; group
  rw [e]
  exact hg (f t)

private theorem flag_smul {r r' : H →* GL (Fin n) k} {β : H →* kˣ}
    (hr : ∀ s, (r' s : Matrix (Fin n) (Fin n) k) = (β s : k) • (r s : Matrix (Fin n) (Fin n) k)) {ψ : Fin n → H →* kˣ}
    (h : W.HasFlag r ψ) : W.HasFlag r' fun i => ψ i * β := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => ?_⟩
  have e : ((g * r' s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (β s : k) • ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    simp only [Units.val_mul, hr, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have h1 := (hg s).1 i j hij
    change ((g * r' s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0
    rw [e, Matrix.smul_apply]
    change _ • ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0
    rw [show ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0 from h1, smul_zero]
  · have h1 := (hg s).2 i
    change ((g * r' s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = _
    rw [e, Matrix.smul_apply, show ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = _ from h1]
    simp [mul_comm]

private def revM (n : ℕ) (k : Type) [Field k] : Matrix (Fin n) (Fin n) k := (1 : Matrix (Fin n) (Fin n) k).submatrix Fin.rev id

private theorem revM_mul (X : Matrix (Fin n) (Fin n) k) (i j : Fin n) : (revM n k * X) i j = X (Fin.rev i) j := by
  simp [revM, Matrix.mul_apply, Matrix.one_apply]

private theorem mul_revM (X : Matrix (Fin n) (Fin n) k) (i j : Fin n) : (X * revM n k) i j = X i (Fin.rev j) := by
  simp [revM, Matrix.mul_apply, Matrix.one_apply, Fin.rev_eq_iff]

private theorem revM_sq : revM n k * revM n k = 1 := by
  ext i j
  rw [revM_mul]
  simp [revM, Matrix.one_apply]

private def revG (n : ℕ) (k : Type) [Field k] : GL (Fin n) k := ⟨revM n k, revM n k, revM_sq, revM_sq⟩

private def trG (g : GL (Fin n) k) : GL (Fin n) k :=
  ⟨(g : Matrix (Fin n) (Fin n) k)ᵀ, ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)ᵀ,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]⟩

private theorem flag_dual {r : H →* GL (Fin n) k} {ψ : Fin n → H →* kˣ} (h : W.HasFlag r ψ) :
    W.HasFlag (GlobalTheory.MonoConj.dualRep r) fun i => (ψ (Fin.rev i))⁻¹ := by
  obtain ⟨g, hg⟩ := h
  refine ⟨revG n k * (trG g)⁻¹, fun s => ?_⟩
  have e : ((revG n k * (trG g)⁻¹ * GlobalTheory.MonoConj.dualRep r s * (revG n k * (trG g)⁻¹)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      revM n k * ((g * r s⁻¹ * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)ᵀ * revM n k := by
    have e1 : revG n k * (trG g)⁻¹ * GlobalTheory.MonoConj.dualRep r s * (revG n k * (trG g)⁻¹)⁻¹ =
        revG n k * ((trG g)⁻¹ * GlobalTheory.MonoConj.dualRep r s * trG g) * (revG n k)⁻¹ := by group
    rw [e1]
    simp only [Units.val_mul, Matrix.transpose_mul, GlobalTheory.MonoConj.coe_dualRep, Matrix.mul_assoc]
    rfl
  have e2 : ∀ i j, ((revG n k * (trG g)⁻¹ * GlobalTheory.MonoConj.dualRep r s * (revG n k * (trG g)⁻¹)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      ((g * r s⁻¹ * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (Fin.rev j) (Fin.rev i) := fun i j => by
    rw [e, mul_revM, revM_mul, Matrix.transpose_apply]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · exact (e2 i j).trans ((hg s⁻¹).1 _ _ (Fin.rev_lt_rev.2 hij))
  · refine (e2 i i).trans (((hg s⁻¹).2 _).trans ?_)
    simp

private theorem aux₁ {C : Type} [CommGroup C] {a b e μ : C} {m : ℕ} (h : a ^ m = (b * e) ^ m) :
    (b⁻¹ * μ) ^ m = (a⁻¹ * μ * e) ^ m := by
  simp only [mul_pow, inv_pow] at h ⊢
  rw [h, mul_inv]
  simp only [mul_comm, mul_left_comm, mul_assoc]
  rw [mul_left_comm (e ^ m), mul_left_comm (e ^ m), mul_inv_cancel, mul_one]

private theorem aux₂ {C : Type} [CommGroup C] {x y e μ : C} {m : ℕ} (h : (x⁻¹ * μ) ^ m = (y⁻¹ * μ * e) ^ m) :
    y ^ m = (x * e) ^ m := by
  simp only [mul_pow, inv_pow] at h ⊢
  have h' : (x ^ m)⁻¹ = (y ^ m)⁻¹ * e ^ m := by
    have := mul_right_cancel (b := μ ^ m) (a := (x ^ m)⁻¹) (c := (y ^ m)⁻¹ * e ^ m) (by rw [h]; simp [mul_comm, mul_left_comm, mul_assoc])
    exact this
  have h2 : x ^ m = y ^ m * (e ^ m)⁻¹ := by
    have := congrArg (·⁻¹) h'
    simpa [mul_comm] using this
  rw [h2]
  simp

private def Rel (r₁ : H →* GL (Fin n) k) (r₂ : H' →* GL (Fin n) k) (f : H' →* H) : Prop :=
  (∃ N : GL (Fin n) k, ∀ t, r₂ t = N * r₁ (f t) * N⁻¹) ∨
    ∃ (N : GL (Fin n) k) (μ : H' →* kˣ), ∀ t, (r₂ t : Matrix (Fin n) (Fin n) k) =
      (μ t : k) • ((N * GlobalTheory.MonoConj.dualRep r₁ (f t) * N⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)

private theorem abs_main {r₁ : H →* GL (Fin n) k} {r₂ : H' →* GL (Fin n) k} {f : H' →* H} (hf : Function.Surjective f)
    (hr : Rel r₁ r₂ f) {ε : H →* kˣ} {ε' : H' →* kˣ} (hε : ∀ t, ε (f t) = ε' t) {ψ : Fin n → H →* kˣ} (h : W.HasFlag r₁ ψ) :
    ∃ κ : Fin n → H' →* kˣ, W.HasFlag r₂ κ ∧ ∀ m : ℕ, (∃ i j, ψ i ^ m = (ψ j * ε) ^ m) ↔ ∃ a b, κ a ^ m = (κ b * ε') ^ m := by
  rcases hr with ⟨N, hN⟩ | ⟨N, μ, hN⟩
  · refine ⟨fun i => (ψ i).comp f, flag_comp hN h, fun m => ⟨?_, ?_⟩⟩
    · rintro ⟨i, j, e⟩
      refine ⟨i, j, MonoidHom.ext fun t => ?_⟩
      have := DFunLike.congr_fun e (f t)
      simpa [← hε] using this
    · rintro ⟨i, j, e⟩
      refine ⟨i, j, MonoidHom.ext fun s => ?_⟩
      obtain ⟨t, rfl⟩ := hf s
      have := DFunLike.congr_fun e t
      simpa [← hε] using this
  · let r₃ : H' →* GL (Fin n) k :=
      { toFun := fun t => N * GlobalTheory.MonoConj.dualRep r₁ (f t) * N⁻¹
        map_one' := by simp
        map_mul' := fun x y => by simp only [map_mul]; group }
    have h3 : W.HasFlag r₃ fun i => ((ψ (Fin.rev i))⁻¹).comp f := flag_comp (fun _ => rfl) (flag_dual h)
    refine ⟨fun i => ((ψ (Fin.rev i))⁻¹).comp f * μ, flag_smul (r := r₃) hN h3, fun m => ⟨?_, ?_⟩⟩
    · rintro ⟨i, j, e⟩
      refine ⟨Fin.rev j, Fin.rev i, MonoidHom.ext fun t => ?_⟩
      have e1 : ψ i (f t) ^ m = (ψ j (f t) * ε (f t)) ^ m := by
        simpa using DFunLike.congr_fun e (f t)
      have := aux₁ (μ := μ t) e1
      simpa [hε] using this
    · rintro ⟨a, b, e⟩
      refine ⟨Fin.rev b, Fin.rev a, MonoidHom.ext fun s => ?_⟩
      obtain ⟨t, rfl⟩ := hf s
      have e1 : ((ψ (Fin.rev a) (f t))⁻¹ * μ t) ^ m = ((ψ (Fin.rev b) (f t))⁻¹ * μ t * ε (f t)) ^ m := by
        simpa [hε] using DFunLike.congr_fun e t
      simpa using aux₂ e1

end Abs

end UpperTheory.V.Z.Ord.CU

namespace UpperTheory.V.Z.Ord.CU

open UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Af.Gu GlobalTheory.MonoConj

section Conc

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

private theorem cycBar_conjGal {τ : E ≃+* E} {σ : Ω ≃+* Ω} (h : IsLift τ σ) (g : G E Ω) :
    cycBar E Ω l (conjGal h g) = cycBar E Ω l g := by
  have e : cycZ E Ω l (conjGal h g) = cycZ E Ω l g := by
    show cyclotomicCharacter Ω l (conjGal h g).toRingEquiv = cyclotomicCharacter Ω l g.toRingEquiv
    have e : (conjGal h g).toRingEquiv = σ⁻¹ * g.toRingEquiv * σ := rfl
    rw [e, map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  simp only [cycBar, MonoidHom.comp_apply, e]

private def decMap {τ : E ≃+* E} {σ : Ω ≃+* Ω} (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) :
    Dec (F := E) A' →* Dec (F := E) A :=
  ((conjGal h).comp (Dec (F := E) A').subtype).codRestrict _ fun t => conjGal_mem_Dec h hA t.2

private theorem decMap_surj {τ : E ≃+* E} {σ : Ω ≃+* Ω} (h : IsLift τ σ) {A A' : ValuationSubring Ω}
    (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) : Function.Surjective (decMap h hA) := fun s => by
  have hA' : ∀ x, σ.symm x ∈ A ↔ x ∈ A' := fun x => by rw [← hA, RingEquiv.apply_symm_apply]
  refine ⟨⟨conjGal h.symm s.1, conjGal_mem_Dec h.symm hA' s.2⟩, Subtype.ext (AlgEquiv.ext fun x => ?_)⟩
  show conjGal h (conjGal h.symm s.1) x = s.1 x
  simp [conjGal_apply]

private theorem rel_one {τ : E ≃+* E} {σ : Ω ≃+* Ω} (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A)
    (ρ : G E Ω →* GL (Fin n) (Qbar l)) (hτ : ∀ x, τ x = x) :
    Rel (ρ.comp (Dec (F := E) A).subtype) (ρ.comp (Dec (F := E) A').subtype) (decMap h hA) := by
  let g₀ : G E Ω := AlgEquiv.ofRingEquiv (f := σ) fun x => by rw [h, hτ]
  refine Or.inl ⟨ρ g₀, fun t => ?_⟩
  have e : conjGal h t.1 = g₀⁻¹ * t.1 * g₀ := AlgEquiv.ext fun x => rfl
  show ρ t.1 = ρ g₀ * ρ (conjGal h t.1) * (ρ g₀)⁻¹
  rw [e, map_mul, map_mul, map_inv]
  group

private theorem isLift_of_conjEl [IsCMField E] {c : G (maximalRealSubfield E) Ω} (hc : IsConjEl c) :
    IsLift (IsCMField.complexConj E).toRingEquiv c.toRingEquiv := fun x => by
  obtain ⟨j, hj⟩ := hc
  refine j.injective ((hj _).trans ?_)
  exact (IsCMField.complexEmbedding_complexConj E (j.comp (algebraMap E Ω)) x).symm

private theorem rel_conj [IsCMField E] {τ : E ≃+* E} {σ : Ω ≃+* Ω} (h : IsLift τ σ) {A A' : ValuationSubring Ω}
    (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) (ρ : G E Ω →* GL (Fin n) (Qbar l)) (hτ : ∀ x, τ x = IsCMField.complexConj E x)
    (g : G (maximalRealSubfield E) Ω) (hg : g.toRingEquiv = σ)
    {c : G (maximalRealSubfield E) Ω} (hc : IsConjEl c) {P : GL (Fin n) (Qbar l)}
    (hP : IsPairing c ρ (cycBar E Ω l ^ (1 - (n : ℤ))) P) :
    Rel (ρ.comp (Dec (F := E) A).subtype) (ρ.comp (Dec (F := E) A').subtype) (decMap h hA) := by
  subst hg
  have hL := isLift_of_conjEl hc
  let u : G E Ω := AlgEquiv.ofRingEquiv (f := c.symm.toRingEquiv.trans g.toRingEquiv) fun x => by
    have e : c.symm (algebraMap E Ω x) = algebraMap E Ω (IsCMField.complexConj E x) := by
      rw [AlgEquiv.symm_apply_eq]
      refine ((hL _).trans ?_).symm
      rw [show (IsCMField.complexConj E).toRingEquiv (IsCMField.complexConj E x) = x from IsCMField.complexConj_apply_apply E x]
    show g (c.symm (algebraMap E Ω x)) = _
    rw [e]
    refine (h _).trans ?_
    rw [hτ, IsCMField.complexConj_apply_apply]
  refine Or.inr ⟨ρ u * P⁻¹, ((cycBar E Ω l ^ (1 - (n : ℤ))).comp (conjGal h)).comp (Dec (F := E) A').subtype, fun t => ?_⟩
  set s : G E Ω := conjGal h t.1 with hs
  let s' : G E Ω := u⁻¹ * t.1 * u
  have hs' : s'.restrictScalars (maximalRealSubfield E) = c * s.restrictScalars (maximalRealSubfield E) * c⁻¹ :=
    AlgEquiv.ext fun x => rfl
  have hpair := hP s s' hs'
  have hD : (dualRep ρ s : Matrix (Fin n) (Fin n) (Qbar l)) * (ρ s : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = 1 := by
    rw [coe_dualRep, ← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.transpose_one]
  have hQ : (ρ s' : Matrix (Fin n) (Fin n) (Qbar l)) =
      ((cycBar E Ω l ^ (1 - (n : ℤ))) s : Qbar l) • ((P⁻¹ * dualRep ρ s * P : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    have h1 : (P : Matrix (Fin n) (Fin n) (Qbar l)) * (ρ s' : Matrix (Fin n) (Fin n) (Qbar l)) =
        ((cycBar E Ω l ^ (1 - (n : ℤ))) s : Qbar l) • ((dualRep ρ s : Matrix (Fin n) (Fin n) (Qbar l)) * (P : Matrix (Fin n) (Fin n) (Qbar l))) := by
      have := congrArg (fun X => (dualRep ρ s : Matrix (Fin n) (Fin n) (Qbar l)) * X) hpair
      simp only [Matrix.mul_smul, ← Matrix.mul_assoc, hD, Matrix.one_mul] at this
      exact this
    have h2 := congrArg (fun X => ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * X) h1
    simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_smul] at h2
    rw [inv_mul_cancel_left, ← mul_assoc] at h2
    exact h2
  have ht : ρ t.1 = ρ u * ρ s' * (ρ u)⁻¹ := by
    simp only [s', map_mul, map_inv]
    group
  have e1 : ρ u * P⁻¹ * dualRep (ρ.comp (Dec (F := E) A).subtype) (decMap h hA t) * (ρ u * P⁻¹)⁻¹ =
      ρ u * (P⁻¹ * dualRep ρ s * P) * (ρ u)⁻¹ := by
    have e2 : dualRep (ρ.comp (Dec (F := E) A).subtype) (decMap h hA t) = dualRep ρ s := rfl
    rw [e2]
    group
  show (ρ t.1 : Matrix (Fin n) (Fin n) (Qbar l)) = ((cycBar E Ω l ^ (1 - (n : ℤ))) s : Qbar l) • _
  rw [e1, ht]
  simp only [Units.val_mul (ρ u * ρ s'), Units.val_mul (ρ u), hQ]
  simp only [Units.val_mul, Matrix.mul_smul, Matrix.smul_mul]

end Conc

end UpperTheory.V.Z.Ord.CU

namespace UpperTheory.V.Z.Ord.CU

open UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Af.Gu GlobalTheory.MonoConj

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

private theorem isPlaceOver_real {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) :
    IsPlaceOver (F := maximalRealSubfield E) A (w.under (𝓞 (maximalRealSubfield E))) := fun x =>
  h (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) x)

private theorem gal_cases (t : E ≃ₐ[maximalRealSubfield E] E) : t = 1 ∨ t = IsCMField.complexConj E := by
  have hc : Nat.card (E ≃ₐ[maximalRealSubfield E] E) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  obtain ⟨y, _, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[maximalRealSubfield E] E)).1 hc
  by_cases h1 : t = 1
  · exact Or.inl h1
  · exact Or.inr ((hy t h1).trans (hy _ (IsCMField.complexConj_ne_one E)).symm)

private theorem exists_rel (ρ : G E Ω →* GL (Fin n) (Qbar l))
    (hp : ∀ c : G (maximalRealSubfield E) Ω, IsConjEl c → ∃ P, IsPairing c ρ (cycBar E Ω l ^ (1 - (n : ℤ))) P)
    {A A' : ValuationSubring Ω} (g : G (maximalRealSubfield E) Ω) (hg : g • A = A') :
    ∃ f : Dec (F := E) A' →* Dec (F := E) A, Function.Surjective f ∧
      Rel (ρ.comp (Dec (F := E) A).subtype) (ρ.comp (Dec (F := E) A').subtype) f ∧
      ∀ t, cycBar E Ω l (f t).1 = cycBar E Ω l t.1 := by
  have hA : ∀ x, g.toRingEquiv x ∈ A' ↔ x ∈ A := fun x => by
    subst hg
    exact ValuationSubring.smul_mem_pointwise_smul_iff (g := g)
  have h : IsLift (g.restrictNormal E).toRingEquiv g.toRingEquiv := fun x =>
    (AlgEquiv.restrictNormal_commutes g E x).symm
  refine ⟨decMap h hA, decMap_surj h hA, ?_, fun t => cycBar_conjGal h t.1⟩
  rcases gal_cases (g.restrictNormal E) with e | e
  · exact rel_one h hA ρ fun x => by
      show g.restrictNormal E x = x
      rw [e]; rfl
  · obtain ⟨c, hc⟩ := (GlobalTheory.ConjElOverReal.main E Ω).1
    obtain ⟨P, hP⟩ := hp c hc
    exact rel_conj h hA ρ (fun x => by
      show g.restrictNormal E x = _
      rw [e]) g rfl hc hP

end UpperTheory.V.Z.Ord.CU
