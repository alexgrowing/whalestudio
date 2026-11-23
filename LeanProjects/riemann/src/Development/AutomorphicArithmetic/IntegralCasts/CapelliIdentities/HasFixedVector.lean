import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

private lemma sum_shift {H M : Type} [Group H] [AddCommMonoid M] (K : Subgroup H)
    [Fintype (H ⧸ K)] (φ : H → M) (hφ : ∀ g, ∀ k ∈ K, φ (g * k) = φ g) (h : H) :
    ∑ q : H ⧸ K, φ (h * (q.out : H)) = ∑ q : H ⧸ K, φ (q.out : H) := by
  have key : ∀ q : H ⧸ K, φ (h * (q.out : H)) = φ ((h • q : H ⧸ K).out : H) := by
    intro q
    have e : ((h * (q.out : H) : H) : H ⧸ K) = h • q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hk : (h * (q.out : H))⁻¹ * ((h • q : H ⧸ K).out : H) ∈ K := by
      apply QuotientGroup.eq.mp
      rw [QuotientGroup.out_eq']
      exact e
    have := hφ (h * (q.out : H)) _ hk
    rw [mul_inv_cancel_left] at this
    exact this.symm
  simp_rw [key]
  exact Equiv.sum_comp (MulAction.toPerm h) (fun q : H ⧸ K => φ (q.out : H))

private lemma core {G W V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [_root_.Module ℂ W] [AddCommGroup V] [_root_.Module ℂ V]
    (σ : Representation ℂ G W) (τ : Representation ℂ G V)
    (hsm : ∀ x : W, IsOpen {g : G | σ g x = x})
    (hsup : ⨆ f : {f : W →ₗ[ℂ] V // ∀ (g : G) (x : W), f (σ g x) = τ g (f x)},
      LinearMap.range (f : W →ₗ[ℂ] V) = ⊤)
    {U : Subgroup G} (hU : IsCompact (U : Set G))
    {v : V} (hv : v ≠ 0) (hfix : ∀ u ∈ U, τ u v = v) :
    ∃ x : W, x ≠ 0 ∧ ∀ u ∈ U, σ u x = x := by
  classical
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have hvt : v ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ (g : G) (x : W), f (σ g x) = τ g (f x)},
      LinearMap.range (f : W →ₗ[ℂ] V) := by rw [hsup]; trivial
  obtain ⟨c, hc, hcs⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hvt
  choose x hx using fun i => LinearMap.mem_range.mp (hc i)
  let stab : W → OpenSubgroup U := fun y =>
    { toSubgroup :=
       { carrier := {h : U | σ (h : G) y = y}
         mul_mem' := by
           intro a b ha hb
           simp only [Set.mem_setOf_eq] at ha hb ⊢
           simp [map_mul, Module.End.mul_apply, ha, hb]
         one_mem' := by simp
         inv_mem' := by
           intro a ha
           simp only [Set.mem_setOf_eq] at ha ⊢
           have : σ ((a : G)⁻¹) (σ (a : G) y) = y := by
             rw [← Module.End.mul_apply, ← map_mul]; simp
           rw [ha] at this
           simpa using this }
      isOpen' := (hsm y).preimage continuous_subtype_val }
  let K : OpenSubgroup U := c.support.inf (fun i => stab (x i))
  haveI : Finite (U ⧸ (K : Subgroup U)) := Subgroup.quotient_finite_of_isOpen _ K.isOpen
  haveI := Fintype.ofFinite (U ⧸ (K : Subgroup U))
  have hK : ∀ i ∈ c.support, ∀ k ∈ (K : Subgroup U), σ ((k : U) : G) (x i) = x i := by
    intro i hi k hk
    have hle : K ≤ stab (x i) := Finset.inf_le hi
    exact hle hk
  let A : W → W := fun y => ∑ q : U ⧸ (K : Subgroup U), σ (((q.out : U)) : G) y
  have hAfix : ∀ i ∈ c.support, ∀ u ∈ U, σ u (A (x i)) = A (x i) := by
    intro i hi u hu
    have := sum_shift (K : Subgroup U) (fun h : U => σ (h : G) (x i))
      (by
        intro g k hk
        simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
        rw [hK i hi k hk]) ⟨u, hu⟩
    simp only [A, map_sum]
    simpa [Subgroup.coe_mul, map_mul, Module.End.mul_apply] using this
  have hsum : ∑ i ∈ c.support, (i : {f : W →ₗ[ℂ] V // ∀ (g : G) (x : W), f (σ g x) = τ g (f x)}).1 (A (x i))
      = (Fintype.card (U ⧸ (K : Subgroup U)) : ℂ) • v := by
    have h1 : ∀ i ∈ c.support, i.1 (A (x i)) = ∑ q : U ⧸ (K : Subgroup U), τ (((q.out : U)) : G) (c i) := by
      intro i _
      simp only [A, map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [i.2, hx i]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    have h2 : ∀ q : U ⧸ (K : Subgroup U), ∑ i ∈ c.support, τ (((q.out : U)) : G) (c i) = v := by
      intro q
      have hcs' : ∑ i ∈ c.support, c i = v := hcs
      rw [← map_sum, hcs']
      exact hfix _ (q.out : U).2
    simp only [h2, Finset.sum_const, Finset.card_univ]
    rw [Nat.cast_smul_eq_nsmul]
  have hne : (Fintype.card (U ⧸ (K : Subgroup U)) : ℂ) • v ≠ 0 := by
    refine smul_ne_zero ?_ hv
    exact_mod_cast Fintype.card_ne_zero
  rw [← hsum] at hne
  obtain ⟨i, hi, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine ⟨A (x i), ?_, hAfix i hi⟩
  intro h0
  exact hne' (by rw [h0, map_zero])

theorem UpperTheory.Reformulated.B.HasFixedVector.hasFixed :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] {n : ℕ} {V : Type} [inst_2 : AddCommGroup V]
      [inst_3 : _root_.Module ℂ V] {ρ : Representation ℂ (GL (Fin n) (GlobalTheory.CuspRep.Af F)) V}
      {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)}
      {σ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w))},
      UpperTheory.V.Af.LocIsotypic ρ w σ →
        ∀ {U : Subgroup (GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w))},
          IsCompact (↑U : Set (GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w))) →
            UpperTheory.V.Af.HasFixed (MonoidHom.comp ρ (GlobalTheory.CuspRep.locGL F n w)) U → UpperTheory.V.Af.HasFixed σ.ρ U := by
  intro F _ _ n V _ _ ρ w σ hiso U hU hfix
  obtain ⟨v, hv, hvfix⟩ := hfix
  obtain ⟨x, hx, hxfix⟩ := core σ.ρ (MonoidHom.comp ρ (GlobalTheory.CuspRep.locGL F n w))
    (by
      cases σ with
      | mk W ρ' hs hi => exact hs)
    (by simpa using hiso.2) hU hv hvfix
  exact ⟨x, hx, hxfix⟩
