import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.FinQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.SingleSubMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.TwMapEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.TwMapUniq
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.LevelJ
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5 GlobalTheory.GalOfCusp

private theorem lc_of_ker {G Q : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] [Group Q]
    (q : G →* Q) (h : IsOpen (q.ker : Set G)) : IsLocallyConstant q := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨(fun y => x⁻¹ * y) ⁻¹' q.ker,
    h.preimage (continuous_const.mul continuous_id), by simp, fun y hy => ?_⟩
  have : q (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this.symm

private theorem lift_mem {B R Q : Type} [CommRing B] [CommRing R] [Algebra B R] [Monoid Q]
    (j : Q →* R) (J : Ideal B) (x : MonoidAlgebra B Q) (h : ∀ z, x.coeff z ∈ J) :
    MonoidAlgebra.lift B R Q j x ∈ J.map (algebraMap B R) := by
  rw [MonoidAlgebra.lift_apply]
  refine Ideal.sum_mem _ fun z _ => ?_
  beta_reduce
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (h z))

theorem UpperTheory.V.Ws.H5.twJN :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B), B.Dense J → B.TwistOk J → ((l : ℕ) : B.B) ∈ maximalIdeal B.B → ∀ γ : V.frame.G₀ →* B.Bˣ, TwCh V.frame γ → ∀ τ : B.B →ₐ[c.O] B.B, TwMap B (RingHom.id B.B) (τ : B.B →+* B.B) γ → ∀ b ∈ J, ∀ N : ℕ, τ b ∈ J ⊔ maximalIdeal B.B ^ (N + 1) := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B J hD hT hl γ hγ τ hτ b hb N
  obtain ⟨Q, _, _, q, j, hQ, hq, hA, hj⟩ := finQuot V.frame hl γ hγ (N + 1)
  obtain ⟨_, hz⟩ := grpCO l c.O B.B hl Q hQ
  have hΓ : TwCh V.frame ((MonoidAlgebra.of B.B Q).toHomUnits.comp q) :=
    ⟨hA.mono fun g hg => by
        rw [MonoidHom.mem_ker] at hg ⊢
        rw [MonoidHom.comp_apply, hg, map_one],
      fun M => (lc_of_ker q hq).comp fun z =>
        Ideal.Quotient.mk (maximalIdeal (MonoidAlgebra B.B Q) ^ M) (MonoidAlgebra.single z 1),
      fun g => hz (q g)⟩
  obtain ⟨tw, htw⟩ := twMapEx B (IsScalarTower.toAlgHom c.O B.B (MonoidAlgebra B.B Q)) _ hΓ
  have hJ := levelJ B J hD hT Q hQ q hq hA tw htw b hb
  haveI : Nontrivial (B.B ⧸ maximalIdeal B.B ^ (N + 1)) := Ideal.Quotient.nontrivial_iff.2 fun h =>
    (maximalIdeal.isMaximal B.B).ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero N)))
  haveI : IsCO c.O (B.B ⧸ maximalIdeal B.B ^ (N + 1)) :=
    co_quot c.O B.B _ (Ideal.Quotient.mkₐ c.O (maximalIdeal B.B ^ (N + 1))) (Ideal.Quotient.mkₐ_surjective c.O (maximalIdeal B.B ^ (N + 1)))
  let e : MonoidAlgebra B.B Q →ₐ[B.B] B.B ⧸ maximalIdeal B.B ^ (N + 1) :=
    MonoidAlgebra.lift B.B (B.B ⧸ maximalIdeal B.B ^ (N + 1)) Q ((Units.coeHom _).comp j)
  have h1 := htw.comp (e : MonoidAlgebra B.B Q →+* B.B ⧸ maximalIdeal B.B ^ (N + 1))
  have h2 := hτ.comp (Ideal.Quotient.mk (maximalIdeal B.B ^ (N + 1)))
  have e1 : (e : MonoidAlgebra B.B Q →+* B.B ⧸ maximalIdeal B.B ^ (N + 1)).comp
      (IsScalarTower.toAlgHom c.O B.B (MonoidAlgebra B.B Q) : B.B →+* MonoidAlgebra B.B Q) =
      (Ideal.Quotient.mk (maximalIdeal B.B ^ (N + 1))).comp (RingHom.id B.B) := RingHom.ext fun x => e.commutes x
  have e2 : pushCh (e : MonoidAlgebra B.B Q →+* B.B ⧸ maximalIdeal B.B ^ (N + 1)) ((MonoidAlgebra.of B.B Q).toHomUnits.comp q) =
      pushCh (Ideal.Quotient.mk (maximalIdeal B.B ^ (N + 1))) γ := by
    rw [← hj]
    ext g
    exact MonoidAlgebra.lift_of (R := B.B) ((Units.coeHom _).comp j) (q g)
  rw [e1, e2] at h1
  have h3 := twMapUniq B _ _ ((e.restrictScalars c.O).comp tw) ((Ideal.Quotient.mkₐ c.O (maximalIdeal B.B ^ (N + 1))).comp τ) h1 h2
  have h4 : e (tw b) = Ideal.Quotient.mk (maximalIdeal B.B ^ (N + 1)) (τ b) := DFunLike.congr_fun h3 b
  have h5 := lift_mem ((Units.coeHom _).comp j) J (tw b) hJ
  rw [← Ideal.mem_quotient_iff_mem_sup, ← h4]
  exact h5
