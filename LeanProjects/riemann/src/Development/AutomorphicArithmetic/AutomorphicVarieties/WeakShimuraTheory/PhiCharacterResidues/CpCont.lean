import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CharpolySmulUnit

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem ac_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s * g s := by
  intro N
  have e : (fun s => Ideal.Quotient.mk (I ^ N) (f s * g s)) =
      fun s => Ideal.Quotient.mk (I ^ N) (f s) * Ideal.Quotient.mk (I ^ N) (g s) := by
    funext s
    exact map_mul _ _ _
  rw [e]
  exact (hf N).comp₂ (hg N) (· * ·)

private theorem ac_pow {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f : Γ → R}
    (hf : AdicCont I f) (k : ℕ) : AdicCont I fun s => f s ^ k := by
  intro N
  have e : (fun s => Ideal.Quotient.mk (I ^ N) (f s ^ k)) =
      (fun x => x ^ k) ∘ fun s => Ideal.Quotient.mk (I ^ N) (f s) := by
    funext s
    exact map_pow _ _ _
  rw [e]
  exact (hf N).comp _

private theorem ac_alg {Γ O R : Type} [TopologicalSpace Γ] [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    {f : Γ → O} (hf : AdicCont (maximalIdeal O) f) : AdicCont (maximalIdeal R) fun s => algebraMap O R (f s) := by
  haveI : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  have hm : maximalIdeal O ≤ (maximalIdeal R).comap (algebraMap O R) := by
    intro x hx
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact ((mem_maximalIdeal _).mp hx) (isUnit_of_map_unit _ _ hu)
  intro N
  have hN : maximalIdeal O ^ N ≤ (maximalIdeal R ^ N).comap (algebraMap O R) :=
    (Ideal.pow_right_mono hm N).trans (Ideal.le_comap_pow _ N)
  have e : (fun s => Ideal.Quotient.mk (maximalIdeal R ^ N) (algebraMap O R (f s))) =
      (Ideal.quotientMap (maximalIdeal R ^ N) (algebraMap O R) hN) ∘
        fun s => Ideal.Quotient.mk (maximalIdeal O ^ N) (f s) := by
    funext s
    simp [Ideal.quotientMap_mk]
  rw [e]
  exact (hf N).comp _

theorem UpperTheory.V.Ws.phiCpCont :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ j, AdicCont (maximalIdeal X.B) fun g => (K.cpT X n g).coeff j := by
  intro Ω _ _ _ l _ c D T c' h K X n j
  have e : (fun g => (K.cpT X n g).coeff j) = fun g =>
      (X.cp (resLe T.F_le g)).coeff j *
        (algebraMap c'.O X.B ((K.κ g : c'.O)) * algebraMap c'.O X.B ((K.β g : c'.O)) ^ n) ^ (4 - j) := by
    funext g
    unfold Link.cpT
    rw [Polynomial.coeff_scaleRoots, (phiCpMap K X n g).2.1]
    simp [Link.sc, map_mul, map_pow]
  rw [e]
  have hcp : AdicCont (maximalIdeal X.B) fun g => (X.cp (resLe T.F_le g)).coeff j := by
    intro N
    exact (X.cp_cont j N).comp_continuous (continuous_resLe T.F_le)
  exact ac_mul hcp (ac_pow (ac_mul (ac_alg K.κ_cont) (ac_pow (ac_alg K.β_cont) n)) _)
