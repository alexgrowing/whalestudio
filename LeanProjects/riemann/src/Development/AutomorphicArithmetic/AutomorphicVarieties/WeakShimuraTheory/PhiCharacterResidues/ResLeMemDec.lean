import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiMu

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem adic_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun x => f x * g x := by
  intro N
  convert (hf N).mul (hg N) using 1
  funext x
  exact map_mul _ _ _

private theorem adic_pow {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f : Γ → R}
    (hf : AdicCont I f) (n : ℕ) : AdicCont I fun x => f x ^ n := by
  induction n with
  | zero =>
    intro N
    simp only [pow_zero, map_one]
    exact IsLocallyConstant.const _
  | succ k ih =>
    simp only [pow_succ]
    exact adic_mul ih hf

private theorem adic_alg {Γ O R : Type} [TopologicalSpace Γ] [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    [IsCO O R] {f : Γ → O} (hf : AdicCont (maximalIdeal O) f) :
    AdicCont (maximalIdeal R) fun x => algebraMap O R (f x) := by
  have hloc : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  intro N
  have hN : (maximalIdeal O) ^ N ≤ Ideal.comap (algebraMap O R) ((maximalIdeal R) ^ N) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    refine Ideal.pow_right_mono ?_ N
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact map_nonunit (algebraMap O R) a ha
  have := (hf N).comp (Ideal.Quotient.lift ((maximalIdeal O) ^ N)
    ((Ideal.Quotient.mk ((maximalIdeal R) ^ N)).comp (algebraMap O R))
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hN ha)))
  convert this using 1
  funext x
  simp

private theorem resLe_mem_Dec {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {F L : IntermediateField ℚ Ω}
    (h : F ≤ L) {A A' : ValuationSubring Ω} (e : A = A') (g : Dec (F := L) A) : resLe h g ∈ Dec (F := F) A' := by
  subst e
  exact g.2

theorem UpperTheory.V.Ws.phiIsPsi :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ (ψ : ∀ v : W.Vl l T.L, Fin 4 → Dec (F := T.L) (K.s.A v) →* X.Bˣ), K.IsPsiT X n ψ → ∀ v i, K.r.IsPsi v i (ψ v i) := by
  intro Ω _ _ _ l _ c D T c' h K X n ψ hψ v i
  change W.Vl l T.L at v
  have hmem : ∀ g : Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))),
      resLe T.F_le (g : G T.L Ω) ∈ (T.fr ∅).Gv (K.e v) :=
    fun g => resLe_mem_Dec T.F_le (K.hA v) g
  refine ⟨?_, ?_, ?_⟩
  · have hsc : AdicCont (maximalIdeal X.B)
        fun g : Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))) => algebraMap c'.O X.B (K.sc n g) := by
      have h0 : AdicCont (maximalIdeal c'.O) fun g : G T.L Ω => K.sc n g :=
        adic_mul K.κ_cont (adic_pow K.β_cont n)
      have h1 : AdicCont (maximalIdeal c'.O)
          fun g : Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))) => K.sc n g :=
        fun N => (h0 N).comp_continuous continuous_subtype_val
      exact adic_alg h1
    have hX : AdicCont (maximalIdeal X.B)
        fun g : Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))) => X.ψ (K.e v) i (resLe T.F_le g) := by
      intro N
      have hc : Continuous fun g : Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))) =>
          (⟨resLe T.F_le g, hmem g⟩ : (T.fr ∅).Gv (K.e v)) :=
        ((continuous_resLe T.F_le).comp continuous_subtype_val).subtype_mk hmem
      exact (X.ψ_cont (K.e v) i N).comp_continuous hc
    show AdicCont (maximalIdeal X.B)
      fun g : Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))) => ((ψ v i g : X.Bˣ) : X.B)
    convert adic_mul hsc hX using 1
    funext g
    exact hψ v i g
  · intro g
    change Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))) at g
    show (res c'.O X.B) ((ψ v i g : X.Bˣ) : X.B) = ((K.r.psib v i g : _) : ResidueField c'.O)
    rw [hψ v i g, K.psib, K.chib, map_mul, AlgHom.commutes, X.ψ_red (K.e v) i _ (hmem g)]
    simp only [Link.sc, IsLocalRing.ResidueField.algebraMap_eq, map_mul, map_pow, K.β_red, one_pow,
      mul_one]
    rfl
  · intro g
    obtain ⟨hκ, ht⟩ := K.mu v g.1 g.2
    have hβ : K.β g.1.1 = 1 := MonoidHom.mem_ker.mp (K.β_t (MonoidHom.mem_ker.mpr ht))
    have hmu : resLe T.F_le g.1.1 ∈ (T.fr ∅).Mu (K.e v) :=
      phiMu ((resLe T.F_le).comp (Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L)))).subtype)
        ((continuous_resLe T.F_le).comp continuous_subtype_val)
        (Dec (F := T.F) (T.pl (K.e v))) hmem g.1 g.2
    have hψ1 : X.ψ (K.e v) i (resLe T.F_le g.1.1) = 1 := by
      apply X.inj
      rw [X.ψ_map _ _ _ (hmem g.1), map_one]
      exact X.pair.mu (K.e v) _ hmu i
    have hsc1 : K.sc n g.1.1 = 1 := by
      simp [Link.sc, hκ, hβ]
    have hth : ((K.r.th v i g : c'.Oˣ) : c'.O) = 1 := by
      have := congrArg (fun f => ((f g : c'.Oˣ) : c'.O)) (K.th v i)
      simpa using this
    show ((ψ v i g.1 : X.Bˣ) : X.B) = algebraMap c'.O X.B ((K.r.th v i g : c'.Oˣ) : c'.O)
    refine Eq.trans ?_ (congrArg (algebraMap c'.O X.B) hth).symm
    rw [map_one, hψ v i g.1, hsc1, hψ1, map_one, mul_one]
