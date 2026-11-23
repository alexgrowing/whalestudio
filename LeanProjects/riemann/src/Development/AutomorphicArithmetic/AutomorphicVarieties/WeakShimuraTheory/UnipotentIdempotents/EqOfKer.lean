import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.PlusEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.PlacesEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.GExRtZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.RangeOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.EqOfMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.CcOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.BarFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private noncomputable def bu {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (L : IntermediateField ℚ Ω) (γ : G ℚ Ω →* c.Oˣ) : G L Ω →* (ResidueField c.O)ˣ :=
  ((Units.map (residue c.O).toMonoidHom).comp γ).comp (resQ L)

private theorem bu_val {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (L : IntermediateField ℚ Ω) (γ : G ℚ Ω →* c.Oˣ) (g : G L Ω) :
    (bu L γ g : ResidueField c.O) = Raw.bar γ (resQ L g) := rfl

private theorem bu_open {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (L : IntermediateField ℚ Ω) [NumberField L] (γ : G ℚ Ω →* c.Oˣ) (h : IsOpen {g : G ℚ Ω | Raw.bar γ g = 1}) :
    IsOpen ((bu L γ).ker : Set (G L Ω)) := by
  have hk : ((bu L γ).ker : Set (G L Ω)) = resQ L ⁻¹' {g | Raw.bar γ g = 1} := by
    ext g
    simp [MonoidHom.mem_ker, Units.ext_iff, bu_val]
  rw [hk]
  exact h.preimage (Af.continuous_restrictScalarsHom ℚ L Ω)

private theorem eq_of_ker {Γ Δ : Type} [Group Γ] [Group Δ] {f : Γ →* Δ} {a b : Γ} (h : a⁻¹ * b ∈ f.ker) : f a = f b := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h
  exact h

private theorem dec_of {Ω F F' : Type} [Field Ω] [Field F] [Field F'] [NumberField F] [NumberField F'] [Algebra F Ω] [Algebra F' Ω] {A : ValuationSubring Ω}
    {σ : G F Ω} {τ : G F' Ω} (h : ∀ x, τ x = σ x) (hσ : σ ∈ Dec (F := F) A) : τ ∈ Dec (F := F') A := by
  have h2 := apply_mem_iff_of_mem_Dec hσ
  rw [mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← h2 (τ⁻¹ x), ← h]
  simp

theorem UpperTheory.V.Ws.Lk.setEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D), D.Good → T.Ok → Nonempty (SetD T) := by
  intro Ω _ _ _ l _ c D T hG hT
  classical
  obtain ⟨hps, hom, -⟩ := barFacts hG
  obtain ⟨g0, hg0eq, hg0om⟩ := gEx T hT
  let U : Subgroup (G T.L Ω) := (bu T.L (D.ps 0)).ker ⊓ (bu T.L (D.ps 1)).ker ⊓
    (bu T.L (D.ps 2)).ker ⊓ (bu T.L (D.ps 3)).ker ⊓ (bu T.L D.om).ker
  have hU : IsOpen (U : Set (G T.L Ω)) := by
    simp only [U, Subgroup.coe_inf]
    exact ((((bu_open _ _ (hps 0)).inter (bu_open _ _ (hps 1))).inter (bu_open _ _ (hps 2))).inter
      (bu_open _ _ (hps 3))).inter (bu_open _ _ hom)
  have hM0 : 2 * (∏ q ∈ D.S, q) * (NumberField.discr T.L).natAbs ≠ 0 := by
    have h1 : (∏ q ∈ D.S, q) ≠ 0 := Finset.prod_ne_zero_iff.2 fun q hq => (hG.S_prime q hq).ne_zero
    have h2 : (NumberField.discr T.L).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)
    exact mul_ne_zero (mul_ne_zero two_ne_zero h1) h2
  obtain ⟨v, B, p, hp, hpM, hpv, hnorm, hB, hBdec, hBpow, hBone⟩ := v0Ex T.L Ω U hU g0 _ hM0
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpM (dvd_mul_of_dvd_left (dvd_mul_right 2 _) _)
  have hpS : p ∉ D.S := fun h =>
    hpM (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ h) 2) _)
  have hpd : ¬ (p : ℤ) ∣ NumberField.discr T.L := by
    intro h
    apply hpM
    apply dvd_mul_of_dvd_right
    simpa using Int.natAbs_dvd_natAbs.mpr h
  obtain ⟨e, he⟩ := placesEq T
  obtain ⟨-, ⟨φ, hφ, hφL⟩, -⟩ := galEq T
  have hIne : ∀ A : ValuationSubring Ω, Ine (F := W.Lp T.L) A ≤ (W.resP T.L Ω).range := by
    intro A σ hσ
    apply (hφL σ).1
    apply hT.unr A
    exact ⟨dec_of (hφ σ) hσ.1, fun x hx => by rw [hφ]; exact hσ.2 x hx⟩
  have hSdec : ∀ q ∈ D.S, ∀ A : ValuationSubring Ω, A.valuation q < 1 →
      Dec (F := W.Lp T.L) A ≤ (W.resP T.L Ω).range := by
    intro q hq A hA σ hσ
    apply (hφL σ).1
    show resQ T.F (φ σ) ∈ T.K.fixingSubgroup
    apply hT.split q hq A hA
    exact dec_of (fun x => by simp [resQ, hφ]) hσ
  obtain ⟨s, hsA, hs0, hsfin, hsB, hsaway⟩ := mkSet l T.L Ω hG.l_odd hIne D.S hG.S_prime hG.l_mem hSdec
    (fun v => T.pl (e v)) he v B p hp hp2 hpS hpd hpv hnorm hB hBdec
  refine ⟨SetD.mk s e hsA hsfin hsaway ?_ ?_ ?_ (ccOf T s)⟩
  · rw [hs0]
    exact hsB
  · intro g hg i j
    rw [hs0] at hg
    obtain ⟨n, hn⟩ := hBpow g hg
    simp only [U, Subgroup.mem_inf] at hn
    obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, -⟩ := hn
    have key : ∀ k, bu T.L (D.ps k) g = bu T.L (D.ps k) (g0 ^ n) := by
      intro k
      fin_cases k
      exacts [eq_of_ker h0, eq_of_ker h1, eq_of_ker h2, eq_of_ker h3]
    have hg0' : bu T.L (chi D T.pr i) g0 = bu T.L (chi D T.pr j) g0 :=
      Units.ext (by rw [bu_val, bu_val]; exact hg0eq i j)
    rw [← bu_val, ← bu_val]
    change ((bu T.L (D.ps (lab T.pr i)) g : ResidueField c.O)) = (bu T.L (D.ps (lab T.pr j)) g : ResidueField c.O)
    rw [key, key]
    congr 1
    simp only [map_pow, map_zpow]
    exact congrArg (· ^ n) hg0'
  · obtain ⟨d, hd, hdU⟩ := hBone
    refine ⟨d, by rw [hs0]; exact hd, ?_⟩
    have h4 : d⁻¹ * g0 ∈ (bu T.L D.om).ker := (Subgroup.mem_inf.1 hdU).2
    rw [← bu_val, eq_of_ker h4, bu_val]
    exact hg0om
