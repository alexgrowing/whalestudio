import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem isDvr_coef {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l) (h : 𝔞.IsZero e) (c : Coef l) :
    𝔞.IsDvr (𝔞.a c) := by
  haveI : CharZero c.O := charZero_of_injective_algebraMap (dvrFacts l c.O).1
  refine ⟨fun x y hxy => Subtype.ext ?_, 𝔞.loc c, inferInstance, (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1, fun x => ?_⟩
  · rw [← h.1 c x, ← h.1 c y, hxy]
  · have h1 : IsAlgebraic ℚ_[l] (e x) := Algebra.IsAlgebraic.isAlgebraic _
    have h2 : IsAlgebraic ℤ_[l] (e x) := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] _).2 h1
    have h3 : IsAlgebraic c.O (e x) := h2.extendScalars (dvrFacts l c.O).1
    obtain ⟨p, hp, hx⟩ := h3
    refine ⟨p, hp, e.injective ?_⟩
    have h4 : (e : 𝔞.K →+* PadicAlgCl l).comp (𝔞.toK.comp (𝔞.a c)) = algebraMap c.O (PadicAlgCl l) :=
      RingHom.ext fun z => h.1 c z
    have h5 := hom_eval₂ p (𝔞.toK.comp (𝔞.a c)) (e : 𝔞.K →+* PadicAlgCl l) x
    rw [h4] at h5
    rw [map_zero]
    exact h5.trans hx

theorem UpperTheory.V.Ws.eptV :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r, D.EPt r → ∃ r', VPt D 𝔞 r' ∧ mapRep ((e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK) r' = r := by
  intro Ω _ _ _ l _ c D _ 𝔞 e h r hr
  obtain ⟨R, _, _, _, ρ, y, hρ, rfl⟩ := hr
  obtain ⟨⟨c', hc', hy'⟩, a, ha1, -, hy⟩ := (coPt c R).1 y
  let y' : R →+* c'.O := (y : R →+* PadicAlgCl l).codRestrict c'.O hy'
  have hn : ∀ z : c'.O, ‖(z : PadicAlgCl l)‖ ≤ 1 := fun z => by
    rw [← h.1 c' z]
    exact (h.2 _).1 (𝔞.a c' z).2
  have hm : ∀ x ∈ maximalIdeal R, y' x ∈ maximalIdeal c'.O := by
    intro x hx hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h1 : y x * (w : PadicAlgCl l) = 1 := congrArg Subtype.val hw
    have h2 : ‖y x‖ ≤ a := by simpa using hy 1 x (by rwa [pow_one])
    have h3 := congrArg norm h1
    rw [norm_mul, norm_one] at h3
    have h4 := mul_le_of_le_one_right (norm_nonneg (y x)) (hn w)
    linarith
  refine ⟨mapRep ((𝔞.a c').comp y') ρ.hom, ⟨⟨c'.O, inferInstance, inferInstance, inferInstance, 𝔞.a c',
    ⟨mapRep y' ρ.hom, fun _ => 1⟩, isDvr_coef 𝔞 e h c', fun i j N => ?_, ?_⟩,
    R, _, _, _, ρ, (𝔞.a c').comp y', hρ, RingHom.ext fun x => ?_, fun x hx => ?_, rfl⟩, ?_⟩
  · have hle : maximalIdeal R ^ N ≤ (maximalIdeal c'.O ^ N).comap y' :=
      le_trans (Ideal.pow_right_mono hm N) (Ideal.le_comap_pow _ N)
    exact (ρ.cont i j N).comp (Ideal.quotientMap _ y' hle)
  · refine PD.ext rfl (funext fun _ => ?_)
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · rw [← 𝔞.compat c c' hc' x]
    exact congrArg (𝔞.a c') (Subtype.ext (y.commutes x))
  · exact map_nonunit (𝔞.a c') _ (hm x hx)
  · ext g i j
    exact h.1 c' (y' (ρ.hom g i j))
