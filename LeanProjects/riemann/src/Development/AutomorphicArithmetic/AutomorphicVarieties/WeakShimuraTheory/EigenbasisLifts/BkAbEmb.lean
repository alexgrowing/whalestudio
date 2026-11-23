import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.BkAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

open scoped Pointwise in
private theorem bkAb_emb {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] (A : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω) (hA : ∀ w, IsPlaceOver (A w) w)
    (τ : F →+* Formalism.BasicNotions.Loc.Om l) :
    ∃ (j : Ω →+* Formalism.BasicNotions.Loc.Om l) (w : HeightOneSpectrum (𝓞 F)), j.comp (algebraMap F Ω) = τ ∧
      ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ Loc.placeJ j = A w := by
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  obtain ⟨j₀, hj₀⟩ : ∃ j : Ω →+* Formalism.BasicNotions.Loc.Om l, j.comp (algebraMap F Ω) = τ := by
    letI : Algebra F (Formalism.BasicNotions.Loc.Om l) := τ.toAlgebra
    exact ⟨(IsAlgClosed.lift (R := F) (S := Ω) (M := Formalism.BasicNotions.Loc.Om l)).toRingHom,
      (IsAlgClosed.lift (R := F) (S := Ω) (M := Formalism.BasicNotions.Loc.Om l)).comp_algebraMap⟩
  obtain ⟨w, hw, hl⟩ := ((Loc.decEmb (F := F) (Ω := Ω) (v := l)).2 j₀).1
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := F) (hA w) hw
  refine ⟨j₀.comp (g : Ω →+* Ω), w, hj₀ ▸ RingHom.ext fun x => congrArg j₀ (g.commutes x), hl, ?_⟩
  ext x
  change g • x ∈ Loc.placeJ j₀ ↔ _
  rw [← hg]
  exact ValuationSubring.smul_mem_pointwise_smul_iff

theorem UpperTheory.V.Ws.Eb.bkAb :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) {n : ℕ} (R : Representation (PadicAlgCl l) V.frame.Γ (Matrix (Fin n) (Fin n) (PadicAlgCl l))), ∀ z ∈ Z1 R,
        (∀ (v : V.frame.Vl) (φ : V.frame.Gv v →* Formalism.BasicNotions.Loc.GQ l), Topology.IsOpenEmbedding φ → (∀ g, φ g ∈ Loc.Iq l ↔ g ∈ V.frame.Iv v) → (∀ g, Loc.cycA l l (PadicAlgCl l) (φ g) = cycBar L Ω l (Subtype.val g)) →
          (fun g : V.frame.Gv v => z (V.frame.φ v g)) ∈ Loc.finiteCocycles φ (R.comp (V.frame.η.ker.subtype.comp (V.frame.φ v)) : Representation (PadicAlgCl l) (V.frame.Gv v) (Matrix (Fin n) (Fin n) (PadicAlgCl l)))) →
        (∀ w : HeightOneSpectrum (𝓞 (W.Lp L)), ((l : ℕ) : 𝓞 (W.Lp L)) ∉ w.asIdeal → ∃ X, ∀ g ∈ Ine (F := W.Lp L) (s.A w), z (toGS Ω V.S' g) = R (toGS Ω V.S' g) X - X) →
        Af.IsBK l (R.comp (toGS Ω V.S') : Representation (PadicAlgCl l) (G (W.Lp L) Ω) (Matrix (Fin n) (Fin n) (PadicAlgCl l))) (fun g => z (toGS Ω V.S' g)) := by
  intro l _ L Ω _ _ _ _ _ _ s V n R z hz h1 h2
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  refine ⟨fun w hw => ⟨s.A w, s.hA w, h2 w hw⟩, fun τ => ?_⟩
  obtain ⟨j, w, hj, hl, hA⟩ := bkAb_emb s.A s.hA τ
  refine ⟨j, hj, ?_⟩
  have key : ∃ φ : ↥(Dec (F := L) (s.A w)) →* Formalism.BasicNotions.Loc.GQ l, Topology.IsOpenEmbedding φ ∧
      (∀ g y, φ g (j y) = j ((g : G L Ω) y)) ∧ (∀ g, φ g ∈ Loc.Iq l ↔ (g : G L Ω) ∈ Ine (F := L) (s.A w)) ∧
      (∀ g, Loc.cyc l l (φ g) = cycZ L Ω l (g : G L Ω)) := by
    rw [← hA]
    obtain ⟨φ, a, b, -, c, d, -⟩ := ((Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j).2
    exact ⟨φ, a, b, c, d l⟩
  obtain ⟨φ, a, b, c, d⟩ := key
  have h3 := h1 ⟨w, hl⟩ φ a c fun g => congrArg (Units.map _) (d g)
  exact (Loc.bkAbove (F := W.Lp L) j φ ((W.resP L Ω).comp (Dec (F := L) (s.A w)).subtype) a b
    (R.comp (toGS Ω V.S')) (fun g => z (toGS Ω V.S' g))
    ⟨hz.1.comp (continuous_toGS Ω _), fun g h => (congrArg z (map_mul _ g h)).trans (hz.2 _ _)⟩).1 h3
