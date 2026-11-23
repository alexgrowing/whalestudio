import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem u_eq_of_marked {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    {Λ : Type} {F : Fam ℂ O Λ g} {N : ℕ} {Cl : ∀ D' : PLat O bar, (Λ → D'.La) → Prop}
    (U : Unif F (RingHom.id ℂ) ρ N Cl) (i i' : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ))
    (P' : (U.Di i').La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ρ P) (hP' : IsPeriod (U.Di i') ρ P')
    (w : (U.Di i').La ≃ₗ[O] (U.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hw : IsMarkedIsom N (U.Di i') (U.Di i) (U.t i') (U.t i) w) (hh : ∀ u, P (w u) = h (P' u)) :
    U.u i' P' = U.u i P := by
  obtain rfl := U.distinct i' i w hw
  exact (U.fibre i' P' P hP' hP).2 ⟨w, h, hw, hh⟩

private theorem marked_of_u_eq {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    {Λ : Type} {F : Fam ℂ O Λ g} {N : ℕ} {Cl : ∀ D' : PLat O bar, (Λ → D'.La) → Prop}
    (U : Unif F (RingHom.id ℂ) ρ N Cl) (i i' : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ))
    (P' : (U.Di i').La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ρ P) (hP' : IsPeriod (U.Di i') ρ P')
    (e : U.u i' P' = U.u i P) :
    ∃ (w : (U.Di i').La ≃ₗ[O] (U.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      IsMarkedIsom N (U.Di i') (U.Di i) (U.t i') (U.t i) w ∧ ∀ u, P (w u) = h (P' u) := by
  obtain rfl := U.disj i' i P' P hP' hP e
  exact (U.fibre i' P' P hP' hP).1 e

private theorem isPeriod_comp {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    {D' D'' : PLat O bar} {P : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D' ρ P) (w : D''.La ≃ₗ[O] D'.La)
    (hw : IsIsom D'' D' w) : IsPeriod D'' ρ (P.comp w.toLinearMap.toAddMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, Hm, hH, hpos, hEF⟩ := hP
  have hs : Set.range (P.comp w.toLinearMap.toAddMonoidHom) = Set.range P := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨w x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨w.symm x, by simp⟩
  have hr : (P.comp w.toLinearMap.toAddMonoidHom).range = P.range := by
    ext z
    exact Set.ext_iff.1 hs z
  refine ⟨fun a x => ?_, h2.comp w.injective, ?_, ?_, Hm, hH, hpos, fun x y => ?_⟩
  · show P (w (a • x)) = _
    rw [map_smul, h1]
    rfl
  · rw [hr]
    exact h3
  · rw [hs]
    exact h4
  · show (hermForm Hm (P (w x)) (P (w y))).im = _
    rw [hEF, hw x y]

private theorem marked_symm {O : Type} [Ring O] {bar : O → O} {Λ : Type} {N : ℕ} {D₁ D₂ : PLat O bar}
    {t₁ : Λ → D₁.La} {t₂ : Λ → D₂.La} {w : D₁.La ≃ₗ[O] D₂.La} (h : IsMarkedIsom N D₁ D₂ t₁ t₂ w) :
    IsMarkedIsom N D₂ D₁ t₂ t₁ w.symm := by
  refine ⟨fun x y => ?_, fun a => ?_⟩
  · have := h.1 (w.symm x) (w.symm y)
    simpa using this.symm
  · obtain ⟨e, he⟩ := h.2 a
    refine ⟨-(w.symm e), ?_⟩
    have h2 := congrArg w.symm he
    rw [LinearEquiv.symm_apply_apply, map_add, map_nsmul] at h2
    rw [h2, smul_neg]
    abel

theorem UpperTheory.Gal.W2.unifG_of :
    UpperTheory.Gal.W2.CoordEx → UpperTheory.Gal.W2.CoordOcc → UpperTheory.Gal.W2.CoordIso → UpperTheory.Gal.W2.CoordMove → UpperTheory.Gal.W2.UnifG := by
  intro hEx hOcc hIso hMove p _ D G L hDa hDm v hv t₀ ht₀ ρ hρ PD RD N hN hNp F U
  have hch : ∀ x : CxPts F.s (RingHom.id ℂ), ∃ (i : Fin U.n) (P : (U.Di i).La →+ (Fin D.g → ℂ))
      (q : GlobalTheory.LKCx.FCls G) (a : GlobalTheory.LKCx.Dat G v (Quot.out q).β) (j : (U.Di i).La →+ VQ D),
      IsPeriod (U.Di i) ρ P ∧ x.1 = U.u i P ∧ IsCoord L (Quot.out q) (PD _) (RD _) N (U.Di i) (U.t i) P j a := by
    intro x
    obtain ⟨i, P, hP, hu⟩ := U.onto x.1 x.2
    obtain ⟨q, a, j, hc⟩ := hEx p D G L hDa hDm v hv t₀ ht₀ ρ hρ PD RD N hN hNp (U.Di i) (U.t i) P (U.mem i) hP
    exact ⟨i, P, q, a, j, hP, hu.symm, hc⟩
  choose i P q a j hP hu hc using hch
  let Φ₀ : CxPts F.s (RingHom.id ℂ) → GlobalTheory.LKCx.AllPts G v (L.KN N) (KHT p G.m G.n 1 G.Fw) :=
    fun x => ⟨q x, Quot.mk _ (a x)⟩
  have hinj : Function.Injective Φ₀ := by
    intro x x' e
    obtain ⟨w, h, hw, hh⟩ := (hIso p D G L v t₀ ρ PD RD N hN hNp (U.Di (i x)) (U.t (i x)) (P x)
      (U.Di (i x')) (U.t (i x')) (P x') (U.mem _) (U.mem _) (q x) (q x') (a x) (a x') (j x) (j x')
      (hc x) (hc x')).2 e
    apply Subtype.ext
    rw [hu x, hu x']
    exact (u_eq_of_marked U _ _ _ _ (hP x) (hP x') w h hw hh).symm
  have hsurj : Function.Surjective Φ₀ := by
    rintro ⟨q₀, c⟩
    obtain ⟨a₀, rfl⟩ := Quot.exists_rep c
    obtain ⟨D', t, Pd, jd, hCl, hPd, hcd⟩ :=
      hOcc p D G L hDa hDm v hv t₀ ht₀ ρ hρ PD RD N hN hNp (Quot.out q₀) a₀
    obtain ⟨i₀, w, hw⟩ := U.all D' t hCl ⟨Pd, hPd⟩
    have hws := marked_symm hw
    let P₀ := Pd.comp w.symm.toLinearMap.toAddMonoidHom
    have hP₀ : IsPeriod (U.Di i₀) ρ P₀ := isPeriod_comp hPd w.symm hws.1
    let j₀ := jd.comp w.symm.toLinearMap.toAddMonoidHom
    have hc₀ : IsCoord L (Quot.out q₀) (PD _) (RD _) N (U.Di i₀) (U.t i₀) P₀ j₀ a₀ :=
      hMove p D G L v t₀ ρ (Quot.out q₀) (PD _) (RD _) N D' t Pd (U.Di i₀) (U.t i₀) P₀ w.symm hws
        (fun _ => rfl) jd j₀ (fun _ => rfl) a₀ hcd
    let x : CxPts F.s (RingHom.id ℂ) := ⟨U.u i₀ P₀, (U.unif i₀ P₀ hP₀).1⟩
    refine ⟨x, ?_⟩
    obtain ⟨w', h', hw', hh'⟩ := marked_of_u_eq U i₀ (i x) P₀ (P x) hP₀ (hP x) (hu x).symm
    exact ((hIso p D G L v t₀ ρ PD RD N hN hNp (U.Di i₀) (U.t i₀) P₀ (U.Di (i x)) (U.t (i x)) (P x)
      (U.mem _) (U.mem _) q₀ (q x) a₀ (a x) j₀ (j x) hc₀ (hc x)).1 ⟨w', h', hw', hh'⟩).symm
  exact ⟨Equiv.ofBijective Φ₀ ⟨hinj, hsurj⟩, fun x => ⟨q x, a x, i x, P x, j x, rfl, hP x, hu x, hc x⟩⟩
