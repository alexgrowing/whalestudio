import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.SepIffInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OneVar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.ExistsPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
open IsLocalRing UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite UpperTheory.V.HV UpperTheory.V.Alg

private theorem algHom_mvPowerSeries_C_eq_algebraMap {A K : Type} [CommRing A] [CommRing K] [Algebra A K] {σ : Type}
    (y : MvPowerSeries σ A →ₐ[A] K) (a : A) : y (MvPowerSeries.C a) = algebraMap A K a := by
  have h := y.commutes a
  simpa [MvPowerSeries.algebraMap_apply] using h

private theorem exists_injective_mvPowerSeries_last_to_powerSeries (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (D : ℕ) :
    ∃ S : MvPowerSeries (Fin (D + 1)) R →+* PowerSeries (MvPowerSeries (Fin D) R),
      Function.Injective S ∧
      (∀ a : R, S (MvPowerSeries.C a) = PowerSeries.C (MvPowerSeries.C a)) ∧
      S (MvPowerSeries.X (Fin.last D)) = PowerSeries.X ∧
      ∀ i : Fin D, S (MvPowerSeries.X i.castSucc) = PowerSeries.C (MvPowerSeries.X i) := by
  haveI hA : UpperTheory.V.Alg.IsCO R (MvPowerSeries (Fin D) R) := UpperTheory.V.Alg.co_mvps R R (Fin D)
  haveI hB : UpperTheory.V.Alg.IsCO R (MvPowerSeries (Fin (D + 1)) R) :=
    UpperTheory.V.Alg.co_mvps R R (Fin (D + 1))
  haveI hP : UpperTheory.V.Alg.IsCO R (MvPowerSeries Unit (MvPowerSeries (Fin D) R)) :=
    UpperTheory.V.Alg.co_mvps R (MvPowerSeries (Fin D) R) Unit
  have nX : ∀ (τ : Type) (s : τ), MvPowerSeries.X s ∈
      IsLocalRing.maximalIdeal (MvPowerSeries τ R) := by
    intro τ s
    rw [IsLocalRing.mem_maximalIdeal]
    intro h
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X] at h
    exact not_isUnit_zero h
  have nX' : (MvPowerSeries.X () : MvPowerSeries Unit (MvPowerSeries (Fin D) R)) ∈
      IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro h
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X] at h
    exact not_isUnit_zero h
  have hmem : ∀ s : Fin (D + 1), (Fin.lastCases (MvPowerSeries.X ())
      (fun i => MvPowerSeries.C (MvPowerSeries.X i)) s :
        MvPowerSeries Unit (MvPowerSeries (Fin D) R)) ∈ IsLocalRing.maximalIdeal _ := by
    intro s
    refine Fin.lastCases ?_ (fun i => ?_) s
    · rw [Fin.lastCases_last]
      exact nX'
    · rw [Fin.lastCases_castSucc, IsLocalRing.mem_maximalIdeal]
      intro h
      rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_C] at h
      exact (IsLocalRing.mem_maximalIdeal _).1 (nX (Fin D) i) h
  obtain ⟨S, ⟨hSC, hSX⟩, -⟩ := UpperTheory.V.Alg.co_ev R R (MvPowerSeries Unit (MvPowerSeries (Fin D) R))
    (Fin (D + 1)) (Algebra.ofId R _) _ hmem
  obtain ⟨ι, ⟨hιC, hιX⟩, -⟩ := UpperTheory.V.Alg.co_ev R R (MvPowerSeries (Fin (D + 1)) R) (Fin D)
    (Algebra.ofId R _) (fun i => MvPowerSeries.X i.castSucc) (fun i => nX _ _)
  obtain ⟨T, ⟨hTC, hTX⟩, -⟩ := UpperTheory.V.Alg.co_ev R (MvPowerSeries (Fin D) R)
    (MvPowerSeries (Fin (D + 1)) R) Unit ι (fun _ => MvPowerSeries.X (Fin.last D)) (fun _ => nX _ _)
  obtain ⟨F, -, hF⟩ := UpperTheory.V.Alg.co_ev R R (MvPowerSeries (Fin (D + 1)) R) (Fin (D + 1))
    (Algebra.ofId R _) MvPowerSeries.X (fun s => nX _ s)
  have hTS : T.comp S = AlgHom.id R _ := by
    have e1 := hF (T.comp S) ⟨fun x => ?_, fun s => ?_⟩
    · have e2 := hF (AlgHom.id R _) ⟨fun x => ?_, fun s => rfl⟩
      · rw [e1, e2]
      · simp [Algebra.ofId_apply, MvPowerSeries.algebraMap_apply]
    · rw [AlgHom.comp_apply, hSC, Algebra.ofId_apply, AlgHom.commutes, Algebra.ofId_apply]
    · refine Fin.lastCases ?_ (fun i => ?_) s
      · rw [AlgHom.comp_apply, hSX, Fin.lastCases_last, hTX]
      · rw [AlgHom.comp_apply, hSX, Fin.lastCases_castSucc, hTC, hιX]
  refine ⟨S.toRingHom, fun x y h => ?_, fun a => ?_, ?_, fun i => ?_⟩
  · have h' : T (S x) = T (S y) := congrArg T h
    simpa [← AlgHom.comp_apply, hTS] using h'
  · have := hSC a
    simp only [Algebra.ofId_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply] at this
    exact this
  · exact (hSX (Fin.last D)).trans (by rw [Fin.lastCases_last]; rfl)
  · exact (hSX i.castSucc).trans (by rw [Fin.lastCases_castSucc]; rfl)

private theorem eq_zero_of_eval_eq_zero_on_infinite_unit_ball (l : ℕ) [Fact l.Prime] : ∀ (D : ℕ) (c : Coef l)
    (Z : Fin D → Set (PadicAlgCl l)), (∀ i, (Z i).Infinite) → (∀ i, ∀ z ∈ Z i, ‖z‖ < 1) →
    ∀ f : MvPowerSeries (Fin D) c.O,
      (∀ (c' : Coef l) (y : MvPowerSeries (Fin D) c.O →ₐ[c.O] PadicAlgCl l),
        (∀ g, y g ∈ c'.O) → (∀ i, y (MvPowerSeries.X i) ∈ Z i) → y f = 0) → f = 0 := by
  intro D
  induction D with
  | zero =>
    intro c Z hZ hn f hf
    obtain ⟨c', y, -, hy, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.existsPt l c (Fin 0) (fun i => i.elim0)
      (fun i => i.elim0)
    have h1 : f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by
      ext n
      have hn0 : n = 0 := Subsingleton.elim _ _
      subst hn0
      simp
    have h2 := hf c' y hy (fun i => i.elim0)
    rw [h1, algHom_mvPowerSeries_C_eq_algebraMap] at h2
    have h3 : MvPowerSeries.constantCoeff f = 0 := Subtype.ext h2
    rw [h1, h3, map_zero]
  | succ D ih =>
    intro c Z hZ hn f hf
    haveI := c.dvr
    haveI := c.fin
    obtain ⟨hcpl, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
    obtain ⟨S, hSi, hSC, hSl, hSc⟩ := exists_injective_mvPowerSeries_last_to_powerSeries c.O D
    apply hSi
    rw [map_zero]
    refine PowerSeries.ext fun n => ?_
    rw [map_zero]
    apply ih c (fun i => Z i.castSucc) (fun i => hZ _) (fun i => hn _)
    intro c'' y'' hint hX
    haveI := c''.dvr
    haveI := c''.fin
    obtain ⟨hcpl'', -⟩ := UpperTheory.V.abelian₂.dvr_finite l c''.O
    let ycr : MvPowerSeries (Fin D) c.O →+* c''.O := y''.toRingHom.codRestrict c''.O hint
    have hycr : ∀ x, ((ycr x : c''.O) : PadicAlgCl l) = y'' x := fun x => rfl
    have hg : PowerSeries.map ycr (S f) = 0 := by
      refine UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.oneVar c''.O (PadicAlgCl l) c''.O.val.toRingHom
        Subtype.val_injective _ (Z (Fin.last D)) (hZ _) ?_
      intro z hz
      obtain ⟨c3, ev, -, hev, hevX⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.existsPt l c'' Unit (fun _ => z)
        (fun _ => hn _ z hz)
      have hevC : ∀ b : c''.O, ev (PowerSeries.C b) = b := fun b => algHom_mvPowerSeries_C_eq_algebraMap ev b
      let G : MvPowerSeries (Fin (D + 1)) c.O →ₐ[c.O] PadicAlgCl l :=
        { toRingHom := ev.toRingHom.comp ((PowerSeries.map ycr).comp S)
          commutes' := by
            intro a
            show ev (PowerSeries.map ycr (S (algebraMap c.O _ a))) = _
            rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hSC,
              PowerSeries.map_C, hevC, hycr, algHom_mvPowerSeries_C_eq_algebraMap] }
      have hG : G f = 0 := by
        refine hf c3 G (fun g => hev _) (fun i => ?_)
        refine Fin.lastCases ?_ (fun j => ?_) i
        · show ev (PowerSeries.map ycr (S (MvPowerSeries.X (Fin.last D)))) ∈ _
          rw [hSl, PowerSeries.map_X]
          exact (hevX ()).symm ▸ hz
        · show ev (PowerSeries.map ycr (S (MvPowerSeries.X j.castSucc))) ∈ _
          rw [hSc, PowerSeries.map_C, hevC, hycr]
          exact hX j
      exact ⟨ev.toRingHom, fun a => hevC a, hevX (), hG⟩
    have h4 := congrArg (PowerSeries.coeff n) hg
    rw [PowerSeries.coeff_map, map_zero] at h4
    have h5 := congrArg Subtype.val h4
    rw [hycr] at h5
    exact h5

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.denseBox :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (D : ℕ) (Z : Fin D → Set (PadicAlgCl l)), (∀ i, (Z i).Infinite) → (∀ i, ∀ z ∈ Z i, ‖z‖ < 1) → Sep {y : MvPowerSeries (Fin D) c.O →ₐ[c.O] PadicAlgCl l | ∀ i, y (MvPowerSeries.X i) ∈ Z i} := by
  intro l _ c D Z hZ hn f hf
  exact eq_zero_of_eval_eq_zero_on_infinite_unit_ball l D c Z hZ hn f (fun c' y _ hX => hf y hX)
