import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.FrobeniusCoeffSupportBddBelow

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

namespace LocReg

theorem hQ (hs1 : W.s = 1) (hR : Ring9 W) : ∃ u : (LetA O n)ˣ, W.Q = (u : LetA O n) * qP W := by
  obtain ⟨u, hu⟩ := hR.2.2.2.2.1
  refine ⟨u, ?_⟩
  have hQq : W.Q = W.q := by
    show (W.φA ^ (W.s - 1)) W.q = W.q
    rw [hs1, Nat.sub_self, pow_zero]
    rfl
  rw [hQq, hu]
  congr 1
  funext i
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qP]

end LocReg

theorem locReg_holds {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {H : ℕ → ℕ} {κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c}
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ lam) (j M g η : ℕ)
    (kind : ℕ → Kind) (b : ℕ → ℕ) (m : ℕ)
    (hκ : κ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m)
    (hk1b : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b)
    (hUnits : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt)
    (hP5 : ∀ i, (latOf C).P5M i m)
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (levB_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
      (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
          (((PD.p : LL) ^ (k - (j : ℤ))) •
            φVB PD (LL := LL) (V := T.V) (Lb.levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ)))))
    (lev_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))
    (hp0 : (PD.p : LL) ≠ 0)
    (hs1 : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) :
    (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).LocReg := by
  intro s hs w
  have hW : ∀ z ∈ (latOf C).pull (c - (ell : ZMod n)) ell,
      z ∈ (latOf C).W c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) := fun z hz =>
    Submodule.mem_comap.2 (Submodule.smul_mem _ _ hz)
  have key : ∀ (z : C.V) (hz : z ∈ (latOf C).pull (c - (ell : ZMod n)) ell),
      prL s ((lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).loc s ⟨z, hW z hz⟩) ∈
        Xi (KsW W s) (Tw (LL := LL) (D := Dc W T c) 0) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz0 =>
      obtain ⟨y, hy, rfl⟩ := hz0
      refine Formalism.ExponentWindows.G.SlopeTestRemainingChoices.mem_Xi.2 fun k => ?_
      rw [level_expansion_d_direct Hy j M g η kind b m hκ hk1b hUnits hP5 (LocReg.hQ hs1 hR) levN_eq levB_φ lev_φ hp0
        y hy ⟨_, hW _ (Submodule.subset_span ⟨y, hy, rfl⟩)⟩ rfl s hs k]
      by_cases hk : 0 ≤ k
      · exact Submodule.tmul_mem_baseChange_of_mem _ (by simp [Tw, hk])
      · rw [frobeniusCoeff_low_eq_zero Lb T c ell _ 0
          (fun k' hk' => levelExpansion_neg_eq_zero levN_eq hs1 T hP4 _ _ k' hk') k (not_le.1 hk), TensorProduct.tmul_zero]
        exact Submodule.zero_mem _
    | zero =>
      have e : (⟨0, hW 0 (Submodule.zero_mem _)⟩ :
          ↥((latOf C).W c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell))) = 0 := rfl
      rw [e, map_zero]
      convert zero_mem (Xi (KsW W s) (Tw (LL := LL) (D := Dc W T c) 0)) using 1
      exact map_zero (prL (hΔ := Hy.delta) (ell := ell) s)
    | add x y hx hy ihx ihy =>
      have e : (⟨x + y, hW _ (Submodule.add_mem _ hx hy)⟩ :
          ↥((latOf C).W c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell))) =
          ⟨x, hW x hx⟩ + ⟨y, hW y hy⟩ := rfl
      rw [e, map_add]
      convert add_mem ihx ihy using 1
      exact map_add (prL (hΔ := Hy.delta) (ell := ell) s) _ _
    | smul a x hx ih =>
      have e : (⟨a • x, hW _ (Submodule.smul_mem _ a hx)⟩ :
          ↥((latOf C).W c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell))) = a • ⟨x, hW x hx⟩ := rfl
      rw [e, LinearMap.map_smul]
      convert xi_module_structure LL (KsW W s) (Dc W T c) _ (tw_mono 0) (rhoL hR c s a) _ ih using 1
      exact prL_smul (hΔ := Hy.delta) s a _
  have hw' : Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell • (w : C.V) ∈ (latOf C).pull (c - (ell : ZMod n)) ell :=
    Submodule.mem_comap.1 w.2
  have e : Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell • (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).loc s w =
      (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).loc s
        ⟨Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell • (w : C.V), hW _ hw'⟩ := by
    rw [← LinearMap.map_smul]
    rfl
  show prL s (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell • (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).loc s w) ∈ _
  rw [e]
  exact key _ hw'

end Formalism.MainNotions.N.Ln03.Pf
