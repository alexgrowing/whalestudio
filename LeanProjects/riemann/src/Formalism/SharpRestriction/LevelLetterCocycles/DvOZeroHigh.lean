import Formalism.SharpRestriction.LevelLetterCocycles.SecInTransport

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

theorem tau_over (hbij : Function.Bijective (algebraMap K₀ K)) (c : ZMod n) :
    ∃ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ c ∧ ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x := by
  let E : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hbij
  refine ⟨(W.emb c).comp E.symm.toAlgHom, ?_, fun x => ?_⟩
  · ext x
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    congr 1
    exact E.symm_apply_apply x
  · simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    congr 1
    exact E.symm_apply_apply x

theorem dvO_letter (T : LocLat G Qp LL O) (c' : ZMod n) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e : ℕ) (c₀ : Fin d → O) :
    dvO W T e b c₀ ∈ DcrisL PD T.ρ (W.emb (c' + (e : ZMod n))) := by
  unfold dvO dv
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
  have hbN : b m ∈ W.N T := (hb.1 m).1.1
  have hbl : (letE c' : LetA O n) • b m = b m := Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' (hb.1 m).2
  have hcl : cmpD W T (b m) ∈ DcrisL PD T.ρ (W.emb c') := by
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hbN]; exact Formalism.MainNotions.UnusedSlot80.ArcF.cmp_mem_letter W T c' hbN hbl
  exact Formalism.MainNotions.UnusedSlot80.ArcF.φVB_pow_letter W T c' hcl e

variable [IsDomain O]

theorem dvO_filLow (hbij : Function.Bijective (algebraMap K₀ K)) (A : ArcP n) (hA : A.OK) (c' : ZMod n)
    (hc' : c' ∈ A.cuts) (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e s : ℕ) (hse : s < e) (c₀ : Fin d → O) :
    dvO W T e b c₀ ∈ FilS W T (c' + (e : ZMod n)) s (-(A.Hs (c' + (e : ZMod n)) e s : ℤ)) := by
  set i : ZMod n := c' + ((e - s : ℕ) : ZMod n) with hidef
  obtain ⟨τ, hτ, hover⟩ := tau_over W hbij i
  have hJ : ∀ a, IsJumpV PD T.ρ τ a → -(A.Hs (c' + (e : ZMod n)) e s : ℤ) ≤ a := by
    intro a ha
    have hw := Formalism.MainNotions.UnusedSlot80.PhiPowers.win_sub A.G₀ A.S A.η (A.ty i) (hA.2.2.2.2.1 i) (hT.2 i τ hτ a ha)
    have hle := Formalism.MainNotions.UnusedSlot80.ArcC.hs_ge A hA c' hc' e (e - s) (by omega) (by omega)
    rw [show e - (e - s) = s by omega, ← hidef] at hle
    have := hw.1
    push_cast at this ⊢
    omega
  have hy := fil_low W T i τ hover hbij.2 _ hJ (dvO_letter W T c' b hb (e - s) c₀)
  refine ⟨dvO W T (e - s) b c₀, ⟨hy, ?_⟩, ?_⟩
  · rw [show c' + (e : ZMod n) - (s : ZMod n) = i by rw [hidef]; push_cast [Nat.cast_sub hse.le]; ring]
    exact dvO_letter W T c' b hb (e - s) c₀
  · rw [← dvO_add, Nat.sub_add_cancel hse.le]

theorem dvO_zero_high [NeZero n] (hbij : Function.Bijective (algebraMap K₀ K))
    (hinj : Function.Injective (algebraMap O LL)) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing (LL := LL) O v)
    (hs : W.s = 1) (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (T : LocLat G Qp LL O) (hT : Win W A T)
    (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e s : ℕ) (hse : s < e) (u : ℤ)
    (hu : (A.Hs (c' + (e : ZMod n)) e s : ℤ) < u) (c₀ : Fin d → O)
    (h : dvO W T e b c₀ ∈ FilS W T (c' + (e : ZMod n)) s u) : c₀ = 0 := by
  obtain ⟨y, ⟨hyF, hyD⟩, hye⟩ := h
  set i : ZMod n := c' + (e : ZMod n) - (s : ZMod n) with hidef
  obtain ⟨τ, hτ, hover⟩ := tau_over W hbij i
  have hHw : Hw A.G₀ A.S A.η (A.ty i) ≤ A.Hs (c' + (e : ZMod n)) e s :=
    Formalism.MainNotions.UnusedSlot80.ArcC.hw_le_hs A hA c' hc' e s hse
  have hJ : ∀ a, IsJumpV PD T.ρ τ a → a ≤ (Hw A.G₀ A.S A.η (A.ty i) : ℤ) := fun a ha =>
    (Formalism.MainNotions.UnusedSlot80.PhiPowers.win_sub A.G₀ A.S A.η (A.ty i) (hA.2.2.2.2.1 i) (hT.2 i τ hτ a ha)).2
  have hy0 := fil_high W T i τ hover hbij.2 _ hJ u (by omega) hyD hyF
  rw [hy0, map_zero] at hye
  have hfb := (Formalism.MainNotions.UnusedSlot80.ArcF.frame_basis W hs hV T h3 (h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT))
    hmod c' e b hb).1
  have hdv : dvO W T e b c₀ = ∑ m, algebraMap O LL (c₀ m) • dv W T e b (Pi.single m 1) := by
    simp only [Formalism.MainNotions.UnusedSlot80.ArcF.dv_single]; rfl
  have hsum : ∑ m, algebraMap O LL (c₀ m) • dv W T e b (Pi.single m 1) = 0 := by rw [← hdv, ← hye]
  funext m
  apply hinj
  rw [Fintype.linearIndependent_iff.1 hfb _ hsum m]
  simp

theorem secIn_piLam (hπ : W.π₀ ∈ W.AΔ) (A : ArcP n) (a : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) {d : ℕ}
    (b : Fin d → W.DD T)
    (hlow : ∀ c₀ : Fin d → O, ∀ s < e, dvO W T e b c₀ ∈ FilS W T a s (-(A.Hs a e s : ℤ)))
    (h : Fin d → W.EE) (hh : ∀ k, InFr W a (W.π₀ * abelian₂ W A a e) 1 (h k)) :
    SecIn W a e (condNN W T a e b) h := by
  refine ⟨d, h, fun i => Pi.single i 1, fun _ s => (A.Hs a e s : ℤ), fun i => ⟨?_, ?_⟩, fun k => ?_⟩
  · obtain ⟨u, hu, hhu⟩ := hh i
    refine ⟨W.π₀ * u, W.AΔ.mul_mem hπ hu, ?_⟩
    have hnum : ∏ s ∈ Finset.range e, ps W s ^ ((A.Hs a e s : ℤ)).toNat = abelian₂ W A a e := by
      simp [abelian₂]
    have hden : ∏ s ∈ Finset.range e, ps W s ^ (-(A.Hs a e s : ℤ)).toNat = 1 :=
      Finset.prod_eq_one fun s _ => by rw [Int.toNat_eq_zero.2 (by omega), pow_zero]
    show algebraMap (LetA O n) W.EE (∏ s ∈ Finset.range e, ps W s ^ (-(A.Hs a e s : ℤ)).toNat) * h i =
      algebraMap (LetA O n) W.EE ((letE a * ∏ s ∈ Finset.range e, ps W s ^ ((A.Hs a e s : ℤ)).toNat) *
        (W.π₀ * u))
    rw [hden, hnum, ← one_mul (h i), ← map_one (algebraMap (LetA O n) W.EE), hhu, map_one, one_mul]
    congr 1; ring
  · intro s hs; exact hlow _ s hs
  · simp [Pi.single_apply]

end Formalism.MainNotions.UnusedSlot80.LevC
