import Formalism.SharpRestriction.LevelLetterCocycles.RingStepsOf
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvDelta
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvGam
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvExp
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvFil
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvRhoC
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvEquiv
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvBasis
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvJumps
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfMapLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfMapLocL
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfMapFl
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfMapHyp
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.GaloisActionFrobeniusComm
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfKapUnit
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLocReg
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfMem
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfHuZ
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfHOmega
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfJumpsLet
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.LvDataLocalizesConstOfCrystalline
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfSplit
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfCoeff
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfHOnil
import Formalism.SharpRestriction.LevelLetterCocycles.CoordStepsOf

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

namespace Assemble

theorem frac_of [IsDomain O] [IsFractionRing O LL] (a : LL) :
    ∃ y o : O, algebraMap O LL y ≠ 0 ∧ algebraMap O LL y * a = algebraMap O LL o := by
  obtain ⟨⟨o, y⟩, h⟩ := IsLocalization.surj (nonZeroDivisors O) a
  exact ⟨y, o, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2, by rw [mul_comm]; exact h⟩

theorem firstGeometricCondition_of_properties (hR : Ring9 W) :
    ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι PowerSeries.X = (w : PowerSeries O) * PowerSeries.X ^ (PD.p - 1) := by
  obtain ⟨w, hw, h⟩ := π₀₁_eq hR
  exact ⟨hw.unit, by rw [(baseIdOf hR).ι_X, IsUnit.unit_spec]; exact h⟩

end Assemble

theorem lvHyp_holds (Lb : LevB W) (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) {T : LocLat G Qp LL O}
    (C : Coord W (baseIdOf hR) T) (c : ZMod n) (ell : ℕ) (Λ κ : PowerSeries O) {r : ℕ} (e : Fin r → C.V)

    (lev_Γ : ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ f : LetA O n,
      W.lev i ζ (W.γA g f) = PowerSeries.rescale (algebraMap O LL (W.χΓ g : O)) (W.lev i ζ' f))
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (hgamK : W.gamK = W.gam)

    (hs1 : W.s = 1) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hT : IsCrys PD T.ρ) {Mj hj : ZMod n → ℕ}
    (hJl : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mj hj)

    (valRing : ValRing O v) (hv : ∀ (s : ℕ) (z : ℤ_[PD.p]), (PD.p : ℤ_[PD.p]) ^ (s + 1) ∣ z →
      ((s + 1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (ιZ z)))

    (hω : ∀ ω : DeltaT PD.p, ∃ g ∈ W.DelF,
      algebraMap O LL (W.χΓ g : O) = algebraMap O LL (ιZ ((ω.1 : ℤ_[PD.p]ˣ) : ℤ_[PD.p])))
    (huZ : ∀ k : ℕ, (k : WithTop ℚ) ≤
      v (algebraMap O LL (W.χΓ W.gam : O) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : LL)))
    (m : ℕ) (hm : ∀ i, Mj i ≤ m) (hκ : κ = Λ * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m) :
    LvHyp Lb hR uZ ιZ C c ell Λ κ (lamOf C c ell e) where
  delta := delta_holds hR uZ ιZ c lev_Γ hω valRing
  gamInv := gamInv_holds uZ ιZ T c
  gamRho := gamRho_holds hR uZ ιZ c lev_Γ hgamK huZ
  kap := kap_holds C ell Λ κ hP5 hT hJl hs1 hR m hm hκ
  expSemi := expSemi_holds Lb hR T c levN_eq
  locInv := locInv_holds Lb C κ (delta_holds hR uZ ιZ c lev_Γ hω valRing) hT levB_Γ hω hv
  loclInv := loclInv_holds hR uZ ιZ T c Λ _ (delta_holds hR uZ ιZ c lev_Γ hω valRing)
  filAnti := filAnti_holds
  rhoC := rhoC_holds hR c

theorem levSteps_of_jumps [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [CharZero LL] [IsFractionRing O LL]
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ}
    {κ : PowerSeries O} {r : ℕ} {e : Fin r → C.V}
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ (lamOf C c ell e))
    (ϖ : O) (j M g G₀ Sz η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ)

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
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)

    (hs1 : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) {π' : LetA O n} (hP9 : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π')
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hT : IsCrys PD T.ρ) {Mj hj : ZMod n → ℕ} (hJl : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mj hj)
    (hfin : FiniteDimensional LL ↥(Dcris PD T.ρ))

    (hϖ : Irreducible ϖ) (hℓm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (n0 : ℕ) (hn0 : ell ≤ n0) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n0))
    (G2 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))
    (hφ : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ PD.p - 1)
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (PD.p ^ (s + 1)) LL,
      1 + rhoZ W c ζ PowerSeries.X = PowerSeries.C ζ * PowerSeries.exp LL)
    (huZv : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (hom' : ∀ a : ZMod PD.p, a ≠ 0 → ∃ j : DeltaT PD.p, PadicInt.toZMod (j.1 : ℤ_[PD.p]) = a)

    (hl : 5 ≤ PD.p) (huZ : ∀ k : ℕ, (k : WithTop ℚ) ≤
      v (algebraMap O LL (W.χΓ W.gam : O) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : LL)))
    (m : ℕ) (hm : ∀ i, Mj i ≤ m)
    (hκ : κ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m)
    (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N (c - (ell : ZMod n))))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k)

    (hmem : (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Mem)
    (hpa1b : (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).LocalizesConst M e)
    (hjumps : ∀ s < ell, Formalism.ExponentWindows.G.Jumps (kind s) G₀ Sz η (b s) (FilD W T c s)) :
    LevSteps Hy ϖ j M g G₀ Sz η kind b e := by
  have R := ringSteps_of Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η ϖ hϖ (by omega) hℓm n0 hn0 hroot (Assemble.firstGeometricCondition_of_properties hR) G2 hφ hρζ
    huZv hutie hom'
  have hp0 : (PD.p : LL) ≠ 0 := Nat.cast_ne_zero.2 PD.hp.ne_zero
  have hP5' : ∀ i, (latOf C).P5M i m := fun i => LvLoc.latOf_P5M_of_p5_of_le C (hP5 T Mj hj hT hJl) hs1 hR m hm i
  exact
    { k1b := R.1
      k1c := fun s hs => (R.2.2.1 s hs).1
      k1d := fun s hs => (R.2.2.1 s hs).2
      unitsAt := R.2.2.2.1
      compl := R.2.2.2.2
      filt := filt_holds ell hfin
      jumps := hjumps
      mem := hmem
      locReg := locReg_holds Hy j M g η kind b m hκ R.1 R.2.2.2.1 hP5' levN_eq levB_φ lev_φ hp0 hs1 hP4
      pa1b := hpa1b
      equiv := equiv_holds Hy j M g η kind b hT levB_Γ hs1 hl huZ
      span := span_holds hBasis hBasis_e
      ind := ind_holds hBasis hBasis_e
      locLIs := locLIs_holds Hy j M g η kind b H rfl R.1 R.2.2.2.1
      lamInd := lamInd_holds hP3 hP9 Assemble.frac_of hBasis hBasis_e rfl
      lamSpan := lamSpan_holds hP3 hP9 hBasis hBasis_e rfl }

theorem levSteps_holds [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [CharZero LL] [IsFractionRing O LL]
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ}
    {κ : PowerSeries O} {r : ℕ} {e : Fin r → C.V}
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ (lamOf C c ell e))
    (ϖ : O) (j M g G₀ Sz η : ℕ) (ty : ZMod n → LT)

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
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)

    (hs1 : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) {π' : LetA O n} (hP9 : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π')
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hT : IsCrys PD T.ρ) {Mj hj : ZMod n → ℕ} (hJl : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mj hj)
    (hfin : FiniteDimensional LL ↥(Dcris PD T.ρ))

    (hϖ : Irreducible ϖ) (hℓm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (n0 : ℕ) (hn0 : ell ≤ n0) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n0))
    (G2 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))
    (hφ : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ PD.p - 1)
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (PD.p ^ (s + 1)) LL,
      1 + rhoZ W c ζ PowerSeries.X = PowerSeries.C ζ * PowerSeries.exp LL)
    (huZv : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (hom' : ∀ a : ZMod PD.p, a ≠ 0 → ∃ j : DeltaT PD.p, PadicInt.toZMod (j.1 : ℤ_[PD.p]) = a)

    (hl : 5 ≤ PD.p) (huZ : ∀ k : ℕ, (k : WithTop ℚ) ≤
      v (algebraMap O LL (W.χΓ W.gam : O) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : LL)))
    (m : ℕ) (hm : ∀ i, Mj i ≤ m)
    (hκ : κ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m)
    (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N (c - (ell : ZMod n))))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k)

    (hmem : (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) (E.kindAt (kdOf ty) c) (E.sizeAt (bbOf ty) c) η).Mem)
    (hpa1b : (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) (E.kindAt (kdOf ty) c) (E.sizeAt (bbOf ty) c) η).LocalizesConst M e)
    (hK : Function.Surjective (algebraMap K₀ K)) (hJ : KindJumps PD T W.emb G₀ Sz η ty) :
    LevSteps Hy ϖ j M g G₀ Sz η (E.kindAt (kdOf ty) c) (E.sizeAt (bbOf ty) c) e :=
  levSteps_of_jumps Hy ϖ j M g G₀ Sz η _ _ levN_eq levB_φ lev_φ levB_Γ hs1 hP4 hP3 hP9 hP5 hT hJl hfin hϖ hℓm n0 hn0 hroot G2 hφ hρζ huZv hutie hom' hl huZ m hm hκ hBasis hBasis_e hmem hpa1b (jumps_holds hK c ell G₀ Sz η ty hJ)

theorem levSteps_holds_quot [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [CharZero LL] [IsFractionRing O LL]
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ}
    {κ : PowerSeries O} {r : ℕ} {e : Fin r → C.V}
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ (lamOf C c ell e))
    (ϖ : O) (j M g G₀ Sz η : ℕ) (ty : ZMod n → LT)

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
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)

    (hs1 : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) {π' : LetA O n} (hP9 : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π')
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hT : IsCrys PD T.ρ) {Mj hj : ZMod n → ℕ} (hJl : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mj hj)
    (hfin : FiniteDimensional LL ↥(Dcris PD T.ρ))

    (hϖ : Irreducible ϖ) (hℓm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (n0 : ℕ) (hn0 : ell ≤ n0) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n0))
    (G2 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))
    (hφ : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ PD.p - 1)
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (PD.p ^ (s + 1)) LL,
      1 + rhoZ W c ζ PowerSeries.X = PowerSeries.C ζ * PowerSeries.exp LL)
    (huZv : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (hom' : ∀ a : ZMod PD.p, a ≠ 0 → ∃ j : DeltaT PD.p, PadicInt.toZMod (j.1 : ℤ_[PD.p]) = a)

    (hl : 5 ≤ PD.p) (huZ : ∀ k : ℕ, (k : WithTop ℚ) ≤
      v (algebraMap O LL (W.χΓ W.gam : O) - ((PadicInt.toZModPow k (uZ : ℤ_[PD.p])).val : LL)))
    (m : ℕ) (hm : ∀ i, Mj i ≤ m)
    (hκ : κ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m)
    (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N (c - (ell : ZMod n))))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k)

    (hmem : (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) (E.kindAt (kdOf ty) c) (E.sizeAt (bbOf ty) c) η).Mem)
    (hpa1b : (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) (E.kindAt (kdOf ty) c) (E.sizeAt (bbOf ty) c) η).LocalizesConst M e)
    (hK : Function.Surjective (algebraMap K₀ K))
    (hQuot : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a)
    {T₀ : LocLat G Qp LL O} (F : LatHom T₀.L T.L) (hc₀ : CrysLat PD T₀) (hc : CrysLat PD T) (hon : F.Onto)
    (hJ : KindJumps PD T₀ W.emb G₀ Sz η ty) :
    LevSteps Hy ϖ j M g G₀ Sz η (E.kindAt (kdOf ty) c) (E.sizeAt (bbOf ty) c) e :=
  levSteps_of_jumps Hy ϖ j M g G₀ Sz η _ _ levN_eq levB_φ lev_φ levB_Γ hs1 hP4 hP3 hP9 hP5 hT hJl hfin hϖ hℓm n0 hn0 hroot G2 hφ hρζ huZv hutie hom' hl huZ m hm hκ hBasis hBasis_e hmem hpa1b
    (jumps_holds_quot hK hQuot F hc₀ hc hon c ell G₀ Sz η ty hJ)

theorem mapSteps_holds {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁} {C₂ : Coord W (baseIdOf hR) T₂}
    {F : LatHom T₁.L T₂.L} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ} {κ₁ κ₂ : PowerSeries O} {r₁ r₂ : ℕ}
    (hC : CoordHom C₁ C₂ F) (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V)
    (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₁ (lamOf C₁ c ell e₁))
    (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₂ (lamOf C₂ c ell e₂))
    (Mh : MapHyp hR uZ ιZ F c) (j M g η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ)
    (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))

    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))

    (hk1b₁ : (lvModel Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b) (hUnits₁ : (lvModel Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt)
    (hk1b₂ : (lvModel Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b) (hUnits₂ : (lvModel Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt)

    (m₁ m₂ : ℕ)
    (hκ₁ : κ₁ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m₁)
    (hκ₂ : κ₂ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m₂)
    (he₁ : ∀ k, e₁ k ∈ (latOf C₁).N (c - (ell : ZMod n)))
    (he₂ : ∀ l, e₂ l ∈ (latOf C₂).N (c - (ell : ZMod n)))
    (hP : ∀ k, ∃ a : Fin r₂ → PowerSeries O, (latHomOf hC).f (e₁ k) = ∑ l, a l • e₂ l ∧
      ∀ l, LinearMap.toMatrix' P l k = PowerSeries.constantCoeff (a l)) :
    MapSteps hC Hy₁ Hy₂ Mh j M g η kind b e₁ e₂ P where
  locComm := locComm_holds hC Hy₁ Hy₂ Mh j M g η kind b levN_eq
    (kapUnit_holds Hy₁ j M g η kind b m₁ hκ₁ hk1b₁ hUnits₁)
    (kapUnit_holds Hy₂ j M g η kind b m₂ hκ₂ hk1b₂ hUnits₂)
  loclComm := loclComm_holds hC Hy₁ Hy₂ Mh j M g η kind b e₁ e₂ P rfl rfl he₁ he₂ hP
  mapFl := mapFl_holds Hy₁ Hy₂ Mh j M g η kind b
  cMap := cMap_holds Mh.memD kind b η P
    (lambda_of_matrixCongruences hC Mh.memD e₁ e₂ P he₁ he₂ (prLIs_holds hC e₁ e₂ P he₂ hP))
  prLIs := prLIs_holds hC e₁ e₂ P he₂ hP

theorem mapHyp_of (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (c : ZMod n) : MapHyp hR uZ ιZ F c :=
  mapHyp_holds hR uZ ιZ F c

namespace Assemble

theorem finrank_one (hKb : Function.Bijective (algebraMap K₀ K)) : Module.finrank K₀ K = 1 :=
  (AlgEquiv.ofBijective (Algebra.ofId K₀ K) hKb).toLinearEquiv.finrank_eq.symm.trans (Module.finrank_self K₀)

theorem pow_unif [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ)
    (hℓm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) :
    ∃ (N : ℕ) (u : O), ((PD.p : ℕ) : O) ^ N = ϖ * u := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hℓm
  obtain ⟨u, hu⟩ := hℓm
  exact ⟨1, u, by rw [pow_one, hu]⟩

theorem p_ne_zero [CharZero LL] : ((PD.p : ℕ) : O) ≠ 0 := by
  intro h
  have h2 : ((PD.p : ℕ) : LL) = 0 := by rw [← map_natCast (algebraMap O LL), h, map_zero]
  exact PD.hp.ne_zero (Nat.cast_eq_zero.1 h2)

theorem jumps_bound [Fintype (K →ₐ[Qp] LL)] (hDR : Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris PD LL)
    (hKb : Function.Bijective (algebraMap K₀ K)) {T : LocLat G Qp LL O} (hc : CrysLat PD T) :
    ∃ (Mj hj : ZMod n → ℕ) (m : ℕ), Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mj hj ∧ ∀ i, Mj i ≤ m := by
  obtain ⟨Mj, hj, h⟩ := jumps_bounded_crystalline (W := W) hDR hKb T hc
  exact ⟨Mj, hj, Finset.univ.sup Mj, h, fun i => Finset.le_sup (Finset.mem_univ i)⟩

end Assemble

theorem lvHyp_holds' (Lb : LevB W) (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) {T : LocLat G Qp LL O}
    (C : Coord W (baseIdOf hR) T) (c : ZMod n) (ell : ℕ) (Λ κ : PowerSeries O) {r : ℕ} (e : Fin r → C.V)

    (lev_Γ : ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ f : LetA O n,
      W.lev i ζ (W.γA g f) = PowerSeries.rescale (algebraMap O LL (W.χΓ g : O)) (W.lev i ζ' f))
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))

    (hs1 : W.s = 1) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.p9 W T) (hT : IsCrys PD T.ρ)
    {Mj hj : ZMod n → ℕ} (hJl : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mj hj)

    (valRing : ValRing O v) (hKb : Function.Bijective (algebraMap K₀ K))

    (hl : 5 ≤ PD.p) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (m : ℕ) (hm : ∀ i, Mj i ≤ m) (hκ : κ = Λ * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m) :
    LvHyp Lb hR uZ ιZ C c ell Λ κ (lamOf C c ell e) :=
  lvHyp_holds Lb hR uZ ιZ C c ell Λ κ e lev_Γ levB_Γ levN_eq (W.gamK_eq_one hs1 (by omega)) hs1 hP5 hT hJl
    valRing (hv_holds W valRing.2.2)
    (hω_holds (card_DelF hs1 (by omega) (Assemble.finrank_one hKb) h9) valRing.1 ιZ)
    (huZ_holds hutie valRing.2.2) m hm hκ

theorem levSteps_of_jumps' [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [CharZero LL] [IsFractionRing O LL]
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ}
    {κ : PowerSeries O} {r : ℕ} {e : Fin r → C.V}
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ (lamOf C c ell e))
    (ϖ : O) (j M g G₀ Sz η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ)

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
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (cmp_eq : ∀ (i : ZMod n) (x : ↥(W.N T)), W.cmp T ((letE i : LetA O n) • x) = Lb.levB T i 1 x 0)

    (hs1 : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hP4L : LevelMapHodgeFiltration W) (hSat : Sat W) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (h9 : Formalism.MainNotions.DeltaInvariantLattices.p9 W T)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hc : CrysLat PD T) {Mj Hj : ZMod n → ℕ} (hJl : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mj Hj)

    (hv_int : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hKb : Function.Bijective (algebraMap K₀ K))

    (hϖ : Irreducible ϖ) (hℓm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (hn : ell ≤ n) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n))
    (G2 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))
    (hφ : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ PD.p - 1)
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (PD.p ^ (s + 1)) LL,
      1 + rhoZ W c ζ PowerSeries.X = PowerSeries.C ζ * PowerSeries.exp LL)
    (huZv : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (hom' : ∀ a : ZMod PD.p, a ≠ 0 → ∃ j : DeltaT PD.p, PadicInt.toZMod (j.1 : ℤ_[PD.p]) = a)

    (hl : 5 ≤ PD.p) (m : ℕ) (hm : ∀ i, Mj i ≤ m)
    (hκ : κ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m)
    (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N (c - (ell : ZMod n))))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k) (hj : j ≤ ell) (h3g : 3 * g ≤ ((baseIdOf hR).Bs.ℓ - 1) * M)
    (hjumps : ∀ s < ell, Formalism.ExponentWindows.G.Jumps (kind s) G₀ Sz η (b s) (FilD W T c s)) :
    LevSteps Hy ϖ j M g G₀ Sz η kind b e := by
  have hℓ2 : PD.p ≠ 2 := by omega
  have hK1 := Assemble.finrank_one hKb
  have hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀ := ((h9 hs1 hℓ2).2.2 hK1).2
  have R := ringSteps_of Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η ϖ hϖ hℓ2 hℓm n hn hroot (Assemble.firstGeometricCondition_of_properties hR) G2 hφ hρζ
    huZv hutie hom'
  have hfin : FiniteDimensional LL ↥(Dcris PD T.ρ) := by
    have := hc.1
    exact lvFil_fin_of_isCrys PD T.ρ hc.2.2.2
  have hP5' : ∀ i, (latOf C).P5M i m := fun i => LvLoc.latOf_P5M_of_p5_of_le C (hP5 T Mj Hj hc.2.2.2 hJl) hs1 hR m hm i
  have he : ∀ k, e k ∈ (latOf C).N (c - (ell : ZMod n)) := fun k => by
    rw [← hBasis_e k]
    exact (hBasis k).2
  have hmem := mem_holds hP4L hSat hc.2.2.2 (levN_eq T) hmod hP3
    (free_of (baseIdOf_inj hR) (baseIdOf_full hR) hmod C c) hroot hn m hκ R.1 R.2.2.2.1
    (filt_holds ell hfin) ϖ R.2.2.2.2 (Assemble.pow_unif hϖ hℓm) Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η
  have hpa1b := lvData_localizesConst_of_crystalline Hy j M g η kind b m e hκ he rfl R.1 R.2.2.2.1 hP5' levN_eq levB_φ lev_φ levB_Γ
    cmp_eq hc.2.2.2 hs1 hℓ2 hP4 hR hj h3g
  exact levSteps_of_jumps Hy ϖ j M g G₀ Sz η kind b levN_eq levB_φ lev_φ levB_Γ hs1 hP4 hP3 hmod hP5
    hc.2.2.2 hJl hfin hϖ hℓm n hn hroot G2 hφ hρζ huZv hutie hom' hl (huZ_holds hutie hv_int) m hm hκ
    hBasis hBasis_e hmem hpa1b hjumps

theorem levSteps_holds' [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [CharZero LL] [IsFractionRing O LL]
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ}
    {κ : PowerSeries O} {r : ℕ} {e : Fin r → C.V}
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ (lamOf C c ell e))
    (ϖ : O) (j M g G₀ Sz η : ℕ) (ty : ZMod n → LT)

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
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (cmp_eq : ∀ (i : ZMod n) (x : ↥(W.N T)), W.cmp T ((letE i : LetA O n) • x) = Lb.levB T i 1 x 0)

    (hs1 : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hP4L : LevelMapHodgeFiltration W) (hSat : Sat W) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (h9 : Formalism.MainNotions.DeltaInvariantLattices.p9 W T)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hc : CrysLat PD T) {Mj Hj : ZMod n → ℕ} (hJl : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mj Hj)

    (hv_int : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hKb : Function.Bijective (algebraMap K₀ K))

    (hϖ : Irreducible ϖ) (hℓm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (hn : ell ≤ n) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n))
    (G2 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))
    (hφ : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ PD.p - 1)
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (PD.p ^ (s + 1)) LL,
      1 + rhoZ W c ζ PowerSeries.X = PowerSeries.C ζ * PowerSeries.exp LL)
    (huZv : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (hom' : ∀ a : ZMod PD.p, a ≠ 0 → ∃ j : DeltaT PD.p, PadicInt.toZMod (j.1 : ℤ_[PD.p]) = a)

    (hl : 5 ≤ PD.p) (m : ℕ) (hm : ∀ i, Mj i ≤ m)
    (hκ : κ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m)
    (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N (c - (ell : ZMod n))))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k) (hj : j ≤ ell) (h3g : 3 * g ≤ ((baseIdOf hR).Bs.ℓ - 1) * M)
    (hJ : KindJumps PD T W.emb G₀ Sz η ty) :
    LevSteps Hy ϖ j M g G₀ Sz η (E.kindAt (kdOf ty) c) (E.sizeAt (bbOf ty) c) e :=
  levSteps_of_jumps' Hy ϖ j M g G₀ Sz η _ _ levN_eq levB_φ lev_φ levB_Γ cmp_eq hs1 hP4 hP4L hSat hP3 h9 hP5 hc hJl hv_int hKb hϖ hℓm hn hroot G2 hφ hρζ huZv hutie hom' hl m hm hκ hBasis hBasis_e hj h3g (jumps_holds hKb.2 c ell G₀ Sz η ty hJ)

theorem levSteps_holds_quot' [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [CharZero LL] [IsFractionRing O LL]
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ}
    {κ : PowerSeries O} {r : ℕ} {e : Fin r → C.V}
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ (lamOf C c ell e))
    (ϖ : O) (j M g G₀ Sz η : ℕ) (ty : ZMod n → LT)

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
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (cmp_eq : ∀ (i : ZMod n) (x : ↥(W.N T)), W.cmp T ((letE i : LetA O n) • x) = Lb.levB T i 1 x 0)

    (hs1 : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hP4L : LevelMapHodgeFiltration W) (hSat : Sat W) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (h9 : Formalism.MainNotions.DeltaInvariantLattices.p9 W T)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hc : CrysLat PD T) {Mj Hj : ZMod n → ℕ} (hJl : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mj Hj)

    (hv_int : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hKb : Function.Bijective (algebraMap K₀ K))

    (hϖ : Irreducible ϖ) (hℓm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (hn : ell ≤ n) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n))
    (G2 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))
    (hφ : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ PD.p - 1)
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (PD.p ^ (s + 1)) LL,
      1 + rhoZ W c ζ PowerSeries.X = PowerSeries.C ζ * PowerSeries.exp LL)
    (huZv : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (hom' : ∀ a : ZMod PD.p, a ≠ 0 → ∃ j : DeltaT PD.p, PadicInt.toZMod (j.1 : ℤ_[PD.p]) = a)

    (hl : 5 ≤ PD.p) (m : ℕ) (hm : ∀ i, Mj i ≤ m)
    (hκ : κ = Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m)
    (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N (c - (ell : ZMod n))))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k) (hj : j ≤ ell) (h3g : 3 * g ≤ ((baseIdOf hR).Bs.ℓ - 1) * M)
    (hQuot : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a)
    {T₀ : LocLat G Qp LL O} (F : LatHom T₀.L T.L) (hc₀ : CrysLat PD T₀) (hon : F.Onto)
    (hJ : KindJumps PD T₀ W.emb G₀ Sz η ty) :
    LevSteps Hy ϖ j M g G₀ Sz η (E.kindAt (kdOf ty) c) (E.sizeAt (bbOf ty) c) e :=
  levSteps_of_jumps' Hy ϖ j M g G₀ Sz η _ _ levN_eq levB_φ lev_φ levB_Γ cmp_eq hs1 hP4 hP4L hSat hP3 h9 hP5 hc hJl hv_int hKb hϖ hℓm hn hroot G2 hφ hρζ huZv hutie hom' hl m hm hκ hBasis hBasis_e hj h3g
    (jumps_holds_quot hKb.2 hQuot F hc₀ hc hon c ell G₀ Sz η ty hJ)

theorem finalArc_holds [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [CharZero LL] [IsFractionRing O LL] [Fintype (K →ₐ[Qp] LL)]
    (Lb : LevB W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O)
    {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁} {C₂ : Coord W (baseIdOf hR) T₂}
    {F : LatHom T₁.L T₂.L} (hC : CoordHom C₁ C₂ F) (c : ZMod n) (ell : ℕ) (H : ℕ → ℕ) (ϖ : O)
    (j M g G₀ Sz η : ℕ) (ty : ZMod n → LT) {r₁ r₂ : ℕ} (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V)
    (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))

    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (cmp_eq : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (x : ↥(W.N T)),
      W.cmp T ((letE i : LetA O n) • x) = Lb.levB T i 1 x 0)
    (levB_φ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL),
      (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
      (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
          (((PD.p : LL) ^ (k - (j : ℤ))) •
            φVB PD (LL := LL) (V := T.V) (Lb.levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ)))))
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (lev_Γ : ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ f : LetA O n,
      W.lev i ζ (W.γA g f) = PowerSeries.rescale (algebraMap O LL (W.χΓ g : O)) (W.lev i ζ' f))
    (lev_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))

    (hs1 : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hP4L : LevelMapHodgeFiltration W) (hSat : Sat W) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hDR : Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris PD LL)
    (hQuot : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a)

    (hc₁ : CrysLat PD T₁) (hc₂ : CrysLat PD T₂) (hon : F.Onto) (hJ : KindJumps PD T₁ W.emb G₀ Sz η ty)

    (valRing : ValRing O v) (hKb : Function.Bijective (algebraMap K₀ K))

    (hϖ : Irreducible ϖ) (hℓm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (hn : ell ≤ n) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ n))
    (G2 : ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))
    (hφ : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ PD.p - 1)
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (PD.p ^ (s + 1)) LL,
      1 + rhoZ W c ζ PowerSeries.X = PowerSeries.C ζ * PowerSeries.exp LL)
    (huZv : ((uZ : ℤ_[PD.p]) - 1).valuation = 1) (hutie : ιZ uZ = (W.χΓ W.gam : O))
    (hom' : ∀ a : ZMod PD.p, a ≠ 0 → ∃ j : DeltaT PD.p, PadicInt.toZMod (j.1 : ℤ_[PD.p]) = a)

    (hl : 5 ≤ PD.p)
    (hBasis₁ : Module.Basis (Fin r₁) (PowerSeries O) ↥((latOf C₁).N (c - (ell : ZMod n))))
    (hBasis_e₁ : ∀ k, (hBasis₁ k : C₁.V) = e₁ k)
    (hBasis₂ : Module.Basis (Fin r₂) (PowerSeries O) ↥((latOf C₂).N (c - (ell : ZMod n))))
    (hBasis_e₂ : ∀ k, (hBasis₂ k : C₂.V) = e₂ k)
    (hP : ∀ k, ∃ a : Fin r₂ → PowerSeries O, (latHomOf hC).f (e₁ k) = ∑ l, a l • e₂ l ∧
      ∀ l, LinearMap.toMatrix' P l k = PowerSeries.constantCoeff (a l))
    (hj : j ≤ ell) (h3g : 3 * g ≤ ((baseIdOf hR).Bs.ℓ - 1) * M) :
    E.FinalArc (latHomOf hC) c ell H LL (KsW W) (DeltaT PD.p) ϖ (W.χΓ W.gam) j M g G₀ Sz η
      (E.kindAt (kdOf ty) c) (E.sizeAt (bbOf ty) c) := by
  obtain ⟨Mj₁, hj₁, m₁, hJl₁, hm₁⟩ := Assemble.jumps_bound (W := W) hDR hKb hc₁
  obtain ⟨Mj₂, hj₂, m₂, hJl₂, hm₂⟩ := Assemble.jumps_bound (W := W) hDR hKb hc₂
  have hT₁ := hc₁.2.2.2
  have hT₂ := hc₂.2.2.2
  have Hy₁ := lvHyp_holds' Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m₁) e₁
    lev_Γ levB_Γ levN_eq hs1 hP5 (hP9 T₁ hT₁) hT₁ hJl₁ valRing hKb hl hutie m₁ hm₁ rfl
  have Hy₂ := lvHyp_holds' Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell * ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ m₂) e₂
    lev_Γ levB_Γ levN_eq hs1 hP5 (hP9 T₂ hT₂) hT₂ hJl₂ valRing hKb hl hutie m₂ hm₂ rfl
  have ls₁ := levSteps_holds' Hy₁ ϖ j M g G₀ Sz η ty levN_eq (levB_φ T₁ hT₁) lev_φ levB_Γ (cmp_eq T₁ hT₁) hs1
    (hP4 T₁ hT₁) hP4L hSat (hP3 T₁ hT₁) (hP9 T₁ hT₁) hP5 hc₁ hJl₁ valRing.2.2 hKb hϖ hℓm hn hroot G2 hφ hρζ
    huZv hutie hom' hl m₁ hm₁ rfl hBasis₁ hBasis_e₁ hj h3g hJ
  have ls₂ := levSteps_holds_quot' Hy₂ ϖ j M g G₀ Sz η ty levN_eq (levB_φ T₂ hT₂) lev_φ levB_Γ (cmp_eq T₂ hT₂)
    hs1 (hP4 T₂ hT₂) hP4L hSat (hP3 T₂ hT₂) (hP9 T₂ hT₂) hP5 hc₂ hJl₂ valRing.2.2 hKb hϖ hℓm hn hroot G2 hφ
    hρζ huZv hutie hom' hl m₂ hm₂ rfl hBasis₂ hBasis_e₂ hj h3g hQuot F hc₁ hon hJ
  have he₁ : ∀ k, e₁ k ∈ (latOf C₁).N (c - (ell : ZMod n)) := fun k => by
    rw [← hBasis_e₁ k]
    exact (hBasis₁ k).2
  have he₂ : ∀ k, e₂ k ∈ (latOf C₂).N (c - (ell : ZMod n)) := fun k => by
    rw [← hBasis_e₂ k]
    exact (hBasis₂ k).2
  have ms := mapSteps_holds hC e₁ e₂ Hy₁ Hy₂ (mapHyp_of hR uZ ιZ F c) j M g η _ _ P levN_eq
    ls₁.k1b ls₁.unitsAt ls₂.k1b ls₂.unitsAt m₁ m₂ rfl rfl he₁ he₂ hP
  exact arc_of_steps hC Hy₁ Hy₂ (mapHyp_of hR uZ ιZ F c) ϖ j M g G₀ Sz η _ _ e₁ e₂ P ls₁ ls₂ ms

theorem coordSteps_holds [IsDomain O] [IsDiscreteValuationRing O] [CharZero LL]
    [Fintype (K →ₐ[Qp] LL)] (hR : Ring9 W) {e : W.DD W.one}

    (hs1 : W.s = 1) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hLem3 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeLengthLemma W) (hDR : Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris PD LL)
    (hUnitGen : UnitGen W e) (hCrysOne : IsCrys PD W.one.ρ)

    (hKb : Function.Bijective (algebraMap K₀ K))

    (hl : 5 ≤ PD.p) :
    CoordSteps hR e :=
  coordSteps_of hR e (coeffStep_holds hR)
    (splitStep_holds inferInstance (hOnil_of (Assemble.p_ne_zero (LL := LL))) hs1
      (by omega) hP9 hLem3 (jumps_bounded_crystalline hDR hKb))
    (unitStep_holds hUnitGen hCrysOne)

end Formalism.MainNotions.N.Ln03.Pf
