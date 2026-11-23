import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalClauseOfFrobeniusHyps
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsXPowMul
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSDivMem
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMulVBFilCris

noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs.Tools

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Exp

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    {W : LocWach PD LL O v n}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW}
    {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai} {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA}
    {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}

def PhiSeq (PD : PeriodData G Qp K₀ K B BdR) (T : LocLat G Qp LL O) (d : ℤ → T.V ⊗[Qp] B) : ℤ → T.V ⊗[Qp] B :=
  fun k => ((PD.p : LL) ^ k) • φVB PD (LL := LL) (V := T.V) (d k)

theorem LB_PhiSeq {T : LocLat G Qp LL O} {m : ℤ} {d : ℤ → T.V ⊗[Qp] B} (hd : LB m d) :
    LB m (PhiSeq PD T d) := fun k hk => by simp [PhiSeq, hd k hk]

theorem PhiSeq_smulS (hp : (PD.p : LL) ≠ 0) {T : LocLat G Qp LL O} {m : ℤ} {d : ℤ → T.V ⊗[Qp] B}
    (hd : LB m d) (g : PowerSeries LL) :
    PhiSeq PD T (smulS g d) = smulS (PowerSeries.rescale (PD.p : LL) g) (PhiSeq PD T d) := by
  funext k
  obtain ⟨N, hN⟩ : ∃ N : ℕ, k - m < N :=
    ⟨Int.toNat (k - m) + 1, by have := Int.self_le_toNat (k - m); push_cast; omega⟩
  rw [smulS_eq_sum (LB_PhiSeq hd) _ k N hN]
  simp only [PhiSeq]
  rw [smulS_eq_sum hd g k N hN, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_smul, PowerSeries.coeff_rescale, smul_smul]
  congr 1
  rw [← zpow_natCast (PD.p : LL) j, mul_right_comm, ← zpow_add₀ hp, add_sub_cancel]

variable (C : CmpTie W E ιdR p1 tS zS)

theorem levB_smul (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (a : LetA O n) (x : ↥(W.N T)) :
    C.levB T i ζ (a • x) = smulS (W.lev i ζ a) (C.levB T i ζ x) := by
  funext k
  refine rk_ιV_inj PD (LL := LL) (V := T.V) ?_
  obtain ⟨m, hm⟩ := C.levB_supp T i ζ x
  rw [← C.levN_eq, smulS_linMap (ιV PD (LL := LL) (V := T.V)) hm, W.levN_smul]
  simp only [smulS, C.levN_eq]

theorem levB_add (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x y : ↥(W.N T)) :
    C.levB T i ζ (x + y) = C.levB T i ζ x + C.levB T i ζ y := map_add _ x y

theorem levB_sub (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x y : ↥(W.N T)) :
    C.levB T i ζ (x - y) = C.levB T i ζ x - C.levB T i ζ y := map_sub _ x y

theorem laurentBounded_zero_of_trivial_twist (hs : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {T : LocLat G Qp LL O}
    (h4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) (i : ZMod n) (x : ↥(W.N T)) : LB 0 (C.levB T i 1 x) := by
  intro k hk
  have hX : W.X = letπ := by simp [LocWach.X, hs]
  obtain ⟨F, hF0, -, hF⟩ := W.lev_π i 1 ⟨0, by simpa using IsPrimitiveRoot.one⟩
  have hcc : PowerSeries.constantCoeff (W.lev i 1 W.X) = 0 := by
    rw [hX]
    have := congrArg PowerSeries.constantCoeff hF
    rw [map_add, map_one, map_mul, PowerSeries.constantCoeff_C, hF0, one_mul] at this
    linear_combination this
  have h0 := ((h4.1 i 1 ⟨0, by simp⟩ hcc).1 x k).2 hk
  refine rk_ιV_inj PD (LL := LL) (V := T.V) ?_
  rw [← C.levN_eq, h0, map_zero]

theorem levB_γ1 (hs : W.s = 1) {T : LocLat G Qp LL O} (hT : IsCrys PD T.ρ) (i : ZMod n) (x : ↥(W.N T))
    (hx : W.γD T W.gam (x : W.DD T) ∈ W.N T) (k : ℤ) :
    C.levB T i 1 ⟨W.γD T W.gam (x : W.DD T), hx⟩ k =
      (algebraMap O LL (W.χΓ W.gam : O)) ^ k • C.levB T i 1 x k := by
  have hv : ((0 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ W.gam : O) - ((1 : ℕ) : LL)) := by
    rw [Nat.cast_one, W.gam_gen, hs]
    exact_mod_cast Nat.zero_le 1
  have := C.levB_Γ T hT W.gam i 1 1 0 1 (by simpa using IsPrimitiveRoot.one) hv (by simp) x hx k
  simpa using this

end Exp

section Chain

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    {W : LocWach PD LL O v n}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW}
    {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai} {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA}
    {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}

open Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.UnusedSlot80.SatW

variable (C : CmpTie W E ιdR p1 tS zS)

theorem rescale_ne_zero (hp : (PD.p : LL) ≠ 0) {f : PowerSeries LL} (hf : f ≠ 0) :
    PowerSeries.rescale (PD.p : LL) f ≠ 0 := by
  intro h
  apply hf
  ext j
  have := congrArg (PowerSeries.coeff j) h
  rw [PowerSeries.coeff_rescale, map_zero] at this
  simpa using (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hp)

theorem cc_levπ1 (i : ZMod n) : PowerSeries.constantCoeff (W.lev i 1 letπ) = 0 := by
  obtain ⟨F, hF0, -, hF⟩ := W.lev_π i 1 ⟨0, by simpa using IsPrimitiveRoot.one⟩
  have := congrArg PowerSeries.constantCoeff hF
  rw [map_add, map_one, map_mul, PowerSeries.constantCoeff_C, hF0, one_mul] at this
  linear_combination this

theorem cc_levπ₀1 (hR : RingA W) (h2 : 2 ≤ PD.p) (i : ZMod n) :
    PowerSeries.constantCoeff (W.lev i 1 W.π₀) = 0 := by
  obtain ⟨w, hw⟩ := hR.2.2.1
  rw [hw, map_mul, map_mul, map_pow, map_pow, cc_levπ1, zero_pow (by omega), mul_zero]

theorem levQ_ne (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hR : RingA W) (i : ZMod n) (ζ : LL)
    (hζ : ζ = 1 ∨ IsPrimitiveRoot ζ PD.p) : W.lev i ζ W.Q ≠ 0 := by
  have hs : W.s = 1 := hA.2.1
  have hp := p_ne_zero_LL W
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  rw [Eat_q] at hw
  have hQ : W.Q = (w : LetA O n) * Formalism.MainNotions.LiftingTheory.qp W := by rw [Q_eq_q hs, hw]; rfl
  rw [hQ, map_mul]
  refine mul_ne_zero ((w.isUnit.map (W.lev i ζ)).ne_zero) ?_
  rcases hζ with rfl | hζ
  · intro h0
    have := congrArg PowerSeries.constantCoeff h0
    have e : Formalism.MainNotions.LiftingTheory.qp W = W.π₀ + ((PD.p : ℕ) : LetA O n) := rfl
    rw [e, map_add, map_natCast, map_add, cc_levπ₀1 hR PD.hp.two_le, map_natCast, map_zero, zero_add] at this
    exact hp this
  · obtain ⟨⟨u, hu, he⟩, -, -⟩ := expRing_of W hR hA i ζ hζ
    rw [he]
    exact mul_ne_zero hu.ne_zero PowerSeries.X_ne_zero

theorem stepφ {T : LocLat G Qp LL O} (hT : IsCrys PD T.ρ) (i' : ZMod n) (ζ : LL) (hζ1 : ζ ^ PD.p = 1)
    (hζr : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) (hQ : W.lev (i' + 1) ζ W.Q ≠ 0)
    (hp : (PD.p : LL) ≠ 0) (y : W.DD T) (b : LetA O n) (hy : b • y ∈ W.N T) {m : ℤ}
    (d : ℤ → T.V ⊗[Qp] B) (hd : LB m d)
    (hE : C.levB T i' 1 ⟨b • y, hy⟩ = smulS (W.lev i' 1 b) d) (hb : W.lev i' 1 b ≠ 0) :
    ∃ (b' : LetA O n) (hb' : b' • W.φD T y ∈ W.N T), W.lev (i' + 1) ζ b' ≠ 0 ∧
      C.levB T (i' + 1) ζ ⟨_, hb'⟩ = smulS (W.lev (i' + 1) ζ b') (PhiSeq PD T d) := by
  obtain ⟨mq, hmq⟩ := W.N_φ T (b • y) hy
  have hmq' : W.Q ^ mq • W.φD T (b • y) ∈ W.N T := hmq
  have e1 : W.Q ^ mq • W.φD T (b • y) = (W.Q ^ mq * W.φA b) • W.φD T y := by
    rw [φD_smulA, mul_smul]
  have hb' : (W.Q ^ mq * W.φA b) • W.φD T y ∈ W.N T := e1 ▸ hmq'
  have hlevφ : W.lev (i' + 1) ζ (W.φA b) = PowerSeries.rescale (PD.p : LL) (W.lev i' 1 b) := by
    have := C.lev_φ (i' + 1) ζ hζr b
    rwa [add_sub_cancel_right, hζ1] at this
  refine ⟨W.Q ^ mq * W.φA b, hb', ?_, ?_⟩
  · rw [map_mul, hlevφ, map_pow]
    exact mul_ne_zero (pow_ne_zero _ hQ) (rescale_ne_zero hp hb)
  · have hsub : (⟨(W.Q ^ mq * W.φA b) • W.φD T y, hb'⟩ : ↥(W.N T)) = ⟨_, hmq'⟩ := Subtype.ext e1.symm
    rw [hsub]
    funext k
    have := C.levB_φ T hT (i' + 1) ζ hζr ⟨b • y, hy⟩ mq hmq' k
    rw [add_sub_cancel_right, hζ1] at this
    rw [this, map_mul, hlevφ, smulS_mul (LB_PhiSeq hd), ← PhiSeq_smulS hp hd, ← hE, map_pow]
    rfl

theorem LB_iter {T : LocLat G Qp LL O} {m : ℤ} {d : ℤ → T.V ⊗[Qp] B} (hd : LB m d) (j : ℕ) :
    LB m ((PhiSeq PD T)^[j] d) := by
  induction j with
  | zero => simpa using hd
  | succ j ih => rw [Function.iterate_succ_apply']; exact LB_PhiSeq ih

theorem chain1 (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hR : RingA W) {T : LocLat G Qp LL O} (hT : IsCrys PD T.ρ)
    (i : ZMod n) (x : ↥(W.N T)) (j : ℕ) :
    ∃ (b : LetA O n) (hb : b • ((W.φD T) ^ j) (x : W.DD T) ∈ W.N T), W.lev (i + j) 1 b ≠ 0 ∧
      C.levB T (i + j) 1 ⟨_, hb⟩ = smulS (W.lev (i + j) 1 b) ((PhiSeq PD T)^[j] (C.levB T i 1 x)) := by
  have hp := p_ne_zero_LL W
  obtain ⟨m, hm⟩ := C.levB_supp T i 1 x
  induction j with
  | zero =>
    refine ⟨1, by simpa using x.2, by simp, ?_⟩
    simp only [Nat.cast_zero, add_zero, Function.iterate_zero, id, map_one]
    rw [smulS_one hm]
    congr 1
    exact Subtype.ext (by simp)
  | succ j ih =>
    obtain ⟨b, hb, hb0, hE⟩ := ih
    have e : i + ((j + 1 : ℕ) : ZMod n) = i + j + 1 := by push_cast; ring
    have hφ : ((W.φD T) ^ (j + 1)) (x : W.DD T) = W.φD T (((W.φD T) ^ j) (x : W.DD T)) := by
      rw [pow_succ', Module.End.mul_apply]
    obtain ⟨b', hb', hb'0, hE'⟩ := stepφ C hT (i + j) 1 (one_pow _) ⟨0, by simpa using IsPrimitiveRoot.one⟩
      (levQ_ne hA hR _ 1 (Or.inl rfl)) hp _ b hb _ (LB_iter hm j) hE hb0
    rw [e, hφ]
    refine ⟨b', hb', hb'0, ?_⟩
    rw [hE', Function.iterate_succ_apply']

end Chain

section Chain2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    {W : LocWach PD LL O v n}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW}
    {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai} {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA}
    {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}

open Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.UnusedSlot80.SatW

variable (C : CmpTie W E ιdR p1 tS zS)

theorem chainζ (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hR : RingA W) {T : LocLat G Qp LL O} (hT : IsCrys PD T.ρ)
    (i : ZMod n) (x : ↥(W.N T)) (j' : ℕ) (ζ : LL) (hζ : ζ = 1 ∨ IsPrimitiveRoot ζ PD.p) :
    ∃ (b : LetA O n) (hb : b • ((W.φD T) ^ (j' + 1)) (x : W.DD T) ∈ W.N T),
      W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ b ≠ 0 ∧
      C.levB T (i + ((j' + 1 : ℕ) : ZMod n)) ζ ⟨_, hb⟩ =
        smulS (W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ b) ((PhiSeq PD T)^[j' + 1] (C.levB T i 1 x)) := by
  have hp := p_ne_zero_LL W
  obtain ⟨m, hm⟩ := C.levB_supp T i 1 x
  obtain ⟨b, hb, hb0, hE⟩ := chain1 C hA hR hT i x j'
  have hζ1 : ζ ^ PD.p = 1 := by
    rcases hζ with rfl | hζ
    · exact one_pow _
    · exact hζ.pow_eq_one
  have hζr : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j) := by
    rcases hζ with rfl | hζ
    · exact ⟨0, by simpa using IsPrimitiveRoot.one⟩
    · exact ⟨1, by rwa [pow_one]⟩
  have e : i + ((j' + 1 : ℕ) : ZMod n) = i + j' + 1 := by push_cast; ring
  have hφ : ((W.φD T) ^ (j' + 1)) (x : W.DD T) = W.φD T (((W.φD T) ^ j') (x : W.DD T)) := by
    rw [pow_succ', Module.End.mul_apply]
  obtain ⟨b', hb', hb'0, hE'⟩ := stepφ C hT (i + j') ζ hζ1 hζr (levQ_ne hA hR _ ζ hζ) hp _ b hb _
    (LB_iter hm j') hE hb0
  rw [e, hφ]
  refine ⟨b', hb', hb'0, ?_⟩
  rw [hE', Function.iterate_succ_apply']

theorem chain_mul {T : LocLat G Qp LL O} (i' : ZMod n) (ζ : LL) (y : W.DD T) (b₀ c : LetA O n)
    (hb₀ : b₀ • y ∈ W.N T) {m : ℤ} (D : ℤ → T.V ⊗[Qp] B) (hD : LB m D)
    (hE : C.levB T i' ζ ⟨b₀ • y, hb₀⟩ = smulS (W.lev i' ζ b₀) D) :
    ∃ h : (c * b₀) • y ∈ W.N T, C.levB T i' ζ ⟨(c * b₀) • y, h⟩ = smulS (W.lev i' ζ (c * b₀)) D := by
  have h : (c * b₀) • y ∈ W.N T := by rw [mul_smul]; exact Submodule.smul_mem _ _ hb₀
  refine ⟨h, ?_⟩
  have e : (⟨(c * b₀) • y, h⟩ : ↥(W.N T)) = c • (⟨b₀ • y, hb₀⟩ : ↥(W.N T)) := Subtype.ext (by
    simp only [SetLike.val_smul]; rw [mul_smul])
  rw [e, levB_smul, hE, map_mul, smulS_mul hD]

end Chain2

section SeqAlg

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

theorem smulS_sum {m : ℤ} (s : Finset ℕ) (f : ℕ → ℤ → V) (hf : ∀ y ∈ s, LB m (f y))
    (g : PowerSeries LL) : smulS g (∑ y ∈ s, f y) = ∑ y ∈ s, smulS g (f y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext k
    simp [smulS]
  | insert a s ha ih =>
    have hs : LB m (∑ y ∈ s, f y) := fun k hk => by
      rw [Finset.sum_apply]
      exact Finset.sum_eq_zero fun y hy => hf y (Finset.mem_insert_of_mem hy) k hk
    rw [Finset.sum_insert ha, Finset.sum_insert ha, smulS_add (hf a (Finset.mem_insert_self a s)) hs,
      ih fun y hy => hf y (Finset.mem_insert_of_mem hy)]

theorem LB_sum {m : ℤ} (s : Finset ℕ) (f : ℕ → ℤ → V) (hf : ∀ y ∈ s, LB m (f y)) :
    LB m (∑ y ∈ s, f y) := fun k hk => by
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero fun y hy => hf y hy k hk

theorem LB_smulS_X {m : ℤ} {f : ℤ → V} (hf : LB m f) (e : ℕ) (g : PowerSeries LL) :
    LB (m + e) (smulS (PowerSeries.X ^ e * g) f) := by
  rw [smulS_mul hf, smulS_X_pow (LB_smulS hf g)]
  intro k hk
  exact LB_smulS hf g _ (by omega)

theorem smulS_single (g : PowerSeries LL) (c : V) (r : ℕ) :
    smulS g (Pi.single (0 : ℤ) c) (r : ℤ) = PowerSeries.coeff r g • c := by
  have hL : LB 0 (Pi.single (0 : ℤ) c : ℤ → V) := fun k hk => by
    rw [Pi.single_apply, if_neg (by omega)]
  rw [smulS_eq_sum hL g r (r + 1) (by omega), Finset.sum_eq_single r]
  · simp
  · intro b _ hb
    rw [Pi.single_apply, if_neg (by omega), smul_zero]
  · intro h; exact absurd (Finset.self_mem_range_succ r) h

end SeqAlg

section KeyJ

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    {W : LocWach PD LL O v n}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW}
    {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai} {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA}
    {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}

open Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.UnusedSlot80.SatW

theorem key_idJ {T : LocLat G Qp LL O} (Φ : W.DD T →ₗ[O] W.DD T) (ψ : LetA O n →ₐ[O] LetA O n)
    (hΦ : ∀ (a : LetA O n) (x : W.DD T), Φ (a • x) = ψ a • Φ x)
    (σ J K : ℕ) (e : ℕ → ℕ) (he : ∀ y ∈ Finset.range K, e y ≤ J)
    (w : W.DD T) (cc : ℕ → W.DD T) (r s : ℕ → LetA O n)
    (hrs : ∀ y, ((PD.p : ℕ) : LetA O n) ^ e y * s y = ((PD.p : ℕ) : LetA O n) ^ σ * r y) :
    ((PD.p : ℕ) : LetA O n) ^ J • (((PD.p : ℕ) : O) ^ σ • Φ w -
        ∑ y ∈ Finset.range K, s y • Φ (cc y)) =
      ((PD.p : ℕ) : LetA O n) ^ σ • Φ (((PD.p : ℕ) : LetA O n) ^ J • w -
        ∑ y ∈ Finset.range K, ((PD.p : ℕ) : LetA O n) ^ (J - e y) • (W.π₀ ^ y • cc y)) +
      ∑ y ∈ Finset.range K, ((PD.p : ℕ) : LetA O n) ^ (σ + (J - e y)) •
        ((ψ W.π₀ ^ y - r y) • Φ (cc y)) := by
  set L : LetA O n := ((PD.p : ℕ) : LetA O n)
  have hΦL : ∀ (k : ℕ) (x : W.DD T), Φ (L ^ k • x) = L ^ k • Φ x := fun k x => by
    rw [hΦ, map_pow, map_natCast]
  have hφ : ∀ y, Φ (L ^ (J - e y) • (W.π₀ ^ y • cc y)) =
      L ^ (J - e y) • (ψ W.π₀ ^ y • Φ (cc y)) := fun y => by
    rw [hΦL, hΦ, map_pow]
  have ht : ∀ y ∈ Finset.range K, L ^ J • (s y • Φ (cc y)) =
      L ^ (σ + (J - e y)) • (r y • Φ (cc y)) := by
    intro y hy
    rw [smul_smul, smul_smul]
    congr 1
    calc L ^ J * s y = L ^ (J - e y) * (L ^ e y * s y) := by
          rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (he y hy)]
      _ = L ^ (σ + (J - e y)) * r y := by rw [hrs y, pow_add]; ring
  have hs : ∀ y ∈ Finset.range K, L ^ (σ + (J - e y)) • ((ψ W.π₀ ^ y - r y) • Φ (cc y)) =
      L ^ σ • (L ^ (J - e y) • (ψ W.π₀ ^ y • Φ (cc y))) -
        L ^ (σ + (J - e y)) • (r y • Φ (cc y)) := by
    intro y _
    rw [sub_smul, smul_sub, smul_smul (L ^ σ), ← pow_add]
  rw [lO_smul, map_sub, map_sum, hΦL, Finset.sum_congr rfl fun y _ => hφ y, smul_sub, smul_sub,
    Finset.smul_sum, Finset.smul_sum, Finset.sum_congr rfl ht, Finset.sum_congr rfl hs,
    Finset.sum_sub_distrib, smul_smul, smul_smul, mul_comm (L ^ J)]
  abel

theorem φpow_smulA {T : LocLat G Qp LL O} (j : ℕ) (a : LetA O n) (x : W.DD T) :
    ((W.φD T) ^ j) (a • x) = (W.φA ^ j) a • ((W.φD T) ^ j) x := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, φD_smulA, pow_succ', AlgHom.mul_apply,
      Module.End.mul_apply]

variable (C : CmpTie W E ιdR p1 tS zS)

theorem smulSeries_apply_zero {V : Type} [AddCommGroup V] [Module LL V] {f : ℤ → V} (hf : LB 0 f)
    (g : PowerSeries LL) : smulS g f 0 = PowerSeries.constantCoeff g • f 0 := by
  rw [smulS_eq_sum hf g 0 1 (by omega)]
  simp

theorem levπ₀_dvd (hR : RingA W) (i : ZMod n) :
    ∃ g : PowerSeries LL, W.lev i 1 W.π₀ = PowerSeries.X ^ (PD.p - 1) * g := by
  obtain ⟨w, hw⟩ := hR.2.2.1
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.2 (cc_levπ1 (W := W) i)
  refine ⟨W.lev i 1 (w : LetA O n) * g ^ (PD.p - 1), ?_⟩
  rw [hw, map_mul, map_pow, hg, mul_pow]
  ring

theorem expH (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hR : RingA W) (hinj : Function.Injective (algebraMap O LL))
    (hχ : ∀ N : ℕ, 0 < N → (((W.χΓ W.gam) ^ N : Oˣ) : O) ≠ 1)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {T : LocLat G Qp LL O} (h4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hT : IsCrys PD T.ρ) (i : ZMod n) (K : ℕ) (w : W.DD T) (hw : w ∈ W.N T)
    (hDL : (letE i : LetA O n) • w = w) (cc : ℕ → W.DD T) (hc0 : cc 0 = 0) (hcc : ∀ y, cc y ∈ W.N T)
    (J : ℕ) (e : ℕ → ℕ) (h : W.DD T)
    (hh : h = ((PD.p : ℕ) : LetA O n) ^ J • w -
      ∑ y ∈ Finset.range K, ((PD.p : ℕ) : LetA O n) ^ (J - e y) • (W.π₀ ^ y • cc y))
    (hhN : h ∈ W.N T) (ν : W.DD T) (hν : ν ∈ W.N T) (hγh : W.γ T h - h = W.π₀ ^ K • ν) :
    LB 0 (C.levB T i 1 ⟨h, hhN⟩) ∧
      (∀ k : ℤ, 0 < k → k < ((PD.p - 1) * K : ℕ) → C.levB T i 1 ⟨h, hhN⟩ k = 0) ∧
      C.levB T i 1 ⟨h, hhN⟩ 0 = (PD.p : LL) ^ J • W.cmp T ⟨w, hw⟩ := by
  have hs : W.s = 1 := hA.2.1
  refine ⟨laurentBounded_zero_of_trivial_twist C hs h4 i _, fun k hk0 hkK => ?_, ?_⟩
  · have hγN : W.γD T W.gam h ∈ W.N T := W.N_Γ T _ h hhN
    have hsub : (⟨W.γD T W.gam h, hγN⟩ : ↥(W.N T)) - ⟨h, hhN⟩ = W.π₀ ^ K • (⟨ν, hν⟩ : ↥(W.N T)) :=
      Subtype.ext hγh
    have e2 := congrFun (congrArg (C.levB T i 1) hsub) k
    rw [levB_sub, levB_smul, Pi.sub_apply, levB_γ1 C hs hT i ⟨h, hhN⟩ hγN] at e2
    obtain ⟨g, hg⟩ := levπ₀_dvd hR i
    have hz : smulS (W.lev i 1 (W.π₀ ^ K)) (C.levB T i 1 ⟨ν, hν⟩) k = 0 := by
      rw [map_pow, hg, mul_pow, ← pow_mul]
      exact LB_smulS_X (laurentBounded_zero_of_trivial_twist C hs h4 i _) _ _ k (by push_cast at hkK ⊢; omega)
    rw [hz, ← one_smul LL (C.levB T i 1 ⟨h, hhN⟩ k), smul_smul, mul_one, ← sub_smul] at e2
    rcases smul_eq_zero.1 e2 with h1 | h1
    · exfalso
      have hk' : k = (k.toNat : ℤ) := (Int.toNat_of_nonneg hk0.le).symm
      rw [hk', zpow_natCast, ← map_pow, sub_eq_zero] at h1
      apply hχ k.toNat (by omega)
      apply hinj
      rw [Units.val_pow_eq_pow_val, h1, map_one]
    · exact h1
  · have hhsub : (⟨h, hhN⟩ : ↥(W.N T)) = ((PD.p : ℕ) : LetA O n) ^ J • (⟨w, hw⟩ : ↥(W.N T)) -
        ∑ y ∈ Finset.range K, (((PD.p : ℕ) : LetA O n) ^ (J - e y) * W.π₀ ^ y) •
          (⟨cc y, hcc y⟩ : ↥(W.N T)) := by
      apply Subtype.ext
      simp only [hh, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_sum, smul_smul]
    rw [hhsub, levB_sub, map_sum, Pi.sub_apply, Finset.sum_apply, levB_smul,
      smulSeries_apply_zero (laurentBounded_zero_of_trivial_twist C hs h4 i _)]
    have h0 : ∀ y ∈ Finset.range K, C.levB T i 1 ((((PD.p : ℕ) : LetA O n) ^ (J - e y) * W.π₀ ^ y) •
        (⟨cc y, hcc y⟩ : ↥(W.N T))) 0 = 0 := by
      intro y _
      rcases Nat.eq_zero_or_pos y with rfl | hy
      · have : (⟨cc 0, hcc 0⟩ : ↥(W.N T)) = 0 := Subtype.ext hc0
        rw [this, smul_zero, map_zero, Pi.zero_apply]
      · rw [levB_smul, smulSeries_apply_zero (laurentBounded_zero_of_trivial_twist C hs h4 i _), map_mul, map_mul, map_pow (W.lev i 1) W.π₀ y,
          map_pow PowerSeries.constantCoeff, cc_levπ₀1 hR PD.hp.two_le, zero_pow (by omega), mul_zero,
          zero_smul]
    rw [Finset.sum_eq_zero h0, sub_zero, map_pow, map_pow, map_natCast]
    have hlet : (letE i : LetA O n) • (⟨w, hw⟩ : ↥(W.N T)) = ⟨w, hw⟩ := Subtype.ext hDL
    rw [← C.cmp_eq T hT i, hlet]
    simp

end KeyJ

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    {W : LocWach PD LL O v n}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW}
    {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai} {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA}
    {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}

open Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.UnusedSlot80.SatW

variable (C : CmpTie W E ιdR p1 tS zS)

theorem smulS_lpow {V : Type} [AddCommGroup V] [Module LL V] (i : ZMod n) (ζ : LL) (m : ℕ) {b : ℤ}
    {f : ℤ → V} (hf : LB b f) :
    smulS (W.lev i ζ (((PD.p : ℕ) : LetA O n) ^ m)) f = (PD.p : LL) ^ m • f := by
  rw [map_pow, map_natCast]
  have e : ((PD.p : ℕ) : PowerSeries LL) = PowerSeries.C (PD.p : LL) := by simp
  rw [e, ← map_pow, smulS_C hf]

theorem PhiSeq_add {T : LocLat G Qp LL O} (f g : ℤ → T.V ⊗[Qp] B) :
    PhiSeq PD T (f + g) = PhiSeq PD T f + PhiSeq PD T g := by
  funext k; simp [PhiSeq, smul_add]

theorem iter_add {T : LocLat G Qp LL O} (j : ℕ) (f g : ℤ → T.V ⊗[Qp] B) :
    (PhiSeq PD T)^[j] (f + g) = (PhiSeq PD T)^[j] f + (PhiSeq PD T)^[j] g := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, PhiSeq_add]

theorem iter_single {T : LocLat G Qp LL O} (j : ℕ) (c : T.V ⊗[Qp] B) :
    (PhiSeq PD T)^[j] (Pi.single (0 : ℤ) c) = Pi.single (0 : ℤ) ((φVB PD (LL := LL) (V := T.V))^[j] c) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    funext k
    by_cases hk : k = 0
    · subst hk; simp [PhiSeq]
    · simp [PhiSeq, Pi.single_apply, hk]

theorem tHor_of (Ct : CmpTie W E ιdR p1 tS zS) (hinj : Function.Injective (algebraMap O LL))
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hχ : Formalism.MainNotions.LiftingTheory.CaseA W → ∀ N : ℕ, 0 < N → (((W.χΓ W.gam) ^ N : Oˣ) : O) ≠ 1) :
    THor W := by
  intro hA hl j M X σ hc T hT i w z hw hwI htr ζ R k a hk hζR
  have hs : W.s = 1 := hA.2.1
  have hp := p_ne_zero_LL W
  obtain ⟨hR, -⟩ := (h9 T hT hA.2.1 hA.2.2).2.2 (finrank_one_of_bij hA.1)
  have hj1 : 1 ≤ j := by rcases hc with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;> omega
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hζ : ζ = 1 ∨ IsPrimitiveRoot ζ PD.p := hζR.elim (fun h => Or.inr h.1) (fun h => Or.inl h.1)
  obtain ⟨hDL, -, -⟩ := hwI
  obtain ⟨cc, r, s, ⟨hc0, hcc, hser⟩, hrs, hz⟩ := htr
  obtain ⟨jj, ν, hν, -, hνe⟩ := hser (max M X + 1)
  have hl1 : (0 : ℝ) ≤ (PD.p : ℝ) - 1 := by
    have : (11 : ℝ) ≤ PD.p := by exact_mod_cast hl
    linarith
  have heK : ∀ y ∈ Finset.range (max M X + 1), eY PD.p y ≤ eY PD.p (max M X + 1) := by
    intro y hy
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_right _ hl1
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (Finset.mem_range.1 hy).le
  have hJe : ∀ y ∈ Finset.range (max M X + 1), eY PD.p y ≤ jj + eY PD.p (max M X + 1) :=
    fun y hy => (heK y hy).trans (Nat.le_add_left _ _)
  obtain ⟨h, hhdef⟩ : ∃ h : W.DD T, h = ((PD.p : ℕ) : LetA O n) ^ (jj + eY PD.p (max M X + 1)) • w -
      ∑ y ∈ Finset.range (max M X + 1), ((PD.p : ℕ) : LetA O n) ^
        (jj + eY PD.p (max M X + 1) - eY PD.p y) • (W.π₀ ^ y • cc y) := ⟨_, rfl⟩
  have hhN : h ∈ W.N T := by
    rw [hhdef]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hw) (Submodule.sum_mem _ fun y _ =>
      Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hcc y).2))
  have hγh : W.γ T h - h = W.π₀ ^ (max M X + 1) • ν := by
    have hs' : ∀ y ∈ Finset.range (max M X + 1),
        jj + (eY PD.p (max M X + 1) - eY PD.p y) = jj + eY PD.p (max M X + 1) - eY PD.p y :=
      fun y hy => by have := heK y hy; omega
    rw [← hνe, hhdef, lin_id (W.γ T) γ'_lA, natCast_pow_smul_sub_sum_eq, p_power_smul_sub_sum]
    congr 1
    exact Finset.sum_congr rfl fun y hy => by rw [hs' y hy]
  obtain ⟨hEh0, hEhK, hEh00⟩ := expH Ct hA hR hinj (hχ hA) (h4 T hT) hT i (max M X + 1) w hw hDL.1 cc hc0
    (fun y => (hcc y).2) (jj + eY PD.p (max M X + 1)) (eY PD.p) h hhdef hhN ν hν hγh
  have hφiter : ∀ (m : ℕ) (c : LL) (x : T.V ⊗[Qp] B),
      (φVB PD (LL := LL) (V := T.V))^[m] (c • x) = c • (φVB PD (LL := LL) (V := T.V))^[m] x := by
    intro m c x
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, map_smul, Function.iterate_succ_apply']
  obtain ⟨bh, hbh, hbh0, hEh'⟩ := chainζ Ct hA hR hT i ⟨h, hhN⟩ j' ζ hζ
  choose bc hbc hbc0 hEc using fun y => chainζ Ct hA hR hT i ⟨cc y, (hcc y).2⟩ j' ζ hζ
  obtain ⟨Bb, hBb⟩ : ∃ Bb : LetA O n, Bb = (∏ y ∈ Finset.range (max M X + 1), bc y) * bh := ⟨_, rfl⟩
  have hBb0 : W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ Bb ≠ 0 := by
    rw [hBb, map_mul, map_prod]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun y _ => hbc0 y) hbh0
  obtain ⟨hBh, hEBh⟩ : ∃ hB : Bb • ((W.φD T) ^ (j' + 1)) h ∈ W.N T,
      Ct.levB T (i + ((j' + 1 : ℕ) : ZMod n)) ζ ⟨_, hB⟩ =
        smulS (W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ Bb)
          ((PhiSeq PD T)^[j' + 1] (Ct.levB T i 1 ⟨h, hhN⟩)) := by
    rw [hBb]
    exact chain_mul Ct (i + ((j' + 1 : ℕ) : ZMod n)) ζ (((W.φD T) ^ (j' + 1)) h) bh
      (∏ y ∈ Finset.range (max M X + 1), bc y) hbh _ (LB_iter hEh0 _) hEh'
  have hΦc : ∀ y, LB 0 ((PhiSeq PD T)^[j' + 1] (Ct.levB T i 1 ⟨cc y, (hcc y).2⟩)) :=
    fun y => LB_iter (laurentBounded_zero_of_trivial_twist Ct hs (h4 T hT) i _) _
  have hΦh : LB 0 ((PhiSeq PD T)^[j' + 1] (Ct.levB T i 1 ⟨h, hhN⟩)) := LB_iter hEh0 _
  have hBc : ∀ y ∈ Finset.range (max M X + 1), ∃ hB : Bb • ((W.φD T) ^ (j' + 1)) (cc y) ∈ W.N T,
      Ct.levB T (i + ((j' + 1 : ℕ) : ZMod n)) ζ ⟨_, hB⟩ =
        smulS (W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ Bb)
          ((PhiSeq PD T)^[j' + 1] (Ct.levB T i 1 ⟨cc y, (hcc y).2⟩)) := by
    intro y hy
    have e : Bb = ((∏ y' ∈ (Finset.range (max M X + 1)).erase y, bc y') * bh) * bc y := by
      rw [hBb, ← Finset.prod_erase_mul _ _ hy]; ring
    rw [e]
    exact chain_mul Ct _ ζ _ (bc y) _ (hbc y) _ (hΦc y) (hEc y)
  have hkey := key_idJ ((W.φD T) ^ (j' + 1)) (W.φA ^ (j' + 1)) (φpow_smulA (j' + 1)) σ
    (jj + eY PD.p (max M X + 1)) (max M X + 1) (eY PD.p) hJe w cc r s (fun y => (hrs y).2)
  rw [← hz, ← hhdef] at hkey
  let xcF : ℕ → ↥(W.N T) := fun y => if hy : y ∈ Finset.range (max M X + 1) then
    ⟨Bb • ((W.φD T) ^ (j' + 1)) (cc y), (hBc y hy).1⟩ else 0
  have hxcF : ∀ y ∈ Finset.range (max M X + 1), (xcF y : W.DD T) = Bb • ((W.φD T) ^ (j' + 1)) (cc y) :=
    fun y hy => by simp only [xcF, dif_pos hy]
  have hLxc : ∀ y ∈ Finset.range (max M X + 1), Ct.levB T (i + ((j' + 1 : ℕ) : ZMod n)) ζ (xcF y) =
      smulS (W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ Bb)
        ((PhiSeq PD T)^[j' + 1] (Ct.levB T i 1 ⟨cc y, (hcc y).2⟩)) :=
    fun y hy => by simp only [xcF, dif_pos hy]; exact (hBc y hy).2
  let U : ↥(W.N T) := (Formalism.MainNotions.LiftingTheory.qp W ^ k * a) • (((PD.p : ℕ) : LetA O n) ^ σ •
      (⟨Bb • ((W.φD T) ^ (j' + 1)) h, hBh⟩ : ↥(W.N T)) +
    ∑ y ∈ Finset.range (max M X + 1), (((PD.p : ℕ) : LetA O n) ^ (σ + (jj + eY PD.p (max M X + 1) -
      eY PD.p y)) * ((W.φA ^ (j' + 1)) W.π₀ ^ y - r y)) • xcF y)
  have hU : (Bb * ((PD.p : ℕ) : LetA O n) ^ (jj + eY PD.p (max M X + 1))) •
      (⟨(Formalism.MainNotions.LiftingTheory.qp W ^ k * a) • z, hk⟩ : ↥(W.N T)) = U := by
    apply Subtype.ext
    simp only [U, Submodule.coe_smul, Submodule.coe_add, Submodule.coe_sum]
    rw [Finset.sum_congr rfl fun y hy => by rw [hxcF y hy]]
    have e1 : (Bb * ((PD.p : ℕ) : LetA O n) ^ (jj + eY PD.p (max M X + 1))) •
        ((Formalism.MainNotions.LiftingTheory.qp W ^ k * a) • z) = (Formalism.MainNotions.LiftingTheory.qp W ^ k * a) •
          (Bb • (((PD.p : ℕ) : LetA O n) ^ (jj + eY PD.p (max M X + 1)) • z)) := by
      rw [smul_smul, smul_smul, smul_smul]; congr 1; ring
    rw [e1, hkey, smul_add, smul_comm Bb (((PD.p : ℕ) : LetA O n) ^ σ), Finset.smul_sum]
    congr 2
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [smul_smul, smul_smul, smul_smul]; congr 1; ring
  obtain ⟨mZ, hmZ⟩ := Ct.levB_supp T (i + ((j' + 1 : ℕ) : ZMod n)) ζ ⟨(Formalism.MainNotions.LiftingTheory.qp W ^ k * a) • z, hk⟩
  obtain ⟨Stuff, hStuff⟩ : ∃ S : ℤ → T.V ⊗[Qp] B, S =
      smulS (W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ (((PD.p : ℕ) : LetA O n) ^ σ))
        ((PhiSeq PD T)^[j' + 1] (Ct.levB T i 1 ⟨h, hhN⟩)) +
      ∑ y ∈ Finset.range (max M X + 1), smulS (W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ
        (((PD.p : ℕ) : LetA O n) ^ (σ + (jj + eY PD.p (max M X + 1) - eY PD.p y)) *
          ((W.φA ^ (j' + 1)) W.π₀ ^ y - r y)))
        ((PhiSeq PD T)^[j' + 1] (Ct.levB T i 1 ⟨cc y, (hcc y).2⟩)) := ⟨_, rfl⟩
  have hSumLB : LB 0 (∑ y ∈ Finset.range (max M X + 1), smulS (W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ
        (((PD.p : ℕ) : LetA O n) ^ (σ + (jj + eY PD.p (max M X + 1) - eY PD.p y)) *
          ((W.φA ^ (j' + 1)) W.π₀ ^ y - r y)))
        ((PhiSeq PD T)^[j' + 1] (Ct.levB T i 1 ⟨cc y, (hcc y).2⟩))) :=
    LB_sum _ _ fun y _ => LB_smulS (hΦc y) _
  have hStuffLB : LB 0 Stuff := by rw [hStuff]; exact LB_add (LB_smulS hΦh _) hSumLB
  have hlev1 : Ct.levB T (i + ((j' + 1 : ℕ) : ZMod n)) ζ
      ((Bb * ((PD.p : ℕ) : LetA O n) ^ (jj + eY PD.p (max M X + 1))) •
        (⟨(Formalism.MainNotions.LiftingTheory.qp W ^ k * a) • z, hk⟩ : ↥(W.N T))) =
      smulS (W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ Bb)
        (smulS (W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ (((PD.p : ℕ) : LetA O n) ^ (jj + eY PD.p (max M X + 1))))
          (Ct.levB T (i + ((j' + 1 : ℕ) : ZMod n)) ζ ⟨(Formalism.MainNotions.LiftingTheory.qp W ^ k * a) • z, hk⟩)) := by
    rw [levB_smul, map_mul, smulS_mul hmZ]
  have hlev2 : Ct.levB T (i + ((j' + 1 : ℕ) : ZMod n)) ζ U =
      smulS (W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ Bb)
        (smulS (W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ (Formalism.MainNotions.LiftingTheory.qp W ^ k * a)) Stuff) := by
    simp only [U]
    rw [levB_smul, levB_add, map_sum, levB_smul, hEBh,
      Finset.sum_congr rfl fun y hy => by rw [levB_smul, hLxc y hy]]
    rw [smulS_comm hΦh, Finset.sum_congr rfl fun y _ => smulS_comm (hΦc y) _ _,
      ← smulS_sum _ _ (fun y _ => LB_smulS (hΦc y) _),
      ← smulS_add (LB_smulS hΦh _) hSumLB, ← hStuff, smulS_comm hStuffLB]
  have heq := smulS_inj (LB_mono (LB_smulS hmZ _) (min_le_left mZ 0))
    (LB_mono (LB_smulS hStuffLB _) (min_le_right mZ 0)) _ hBb0 (by rw [← hlev1, hU, hlev2])
  rw [smulS_lpow _ _ _ hmZ] at heq
  have hK1 : 1 ≤ PD.p - 1 := by omega
  obtain ⟨R₀, hF1, hF2, hF3⟩ : ∃ R₀ : ℕ, R₀ ≤ (PD.p - 1) * (max M X + 1) ∧
      (∀ y, ∃ g : PowerSeries LL, W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ
        (((PD.p : ℕ) : LetA O n) ^ (σ + (jj + eY PD.p (max M X + 1) - eY PD.p y)) *
          ((W.φA ^ (j' + 1)) W.π₀ ^ y - r y)) = PowerSeries.X ^ R₀ * g) ∧
      (∀ Er : ℤ → T.V ⊗[Qp] B, LB (R₀ : ℤ) Er → ∀ r : ℕ, r < R →
        smulS (W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ (Formalism.MainNotions.LiftingTheory.qp W ^ k * a)) Er r = 0) := by
    rcases hζR with ⟨hprim, hRd⟩ | ⟨hz1, hRd⟩
    · obtain ⟨⟨u, -, hqp⟩, -, -⟩ := expRing_of W hR hA (i + ((j' + 1 : ℕ) : ZMod n)) ζ hprim
      refine ⟨X, ?_, fun y => ?_, fun Er hEr r hr => ?_⟩
      · calc X ≤ max M X + 1 := by omega
          _ ≤ (PD.p - 1) * (max M X + 1) := Nat.le_mul_of_pos_left _ (by omega)
      · obtain ⟨-, g, hg⟩ := (hrs y).1
        refine ⟨W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ (((PD.p : ℕ) : LetA O n) ^
          (σ + (jj + eY PD.p (max M X + 1) - eY PD.p y))) * W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ W.π₀ ^ M *
          u ^ X * W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ g, ?_⟩
        rw [map_mul, hg, fMX]
        simp only [map_mul, map_pow, hqp]
        ring
      · rw [map_mul, map_pow, hqp, mul_pow, mul_comm (u ^ k), mul_assoc]
        exact LB_smulS_X hEr k _ r (by push_cast; omega)
    · subst hz1
      obtain ⟨g₁, hg₁⟩ := levπ₀_dvd hR (i + ((j' + 1 : ℕ) : ZMod n))
      refine ⟨(PD.p - 1) * M, Nat.mul_le_mul le_rfl (by omega), fun y => ?_, fun Er hEr r hr => ?_⟩
      · obtain ⟨-, g, hg⟩ := (hrs y).1
        refine ⟨W.lev (i + ((j' + 1 : ℕ) : ZMod n)) 1 (((PD.p : ℕ) : LetA O n) ^
          (σ + (jj + eY PD.p (max M X + 1) - eY PD.p y))) * g₁ ^ M *
          W.lev (i + ((j' + 1 : ℕ) : ZMod n)) 1 (Formalism.MainNotions.LiftingTheory.qp W) ^ X *
          W.lev (i + ((j' + 1 : ℕ) : ZMod n)) 1 g, ?_⟩
        rw [map_mul, hg, fMX]
        simp only [map_mul, map_pow, hg₁]
        ring
      · exact LB_smulS hEr _ r (by push_cast; omega)
  have hEh'LB : LB (((PD.p - 1) * (max M X + 1) : ℕ) : ℤ) (Ct.levB T i 1 ⟨h, hhN⟩ -
      Pi.single (0 : ℤ) ((PD.p : LL) ^ (jj + eY PD.p (max M X + 1)) • W.cmp T ⟨w, hw⟩)) := by
    intro kk hkk
    rw [Pi.sub_apply]
    rcases lt_trichotomy kk 0 with hk0 | rfl | hk0
    · rw [hEh0 kk hk0, Pi.single_apply, if_neg (ne_of_lt hk0), sub_zero]
    · rw [hEh00, Pi.single_eq_same, sub_self]
    · rw [hEhK kk hk0 hkk, Pi.single_apply, if_neg (ne_of_gt hk0), sub_zero]
  have hpt : ∀ kk : ℤ, kk < R₀ → Stuff kk = (Pi.single (0 : ℤ)
      ((PD.p : LL) ^ σ • ((PD.p : LL) ^ (jj + eY PD.p (max M X + 1)) •
        (φVB PD (LL := LL) (V := T.V))^[j' + 1] (W.cmp T ⟨w, hw⟩))) : ℤ → T.V ⊗[Qp] B) kk := by
    intro kk hkk
    have hSig : (∑ y ∈ Finset.range (max M X + 1), smulS (W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ
        (((PD.p : ℕ) : LetA O n) ^ (σ + (jj + eY PD.p (max M X + 1) - eY PD.p y)) *
          ((W.φA ^ (j' + 1)) W.π₀ ^ y - r y)))
        ((PhiSeq PD T)^[j' + 1] (Ct.levB T i 1 ⟨cc y, (hcc y).2⟩))) kk = 0 := by
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun y _ => ?_
      obtain ⟨g, hg⟩ := hF2 y
      rw [hg]
      exact LB_smulS_X (hΦc y) R₀ g kk (by push_cast; omega)
    have hdec : Ct.levB T i 1 ⟨h, hhN⟩ = Pi.single (0 : ℤ) ((PD.p : LL) ^ (jj + eY PD.p (max M X + 1)) •
        W.cmp T ⟨w, hw⟩) + (Ct.levB T i 1 ⟨h, hhN⟩ - Pi.single (0 : ℤ) ((PD.p : LL) ^
          (jj + eY PD.p (max M X + 1)) • W.cmp T ⟨w, hw⟩)) := (add_sub_cancel _ _).symm
    rw [hStuff, Pi.add_apply, hSig, add_zero, smulS_lpow _ _ _ hΦh, Pi.smul_apply, hdec, iter_add,
      iter_single, Pi.add_apply, LB_iter hEh'LB _ kk (lt_of_lt_of_le hkk (by exact_mod_cast hF1)), add_zero, hφiter]
    by_cases h0 : kk = 0
    · subst h0; simp
    · simp [Pi.single_apply, h0]
  have hErr : LB (R₀ : ℤ) (Stuff - Pi.single (0 : ℤ)
      ((PD.p : LL) ^ σ • ((PD.p : LL) ^ (jj + eY PD.p (max M X + 1)) •
        (φVB PD (LL := LL) (V := T.V))^[j' + 1] (W.cmp T ⟨w, hw⟩)))) := fun kk hkk => by
    rw [Pi.sub_apply, hpt kk hkk, sub_self]
  have hsingLB : LB 0 (Pi.single (0 : ℤ)
      ((PD.p : LL) ^ σ • ((PD.p : LL) ^ (jj + eY PD.p (max M X + 1)) •
        (φVB PD (LL := LL) (V := T.V))^[j' + 1] (W.cmp T ⟨w, hw⟩))) : ℤ → T.V ⊗[Qp] B) := fun kk hkk => by
    rw [Pi.single_apply, if_neg (by omega)]
  have hpos : ∀ r : ℕ, r < R → Ct.levB T (i + ((j' + 1 : ℕ) : ZMod n)) ζ
      ⟨(Formalism.MainNotions.LiftingTheory.qp W ^ k * a) • z, hk⟩ r =
      PowerSeries.coeff r (W.lev (i + ((j' + 1 : ℕ) : ZMod n)) ζ (Formalism.MainNotions.LiftingTheory.qp W ^ k * a)) •
        ((PD.p : LL) ^ σ • (φVB PD (LL := LL) (V := T.V))^[j' + 1] (W.cmp T ⟨w, hw⟩)) := by
    intro r hr
    have h1 := congrFun heq r
    rw [Pi.smul_apply, ← add_sub_cancel (Pi.single (0 : ℤ)
      ((PD.p : LL) ^ σ • ((PD.p : LL) ^ (jj + eY PD.p (max M X + 1)) •
        (φVB PD (LL := LL) (V := T.V))^[j' + 1] (W.cmp T ⟨w, hw⟩)))) Stuff,
      smulS_add hsingLB (LB_mono hErr (by omega)), Pi.add_apply, smulS_single, hF3 _ hErr r hr,
      add_zero] at h1
    apply smul_right_injective _ (pow_ne_zero (jj + eY PD.p (max M X + 1)) hp)
    simp only
    rw [h1, smul_comm ((PD.p : LL) ^ σ), smul_comm (PowerSeries.coeff r _)]
  have hneg : ∀ r : ℤ, r < 0 → Ct.levB T (i + ((j' + 1 : ℕ) : ZMod n)) ζ
      ⟨(Formalism.MainNotions.LiftingTheory.qp W ^ k * a) • z, hk⟩ r = 0 := by
    intro r hr
    have h1 := congrFun heq r
    rw [Pi.smul_apply, LB_smulS hStuffLB _ r hr] at h1
    exact (smul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hp)
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · rw [Ct.levN_eq, hneg r hr, map_zero]
  · rw [Ct.levN_eq, hpos r hr, map_smul, map_smul]

end Main

section Rows

open Formalism.MainNotions.UnusedSlot80

theorem frobenius_power_congruence_local (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h1 : Formalism.MainNotions.RamifiedCoefficientChains.adm1 D HW F Cm) : FrobeniusExpansionCongruence D HW F Cm := by
  intro l _ K LL hg _
  exact tHor_of ((Cm l).C K 1 LL hg).tie Subtype.val_injective (h1 l K 1 LL hg).2.2.2.1
    (h1 l K 1 LL hg).2.2.2.2.2.2.2.2.1
    (fun hCA => χ_pow_ne_one (RToolNum_holds (D.loc l) (HW l) K LL hg hCA))

theorem frobenius_power_congruence_of_admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    {CR CA CB CK : ℝ} (hA : Formalism.MainNotions.RamifiedCoefficientChains.admitted D HW F Cm CR CA CB CK) : FrobeniusExpansionCongruence D HW F Cm :=
  frobenius_power_congruence_local D HW F Cm hA.1

end Rows

end Formalism.MainNotions.CrystallineLiftingInputs.Tools
