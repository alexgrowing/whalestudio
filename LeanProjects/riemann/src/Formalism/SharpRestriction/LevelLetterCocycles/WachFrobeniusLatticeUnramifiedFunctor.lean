import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller
import Formalism.SharpRestriction.LevelLetterCocycles.SecondComparisonInCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.LiftFOf
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.GoodOf

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

namespace WachFrobeniusLattice

section LatD

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

def DV (_I : BaseId W) (T : LocLat G Qp LL O) : Type := W.DD T

instance (I : BaseId W) (T : LocLat G Qp LL O) : AddCommGroup (DV I T) :=
  inferInstanceAs (AddCommGroup (W.DD T))

instance (I : BaseId W) (T : LocLat G Qp LL O) : Module (PowerSeries O) (DV I T) :=
  Module.compHom (W.DD T) (I.d : PowerSeries O →+* LetA O n)

def DV.d {I : BaseId W} {T : LocLat G Qp LL O} (x : DV I T) : W.DD T := x

def toDV (I : BaseId W) {T : LocLat G Qp LL O} (x : W.DD T) : DV I T := x

@[simp] theorem DV.d_toDV (I : BaseId W) {T : LocLat G Qp LL O} (x : W.DD T) : (toDV I x).d = x := rfl
@[simp] theorem DV.d_add {I : BaseId W} {T : LocLat G Qp LL O} (x y : DV I T) : (x + y).d = x.d + y.d := rfl
@[simp] theorem DV.d_sub {I : BaseId W} {T : LocLat G Qp LL O} (x y : DV I T) : (x - y).d = x.d - y.d := rfl
@[simp] theorem DV.d_zero {I : BaseId W} {T : LocLat G Qp LL O} : (0 : DV I T).d = 0 := rfl
@[simp] theorem DV.d_smul {I : BaseId W} {T : LocLat G Qp LL O} (a : PowerSeries O) (x : DV I T) :
    (a • x).d = I.d a • x.d := rfl
theorem DV.d_inj {I : BaseId W} {T : LocLat G Qp LL O} {x y : DV I T} (h : x.d = y.d) : x = y := h
theorem DV.d_sum {I : BaseId W} {T : LocLat G Qp LL O} {κ : Type} (s : Finset κ) (f : κ → DV I T) :
    (∑ j ∈ s, f j).d = ∑ j ∈ s, (f j).d := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro j s hj ih
  rw [Finset.sum_insert hj, Finset.sum_insert hj, DV.d_add, ih]

def NlΔ (I : BaseId W) (T : LocLat G Qp LL O) (i : ZMod n) : Submodule (PowerSeries O) (DV I T) where
  carrier := {x | x.d ∈ W.NΔ T ∧ (letE i : LetA O n) • x.d = x.d}
  zero_mem' := ⟨(W.NΔ T).zero_mem, by rw [DV.d_zero]; exact smul_zero (letE i : LetA O n)⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨(W.NΔ T).add_mem ha hb, by rw [DV.d_add, smul_add, ha', hb']⟩
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    refine ⟨⟨(W.N T).smul_mem _ hx.1, fun δ hδ => ?_⟩, ?_⟩
    · rw [DV.d_smul, γD_smulA, I.γA_Δ δ hδ, hx.2 δ hδ]
    · rw [DV.d_smul, smul_smul, mul_comm, ← smul_smul, hx']

theorem mem_NlΔ (I : BaseId W) (T : LocLat G Qp LL O) (i : ZMod n) (x : DV I T) :
    x ∈ NlΔ I T i ↔ x.d ∈ W.NΔ T ∧ (letE i : LetA O n) • x.d = x.d := Iff.rfl

def latD (I : BaseId W) (T : LocLat G Qp LL O) : Formalism.ExponentWindows.E.Lat I.Bs n (DV I T) where
  φ _ := { toFun := fun x => toDV I (W.φD T x.d), map_zero' := map_zero (W.φD T),
           map_add' := fun a b => map_add (W.φD T) a.d b.d }
  γ _ := { toFun := fun x => toDV I (W.γD T W.gamK x.d), map_zero' := map_zero (W.γD T W.gamK),
           map_add' := fun a b => map_add (W.γD T W.gamK) a.d b.d }
  φ_semi _ a x := by
    apply DV.d_inj
    change W.φD T (I.d a • x.d) = I.d (I.Bs.φ a) • W.φD T x.d
    rw [φD_smulA, I.φA_d]
  γ_semi _ a x := by
    apply DV.d_inj
    change W.γD T W.gamK (I.d a • x.d) = I.d (I.Bs.γ a) • W.γD T W.gamK x.d
    rw [γD_smulA, I.γA_d]
  comm _ x := W.φγ_comm T W.gamK x.d
  N i := NlΔ I T i

@[simp] theorem latD_φ (I : BaseId W) (T : LocLat G Qp LL O) (i : ZMod n) (x : DV I T) :
    ((latD I T).φ i x).d = W.φD T x.d := rfl

@[simp] theorem latD_γ (I : BaseId W) (T : LocLat G Qp LL O) (i : ZMod n) (x : DV I T) :
    ((latD I T).γ i x).d = W.γD T W.gamK x.d := rfl

theorem mem_sm_latD (I : BaseId W) (T : LocLat G Qp LL O) (i : ZMod n) (a : PowerSeries O) (x : DV I T) :
    x ∈ Formalism.ExponentWindows.E.sm a ((latD I T).N i) ↔
      ∃ y ∈ W.NΔ T, (letE i : LetA O n) • y = y ∧ x.d = I.d a • y := by
  show x ∈ Submodule.map (LinearMap.lsmul (PowerSeries O) (DV I T) a) (NlΔ I T i) ↔ _
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_NlΔ] at hz
    exact ⟨z.d, hz.1, hz.2, rfl⟩
  · rintro ⟨y, hy, hy', hx⟩
    refine ⟨toDV I y, (mem_NlΔ I T i _).2 ⟨hy, hy'⟩, ?_⟩
    apply DV.d_inj
    rw [LinearMap.lsmul_apply, DV.d_smul, hx]
    rfl

theorem latD_free (I : BaseId W) (T : LocLat G Qp LL O) (hInj : I.Inj) (hFull : I.Full)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (i : ZMod n) : (latD I T).Free i := by
  obtain ⟨⟨r, b, hbN, huniq, hΔ⟩, -⟩ := hmod
  have hinj : Function.Injective I.ι := hInj
  have hfull : ∀ a : PowerSeries O, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ f, I.ι f = a := hFull
  have hdk : ∀ (f : PowerSeries O) (k : ZMod n), (I.d f) k = I.ι f := fun _ _ => rfl
  have hsingle : ∀ c : LetA O n, c * (letE i : LetA O n) = Pi.single i (c i) := by
    intro c
    funext k
    simp only [letE, Pi.mul_apply, Pi.single_apply]
    split_ifs with hk
    · subst hk
      simp
    · simp
  refine ⟨r, fun j => toDV I ((letE i : LetA O n) • b j), ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h0 : (0 : W.DD T) ∈ W.N T := (W.N T).zero_mem
    have hsum : ∑ j, (I.d (g j) * (letE i : LetA O n)) • b j = 0 := by
      have h1 := congrArg DV.d hg
      simp only [DV.d_sum, DV.d_smul, DV.d_toDV, DV.d_zero] at h1
      simpa only [mul_smul] using h1
    have hu := (huniq 0 h0).unique (y₁ := fun j => I.d (g j) * (letE i : LetA O n)) (y₂ := 0)
      hsum.symm (by simp)
    have h2 := congrFun (congrFun hu j) i
    simp only [hsingle, Pi.single_eq_same, Pi.zero_apply] at h2
    apply hinj
    rw [map_zero, ← hdk (g j) i]
    exact h2
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have hE : ∀ δ, W.γA δ (letE i : LetA O n) = letE i := by
        intro δ
        funext k
        change W.γ₀ δ ((letE i : LetA O n) k) = (letE i : LetA O n) k
        simp only [letE, Pi.single_apply]
        split_ifs <;> simp
      refine (mem_NlΔ I T i _).2 ⟨⟨(W.N T).smul_mem _ (hbN j).1, fun δ hδ => ?_⟩, ?_⟩
      · rw [DV.d_toDV, γD_smulA, (hbN j).2 δ hδ, hE]
      · rw [DV.d_toDV, smul_smul, hsingle]
        congr 1
        simp [letE]
    · intro x hx
      rw [show (latD I T).N i = NlΔ I T i from rfl, mem_NlΔ] at hx
      obtain ⟨a, haΔ, hxa⟩ := hΔ x.d hx.1
      have hinv : ∀ j, ∀ δ ∈ W.DelF, W.γ₀ δ (a j i) = a j i := by
        intro j δ hδ
        change (W.γA δ (a j)) i = a j i
        exact congrFun ((show ∀ δ ∈ W.DelF, W.γA δ (a j) = a j from haΔ j) δ hδ) i
      choose f hf using fun j => hfull (a j i) (hinv j)
      have hx' : x = ∑ j, f j • toDV I ((letE i : LetA O n) • b j) := by
        apply DV.d_inj
        rw [DV.d_sum, ← hx.2, hxa, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [DV.d_smul, DV.d_toDV, smul_smul, smul_smul, hsingle, mul_comm, hsingle, hdk, hf]
      rw [hx']
      exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

theorem latD_p5M (I : BaseId W) (T : LocLat G Qp LL O) (hs : W.s = 1) (hR : RingA W)
    {M h : ZMod n → ℕ} (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h) (i : ZMod n) (m : ℕ) (hm : M i ≤ m) :
    (latD I T).P5M i m := by
  intro v hv
  rw [show (latD I T).N (i - 1) = NlΔ I T (i - 1) from rfl, mem_NlΔ] at hv
  have hq : I.d I.Bs.q = Formalism.MainNotions.WachCoordinates.qP W := by
    funext k
    change I.ι (PowerSeries.X + PowerSeries.C (I.Bs.ℓ : O)) = W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)
    rw [map_add, I.ι_X, I.ℓ_eq, map_natCast PowerSeries.C, map_natCast]
  have hQ : W.Q = W.q := by
    show (W.φA ^ (W.s - 1)) W.q = W.q
    simp [hs]
  have hEat : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ =
      Formalism.MainNotions.WachCoordinates.qP W := by
    funext k
    change Polynomial.aeval W.π₀₁ (Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) =
      W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)
    simp
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  have hqP : Formalism.MainNotions.WachCoordinates.qP W = ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * W.Q := by
    rw [hQ, hw, ← mul_assoc, Units.inv_mul, one_mul]
    exact hEat.symm
  have hNl : v.d ∈ W.Nl T (i - 1) :=
    Submodule.mem_map.2 ⟨v.d, hv.1.1, by rw [LinearMap.smul_apply, LinearMap.id_apply]; exact hv.2⟩
  have h1 := h5.1 i v.d hNl
  have hpow : (Formalism.MainNotions.WachCoordinates.qP W) ^ m =
      ((w⁻¹ : (LetA O n)ˣ) : LetA O n) ^ m * W.Q ^ (m - M i) * W.Q ^ (M i) := by
    rw [hqP, mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
  have hN : (Formalism.MainNotions.WachCoordinates.qP W) ^ m • W.φD T v.d ∈ W.N T := by
    rw [hpow, mul_smul]
    exact (W.N T).smul_mem _ h1
  have hΔ : ∀ δ ∈ W.DelF, W.γD T δ ((Formalism.MainNotions.WachCoordinates.qP W) ^ m • W.φD T v.d) =
      (Formalism.MainNotions.WachCoordinates.qP W) ^ m • W.φD T v.d := by
    intro δ hδ
    rw [γD_smulA, map_pow, ← hq, I.γA_Δ δ hδ, ← W.φγ_comm, hv.1.2 δ hδ]
  have hφE : W.φA (letE (i - 1) : LetA O n) = letE i := by
    funext k
    change W.φ₀ ((letE (i - 1) : LetA O n) (k - 1)) = (letE i : LetA O n) k
    simp only [letE, Pi.single_apply, sub_left_inj]
    split_ifs <;> simp
  have hφl : W.φD T v.d = (letE i : LetA O n) • W.φD T v.d := by
    conv_lhs => rw [← hv.2]
    rw [φD_smulA, hφE]
  rw [show (latD I T).N i = NlΔ I T i from rfl, mem_NlΔ, DV.d_smul, latD_φ, map_pow, hq]
  refine ⟨⟨hN, hΔ⟩, ?_⟩
  rw [smul_smul, mul_comm, ← smul_smul, ← hφl]

end LatD

section Tools1

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

theorem sum_letE_smul (T : LocLat G Qp LL O) (x : W.DD T) : ∑ i : ZMod n, (letE i : LetA O n) • x = x := by
  rw [← Finset.sum_smul]
  have h1 : ∑ i : ZMod n, (letE i : LetA O n) = 1 := Finset.univ_sum_single (1 : LetA O n)
  rw [h1, one_smul]

theorem sum_shift {M : Type} [AddCommMonoid M] (f : ZMod n → M) : ∑ i : ZMod n, f (i - 1) = ∑ i, f i := Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun _ => rfl)

theorem mul_mem_sum (T : LocLat G Qp LL O) (a : LetA O n) (f : ZMod n → W.DD T)
    (h : ∀ i, ∃ y ∈ W.NΔ T, f i = a • y) : ∃ y ∈ W.NΔ T, ∑ i, f i = a • y := by
  choose y hy hfy using h
  refine ⟨∑ i, y i, Submodule.sum_mem _ (fun i _ => hy i), ?_⟩
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => hfy i)

theorem letE_mem_NΔ (T : LocLat G Qp LL O) (i : ZMod n) {y : W.DD T} (hy : y ∈ W.NΔ T) :
    (letE i : LetA O n) • y ∈ W.NΔ T := by
  refine ⟨(W.N T).smul_mem _ hy.1, fun δ hδ => ?_⟩
  have hE : W.γA δ (letE i : LetA O n) = letE i := by
    funext j
    change W.γ₀ δ ((letE i : LetA O n) j) = (letE i : LetA O n) j
    simp only [letE, Pi.single_apply]
    split_ifs <;> simp
  rw [γD_smulA, hy.2 δ hδ, hE]

theorem letE_letE (T : LocLat G Qp LL O) (i : ZMod n) (y : W.DD T) :
    (letE i : LetA O n) • ((letE i : LetA O n) • y) = (letE i : LetA O n) • y := by
  rw [smul_smul]
  congr 1
  funext j
  simp only [letE, Pi.mul_apply, Pi.single_apply]
  split_ifs <;> simp

theorem wach_frobenius_divisibility_unique_solution [IsDomain O] (hR : RingA W) (hs : W.s = 1) (T : LocLat G Qp LL O)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (hh M : ℕ) (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T (fun _ => hh) (fun _ => hh))
    (hM : hh < (PD.p - 1) * M) (hcomp : IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O) :
    (∀ x ∈ W.NΔ T, ∃ y ∈ W.NΔ T, W.φD T (W.π₀ ^ M • x) = (W.π₀ ^ M * Formalism.MainNotions.WachCoordinates.qP W) • y) ∧
    (∀ w : W.DD T, (∃ y ∈ W.NΔ T, w = W.π₀ ^ M • y) →
      ∃! z : W.DD T, (∃ y ∈ W.NΔ T, z = W.π₀ ^ M • y) ∧ W.φD T z - z = w) := by
  let I : BaseId W := baseIdOf hR
  have hInj : I.Inj := baseIdOf_inj hR
  have hFull : I.Full := baseIdOf_full hR
  have hE3 : I.Bs.E3 := frobenius_uniformizer_identity hR
  have hfree : ∀ i, (latD I T).Free i := latD_free I T hInj hFull hmod
  have hA := Formalism.ExponentWindows.E.lattice_filtration_first_form O I.Bs n M (DV I T) (latD I T) (fun _ => hh) hE3
    (fun i => latD_p5M I T hs hR h5 i hh le_rfl) (fun _ => by exact hM)
  have hq : (latD I T).FrobeniusMapsXPow M := hA.1
  have hC : (latD I T).Complete := Formalism.ExponentWindows.E.completion_holds O I.Bs n (DV I T) (latD I T) hcomp hfree
  have hX : (latD I T).XReg := Formalism.ExponentWindows.E.X_regular_on_lattice O I.Bs n (DV I T) (latD I T) hfree
  have hdX : I.d (PowerSeries.X ^ M) = W.π₀ ^ M := by rw [map_pow, I.d_X]
  have hdXq : I.d (PowerSeries.X ^ M * I.Bs.q) = W.π₀ ^ M * Formalism.MainNotions.WachCoordinates.qP W := by
    rw [map_mul, hdX, I.d_q]

  have hlet : ∀ (i : ZMod n) (y : W.DD T), y ∈ W.NΔ T →
      toDV I ((letE i : LetA O n) • (W.π₀ ^ M • y)) ∈ Formalism.ExponentWindows.E.sm (PowerSeries.X ^ M) ((latD I T).N i) := by
    intro i y hy
    refine (mem_sm_latD I T i _ _).2 ⟨(letE i : LetA O n) • y, letE_mem_NΔ T i hy, letE_letE T i y, ?_⟩
    rw [DV.d_toDV, hdX, smul_comm]
  refine ⟨fun x hx => ?_, fun w hw => ?_⟩
  · have key : ∀ j : ZMod n, ∃ y ∈ W.NΔ T,
        W.φD T (W.π₀ ^ M • ((letE (j - 1) : LetA O n) • x)) = (W.π₀ ^ M * Formalism.MainNotions.WachCoordinates.qP W) • y := by
      intro j
      obtain ⟨y, hy, -, hyy⟩ := (mem_sm_latD I T j _ _).1 (hq j _ (hlet (j - 1) x hx))
      refine ⟨y, hy, ?_⟩
      rw [← hdXq, ← hyy, latD_φ, DV.d_toDV, smul_comm]
    have := mul_mem_sum T _ _ key
    rwa [sum_shift (fun j => W.φD T (W.π₀ ^ M • ((letE j : LetA O n) • x))), ← map_sum,
      ← Finset.smul_sum, sum_letE_smul] at this
  · obtain ⟨y0, hy0, rfl⟩ := hw
    let t : ZMod n → DV I T := fun i => toDV I ((letE i : LetA O n) • (W.π₀ ^ M • y0))
    obtain ⟨z, ⟨hz, hdz⟩, huniq⟩ := Formalism.ExponentWindows.E.lattice_filtration_second_form O I.Bs n M (DV I T) (latD I T) hE3 hq hC hX t
      (fun i => hlet i y0 hy0)
    have hzd : ∀ i, ∃ y ∈ W.NΔ T, (z i).d = W.π₀ ^ M • y := by
      intro i
      obtain ⟨y, hy, -, hyy⟩ := (mem_sm_latD I T i _ _).1 (hz i)
      exact ⟨y, hy, by rw [hyy, hdX]⟩
    have hdzi : ∀ i, W.φD T (z (i - 1)).d - (z i).d = (letE i : LetA O n) • (W.π₀ ^ M • y0) := by
      intro i
      have := congrArg DV.d (congrFun hdz i)
      simpa [Formalism.ExponentWindows.E.Lat.dφ, t] using this
    refine ⟨∑ i, (z i).d, ⟨?_, ?_⟩, ?_⟩
    · exact mul_mem_sum T _ _ hzd
    · rw [map_sum, ← sum_shift (fun i => W.φD T (z i).d), ← Finset.sum_sub_distrib]
      rw [Finset.sum_congr rfl fun i _ => hdzi i, sum_letE_smul]
    · rintro Z ⟨⟨yZ, hyZ, rfl⟩, hZ⟩
      let z' : ZMod n → DV I T := fun i => toDV I ((letE i : LetA O n) • (W.π₀ ^ M • yZ))
      have hz' : z' = z := by
        refine huniq z' ⟨fun i => hlet i yZ hyZ, funext fun i => DV.d_inj ?_⟩
        simp only [Formalism.ExponentWindows.E.Lat.dφ, DV.d_sub, latD_φ, z', t, DV.d_toDV]
        rw [φD_smulA, φA_letE, ← smul_sub, hZ]
      rw [← sum_letE_smul T (W.π₀ ^ M • yZ)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hz']
      rfl

end Tools1

section Classes

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

def InPM (T : LocLat G Qp LL O) (M : ℕ) (z : W.DD T) : Prop := ∃ y ∈ W.NΔ T, z = W.π₀ ^ M • y

theorem inPM_sub {T : LocLat G Qp LL O} {M : ℕ} {a b : W.DD T} (ha : InPM T M a) (hb : InPM T M b) :
    InPM T M (a - b) := by
  obtain ⟨y, hy, rfl⟩ := ha
  obtain ⟨y', hy', rfl⟩ := hb
  exact ⟨y - y', (W.NΔ T).sub_mem hy hy', (smul_sub _ _ _).symm⟩

theorem inPM_zero (T : LocLat G Qp LL O) (M : ℕ) : InPM (W := W) T M 0 := ⟨0, (W.NΔ T).zero_mem, (smul_zero _).symm⟩

theorem smul_NΔ (T : LocLat G Qp LL O) {a : LetA O n} (ha : a ∈ W.AΔ) {y : W.DD T} (hy : y ∈ W.NΔ T) :
    a • y ∈ W.NΔ T := by
  refine ⟨(W.N T).smul_mem _ hy.1, fun δ hδ => ?_⟩
  have ha' : W.γA δ a = a := (show ∀ δ ∈ W.DelF, W.γA δ a = a from ha) δ hδ
  rw [γD_smulA, hy.2 δ hδ, ha']

theorem inPM_Δ {T : LocLat G Qp LL O} {M : ℕ} (hR : RingA W) {z : W.DD T} (hz : InPM T M z) :
    ∀ δ ∈ W.DelF, W.γD T δ z = z := by
  obtain ⟨y, hy, rfl⟩ := hz
  intro δ hδ
  have hπ : W.γA δ W.π₀ = W.π₀ := (show ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ from hR.1) δ hδ
  rw [γD_smulA, map_pow, hπ, hy.2 δ hδ]

theorem inPM_γK [IsDomain O] (hR : RingA W) (hg : W.gamK = W.gam) {T : LocLat G Qp LL O} {M : ℕ}
    {z : W.DD T} (hz : InPM T M z) : InPM T M (W.γD T W.gamK z) := by
  let I : BaseId W := baseIdOf hR
  obtain ⟨e, he⟩ := fourth_lefschetz_of_first hR hg
  have hu : W.γA W.gamK W.π₀ = W.π₀ * I.d (1 + (e : PowerSeries O) * I.Bs.q) := by
    rw [← I.d_X, I.γA_d, ← map_mul]
    exact congrArg I.d he
  have huΔ : I.d (1 + (e : PowerSeries O) * I.Bs.q) ∈ W.AΔ := fun δ hδ => I.γA_Δ δ hδ _
  obtain ⟨y, hy, rfl⟩ := hz
  have hγy : W.γD T W.gamK y ∈ W.NΔ T :=
    ⟨W.N_Γ T _ y hy.1, fun δ hδ => by rw [← W.γD_mul, mul_comm, W.γD_mul, hy.2 δ hδ]⟩
  refine ⟨I.d (1 + (e : PowerSeries O) * I.Bs.q) ^ M • W.γD T W.gamK y,
    smul_NΔ T (W.AΔ.pow_mem huΔ M) hγy, ?_⟩
  rw [γD_smulA, map_pow, hu, mul_pow, mul_smul]

theorem inPM_inj {T : LocLat G Qp LL O} {M : ℕ} (hR : RingA W)
    (h1 : ∀ x ∈ W.NΔ T, ∃ y ∈ W.NΔ T, W.φD T (W.π₀ ^ M • x) = (W.π₀ ^ M * Formalism.MainNotions.WachCoordinates.qP W) • y)
    (h2 : ∀ w : W.DD T, InPM T M w → ∃! z : W.DD T, InPM T M z ∧ W.φD T z - z = w)
    {a b : W.DD T} (ha : InPM T M a) (hb : InPM T M b) (he : W.φD T a - a = W.φD T b - b) : a = b := by
  have hq : Formalism.MainNotions.WachCoordinates.qP W ∈ W.AΔ := by
    show W.π₀ + ((PD.p : ℕ) : LetA O n) ∈ W.AΔ
    exact W.AΔ.add_mem hR.1 (Subalgebra.natCast_mem _ _)
  have hφ : ∀ {c : W.DD T}, InPM T M c → InPM T M (W.φD T c) := by
    rintro c ⟨y, hy, rfl⟩
    obtain ⟨y', hy', he'⟩ := h1 y hy
    exact ⟨Formalism.MainNotions.WachCoordinates.qP W • y', smul_NΔ T hq hy', by rw [he', mul_smul]⟩
  exact (h2 _ (inPM_sub (hφ ha) ha)).unique ⟨ha, rfl⟩ ⟨hb, he.symm⟩

end Classes

section F1At

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

theorem inPM_add {T : LocLat G Qp LL O} {M : ℕ} {a b : W.DD T} (ha : InPM T M a) (hb : InPM T M b) :
    InPM T M (a + b) := by
  obtain ⟨y, hy, rfl⟩ := ha
  obtain ⟨y', hy', rfl⟩ := hb
  exact ⟨y + y', (W.NΔ T).add_mem hy hy', (smul_add _ _ _).symm⟩

theorem inPM_map {T T' : LocLat G Qp LL O} {M : ℕ} (f : LatHom T.L T'.L) (hT : IsCrys PD T.ρ)
    (hT' : IsCrys PD T'.ρ) {a : W.DD T} (ha : InPM T M a) :
    InPM T' M (W.map f a) := by
  obtain ⟨y, hy, rfl⟩ := ha
  exact ⟨W.map f y, ⟨W.map_N f hT hT' y hy.1, fun δ hδ => by rw [← W.map_γ, hy.2 δ hδ]⟩, map_smulA W f _ y⟩

theorem wach_frobenius_divisibility_ringA [IsDomain O] (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hcomp : IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (h M : ℕ) (hM : h < (PD.p - 1) * M) (hJ : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T (fun _ => h) (fun _ => h)) :
    RingA W ∧
    (∀ x ∈ W.NΔ T, ∃ y ∈ W.NΔ T, W.φD T (W.π₀ ^ M • x) = (W.π₀ ^ M * Formalism.MainNotions.WachCoordinates.qP W) • y) ∧
    (∀ w : W.DD T, InPM T M w → ∃! z : W.DD T, InPM T M z ∧ W.φD T z - z = w) := by
  have hs : W.s = 1 := hA.2.1
  have hp : PD.p ≠ 2 := hA.2.2
  have hrk : Module.finrank K₀ K = 1 :=
    (LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1)).symm.trans
      (Module.finrank_self K₀)
  obtain ⟨hR, hmod⟩ := (h9 T hT hs hp).2.2 hrk
  have ht := wach_frobenius_divisibility_unique_solution hR hs T hmod h M (h5 T _ _ hT hJ) hM hcomp
  exact ⟨hR, ht.1, ht.2⟩

theorem coc_of {T : LocLat G Qp LL O} (x : ↥(W.wachCocyclesDelta T)) :
    W.γD T W.gamK (x : W.DD T × W.DD T).1 - (x : W.DD T × W.DD T).1 =
      W.φD T (x : W.DD T × W.DD T).2 - (x : W.DD T × W.DD T).2 := by
  have hx := x.2
  simp only [LocWach.wachCocyclesDelta, herrZ1Δ, Submodule.mem_inf] at hx
  have h := hx.1
  simp only [herrCocycles, LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply,
    LinearMap.neg_apply, LinearMap.id_apply] at h
  exact sub_eq_zero.1 ((sub_eq_add_neg _ _).trans h)

theorem wach_frobenius_lattice_unramified_functor [IsDomain O] (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (h2a : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexFirstProperty W) (hnat : Formalism.MainNotions.DeltaInvariantLattices.ClKNatG W)
    (hcomp : IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O) : Formalism.MainNotions.WachCoordinates.F1 W := by
  replace hnat : W.ClKNat := hnat (fun hp => absurd hp hA.2.2)
  have hg : W.gamK = W.gam := W.gamK_eq_one hA.2.1 hA.2.2
  intro h M hM
  refine ⟨fun T hT hJ => ?_, fun T T' F hT hT' hJ hJ' c x x' hx hx' hmap => ?_⟩
  · obtain ⟨hR, c1, c2⟩ := wach_frobenius_divisibility_ringA hA h5 h9 hcomp T hT h M hM (fun τ _ _ => hJ τ)
    refine ⟨c1, fun w hw => c2 w hw, ?_, ?_⟩
    · intro c x ⟨_, _, hz⟩ hy
      obtain ⟨m, ⟨hm, hφm⟩, -⟩ := c2 _ hy
      have hc := coc_of x
      have hzeq : (x : W.DD T × W.DD T).2 = W.γD T W.gamK m - m := by
        refine inPM_inj hR c1 c2 hz (inPM_sub (inPM_γK hR hg hm) hm) ?_
        rw [← hc, map_sub, W.φγ_comm, ← hφm, map_sub]
        abel
      exact (((h2a T hT).2 hA.2.1 hA.2.2).2 x).2 ⟨m, inPM_Δ hR hm, Prod.ext hφm.symm hzeq⟩
    · intro c x₁ x₂ x₃ h₁ h₂ h₃ he
      have e : x₃ = x₁ + x₂ := by
        have hd : InPM T M ((x₃ : W.DD T × W.DD T).2 - (x₁ : W.DD T × W.DD T).2 - (x₂ : W.DD T × W.DD T).2) :=
          inPM_sub (inPM_sub h₃.2.2 h₁.2.2) h₂.2.2
        have h0 := inPM_inj hR c1 c2 hd (inPM_zero T M) (by
          rw [map_sub, map_sub, map_zero, sub_zero]
          have e3 := coc_of x₃
          have e1 := coc_of x₁
          have e2 := coc_of x₂
          rw [he, map_add] at e3
          have e4 : W.φD T (x₃ : W.DD T × W.DD T).2 - (x₃ : W.DD T × W.DD T).2 =
              (W.φD T (x₁ : W.DD T × W.DD T).2 - (x₁ : W.DD T × W.DD T).2) +
                (W.φD T (x₂ : W.DD T × W.DD T).2 - (x₂ : W.DD T × W.DD T).2) := by
            rw [← e3, ← e1, ← e2]; abel
          calc _ = (W.φD T (x₃ : W.DD T × W.DD T).2 - (x₃ : W.DD T × W.DD T).2) -
                ((W.φD T (x₁ : W.DD T × W.DD T).2 - (x₁ : W.DD T × W.DD T).2) +
                  (W.φD T (x₂ : W.DD T × W.DD T).2 - (x₂ : W.DD T × W.DD T).2)) := by abel
            _ = 0 := by rw [e4, sub_self])
        apply Subtype.ext
        refine Prod.ext he ?_
        change (x₃ : W.DD T × W.DD T).2 = (x₁ : W.DD T × W.DD T).2 + (x₂ : W.DD T × W.DD T).2
        rw [sub_sub, sub_eq_zero] at h0
        exact h0
      rw [e]
      exact (W.clK T).map_add x₁ x₂
  · obtain ⟨hR, c1, c2⟩ := wach_frobenius_divisibility_ringA hA h5 h9 hcomp T' hT' h M hM (fun τ _ _ => hJ' τ)
    have hz' : (x' : W.DD T' × W.DD T').2 = W.map F (x : W.DD T × W.DD T).2 := by
      refine inPM_inj hR c1 c2 hx'.2.2 (inPM_map F hT hT' hx.2.2) ?_
      rw [← coc_of x', hmap, ← W.map_φ, ← map_sub, ← coc_of x, map_sub, W.map_γ]
    exact (hnat F x x' (Prod.ext hmap hz')).symm

end F1At

section F1AAt

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

theorem wach_frobenius_lattice_at_functor [IsDomain O] (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (h2a : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexFirstProperty W) (hnat : Formalism.MainNotions.DeltaInvariantLattices.ClKNatG W)
    (hcomp : IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O) : Formalism.MainNotions.ArcLiftingSetup.FirstWachFiltration W := by
  intro hA h M hM
  replace hnat : W.ClKNat := hnat (fun hp => absurd hp hA.2.2)
  have hg : W.gamK = W.gam := W.gamK_eq_one hA.2.1 hA.2.2
  have hJL : ∀ T : LocLat G Qp LL O, Formalism.MainNotions.ArcLiftingSetup.JumpsLe PD T h →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T (fun _ => h) (fun _ => h) :=
    fun T hJ τ _ _ a ha => Set.mem_Icc.2 (abs_le.1 (hJ τ a ha))
  refine ⟨fun T hT hJ => ?_, fun T T' f hT hT' hJ hJ' c y x hy hcls => ?_⟩
  · obtain ⟨hR, c1, c2⟩ := wach_frobenius_divisibility_ringA hA h5 h9 hcomp T hT h M hM (hJL T hJ)
    refine ⟨c1, fun z hz => ?_, ?_, ?_, ?_⟩
    · obtain ⟨x, ⟨hx, hφ⟩, hu⟩ := c2 z hz
      exact ⟨x, hx, hφ, fun x' hx' he => hu x' ⟨hx', he⟩⟩
    · rintro c y - hyΔ ⟨y', hy', -, hw⟩
      obtain ⟨z, ⟨hz, hφz⟩, -⟩ := c2 _ ⟨y', hy', hw⟩
      have hmem : (y, z) ∈ W.wachCocyclesDelta T := (mem_Z1DΔ y z).2 ⟨by rw [hg, hφz]; rfl, hyΔ, inPM_Δ hR hz⟩
      exact ⟨_, z, hmem, hz, rfl⟩
    · rintro c y₁ y₂ x₁ x₂ - - ⟨z₁, h₁, hz₁, rfl⟩ ⟨z₂, h₂, hz₂, rfl⟩
      exact ⟨z₁ + z₂, (W.wachCocyclesDelta T).add_mem h₁ h₂, inPM_add hz₁ hz₂, (W.clK T).map_add ⟨(y₁, z₁), h₁⟩ ⟨(y₂, z₂), h₂⟩⟩
    · rintro c y - hyΔ ⟨y', hy', -, hyy⟩
      obtain ⟨m, ⟨hm, hφm⟩, -⟩ := c2 y ⟨y', hy', hyy⟩
      have hzm : InPM T M (W.γD T W.gamK m - m) := inPM_sub (inPM_γK hR hg hm) hm
      have hmem : (y, W.γD T W.gamK m - m) ∈ W.wachCocyclesDelta T := by
        refine (mem_Z1DΔ _ _).2 ⟨?_, hyΔ, inPM_Δ hR hzm⟩
        rw [map_sub, W.φγ_comm, ← hφm, map_sub]
        abel
      exact ⟨_, hmem, hzm, (((h2a T hT).2 hA.2.1 hA.2.2).2 _).2 ⟨m, inPM_Δ hR hm, Prod.ext hφm.symm rfl⟩⟩
  · obtain ⟨z, hz, hzN, rfl⟩ := hcls
    exact ⟨W.map f z, map_mem_Z1DΔ f ⟨(y, z), hz⟩, inPM_map f hT hT' hzN,
      (hnat f ⟨(y, z), hz⟩ ⟨_, map_mem_Z1DΔ f ⟨(y, z), hz⟩⟩ rfl).symm⟩

end F1AAt

end WachFrobeniusLattice

open WachFrobeniusLattice

section F1Rows

theorem caseA_of_unram' {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) {K LL : FinExt l}
    (h : Good K 1 LL) (hK : K.1 ≤ MaximalUnramifiedExtension l) (hl : l ≠ 2) : Formalism.MainNotions.LiftingTheory.CaseA (H.W K 1 LL h) := by
  refine ⟨⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x, x.2, hK x.2⟩, rfl⟩⟩, H.W_s K 1 LL h, ?_⟩
  rw [P.PD_p]
  exact hl

theorem neZero_finrank_max_unramified {l : ℕ} [Fact l.Prime] (K : FinExt l) : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := by
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  have hle : K0 K ≤ K.1 := inf_le_left
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  exact ⟨Module.finrank_pos.ne'⟩

theorem eq_sum_herm_smul_frame_of_inW {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) :
    IsAdicComplete (Ideal.span {((((P.PD K).p : ℕ) : ↥(OL LL)))}) ↥(OL LL) := by
  rw [P.PD_p]
  exact complete_OL LL

theorem wach_frobenius_lattice_unramified_case (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h : FirstFiltrationHypotheses D HW F) :
    FirstFiltrationEtale D HW F := fun l _ K LL hA _ =>
  haveI := neZero_finrank_max_unramified K
  wach_frobenius_lattice_unramified_functor (caseA_of_unram' (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1) (h.2.1 l K 1 LL hA.2.2)
    (h.2.2.1 l K 1 LL hA.2.2) (h.2.2.2.1 l K 1 LL hA.2.2) (h.2.2.2.2 l K 1 LL hA.2.2).2
    (eq_sum_herm_smul_frame_of_inW (D.loc l) K LL)

theorem firstFiltrationTheoremEtale (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : FirstFiltrationTheoremEtale D HW F := fun h => wach_frobenius_lattice_unramified_case D HW F h

theorem wach_first_filtration_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h : FirstFiltrationHypotheses D HW F) :
    FirstFiltrationArcLifting D HW F := fun l _ K LL hG _ _ =>
  haveI := neZero_finrank_max_unramified K
  wach_frobenius_lattice_at_functor (h.2.1 l K 1 LL hG) (h.2.2.1 l K 1 LL hG) (h.2.2.2.1 l K 1 LL hG) (h.2.2.2.2 l K 1 LL hG).2
    (eq_sum_herm_smul_frame_of_inW (D.loc l) K LL)

theorem firstFiltrationTheoremCaseA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : FirstFiltrationTheoremCaseA D HW F := fun h => wach_first_filtration_of_hypotheses D HW F h

end F1Rows

end Formalism.MainNotions.UnusedSlot80
