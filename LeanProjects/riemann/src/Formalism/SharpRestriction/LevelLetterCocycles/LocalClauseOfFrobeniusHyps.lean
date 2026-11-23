import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool
import Formalism.SharpRestriction.LevelLetterCocycles.WachFrobeniusLatticeUnramifiedFunctor
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusIterateUniformizerUnitProducts
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationUnramifiedOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkFilLetter
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HodgeFontaineExactness.OneNotMemFilOne

noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs.Tools

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Jumps

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem filV_succ_le (a : ℤ) : FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  have hle : (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := PD.Fil_anti a
  have hcomp : AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil (a + 1)).restrictScalars Qp).subtype =
      (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype).comp
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle)) := by
    rw [← AlgebraTensorModule.map_comp, LinearMap.id_comp, Submodule.subtype_comp_inclusion]
  unfold FilV
  rw [hcomp]
  exact LinearMap.range_comp_le_range _ _

theorem fildR_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) : FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a :=
  inf_le_inf_left _ (filV_succ_le PD a)

theorem jumps_bdd (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∃ h : ℕ, ∀ a : ℤ, IsJumpV PD ρ τ a → a ≤ h := by
  classical
  have hfd : ∀ a, FiniteDimensional LL ↥(FildR PD ρ τ a) := fun a =>
    Module.Finite.of_injective (Submodule.inclusion (inf_le_left : FildR PD ρ τ a ≤ DdRE PD ρ τ))
      (Submodule.inclusion_injective _)
  let f : ℤ → ℕ := fun a => finrank LL ↥(FildR PD ρ τ a)
  have hanti : Antitone fun a => FildR PD ρ τ a := antitone_int_of_succ_le (fildR_succ_le PD ρ τ)
  have hmono : ∀ a b : ℤ, a ≤ b → f b ≤ f a := fun a b hab =>
    LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective (hanti hab))
  have hlt : ∀ a, IsJumpV PD ρ τ a → f (a + 1) < f a := fun a ha =>
    Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (fildR_succ_le PD ρ τ a) ha)
  have hinj : Set.InjOn f {a | IsJumpV PD ρ τ a} := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · have := hmono (a + 1) b (by omega)
      have := hlt a ha
      simp only [f] at *
      omega
    · exact h
    · have := hmono (b + 1) a (by omega)
      have := hlt b hb
      simp only [f] at *
      omega
  have himg : f '' {a | IsJumpV PD ρ τ a} ⊆ Set.Iic (finrank LL ↥(DdRE PD ρ τ)) := by
    rintro _ ⟨a, -, rfl⟩
    exact LinearMap.finrank_le_finrank_of_injective
      (Submodule.inclusion_injective (inf_le_left : FildR PD ρ τ a ≤ DdRE PD ρ τ))
  have hfin : {a | IsJumpV PD ρ τ a}.Finite :=
    Set.Finite.of_finite_image ((Set.finite_Iic _).subset himg) hinj
  obtain ⟨M, hM⟩ := hfin.bddAbove
  exact ⟨M.toNat, fun a ha => (hM ha).trans (Int.self_le_toNat M)⟩

end Jumps

section Box

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem over_unique (W : LocWach PD LL O v n) (hbij : Function.Bijective (algebraMap K₀ K))
    {i : ZMod n} {τ τ' : K →ₐ[Qp] LL} (h : Formalism.MainNotions.LiftingTheory.Over W τ i) (h' : Formalism.MainNotions.LiftingTheory.Over W τ' i) :
    τ = τ' := by
  ext x
  obtain ⟨y, rfl⟩ := hbij.2 x
  have := congrArg (fun f : K₀ →ₐ[Qp] LL => f y) (h.trans h'.symm)
  simpa using this

theorem exists_ub (W : LocWach PD LL O v n) (hbij : Function.Bijective (algebraMap K₀ K))
    (hDR : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) :
    ∃ hi : ZMod n → ℕ, ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∀ a : ℤ, IsJumpV PD T.ρ τ a → a ≤ hi i := by
  classical
  have hb : ∀ τ : K →ₐ[Qp] LL, ∃ h : ℕ, ∀ a : ℤ, IsJumpV PD T.ρ τ a → a ≤ h := fun τ => by
    have := ((hDR hbij T.V T.ρ hT).2 τ).1
    exact jumps_bdd PD T.ρ τ
  choose H hH using hb
  refine ⟨fun i => if h : ∃ τ, Formalism.MainNotions.LiftingTheory.Over W τ i then H h.choose else 0, ?_⟩
  intro i τ hτ a ha
  have hex : ∃ τ, Formalism.MainNotions.LiftingTheory.Over W τ i := ⟨τ, hτ⟩
  have he : hex.choose = τ := over_unique W hbij hex.choose_spec hτ
  simp only [dif_pos hex]
  have := hH τ a ha
  rw [← he] at this
  exact this

end Box

section F12

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

open Formalism.MainNotions.UnusedSlot80.WachFrobeniusLattice Formalism.MainNotions.WachCoordinates.Br

theorem Frobenius_divisibility_unique_solution [IsDomain O] (hR : RingA W) (hs : W.s = 1) (T : LocLat G Qp LL O)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (hh M : ℕ) (hi : ZMod n → ℕ)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T (fun _ => hh) hi)
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

theorem qpow_φ_mem (hs : W.s = 1) (hR : RingA W) {T : LocLat G Qp LL O} {H : ℕ} {hi : ZMod n → ℕ}
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T (fun _ => H) hi) {x : W.DD T} (hx : x ∈ W.N T) :
    Formalism.MainNotions.LiftingTheory.qp W ^ H • W.φD T x ∈ W.N T := by
  rw [← sum_letE_smul T (W.φD T x), Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have e : (letE i : LetA O n) • W.φD T x = W.φD T ((letE (i - 1) : LetA O n) • x) := by
    rw [φD_smulA, φA_letE]
  rw [e]
  exact qP_pow_mem hs hR (W.N T) (h5.1 i _ ⟨x, hx, rfl⟩)

theorem inPN_iff {T : LocLat G Qp LL O} {k : ℕ} {x : W.DD T} : InPN W T k x ↔ InPM T k x := by
  constructor
  · rintro ⟨y, hy, hinv, rfl⟩
    exact ⟨y, ⟨hy, hinv⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy.1, hy.2, rfl⟩

end F12

section Alg5

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

open Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.UnusedSlot80.SatW Formalism.MainNotions.UnusedSlot80.WachFrobeniusLattice Formalism.MainNotions.WachCoordinates.Br

theorem lO_smul {T : LocLat G Qp LL O} (k : ℕ) (x : W.DD T) :
    ((PD.p : ℕ) : O) ^ k • x = ((PD.p : ℕ) : LetA O n) ^ k • x := by
  rw [← map_natCast (algebraMap O (LetA O n)), ← map_pow, algebraMap_smul]

theorem φ_lA {T : LocLat G Qp LL O} (k : ℕ) (x : W.DD T) :
    W.φD T (((PD.p : ℕ) : LetA O n) ^ k • x) = ((PD.p : ℕ) : LetA O n) ^ k • W.φD T x := by
  rw [φD_smulA, map_pow, map_natCast]

theorem γ_lA {T : LocLat G Qp LL O} (g : W.Gam) (k : ℕ) (x : W.DD T) :
    W.γD T g (((PD.p : ℕ) : LetA O n) ^ k • x) = ((PD.p : ℕ) : LetA O n) ^ k • W.γD T g x := by
  rw [γD_smulA, map_pow, map_natCast]

theorem γA_letπ (g : W.Gam) : ∃ u : (LetA O n)ˣ, W.γA g letπ = (u : LetA O n) * letπ := by
  obtain ⟨h0, h1⟩ := W.γ₀_X g
  obtain ⟨h, hh⟩ := PowerSeries.X_dvd_iff.2 h0
  have hc : PowerSeries.constantCoeff h = (W.χΓ g : O) := by
    rw [← h1, hh, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hu : IsUnit h := PowerSeries.isUnit_iff_constantCoeff.2 (by rw [hc]; exact Units.isUnit _)
  have hU : IsUnit (fun _ : ZMod n => h) := Pi.isUnit_iff.2 fun _ => hu
  refine ⟨hU.unit, ?_⟩
  funext i
  simp only [IsUnit.unit_spec, Pi.mul_apply, letπ, LocWach.γA, letγ, AlgHom.pi_apply,
    AlgHom.comp_apply, Pi.evalAlgHom_apply]
  rw [hh, mul_comm]

theorem UPi_γA (g : W.Gam) {a : LetA O n} (ha : UPi PD.p a) : UPi PD.p (W.γA g a) := by
  obtain ⟨u, m, r, rfl⟩ := ha
  obtain ⟨u', hu'⟩ := γA_letπ (W := W) g
  refine ⟨(Units.map (W.γA g : LetA O n →* LetA O n) u) * u' ^ m, m, W.γA g r, ?_⟩
  rw [map_add, map_mul, map_mul, map_pow, hu', map_natCast, mul_pow, Units.val_mul, Units.val_pow_eq_pow_val]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  ring

theorem φpow_AΔ {a : LetA O n} (ha : a ∈ W.AΔ) (j : ℕ) : (W.φA ^ j) a ∈ W.AΔ := by
  have step : ∀ b : LetA O n, b ∈ W.AΔ → W.φA b ∈ W.AΔ := by
    intro b hb
    show ∀ δ ∈ W.DelF, W.γA δ (W.φA b) = W.φA b
    intro δ hδ
    have hb' : W.γA δ b = b := hb δ hδ
    rw [← W.φA_γA, hb']
  induction j with
  | zero => exact ha
  | succ j ih =>
    rw [pow_succ']
    exact step _ ih

theorem γA_AΔ {a : LetA O n} (ha : a ∈ W.AΔ) (g : W.Gam) : W.γA g a ∈ W.AΔ := by
  intro δ hδ
  rw [← γA_mul, mul_comm, γA_mul, ha δ hδ]

theorem φ_pow_apply (j : ℕ) (a : LetA O n) : W.φA ((W.φA ^ j) a) = (W.φA ^ (j + 1)) a := by
  rw [pow_succ']
  rfl

def InMN (T : LocLat G Qp LL O) (M : ℕ) (x : W.DD T) : Prop := ∃ y ∈ W.N T, x = W.π₀ ^ M • y

theorem InMN.zero (T : LocLat G Qp LL O) (M : ℕ) : InMN (W := W) T M 0 :=
  ⟨0, (W.N T).zero_mem, (smul_zero _).symm⟩

theorem InMN.add {T : LocLat G Qp LL O} {M : ℕ} {x y : W.DD T} (hx : InMN T M x) (hy : InMN T M y) :
    InMN T M (x + y) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a + b, (W.N T).add_mem ha hb, (smul_add _ _ _).symm⟩

theorem InMN.sub {T : LocLat G Qp LL O} {M : ℕ} {x y : W.DD T} (hx : InMN T M x) (hy : InMN T M y) :
    InMN T M (x - y) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a - b, (W.N T).sub_mem ha hb, (smul_sub _ _ _).symm⟩

theorem InMN.smul {T : LocLat G Qp LL O} {M : ℕ} {x : W.DD T} (hx : InMN T M x) (a : LetA O n) :
    InMN T M (a • x) := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨a • y, (W.N T).smul_mem a hy, smul_comm _ _ _⟩

theorem InMN.sum {T : LocLat G Qp LL O} {M : ℕ} (s : Finset ℕ) (f : ℕ → W.DD T)
    (h : ∀ y ∈ s, InMN T M (f y)) : InMN T M (∑ y ∈ s, f y) := by
  exact Finset.sum_induction f (InMN T M) (fun _ _ => InMN.add) (InMN.zero T M) h

theorem InMN.γ (hR : RingA W) {T : LocLat G Qp LL O} {M : ℕ} {x : W.DD T} (hx : InMN T M x) :
    InMN T M (W.γ T x) := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨w, hw⟩ := hR.2.2.2.2.2.2.1
  have e : W.γA W.gam W.π₀ = W.π₀ * (1 + (w : LetA O n) *
      Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀) := by
    rw [mul_add, mul_one, ← mul_assoc, mul_comm W.π₀ (w : LetA O n), ← hw]; ring
  refine ⟨(1 + (w : LetA O n) * Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀) ^ M •
    W.γ T y, Submodule.smul_mem _ _ (W.N_Γ T _ y hy), ?_⟩
  show W.γD T W.gam (W.π₀ ^ M • y) = _
  rw [γD_smulA, map_pow, e, mul_pow, mul_smul]
  rfl

theorem InMN.γsub (hR : RingA W) {T : LocLat G Qp LL O} {M : ℕ} {x : W.DD T} (hx : InMN T M x) :
    InMN T M (W.γ T x - x) := (hx.γ hR).sub hx

theorem γ'_lA {T : LocLat G Qp LL O} (k : ℕ) (x : W.DD T) :
    W.γ T (((PD.p : ℕ) : LetA O n) ^ k • x) = ((PD.p : ℕ) : LetA O n) ^ k • W.γ T x :=
  γ_lA W.gam k x

theorem lin_id {T : LocLat G Qp LL O} (f : W.DD T →ₗ[O] W.DD T)
    (hf : ∀ (k : ℕ) (x : W.DD T), f (((PD.p : ℕ) : LetA O n) ^ k • x) = ((PD.p : ℕ) : LetA O n) ^ k • f x)
    (J : ℕ) (a : ℕ → ℕ) (K : ℕ) (w : W.DD T) (B : ℕ → W.DD T) :
    f (((PD.p : ℕ) : LetA O n) ^ J • w - ∑ y ∈ Finset.range K, ((PD.p : ℕ) : LetA O n) ^ a y • B y) -
        (((PD.p : ℕ) : LetA O n) ^ J • w - ∑ y ∈ Finset.range K, ((PD.p : ℕ) : LetA O n) ^ a y • B y) =
      ((PD.p : ℕ) : LetA O n) ^ J • (f w - w) -
        ∑ y ∈ Finset.range K, ((PD.p : ℕ) : LetA O n) ^ a y • (f (B y) - B y) := by
  rw [map_sub, hf, map_sum]
  simp only [hf, smul_sub, Finset.sum_sub_distrib]
  abel

theorem natCast_pow_smul_sub_sum_eq {T : LocLat G Qp LL O} (j e0 : ℕ) (a : ℕ → ℕ) (K : ℕ) (X : W.DD T) (B : ℕ → W.DD T) :
    ((PD.p : ℕ) : O) ^ j • (((PD.p : ℕ) : O) ^ e0 • X - ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ a y • B y) =
      ((PD.p : ℕ) : LetA O n) ^ j • (((PD.p : ℕ) : LetA O n) ^ e0 • X -
        ∑ y ∈ Finset.range K, ((PD.p : ℕ) : LetA O n) ^ a y • B y) := by
  simp only [lO_smul]

theorem p_power_smul_sub_sum {T : LocLat G Qp LL O} (j e0 : ℕ) (a : ℕ → ℕ) (K : ℕ) (X : W.DD T) (B : ℕ → W.DD T) :
    ((PD.p : ℕ) : LetA O n) ^ j • (((PD.p : ℕ) : LetA O n) ^ e0 • X -
        ∑ y ∈ Finset.range K, ((PD.p : ℕ) : LetA O n) ^ a y • B y) =
      ((PD.p : ℕ) : LetA O n) ^ (j + e0) • X -
        ∑ y ∈ Finset.range K, ((PD.p : ℕ) : LetA O n) ^ (j + a y) • B y := by
  rw [smul_sub, Finset.smul_sum, smul_smul, ← pow_add]
  congr 1
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [smul_smul, ← pow_add]

theorem φA_AΔ {a : LetA O n} (ha : a ∈ W.AΔ) : W.φA a ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ (W.φA a) = W.φA a
  intro δ hδ
  have ha' : W.γA δ a = a := ha δ hδ
  rw [← W.φA_γA, ha']

theorem key_id {T : LocLat G Qp LL O} (σ J K : ℕ) (e : ℕ → ℕ) (he : ∀ y ∈ Finset.range K, e y ≤ J)
    (w : W.DD T) (cc : ℕ → W.DD T) (r s : ℕ → LetA O n)
    (hrs : ∀ y, ((PD.p : ℕ) : LetA O n) ^ e y * s y = ((PD.p : ℕ) : LetA O n) ^ σ * r y) :
    ((PD.p : ℕ) : LetA O n) ^ J • (((PD.p : ℕ) : O) ^ σ • W.φD T w -
        ∑ y ∈ Finset.range K, s y • W.φD T (cc y)) =
      ((PD.p : ℕ) : LetA O n) ^ σ • W.φD T (((PD.p : ℕ) : LetA O n) ^ J • w -
        ∑ y ∈ Finset.range K, ((PD.p : ℕ) : LetA O n) ^ (J - e y) • (W.π₀ ^ y • cc y)) +
      ∑ y ∈ Finset.range K, ((PD.p : ℕ) : LetA O n) ^ (σ + (J - e y)) •
        ((W.φA W.π₀ ^ y - r y) • W.φD T (cc y)) := by
  have hterm : ∀ y ∈ Finset.range K, ((PD.p : ℕ) : LetA O n) ^ J * s y =
      ((PD.p : ℕ) : LetA O n) ^ (σ + (J - e y)) * r y := by
    intro y hy
    have hJ : J = (J - e y) + e y := (Nat.sub_add_cancel (he y hy)).symm
    calc ((PD.p : ℕ) : LetA O n) ^ J * s y
        = ((PD.p : ℕ) : LetA O n) ^ (J - e y) * (((PD.p : ℕ) : LetA O n) ^ e y * s y) := by
          conv_lhs => rw [hJ]
          rw [pow_add, mul_assoc]
      _ = ((PD.p : ℕ) : LetA O n) ^ (σ + (J - e y)) * r y := by
          rw [hrs, pow_add]
          ring
  rw [lO_smul, map_sub, map_sum, φ_lA]
  simp only [φ_lA, φD_smulA, map_pow, map_natCast]
  rw [smul_sub, smul_sub, Finset.smul_sum, Finset.smul_sum, smul_smul, smul_smul,
    mul_comm (((PD.p : ℕ) : LetA O n) ^ J), sub_add, sub_right_inj, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y hy => ?_
  simp only [smul_smul]
  rw [← sub_smul, hterm y hy]
  congr 1
  rw [pow_add]
  ring

def GrInj (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (K : ℕ) (h : W.DD T),
    InPN W T 1 h → InPN W T K (W.γ T h - h) → ∃ E : ℕ, InPN W T K (((PD.p : ℕ) : O) ^ E • h)

theorem clause5 [IsDomain O] (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hR : RingA W)
    (hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0)
    {T : LocLat G Qp LL O} (hT : IsCrys PD T.ρ) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    {H M η : ℕ} {hi : ZMod n → ℕ} (hHM : H < (PD.p - 1) * M) (h11 : 11 ≤ PD.p)
    (h5T : Formalism.MainNotions.DeltaInvariantLattices.p5 W T (fun _ => H) hi) {c : ZMod n}
    (hqη : ∀ x ∈ W.N T, (letE c : LetA O n) • x = x → Formalism.MainNotions.LiftingTheory.qp W ^ η • W.φD T x ∈ W.N T)
    (c1 : ∀ x ∈ W.NΔ T, ∃ y ∈ W.NΔ T, W.φD T (W.π₀ ^ M • x) = (W.π₀ ^ M * Formalism.MainNotions.WachCoordinates.qP W) • y)
    (c2 : ∀ w : W.DD T, InPM T M w → ∃! z : W.DD T, InPM T M z ∧ W.φD T z - z = w)
    (h2aK : Formalism.MainNotions.DeltaInvariantLattices.p2aK W T) (hInv : GrInj W) {σ : ℕ} {w z : W.DD T}
    (hw : InI W T c w) (htr : IsTrunc W T c 1 M η σ w z) :
    (∃ x : W.wachCocyclesDelta T, (x : W.DD T × W.DD T).1 = z ∧ InPN W T M (x : W.DD T × W.DD T).2) ∧
      (InPN W T 1 w → ∀ x : W.wachCocyclesDelta T, (x : W.DD T × W.DD T).1 = z →
        InPN W T M (x : W.DD T × W.DD T).2 → W.clK T x = 0) := by
  obtain ⟨hDL, ⟨kk, k, hk⟩, -⟩ := hw
  obtain ⟨cc, r, s, ⟨hc0, hcc, hser⟩, hrs, hz⟩ := htr
  have hg : W.gamK = W.gam := W.gamK_eq_one hA.2.1 hA.2.2
  obtain ⟨h3, h6⟩ := ring_clauses W hR
  set L : LetA O n := ((PD.p : ℕ) : LetA O n) with hL
  set K := max M η + 1 with hK
  obtain ⟨j, hj⟩ := hser K
  have hl1 : (0 : ℝ) ≤ (PD.p : ℝ) - 1 := by
    have : (11 : ℝ) ≤ PD.p := by exact_mod_cast h11
    linarith
  have heK : ∀ y ∈ Finset.range K, eY PD.p y ≤ eY PD.p K := by
    intro y hy
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_right _ hl1
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (Finset.mem_range.1 hy).le
  have hz' : z = ((PD.p : ℕ) : O) ^ σ • W.φD T w - ∑ y ∈ Finset.range K, s y • W.φD T (cc y) := by
    rw [hz]; simp only [pow_one]
  have hrs' : ∀ y, L ^ eY PD.p y * s y = L ^ σ * r y := fun y => (hrs y).2
  have hrem : ∀ y, ∃ g, W.φA W.π₀ ^ y - r y = W.π₀ ^ M * Formalism.MainNotions.LiftingTheory.qp W ^ η * g := fun y => by
    obtain ⟨-, g, hg'⟩ := (hrs y).1
    exact ⟨g, by simpa [pow_one, fMX] using hg'⟩
  have ht : ∀ y, InMN T M ((W.φA W.π₀ ^ y - r y) • W.φD T (cc y)) := by
    intro y
    obtain ⟨g, hg'⟩ := hrem y
    refine ⟨g • (Formalism.MainNotions.LiftingTheory.qp W ^ η • W.φD T (cc y)),
      Submodule.smul_mem _ _ (hqη _ (hcc y).2 (hcc y).1.1), ?_⟩
    rw [hg', smul_smul, smul_smul]
    congr 1
    ring
  have htop : ∀ ν ∈ W.N T, InMN T M ((W.φA W.π₀) ^ K • W.φD T ν) := by
    intro ν hν
    obtain ⟨u, hu⟩ := h6
    obtain ⟨a, ha⟩ : ∃ a, K = M + a := ⟨K - M, by omega⟩
    have hMK : (PD.p - 1) * M ≤ (PD.p - 1) * K := Nat.mul_le_mul_left _ (by omega)
    obtain ⟨b', hb'⟩ : ∃ b', (PD.p - 1) * K = H + b' := ⟨(PD.p - 1) * K - H, by omega⟩
    refine ⟨((u : LetA O n) ^ K * W.π₀ ^ a * Formalism.MainNotions.LiftingTheory.qp W ^ b') •
      (Formalism.MainNotions.LiftingTheory.qp W ^ H • W.φD T ν), Submodule.smul_mem _ _ (qpow_φ_mem hA.2.1 hR h5T hν), ?_⟩
    rw [hu, smul_smul, smul_smul]
    congr 1
    rw [mul_pow, mul_pow, ← pow_mul, hb', show W.π₀ ^ K = W.π₀ ^ M * W.π₀ ^ a by rw [ha, pow_add]]
    simp only [Formalism.MainNotions.LiftingTheory.qp, pow_add]
    ring
  have hqpΔ : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := W.AΔ.add_mem hR.1 (W.AΔ.natCast_mem _)
  have hrΔ : ∀ y, r y ∈ W.AΔ := by
    intro y
    obtain ⟨⟨a, ha⟩, -⟩ := (hrs y).1
    rw [ha]
    exact Subalgebra.sum_mem _ fun i _ => W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hR.1 _)
  have hsΔ : ∀ y, s y ∈ W.AΔ := fun y => mem_AΔ_of_p_pow W hO (eY PD.p y) (by
    rw [hrs' y]; exact W.AΔ.mul_mem (W.AΔ.pow_mem (W.AΔ.natCast_mem _) _) (hrΔ y))
  have hzΔ : ∀ δ ∈ W.DelF, W.γD T δ z = z := by
    intro δ hδ
    rw [hz', map_sub, map_sum, map_smul]
    congr 1
    · rw [← W.φγ_comm, hDL.2 δ hδ]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [γD_smulA, hsΔ y δ hδ, ← W.φγ_comm, (hcc y).1.2 δ hδ]
  have huΔ : ∀ δ ∈ W.DelF, W.γD T δ (W.γ T z - z) = W.γ T z - z := by
    intro δ hδ
    rw [map_sub, hzΔ δ hδ]
    congr 1
    show W.γD T δ (W.γD T W.gam z) = W.γD T W.gam z
    rw [← W.γD_mul, mul_comm, W.γD_mul, hzΔ δ hδ]
  set Λ := (∏ i ∈ Finset.range kk, Formalism.MainNotions.LiftingTheory.pk W i) ^ k with hΛ
  set f2 := Formalism.MainNotions.LiftingTheory.qp W ^ H * W.φA Λ with hf2
  have hUf2 : UPi PD.p f2 := by
    refine UPi.mul (UPi.pow ?_ H) ?_
    · have h0 := UPi_qpow W h3 h6 0
      rw [pow_zero, AlgHom.one_apply] at h0
      exact h0
    · rw [hΛ, map_pow, map_prod]
      refine UPi.pow (UPi.prod _ _ fun i _ => ?_) k
      simp only [Formalism.MainNotions.LiftingTheory.pk, Formalism.MainNotions.LiftingTheory.qp, φ_pow_apply]
      exact UPi_qpow W h3 h6 (i + 1)
  have hΛΔ : Λ ∈ W.AΔ := W.AΔ.pow_mem (Subalgebra.prod_mem _ fun i _ => φpow_AΔ hqpΔ i) k
  have hf2Δ : f2 ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.pow_mem hqpΔ H) (φA_AΔ hΛΔ)
  have hf2z : f2 • z ∈ W.N T := by
    rw [hz', smul_sub, Finset.smul_sum]
    refine Submodule.sub_mem _ ?_ (Submodule.sum_mem _ fun y _ => ?_)
    · rw [smul_comm f2 (((PD.p : ℕ) : O) ^ σ)]
      refine Submodule.smul_of_tower_mem _ _ ?_
      rw [hf2, mul_smul, ← φD_smulA]
      exact qpow_φ_mem hA.2.1 hR h5T hk
    · rw [smul_comm f2 (s y)]
      refine Submodule.smul_mem _ _ ?_
      rw [hf2, mul_smul, smul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ H)]
      exact Submodule.smul_mem _ _ (qpow_φ_mem hA.2.1 hR h5T (hcc y).2)
  obtain ⟨⟨rb, bb, hbb, huniq, hbΔ⟩, -⟩ := hmod
  have hUM : UPi PD.p (W.π₀ ^ M) := (UPi_π₀ W h3).pow M
  have concl : ∀ (x : W.DD T) (f' : LetA O n) (J : ℕ), UPi PD.p f' → f' • x ∈ W.NΔ T →
      (∀ δ ∈ W.DelF, W.γD T δ x = x) → InMN T M (L ^ J • x) → InPM T M x := by
    rintro x f' J hf' hfx hxΔ ⟨Yt, hYt, hYe⟩
    have hYtΔ : ∀ δ ∈ W.DelF, W.γD T δ Yt = Yt := by
      intro δ hδ
      apply smul_cancel W T (isUnit_EE_of_UPi W hUM)
      have e1 := congrArg (W.γD T δ) hYe
      rw [γ_lA, hxΔ δ hδ, γD_smulA, (W.AΔ.pow_mem hR.1 M) δ hδ] at e1
      exact e1.symm.trans hYe
    obtain ⟨z', hz'N, hz'e⟩ := sat_basis W hO T bb hbb huniq hbΔ hUM hf' x hfx J Yt ⟨hYt, hYtΔ⟩ hYe
    exact ⟨z', hz'N, hz'e⟩

  have hmainZ : ∀ J, (∀ y ∈ Finset.range K, eY PD.p y ≤ J) → ∀ ν ∈ W.N T,
      W.φD T (L ^ J • w - ∑ y ∈ Finset.range K, L ^ (J - eY PD.p y) • (W.π₀ ^ y • cc y)) =
        (W.φA W.π₀) ^ K • W.φD T ν → InMN T M (L ^ J • z) := by
    intro J hJ ν hν hφ
    rw [hz', key_id σ J K (eY PD.p) hJ w cc r s hrs', hφ]
    exact ((htop ν hν).smul _).add (InMN.sum _ _ fun y _ => (ht y).smul _)
  have hmainU : ∀ J, (∀ y ∈ Finset.range K, eY PD.p y ≤ J) → ∀ ν ∈ W.N T,
      W.φD T (W.γ T (L ^ J • w - ∑ y ∈ Finset.range K, L ^ (J - eY PD.p y) • (W.π₀ ^ y • cc y)) -
        (L ^ J • w - ∑ y ∈ Finset.range K, L ^ (J - eY PD.p y) • (W.π₀ ^ y • cc y))) =
        (W.φA W.π₀) ^ K • W.φD T ν → InMN T M (L ^ J • (W.γ T z - z)) := by
    intro J hJ ν hν hφ
    have e1 : L ^ J • (W.γ T z - z) = W.γ T (L ^ J • z) - L ^ J • z := by rw [γ'_lA, smul_sub]
    have hγφ : ∀ x : W.DD T, W.γ T (W.φD T x) = W.φD T (W.γ T x) := fun x => (W.φγ_comm T W.gam x).symm
    have eA : ∀ x : W.DD T, W.γ T (L ^ σ • W.φD T x) - L ^ σ • W.φD T x = L ^ σ • W.φD T (W.γ T x - x) :=
      fun x => by rw [γ'_lA, hγφ, ← smul_sub, ← map_sub]
    have eS : ∀ (f : ℕ → W.DD T), W.γ T (∑ y ∈ Finset.range K, f y) - ∑ y ∈ Finset.range K, f y =
        ∑ y ∈ Finset.range K, (W.γ T (f y) - f y) := fun f => by
      rw [map_sum, Finset.sum_sub_distrib]
    have e2 : ∀ a b : W.DD T, W.γ T (a + b) - (a + b) = (W.γ T a - a) + (W.γ T b - b) := fun a b => by
      rw [map_add]; abel
    rw [e1, hz', key_id σ J K (eY PD.p) hJ w cc r s hrs', e2, eA, eS, hφ]
    exact ((htop ν hν).smul _).add (InMN.sum _ _ fun y _ => ((ht y).smul _).γsub hR)
  refine ⟨?_, ?_⟩
  · obtain ⟨ν, hν, -, hνe⟩ := hj
    have hJ : ∀ y ∈ Finset.range K, eY PD.p y ≤ j + eY PD.p K :=
      fun y hy => (heK y hy).trans (Nat.le_add_left _ _)
    have hs : ∀ y ∈ Finset.range K, j + (eY PD.p K - eY PD.p y) = j + eY PD.p K - eY PD.p y :=
      fun y hy => by have := heK y hy; omega
    have hγh : W.γ T (L ^ (j + eY PD.p K) • w -
          ∑ y ∈ Finset.range K, L ^ (j + eY PD.p K - eY PD.p y) • (W.π₀ ^ y • cc y)) -
        (L ^ (j + eY PD.p K) • w -
          ∑ y ∈ Finset.range K, L ^ (j + eY PD.p K - eY PD.p y) • (W.π₀ ^ y • cc y)) =
        ((PD.p : ℕ) : O) ^ j • (((PD.p : ℕ) : O) ^ eY PD.p K • (W.γ T w - w) -
          ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (eY PD.p K - eY PD.p y) •
            (W.γ T (W.π₀ ^ y • cc y) - W.π₀ ^ y • cc y)) := by
      rw [lin_id (W.γ T) γ'_lA, natCast_pow_smul_sub_sum_eq, p_power_smul_sub_sum]
      congr 1
      exact Finset.sum_congr rfl fun y hy => by rw [hs y hy]
    have hφ : W.φD T (W.γ T (L ^ (j + eY PD.p K) • w -
          ∑ y ∈ Finset.range K, L ^ (j + eY PD.p K - eY PD.p y) • (W.π₀ ^ y • cc y)) -
        (L ^ (j + eY PD.p K) • w -
          ∑ y ∈ Finset.range K, L ^ (j + eY PD.p K - eY PD.p y) • (W.π₀ ^ y • cc y))) =
        (W.φA W.π₀) ^ K • W.φD T ν := by
      rw [hγh, hνe, φD_smulA, map_pow]
    have hU := hmainU _ hJ ν hν hφ
    have hfu : (f2 * W.γA W.gam f2) • (W.γ T z - z) ∈ W.NΔ T := by
      refine ⟨?_, fun δ hδ => ?_⟩
      · rw [smul_sub]
        refine Submodule.sub_mem _ ?_ ?_
        · rw [mul_smul]
          refine Submodule.smul_mem _ _ ?_
          have : W.γA W.gam f2 • W.γ T z = W.γ T (f2 • z) := (γD_smulA W T W.gam f2 z).symm
          rw [this]
          exact W.N_Γ T _ _ hf2z
        · rw [mul_comm, mul_smul]
          exact Submodule.smul_mem _ _ hf2z
      · rw [γD_smulA, (W.AΔ.mul_mem hf2Δ (γA_AΔ hf2Δ W.gam)) δ hδ, huΔ δ hδ]
    have hu := concl (W.γ T z - z) _ _ (hUf2.mul (UPi_γA W.gam hUf2)) hfu huΔ hU
    obtain ⟨mm, ⟨hm, hφm⟩, -⟩ := c2 _ hu
    refine ⟨⟨(z, mm), (mem_Z1DΔ z mm).2 ⟨?_, hzΔ, inPM_Δ hR hm⟩⟩, rfl, inPN_iff.2 hm⟩
    rw [hg, hφm]
    rfl
  · rintro ⟨w', hw', hw'Δ, hw'e⟩ x hx1 hx2
    set hh := L ^ j • (L ^ eY PD.p K • w - ∑ y ∈ Finset.range K,
      L ^ (eY PD.p K - eY PD.p y) • (W.π₀ ^ y • cc y)) with hhdef
    have hγhh : W.γ T hh - hh = ((PD.p : ℕ) : O) ^ j • (((PD.p : ℕ) : O) ^ eY PD.p K • (W.γ T w - w) -
          ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (eY PD.p K - eY PD.p y) •
            (W.γ T (W.π₀ ^ y • cc y) - W.π₀ ^ y • cc y)) := by
      rw [hhdef, γ'_lA, ← smul_sub, lin_id (W.γ T) γ'_lA, natCast_pow_smul_sub_sum_eq]
    have hB : ∀ y, W.π₀ ^ y • cc y = W.π₀ • (W.π₀ ^ (y - 1) • cc y) := by
      intro y
      rcases y with _ | y
      · simp [hc0]
      · rw [smul_smul, ← pow_succ']
        simp
    have hh1 : InPN W T 1 hh := by
      refine ⟨L ^ j • (L ^ eY PD.p K • w' - ∑ y ∈ Finset.range K,
        L ^ (eY PD.p K - eY PD.p y) • (W.π₀ ^ (y - 1) • cc y)), ?_, ?_, ?_⟩
      · refine Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hw')
          (Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hcc y).2)))
      · intro δ hδ
        rw [γ_lA, map_sub, γ_lA, hw'Δ δ hδ, map_sum]
        congr 2
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [γ_lA, γD_smulA, (W.AΔ.pow_mem hR.1 _) δ hδ, (hcc y).1.2 δ hδ]
      · rw [hhdef, hw'e, pow_one, smul_comm W.π₀ (L ^ j)]
        congr 1
        rw [smul_sub, smul_comm W.π₀ (L ^ eY PD.p K), Finset.smul_sum]
        congr 1
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [smul_comm W.π₀, ← hB y]
    obtain ⟨E, ν, hν, -, hνe⟩ := hInv hA T hT K hh hh1 (by rw [hγhh]; exact hj)
    set J := E + (j + eY PD.p K) with hJdef
    have hJ : ∀ y ∈ Finset.range K, eY PD.p y ≤ J := fun y hy => (heK y hy).trans (by omega)
    have he : L ^ J • w - ∑ y ∈ Finset.range K, L ^ (J - eY PD.p y) • (W.π₀ ^ y • cc y) =
        ((PD.p : ℕ) : O) ^ E • hh := by
      rw [hhdef, lO_smul, p_power_smul_sub_sum, p_power_smul_sub_sum]
      have hs : ∀ y ∈ Finset.range K, E + (j + (eY PD.p K - eY PD.p y)) = J - eY PD.p y := fun y hy => by
        have := heK y hy; omega
      congr 1
      exact (Finset.sum_congr rfl fun y hy => by rw [hs y hy]).symm
    have hZ := hmainZ J hJ ν hν (by rw [he, hνe, φD_smulA, map_pow])
    have hf2zΔ : f2 • z ∈ W.NΔ T :=
      ⟨hf2z, fun δ hδ => by rw [γD_smulA, hf2Δ δ hδ, hzΔ δ hδ]⟩
    have hzM := concl z f2 J hUf2 hf2zΔ hzΔ hZ
    obtain ⟨mm, ⟨hm, hφm⟩, -⟩ := c2 z hzM
    have hx2' : (x : W.DD T × W.DD T).2 = W.γD T W.gamK mm - mm := by
      refine inPM_inj hR c1 c2 (inPN_iff.1 hx2) (inPM_sub (inPM_γK hR hg hm) hm) ?_
      rw [← coc_of x, hx1, ← hφm, map_sub, map_sub, W.φγ_comm]
      abel
    exact ((h2aK hA.2.1 hA.2.2).2 x).2 ⟨mm, inPM_Δ hR hm, Prod.ext (hx1.trans hφm.symm) hx2'⟩

end Alg5

section GrInjProof

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

open Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.UnusedSlot80.SatW Formalism.MainNotions.UnusedSlot80.WachFrobeniusLattice Formalism.MainNotions.WachCoordinates.Br

theorem cc_γ₀ (g : W.Gam) (a : PowerSeries O) :
    PowerSeries.constantCoeff (W.γ₀ g a) = PowerSeries.constantCoeff a := by
  have hC : ∀ c : O, W.γ₀ g (PowerSeries.C c) = PowerSeries.C c := by
    intro c
    have : PowerSeries.C c = algebraMap O (PowerSeries O) c := by simp
    rw [this, AlgHom.commutes]
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const a]
  rw [map_add, map_mul, hC, map_add, map_mul, (W.γ₀_X g).1, zero_mul, zero_add,
    PowerSeries.constantCoeff_C]

theorem divπ (a : LetA O n) (h : ∀ i, PowerSeries.constantCoeff (a i) = 0) : ∃ r : LetA O n, a = letπ * r := by
  refine ⟨fun i => PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (a i), funext fun i => ?_⟩
  have := PowerSeries.eq_X_mul_shift_add_const (a i)
  rw [h i, map_zero, add_zero] at this
  simpa [letπ] using this

theorem χ_pow_ne_one (hR0 : RToolNum W) (N : ℕ) (hN : 0 < N) :
    (((W.χΓ W.gam) ^ N : Oˣ) : O) ≠ 1 := by
  intro h1
  have e : cR W (-(N : ℤ)) = 0 := by
    unfold cR
    rw [neg_neg, zpow_natCast, h1, map_one, sub_self, zero_div]
  have := hR0.2 (-(N : ℤ)) 0 (by omega)
  rw [e, hR0.1, sub_zero, AddValuation.map_zero] at this
  exact WithTop.top_ne_coe this

theorem mem_π₀_of_const [IsDomain O] (hR : RingA W) {T : LocLat G Qp LL O} (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    {x : W.DD T} (hx : x ∈ W.N T) {c : O} (hc : c ≠ 0) {z : W.DD T} (hz : z ∈ W.N T)
    (hcz : algebraMap O (LetA O n) c • x = W.π₀ • z) : ∃ x₁ ∈ W.N T, x = W.π₀ • x₁ := by
  obtain ⟨⟨r, b, hb, huniq, -⟩, -⟩ := hmod
  obtain ⟨w', hw'⟩ := hR.2.2.1
  obtain ⟨a, ha, -⟩ := huniq x hx
  obtain ⟨zz, hzz, -⟩ := huniq z hz
  have hcx : algebraMap O (LetA O n) c • x ∈ W.N T := Submodule.smul_mem _ _ hx
  obtain ⟨_, -, hu⟩ := huniq _ hcx
  have e1 : algebraMap O (LetA O n) c • x = ∑ j, (algebraMap O (LetA O n) c * a j) • b j := by
    rw [ha, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
  have e2 : algebraMap O (LetA O n) c • x = ∑ j, (W.π₀ * zz j) • b j := by
    rw [hcz, hzz, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
  have hcoef : (fun j => algebraMap O (LetA O n) c * a j) = fun j => W.π₀ * zz j :=
    (hu _ e1).trans (hu _ e2).symm
  have hdiv : ∀ j, ∃ q : LetA O n, a j = letπ ^ (PD.p - 1) * q := by
    intro j
    have hj := congrFun hcoef j
    have hi : ∀ i, (PowerSeries.X : PowerSeries O) ^ (PD.p - 1) ∣ a j i := by
      intro i
      have hii := congrFun hj i
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      have h0 : PowerSeries.coeff m ((algebraMap O (LetA O n) c * a j) i) = 0 := by
        rw [hii, hw']
        simp only [Pi.mul_apply, Pi.pow_apply, letπ]
        rw [mul_comm ((w' : LetA O n) i), mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
      have h1 : PowerSeries.coeff m ((algebraMap O (LetA O n) c * a j) i) =
          c * PowerSeries.coeff m (a j i) := by
        simp [Pi.mul_apply, PowerSeries.coeff_C_mul]
      rw [h1] at h0
      exact (mul_eq_zero.1 h0).resolve_left hc
    choose q hq using hi
    exact ⟨fun i => q i, funext fun i => by simpa [letπ, Pi.mul_apply] using hq i⟩
  choose q hq using hdiv
  refine ⟨∑ j, (((w'⁻¹ : (LetA O n)ˣ) : LetA O n) * q j) • b j,
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hb j).1, ?_⟩
  rw [ha, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, hq j, hw']
  congr 1
  have : (w' : LetA O n) * ((w'⁻¹ : (LetA O n)ˣ) : LetA O n) = 1 := Units.mul_inv w'
  linear_combination (-(letπ ^ (PD.p - 1) * q j)) * this

theorem inPN_one_of_gamma_sub [IsDomain O] (hR : RingA W) {T : LocLat G Qp LL O} (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    (hp : Nat.Prime PD.p) (hl2 : PD.p ≠ 2)
    (hχ : ∀ N : ℕ, 0 < N → (((W.χΓ W.gam) ^ N : Oˣ) : O) ≠ 1)
    (k : ℕ) (hk : 1 ≤ k) (x : W.DD T) (hx : x ∈ W.NΔ T)
    (hγ : InPN W T (k + 1) (W.γ T (W.π₀ ^ k • x) - W.π₀ ^ k • x)) : InPN W T 1 x := by
  obtain ⟨w', hw'⟩ := hR.2.2.1
  obtain ⟨u', hu'⟩ := γA_letπ (W := W) W.gam
  obtain ⟨U, hUdef⟩ : ∃ U : LetA O n, U = W.γA W.gam (w' : LetA O n) *
      ((w'⁻¹ : (LetA O n)ˣ) : LetA O n) * (u' : LetA O n) ^ (PD.p - 1) := ⟨_, rfl⟩
  have hww : (w' : LetA O n) * ((w'⁻¹ : (LetA O n)ˣ) : LetA O n) = 1 := Units.mul_inv w'
  have hU : W.γA W.gam W.π₀ = W.π₀ * U := by
    rw [hw', map_mul, map_pow, hu', mul_pow, hUdef]
    linear_combination (-(W.γA W.gam (w' : LetA O n) * (u' : LetA O n) ^ (PD.p - 1) *
      letπ ^ (PD.p - 1))) * hww
  obtain ⟨x', hx', hxe⟩ := hmod.2 x hx
  obtain ⟨y, hy, -, hye⟩ := hγ
  have h1 : W.γ T (W.π₀ ^ k • x) = W.π₀ ^ k • (U ^ k • x) + W.π₀ ^ k • (U ^ k • (W.π₀ • x')) := by
    have hgx : W.γ T x = x + W.π₀ • x' := by rw [← hxe]; abel
    show W.γD T W.gam (W.π₀ ^ k • x) = _
    rw [γD_smulA, map_pow, hU, mul_pow, mul_smul]
    show W.π₀ ^ k • (U ^ k • W.γ T x) = _
    rw [hgx, smul_add, smul_add]
  have e1 : W.π₀ ^ k • ((U ^ k - 1) • x) = W.π₀ ^ k • (W.π₀ • (y - U ^ k • x')) := by
    have h2 : W.π₀ ^ k • (U ^ k • (W.π₀ • x')) = W.π₀ ^ (k + 1) • (U ^ k • x') := by
      rw [smul_comm (U ^ k) W.π₀ x', smul_smul, ← pow_succ]
    have h3 : W.π₀ ^ k • (W.π₀ • (y - U ^ k • x')) = W.π₀ ^ (k + 1) • y - W.π₀ ^ (k + 1) • (U ^ k • x') := by
      rw [smul_smul, ← pow_succ, smul_sub]
    rw [h3, ← hye, h1, h2, sub_smul, one_smul, smul_sub]
    abel
  have e2 : (U ^ k - 1) • x = W.π₀ • (y - U ^ k • x') :=
    smul_cancel W T (isUnit_EE_of_UPi W ((UPi_π₀ W (ring_clauses W hR).1).pow k)) e1
  have hcu : ∀ i, PowerSeries.constantCoeff ((u' : LetA O n) i) = ((W.χΓ W.gam : Oˣ) : O) := by
    intro i
    have h2 := congrFun hu' i
    have h3 : (W.γA W.gam letπ) i = W.γ₀ W.gam PowerSeries.X := rfl
    rw [h3] at h2
    have := (W.γ₀_X W.gam).2
    rw [h2, Pi.mul_apply] at this
    simpa [letπ, PowerSeries.coeff_succ_mul_X] using this
  have hcU : ∀ i, PowerSeries.constantCoeff ((U ^ k) i) = ((W.χΓ W.gam : Oˣ) : O) ^ ((PD.p - 1) * k) := by
    intro i
    have hwi : PowerSeries.constantCoeff ((w' : LetA O n) i) *
        PowerSeries.constantCoeff (((w'⁻¹ : (LetA O n)ˣ) : LetA O n) i) = 1 := by
      rw [← map_mul, ← Pi.mul_apply, hww]; simp
    have hγw : (W.γA W.gam (w' : LetA O n)) i = W.γ₀ W.gam ((w' : LetA O n) i) := rfl
    rw [Pi.pow_apply, map_pow, hUdef, Pi.mul_apply, Pi.mul_apply, Pi.pow_apply, map_mul, map_mul, map_pow,
      hγw, cc_γ₀, hwi, one_mul, hcu, ← pow_mul]
  obtain ⟨c, hcdef⟩ : ∃ c : O, c = ((W.χΓ W.gam : Oˣ) : O) ^ ((PD.p - 1) * k) - 1 := ⟨_, rfl⟩
  have hpos : 0 < (PD.p - 1) * k := Nat.mul_pos (by have := hp.two_le; omega) hk
  have hc : c ≠ 0 := by
    have := hχ _ hpos
    rw [Units.val_pow_eq_pow_val] at this
    rw [hcdef]
    exact sub_ne_zero.2 this
  obtain ⟨r, hr⟩ := divπ (U ^ k - 1 - algebraMap O (LetA O n) c) fun i => by
    rw [Pi.sub_apply, Pi.sub_apply, map_sub, map_sub, hcU i, hcdef]
    simp
  have hev : Even (PD.p - 1) := hp.even_sub_one hl2
  have hsub : algebraMap O (LetA O n) c - -(letπ * r) = U ^ k - 1 := by
    rw [sub_neg_eq_add, ← hr]; ring
  obtain ⟨S, hS⟩ : ∃ S : LetA O n, S = ∑ i ∈ Finset.range (PD.p - 1),
      algebraMap O (LetA O n) c ^ i * (-(letπ * r)) ^ (PD.p - 1 - 1 - i) := ⟨_, rfl⟩
  have hgeom := geom_sum₂_mul (algebraMap O (LetA O n) c) (-(letπ * r)) (PD.p - 1)
  rw [← hS, hsub, hev.neg_pow] at hgeom
  have hkey : algebraMap O (LetA O n) (c ^ (PD.p - 1)) =
      S * (U ^ k - 1) + letπ ^ (PD.p - 1) * r ^ (PD.p - 1) := by
    rw [map_pow, ← mul_pow]
    linear_combination (-1 : LetA O n) * hgeom
  have hπm : (letπ : LetA O n) ^ (PD.p - 1) = ((w'⁻¹ : (LetA O n)ˣ) : LetA O n) * W.π₀ := by
    rw [hw', ← mul_assoc, mul_comm ((w'⁻¹ : (LetA O n)ˣ) : LetA O n), hww, one_mul]
  have hcx : algebraMap O (LetA O n) (c ^ (PD.p - 1)) • x =
      W.π₀ • (S • (y - U ^ k • x') + (((w'⁻¹ : (LetA O n)ˣ) : LetA O n) * r ^ (PD.p - 1)) • x) := by
    rw [hkey, add_smul, mul_smul, e2, smul_add]
    congr 1
    · exact smul_comm S W.π₀ _
    · rw [smul_smul, hπm]
      congr 1
      ring
  have hz : S • (y - U ^ k • x') + (((w'⁻¹ : (LetA O n)ˣ) : LetA O n) * r ^ (PD.p - 1)) • x ∈ W.N T :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ hy
      (Submodule.smul_mem _ _ hx'.1))) (Submodule.smul_mem _ _ hx.1)
  obtain ⟨x₁, hx₁, hx₁e⟩ := mem_π₀_of_const hR hmod hx.1 (pow_ne_zero (PD.p - 1) hc) hz hcx
  refine ⟨x₁, hx₁, fun δ hδ => ?_, by rw [pow_one]; exact hx₁e⟩
  apply smul_cancel W T (isUnit_EE_of_UPi W (UPi_π₀ W (ring_clauses W hR).1))
  have := hx.2 δ hδ
  rw [hx₁e, γD_smulA, hR.1 δ hδ] at this
  exact this

theorem inPN_mono {T : LocLat G Qp LL O} {K k : ℕ} {z : W.DD T} (hR : RingA W) (h : InPN W T K z)
    (hk : k ≤ K) : InPN W T k z := by
  obtain ⟨y, hy, hyΔ, rfl⟩ := h
  refine ⟨W.π₀ ^ (K - k) • y, Submodule.smul_mem _ _ hy, fun δ hδ => ?_, ?_⟩
  · rw [γD_smulA, (W.AΔ.pow_mem hR.1 _) δ hδ, hyΔ δ hδ]
  · rw [smul_smul, ← pow_add, Nat.add_sub_cancel' hk]

theorem grInj_of [IsDomain O] (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hp : Nat.Prime PD.p)
    (hχ : Formalism.MainNotions.LiftingTheory.CaseA W → ∀ N : ℕ, 0 < N → (((W.χΓ W.gam) ^ N : Oˣ) : O) ≠ 1) : GrInj W := by
  intro hA T hT K h hh1 hγ
  refine ⟨0, ?_⟩
  rw [pow_zero, one_smul]
  obtain ⟨hR, hmod⟩ := (h9 T hT hA.2.1 hA.2.2).2.2 (finrank_one_of_bij hA.1)
  have key : ∀ k, 1 ≤ k → k ≤ K → InPN W T k h := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base => intro _; exact hh1
    | succ k hk ih =>
      intro hkK
      obtain ⟨x, hx, hxΔ, hxe⟩ := ih (by omega)
      have hk' : InPN W T (k + 1) (W.γ T (W.π₀ ^ k • x) - W.π₀ ^ k • x) := by
        rw [← hxe]; exact inPN_mono hR hγ hkK
      obtain ⟨x₁, hx₁, hx₁Δ, hx₁e⟩ := inPN_one_of_gamma_sub hR hmod hp hA.2.2 (hχ hA) k hk x ⟨hx, hxΔ⟩ hk'
      exact ⟨x₁, hx₁, hx₁Δ, by rw [hxe, hx₁e, smul_smul, ← pow_add]⟩
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · exact inPN_mono hR hh1 (Nat.zero_le 1)
  · exact key K hK le_rfl

end GrInjProof

section FMain

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

open Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.UnusedSlot80.SatW Formalism.MainNotions.UnusedSlot80.WachFrobeniusLattice Formalism.MainNotions.WachCoordinates.Br

theorem FTool_of (W : LocWach PD LL O v n)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h7 : Formalism.MainNotions.DeltaInvariantLattices.WachCrystallineExtension W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (h2a : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexFirstProperty W) (h2b : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexSecondProperty W)
    (hres : W.gamK = W.gam → ∀ (T : LocLat G Qp LL O) (pr : ↥(W.wachCocyclesDelta T)) (pr' : ↥(W.divisibleCocycles T)),
      (pr' : W.DD T × W.DD T) = (pr : W.DD T × W.DD T) → resH1 T W.GKs (W.clK T pr) = W.cl T pr')
    (hcomp : IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O)
    (hDR : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (hχ : Formalism.MainNotions.LiftingTheory.CaseA W → ∀ N : ℕ, 0 < N → (((W.χΓ W.gam) ^ N : Oˣ) : O) ≠ 1) : FTool W := by
  intro d T₁ T₂ F b S η m hS T hT hJ hJη M
  obtain ⟨hA, h11, -, ⟨hdom, -, hfrac⟩, -⟩ := hS
  have := hdom
  have hg : W.gamK = W.gam := W.gamK_eq_one hA.2.1 hA.2.2
  have hfr : Module.finrank K₀ K = 1 := finrank_one_of_bij hA.1
  have hp1 : 0 < PD.p - 1 := by omega
  have hM : Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S < (PD.p - 1) * M := Nat.lt_mul_div_succ _ hp1
  obtain ⟨hi, hhi⟩ := exists_ub W hA.1 hDR T hT
  have hJ5 : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T (fun _ => Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S) hi :=
    fun τ i hτ a ha => ⟨hJ i τ hτ a ha, hhi i τ hτ a ha⟩
  let Mi' : ZMod n → ℕ := fun i => if ((i - 1).val + d) % 2 = 0 then η else Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S
  have hJ5' : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mi' hi := by
    intro τ i hτ a ha
    refine ⟨?_, hhi i τ hτ a ha⟩
    by_cases hc : ((i - 1).val + d) % 2 = 0
    · have h1 : Formalism.MainNotions.LiftingTheory.Over W τ (i - 1 + 1) := by rw [sub_add_cancel]; exact hτ
      have := hJη (i - 1) τ hc h1 a ha
      simpa [Mi', hc] using this
    · have := hJ i τ hτ a ha
      simpa [Mi', hc] using this
  have h5T := h5 T (fun _ => Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S) hi hT hJ5
  have h5T' := h5 T Mi' hi hT hJ5'
  obtain ⟨hR, hmod⟩ := (h9 T hT hA.2.1 hA.2.2).2.2 hfr
  obtain ⟨c1, c2⟩ := Frobenius_divisibility_unique_solution hR hA.2.1 T hmod _ M hi h5T hM hcomp
  have := hfrac
  have hqη : ∀ c : ZMod n, (c.val + d) % 2 = 0 → ∀ x ∈ W.N T, (letE c : LetA O n) • x = x →
      Formalism.MainNotions.LiftingTheory.qp W ^ η • W.φD T x ∈ W.N T := by
    intro c hc x hx hlet
    have hmem : x ∈ W.Nl T (c + 1 - 1) := by rw [add_sub_cancel_right]; exact ⟨x, hx, hlet⟩
    have := qP_pow_mem hA.2.1 hR (W.N T) (h5T'.1 (c + 1) _ hmem)
    simp only [Mi', add_sub_cancel_right, hc, if_true] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i x hx hDL
    obtain ⟨y, hy, e⟩ := c1 x ⟨hx, hDL.2⟩
    exact ⟨y, hy.1, e⟩
  · intro w hw
    obtain ⟨z, hz, hu⟩ := c2 w (inPN_iff.1 hw)
    exact ⟨z, ⟨inPN_iff.2 hz.1, hz.2⟩, fun z' hz' => hu z' ⟨inPN_iff.1 hz'.1, hz'.2⟩⟩
  · intro i x _ hx2
    refine ⟨fun hy => ?_, fun hpol => ?_⟩
    · obtain ⟨mm, ⟨hm, hφm⟩, -⟩ := c2 _ (inPN_iff.1 hy)
      have hzeq : (x : W.DD T × W.DD T).2 = W.γD T W.gamK mm - mm := by
        refine inPM_inj hR c1 c2 (inPN_iff.1 hx2) (inPM_sub (inPM_γK hR hg hm) hm) ?_
        rw [← coc_of x, map_sub, W.φγ_comm, ← hφm, map_sub]
        abel
      exact (((h2a T hT).2 hA.2.1 hA.2.2).2 x).2 ⟨mm, inPM_Δ hR hm, Prod.ext hφm.symm hzeq⟩
    · obtain ⟨k, k', hk⟩ := hpol
      refine wach_cocycle_class_mem_latticeFiniteCohomology W hA.2.1 hA.2.2 hfr h7 h9 h2b (hres hg) T hT M (Nat.mul_pos hp1 (Nat.succ_pos _)) x
        ?_ _ (Submonoid.pow_mem _ (Submonoid.prod_mem _ fun j _ =>
          frobenius_iterate_uniformizer_unit_products W hA.2.1 hA.2.2 hfr h9 T hT j) k') hk
      obtain ⟨y, hy, hΔ, e⟩ := hx2
      exact ⟨y, ⟨hy, hΔ⟩, e⟩
  · intro c x hc hx hlet
    have key : ∀ y ∈ W.φpull T,
        Formalism.MainNotions.LiftingTheory.qp W ^ η • ((letE (c + 1) : LetA O n) • y) ∈ W.N T := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨y0, hy0, rfl⟩ := hy
        have hφe : W.φA (letE c : LetA O n) = letE (c + 1) := by
          have := φA_letE (W := W) (c + 1)
          simpa only [add_sub_cancel_right] using this
        have e : (letE (c + 1) : LetA O n) • W.φD T y0 = W.φD T ((letE c : LetA O n) • y0) := by
          rw [φD_smulA, hφe]
        have hmem : (letE c : LetA O n) • y0 ∈ W.Nl T (c + 1 - 1) := by
          rw [add_sub_cancel_right]; exact ⟨y0, hy0, rfl⟩
        have := qP_pow_mem hA.2.1 hR (W.N T) (h5T'.1 (c + 1) _ hmem)
        simp only [Mi', add_sub_cancel_right, hc, if_true] at this
        rw [e]
        exact this
      | zero => rw [smul_zero, smul_zero]; exact Submodule.zero_mem _
      | add y y' _ _ hy hy' => rw [smul_add, smul_add]; exact Submodule.add_mem _ hy hy'
      | smul a y _ hy =>
        rw [smul_comm (letE (c + 1) : LetA O n) a y, smul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ η) a]
        exact Submodule.smul_mem _ _ hy
    have := key x hx
    rwa [hlet] at this
  · intro c w z hc hw htr
    exact clause5 hA hR (p_nzd_O W (IsFractionRing.injective O LL)) hT hmod hM h11 h5T (hqη c hc) c1 c2
      ((h2a T hT).2) (grInj_of h9 PD.hp hχ) hw htr

end FMain

section QMain

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

open Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.UnusedSlot80.WachFrobeniusLattice Formalism.MainNotions.WachCoordinates.Br

def ExtJumps (W : LocWach PD LL O v n) : Prop :=
  ∀ (T Y : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (π : LatHom Y.L W.one.L),
    IsSESLat (G := G) (Qp := Qp) (LL := LL) (O := O) ι π → IsCrys PD T.ρ → IsCrys PD Y.ρ →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD Y.ρ τ a → IsJumpV PD T.ρ τ a ∨ a = 0

theorem extJumps_of (W : LocWach PD LL O v n) (hJ : Formalism.MainNotions.LiftingTheory.coreJumps PD LL O)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) : ExtJumps W := by
  intro T Y ι π hses hT hY τ a ha
  have hker : LinearMap.ker π.f = LinearMap.range ι.f := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    exact hses.2.2.2.1 x
  have hone : IsCrys PD W.one.ρ :=
    (hC T.V T.ρ Y.V Y.ρ W.one.V W.one.ρ ι.f π.f ι.equiv π.equiv hses.1 hses.2.1 hker hY).2
  rcases (hJ T Y W.one ι π hses hT hY hone τ a).1 ha with h | h
  · exact Or.inl h
  · exact Or.inr (PI.HodgeOfFon.W.Triv.no_jump PD W.one.ρ W.one_triv τ a h)

theorem QToolOpen_of (W : LocWach PD LL O v n) (hX : Formalism.MainNotions.LiftingTheory.coreWX W) (hWA : Formalism.MainNotions.LiftingTheory.coreWA W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hY : ExtJumps W) :
    QToolOpen W := by
  intro d T₁ T₂ F b S η m Mi hi hS hJ
  obtain ⟨hA, h11, -, -, -, ⟨h1, h2, hon⟩, -⟩ := hS
  have hp1 : 0 < PD.p - 1 := by omega
  obtain ⟨hR, -⟩ := (h9 T₁ h1 hA.2.1 hA.2.2).2.2 (finrank_one_of_bij hA.1)
  obtain ⟨u, hu⟩ := hR.2.2.1
  have hXπ : W.X = letπ := by simp [LocWach.X, hA.2.1]
  have hkill : ∀ {T T' : LocLat G Qp LL O} (G' : LatHom T.L T'.L) (i : ZMod n),
      Formalism.MainNotions.LiftingTheory.Kills W G' i (W.X ^ Formalism.MainNotions.LiftingTheory.Hmax n Mi hi) →
      Formalism.MainNotions.LiftingTheory.Kills W G' i (W.π₀ ^ (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi / (PD.p - 1) + 1)) := by
    intro T T' G' i hK y hy
    obtain ⟨c, hc⟩ : ∃ c, (PD.p - 1) * (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi / (PD.p - 1) + 1) =
        Formalism.MainNotions.LiftingTheory.Hmax n Mi hi + c :=
      ⟨_, (Nat.add_sub_cancel' (Nat.lt_mul_div_succ (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi) hp1).le).symm⟩
    have e : W.π₀ ^ (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi / (PD.p - 1) + 1) =
        ((u : LetA O n) ^ (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi / (PD.p - 1) + 1) * letπ ^ c) *
          W.X ^ Formalism.MainNotions.LiftingTheory.Hmax n Mi hi := by
      rw [hu, mul_pow, ← pow_mul, hc, pow_add, hXπ]
      ring
    rw [e, mul_smul]
    exact Submodule.smul_mem _ _ (hK y hy)
  have hJ2 : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i → ∀ a : ℤ,
      IsJumpV PD T₂.ρ τ a → a ∈ Set.Icc (-(Mi i : ℤ)) (hi i) := fun i τ hτ a ha =>
    hJ i τ hτ a (Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jump_of W hA.1 hE hC hQ F h1 h2 hon τ i hτ a ha)
  refine ⟨fun i => hkill F i (hX T₁ T₂ F Mi hi ⟨h1, h2, hon⟩ hJ i), fun Y ι π hses hYc i => ?_⟩
  have hker : LinearMap.ker π.f = LinearMap.range ι.f := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    exact hses.2.2.2.1 x
  have hone : IsCrys PD W.one.ρ :=
    (hC T₂.V T₂.ρ Y.V Y.ρ W.one.V W.one.ρ ι.f π.f ι.equiv π.equiv hses.1 hses.2.1 hker hYc).2
  have hJY : Formalism.MainNotions.LiftingTheory.JumpsLet W Y Mi hi := by
    intro i τ hτ a ha
    rcases hY T₂ Y ι π hses h2 hYc τ a ha with h | h
    · exact hJ2 i τ hτ a h
    · subst h
      exact ⟨by simp, by simp⟩
  have hSπ : Formalism.MainNotions.LiftingTheory.Sur W π := ⟨hYc, hone, hses.2.2.1⟩
  exact ⟨hkill π i (hX Y W.one π Mi hi hSπ hJY i), hWA hA Y W.one π Mi hi hSπ hJY i⟩

theorem QTool_of_crys (W : LocWach PD LL O v n) (hX : Formalism.MainNotions.LiftingTheory.coreWX W) (hWA : Formalism.MainNotions.LiftingTheory.coreWA W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hY : ExtJumps W) :
    QTool W :=
  QTool_of_open W hWA (QToolOpen_of W hX hWA h9 hE hC hQ hY)

end QMain

section Rows

open Formalism.MainNotions.UnusedSlot80

theorem local_clause_of_frobenius_hyps (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h1 : Formalism.MainNotions.RamifiedCoefficientChains.adm1 D HW F Cm) (h3 : Formalism.MainNotions.RamifiedCoefficientChains.adm3 D HW F) (h11 : Formalism.MainNotions.RamifiedCoefficientChains.adm11 D) :
    adm16 D HW F Cm := by
  intro l _ K LL hg _
  have hT1 := h1 l K 1 LL hg
  have hP2 := h3 l K 1 LL hg
  exact FTool_of _ hT1.2.2.2.2.1 hT1.2.2.2.2.2.2.1 hT1.2.2.2.2.2.2.2.2.1 hP2.1 hP2.2.1
    ((F l).E K 1 LL hg).tie.clK_res (eq_sum_herm_smul_frame_of_inW (D.loc l) K LL) (h11 l K LL).2.2
    (fun hCA => χ_pow_ne_one (RToolNum_holds (D.loc l) (HW l) K LL hg hCA))

theorem local_clause_of_admitted_statements (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    {CR CA CB CK : ℝ} (hA : Formalism.MainNotions.RamifiedCoefficientChains.admitted D HW F Cm CR CA CB CK) : adm16 D HW F Cm :=
  local_clause_of_frobenius_hyps D HW F Cm hA.1 hA.2.2.1 hA.2.2.2.2.2.2.2.2.2.2.1

theorem QToolOpen_of_adm (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h1 : Formalism.MainNotions.RamifiedCoefficientChains.adm1 D HW F Cm) (h6 : Formalism.MainNotions.RamifiedCoefficientChains.adm6 D HW F) (h11 : Formalism.MainNotions.RamifiedCoefficientChains.adm11 D)
    (hJ : Formalism.MainNotions.LiftingTheory.adm23 D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))] : QToolOpen ((HW l).W K 1 LL hg) :=
  QToolOpen_of _ (h6.1 l K 1 LL hg) (h6.2.2.1 l K 1 LL hg) (h1 l K 1 LL hg).2.2.2.2.2.2.2.2.1
    (h11 l K LL).1 (h11 l K LL).2.1 (h11 l K LL).2.2 (extJumps_of _ (hJ l K LL) (h11 l K LL).2.1)

theorem level_clause_of_local_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h1 : Formalism.MainNotions.RamifiedCoefficientChains.adm1 D HW F Cm) (h6 : Formalism.MainNotions.RamifiedCoefficientChains.adm6 D HW F) (h11 : Formalism.MainNotions.RamifiedCoefficientChains.adm11 D)
    (hJ : Formalism.MainNotions.LiftingTheory.adm23 D HW F) : adm13 D HW F Cm :=
  level_clause_of_open_tool' D HW F Cm h6 fun l _ K LL hg _ => QToolOpen_of_adm D HW F Cm h1 h6 h11 hJ l K LL hg

theorem level_clause_of_admitted_statements (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    {CR CA CB CK : ℝ} (hA : Formalism.MainNotions.RamifiedCoefficientChains.admitted D HW F Cm CR CA CB CK) (hJ : Formalism.MainNotions.LiftingTheory.adm23 D HW F) :
    adm13 D HW F Cm :=
  level_clause_of_local_hypotheses D HW F Cm hA.1 hA.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.2.2.1 hJ

end Rows

end Formalism.MainNotions.CrystallineLiftingInputs.Tools
