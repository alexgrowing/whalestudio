import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeGaloisTrivialModUniformizer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumpsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNOfMapMemSaturatedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAndDecompletion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneNotMemFilOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevLawsOfEvLaw
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.NygaardFrobeniusPower

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem map_smulA {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (a : LetA O n) (x : W.DD T) :
    W.map f (a • x) = a • W.map f x := by
  rw [← algebraMap_smul W.EE a x, LinearMap.map_smul, algebraMap_smul]

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

theorem φA_letE (i : ZMod n) : W.φA (letE (i - 1) : LetA O n) = letE i := by
  funext j
  simp only [LocWach.φA, letφ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply, letE,
    Pi.single_apply, sub_left_inj]
  split_ifs <;> simp

theorem sum_letE [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem isUnit_φA_pow (k : ℕ) (a : LetA O n) (ha : IsUnit (algebraMap (LetA O n) W.EE a)) :
    IsUnit (algebraMap (LetA O n) W.EE ((W.φA ^ k) a)) := by
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [pow_succ', AlgHom.mul_apply]
    have : algebraMap (LetA O n) W.EE (W.φA ((W.φA ^ k) a)) =
        W.φE (algebraMap (LetA O n) W.EE ((W.φA ^ k) a)) := (W.φE_ext _).symm
    rw [this]
    exact ih.map W.φE

theorem isUnit_X : IsUnit (algebraMap (LetA O n) W.EE W.X) :=
  isUnit_φA_pow W (W.s - 1) letπ W.EE_π

theorem Q_pow_φ_mem [NeZero n] (T : LocLat G Qp LL O) (M : ZMod n → ℕ)
    (hM : ∀ i, ∀ x ∈ W.Nl T (i - 1), W.Q ^ (M i) • W.φD T x ∈ W.N T)
    (x : W.DD T) (hx : x ∈ W.N T) : W.Q ^ (mx M) • W.φD T x ∈ W.N T := by
  have hx' : x = ∑ i : ZMod n, (letE i : LetA O n) • x := by
    rw [← Finset.sum_smul, sum_letE, one_smul]
  rw [hx', map_sum, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hle : M (i + 1) ≤ mx M := le_ciSup (Set.finite_range M).bddAbove (i + 1)
  have hmem : (letE i : LetA O n) • x ∈ W.Nl T (i + 1 - 1) := by
    rw [add_sub_cancel_right]
    exact ⟨x, hx, by simp⟩
  have h1 := hM (i + 1) _ hmem
  rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
  exact Submodule.smul_mem _ _ h1

theorem core [NeZero n] (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L)
    (M : ZMod n → ℕ)
    (hex : ∀ y, W.map π y = 0 → ∃ z, W.map ι z = y)
    (hsat : ∀ z : W.DD T, W.map ι z ∈ W.N Tp → z ∈ W.N T)
    (hφ : ∀ i, ∀ x ∈ W.Nl Tp (i - 1), W.Q ^ (M i) • W.φD Tp x ∈ W.N Tp)
    (hγ : ∀ x ∈ W.N Tp, W.γ Tp x - x ∈ (aN W) Tp W.X)
    (e : W.DD W.one) (he : W.φD W.one e = e) (hge : ∀ g, W.γD W.one g e = e)
    (x : W.DD Tp) (hx : x ∈ W.N Tp) (c : O) (hc : W.map π x = c • e) :
    (∃ y ∈ (invN W) T (W.Q ^ mx M), W.map ι y = W.φD Tp x - x) ∧
      (∃ z ∈ (aN W) T W.X, W.map ι z = W.γ Tp x - x) := by
  constructor
  · have h0 : W.map π (W.φD Tp x - x) = 0 := by
      rw [map_sub, W.map_φ, hc, (W.φD W.one).map_smul, he, sub_self]
    obtain ⟨y, hy⟩ := hex _ h0
    refine ⟨y, hsat _ ?_, hy⟩
    change W.map ι (W.Q ^ mx M • y) ∈ W.N Tp
    rw [map_smulA, hy, smul_sub]
    exact Submodule.sub_mem _ (Q_pow_φ_mem W Tp M hφ x hx) (Submodule.smul_mem _ _ hx)
  · obtain ⟨w, hw, hw'⟩ := hγ x hx
    change W.X • w = W.γ Tp x - x at hw'
    have hX0 : W.X • W.map π w = 0 := by
      rw [← map_smulA, hw', map_sub, LocWach.γ, W.map_γ, hc, (W.γD W.one W.gam).map_smul, hge,
        sub_self]
    have h0 : W.map π w = 0 := by
      obtain ⟨u, hu⟩ := isUnit_X W
      rw [← algebraMap_smul W.EE W.X, ← hu] at hX0
      have := congrArg (fun y => ((u⁻¹ : W.EEˣ) : W.EE) • y) hX0
      simpa [smul_smul] using this
    obtain ⟨z, hz⟩ := hex _ h0
    have hzN : z ∈ W.N T := hsat z (hz ▸ hw)
    refine ⟨W.X • z, ⟨z, hzN, rfl⟩, ?_⟩
    rw [map_smulA, hz]
    exact hw'

end Generic

set_option maxHeartbeats 1000000 in

theorem crystalline_extension_integral_cocycle_all_places : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), P8 D HW F := by
  intro D HW F Cm l _ K s LL h T M hh hT hjT Tp ι π hses hTp e heN hφe hγe x hx c hc
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hexact := (GlobalTheory.EtaleExact.DD_exact D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F)
    l K s LL h T Tp ((HW l).W K s LL h).one ι π hses).2.1
  have hsat := GlobalTheory.T.mem_wachN_of_map_mem_saturated D HW F l K s LL h T Tp ((HW l).W K s LL h).one ι π hT hTp
    (GlobalTheory.NL.one_crys (HW l) h) hses
  have hjs := GlobalTheory.NL.JumpsSES.jumps_ses_and_one D HW l K s LL h T Tp ((HW l).W K s LL h).one ι π hTp hses
  have hjTp : JumpsLet ((HW l).W K s LL h) Tp M hh := by
    intro τ i hτ a ha
    rcases (hjs.1 τ a).1 ha with h1 | h1
    · exact hjT τ i hτ a h1
    · rw [hjs.2 τ a h1]
      exact ⟨by simp, by simp⟩
  have h5 := (GlobalTheory.T.wachLattice_heights_from_hodgeJumps D HW F Cm l K s LL h Tp M hh hTp hjTp).1
  have h2 := (GlobalTheory.NL.WachLatticeTrivialModUniformizer.wachLattice_galois_trivial_mod_uniformizer D HW F Cm l K s LL h Tp hTp).2.2
  exact core _ T Tp ι π M (fun y hy => (hexact y).1 hy) hsat h5 h2 e hφe hγe x hx c hc

end GlobalTheory.NL.NygaardFrobeniusPower
