import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RePosOfIsMultIP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PostOnMemGoodPart
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationPrincipalLevelEqCoreLevelOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCongruenceConjContainsCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalCongruenceLevelContainedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCongruenceInLevelCharacterOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurPairingInvariantUnderStandardGroupStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAdmissibleUnitaryMemSupIsotypicPartsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelVectorSumOfIsotypicPiecesStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.FinTypesRows

section Minf

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {n : ℕ}

theorem isMultMap_relevel {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} {T : MMap M} (h : IsMultMap θ M J χ T)
    (h' : ∀ v, ∀ k ∈ J', ∀ g, T v (g * k) = χ' k * T v g) : IsMultMap θ M J' χ' T :=
  { h with lev := h' }

theorem levN_anti (P : principalLevelFrame.RowPsi V n) {a b : ℕ} (hab : a ∣ b) : principalLevelFrame.levN P b ⊆ principalLevelFrame.levN P a := by
  obtain ⟨c, rfl⟩ := hab
  rintro _ ⟨κ, hκ, rfl⟩
  exact ⟨κ, Formalism.L2.NG.Cong.of_mul_left D.host.E n hκ, rfl⟩

theorem mult_levN_mono (P : principalLevelFrame.RowPsi V n) {a b : ℕ} (hab : a ∣ b) {T : MMap M}
    (hT : T ∈ Mult θ M (principalLevelFrame.levN P a) (fun _ => 1)) : T ∈ Mult θ M (principalLevelFrame.levN P b) (fun _ => 1) := by
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
  exact isMultMap_relevel hT fun v k hk g => hT.lev v k (levN_anti P hab hk) g

theorem mem_Minf_iff (P : principalLevelFrame.RowPsi V n) (T : MMap M) :
    T ∈ principalLevelFrame.Minf θ P M ↔ ∃ N : ℕ, 0 < N ∧ T ∈ Mult θ M (principalLevelFrame.levN P N) (fun _ => 1) := by
  unfold principalLevelFrame.Minf
  have hdir : Directed (· ≤ ·) (fun N : ℕ => Mult θ M (principalLevelFrame.levN P (N + 1)) (fun _ => 1)) := by
    intro a b
    refine ⟨(a + 1) * (b + 1) - 1, ?_, ?_⟩
    · intro T hT
      have e : (a + 1) * (b + 1) - 1 + 1 = (a + 1) * (b + 1) := Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos b))
      show T ∈ Mult θ M (principalLevelFrame.levN P ((a + 1) * (b + 1) - 1 + 1)) (fun _ => 1)
      rw [e]
      exact mult_levN_mono P (Dvd.intro _ rfl) hT
    · intro T hT
      have e : (a + 1) * (b + 1) - 1 + 1 = (a + 1) * (b + 1) := Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos b))
      show T ∈ Mult θ M (principalLevelFrame.levN P ((a + 1) * (b + 1) - 1 + 1)) (fun _ => 1)
      rw [e]
      exact mult_levN_mono P (Dvd.intro_left _ rfl) hT
  rw [Submodule.mem_iSup_of_directed _ hdir]
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N + 1, Nat.succ_pos N, hN⟩
  · rintro ⟨N, hN, hT⟩
    refine ⟨N - 1, ?_⟩
    rw [Nat.sub_add_cancel hN]
    exact hT

theorem mem_Minf_of (P : principalLevelFrame.RowPsi V n) {N : ℕ} (hN : 0 < N) {T : MMap M}
    (hT : T ∈ Mult θ M (principalLevelFrame.levN P N) (fun _ => 1)) : T ∈ principalLevelFrame.Minf θ P M :=
  (mem_Minf_iff P T).2 ⟨N, hN, hT⟩

theorem minf_smooth (P : principalLevelFrame.RowPsi V n) {T : MMap M} (hT : T ∈ principalLevelFrame.Minf θ P M) :
    ∃ N : ℕ, 0 < N ∧ ∀ κ, Formalism.L2.NG.Cong D.host.E n N κ → principalLevelFrame.actM P M κ T = T := by
  obtain ⟨N, hN, hT⟩ := (mem_Minf_iff P T).1 hT
  refine ⟨N, hN, fun κ hκ => ?_⟩
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT
  apply MultilinearMap.ext
  intro v
  funext g
  rw [principalLevelFrame.actM_apply, hT.lev v _ ⟨κ, hκ, rfl⟩ g, one_mul]

theorem mult_of_minf (P : principalLevelFrame.RowPsi V n) {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M}
    (hT : T ∈ principalLevelFrame.Minf θ P M) (hl : ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g) : T ∈ Mult θ M J χ := by
  obtain ⟨N, -, hT⟩ := (mem_Minf_iff P T).1 hT
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
  exact isMultMap_relevel hT hl

theorem minf_stable (P : principalLevelFrame.RowPsi V n) (hc : principalLevelFrame.CongConj D.host.E n) (h : Formalism.AUTREP.GAf D.host.E n)
    {T : MMap M} (hT : T ∈ principalLevelFrame.Minf θ P M) : principalLevelFrame.actM P M h T ∈ principalLevelFrame.Minf θ P M := by
  obtain ⟨N, hN, hT⟩ := (mem_Minf_iff P T).1 hT
  obtain ⟨N', hN', hN'c⟩ := hc h N hN
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT
  refine mem_Minf_of P hN' ?_
  rw [GlobalTheory.MultMem.mem_mult_iff]
  have := GlobalTheory.MultTranslate.isMultMap_rTr (J' := principalLevelFrame.levN P N') (χ' := fun _ => 1) (P.into h) (fun k hk => by
    obtain ⟨κ, hκ, rfl⟩ := hk
    refine ⟨⟨h⁻¹ * κ * h, hN'c κ hκ, by simp [map_mul, map_inv]⟩, rfl⟩) hT
  exact this

end Minf

end GlobalTheory.FinTypesRows

namespace GlobalTheory.FinTypesRows

section Forms

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {n : ℕ}

theorem exists_common (P : principalLevelFrame.RowPsi V n) {x y : MMap M} (hx : x ∈ principalLevelFrame.Minf θ P M) (hy : y ∈ principalLevelFrame.Minf θ P M) :
    ∃ N : ℕ, 0 < N ∧ x ∈ Mult θ M (principalLevelFrame.levN P N) (fun _ => 1) ∧ y ∈ Mult θ M (principalLevelFrame.levN P N) (fun _ => 1) := by
  obtain ⟨a, ha, hx⟩ := (mem_Minf_iff P x).1 hx
  obtain ⟨b, hb, hy⟩ := (mem_Minf_iff P y).1 hy
  exact ⟨a * b, Nat.mul_pos ha hb, mult_levN_mono P (Dvd.intro _ rfl) hx, mult_levN_mono P (Dvd.intro_left _ rfl) hy⟩

theorem exists_common3 (P : principalLevelFrame.RowPsi V n) {x y z : MMap M} (hx : x ∈ principalLevelFrame.Minf θ P M)
    (hy : y ∈ principalLevelFrame.Minf θ P M) (hz : z ∈ principalLevelFrame.Minf θ P M) :
    ∃ N : ℕ, 0 < N ∧ x ∈ Mult θ M (principalLevelFrame.levN P N) (fun _ => 1) ∧ y ∈ Mult θ M (principalLevelFrame.levN P N) (fun _ => 1) ∧
      z ∈ Mult θ M (principalLevelFrame.levN P N) (fun _ => 1) := by
  obtain ⟨a, ha, hx, hy⟩ := exists_common P hx hy
  obtain ⟨b, hb, hz⟩ := (mem_Minf_iff P z).1 hz
  exact ⟨a * b, Nat.mul_pos ha hb, mult_levN_mono P (Dvd.intro _ rfl) hx, mult_levN_mono P (Dvd.intro _ rfl) hy,
    mult_levN_mono P (Dvd.intro_left _ rfl) hz⟩

variable (μ : Measure (GA D V)) (𝓕 : Set (GA D V))

theorem minf_sesq (P : principalLevelFrame.RowPsi V n) (hS : SchurAll D) (hV : V.SigOK) (hθ : IsInfFam θ) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) :
    (∀ x ∈ principalLevelFrame.Minf θ P M, ∀ y ∈ principalLevelFrame.Minf θ P M, ∀ z ∈ principalLevelFrame.Minf θ P M, ∀ c : ℂ,
      ipM M μ 𝓕 x (y + c • z) = ipM M μ 𝓕 x y + c * ipM M μ 𝓕 x z) ∧
    (∀ x ∈ principalLevelFrame.Minf θ P M, ∀ y ∈ principalLevelFrame.Minf θ P M, ipM M μ 𝓕 x y = starRingEnd ℂ (ipM M μ 𝓕 y x)) ∧
    (∀ x ∈ principalLevelFrame.Minf θ P M, x ≠ 0 → 0 < (ipM M μ 𝓕 x x).re) := by
  have key := fun N : ℕ => GlobalTheory.SchurConst.ipM_posDef D θ V S M (principalLevelFrame.levN P N) (fun _ => 1) μ 𝓕 hθ hμ h𝓕
    (hS V hV S θ M _ _ μ 𝓕) (GlobalTheory.GardingVec.sm_ne_bot D V S M)
  refine ⟨fun x hx y hy z hz c => ?_, fun x hx y hy => ?_, fun x hx hx0 => ?_⟩
  · obtain ⟨N, -, hx, hy, hz⟩ := exists_common3 P hx hy hz
    exact ((key N).1 x hx y hy z hz c).1
  · obtain ⟨N, -, hx, hy⟩ := exists_common P hx hy
    exact ((key N).1 y hy x hx 0 (Submodule.zero_mem _) 0).2
  · obtain ⟨N, -, hx⟩ := (mem_Minf_iff P x).1 hx
    exact (key N).2 x hx hx0

theorem minf_adm (P : principalLevelFrame.RowPsi V n) (hH : HCAll D) (hV : V.SigOK) (hθ : IsInfFam θ)
    (hU : ∀ N : ℕ, 0 < N → ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ principalLevelFrame.levN P N)
    (N : ℕ) (hN : 0 < N) :
    FiniteDimensional ℂ ↥(Submodule.span ℂ {x | x ∈ principalLevelFrame.Minf θ P M ∧
      ∀ κ, Formalism.L2.NG.Cong D.host.E n N κ → principalLevelFrame.actM P M κ x = x}) := by
  have hfd : FiniteDimensional ℂ (Mult θ M (principalLevelFrame.levN P N) (fun _ => 1)) := by
    obtain ⟨U, hUo, hUk⟩ := hU N hN
    exact hH V hV S θ M _ _ hθ ⟨U, hUo, fun k hk hkf => ⟨hUk k hk hkf, rfl⟩⟩
  have hle : Submodule.span ℂ {x | x ∈ principalLevelFrame.Minf θ P M ∧
      ∀ κ, Formalism.L2.NG.Cong D.host.E n N κ → principalLevelFrame.actM P M κ x = x} ≤ Mult θ M (principalLevelFrame.levN P N) (fun _ => 1) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨hx, hfix⟩
    refine mult_of_minf P hx fun v k hk g => ?_
    obtain ⟨κ, hκ, rfl⟩ := hk
    have := congrFun (congrArg (fun T : MMap M => T v) (hfix κ hκ)) g
    rw [principalLevelFrame.actM_apply] at this
    rw [this, one_mul]
  exact Submodule.finiteDimensional_of_le hle

end Forms

section Isot

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A]

theorem isotIn_le {D : D7} (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A)
    (π : Formalism.L2.NG.FinTyp D.host.E n) : principalLevelFrame.isotIn (D := D) ρ C π ≤ C :=
  iSup₂_le fun _ h => h.2

theorem isotIn_stable {D : D7} (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A)
    (π : Formalism.L2.NG.FinTyp D.host.E n) (h : Formalism.AUTREP.GAf D.host.E n) {x : A}
    (hx : x ∈ principalLevelFrame.isotIn (D := D) ρ C π) : ρ h x ∈ principalLevelFrame.isotIn (D := D) ρ C π := by
  have : principalLevelFrame.isotIn (D := D) ρ C π ≤ (principalLevelFrame.isotIn (D := D) ρ C π).comap (ρ h) := by
    refine iSup₂_le fun Φ hΦ => ?_
    rintro _ ⟨f, rfl⟩
    show ρ h (Φ f) ∈ principalLevelFrame.isotIn (D := D) ρ C π
    rw [← hΦ.1 h f]
    exact (le_iSup₂ (f := fun (Φ : π.S →ₗ[ℂ] A) (_ : principalLevelFrame.IsEqvA ρ π Φ ∧ LinearMap.range Φ ≤ C) => LinearMap.range Φ) Φ hΦ)
      (LinearMap.mem_range_self Φ _)
  exact this hx

end Isot

end GlobalTheory.FinTypesRows

namespace GlobalTheory.FinTypesRows

theorem levN_open {D : D7} {V : HSp D} {n : ℕ} (P : principalLevelFrame.RowPsi V n) {hF : D.host.F = maximalRealSubfield D.host.E}
    (hP : StdFrame hF P) (N : ℕ) (hN : 0 < N) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ principalLevelFrame.levN P N := by
  obtain ⟨N', hN', h⟩ := GlobalTheory.T.principal_congruence_level_contained D V n P hF hP N hN
  exact ⟨GlobalTheory.HolDict.PrincLev.congGroup V N', GlobalTheory.HolDict.PrincLev.isOpen_congGroup V hN', fun k hk hkf => h k hkf hk⟩

theorem levOK_levS {D : D7} {V : HSp D} {n : ℕ} (P : principalLevelFrame.RowPsi V n) {hF : D.host.F = maximalRealSubfield D.host.E}
    (hP : StdFrame hF P) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    principalLevelFrame.LevOK P (levS V β L) (levChi V β L) := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.T.exists_lattice_congruence_in_level_character_one D V β L
  obtain ⟨N', hN', h'⟩ := GlobalTheory.T.exists_congruence_level_maps_into_lattice_congruence D V n P hF hP N hN
  exact ⟨N', hN', fun κ hκ => h _ (P.into κ) (h' κ hκ)⟩

end GlobalTheory.FinTypesRows

namespace GlobalTheory.FinTypesRows

theorem isotL_span_orth : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (P : principalLevelFrame.RowPsi V D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), Inputs D → V.SigOK → IsInfFam θ → StdFrame hF P → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → (∃ (s : Finset (GA D V)) (c : GA D V → ℂ), (∀ g ∈ s, g ∈ GfC V) ∧ e = ∑ g ∈ s, c g • principalLevelFrame.rtA g) → (⨆ π, principalLevelFrame.isotL θ P M (levS V β L) (levChi V β L) e π) = goodPart θ M (levS V β L) (levChi V β L) e ∧ ∀ π π', ¬ π.Iso π' → ∀ x ∈ principalLevelFrame.isotL θ P M (levS V β L) (levChi V β L) e π, ∀ y ∈ principalLevelFrame.isotL θ P M (levS V β L) (levChi V β L) e π', ipM M μ 𝓕 x y = 0 := by
  intro D V S θ M P hF β L e μ 𝓕 hI hV hθ hStd hμ h𝓕 he
  have hc : principalLevelFrame.CongConj D.host.E D.R.r := GlobalTheory.T.unitary_congruence_conj_contains_congruence D.host.E D.R.r
  obtain ⟨hsesq, hherm, hpos⟩ := minf_sesq (θ := θ) (M := M) μ 𝓕 P hI.schur hV hθ hμ h𝓕
  have hstab : ∀ h, ∀ x ∈ principalLevelFrame.Minf θ P M, principalLevelFrame.actM P M h x ∈ principalLevelFrame.Minf θ P M :=
    fun h x hx => minf_stable P hc h hx
  have hinv := GlobalTheory.T.schur_pairing_invariant_under_standard_group D V S θ M D.R.r P μ 𝓕 hI.schur hV hθ hμ h𝓕
  have hadm := minf_adm (M := M) P hI.hc hV hθ (levN_open P hStd)
  have hsm : ∀ x ∈ principalLevelFrame.Minf θ P M, ∃ N : ℕ, 0 < N ∧ ∀ κ, Formalism.L2.NG.Cong D.host.E D.R.r N κ → principalLevelFrame.actM P M κ x = x :=
    fun x hx => minf_smooth P hx
  have horth := GlobalTheory.IsotOrth.isotIn_orthogonal D D.R.r (MMap M) (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) (ipM M μ 𝓕)
    hsesq hherm hpos hstab hinv hadm
  refine ⟨le_antisymm (iSup_le fun π => inf_le_left) ?_, fun π π' hne x hx y hy => horth π π' hne x hx.2 y hy.2⟩
  intro T hT
  have hTm := (mem_goodPart θ M (levS V β L) (levChi V β L) e T).1 hT

  obtain ⟨N0, hN0, h0⟩ := levOK_levS P hStd β L
  have hTC : T ∈ principalLevelFrame.Minf θ P M := by
    refine mem_Minf_of P hN0 ?_
    have hl := principalLevelFrame.mult_lev hTm.1
    rw [GlobalTheory.MultMem.mem_mult_iff]
    rw [GlobalTheory.MultMem.mem_mult_iff] at hTm
    exact isMultMap_relevel hTm.1 fun v k hk g => by
      obtain ⟨κ, hκ, rfl⟩ := hk
      rw [hl v _ (h0 κ hκ).1 g, (h0 κ hκ).2]

  let O : Option (levS V β L) → MMap M →ₗ[ℂ] MMap M := fun i => match i with
    | none => postOn M e - LinearMap.id
    | some k => postOn M (principalLevelFrame.rtA k.1) - levChi V β L k.1 • LinearMap.id
  have hJf : ∀ k ∈ levS V β L, k ∈ GfC V := fun k hk => hk.1
  have hrt : ∀ π, ∀ k ∈ GfC V, ∀ x ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) π,
      postOn M (principalLevelFrame.rtA k) x ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) π := by
    intro π k hk x hx
    obtain ⟨h, rfl⟩ := P.onto k hk
    exact isotIn_stable _ _ π h hx
  obtain ⟨s, c, hs, rfl⟩ := he
  have hpres : ∀ i π, ∀ x ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) π,
      O i x ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) π := by
    intro i π x hx
    rcases i with _ | k
    · show postOn M (∑ g ∈ s, c g • principalLevelFrame.rtA g) x - x ∈ _
      refine Submodule.sub_mem _ ?_ hx
      have : postOn M (∑ g ∈ s, c g • principalLevelFrame.rtA g) x = ∑ g ∈ s, c g • postOn M (principalLevelFrame.rtA g) x := by
        apply MultilinearMap.ext
        intro v
        simp [postOn_apply, LinearMap.sum_apply]
      rw [this]
      exact Submodule.sum_mem _ fun g hg => Submodule.smul_mem _ _ (hrt π g (hs g hg) x hx)
    · show postOn M (principalLevelFrame.rtA k.1) x - levChi V β L k.1 • x ∈ _
      exact Submodule.sub_mem _ (hrt π k.1 (hJf k.1 k.2) x hx) (Submodule.smul_mem _ _ hx)
  have hTO : ∀ i, O i T = 0 := by
    intro i
    rcases i with _ | k
    · show postOn M (∑ g ∈ s, c g • principalLevelFrame.rtA g) T - T = 0
      rw [sub_eq_zero]
      apply MultilinearMap.ext
      intro v
      exact hTm.2 v
    · show postOn M (principalLevelFrame.rtA k.1) T - levChi V β L k.1 • T = 0
      rw [sub_eq_zero]
      apply MultilinearMap.ext
      intro v
      funext g
      exact principalLevelFrame.mult_lev hTm.1 v k.1 k.2 g
  have hspan := GlobalTheory.T.smooth_admissible_unitary_mem_sup_isotypic_parts D D.R.r (MMap M) (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) (ipM M μ 𝓕) hsesq hherm hpos hstab hinv
    hadm hsm T hTC
  have hdec := GlobalTheory.T.kernel_vector_sum_of_isotypic_pieces D D.R.r (MMap M) (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) (ipM M μ 𝓕) hsesq hherm hpos horth
    (Option (levS V β L)) O hpres T hspan hTO
  have hle : (⨆ π : Formalism.L2.NG.FinTyp D.host.E D.R.r,
      (principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) π ⊓ ⨅ i, LinearMap.ker (O i))) ≤
      ⨆ π, principalLevelFrame.isotL θ P M (levS V β L) (levChi V β L) (∑ g ∈ s, c g • principalLevelFrame.rtA g) π := by
    refine iSup_mono fun π => ?_
    rintro y ⟨hy, hyO⟩
    refine ⟨?_, hy⟩
    have hyO' : ∀ i, O i y = 0 := fun i => (Submodule.mem_iInf _).1 hyO i
    have hyC := isotIn_le _ _ π hy
    change y ∈ goodPart θ M (levS V β L) (levChi V β L) (∑ g ∈ s, c g • principalLevelFrame.rtA g)
    rw [mem_goodPart]
    refine ⟨mult_of_minf P hyC fun v k hk g => ?_, fun v => ?_⟩
    · have := congrFun (congrArg (fun T : MMap M => T v) (sub_eq_zero.1 (hyO' (some ⟨k, hk⟩)))) g
      exact this
    · have := congrArg (fun T : MMap M => T v) (sub_eq_zero.1 (hyO' none))
      exact this
  exact hle hdec

end GlobalTheory.FinTypesRows

end
