import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LatticeFinrank
import Formalism.SharpRestriction.LevelLetterCocycles.DdRFull

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules PowerSeries
open scoped TensorProduct

theorem inj_of_range {LL X : Type*} [Field LL] [AddCommGroup X] [Module LL X] {r : ℕ}
    (Phi : (Fin r → LL) →ₗ[LL] X) (I : Submodule LL X) (hI : LinearMap.range Phi = I)
    (hdim : finrank LL ↥I = r) : Function.Injective Phi := by
  have h1 := LinearMap.finrank_range_add_finrank_ker Phi
  rw [hI, hdim, Module.finrank_fin_fun] at h1
  have h0 : finrank LL ↥(LinearMap.ker Phi) = 0 := by omega
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.finrank_eq_zero.1 h0

theorem comap_finrank {LL X : Type*} [Field LL] [AddCommGroup X] [Module LL X] {r : ℕ}
    (Phi : (Fin r → LL) →ₗ[LL] X) (hinj : Function.Injective Phi) (S : Submodule LL X) :
    finrank LL ↥(S.comap Phi) = finrank LL ↥(LinearMap.range Phi ⊓ S) := by
  rw [← Submodule.map_comap_eq]
  exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq

section Count

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem count (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] {r : ℕ}
    (Phi : (Fin r → LL) →ₗ[LL] V ⊗[Qp] BdR) (hinj : Function.Injective Phi)
    (Oth : Submodule LL (V ⊗[Qp] BdR)) (hIO : Disjoint (LinearMap.range Phi) Oth)
    (hcomap : ∀ a : ℤ, finrank LL ↥((FildR PD ρ τ a ⊔ Oth).comap Phi) = finrank LL ↥(FildR PD ρ τ a))
    (hdR' : finrank LL ↥(DdRE PD ρ τ) = r) (FC : ℤ → Submodule LL (V ⊗[Qp] BdR))
    (hFC : ∀ a, FC a = FildR PD ρ τ a ⊔ Oth)
    (S η m : ℕ) (upτ : Bool) (bτ : ℕ)
    (hj : JumpsInV PD ρ τ (deep upτ bτ S ∪ Set.Icc (-(η : ℤ)) η)) (hηb : η < bτ)
    (hm : ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV PD ρ τ a ≤ m) :
    (upτ = true →
      (∀ i : ℤ, i < -((bτ : ℤ) + S) → ∀ d : Fin r → LL, Phi d ∈ FC (-i) → d = 0) ∧
      r ≤ finrank LL ↥((FC bτ).comap Phi) + m) ∧
    (upτ = false → finrank LL ↥((FC (-(bτ : ℤ) + 1)).comap Phi) ≤ m) := by
  classical
  have : ∀ a, FiniteDimensional LL ↥(FildR PD ρ τ a) :=
    fun a => Submodule.finiteDimensional_of_le (inf_le_left : FildR PD ρ τ a ≤ DdRE PD ρ τ)
  obtain ⟨hi, hhi⟩ := fr_fildR_hi PD ρ τ
  obtain ⟨lo, hlo⟩ := fr_fildR_lo PD ρ τ
  have hmult0 : ∀ a, a ∉ deep upτ bτ S → a ∉ Set.Icc (-(η : ℤ)) η → multV PD ρ τ a = 0 :=
    fun a h1 h2 => fr_multV_of_not_jump PD ρ τ a (fun hJ => (hj a hJ).elim h1 h2)
  refine ⟨fun hup => ⟨?_, ?_⟩, fun hdn => ?_⟩
  · intro i hi' d hd
    rw [hFC] at hd
    have htop : FildR PD ρ τ ((bτ : ℤ) + S + 1) = ⊥ := by
      have hsum := fr_sum_multV PD ρ τ ((bτ : ℤ) + S + 1) (max hi ((bτ : ℤ) + S + 1)) (le_max_right _ _)
      have h0 : ∑ a ∈ Finset.Ico ((bτ : ℤ) + S + 1) (max hi ((bτ : ℤ) + S + 1)), multV PD ρ τ a = 0 :=
        Finset.sum_eq_zero fun a ha => by
          rw [Finset.mem_Ico] at ha
          refine hmult0 a (fun h => ?_) (fun h => ?_)
          · rw [hup] at h
            simp only [deep, if_true, Set.mem_Icc] at h
            omega
          · rw [Set.mem_Icc] at h
            omega
      rw [hhi _ (le_max_left _ _), finrank_bot, h0] at hsum
      exact Submodule.finrank_eq_zero.1 (by omega)
    have h1 : FildR PD ρ τ (-i) ⊔ Oth ≤ Oth :=
      sup_le (le_trans (fr_fildR_anti PD ρ τ (by omega)) (htop ▸ bot_le)) le_rfl
    have h0 := Submodule.disjoint_def.1 hIO _ ⟨d, rfl⟩ (h1 hd)
    exact hinj (by rw [h0, map_zero])
  · rw [hFC, hcomap]
    have hsum := fr_sum_multV PD ρ τ (min lo (-(η : ℤ))) bτ (by omega)
    have hsub : ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV PD ρ τ a =
        ∑ a ∈ Finset.Ico (min lo (-(η : ℤ))) bτ, multV PD ρ τ a := by
      refine Finset.sum_subset (fun a ha => ?_) (fun a ha hna => hmult0 a (fun h => ?_) (fun h => ?_))
      · rw [Finset.mem_Icc] at ha
        rw [Finset.mem_Ico]
        omega
      · rw [hup] at h
        simp only [deep, if_true, Set.mem_Icc] at h
        rw [Finset.mem_Ico] at ha
        omega
      · exact hna (by rw [Finset.mem_Icc]; exact h)
    rw [hlo _ (min_le_left _ _), hdR'] at hsum
    omega
  · rw [hFC, hcomap]
    have hsum := fr_sum_multV PD ρ τ (-(bτ : ℤ) + 1) (max hi ((η : ℤ) + 1)) (by omega)
    have hsub : ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV PD ρ τ a =
        ∑ a ∈ Finset.Ico (-(bτ : ℤ) + 1) (max hi ((η : ℤ) + 1)), multV PD ρ τ a := by
      refine Finset.sum_subset (fun a ha => ?_) (fun a ha hna => hmult0 a (fun h => ?_) (fun h => ?_))
      · rw [Finset.mem_Icc] at ha
        rw [Finset.mem_Ico]
        omega
      · rw [hdn] at h
        simp only [deep, Bool.false_eq_true, if_false, Set.mem_Icc] at h
        rw [Finset.mem_Ico] at ha
        omega
      · exact hna (by rw [Finset.mem_Icc]; exact h)
    rw [hhi _ (le_max_left _ _), finrank_bot] at hsum
    omega

end Count

theorem pt_root (D : D7) (HW : HWOf D.loc) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) : ζ ^ ((D.loc l).PD K).p = 1 ∧ ζ ≠ 1 := by
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  obtain ⟨τs, hIs, -⟩ := hpt
  have hz1 : (D.loc l).ζQ 1 ^ l = 1 := by
    rw [(D.loc l).ζQ_succ 0, (D.loc l).ζQ_zero]
  have hmem : (D.loc l).ζQ 1 ∈ Ks K 1 :=
    le_sup_right (a := K0 K) (IntermediateField.subset_adjoin _ _ (by rw [pow_one]; exact hz1))
  have hy := hIs.2 ⟨_, hmem⟩ rfl
  have hyl : (⟨_, hmem⟩ : ↥(Ks K 1)) ^ l = 1 := Subtype.ext (by simpa using hz1)
  refine ⟨?_, ?_⟩
  · rw [hp, ← hy, ← map_pow, hyl, map_one]
  · intro h1
    rw [← hy] at h1
    have : (⟨_, hmem⟩ : ↥(Ks K 1)) = 1 := τs.toRingHom.injective (by rw [map_one]; exact h1)
    exact (D.loc l).ζQ_one (congrArg Subtype.val this)

theorem phi_zero (D : D7) (HW : HWOf D.loc) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1)
    (hζ : ζ ^ ((D.loc l).PD K).p = 1 ∧ ζ ≠ 1) : PowerSeries.constantCoeff (((HW l).W K 1 LL hG).lev c ζ (((HW l).W K 1 LL hG).φA π')) = 0 := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  obtain ⟨-, -, -, -, ⟨w2, hw2⟩, ⟨w3, hw3⟩, -, -⟩ := hp9
  have hQ : ((HW l).W K 1 LL hG).Q = (w2 : LetA _ _) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' := by rw [ModelFPf.Q_eq_q ((HW l).W K 1 LL hG) hs]; exact hw2
  have hE0 := ModelFPf.levE_zero ((HW l).W K 1 LL hG) (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') c hs (Units.inv_mul w2) hQ ζ hζ.1 hζ.2
  have hs1 : 1 ≤ sK l K := by
    have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
    have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
    have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, zero_dvd_iff] at hd
      omega
    exact Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  rw [hw3, map_mul, map_mul, map_pow, map_mul, map_mul, map_pow, hE0, zero_pow (by omega), mul_zero]

set_option maxHeartbeats 1000000 in
theorem range_eq (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) (hdR : DdRFull D) (hDi : DiRank D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ)
    (r : ℕ) (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) (rep : Fin r → ((HW l).W K 1 LL hG).DD T)
    (hrep : ∀ k, rep k ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)) (hbrep : ∀ k, bL k = mkL ((HW l).W K 1 LL hG) T π' c (rep k) (hrep k))
:
    LinearMap.range (UniversalLiftFrames.Phi ((HW l).W K 1 LL hG) T c ζ rep) = (Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) := by
  classical
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 ((HW l).W K 1 LL hG) (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) T := (hA l K 1 LL hG).2.2.2.1 T hT
  have hζ := pt_root D HW K LL hG c τ ζ hpt
  obtain ⟨hc0, hc1⟩ := ModelFPf.levQ_pt ((HW l).W K 1 LL hG) hs c ζ hζ.1 hζ.2
  have hφπ := phi_zero D HW hl K LL hG π' E hp9 c ζ hζ
  obtain ⟨-, ⟨-, -, -, ⟨r0, b, hbΔ, hbu, -⟩, -⟩, -⟩ :=
    (hA l K 1 LL hG).2.2.2.2.2.2.2.2.1 T hT hs (by rw [hp]; exact hl)
  have hrN : ∀ k, rep k ∈ ((HW l).W K 1 LL hG).N T := fun k => ((mem_NcS ((HW l).W K 1 LL hG) T _ _).1 (hrep k)).1
  refine le_antisymm ?_ (span_le_range ((HW l).W K 1 LL hG) T c ζ hp4 hpt hc0 hc1 π' hφπ b hbΔ hbu bL rep hrep hbrep)
  rintro _ ⟨d, rfl⟩
  rw [UniversalLiftFrames.Phi_apply]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (ModelFPf.valAt_mem ((HW l).W K 1 LL hG) T c hp4 hpt (hrN k))

set_option maxHeartbeats 1000000 in
theorem setup_fd (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) (hdR : DdRFull D) (hDi : DiRank D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ)
    (r : ℕ) (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) (rep : Fin r → ((HW l).W K 1 LL hG).DD T)
    (hrep : ∀ k, rep k ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)) (hbrep : ∀ k, bL k = mkL ((HW l).W K 1 LL hG) T π' c (rep k) (hrep k))
    (hrpos : 0 < r) :
    FiniteDimensional ↥LL.1 ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) ∧ FiniteDimensional ↥LL.1 ↥(DdRE ((D.loc l).PD K) T.ρ τ) ∧
      finrank ↥LL.1 ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) = r ∧ finrank ↥LL.1 ↥(DdRE ((D.loc l).PD K) T.ρ τ) = r := by
  have hr : r = finrank ↥LL.1 T.V := r_eq D HW F Cm hA hl K LL hG π' E hp9 T hT c r bL
  have hDiR := hDi l K LL hG T hT c
  have hdRR := hdR l K LL ⟨1, hG⟩ T hT τ
  exact ⟨Module.finite_of_finrank_pos (by omega), Module.finite_of_finrank_pos (by omega), by omega,
    by omega⟩

set_option maxHeartbeats 1000000 in
theorem setup_inj (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) (hdR : DdRFull D) (hDi : DiRank D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ)
    (r : ℕ) (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) (rep : Fin r → ((HW l).W K 1 LL hG).DD T)
    (hrep : ∀ k, rep k ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)) (hbrep : ∀ k, bL k = mkL ((HW l).W K 1 LL hG) T π' c (rep k) (hrep k))
    (hrpos : 0 < r) : Function.Injective (UniversalLiftFrames.Phi ((HW l).W K 1 LL hG) T c ζ rep) := by
  obtain ⟨-, -, hI, -⟩ := setup_fd D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T hT c τ ζ hpt r bL rep hrep hbrep hrpos
  exact inj_of_range _ _ (range_eq D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T hT c τ ζ hpt r bL rep hrep hbrep) hI

set_option maxHeartbeats 1000000 in
theorem setup_match (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) (hdR : DdRFull D) (hDi : DiRank D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ)
    (r : ℕ) (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) (rep : Fin r → ((HW l).W K 1 LL hG).DD T)
    (hrep : ∀ k, rep k ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)) (hbrep : ∀ k, bL k = mkL ((HW l).W K 1 LL hG) T π' c (rep k) (hrep k))
    (hrpos : 0 < r) :
    Disjoint (Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) (⨆ (τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (_ : τ' ≠ τ), DdRE ((D.loc l).PD K) T.ρ τ') ∧ ∀ a : ℤ, finrank ↥LL.1 ↥((Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) ⊓ (FildR ((D.loc l).PD K) T.ρ τ a ⊔ (⨆ (τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (_ : τ' ≠ τ), DdRE ((D.loc l).PD K) T.ρ τ'))) = finrank ↥LL.1 ↥(FildR ((D.loc l).PD K) T.ρ τ a) := by
  obtain ⟨h1, h2, hI, hD⟩ := setup_fd D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T hT c τ ζ hpt r bL rep hrep hbrep hrpos
  have hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 ((HW l).W K 1 LL hG) (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) T := (hA l K 1 LL hG).2.2.2.1 T hT
  have : FiniteDimensional ℚ_[l] ↥K.1 := ((D.loc l).PD K).finK
  have hDO := oth_disj ((D.loc l).PD K) T.ρ τ
  have hDI := dR_le ((HW l).W K 1 LL hG) T c hp4 hpt
  obtain ⟨hIO, hFil⟩ := match_fil _ _ _ hDO (by rw [hI, hD]) hDI
  exact ⟨hIO, fun a => hFil _ inf_le_left⟩

theorem comap_count {LL X : Type*} [Field LL] [AddCommGroup X] [Module LL X] {r : ℕ}
    (Phi : (Fin r → LL) →ₗ[LL] X) (hinj : Function.Injective Phi) (I : Submodule LL X)
    (hre : LinearMap.range Phi = I) (S : Submodule LL X) {k : ℕ} (h : finrank LL ↥(I ⊓ S) = k) :
    finrank LL ↥(S.comap Phi) = k := by
  rw [comap_finrank Phi hinj, hre]
  exact h

theorem jumps_sub {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (S η : ℕ) (bτ : ℕ)
    (hj : JumpsInV PD ρ τ (deep false bτ S ∪ Set.Icc (-(η : ℤ)) η)) (hηb : η < bτ) :
    JumpsInV PD ρ τ (Set.Icc (-((bτ + S : ℕ) : ℤ)) ((bτ + S : ℕ) : ℤ)) := by
  intro a hJ
  rcases hj a hJ with h | h
  · simp only [deep, Bool.false_eq_true, if_false, Set.mem_Icc] at h
    rw [Set.mem_Icc]
    push_cast
    omega
  · rw [Set.mem_Icc] at h ⊢
    push_cast
    omega

set_option maxHeartbeats 1000000 in
theorem down_d (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) (hdR : DdRFull D) (hDi : DiRank D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ)
    (r : ℕ) (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) (rep : Fin r → ((HW l).W K 1 LL hG).DD T)
    (hrep : ∀ k, rep k ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)) (hbrep : ∀ k, bL k = mkL ((HW l).W K 1 LL hG) T π' c (rep k) (hrep k))
    (S bτ : ℕ)
    (hjm : JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-((bτ + S : ℕ) : ℤ)) ((bτ + S : ℕ) : ℤ))) (d : Fin r → ↥LL.1) :
    (UniversalLiftFrames.Phi ((HW l).W K 1 LL hG) T c ζ rep) d ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := ((D.loc l).PD K)) T τ (-((bτ : ℤ) + S)) := by
  have hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 ((HW l).W K 1 LL hG) (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) T := (hA l K 1 LL hG).2.2.2.1 T hT
  have hre := range_eq D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T hT c τ ζ hpt r bL rep hrep hbrep
  have hmem : (UniversalLiftFrames.Phi ((HW l).W K 1 LL hG) T c ζ rep) d ∈ (Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) := hre ▸ LinearMap.mem_range_self _ d
  have := ModelFPf.ιDi_le_top ((HW l).W K 1 LL hG) T (bτ + S) c hp4 hpt hjm hmem
  convert this using 2
  push_cast
  ring

set_option maxHeartbeats 1000000 in
theorem universal_filtration_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) (hdR : DdRFull D) (hDi : DiRank D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ)
    (r : ℕ) (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) (rep : Fin r → ((HW l).W K 1 LL hG).DD T)
    (hrep : ∀ k, rep k ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)) (hbrep : ∀ k, bL k = mkL ((HW l).W K 1 LL hG) T π' c (rep k) (hrep k))
    (S η m : ℕ) (upτ : Bool) (bτ : ℕ)
    (hj : JumpsInV ((D.loc l).PD K) T.ρ τ (deep upτ bτ S ∪ Set.Icc (-(η : ℤ)) η)) (hηb : η < bτ)
    (hm : ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV ((D.loc l).PD K) T.ρ τ a ≤ m) :
    (upτ = true →
      (∀ i : ℤ, i < -((bτ : ℤ) + S) → ∀ d : Fin r → ↥LL.1,
        UniversalLiftFrames.Phi ((HW l).W K 1 LL hG) T c ζ rep d ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ (-i) → d = 0) ∧
      r ≤ finrank ↥LL.1 ((Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ bτ).comap (UniversalLiftFrames.Phi ((HW l).W K 1 LL hG) T c ζ rep)) + m) ∧
    (upτ = false →
      finrank ↥LL.1 ((Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ (-(bτ : ℤ) + 1)).comap
        (UniversalLiftFrames.Phi ((HW l).W K 1 LL hG) T c ζ rep)) ≤ m ∧
      ∀ d : Fin r → ↥LL.1,
        UniversalLiftFrames.Phi ((HW l).W K 1 LL hG) T c ζ rep d ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ (-((bτ : ℤ) + S))) := by
  classical
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0
    refine ⟨fun _ => ⟨fun i _ d _ => funext fun k => k.elim0, by omega⟩, fun _ => ⟨?_, fun d => ?_⟩⟩
    · exact (Submodule.finrank_le _).trans (by simp)
    · rw [show d = 0 from funext fun k => k.elim0, map_zero]
      exact Submodule.zero_mem _
  obtain ⟨-, hfd, -, hD⟩ := setup_fd D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T hT c τ ζ hpt r bL rep hrep hbrep hrpos
  have hinj := setup_inj D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T hT c τ ζ hpt r bL rep hrep hbrep hrpos
  obtain ⟨hIO, hFil⟩ := setup_match D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T hT c τ ζ hpt r bL rep hrep hbrep hrpos
  have hre := range_eq D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T hT c τ ζ hpt r bL rep hrep hbrep
  obtain ⟨cu, cd⟩ := count ((D.loc l).PD K) T.ρ τ (UniversalLiftFrames.Phi ((HW l).W K 1 LL hG) T c ζ rep) hinj (⨆ (τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (_ : τ' ≠ τ), DdRE ((D.loc l).PD K) T.ρ τ') (hre ▸ hIO)
    (fun a => comap_count (UniversalLiftFrames.Phi ((HW l).W K 1 LL hG) T c ζ rep) hinj (Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) hre _ (hFil a)) hD (Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := ((D.loc l).PD K)) T τ)
    (fun a => rfl) S η m upτ bτ hj hηb hm
  refine ⟨cu, fun hdn => ⟨cd hdn, ?_⟩⟩
  subst hdn
  exact down_d D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T hT c τ ζ hpt r bL rep hrep hbrep S bτ
    (jumps_sub ((D.loc l).PD K) T.ρ τ S η bτ hj hηb)

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
