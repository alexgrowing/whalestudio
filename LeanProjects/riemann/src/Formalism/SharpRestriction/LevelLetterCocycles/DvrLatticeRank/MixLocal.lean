import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.TmulMkLMemInvLOfValAtMemFilC

noncomputable section

namespace Formalism.MainNotions.N.Ln34.LevelExpansions

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.N.Ln34.DescentValuation TensorProduct
open Formalism.MainNotions.ElementDenominator PowerSeries

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem letE_inv (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) (hE : Eπ ∈ W.AΔ) (z : LcQ W T π' c) :
    algebraMap (LetA O n) W.EE (letE c) ⊗ₜ z ∈ InvL W T Pt π' Eπ h' c ⊤ := by
  refine Submodule.mem_inf.2 ⟨tmul_mem_LamLA W T π' Eπ h' c (a := letE c * Eπ ^ h')
    (W.AΔ.mul_mem (letE_mem W c) (W.AΔ.pow_mem hE _))
    (by rw [← mul_assoc, CrystallineExponents.letE_mul_self]) (by rw [← map_mul, mul_comm]) z, ?_⟩
  rw [Submodule.mem_comap, LinearMap.sub_apply, ModelFPf.γLA_tmul,
    show W.γE W.gamK (algebraMap (LetA O n) W.EE (letE c)) =
      algebraMap (LetA O n) W.EE (W.γA W.gamK (letE c)) from W.γE_ext _ _, Formalism.MainNotions.LiftingTheory.wmap_γA_letE,
    LinearMap.id_apply, sub_self]
  exact Submodule.zero_mem _

theorem mix_local [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] [Fact PD.p.Prime]
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O}
    {h' M σ S η ρ yc : ℕ} {c : ZMod n} {up : (K →ₐ[Qp] LL) → Bool} {b : (K →ₐ[Qp] LL) → ℕ}
    {α : FrA W π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' M c} {β : FrB W π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' M c}
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 2 s' π' E) (hs : 2 * s' = PD.p - 1) (hs1 : 1 ≤ s')
    (hprim : ∀ τ ζ, Pt c ζ τ → IsPrimitiveRoot ζ PD.p)
    (hzO : ∀ ζ : LL, IsPrimitiveRoot ζ PD.p → ∃ z : O, algebraMap O LL z = ζ)
    (hΓ : ∀ τ ζ, Pt c ζ τ → ∃ u : LL, u ≠ 0 ∧
      ∀ a, W.lev c ζ (W.γA W.gamK a) = rescale u (W.lev c ζ a))
    (hPt : ∀ τ ζ, Pt c ζ τ → Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c)
    (hcard : ∀ τ τ' τ'', Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c → Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ' c →
      Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ'' c → τ ≠ τ' → τ'' = τ ∨ τ'' = τ')
    (hun : ∀ m : ℕ, ¬ PD.p ∣ m → IsUnit (m : O))
    (hc1 : IsCrys PD T₁.ρ) (hc2 : IsCrys PD T₂.ρ)
    (hd1 : ∀ τ, JumpsInV PD T₁.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η))
    (hd2 : ∀ τ, JumpsInV PD T₂.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η))
    (hηb : ∀ τ, η < b τ) (hbS : ∀ τ, b τ + S ≤ h') (hh : 1 ≤ h')
    (hfr : IsFrame W Pt π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' M σ c α β)
    (hMF1 : ModelF W T₁ Pt π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' M c α β)
    (hMF2 : ModelF W T₂ Pt π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' M c α β) (hM : 1 ≤ M)
    (V₁ : ValH W T₁ Pt π' c) (V₂ : ValH W T₂ Pt π' c) (hW : WKill W F ρ)
    (hNL : NinLam W T₁ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h') (hG1 : GamPi W T₁ π') (hG2 : GamPi W T₂ π')
    (hyc : ∀ b B : ℕ, b ≤ h' → b ≤ B + 2 * η → B ≤ b →
      b - B + 1 + 2 * padicValNat PD.p (b.choose (B - 1)) ≤ 2 * yc) :
    ThirdPropositionSlot W F Pt π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' M S up b c (ρ + max (2 * σ) yc) α := by
  intro f hf x hx hFil h1 y hy hα
  set Eπ := Formalism.MainNotions.DeltaInvariantLattices.Eat E π' with hEπ
  have hj1 := fun τ => u3downPf_jumps T₁ τ (up τ) (b τ) S η h' (hd1 τ) (hηb τ) (hbS τ)
  have hj2 := fun τ => u3downPf_jumps T₂ τ (up τ) (b τ) S η h' (hd2 τ) (hηb τ) (hbS τ)
  obtain ⟨w, hw⟩ := hp9.2.2.1
  obtain ⟨w', hw'⟩ := hp9.2.2.2.2.1
  have hπΔ : π' ∈ W.AΔ := hp9.1
  have hEΔ : Eπ ∈ W.AΔ := Eat_mem W hπΔ E
  have hπu : IsUnit (algebraMap (LetA O n) W.EE π') := by
    rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (W.EE_π.pow _)
  have hEu : IsUnit (algebraMap (LetA O n) W.EE Eπ) := by
    have hq := Formalism.MainNotions.LiftingTheory.liftb_q_unit W
    rw [hw', map_mul] at hq
    exact isUnit_of_mul_isUnit_right hq
  have hE := fun τ ζ (hpt : Pt c ζ τ) => u3downPf_lev_E W c ζ (hprim τ ζ hpt) Eπ w' hw'
  have hp0 : (PD.p : O) ≠ 0 := by
    intro h
    have h2 : (PD.p : LL) = 0 := by rw [← map_natCast (algebraMap O LL), h, map_zero]
    have := W.v_l
    rw [h2, AddValuation.map_zero] at this
    exact WithTop.top_ne_coe this
  obtain ⟨g, hgU, hgD, hgI⟩ := tmul_mkL_mem_InvL_of_valAt_mem_filC W Pt π' Eπ h' S up b c hπu hEu
    (fun τ ζ hpt => u3downPf_cc_π' W c ζ (hprim τ ζ hpt) π' _ w hw) hE hΓ f hf
  have low : ∀ (T : LocLat G Qp LL O), ValH W T Pt π' c →
      (∀ τ, JumpsInV PD T.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) →
      ∀ τ ζ, Pt c ζ τ → ∀ z ∈ NcS W T (c - 1), ∀ a : ℤ,
      (if up τ then a ≤ -(η : ℤ) else a ≤ -((b τ : ℤ) + S)) →
      valAt W T c ζ z ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a := by
    intro T V hd τ ζ hpt z hz a ha
    obtain ⟨k, hk⟩ := V.fil τ ζ hpt z hz
    refine u3downPf_filC_low T τ a (fun i hi => ?_) le_rfl hk
    have h := hd τ i hi
    have := hηb τ
    unfold deep at h
    split_ifs at h ha <;> simp only [Set.mem_union, Set.mem_Icc] at h <;> omega
  have hC : ∀ (T : LocLat G Qp LL O), ValH W T Pt π' c →
      (∀ τ, JumpsInV PD T.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) →
      ∀ z (hz : z ∈ NcS W T (c - 1)), (∀ τ ζ, Pt c ζ τ → up τ = true →
        valAt W T c ζ z ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (b τ)) →
      f ⊗ₜ mkL W T π' c z hz ∈ InvL W T Pt π' Eπ h' c ⊤ := by
    intro T V hd z hz hU
    refine hgI T z hz fun τ ζ hpt => ?_
    have := hbS τ
    cases hu : up τ
    · exact ⟨_, hgD τ ζ hpt hu, low T V hd τ ζ hpt z hz _ (by simp only [hu]; push_cast; omega)⟩
    · refine ⟨_, hgU τ ζ hpt hu, ?_⟩
      rw [show (h' : ℤ) - ((h' - b τ : ℕ) : ℤ) = b τ by omega]
      exact hU τ ζ hpt hu
  have hxU : ∀ τ ζ, Pt c ζ τ → up τ = true →
      valAt W T₂ c ζ x ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T₂ τ (b τ) :=
    fun τ ζ hpt hu => hFil τ (hPt τ ζ hpt) hu ζ hpt
  have hI2 := hC T₂ V₂ hd2 x hx hxU
  have hyI : y ∈ InvS W T₂ π' Eπ h' 1 c := hMF2.2.2.2.1 _ h1 y hy hα hI2
  have hroot : ∀ τ ζ, Pt c ζ τ → ∃ r : O, constantCoeff (W.lev c ζ π') = algebraMap O LL r ∧
      (PD.p : O) ∣ r ^ 2 := by
    intro τ ζ hpt
    obtain ⟨z, hz⟩ := hzO ζ (hprim τ ζ hpt)
    exact root W hinj hp9 hs c (hprim τ ζ hpt) hz
  obtain ⟨x₁, hx₁, hFx₁⟩ := hW (c - 1) x hx
  have hdiff : W.map F x₁ - ((PD.p : ℕ) : O) ^ ρ • x ∈ PiNS W T₂ π' 1 := by
    rw [hFx₁, sub_self]; exact Submodule.zero_mem _
  obtain ⟨a, ha, hea, hΛ, hup, hdn, -⟩ := hf
  by_cases hA : ∃ τ ζ, Pt c ζ τ ∧ up τ = false
  swap
  · refine lifts_mono W F (Nat.le_add_right _ _) (u3upPf_lift W F Pt π' Eπ h' M ρ c _ _ hMF2 hM hW hNL
      hG1 hG2 _ h1 (memNL0 W T₂ Pt π' Eπ h' c ha hea hΛ x hx fun τ ζ hpt => ?_) y hy hα)
    have hu : up τ = true := by
      by_contra hu
      exact hA ⟨τ, ζ, hpt, by simpa using hu⟩
    have := hbS τ
    refine ⟨h' - b τ, fun i hi => hup τ ζ hpt hu i (by omega), ?_⟩
    rw [show (h' : ℤ) - ((h' - b τ : ℕ) : ℤ) = b τ by omega]
    exact hxU τ ζ hpt hu
  by_cases hB : ∀ τ ζ, Pt c ζ τ → ∃ τ' ζ', Pt c ζ' τ' ∧ up τ' = false ∧
      constantCoeff (W.lev c ζ' π') = constantCoeff (W.lev c ζ π')
  · refine lifts_mono W F (Nat.le_add_right _ _) (core W F hfr hc1 hc2 hj1 hj2 hMF1 hMF2 hM f x hx x₁ hx₁
      ρ hdiff (hgI T₁ x₁ hx₁ fun τ ζ hpt => ?_) hI2 h1 y hy hα)
    cases hu : up τ
    · exact ⟨_, hgD τ ζ hpt hu, low T₁ V₁ hd1 τ ζ hpt x₁ hx₁ _ (by simp only [hu]; push_cast; omega)⟩
    · obtain ⟨τ', ζ', hpt', hu', hcc⟩ := hB τ ζ hpt
      obtain ⟨r, hr, hpr⟩ := hroot τ ζ hpt
      obtain ⟨u, hyu, -⟩ := simple W hinj hp9 c (hprim τ ζ hpt) hr
      obtain ⟨u', hyu', huu'⟩ := simple W hinj hp9 c (hprim τ' ζ' hpt') (hcc.trans hr)
      have ht := (dv W hp9 hs1 c hpr).transfer hyu' huu' hyu (h' + b τ' + S) g g 0
        (fun i hi => by rw [zero_mul]; exact hgD τ' ζ' hpt' hu' i hi)
      have := hηb τ'
      refine ⟨h' + b τ' + S, fun i hi => ?_, low T₁ V₁ hd1 τ ζ hpt x₁ hx₁ _
        (by simp only [hu]; push_cast; omega)⟩
      have h2 := ht i hi
      rwa [zero_mul] at h2
  push Not at hB
  obtain ⟨τU, ζU, hptU, hne⟩ := hB
  obtain ⟨τD, ζD, hptD, huD⟩ := hA
  have huU : up τU = true := by
    by_contra hu
    exact hne τU ζU hptU (by simpa using hu) rfl
  obtain ⟨rU, hrU, hpU⟩ := hroot τU ζU hptU
  obtain ⟨rD, hrD, hpD⟩ := hroot τD ζD hptD
  have hrne : rU ≠ rD := fun h => hne τD ζD hptD huD (by rw [hrD, hrU, h])
  obtain ⟨zU, hzU⟩ := hzO ζU (hprim τU ζU hptU)
  obtain ⟨a₂, ha₂, hfac, hδ⟩ := fact2 W hinj hp9 hs hs1 c (hprim τU ζU hptU) (hprim τD ζD hptD) hzU
    hrU hpU hrD hpD hrne hp0
  have hτne : τU ≠ τD := fun h => by rw [h, huD] at huU; exact Bool.false_ne_true huU
  have hτU : ∀ τ ζ, Pt c ζ τ → up τ = true → τ = τU := fun τ ζ hpt hu =>
    (hcard τU τD τ (hPt _ _ hptU) (hPt _ _ hptD) (hPt _ _ hpt) hτne).resolve_right fun h => by
      rw [h, huD] at hu; exact Bool.false_ne_true hu
  have hτD : ∀ τ ζ, Pt c ζ τ → up τ = false → τ = τD := fun τ ζ hpt hu =>
    (hcard τU τD τ (hPt _ _ hptU) (hPt _ _ hptD) (hPt _ _ hpt) hτne).resolve_left fun h => by
      rw [h, huU] at hu; exact Bool.false_ne_true hu.symm
  have hrr : ∀ τ ζ, Pt c ζ τ → constantCoeff (W.lev c ζ π') = algebraMap O LL rU ∨
      constantCoeff (W.lev c ζ π') = algebraMap O LL rD := by
    intro τ ζ hpt
    obtain ⟨e₁, he₁, -⟩ := hE τ ζ hpt
    have h0 := congrArg constantCoeff ((hfac ζ).symm.trans he₁)
    simp only [yR, map_mul, map_sub, constantCoeff_C, constantCoeff_X, zero_mul, mul_eq_zero,
      sub_eq_zero] at h0
    rcases h0 with (h0 | h0) | h0
    · exact absurd h0 (ha₂.map (algebraMap O LL)).ne_zero
    · exact Or.inl h0
    · exact Or.inr h0
  have hDr : ∀ τ ζ, Pt c ζ τ → up τ = false → constantCoeff (W.lev c ζ π') = algebraMap O LL rD :=
    fun τ ζ hpt hu => (hrr τ ζ hpt).resolve_left fun h => hne τ ζ hpt hu (h.trans hrU.symm)
  obtain ⟨uU, hyU, huU'⟩ := simple W hinj hp9 c (hprim τU ζU hptU) hrU
  obtain ⟨uD, hyD, huD'⟩ := simple W hinj hp9 c (hprim τD ζD hptD) hrD
  have DU := dv W hp9 hs1 c hpU
  have DD := dv W hp9 hs1 c hpD
  have hbU := hbS τU
  have hbD := hbS τD
  have hηD := hηb τD
  by_cases hcase : b τD + S + 2 * η < b τU
  · have hΛu : IsUnit (algebraMap (LetA O n) W.EE (Eπ ^ h')) := by rw [map_pow]; exact hEu.pow _
    set a₀ : LetA O n := letE c * ((π' - algebraMap O (LetA O n) rU) ^ (h' - b τU) *
      (π' - algebraMap O (LetA O n) rD) ^ (h' + (b τD + S))) with ha₀
    have ha₀Δ : a₀ ∈ W.AΔ := W.AΔ.mul_mem (letE_mem W c) (W.AΔ.mul_mem
      (W.AΔ.pow_mem (W.AΔ.sub_mem hπΔ (W.AΔ.algebraMap_mem _)) _)
      (W.AΔ.pow_mem (W.AΔ.sub_mem hπΔ (W.AΔ.algebraMap_mem _)) _))
    have hea₀ : (letE c : LetA O n) * a₀ = a₀ := by rw [ha₀, ← mul_assoc, CrystallineExponents.letE_mul_self]
    have hΛ₀ : algebraMap (LetA O n) W.EE (Eπ ^ h') *
        ((↑hΛu.unit⁻¹ : W.EE) * algebraMap (LetA O n) W.EE a₀) = algebraMap (LetA O n) W.EE a₀ := by
      rw [← mul_assoc, hΛu.mul_val_inv, one_mul]
    have hlev₀ : ∀ ζ, W.lev c ζ a₀ = yR W π' c rU ζ ^ (h' - b τU) * yR W π' c rD ζ ^ (h' + (b τD + S)) := by
      intro ζ
      rw [ha₀, map_mul, lev_letE, one_mul, map_mul, map_pow, map_pow, map_sub, map_sub, lev_alg, lev_alg]
      rfl
    have hvanD : ∀ τ ζ, Pt c ζ τ → constantCoeff (W.lev c ζ π') = algebraMap O LL rD →
        ∀ i < h' + (b τD + S), coeff i (W.lev c ζ a₀) = 0 := by
      intro τ ζ hpt hr
      obtain ⟨u, hyu, -⟩ := simple W hinj hp9 c (hprim τ ζ hpt) hr
      rw [hlev₀, mul_comm]
      exact van_of_dvd hyu _
    have hN := memNL0 W T₂ Pt π' Eπ h' c ha₀Δ hea₀ hΛ₀ x hx fun τ ζ hpt => by
      cases hu : up τ
      · refine ⟨_, hvanD τ ζ hpt (hDr τ ζ hpt hu), low T₂ V₂ hd2 τ ζ hpt x hx _ ?_⟩
        have := hτD τ ζ hpt hu
        subst this
        simp only [hu]; push_cast; omega
      · have := hτU τ ζ hpt hu
        subst this
        refine ⟨h' - b τ, fun i hi => ?_, ?_⟩
        · rcases hrr τ ζ hpt with hr | hr
          · obtain ⟨u, hyu, -⟩ := simple W hinj hp9 c (hprim τ ζ hpt) hr
            rw [hlev₀]
            exact van_of_dvd hyu _ i hi
          · exact hvanD τ ζ hpt hr i (by omega)
        · rw [show (h' : ℤ) - ((h' - b τ : ℕ) : ℤ) = b τ by omega]
          exact hxU τ ζ hpt hu
    obtain ⟨m, a', y', hy', hGd, hcmp⟩ := compare W F hfr hc1 hc2 hj1 hj2 hMF1 hMF2 hW hNL V₂ hEu hh hE
      hea₀ hΛ₀ x hx hN
    have hy2 : ∀ j, W.map F (y' j) ∈ NcS W T₂ (c - 1) := fun j => u3downPf_map_NcS W F hc1 hc2 _ (hy' j)
    have hmap : ∀ o : Fin m → O, W.map F (∑ j, o j • y' j) = ∑ j, o j • W.map F (y' j) := by
      intro o
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => LinearMap.map_smul_of_tower _ _ _
    have hsumN : ∀ o : Fin m → O, ∑ j, o j • y' j ∈ NcS W T₁ (c - 1) := fun o =>
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hy' j)
    obtain ⟨o, ho1, ho2⟩ := caseB DU DD hyU huU' hyD huD' (δ := algebraMap O LL (rU - rD))
      (fun h => sub_ne_zero.2 hrne (hinj (h.trans (map_zero _).symm)))
      (by simp only [yR, map_sub]; ring) a' (fun j => valAt W T₁ c ζU (y' j))
      (fun j => valAt W T₂ c ζU (W.map F (y' j))) (valAt W T₂ c ζU x)
      (CrystallineExponents.filC_anti T₁ τU) (CrystallineExponents.filC_anti T₁ τD) h' (b τU) (b τD + S) η (by omega) hcase
      ((PD.p : LL) ^ (ρ + 2 * σ)) (fun o ho => by
        rw [← V₁.sum hptU _ o y' hy'] at ho ⊢
        rw [V₁.indep _ _ _ _ hptU hptD _ (hsumN o)] at ho ⊢
        have h0 := V₁.inj τD ζD hptD _ (hsumN o) (filC_top T₁ τD _ (fun i hi hJ => by
          have h := hd1 τD i hJ
          unfold deep at h
          simp only [huD, Bool.false_eq_true, if_false, Set.mem_union, Set.mem_Icc] at h
          omega) ho)
        refine ⟨h0, ?_⟩
        rw [← V₂.sum hptU _ o _ hy2, ← hmap]
        exact (V₂.ker τU ζU hptU _ (u3downPf_map_NcS W F hc1 hc2 _ (hsumN o))).2
          (UnivLinkPf.univLinkPf_map_PiNS W F hc1 hc2 π' 1 ((V₁.ker τD ζD hptD _ (hsumN o)).1 h0)))
      (by
        have := hGd τD ζD hptD
        rwa [funext fun j => V₁.indep _ _ _ _ hptD hptU _ (hy' j)] at this)
      (hGd τU ζU hptU) (fun i hi => by rw [hcmp τU ζU hptU i hi, hlev₀, mul_assoc])
    rw [← V₁.sum hptU _ o y' hy'] at ho1
    rw [← V₂.sum hptU _ o _ hy2, ← hmap] at ho2
    have hFN := u3downPf_map_NcS W F hc1 hc2 _ (hsumN o)
    have hd : W.map F (∑ j, o j • y' j) - ((PD.p : ℕ) : O) ^ (ρ + 2 * σ) • x ∈ PiNS W T₂ π' 1 := by
      refine (V₂.ker τU ζU hptU _ (Submodule.sub_mem _ hFN (Submodule.smul_mem _ _ hx))).1 ?_
      rw [sub_eq_add_neg, ← neg_smul, V₂.add τU ζU hptU _ hFN _ (Submodule.smul_mem _ _ hx),
        V₂.smul τU ζU hptU _ _ hx, ho2, map_neg, map_pow, map_natCast, neg_smul, add_neg_cancel]
    refine lifts_mono W F (Nat.add_le_add_left (le_max_left _ _) _) (core W F hfr hc1 hc2 hj1 hj2 hMF1
      hMF2 hM f x hx _ (hsumN o) _ hd (hC T₁ V₁ hd1 _ (hsumN o) fun τ ζ hpt hu => ?_) hI2 h1 y hy hα)
    have := hτU τ ζ hpt hu
    subst this
    rw [V₁.indep _ _ _ _ hpt hptU _ (hsumN o)]
    unfold Formalism.MainNotions.DeltaInvariantLattices.FilC at ho1 ⊢
    rwa [fildR_gap T₁ τ (η + 1) (b τ) (by have := hηb τ; omega) fun i h1 h2 hJ => by
      have h := hd1 τ i hJ
      unfold deep at h
      simp only [hu, if_true, Set.mem_union, Set.mem_Icc] at h
      omega]
  · obtain ⟨x₀, hx₀⟩ := hdn τD ζD hptD huD
    have hint := integ DU DD hyU huU' hyD huD' (δ := algebraMap O LL (rD - rU))
      (fun h => sub_ne_zero.2 hrne.symm (hinj (h.trans (map_zero _).symm)))
      (by simp only [yR, map_sub]; ring) ⟨a, ha⟩ x₀ (algebraMap O LL a₂) h' (b τU) (b τD + S) (by omega)
      (hup τU ζU hptU huU) (fun i hi => by rw [← hfac, ← map_pow]; exact hx₀ i (by omega))
    obtain ⟨y₀, hy₀, o₁, ho₁⟩ : ∃ y₀ ≤ yc, ∃ o₁ : O,
        algebraMap O LL o₁ = (PD.p : LL) ^ y₀ * (x₀ * algebraMap O LL a₂ ^ h') := by
      rcases lt_or_ge (b τU) (b τD + S) with h | h
      · obtain ⟨o₁, ho₁⟩ := hint (b τU) h
        exact ⟨0, Nat.zero_le _, o₁, by simpa using ho₁⟩
      · obtain ⟨o₁, ho₁⟩ := hint (b τD + S - 1) (by omega)
        exact ⟨yc, le_rfl, caseC PD.p (rD - rU) hδ hun _ (b τU) (b τD + S) (by omega) h o₁ ho₁ yc
          (hyc _ _ (by omega) (by omega) h)⟩
    obtain ⟨o, ho⟩ : ∃ o : O, algebraMap O LL o = (PD.p : LL) ^ y₀ * x₀ := by
      obtain ⟨a₃, ha₃⟩ := ha₂.exists_right_inv
      refine ⟨o₁ * a₃ ^ h', ?_⟩
      rw [map_mul, ho₁, mul_assoc, mul_assoc, map_pow, ← mul_pow, ← map_mul, ha₃, map_one, one_pow,
        mul_one]
    set aN : LetA O n := ((PD.p : ℕ) : O) ^ y₀ • a - o • (letE c * Eπ ^ h') with haN
    have haNΔ : aN ∈ W.AΔ := W.AΔ.sub_mem (W.AΔ.smul_mem ha _)
      (W.AΔ.smul_mem (W.AΔ.mul_mem (letE_mem W c) (W.AΔ.pow_mem hEΔ _)) _)
    have heN : (letE c : LetA O n) * aN = aN := by
      rw [haN, mul_sub, mul_smul_comm, mul_smul_comm, hea, ← mul_assoc, CrystallineExponents.letE_mul_self]
    have hΛN : algebraMap (LetA O n) W.EE (Eπ ^ h') *
        (((PD.p : ℕ) : O) ^ y₀ • f - o • algebraMap (LetA O n) W.EE (letE c)) =
        algebraMap (LetA O n) W.EE aN := by
      rw [haN, mul_sub, mul_smul_comm, mul_smul_comm, hΛ, map_sub, algE_smul, algE_smul, ← map_mul,
        mul_comm]
    have hlevN : ∀ ζ i, coeff i (W.lev c ζ aN) = (PD.p : LL) ^ y₀ *
        (coeff i (W.lev c ζ a) - x₀ * coeff i (W.lev c ζ (Eπ ^ h'))) := by
      intro ζ i
      rw [haN, map_sub, map_sub, lev_smul, lev_smul, map_mul, lev_letE, one_mul, ho, map_pow, map_natCast]
      ring
    have hN := memNL0 W T₂ Pt π' Eπ h' c haNΔ heN hΛN x hx fun τ ζ hpt => by
      cases hu : up τ
      · obtain ⟨u, hyu, -⟩ := simple W hinj hp9 c (hprim τ ζ hpt) (hDr τ ζ hpt hu)
        have ht := DD.transfer hyD huD' hyu (h' + b τD + S) ⟨a, ha⟩ ⟨Eπ ^ h', W.AΔ.pow_mem hEΔ _⟩ x₀ hx₀
        refine ⟨h' + b τD + S, fun i hi => ?_, low T₂ V₂ hd2 τ ζ hpt x hx _ ?_⟩
        · rw [hlevN, show coeff i (W.lev c ζ a) = x₀ * coeff i (W.lev c ζ (Eπ ^ h')) from ht i hi,
            sub_self, mul_zero]
        · have := hτD τ ζ hpt hu
          subst this
          simp only [hu]; push_cast; omega
      · have := hbS τ
        obtain ⟨e₁, he₁, -⟩ := hE τ ζ hpt
        refine ⟨h' - b τ, fun i hi => ?_, ?_⟩
        · have h2 := van_of_dvd (G := 1) he₁ h' i (by omega)
          rw [mul_one, ← map_pow] at h2
          rw [hlevN, hup τ ζ hpt hu i (by omega), h2, mul_zero, sub_zero, mul_zero]
        · rw [show (h' : ℤ) - ((h' - b τ : ℕ) : ℤ) = b τ by omega]
          exact hxU τ ζ hpt hu
    have hK2 := letE_inv W T₂ Pt π' Eπ h' c hEΔ (mkL W T₂ π' c x hx)
    refine lifts_mono W F (Nat.add_le_add_left (hy₀.trans (le_max_right _ _)) _)
      (combine W F hMF2 hM ρ y₀ o ⟨_, h1⟩ ⟨_, (Submodule.mem_inf.1 hK2).1⟩
        ⟨_, ModelFPf.NL_le_LamLA W T₂ π' Eπ h' c Pt hN⟩ (Subtype.ext ?_) (fun z hz hαz => ?_)
        (fun z hz hαz => ?_) y hy hα hyI)
    · simp only [Submodule.coe_add, Submodule.coe_smul, TensorProduct.sub_tmul,
        ← TensorProduct.smul_tmul']
      abel
    · exact core W F hfr hc1 hc2 hj1 hj2 hMF1 hMF2 hM _ x hx x₁ hx₁ ρ hdiff
        (letE_inv W T₁ Pt π' Eπ h' c hEΔ _) hK2 _ z hz hαz
    · exact u3upPf_lift W F Pt π' Eπ h' M ρ c _ _ hMF2 hM hW hNL hG1 hG2 _ _ hN z hz hαz

end Main

end Formalism.MainNotions.N.Ln34.LevelExpansions

end
