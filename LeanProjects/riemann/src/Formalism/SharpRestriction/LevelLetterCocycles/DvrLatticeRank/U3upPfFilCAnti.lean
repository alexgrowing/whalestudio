import Formalism.SharpRestriction.LevelLetterCocycles.UpPositionHypothesis
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantUniformizer
import Formalism.SharpRestriction.LevelLetterCocycles.MapCompZero
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.NinLamPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GamPiPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrobPiNPf

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem u3upPf_FilC_anti (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) {a a' : ℤ} (h : a' ≤ a) :
    Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a' := by
  have hs : ∀ k : ℤ, FildR PD T.ρ τ (k + 1) ≤ FildR PD T.ρ τ k := by
    intro k
    refine inf_le_inf_left _ ?_
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul u w => exact ⟨u ⊗ₜ ⟨(w : BdR), PD.Fil_anti k w.2⟩, rfl⟩
    | add z z' hz hz' => rw [map_add]; exact Submodule.add_mem _ hz hz'
  have hA : Antitone fun k => FildR PD T.ρ τ k := antitone_int_of_succ_le hs
  unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
  exact sup_le_sup_right (hA h) _

theorem u3upPf_memNL (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' S : ℕ) (up : (K →ₐ[Qp] LL) → Bool) (b : (K →ₐ[Qp] LL) → ℕ) (c : ZMod n)
    (hPt : ∀ ζ τ, Pt c ζ τ → Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c)
    (hup : ∀ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c → up τ = true) (f : W.EE)
    (hf : IsCoord W Pt π' Eπ h' S up b c f) (x : W.DD T) (hx : x ∈ NcS W T (c - 1))
    (hFil : ∀ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c → up τ = true → x ∈ FilL W T Pt c τ (b τ)) :
    f ⊗ₜ mkL W T π' c x hx ∈ NL W T Pt π' Eπ h' c := by
  obtain ⟨a, ha, hea, hΛ, hup0, -, -⟩ := hf
  apply Submodule.subset_span
  refine ⟨1, fun _ => ⟨a, ha⟩, fun _ => x, ⟨fun _ => hx, ?_⟩, ?_⟩
  · rw [Fin.sum_univ_one]
    show TensorProduct.map (LinearMap.mulLeft O (algebraMap (LetA O n) W.EE (Eπ ^ h'))) LinearMap.id
        (f ⊗ₜ mkL W T π' c x hx) = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ mkL W T π' c x hx
    rw [TensorProduct.map_tmul, LinearMap.mulLeft_apply, LinearMap.id_apply, hΛ, hea]
  · intro τ ζ hpt i
    have hO := hPt ζ τ hpt
    have hu := hup τ hO
    have hv : valAt W T c ζ x ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (b τ) := hFil τ hO hu ζ hpt
    show (∑ j : Fin 1, serC (W.lev c ζ a) (valAt W T c ζ x) i) ∈ _
    rw [Fin.sum_univ_one]
    unfold serC
    split_ifs with hi
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
      simp only [Int.toNat_natCast]
      by_cases hlt : k + b τ < h'
      · rw [hup0 τ ζ hpt hu k hlt, zero_smul]
        exact Submodule.zero_mem _
      · apply Submodule.smul_mem
        refine u3upPf_FilC_anti T τ ?_ hv
        push_neg at hlt
        omega
    · exact Submodule.zero_mem _

theorem u3upPf_PiNS_one (T : LocLat G Qp LL O) (π' : LetA O n) {M : ℕ} (hM : 1 ≤ M) {z : W.DD T}
    (hz : z ∈ PiNS W T π' M) : z ∈ PiNS W T π' 1 := by
  obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.1 hz
  refine Submodule.mem_inf.2 ⟨?_, hz2⟩
  rw [Submodule.restrictScalars_mem] at hz1 ⊢
  unfold Formalism.MainNotions.DeltaInvariantLattices.aN at hz1 ⊢
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz1
  refine Submodule.mem_map.2 ⟨π' ^ (M - 1) • w, (W.N T).smul_mem _ hw, ?_⟩
  simp only [Formalism.MainNotions.DeltaInvariantLattices.smulA, LinearMap.smul_apply, LinearMap.id_apply]
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' hM]

theorem u3upPf_lift {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n) (h' M ρ : ℕ) (c : ZMod n)
    (α : FrA W π' Eπ h' M c) (β : FrB W π' Eπ h' M c)
    (hMF : ModelF W T₂ Pt π' Eπ h' M c α β) (hM : 1 ≤ M) (hW : WKill W F ρ)
    (hNL : NinLam W T₁ Eπ h') (hG1 : GamPi W T₁ π') (hG2 : GamPi W T₂ π')
    (x : LA W T₂ π' c) (hx : x ∈ LamLA W T₂ π' Eπ h' c ⊤) (hxN : x ∈ NL W T₂ Pt π' Eπ h' c)
    (y : W.DD T₂) (hy : y ∈ LamPS W T₂ Eπ h' c)
    (hα : α T₂ ⟨x, hx⟩ = mkP W T₂ π' Eπ h' M c y hy) : LiftsBy W F π' Eπ h' ρ c y := by
  obtain ⟨n₂, hn₂, hn₂N, hα₂⟩ := hMF.1 x hx hxN
  have hd : y - n₂ ∈ PiNS W T₂ π' M := by
    refine (hMF.2.2.1 M hM le_rfl).1 0 (Submodule.zero_mem _) (y - n₂)
      (Submodule.sub_mem _ hy hn₂) ?_ (Submodule.zero_mem _)
    have h0 : (⟨0, Submodule.zero_mem _⟩ : ↥(LamLA W T₂ π' Eπ h' c ⊤)) = 0 := rfl
    rw [h0, map_zero]
    symm
    show Submodule.Quotient.mk ((⟨y, hy⟩ : ↥(LamPS W T₂ Eπ h' c)) - ⟨n₂, hn₂⟩) =
      (0 : QLamP W T₂ π' Eπ h' M c)
    rw [Submodule.Quotient.mk_sub, sub_eq_zero]
    exact hα.symm.trans hα₂
  have hyN : y ∈ NcS W T₂ c := by
    obtain ⟨-, hΔ, hl⟩ := (mem_LamPS W T₂ Eπ h' c y).1 hy
    refine (mem_NcS W T₂ c y).2 ⟨?_, hΔ, hl⟩
    have h1 := PiNS_le_N W T₂ π' M hd
    have h2 := ((mem_NcS W T₂ c n₂).1 hn₂N).1
    have h3 := Submodule.add_mem _ h1 h2
    rwa [sub_add_cancel] at h3
  obtain ⟨n₁, hn₁, hF⟩ := hW c n₂ hn₂N
  refine ⟨(mem_InvS W T₂ π' Eπ h' 1 c y).2 ⟨hy, (Submodule.mem_inf.1 (hG2 c y hyN)).1⟩, n₁,
    (mem_InvS W T₁ π' Eπ h' 1 c n₁).2 ⟨hNL c hn₁, (Submodule.mem_inf.1 (hG1 c n₁ hn₁)).1⟩, ?_⟩
  rw [hF, ← smul_sub]
  exact Submodule.smul_mem _ _ (u3upPf_PiNS_one W T₂ π' hM hd)

end Local

theorem u3upPf_pt_over (D : D7) (HW : HWOf D.loc) {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
    (hG : Good K 1 LL) (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) : Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c := by
  obtain ⟨τs, ⟨hemb, -⟩, hres⟩ := hpt
  apply AlgHom.ext
  intro z
  have hzK : (z : Om l) ∈ Ks K 1 := (le_sup_left : K0 K ≤ Ks K 1) z.2
  rw [AlgHom.comp_apply, hres (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 z) ⟨z, hzK⟩ rfl]
  exact hemb z ⟨z, hzK⟩ rfl

theorem u3upPf_MK_pos {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL) (h' : ℕ)
    (hh' : 1 ≤ h') : 1 ≤ MK l K h' := by
  have hs := frobpin_sK_pos hl K LL hG
  have h4 : (0 : ℝ) < 4 * (h' : ℝ) := by
    have : (1 : ℝ) ≤ h' := by exact_mod_cast hh'
    linarith
  have hs' : (0 : ℝ) < (sK l K : ℝ) := by exact_mod_cast hs
  exact Nat.ceil_pos.2 (div_pos h4 hs')

theorem u3upPf_ofR (D : D7) (HW : HWOf D.loc) (hMF : modelFR D HW) (hW : wKillR D HW)
    (hNL : ninLamR D HW) (hGP : gamPiR D HW) : UpSlotProposition D HW := by
  intro l _ hl K LL hG π' E hπ T₁ T₂ F S η m h' up b c α β hfr hN hall
  intro f hf x hx hFil h1 y hy hα
  obtain ⟨hc1, hc2, hon, hj1, hj2, hηb, hbS, hh', -, -⟩ := hN
  have hjI : ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
      (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) →
      ∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h') := by
    intro T hj τ a ha
    have hd := hj τ a ha
    have hb := hbS τ
    have hη := hηb τ
    rw [Set.mem_Icc]
    rcases hd with hd | hd
    · unfold deep at hd
      split_ifs at hd <;> (rw [Set.mem_Icc] at hd; constructor <;> omega)
    · rw [Set.mem_Icc] at hd
      constructor <;> omega
  have hM := u3upPf_MK_pos hl K LL hG h' hh'
  have hMF2 := hMF l hl K LL hG π' E hπ h' hh' c α β hfr T₂ hc2 (hjI T₂ hj2)
  have hW' := hW l hl K LL hG π' E hπ T₁ T₂ F h' hc1 hc2 hon (hjI T₁ hj1)
  have hNL1 := hNL l hl K LL hG π' E hπ T₁ h' hc1 (hjI T₁ hj1)
  have hG1 := hGP l hl K LL hG π' E hπ T₁ hc1
  have hG2 := hGP l hl K LL hG π' E hπ T₂ hc2
  have hxN := u3upPf_memNL _ T₂ _ π' _ h' S up b c (fun ζ τ hpt => u3upPf_pt_over D HW hG c ζ τ hpt)
    hall f hf x hx hFil
  exact u3upPf_lift _ F _ π' _ h' _ _ c α β hMF2 hM hW' hNL1 hG1 hG2 _ h1 hxN y hy hα

theorem u3upPf_step (hMF : ModelFStep) (hW : WStep) : UpSlotHypothesis := by
  intro D HW F Cm CA CB CK hA
  exact u3upPf_ofR D HW (hMF D HW F Cm CA CB CK hA) (hW D HW F Cm CA CB CK hA)
    (ninlam_pf D HW F Cm CA CB CK hA) (gamPiCondition D HW F Cm CA CB CK hA)

end Formalism.MainNotions.N.Ln34

end
