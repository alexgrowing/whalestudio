import Formalism.SharpRestriction.LevelLetterCocycles.UpPositionHypothesis
import Formalism.SharpRestriction.LevelLetterCocycles.UpPositionOfModels
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UnivLinkPfA
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ClassMapPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdCondition
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3downPfFildRConst
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.WLocal

noncomputable section

namespace Formalism.MainNotions.N.Ln34.DescentValuation

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct
open Formalism.MainNotions.N.Ln34 Formalism.MainNotions.N.Ln34.UnivLinkPf

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem u3downPf_map_NcS {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (h1 : IsCrys PD T₁.ρ)
    (h2 : IsCrys PD T₂.ρ) (c : ZMod n) {x : W.DD T₁} (hx : x ∈ NcS W T₁ c) : W.map F x ∈ NcS W T₂ c := by
  rw [mem_NcS] at hx ⊢
  exact ⟨W.map_N F h1 h2 x hx.1, univLinkPf_map_DelS W F hx.2.1, by rw [← map_letA_smul, hx.2.2]⟩

theorem u3downPf_mkL_eq (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n) {x z : W.DD T}
    (hx : x ∈ NcS W T (c - 1)) (hz : z ∈ NcS W T (c - 1)) (r : O) (h : z - r • x ∈ PiNS W T π' 1) :
    mkL W T π' c z hz = r • mkL W T π' c x hx := by
  unfold mkL
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap]
  simpa using h

theorem u3downPf_core {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {π' Eπ : LetA O n} {h' M σ S ρ : ℕ}
    {up : (K →ₐ[Qp] LL) → Bool} {b : (K →ₐ[Qp] LL) → ℕ} {c : ZMod n}
    {α : FrA W π' Eπ h' M c} {β : FrB W π' Eπ h' M c}
    (hfr : IsFrame W Pt π' Eπ h' M σ c α β) (hc1 : IsCrys PD T₁.ρ) (hc2 : IsCrys PD T₂.ρ)
    (hj1 : ∀ τ, JumpsInV PD T₁.ρ τ (Set.Icc (-(h' : ℤ)) h'))
    (hj2 : ∀ τ, JumpsInV PD T₂.ρ τ (Set.Icc (-(h' : ℤ)) h'))
    (hMF1 : ModelF W T₁ Pt π' Eπ h' M c α β) (hMF2 : ModelF W T₂ Pt π' Eπ h' M c α β) (hM : 1 ≤ M)
    (hK : ModelK W F π' ρ c)
    (hC1 : ∀ x (hx : x ∈ NcS W T₁ (c - 1)) f, IsCoord W Pt π' Eπ h' S up b c f →
      f ⊗ₜ mkL W T₁ π' c x hx ∈ InvL W T₁ Pt π' Eπ h' c ⊤)
    (hC2 : ∀ x (hx : x ∈ NcS W T₂ (c - 1)) f, IsCoord W Pt π' Eπ h' S up b c f →
      f ⊗ₜ mkL W T₂ π' c x hx ∈ InvL W T₂ Pt π' Eπ h' c ⊤) :
    ThirdPropositionSlot W F Pt π' Eπ h' M S up b c ρ α := by
  intro f hf x hx _ h1 y hy hα
  obtain ⟨x₁, hx₁, hdiff⟩ := hK x hx
  have hyI : y ∈ InvS W T₂ π' Eπ h' 1 c := hMF2.2.2.2.1 _ h1 y hy hα (hC2 x hx f hf)
  have hI1 := hC1 x₁ hx₁ f hf
  have hL1 : f ⊗ₜ mkL W T₁ π' c x₁ hx₁ ∈ LamLA W T₁ π' Eπ h' c ⊤ := (Submodule.mem_inf.1 hI1).1
  obtain ⟨w₁, hw₁⟩ := Submodule.Quotient.mk_surjective _ (α T₁ ⟨_, hL1⟩)
  have hw₁I : (w₁ : W.DD T₁) ∈ InvS W T₁ π' Eπ h' 1 c := hMF1.2.2.2.1 _ hL1 w₁ w₁.2 hw₁.symm hI1
  have hmx : W.map F x₁ ∈ NcS W T₂ (c - 1) := u3downPf_map_NcS W F hc1 hc2 (c - 1) hx₁
  have hL2 : f ⊗ₜ mkL W T₂ π' c (W.map F x₁) hmx ∈ LamLA W T₂ π' Eπ h' c ⊤ :=
    (Submodule.mem_inf.1 (hC2 _ hmx f hf)).1
  have hy₂ : W.map F (w₁ : W.DD T₁) ∈ LamPS W T₂ Eπ h' c := univLinkPf_map_LamPS W F hc1 hc2 Eπ h' c w₁.2
  have hnat := (hfr.2 T₁ T₂ F hc1 hc2 hj1 hj2).1 _ hL1 _ hL2 _ w₁.2 hy₂
    ⟨1, fun _ => f, fun _ => x₁, fun _ => hx₁, fun _ => hmx, by simp, by simp⟩ hw₁.symm
  have heq : mkL W T₂ π' c (W.map F x₁) hmx = ((PD.p : ℕ) : O) ^ ρ • mkL W T₂ π' c x hx :=
    u3downPf_mkL_eq W T₂ π' c hx hmx _ hdiff
  have hsub : (⟨_, hL2⟩ : ↥(LamLA W T₂ π' Eπ h' c ⊤)) = ((PD.p : ℕ) : O) ^ ρ • ⟨_, h1⟩ :=
    Subtype.ext (by simp [heq, TensorProduct.tmul_smul])
  rw [hsub, map_smul, hα] at hnat
  have hJ : Submodule.Quotient.mk (((PD.p : ℕ) : O) ^ ρ • (⟨y, hy⟩ : ↥(LamPS W T₂ Eπ h' c)) - ⟨_, hy₂⟩) =
      (0 : QLamP W T₂ π' Eπ h' M c) := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, sub_eq_zero]
    exact hnat
  have hP := univLinkPf_PiNS_anti W T₂ π' hM (univLinkPf_JP W T₂ hMF2 hM _ hJ)
  refine ⟨hyI, w₁, hw₁I, ?_⟩
  simpa using hP

theorem u3downPf_jumps (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (u : Bool) (bt S η h' : ℕ)
    (hj : JumpsInV PD T.ρ τ (deep u bt S ∪ Set.Icc (-(η : ℤ)) η)) (hηb : η < bt) (hbS : bt + S ≤ h') :
    JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h') := by
  intro a ha
  have h := hj a ha
  unfold deep at h
  split_ifs at h <;> simp only [Set.mem_union, Set.mem_Icc] at h ⊢ <;> omega

end Local

section Record

theorem u3downPf_sK_pos {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL) :
    1 ≤ sK l K := by
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have hl1 : 0 < l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  have he : 0 < eK K := by
    rcases Nat.eq_zero_or_pos (eK K) with h | h
    · rw [h, zero_dvd_iff] at hd; omega
    · exact h
  exact Nat.div_pos (Nat.le_of_dvd hl1 hd) he

theorem u3downPf_modelK_of_wKill (D : D7) (HW : HWOf D.loc) (hW : wKillR D HW) : modelKR D HW := by
  intro l _ hl K LL hG π' E hp T₁ T₂ F h' _ hc1 hc2 hon hj1 c y hy
  obtain ⟨x, hx, hxy⟩ := hW l hl K LL hG π' E hp T₁ T₂ F h' hc1 hc2 hon hj1 (c - 1) y hy
  exact ⟨x, hx, by rw [hxy, sub_self]; exact Submodule.zero_mem _⟩

theorem u3downPf_lemC_rec (D : D7) (HW : HWOf D.loc) (Fo : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW Fo) (h1 : adm1 D HW Fo Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (S η h' : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool)
    (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) (c : ZMod (finrank ℚ_[l] ↥(K0 K)))
    (hc : IsCrys ((D.loc l).PD K) T.ρ)
    (hj : ∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η))
    (hηb : ∀ τ, η < b τ)
    (hdown : ∀ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c → up τ = false) :
    LemC ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' S up b c := by
  intro x hx _ f hf
  obtain ⟨-, -, ⟨w, hw⟩, -, ⟨w', hw'⟩, -⟩ := hp
  have hprim : ∀ τ ζ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → IsPrimitiveRoot ζ ((D.loc l).PD K).p := by
    intro τ ζ hpt
    rw [(D.loc l).PD_p K]
    exact framepf_pt_prim D HW hG c ζ τ hpt
  have hdown' : ∀ τ ζ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → up τ = false := fun τ ζ hpt =>
    hdown τ (u3upPf_pt_over D HW hG c ζ τ hpt)
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hgk : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [(D.loc l).PD_p K]; exact hl)
  refine u3downPf_lemC ((HW l).W K 1 LL hG) T _ π' _ h' S up b c ?_ ?_ hdown' ?_ ?_ ?_ ?_ ?_ x hx f hf
  · rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (((HW l).W K 1 LL hG).EE_π.pow _)
  · have hq := Formalism.MainNotions.LiftingTheory.liftb_q_unit ((HW l).W K 1 LL hG)
    rw [hw', map_mul] at hq
    exact isUnit_of_mul_isUnit_right hq
  · intro τ ζ hpt
    exact u3downPf_cc_π' _ c ζ (hprim τ ζ hpt) π' _ w hw
  · intro τ ζ hpt
    exact u3downPf_lev_E _ c ζ (hprim τ ζ hpt) _ w' hw'
  · intro τ ζ hpt
    refine ⟨algebraMap ↥(OL LL) ↥LL.1 (((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : ↥(OL LL)),
      (((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK).isUnit.map (algebraMap ↥(OL LL) ↥LL.1)).ne_zero),
      fun a => ?_⟩
    have hv : ((1 : ℕ) : WithTop ℚ) ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
        (((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : ↥(OL LL)) - ((1 : ℕ) : ↥LL.1)) := by
      rw [hgk, Nat.cast_one, Nat.cast_one, ((HW l).W K 1 LL hG).gam_gen, hs, Nat.cast_one]
    have h1' : IsPrimitiveRoot ζ (((D.loc l).PD K).p ^ 1) := by rw [pow_one]; exact hprim τ ζ hpt
    have := ((Cm l).C K 1 LL hG).tie.lev_Γ ((HW l).W K 1 LL hG).gamK c ζ ζ 1 1 h1' hv (by rw [pow_one]) a
    exact this
  · intro x' hx' τ ζ hpt
    exact u3downPf_valAt_fil _ T c ζ τ (((h1 l K 1 LL hG).2.2.2.1 T hc).2 c ζ τ hpt).2.1 x' hx'
  · intro τ ζ hpt a hJ
    have h := hj τ a hJ
    have hd := hdown' τ ζ hpt
    have hb := hηb τ
    unfold deep at h
    rw [if_neg (by simp [hd])] at h
    simp only [Set.mem_union, Set.mem_Icc] at h
    omega

theorem u3downPf_link (hW : WStep) : DownSlotOfModels := by
  intro D HW Fo Cm CA CB CK hA hMF l _ hl K LL hG π' E hp T₁ T₂ F S η m h' up b c α β hfr hN hdown
  obtain ⟨hc1, hc2, hon, hj1, hj2, hηb, hbS, hh', -, -⟩ := hN
  have hJ1 : ∀ τ, JumpsInV ((D.loc l).PD K) T₁.ρ τ (Set.Icc (-(h' : ℤ)) h') := fun τ =>
    u3downPf_jumps T₁ τ (up τ) (b τ) S η h' (hj1 τ) (hηb τ) (hbS τ)
  have hJ2 : ∀ τ, JumpsInV ((D.loc l).PD K) T₂.ρ τ (Set.Icc (-(h' : ℤ)) h') := fun τ =>
    u3downPf_jumps T₂ τ (up τ) (b τ) S η h' (hj2 τ) (hηb τ) (hbS τ)
  have hM : 1 ≤ MK l K h' :=
    Formalism.MainNotions.N.Ln34.ClassMapPf.classMapPf_MK_pos K h' hh' (u3downPf_sK_pos hl K LL hG)
  have hF' := hMF l hl K LL hG π' E hp h' hh' c α β hfr
  have hK' := u3downPf_modelK_of_wKill D HW (hW D HW Fo Cm CA CB CK hA) l hl K LL hG π' E hp
    T₁ T₂ F h' hh' hc1 hc2 hon hJ1 c
  refine u3downPf_core ((HW l).W K 1 LL hG) F hfr hc1 hc2 hJ1 hJ2 (hF' T₁ hc1 hJ1) (hF' T₂ hc2 hJ2)
    hM hK' ?_ ?_
  · intro x hx f hf
    exact u3downPf_lemC_rec D HW Fo Cm hA.1 hl K LL hG π' E hp T₁ S η h' up b c hc1 hj1 hηb hdown x hx
      (fun τ hτ hup => by simp [hdown τ hτ] at hup) f hf
  · intro x hx f hf
    exact u3downPf_lemC_rec D HW Fo Cm hA.1 hl K LL hG π' E hp T₂ S η h' up b c hc2 hj2 hηb hdown x hx
      (fun τ hτ hup => by simp [hdown τ hτ] at hup) f hf

end Record

theorem down_of_models : Formalism.MainNotions.N.Ln34.DownSlotOfModels := u3downPf_link Formalism.MainNotions.N.Ln34.w_pf

end Formalism.MainNotions.N.Ln34.DescentValuation
