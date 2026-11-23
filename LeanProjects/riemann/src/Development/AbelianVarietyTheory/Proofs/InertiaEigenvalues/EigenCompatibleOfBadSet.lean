import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjEqOfNormalises
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentVacuumHyperspecialDictionary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHyperspecialSubgroupAtPlaceIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsHeckeDatum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFamilyIffRationalHecke
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt

noncomputable section

namespace GlobalTheory.TwInputs.Eig

section Satake

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult ReciprocityTheory.Aut Formalism.AUTREP
  NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.EigRows
open GlobalTheory.StdFrame (StdPsi tensCastR)
open GlobalTheory.Hk3 (hyp SphOp)
open GlobalTheory.HeckeScalarSph (locK)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {Q : principalLevelFrame.RowPsi V n}

theorem triv_iff (hQ : StdPsi hF Q) (s : SplitPlace D.host.E) (κ : GAf D.host.E n) :
    TrivOutside {s.v} κ ↔ Q.ψ κ ∈ (emb D.sp.cm.sig V.gram (s.w.under (𝓞 D.host.F))).range := by
  obtain ⟨⟨β, β', h1, h2, hβ⟩, -⟩ := hQ
  rw [range_emb, mem_atPts, triv_cast hF, and_iff_right (show Q.ψ κ ∈ finPts D.sp.cm.sig V.gram from Q.into κ)]
  refine forall_congr' fun u => imp_congr (by simp) ?_
  let φ := (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F u) (AlgHom.id D.host.F D.host.E)).toRingHom
  have e : (matHom _ D.sp.cm.sig V.gram (proj D.sp.cm.sig V.gram u (Q.ψ κ))).1 = (finMat D.sp.cm.sig V.gram (Q.ψ κ)).map φ := by
    rw [← projFinLoc_projFin]; rfl
  have e2 := e.trans (congrArg (fun M => Matrix.map M φ) (hβ κ))
  refine (map_conj_eq_one_iff φ h1 h2 _).trans ?_
  exact ⟨fun h => Subtype.ext (Units.ext (e2.trans h)), fun h => e2.symm.trans (by rw [h]; rfl)⟩

theorem hyp_iff (hQ : StdPsi hF Q) (s : SplitPlace D.host.E) (κ : GAf D.host.E n) :
    Q.ψ κ ∈ hyp V s.w ↔ κ ∈ locK n s.v := by
  rw [GlobalTheory.HypDict.mem_hyp_iff_embV D _ s.w rfl]
  constructor
  · rintro ⟨k, hk, e⟩
    exact ⟨(hQ.2 κ).2 (e ▸ (Supp.emb_mem_KsphC V k).2 hk), (triv_iff hQ s κ).2 ⟨k, e.symm⟩⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨k, e⟩ := (triv_iff hQ s κ).1 h2
    exact ⟨k, (Supp.emb_mem_KsphC V k).1 (e ▸ (hQ.2 κ).1 h1), e.symm⟩

theorem exists_locMat {Q : principalLevelFrame.RowPsi V V.rank} (hQ : StdPsi hF Q) (s : SplitPlace D.host.E)
    (i : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E) (hi : Continuous i)
    (hic : ∀ x : D.host.E, i (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) :
    ∃ b : GL (Fin V.rank) (s.w.adicCompletion D.host.E), ∀ κ,
      locMat D.sp.cm.sig V.gram (rfl : s.w.under (𝓞 D.host.F) = _) (proj D.sp.cm.sig V.gram _ (Q.ψ κ)) =
        b * Matrix.GeneralLinearGroup.map i.toRingHom (s.loc V.rank κ) * b⁻¹ := by
  obtain ⟨⟨β, β', h1, h2, hβ⟩, -⟩ := hQ
  refine ⟨⟨β.map (GlobalTheory.LFun.compAt D.host.F s.w), β'.map (GlobalTheory.LFun.compAt D.host.F s.w),
    map_mul_eq_one _ h1, map_mul_eq_one _ h2⟩, fun κ => Units.ext ?_⟩
  have e : (κ.1.1.map (tensCastR hF).symm).map (GlobalTheory.LFun.compAt D.host.F s.w) =
      (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc V.rank κ)).1 := Matrix.ext fun a b => compAt_cast hF s i hi hic _
  refine (finMat_map_compAt _ _ _ _).symm.trans
    ((congrArg (fun M => Matrix.map M (GlobalTheory.LFun.compAt D.host.F s.w)) (hβ κ)).trans ((map_conj _ _).trans ?_))
  rw [e]
  rfl

theorem rank_eq (hQ : StdPsi hF Q) (w : HeightOneSpectrum (𝓞 D.host.E)) : n = V.rank := by
  obtain ⟨⟨β, β', h1, h2, -⟩, -⟩ := hQ
  have m1 := map_mul_eq_one (GlobalTheory.LFun.compAt D.host.F w) h1
  have m2 := map_mul_eq_one (GlobalTheory.LFun.compAt D.host.F w) h2
  have a := (Matrix.rank_mul_le_left _ _).trans' (congrArg Matrix.rank m1).ge
  have b := (Matrix.rank_mul_le_left _ _).trans' (congrArg Matrix.rank m2).ge
  rw [Matrix.rank_one, Fintype.card_fin] at a b
  exact le_antisymm (b.trans (Matrix.rank_le_width _)) (a.trans (Matrix.rank_le_width _))

set_option maxHeartbeats 1000000 in

theorem sphEig_eq_satEig (hQ : StdPsi hF Q) (π : NG.FinTyp D.host.E n) (s : SplitPlace D.host.E)
    (hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (s.w.under (𝓞 D.host.F)))
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion D.host.E))) (hτ : IsLocS π.S s τ) {α : Fin n → ℂˣ}
    (hα : GlobalTheory.SmGL.HasSatake τ.ρ α) {k : ℕ} (hk : k ≤ n) :
    sphEig Q π s.w (diagLab n k) = satEig (Formalism.UG.qV D.host.E s.w) n (Finset.univ.val.map α) k := by
  obtain rfl := rank_eq hQ s.w
  obtain ⟨i, T, hi, hic, hinj, hTS, hT⟩ := hτ
  obtain ⟨u, hu⟩ := (GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake D.host.E s.w _ _ τ.ρ α hα).exists_vec
  obtain ⟨b, hb⟩ := exists_locMat hQ s i hi hic
  have hL := GlobalTheory.HeckeDual.isLattice_frameLat V
  obtain ⟨e, he, -⟩ := SplitChart.exists_isSplitChart (isCMExt_host D)
    ((GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V) hL.fg hL.span_eq_top
    (rfl : s.w.under (𝓞 D.host.F) = _) hs (GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D V _)
  obtain ⟨⟨a, -, ha⟩, hK⟩ := id he

  have hκ : ∀ g, ∃ κ, Q.ψ κ = emb D.sp.cm.sig V.gram (s.w.under (𝓞 D.host.F)) g := fun g =>
    Q.onto _ (mem_finPts.2 (projInf_emb _ _ _ g))
  choose κ hκ using hκ
  have htr : ∀ g, TrivOutside {s.v} (κ g) := fun g => (triv_iff hQ s _).2 ⟨g, (hκ g).symm⟩
  have hM : ∀ g, Matrix.GeneralLinearGroup.map i.toRingHom (s.loc V.rank (κ g)) = (a⁻¹ * b)⁻¹ * e g * (a⁻¹ * b) := fun g => by
    have := hb (κ g)
    rw [hκ, proj_emb_self] at this
    rw [ha, this]; group
  obtain ⟨c, hc, hcc⟩ := conj_eq_of_normalises s.w (a⁻¹ * b) fun y hy => by
    obtain ⟨g, rfl⟩ := e.surjective y
    rw [← hM, map_loc_mem_iff s i hi hic (htr g), hQ.2, hκ, Supp.emb_mem_KsphC]
    exact (hK g).2 hy
  have hfix : ∀ y ∈ KGL s.w V.rank, τ.ρ y u = u := GlobalTheory.LGrp.mem_fixed.1 hu.2.1
  have hx : IsSphVec Q π s.w (T u) := ⟨hTS u, fun y hy => by
    obtain ⟨h1, h2⟩ := (hyp_iff hQ s y).1 hy
    rw [← hT y h2, hfix _ ((map_loc_mem_iff s i hi hic h2).2 h1)]⟩
  let Φ : τ.V →ₗ[ℂ] (GA D V → ℂ) := GlobalTheory.SphScalar.ext0 Q ∘ₗ T ∘ₗ τ.ρ c⁻¹
  have hΦu : Φ u = GlobalTheory.SphScalar.ext0 Q (T u) := by
    simp only [Φ, LinearMap.comp_apply, hfix _ (inv_mem hc)]
  have hΦ : ∀ y w, Φ (τ.ρ y w) = (((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram (s.w.under (𝓞 D.host.F)))).comp
      e.symm.toMonoidHom) y (Φ w) := fun y w => by
    obtain ⟨g, rfl⟩ := e.surjective y
    have h1 : τ.ρ c⁻¹ (τ.ρ (e g) w) = τ.ρ (c⁻¹ * e g * c) (τ.ρ c⁻¹ w) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]
    simp only [Φ, LinearMap.comp_apply]
    rw [h1, ← hcc, ← hM, hT _ (htr g), GlobalTheory.SphScalar.extendByZeroThroughUnitaryFrame_right_translate, hκ]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  have h0 : Φ u ≠ 0 := fun h => hu.1 (hinj (GlobalTheory.SphScalar.extendByZeroThroughUnitaryFrame_injective Q (by rw [← hΦu, h, map_zero, map_zero])))
  have hsat := hu.map Φ hΦ h0
  have hfx := (mem_fixed_comp_symm e hK).1 hsat.2.1
  have hsys := isEigenSys_of_heckeLin (sphOff_KsphC V ∅) (Finset.notMem_empty _) (rfl : s.w.under (𝓞 D.host.F) = _) hfx
    (c := sphEig Q π s.w) fun d R hR => by
      have h1 := congrArg (GlobalTheory.SphScalar.ext0 Q) (actsOnSph_sphEig hQ π s.w d R hR _ hx)
      rw [GlobalTheory.SphScalar.extendByZeroThroughUnitaryFrame_hecke Q R fun γ hγ => Q.onto γ ?_, map_smul, ← hΦu] at h1
      · rw [← h1]
        funext g
        rw [Finset.sum_apply]
        rfl
      · obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, -, -, h2⟩ := hR
        exact (h2.1 γ hγ).1
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV s.w
  exact smul_left_injective ℂ h0 ((hsys.split hfx he hϖ hk).symm.trans (hsat.2.2.2 ϖ hϖ k hk))

end Satake

section Rows

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem
  GlobalTheory.HeightCounting GlobalTheory.EigRows
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 400000

def Low (D : D7) (Sb : Finset (PlE D.host)) : Prop :=
  ∀ P : PlE D.host, ((2 * (D.host.g 0 * D.host.g 1) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → P ∈ Sb

theorem exists_low {D : D7} {ι : Type} (Sb : Finset (PlE D.host)) (S₀ : ι → Finset (PlE D.host)) (h : ∀ i, Sb ⊆ S₀ i)
    (h' : ∀ i, Low D (S₀ i)) : ∃ Sb', Sb ⊆ Sb' ∧ Low D Sb' ∧ ∀ i, Sb' ⊆ S₀ i := by
  classical
  have hf := GlobalTheory.RowTie.placesOver_finite_of_ne_zero D.host.E (2 * (D.host.g 0 * D.host.g 1))
    (mul_ne_zero two_ne_zero (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero))
  exact ⟨Sb ∪ hf.toFinset, Finset.subset_union_left, fun P hP => Finset.mem_union_right _ (hf.mem_toFinset.2 hP),
    fun i => Finset.union_subset (h i) fun P hP => h' i P (hf.mem_toFinset.1 hP)⟩

theorem low_SbD (D : D7) : Low D (RatSide.SbD D) := by
  intro P hP
  refine (RatSide.lowSet_finite D).mem_toFinset.2 ?_
  rw [Nat.cast_mul, Nat.cast_mul] at hP
  rcases P.isPrime.mem_or_mem hP with h | h
  · exact ⟨2, by simp [lowAll, lowPr], two_ne_zero, h⟩
  · rcases P.isPrime.mem_or_mem h with h | h
    · exact ⟨_, by simp [lowAll], (D.host.g_prime 0).ne_zero, h⟩
    · exact ⟨_, by simp [lowAll], (D.host.g_prime 1).ne_zero, h⟩

theorem Low.mono {D : D7} {S S' : Finset (PlE D.host)} (h : Low D S) (hs : S ⊆ S') : Low D S' := fun P hP => hs (h P hP)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Sb Sb' : Finset (PlE D.host)}

theorem Low.odd (h : Low D Sb) {P : PlE D.host} (hP : P ∉ Sb) : ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h2 =>
  hP (h P (by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h2))

theorem Low.type (h : Low D Sb) {P : PlE D.host} (hP : P ∉ Sb) (k : Fin 2) : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h2 =>
  hP (h P (by
    rw [Nat.cast_mul, Nat.cast_mul]
    refine Ideal.mul_mem_left _ _ ?_
    fin_cases k
    exacts [Ideal.mul_mem_right _ _ h2, Ideal.mul_mem_left _ _ h2]))

theorem Low.offPg (h : Low D Sb) (hL : R.toLevCh.Is A3.A.μ0) {P : PlE D.host} (hP : P ∉ Sb) :
    ∀ PP ∈ R.Pg, PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
  intro PP hPP
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPP
  have h1 := R.C.P.pb_over k
  rw [← hk] at h1
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (D.host.g k : ℕ) ∈ PP.asIdeal := h1
  rw [map_natCast] at h2
  refine ⟨fun e => h.type hP k (e ▸ h2), fun e => h.type hP k ?_⟩
  obtain ⟨c, hc, e⟩ := e _ h2
  have : c = (D.host.g k : ℕ) := RingOfIntegers.ext (by rw [e]; simp)
  exact this ▸ hc

theorem exists_hkDat (F : Face3 D A3) (hL : R.toLevCh.Is A3.A.μ0) (hsub : Sb ⊆ Sb') (hlow : Low D Sb') (i : Fin D.R.m) {P : PlE D.host}
    (hs : IsSplitPl D.host P) (hP : P ∉ Sb') {k : ℕ} (hk : k ≤ D.R.r) : ∃ α B, HkDat R Sb i k P α B ∧
      IsDiagOpAt (Wc D i) (levW R.toRealDat F.lv2 i) (chiW R.toRealDat F.lv2 i) ∅ P k B := by
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P ((GlobalTheory.HeckeTieCompare.isSplitPl_iff P).1 hs)
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
  obtain ⟨α, hα⟩ := ((GlobalTheory.SplitPlace.split_local (Wc D i) P e he).2.2 ϖ h1 h2).1 k ((rank_Wc i).symm ▸ hk)
  obtain ⟨B, hB, hD⟩ := exists_local (A3 := A3) (R := R.toRealDat) (F := F.lv2) hL i (hlow.offPg hL hP) hk ⟨e, ϖ, he, h1, h2, hα⟩
  exact ⟨α, B, ⟨hs, fun h => hP (hsub h), hlow.odd hP, hk, ⟨e, ϖ, he, h1, h2, hα⟩, hD⟩, hB⟩

theorem satEig_eq (Rk : Ranks) (q : ℕ) (B : Multiset ℂˣ) {k : ℕ} (hk : k ≤ Rk.r) :
    GlobalTheory.LFun.satEig q Rk.r B k = (q : ℂ) ^ (k * (Rk.r - k) / 2) * (B.map fun b : ℂˣ => (b : ℂ)).esymm k := by
  have hodd : Odd Rk.r := by
    obtain ⟨a, ha⟩ := Rk.k_even
    obtain ⟨b, hb⟩ := Rk.m_even
    have := Rk.two_le_m
    exact ⟨a + b - 1, by unfold Ranks.r; omega⟩
  have he : Even (k * (Rk.r - k)) := by
    rcases Nat.even_or_odd k with h | h
    · exact h.mul_right _
    · exact (Nat.Odd.sub_odd hodd h).mul_left _
  obtain ⟨c, hc⟩ := he
  have h1 : ((k : ℂ) * ((Rk.r : ℂ) - k)) / 2 = (c : ℕ) := by
    rw [← Nat.cast_sub hk, ← Nat.cast_mul, hc]; push_cast; ring
  rw [GlobalTheory.LFun.satEig, h1, Complex.cpow_natCast, hc, show (c + c) / 2 = c by omega]

set_option maxHeartbeats 1000000 in

theorem eigTrue (hL : GlobalTheory.Published.LocalLanglandsGL) (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hlev : R.toLevCh.Is A3.A.μ0)
    (W : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : RowSide D) {sat : D.what₂.FT → PlE D.host → Multiset ℂ}
    (hrow : RowTrue hL D (typeR Y) (fun σ w => W.e w (Rw.locR σ w)) sat)
    {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} (he : EigAd Y Sb eig) (hsub : Sb ⊆ Sb') (hlow : Low D Sb') :
    EigTrue D R.C Rw Sb' eig := by
  intro j σ hne hgood P hs hP
  obtain ⟨s, rfl⟩ := GlobalTheory.TypeBlockPf.splitAt D P hs
  have hQ := stdPsi_PW Y j
  obtain ⟨_, B₀, -, hB₀⟩ := exists_hkDat (Sb := Sb) F hlev hsub hlow j hs hP (Nat.zero_le _)
  obtain ⟨x, hx, hx0⟩ := exists_sphVec hQ (partR_ne_bot Y hne) hB₀.full
  have hK : ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.r s.v, NG.rt D.host.E D.R.r κ x = x := fun κ hκ =>
    hx.2 κ ((hyp_iff hQ s κ).2 hκ)
  obtain ⟨τ, hτ⟩ := exists_isLocS (typeR Y σ) s hx.1 hx0 hK
  have hrec := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 s.w)
  have hu := (GlobalTheory.CuspRep.ParLaws.unr_iff hrec τ).2 (isSpherical_of_isLocS (typeR Y σ) s τ hτ hx.1 hx0 hK)
  obtain ⟨α, hα⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake_of_unr hrec hu
  have hpar : W.e s.w (Rw.locR σ s.w) = _ := hrow.1 σ s τ hτ
  have hunr : D.naut.unr (Rw.locR σ s.w) := (W.unr _ _).2 (hpar ▸ hu)
  refine ⟨hunr, fun k _ hk => ?_⟩
  obtain ⟨a, B, hd, -⟩ := exists_hkDat (Sb := Sb) F hlev hsub hlow j hs hP hk
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h1 : hkNorm R j k s.w • heckeOn _ B (readW Y j y) = _ • readW Y j y := he j σ k s.w a B hd hgood y hy
  rw [heckeOn_partR Y hlev j (hlow.offPg hlev hP) hk hd.elt hd.reps σ ((mem_isot_iff Y j σ y).1 hy), smul_smul] at h1
  have h2 := smul_left_injective ℂ (fun h => hy0 (readW_injective Y j (h.trans (map_zero _).symm))) h1
  have h3 := sphEig_eq_satEig hQ (typeR Y σ) s ((GlobalTheory.PlaceDict.isSplit_iff_conjPl_ne D _ s.w rfl).2
    (GlobalTheory.HeckeDatumExists.conj_ne_of_split hs)) τ hτ hα hk
  have hq : Formalism.UG.qV D.host.E s.w = normV s.w := Ideal.absNorm_apply _
  have h4 : D.naut.frobEig (Rw.locR σ s.w) = Finset.univ.val.map fun i => (((α i)⁻¹ : ℂˣ) : ℂ) := by
    rw [W.frobEig _ _ hunr, hpar, GlobalTheory.CuspRep.ParLaws.rec_eq_diag hrec hα, GlobalTheory.WeilDeligne.WD.frobEig_diag]
  rw [← h2, rowEig, h3, satEig_eq _ _ _ hk, hq, h4, Multiset.map_map, Multiset.map_map]
  set c : ℂ := (((R.C.mu0 j).val s.w : ℂˣ) : ℂ)⁻¹ * (((normV s.w : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹ with hc
  have h5 : (Finset.univ.val.map ((fun a : ℂ => a⁻¹ * (((R.C.mu0 j).val s.w : ℂˣ) : ℂ)⁻¹ *
      (((normV s.w : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹) ∘ fun i => (((α i)⁻¹ : ℂˣ) : ℂ))) =
      (Finset.univ.val.map ((fun b : ℂˣ => (b : ℂ)) ∘ α)).map (c • ·) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    simp only [Function.comp_apply, Units.val_inv_eq_inv_val, inv_inv, smul_eq_mul, hc]
    ring
  have h6 : hkNorm R j k s.w = c ^ k := by
    rw [hc, mul_pow, inv_pow (_ ^ _), ← pow_mul, mul_comm (D.R.nV / 2)]
    rfl
  rw [h5, ← Multiset.pow_smul_esymm, h6, smul_eq_mul]
  ring

set_option maxHeartbeats 1000000 in

theorem exists_rat (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hlev : R.toLevCh.Is A3.A.μ0) (hU : R.toRealDat.LUnif)
    (hW : R.toRealDat.models_HW) {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} (he : EigAd Y Sb eig) (hsub : Sb ⊆ Sb')
    (hlow : Low D Sb') (i : Fin D.R.m) {σ : D.what₂.FT} (hne : D.what₂.isot (i.1 + 1) σ ≠ ⊥) (hgood : D.nd.goodRow σ)
    (Op : ℕ → PlE D.host → Module.End D.what₂.LL (Fin (R.nW i) → D.what₂.LL))
    (hOp : ∀ k P α Rr, HkDat R Sb' i k P α Rr → ∀ x, (R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) (Op k P x)) =
      hkNorm R i k P • heckeOn (R.MW i (sg0 D A3.A)) Rr ((R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) x))) :
    ∃ x, x ≠ 0 ∧
      ∑ g, (idemOf A3.A.X).coeff g • (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)⁻¹ • (R.FW i).ρ g x = x ∧
      (∀ p : F.P0, (((R.FW i).chi p : D.what₂.LLˣ) : D.what₂.LL)⁻¹ • (R.FW i).ρ p x = (((F.ψ0 p)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • x) ∧
      ∀ k P, k ≤ D.R.r → IsSplitPl D.host P → P ∉ Sb' → Op k P x = ((eig (i.1 + 1) σ k P : ↥D.LL0) : D.what₂.LL) • x := by
  have h0 : sg0 D A3.A = D.what₂.embLL := sgAt_mk _ R.hv0
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hz0 : Y.mj.eW i y ≠ 0 := fun h => hy0 (readW_injective Y i (by
    show (R.HW i (sg0 D A3.A)).e (Y.mj.eW i y) = _
    rw [h, map_zero, map_zero]))
  have hzW : (R.HW i (sg0 D A3.A)).e (Y.mj.eW i y) ∈ R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) :=
    (Y.mj.eW_range i).le (LinearMap.mem_range_self _ y)
  obtain ⟨act, hact, hty, hpr⟩ : ∃ act : G → Module.End ℂ (MMap (R.MW i (sg0 D A3.A))),
      (∀ g x, (R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) ((R.FW i).ρ g x)) =
        sg0 D A3.A (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) • act g ((R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) x))) ∧
      (∀ p : F.P0, act p ((R.HW i (sg0 D A3.A)).e (Y.mj.eW i y)) =
        sg0 D A3.A (((F.ψ0 p)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • (R.HW i (sg0 D A3.A)).e (Y.mj.eW i y)) ∧
      ∑ g, sg0 D A3.A ((idemOf A3.A.X).coeff g) • act g ((R.HW i (sg0 D A3.A)).e (Y.mj.eW i y)) =
        (R.HW i (sg0 D A3.A)).e (Y.mj.eW i y) :=
    ⟨_, (hU i _).2.2, (GlobalTheory.LevelForms.mem_wat_iff R.toRealDat F.lv2 hU hW false i _ _).1 hzW⟩
  have hact' : ∀ g x, (R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A)
      ((((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)⁻¹ • (R.FW i).ρ g x)) =
      act g ((R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) x)) := fun g x => by
    rw [map_smulₛₗ, map_smul, hact, smul_smul, ← map_mul, inv_mul_cancel₀ (Units.ne_zero _), map_one, one_smul]
  have hex : ∀ t : {t : ℕ × PlE D.host // t.1 ≤ D.R.r ∧ IsSplitPl D.host t.2 ∧ t.2 ∉ Sb'}, ∃ α B, HkDat R Sb' i t.1.1 t.1.2 α B :=
    fun t => (exists_hkDat F hlev subset_rfl hlow i t.2.2.1 t.2.2.2 t.2.1).imp fun _ h => h.imp fun _ h => h.1
  choose α B hd using hex
  obtain ⟨x, hx0, hx⟩ := descent (ι := Unit ⊕ F.P0 ⊕ {t : ℕ × PlE D.host // t.1 ≤ D.R.r ∧ IsSplitPl D.host t.2 ∧ t.2 ∉ Sb'})
    (sg0 D A3.A) ((R.FW i).j (sg0 D A3.A)) ((hU i _).1 _ _ (Pi.basisFun D.what₂.LL _).linearIndependent) (hU i _).2.1
    (R.HW i (sg0 D A3.A)).e (hW i _).1
    (Sum.elim (fun _ => ∑ g, (idemOf A3.A.X).coeff g • (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)⁻¹ • (R.FW i).ρ g - 1)
      (Sum.elim (fun p => (((R.FW i).chi p : D.what₂.LLˣ) : D.what₂.LL)⁻¹ • (R.FW i).ρ p - (((F.ψ0 p)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • 1)
        fun t => Op t.1.1 t.1.2 - ((eig (i.1 + 1) σ t.1.1 t.1.2 : ↥D.LL0) : D.what₂.LL) • 1))
    (fun a => (Sum.elim (fun _ => ∑ g, sg0 D A3.A ((idemOf A3.A.X).coeff g) • act g - 1)
      (Sum.elim (fun p : F.P0 => act p - sg0 D A3.A (((F.ψ0 p)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • 1)
        fun t => hkNorm R i t.1.1 t.1.2 • heckeOn (R.MW i (sg0 D A3.A)) (B t) -
          sg0 D A3.A ((eig (i.1 + 1) σ t.1.1 t.1.2 : ↥D.LL0) : D.what₂.LL) • 1) a :
        Module.End ℂ (MMap (R.MW i (sg0 D A3.A)))) ∘ₗ (R.HW i (sg0 D A3.A)).e)
    (by
      rintro (_ | p | t) x
      · simp only [Sum.elim_inl, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
          Module.End.one_apply, map_sub, map_sum]
        congr 1
        exact Finset.sum_congr rfl fun g _ => by rw [map_smulₛₗ, map_smul, hact']
      · simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
          Module.End.one_apply, map_sub]
        rw [hact', map_smulₛₗ, map_smul]
      · simp only [Sum.elim_inr, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
          Module.End.one_apply, map_sub]
        rw [hOp _ _ _ _ (hd t), map_smulₛₗ, map_smul])
    hz0
    (by
      rintro (_ | p | t)
      · simp only [Sum.elim_inl, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
          Module.End.one_apply, sub_eq_zero]
        exact hpr
      · simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
          Module.End.one_apply, sub_eq_zero]
        exact hty p
      · simp only [Sum.elim_inr, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
          Module.End.one_apply, sub_eq_zero]
        have h1 := he i σ _ _ _ _ ⟨(hd t).split, fun h => (hd t).offS (hsub h), (hd t).odd, (hd t).le, (hd t).elt, (hd t).reps⟩
          hgood y hy
        rw [← h0] at h1
        exact h1)
  refine ⟨x, hx0, ?_, fun p => ?_, fun k P hk hs hP => ?_⟩
  · simpa only [Sum.elim_inl, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] using hx (Sum.inl ())
  · simpa only [Sum.elim_inl, Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] using hx (Sum.inr (Sum.inl p))
  · simpa only [Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] using hx (Sum.inr (Sum.inr ⟨(k, P), hk, hs, hP⟩))

variable {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}

set_option maxHeartbeats 1000000 in

theorem exists_goodL (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hlev : R.toLevCh.Is A3.A.μ0) (hU : R.toRealDat.LUnif)
    (hW : R.toRealDat.models_HW)
    (hidem : ∀ g, D.what₂.embLL ((idemOf A3.A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g))
    (hψ : RatSide.LvlPsi R F cG θ) {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} (he : EigAd Y Sb eig) (hsub : Sb ⊆ Sb')
    (hlow : Low D Sb') {S : RatDat D.ntw} (j : ℕ) (i : Fin D.R.m) (hj : i.1 + 1 = j) (fi : FormsIso (S.A j) (R.FW i))
    (geq : ∀ g : S.G, cG (R.eG (fi.eG g)) = S.eG g) (Op : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hOp : ∀ k P α Rr, HkDat R Sb' i k P α Rr → ∀ x, (R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) (fi.e (Op k P x))) =
      hkNorm R i k P • heckeOn (R.MW i (sg0 D A3.A)) Rr ((R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) (fi.e x))))
    {σ : D.what₂.FT} (hne : D.what₂.isot j σ ≠ ⊥) (hgood : D.nd.goodRow σ) :
    ∃ x ∈ goodL D S θ j, x ≠ 0 ∧
      ∀ k P, k ≤ D.R.r → IsSplitPl D.host P → P ∉ Sb' → Op k P x = ((eig j σ k P : ↥D.LL0) : D.what₂.LL) • x := by
  obtain ⟨x, hx0, h1, h2, h3⟩ := exists_rat Y hlev hU hW he hsub hlow i (hj ▸ hne) hgood
    (fun k P => fi.e.toLinearMap ∘ₗ Op k P ∘ₗ fi.e.symm.toLinearMap) fun k P α Rr hd x => by
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hOp k P α Rr hd (fi.e.symm x)
  obtain ⟨x, rfl⟩ := fi.e.surjective x
  have hact : ∀ g : G, fi.e (GlobalTheory.HeightCounting.actL D S j ((R.eG.trans cG) g) x) =
      (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)⁻¹ • (R.FW i).ρ g (fi.e x) := fun g => by
    obtain ⟨g, rfl⟩ := fi.eG.surjective g
    rw [MulEquiv.trans_apply, geq, GlobalTheory.HeightCounting.actL, MulEquiv.symm_apply_apply, LinearMap.smul_apply, map_smul, fi.rho, fi.chi]
  refine ⟨x, Submodule.mem_inf.2 ⟨Module.End.mem_eigenspace_iff.2 ?_, (Submodule.mem_iInf _).2 fun u =>
    Module.End.mem_eigenspace_iff.2 ?_⟩, fun h => hx0 (by rw [h, map_zero]), fun k P hk hs hP => ?_⟩
  · rw [one_smul, ← finsum_comp_equiv (R.eG.trans cG).toEquiv, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
    apply fi.e.injective
    rw [map_sum, ← h1]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hc : ((D.nexp.eLL0 ((R.eG.trans cG) g) : ↥D.LL0) : D.what₂.LL) = (idemOf A3.A.X).coeff g :=
      D.what₂.embLL.injective ((D.nStage_trivialCharacter_coeff_eq _).trans (hidem g).symm)
    rw [← hc, ← hact, ← map_smul]
    rfl
  · obtain ⟨u, hu⟩ := u
    obtain ⟨g, rfl⟩ := (R.eG.trans cG).surjective u
    apply fi.e.injective
    rw [map_smul, hψ.2 ⟨g, (hψ.1 g).2 hu⟩ hu, ← h2]
    exact hact g
  · apply fi.e.injective
    have := h3 k P hk hs hP
    rw [hj] at this
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, map_smul] using this

theorem eigOcc (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hlev : R.toLevCh.Is A3.A.μ0) (hU : R.toRealDat.LUnif)
    (hW : R.toRealDat.models_HW)
    (hidem : ∀ g, D.what₂.embLL ((idemOf A3.A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g))
    (hψ : RatSide.LvlPsi R F cG θ) {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} (he : EigAd Y Sb eig) (hsub : Sb ⊆ Sb')
    (hlow : Low D Sb') {kKs : Ks →+* ↥D.LL0} {hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j)}
    (hrd : RatSide.HeckeRd R cG kKs hk Sb' hL) : EigOcc D (ratDatR R cG kKs hk) θ hL Sb' eig := by
  intro j h1 h2 σ hne hgood
  obtain ⟨x, hx, hx0, h⟩ := exists_goodL Y hlev hU hW hidem hψ he hsub hlow (S := ratDatR R cG kKs hk) j (idxOf D j)
    (by simp only [idxOf]; omega)
    ⟨RingEquiv.refl _, fun _ => rfl, LinearEquiv.refl _ _, MulEquiv.refl _, fun _ => LinearIsometryEquiv.refl _ _,
      fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩ (fun _ => rfl) (hL j)
    (fun k P α Rr hd x => hrd j k P α Rr h1 h2 hd x) hne hgood
  exact ⟨x, hx, hx0, fun k P _ => h k P⟩

theorem eig_of_ratAd (hL : GlobalTheory.Published.LocalLanglandsGL) (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hlev : R.toLevCh.Is A3.A.μ0)
    (hU : R.toRealDat.LUnif) (hW : R.toRealDat.models_HW)
    (hidem : ∀ g, D.what₂.embLL ((idemOf A3.A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g))
    {kKs : Ks →+* ↥D.LL0} {hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x}
    {In : RatIn D (ratDatR R cG kKs hk)} (h : RatAd Y cG kKs hk In) (W : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : RowSide D)
    {sat : D.what₂.FT → PlE D.host → Multiset ℂ} (hrow : RowTrue hL D (typeR Y) (fun σ w => W.e w (Rw.locR σ w)) sat)
    (hsub : In.Sb ⊆ Sb') (hlow : Low D Sb') :
    EigTrue D R.C Rw Sb' In.eig ∧ EigOcc D (ratDatR R cG kKs hk) In.θ In.hL Sb' In.eig :=
  ⟨eigTrue hL Y hlev W Rw hrow h.eig hsub hlow, eigOcc Y hlev hU hW hidem ⟨h.lvl, h.psi⟩ h.eig hsub hlow
    fun j k P α Rr h1 h2 hd => h.hecke j k P α Rr h1 h2 ⟨hd.split, fun e => hd.offS (hsub e), hd.odd, hd.le, hd.elt, hd.reps⟩⟩

end Rows

section AtRows

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

end AtRows

end GlobalTheory.TwInputs.Eig

end
