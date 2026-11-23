import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.ContOfFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdExtChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocCharDR

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open GlobalTheory.Pst GlobalTheory.TripleGal Module
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
namespace UpperTheory.V.Z.Ord.OrdinaryPolarizedFromFlag
section Tri
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
private theorem tri_dR (T : LocTied l P AI) (Bw : LocBridge l E Ω (Dec (F := E) A) O) (LL : FinExt l) (n : ℕ) :
    ∀ (r : ↥(Dec (F := E) A) →* GL (Fin n) ↥LL.1) (c : Fin n → ↥(Dec (F := E) A) →* GL (Fin 1) ↥LL.1),
    (∀ g i j, j < i → (r g).val i j = 0) → (∀ g i, (r g).val i i = (c i g).val 0 0) →
    Bw.IsdRE P LL r → ∀ i, Bw.IsdRE P LL (c i) := by
  induction n with
  | zero => exact fun _ _ _ _ _ i => i.elim0
  | succ n ih =>
    intro r c hr hc hd
    obtain ⟨r', hr'⟩ := UpperTheory.V.Loc.PstExact.exists_tail r hr
    obtain ⟨h1, h2⟩ := UpperTheory.V.Loc.PstExact.exact_line (k := ↥LL.1) (n := n)
    have h3 := LinearMap.funLeft_surjective_of_injective ↥LL.1 ↥LL.1 _ (Fin.succ_injective n)
    have hi : ∀ g v, ((LinearMap.single ↥LL.1 (fun _ : Fin (n + 1) => ↥LL.1) 0).comp
        (LinearMap.proj (0 : Fin 1) : (Fin 1 → ↥LL.1) →ₗ[↥LL.1] ↥LL.1)) (Bw.repE LL (c 0) g v) =
        Bw.repE LL r g (((LinearMap.single ↥LL.1 (fun _ : Fin (n + 1) => ↥LL.1) 0).comp
        (LinearMap.proj (0 : Fin 1) : (Fin 1 → ↥LL.1) →ₗ[↥LL.1] ↥LL.1)) v) := fun g v => by
      rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [Matrix.mulVec, dotProduct, hc, Fin.sum_univ_succ]
      · simp [Matrix.mulVec, dotProduct, hr _ j.succ 0 (Fin.succ_pos j), Fin.sum_univ_succ]
    have hp : ∀ g v, LinearMap.funLeft ↥LL.1 ↥LL.1 (Fin.succ : Fin n → Fin (n + 1)) (Bw.repE LL r g v) =
        Bw.repE LL r' g (LinearMap.funLeft ↥LL.1 ↥LL.1 Fin.succ v) := fun g v => by
      rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply]
      funext i
      simp [LinearMap.funLeft_apply, Matrix.mulVec, dotProduct, hr _ i.succ 0 (Fin.succ_pos i), Fin.sum_univ_succ, hr']
    obtain ⟨d₀, d₂, -⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l P AI T Bw.Kw LL _ _ _ _ _ _ _ _ hi hp h1 h3
      h2.linearMap_ker_eq.symm (by rw [IsDR, finrank_fin_fun]; exact hd)
    rw [IsDR, finrank_fin_fun] at d₀ d₂
    have hq := ih r' (fun i => c i.succ) (fun g i j hij => by rw [hr', hr g _ _ (Fin.succ_lt_succ_iff.2 hij)])
      (fun g i => by rw [hr', hc]) d₂
    exact fun i => Fin.cases d₀ hq i
private theorem flag_jumps (T : LocTied l P AI) (Bw : LocBridge l E Ω (Dec (F := E) A) O) {n : ℕ}
    (r : ↥(Dec (F := E) A) →* GL (Fin n) (Om l)) (c : Fin n → ↥(Dec (F := E) A) →* GL (Fin 1) (Om l))
    (M : GL (Fin n) (Om l)) (hr : ∀ g i j, j < i → (M * r g * M⁻¹).val i j = 0)
    (hc : ∀ g i, (M * r g * M⁻¹).val i i = (c i g).val 0 0) (τ : E →+* Om l) (J : Multiset ℤ)
    (hJ : IsJumpsAt P Bw r τ J) (i : Fin n) : ∃ a, IsJumpsAt P Bw (c i) τ {a} := by
  let r' : ↥(Dec (F := E) A) →* GL (Fin n) (Om l) := (MulAut.conj M).toMonoidHom.comp r
  have hr' : ∀ g, r' g = M * r g * M⁻¹ := fun _ => rfl
  obtain ⟨L, r₂, hm, hd, τ₂, hτ, -⟩ := (GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw n r r' M hr').2.2.2 τ J hJ
  obtain ⟨c₂, hm', hc₂⟩ := UpperTheory.V.Loc.PstExact.exists_diag Bw (r := r') hc hm
  have htri : ∀ g i j, j < i → (r₂ g).val i j = 0 := fun g i j hij => Subtype.ext (by
    have := hr g i j hij
    rw [← hr', ← hm.2] at this
    exact this)
  have hdr := tri_dR T Bw L n r₂ c₂ htri hc₂ hd i
  have hdr' : IsDR (P.PD Bw.Kw) (Bw.repE L (c₂ i)) := by
    rw [IsDR, finrank_fin_fun]
    exact hdr
  obtain ⟨hfin, -, hrk⟩ := (GlobalTheory.Per.Components.components_finrank l P AI T _ L _ (Bw.repE L (c₂ i))).1 τ₂
  obtain ⟨J', h1, h2⟩ := @GlobalTheory.HtCardProof.exists_count _ _ _ _ _ T _ _ ((c₂ i).comp Bw.e.symm.toMonoidHom) τ₂ hfin
  obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 (h1.trans ((hrk hdr').trans (finrank_fin_fun _)))
  exact ⟨a, L, c₂ i, hm' i, hdr, τ₂, hτ, h2⟩
end Tri
section Loc
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}
private theorem emb_norm (j : W.Emb l w) (x : 𝓞 L) : ‖j.1.comp (algebraMap L _) (x : L)‖ < 1 ↔ x ∈ w.asIdeal := by
  have h1 : w.asIdeal ≤ (GlobalTheory.EvExtend.placeOf (j.1.comp (algebraMap L _))).asIdeal := fun y hy => by
    rw [GlobalTheory.EvExtend.mem_placeOf, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
    have h2 : Valued.v (algebraMap L (w.adicCompletion L) (y : L)) < 1 := by
      rw [show Valued.v (algebraMap L (w.adicCompletion L) (y : L)) = w.valuation L (algebraMap (𝓞 L) L y) from
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 hy
    have h3 := (j.2.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one h2)
    simpa [Function.comp_def] using h3
  rw [w.isMaximal.eq_of_le (GlobalTheory.EvExtend.placeOf _).isPrime.ne_top h1, GlobalTheory.EvExtend.mem_placeOf]
private theorem cont_of_flag {n : ℕ} {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {r : Γ →* GL (Fin n) (Qbar l)}
    (hr : Continuous r) {ψ : Fin n → Γ →* (Qbar l)ˣ} (hf : W.HasFlag r ψ) (i : Fin n) : Continuous (ψ i) := by
  obtain ⟨g, hg⟩ := hf
  have h1 : Continuous fun s => (ψ i s : Qbar l) :=
    ((Units.continuous_val.comp ((continuous_const.mul hr).mul continuous_const)).matrix_elem i i).congr fun s => (hg s).2 i
  exact Units.continuous_iff.2 ⟨h1, (h1.comp continuous_inv).congr fun s => by simp⟩
private theorem ord_of_flag (N : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (ι : Qbar l ≃+* ℂ) (h : IsPlaceOver A w) (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal)
    {a : Weil h →* (w.adicCompletion L)ˣ} (ha : IsLocalArtin h a) {n : ℕ} {r : ↥(Dec (F := L) A) →* GL (Fin n) (Qbar l)} (hr : Continuous r)
    {ψ : Fin n → ↥(Dec (F := L) A) →* (Qbar l)ˣ} (hf : W.HasFlag r ψ) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l L Ω (Dec (F := L) A) O) (hj : Induces Bw) (HT : (L →+* Qbar l) → Multiset ℤ)
    (hJ : ∀ (τ : L →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
      IsJumpsAt (Loc.PP l) Bw r τ (HT τ)) :
    ∃ (hh : Fin n → (L →+* Qbar l) → ℤ) (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ), ∀ i, OrdChar ι a (ω i) (hh i) (ψ i) := by
  classical
  have art := N.aut.art
  have hD : GlobalTheory.Published.HeckeLAdicCharacterDeRham := by
    intro E Ω _ _ _ _ _ l _ P AI ht ι art ha χ n μ h1 h2 h3 w A hA O _ _ _ Bw hB
    have := N.aut.chA E Ω l P AI ht ι art ha χ n μ h1 h2 h3 w A hA O Bw hB
    exact ⟨this.1, this.2.2.2⟩
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨M, hM⟩ := hf
  have hf' : W.HasFlag r ψ := ⟨M, hM⟩
  have hone : ∀ (i : Fin n) (j : W.Emb l w), ∃ b, IsJumpsAt (Loc.PP l) Bw (rk1 (ψ i)) (j.1.comp (algebraMap L _)) {b} := fun i j => by
    obtain ⟨τ', hτ'⟩ := GlobalTheory.CharAboveRead.exists_isInduced_of _ w hw (emb_norm j) A h O Bw hj
    exact flag_jumps T Bw r (fun i => rk1 (ψ i)) M (fun g => (hM g).1)
      (fun g i => ((hM g).2 i).trans (by simp [rk1])) _ _ (hJ _ _ τ' hτ') i
  let hh : Fin n → (L →+* Qbar l) → ℤ := fun i τ =>
    if hx : ∃ b, IsJumpsAt (Loc.PP l) Bw (rk1 (ψ i)) τ {b} then hx.choose else 0
  have hs : ∀ (i : Fin n) (j : W.Emb l w),
      IsJumpsAt (Loc.PP l) Bw (rk1 (ψ i)) (j.1.comp (algebraMap L _)) {hh i (j.1.comp (algebraMap L _))} := fun i j => by
    simp only [hh, dif_pos (hone i j)]
    exact (hone i j).choose_spec
  have hc := cont_of_flag hr hf'
  have hla := fun i => UpperTheory.V.Loc.laConv art art.heckeLAdicCharacter hD N.aut.berger h (ψ i) (hc i) O Bw hj
    (fun j => hh i (j.1.comp (algebraMap L _))) (hs i)
  choose ω hω using fun i => (UpperTheory.V.Loc.ordCharIff art h ι a ha (hh i) (ψ i)).1.2 ⟨hc i, hla i⟩
  exact ⟨hh, ω, hω⟩
private theorem pol_of_flag (N : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (ι : Qbar l ≃+* ℂ) (h : IsPlaceOver A w) (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal)
    {a : Weil h →* (w.adicCompletion L)ˣ} (ha : IsLocalArtin h a) {n : ℕ} {r : ↥(Dec (F := L) A) →* GL (Fin n) (Qbar l)}
    {ψ : Fin n → ↥(Dec (F := L) A) →* (Qbar l)ˣ} (hf : W.HasFlag r ψ) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l L Ω (Dec (F := L) A) O) (hj : Induces Bw) (hp : IsPstAt (Loc.PP l) Bw r)
    {hh : Fin n → (L →+* Qbar l) → ℤ} {ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ} (hω : ∀ i, OrdChar ι a (ω i) (hh i) (ψ i)) (s : Weil h) :
    (wdAt (Loc.PP l) ι Bw h hj r).charPol s = ∏ i, (X - C ((ω i (a s) : ℂˣ) : ℂ)) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  have hc := fun i => (_root_.UpperTheory.V.Loc.hecke_char_de_rham_of_local_artin_above_l N h hw ι a ha (ω i) (hh i) (ψ i) (hω i)).1 O Bw hj
  obtain ⟨-, F₂⟩ := UpperTheory.V.Loc.PstExact.flag T ι Bw h hj _ (fun i => rk1 (ψ i)) M
    (fun g => (hM g).1) (fun g i => ((hM g).2 i).trans (by simp [rk1]))
  rw [(F₂ hp).2 s]
  exact Finset.prod_congr rfl fun i _ => (hc i).2.2 s
end Loc
private theorem mem_of_prod {M : Type} [Monoid M] {n : ℕ} (f g : Fin n → (M →* ℂ))
    (h : ∀ x, ∏ j, (X - C (f j x)) = ∏ j, (X - C (g j x))) (j : Fin n) : ∃ i, g i = f j := by
  have hc := GlobalTheory.CharDeg.card_fiber_eq_of_sum_eq f g (fun x => GlobalTheory.CharDeg.sum_eq_of_prod_eq _ _ (h x)) (f j)
  haveI : Nonempty {i // f i = f j} := ⟨⟨j, rfl⟩⟩
  haveI : Finite {i // g i = f j} := inferInstance
  have hpos : 0 < Nat.card {i // g i = f j} := hc ▸ Nat.card_pos
  obtain ⟨⟨i, hi⟩⟩ := (Nat.card_pos_iff.1 hpos).1
  exact ⟨i, hi⟩
end UpperTheory.V.Z.Ord.OrdinaryPolarizedFromFlag
open UpperTheory.V.Z.Ord.OrdinaryPolarizedFromFlag GroundTheory.Global.SemiLocal UpperTheory.V.Z.Win UpperTheory.V.Z.Gam UpperTheory.Zero.LLC UpperTheory.V.Af in
theorem UpperTheory.V.Z.Ord.thruL_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → Win.PlainRec → Win.Thru true := by
  intro Pr hPR hRow K L Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n hn r hc hIne P hreg hpol hatt v hv hpot w t hwin s hs ζ hζ hmem
  obtain ⟨σ, hσ, hsup⟩ := hs
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := K) L
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed K, inferInstance⟩
  haveI : CharZero (w.1.adicCompletion L) := charZero_of_injective_algebraMap (algebraMap L _).injective
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w.1
  have hAv : IsPlaceOver A v := by
    have e : w.1.under (𝓞 K) = v := by
      ext1
      exact (Ideal.over_def w.1.asIdeal v.asIdeal).symm
    exact e ▸ GlobalTheory.AboveL.SatBC.isPlaceOver_under hA
  have hlv : ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := hv.2 rfl
  have hlw : ((l : ℕ) : 𝓞 L) ∈ w.1.asIdeal := by
    rw [Ideal.over_def w.1.asIdeal v.asIdeal, Ideal.under, Ideal.mem_comap] at hlv
    simpa using hlv
  set rL : G L Ω →* GL (Fin n) (Qbar l) := r.comp (AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω) with hrL
  have hcL : Continuous rL := hc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom K L Ω)
  obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists L Ω A w.1 hA
  obtain ⟨HT, -, hC⟩ := UpperTheory.V.Z.Win.compatTOf hRow hPR L Ω l ι n (by omega) rL P hcL hreg hpol hatt
  obtain ⟨hPT, hTor, hMono⟩ := hPR L Ω A w.1 hA rc hrc n P t hwin σ hσ
  obtain ⟨O, _, _, _, Bw, hj⟩ := Af.exists_bridge (l := l) hA hlw
  have hHT := (hC w.1 σ hσ).2 hPT A hA O Bw hj
  obtain ⟨hpst, hwd⟩ := ((hC w.1 σ hσ).1 A hA rc hrc).2 O Bw hj ⟨hTor, hMono⟩
  obtain ⟨κ, hκ, -⟩ := hpot rfl A hAv
  let res : ↥(Dec (F := L) A) →* ↥(Dec (F := K) A) :=
    ((AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω).comp (Dec (F := L) A).subtype).codRestrict _ fun g => g.2
  let ψ : Fin n → ↥(Dec (F := L) A) →* (Qbar l)ˣ := fun i => (κ i).comp res
  have hκf : W.HasFlag (r.comp (Dec (F := K) A).subtype) κ := hκ
  have hfL : W.HasFlag (rL.comp (Dec (F := L) A).subtype) ψ := by
    obtain ⟨M, hM⟩ := hκf
    exact ⟨M, fun g => hM (res g)⟩
  have hcD : Continuous (rL.comp (Dec (F := L) A).subtype) := hcL.comp continuous_subtype_val
  have hcK : Continuous (r.comp (Dec (F := K) A).subtype) := hc.comp continuous_subtype_val
  obtain ⟨a, ha, hLaws⟩ := hrc
  obtain ⟨hh, ω, hω⟩ := ord_of_flag Pr.litN ι hA hlw ha hcD hfL Bw hj HT hHT.2
  have hpolW : ∀ g : Weil hA, (rc (algNorm σ)).charPol g = ∏ i, (X - C ((ω i (a g) : ℂˣ) : ℂ)) := fun g => by
    rw [← hwd]
    exact pol_of_flag Pr.litN ι hA hlw ha hfL Bw hj hpst hω g
  obtain ⟨ξ, hξ, hsupx, -⟩ := GlobalTheory.RoadU.plainTor_exists_chars (w.1.adicCompletion L) (IrrGL.of σ.ρ σ.smooth σ.irred) hPT
  let c : ℂ := (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)
  let ξ' : Fin n → ((w.1.adicCompletion L)ˣ →* ℂˣ) := fun j => ξ j * absPow _ c
  have hξ' : ∀ j, IsSmoothChar (ξ' j) := fun j => (hξ j).mul (GlobalTheory.LocGL.isSmoothChar_absPow _)
  have hsup' : HasSupport (algNorm σ).rep (GlobalTheory.RoadU.chars ξ' hξ') :=
    (GlobalTheory.RoadU.TwistSupp.supp_nu_chars (w.1.adicCompletion L) (IrrGL.of σ.ρ σ.smooth σ.irred) n ξ ξ' hξ hξ' c fun _ => rfl).1.1 hsupx
  have hpolC : ∀ g : Weil hA, (rc (algNorm σ)).charPol g = ∏ j, (X - C ((ξ' j (a g) : ℂˣ) : ℂ)) := fun g =>
    charPol_of_chars hLaws _ ξ' hξ' hsup' g
  obtain ⟨hG, hZ⟩ := GlobalTheory.geometricLemma_and_zelevinskyPolynomialRing
  have hse : s = GlobalTheory.RoadU.chars ξ hξ := GlobalTheory.LocGL.SupportUnique.hasSupport_unique hG GlobalTheory.Laid.bzfin_holds hZ _
    (IrrGL.of σ.ρ σ.smooth σ.irred) _ _ (hsup.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)) hsupx
  obtain ⟨j, -, hj'⟩ := Multiset.mem_map.1 (hse ▸ hmem)
  have hζj : ξ j = ζ := IrrGL.ofChar_inj.1 hj'
  let f : Fin n → (Weil hA →* ℂ) := fun j => (Units.coeHom ℂ).comp ((ξ' j).comp a)
  let g : Fin n → (Weil hA →* ℂ) := fun i => (Units.coeHom ℂ).comp ((ω i).comp a)
  obtain ⟨i, hi⟩ := mem_of_prod f g (fun x => (hpolC x).symm.trans (hpolW x)) j
  obtain ⟨χ, hχ, hu⟩ := _root_.UpperTheory.V.Z.Ord.ext_character_of_literal_automorphy_n Pr.litN K L Ω l ι v w A hA hlv a ha (κ i) (ψ i)
    (cont_of_flag hcK hκf i) (fun x y e => congrArg (κ i) (Subtype.ext e.symm)) (ω i) (hh i) (hω i)
  refine ⟨χ, hχ, fun x hx1 => ?_⟩
  have e := hu x hx1
  obtain ⟨y, rfl⟩ := ha.surj x
  have e1 : ω i (a y) = ξ' j (a y) := Units.ext (DFunLike.congr_fun hi y)
  have e' : ξ' j (a y) = ξ j (a y) := by
    simp only [ξ', MonoidHom.mul_apply, isUnram_absPow _ c _ hx1, mul_one]
  rw [MonoidHom.mul_apply] at e ⊢
  rw [← hζj, ← e', ← e1]
  exact e
end
end
