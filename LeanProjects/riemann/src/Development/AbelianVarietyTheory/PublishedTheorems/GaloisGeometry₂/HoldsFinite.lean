import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne Polynomial TensorProduct Module
open GlobalTheory.Published.ParamAboveModel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published.CharWDModel

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw)

theorem holds_finite {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) {χ : HChar E} {k : ℕ} (hk : 0 < k)
    (hχ : χ.OrderDvd k) {μ : G E Ω →* (Qbar l)ˣ} (hμ : Continuous μ) (hL : IsLAdicOf art ι χ 0 μ)
    (hr : IsPstAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype))
    {ξ : (w.adicCompletion E)ˣ →* ℂˣ} (hξ : GlobalTheory.NPin.IsComp χ w ξ)
    {a : Weil h →* (w.adicCompletion E)ˣ} (ha' : IsLocalArtin h a) :
    wdAt P ι Bw h hj ((rk1 μ).comp (Dec (F := E) A).subtype) =
      WD.lpOfChar h (ξ.comp a) (ha'.smooth hξ.1) := by
  obtain rfl := eq_loc hξ
  have ho : IsOpen (μ.ker : Set (G E Ω)) :=
    isOpen_ker_of_pow μ hμ hk fun g => DFunLike.congr_fun (hL.pow_eq_one ha.quot.surjective hχ) g
  have ho2 : IsOpen {g : GK Bw.Kw | μ (Bw.e.symm g : Dec (F := E) A) = 1} :=
    ho.preimage (continuous_subtype_val.comp Bw.e_symm_cont)
  obtain ⟨U, hU, hU'⟩ := isOpen_induced_iff.1 ho2
  have h1 : (1 : GQ l) ∈ U := by
    have : (1 : GK Bw.Kw) ∈ Subtype.val ⁻¹' U := by rw [hU']; simp
    exact this
  obtain ⟨K', hK1, hK2⟩ := (krullTopology_mem_nhds_one_iff _ _ U).1 (hU.mem_nhds h1)
  have := nontrivial_B P
  refine eq_lpOfChar h _ (Test.lpDim_wdAt P ι Bw h hj _) _ _ fun σ => ?_
  have key := mem_eig_wdAt P ι Bw h hj μ hr 1 one_ne_zero 1 one_ne_zero (by simp) (fun _ => 1) (by simp) (by simp)
    ⟨K', hK1⟩ (fun g hg => by
      have : Bw.e g ∈ Subtype.val ⁻¹' U := hK2 hg
      rw [hU'] at this
      have h2 : μ g = 1 := by simpa using this
      simp [h2]) σ
  rw [hL.loc_away (Or.inr rfl) _ _ (ha'.glob art ha σ)] at key
  simpa using key

theorem holds_abs {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) {n : (E →+* ℂ) → ℤ}
    {μ : G E Ω →* (Qbar l)ˣ} (hμ : Continuous μ) (hL : IsLAdicOf art ι (Model.absPow E (1 : ℕ)) n μ)
    (hr : IsPstAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype))
    {ξ : (w.adicCompletion E)ˣ →* ℂˣ} (hξ : GlobalTheory.NPin.IsComp (Model.absPow E (1 : ℕ)) w ξ)
    {a : Weil h →* (w.adicCompletion E)ˣ} (ha' : IsLocalArtin h a) :
    wdAt P ι Bw h hj ((rk1 μ).comp (Dec (F := E) A).subtype) =
      WD.lpOfChar h (ξ.comp a) (ha'.smooth hξ.1) := by
  obtain rfl := eq_loc hξ
  have hμ' := CharAboveModel.eq_cyc_pow ha hμ hL
  rw [pow_one] at hμ'
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have := nontrivial_B P
  have hcyc : ∀ g : Dec (F := E) A, (μ g : Om l) = algebraMap _ _ (P.χQ (Bw.e g) : ℚ_[l]) := fun g => by
    rw [GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc P Bw.j (g : G E Ω) (Bw.e g : GQ l) (Bw.e_comm g), hμ', cyc_eq_map_cycZ]
    rfl
  refine eq_lpOfChar h _ (Test.lpDim_wdAt P ι Bw h hj _) _ _ fun σ => ?_
  have key := mem_eig_wdAt P ι Bw h hj μ hr (tInv P) (fun h0 => by simpa [h0] using tInv_mul P) (l : ℚ_[l])⁻¹
    (inv_ne_zero hl) (by rw [eq_inv_smul_iff₀ hl, smul_phiB_tInv]) (fun g => P.χQ g) (fun g => Units.ne_zero _)
    (smul_actQ_tInv P) Bw.Kw (fun g _ => hcyc g) σ
  have h2 : (μ σ : Om l) = algebraMap _ _ (P.χQ (weilToGK Bw h σ) : ℚ_[l]) := hcyc ⟨σ, Weil_le_Dec h σ.2⟩
  rw [h2, ← map_mul, mul_inv_cancel_left₀ (Units.ne_zero _), inv_zpow', neg_neg, map_zpow₀, map_zpow₀, map_natCast,
    map_natCast, alpha, zpow_mul, zpow_natCast, ← Nat.cast_pow, ← normV_eq_pow (hj.mem_placesOver h)] at key
  convert key using 1
  have hu := (Model.absPow_isAbsPow E (1 : ℕ)).1 w
  have hval := (Model.absPow_isAbsPow E (1 : ℕ)).2.1 w
  set χ := Model.absPow E (1 : ℕ)
  have e1 : ∀ x, χ.loc w x = χ.val w ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x := fun x => by
    have h2 := unif_spec w
    have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
    have h1 : IsUnitAt w (x * (atFin w (unif w) ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
        map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, GlobalTheory.SmGL.SphCompletion.ord_completion]
      simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
      rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
    have h3 := hu _ h1
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
    exact h3
  rw [MonoidHom.comp_apply, e1, ha'.ord_eq, Units.val_zpow_eq_zpow_val, hval]
  simp [Complex.cpow_neg, normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

omit P Bw h hj in

theorem hypotheses_met (hA : GlobalArtinReciprocity) (hL : LocalLanglandsGL) (hw : w ∈ placesOver E l) :
    ∃ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) ∧ ∃ art : Ideles E →* Gab E Ω, IsGlobalArtin art ∧
      ∃ μ : G E Ω →* (Qbar l)ˣ, IsAlgPos (Model.absPow E (1 : ℕ)) (fun _ => ((1 : ℕ) : ℤ)) ∧ Continuous μ ∧
      IsLAdicOf art ι (Model.absPow E (1 : ℕ)) (fun _ => ((1 : ℕ) : ℤ)) μ ∧
      ∃ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (LL : FinExt l)
        (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL LL)), GlobalTheory.Pst.Induces Bw ∧
        (∃ ξ, GlobalTheory.NPin.IsComp (Model.absPow E (1 : ℕ)) w ξ) ∧ ∃ a, IsLocalArtin h a := by
  obtain ⟨P, AI, hT, art, ha, μ, h1, h2, h3, A, h, LL, Bw, hj, hξ, rc, a, ha', -⟩ :=
    ParamAboveModel.hypotheses_met (Ω := Ω) ι hA hL hw
  exact ⟨P, AI, hT, art, ha, μ, h1, h2, h3, A, h, LL, Bw, hj, hξ, a, ha'⟩

end GlobalTheory.Published.CharWDModel

end
