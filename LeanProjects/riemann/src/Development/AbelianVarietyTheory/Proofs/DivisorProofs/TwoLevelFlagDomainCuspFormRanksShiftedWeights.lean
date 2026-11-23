import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyRealDegreeAndChartDimensionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormIndependentTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerRankCuspFormsDetWeightOneComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroBoundedSectionShiftedWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIndependentBoundedSectionsShiftedWeightLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoBinomialRatioBoundsStatement

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShareRanks

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem li_iff {α : Type} {D : Set α} {m : ℕ} (f : Fin m → α → ℂ) :
    LinearIndependent ℂ (fun q (x : D) => f q x.1) ↔
      ∀ u : Fin m → ℂ, (∀ x ∈ D, ∑ q, u q * f q x = 0) → u = 0 := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h u hu
    funext q
    refine h u ?_ q
    funext x
    simp [Finset.sum_apply, hu x.1 x.2]
  · intro h u hu q
    have : u = 0 := h u fun x hx => by
      have := congrFun hu ⟨x, hx⟩
      simpa [Finset.sum_apply] using this
    simp [this]

def UpC (X : Data E r) {Ψ : Finset (E →+* ℂ)} (hΨ : X.Ψ = Ψ) (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (la : Wt Ψ r) (N : ℕ) : Prop :=
  ∀ (m : ℕ) (f : Fin m → Frame Ψ r → ℂ), (∀ q, (fun y => f q (castFrame hΨ y)) ∈ X.SS (castWt hΨ la)) →
    LinearIndependent ℂ (fun q (x : GG Ψ G p0) => f q x.1) → m ≤ N

def LowC (X : Data E r) {Ψ : Finset (E →+* ℂ)} (hΨ : X.Ψ = Ψ) (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (la : Wt Ψ r) (N : ℕ) : Prop :=
  ∃ g : Fin N → Frame Ψ r → ℂ, (∀ q, (fun y => g q (castFrame hΨ y)) ∈ X.SS (castWt hΨ la)) ∧
    LinearIndependent ℂ (fun q (x : GG Ψ G p0) => g q x.1)

theorem span_upper {C D : Type} [Finite C] (S : Set (C → D → ℂ)) (N : C → ℕ)
    (hup : ∀ c (m : ℕ) (g : Fin m → C → D → ℂ), (∀ q, g q ∈ S) → LinearIndependent ℂ (fun q => g q c) → m ≤ N c) :
    Module.Finite ℂ (Submodule.span ℂ S) ∧ finrank ℂ (Submodule.span ℂ S) ≤ ∑ᶠ c, N c := by
  classical
  have : Fintype C := Fintype.ofFinite C
  let Sc : C → Set (D → ℂ) := fun c => (fun g => g c) '' S
  have hc : ∀ c, Module.Finite ℂ (Submodule.span ℂ (Sc c)) ∧ finrank ℂ (Submodule.span ℂ (Sc c)) ≤ N c := by
    intro c
    obtain ⟨b, hbS, hbsp, hbli⟩ := exists_linearIndependent ℂ (Sc c)
    have hcard : ∀ t : Finset (D → ℂ), (↑t : Set (D → ℂ)) ⊆ b → t.card ≤ N c := by
      intro t ht
      have hmem : ∀ v ∈ t, ∃ g ∈ S, g c = v := fun v hv => hbS (ht hv)
      choose g hgS hgc using hmem
      let e := t.equivFin
      let gg : Fin t.card → C → D → ℂ := fun q => g (e.symm q).1 (e.symm q).2
      have hli : LinearIndependent ℂ (fun q => gg q c) := by
        have h1 : LinearIndependent ℂ (fun v : b => (v : D → ℂ)) := hbli
        have h2 : LinearIndependent ℂ (fun v : t => (v : D → ℂ)) :=
          h1.comp (fun v : t => (⟨v.1, ht v.2⟩ : b)) (fun v w h => Subtype.ext (by simpa using congrArg Subtype.val h))
        have h3 := h2.comp e.symm e.symm.injective
        convert h3 using 1
        funext q
        simp [gg, hgc]
      exact hup c _ gg (fun q => hgS _ _) hli
    have hfin : b.Finite := by
      by_contra hinf
      obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (N c + 1)
      have := hcard t ht
      omega
    have hfs := hfin.fintype
    have hsp : Submodule.span ℂ (Sc c) = Submodule.span ℂ b := hbsp.symm
    rw [hsp]
    refine ⟨FiniteDimensional.span_of_finite ℂ hfin, ?_⟩
    rw [finrank_span_set_eq_card hbli]
    have := hcard hfin.toFinset (by simp)
    simpa [Set.toFinset_card] using this
  have : ∀ c, Module.Finite ℂ (Submodule.span ℂ (Sc c)) := fun c => (hc c).1
  let φ : Submodule.span ℂ S →ₗ[ℂ] ((c : C) → Submodule.span ℂ (Sc c)) :=
    LinearMap.pi fun c => ((LinearMap.proj c).comp (Submodule.span ℂ S).subtype).codRestrict _ (by
      intro v
      have hv := v.2
      refine Submodule.span_induction (p := fun w _ => w c ∈ Submodule.span ℂ (Sc c)) ?_ ?_ ?_ ?_ hv
      · intro w hw
        exact Submodule.subset_span ⟨w, hw, rfl⟩
      · simp
      · intro x y _ _ hx hy
        simpa using Submodule.add_mem _ hx hy
      · intro a x _ hx
        simpa using Submodule.smul_mem _ a hx)
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply Subtype.ext
    funext c
    have h1 : ((φ v c : Submodule.span ℂ (Sc c)) : D → ℂ) = 0 := by rw [hv]; rfl
    exact h1
  refine ⟨Module.Finite.of_injective φ hinj, ?_⟩
  calc finrank ℂ (Submodule.span ℂ S) ≤ finrank ℂ ((c : C) → Submodule.span ℂ (Sc c)) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = ∑ c, finrank ℂ (Submodule.span ℂ (Sc c)) := Module.finrank_pi_fintype ℂ
    _ ≤ ∑ c, N c := Finset.sum_le_sum fun c _ => (hc c).2
    _ = ∑ᶠ c, N c := (finsum_eq_sum_of_fintype _).symm

theorem lower_of_comps {C D : Type} [Finite C] (W : Submodule ℂ (C → D → ℂ)) [Module.Finite ℂ W] (N : C → ℕ)
    (hlow : ∀ c, ∃ g : Fin (N c) → C → D → ℂ, (∀ q, g q ∈ W) ∧ (∀ q, ∀ c' ≠ c, g q c' = 0) ∧
      LinearIndependent ℂ (fun q => g q c)) :
    ∑ᶠ c, N c ≤ finrank ℂ W := by
  classical
  have : Fintype C := Fintype.ofFinite C
  choose g hgW hg0 hgli using hlow
  let G : (Σ c, Fin (N c)) → W := fun i => ⟨g i.1 i.2, hgW i.1 i.2⟩
  have hli : LinearIndependent ℂ G := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    obtain ⟨c, q⟩ := i
    have h1 := congrArg (fun v : W => (v : C → D → ℂ) c) ha
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, G,
      Submodule.coe_zero, Pi.zero_apply] at h1
    rw [Fintype.sum_sigma] at h1
    rw [Finset.sum_eq_single c (fun c' _ hc' => by simp [hg0 _ _ c (Ne.symm hc')]) (by simp)] at h1
    exact Fintype.linearIndependent_iff.1 (hgli c) (fun q => a ⟨c, q⟩) h1 q
  have := hli.fintype_card_le_finrank
  rw [finsum_eq_sum_of_fintype]
  simpa [Fintype.card_sigma] using this

theorem indep_mul (X : Data E r) {la : Wt X.Ψ r} {w : Frame X.Ψ r → ℂ} (hw : DifferentiableOn ℂ w X.dom)
    (hw0 : ∃ x ∈ X.dom, w x ≠ 0) {m : ℕ} {f : Fin m → Frame X.Ψ r → ℂ} (hf : ∀ q, X.IsBddSec la (f q))
    (hi : ∀ u : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, u q * f q x = 0) → u = 0) :
    ∀ u : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, u q * (f q * w) x = 0) → u = 0 := by
  intro u hu
  apply hi u
  obtain ⟨x0, hx0, hw0⟩ := hw0
  have hg := (GlobalTheory.UpperModel.isBddSec_sum X hf u).1.1
  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero (FourierCoefficientDomain.isOpen_dom X)
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected hw hg ?_ hx0 hw0
  intro y hy
  rw [Finset.mul_sum, ← hu y hy]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.mul_apply]
  ring

theorem mul_mem (X : Data E r) {la la' mu : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la)
    (hQ : X.IsBddSec la' Q) (h : la + la' = mu) : P * Q ∈ X.SS mu := by
  have := (ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds r X la la' 0).2.1 P hP Q hQ
  rw [h] at this
  exact this

theorem compX (X : DataX E r) (Xa : ArchInM X.toData) (Fl : FlatM X.toData Xa) (hm : GlobalTheory.Shares.Margins X.toData Xa)
    (h0 : 0 < X.p0) (h1 : X.p0 < r) (hg1 : GapsGe X.p0 Xa.L 1) (hg2 : PairGe Xa.L (1.9 * Xa.T))
    (hg3 : GapsGe X.p0 (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 0)
    (hg4 : PairGe (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 1) (s : ℕ) (hs : Even s) (hsT : s ≤ Xa.T)
    (u : Frame X.Ψ r → ℂ) (hu : u ∈ X.SS (deMul X.Ψ r X.p0 s)) (hu0 : ∃ x ∈ X.dom, u x ≠ 0) :
    (∀ (m : ℕ) (f : Fin m → Frame X.Ψ r → ℂ), (∀ q, f q ∈ X.SS (Xa.Fp + Xa.T • Xa.L)) →
      (∀ a : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, a q * f q x = 0) → a = 0) →
      m ≤ Fl.δ * (Xa.T + 2 * nd X.toData + 6).choose (nd X.toData)) ∧
    (∀ (m : ℕ) (f : Fin m → Frame X.Ψ r → ℂ), (∀ q, f q ∈ X.SS (Xa.Fp + Xa.T • Xa.L - deMul X.Ψ r X.p0 s)) →
      (∀ a : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, a q * f q x = 0) → a = 0) →
      m ≤ Fl.δ * (Xa.T + 2 * nd X.toData + 6).choose (nd X.toData)) ∧
    (∀ (m : ℕ) (f : Fin m → Frame X.Ψ r → ℂ), (∀ q, f q ∈ X.SS (Xa.Fp + Xa.T • Xa.L + 2 • deMul X.Ψ r X.p0 s)) →
      (∀ a : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, a q * f q x = 0) → a = 0) →
      m ≤ Fl.δ * (Xa.T + 3 * nd X.toData + 10).choose (nd X.toData)) ∧
    ∃ g : Fin (Fl.δ * (Xa.T + nd X.toData).choose (nd X.toData)) → Frame X.Ψ r → ℂ,
      (∀ q, g q ∈ X.SS (Xa.Fp + Xa.T • Xa.L - deMul X.Ψ r X.p0 s)) ∧
      ∀ a : _ → ℂ, (∀ x ∈ X.dom, ∑ q, a q * g q x = 0) → a = 0 := by
  have hup : ∀ (m : ℕ) (f : Fin m → Frame X.Ψ r → ℂ), (∀ q, f q ∈ X.SS (Xa.Fp + Xa.T • Xa.L)) →
      (∀ a : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, a q * f q x = 0) → a = 0) →
      m ≤ Fl.δ * (Xa.T + 2 * nd X.toData + 6).choose (nd X.toData) := fun m f hf hi =>
    GlobalTheory.UpperModel.upper E r X.toData Xa Fl m f (fun q => (hf q).1) hi
  refine ⟨hup, ?_, ?_, GlobalTheory.T.lowerRank_cuspForms_detWeight_oneComponent E r X Xa Fl hm h0 h1 hg1 hg2 hg3 hg4 s hs hsT u hu hu0⟩
  · intro m f hf hi
    have hmem : ∀ q, f q * u ∈ X.SS (Xa.Fp + Xa.T • Xa.L) := fun q =>
      mul_mem X.toData (hf q) hu.1 (sub_add_cancel _ _)
    exact hup m _ hmem (indep_mul X.toData hu.1.1.1 hu0 (fun q => (hf q).1) hi)
  · intro m f hf hi
    obtain ⟨w, hw, hw0⟩ := GlobalTheory.T.exists_nonzero_boundedSection_shiftedWeight E r X Xa Fl hm h0 h1 hg1 hg2 hg3 hg4 s hs hsT u hu hu0
    have hmem : ∀ q, X.IsBddSec (Xa.Fp + (Xa.T + (nd X.toData + 4)) • Xa.L) (f q * w) := fun q =>
      (mul_mem X.toData (hf q) hw (by simp only [add_smul]; abel)).1
    exact GlobalTheory.T.card_independent_boundedSections_shiftedWeight_le E r X.toData Xa Fl m _ hmem (indep_mul X.toData hw.1.1 hw0 (fun q => (hf q).1) hi)

theorem compT (X : DataX E r) {Ψ : Finset (E →+* ℂ)} (hΨ : X.Ψ = Ψ) (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (hG : X.Gm = G) (hp : X.p0 = p0) (L Fp : Wt Ψ r) (T s : ℕ)
    (hA : ArchOne X.toData (castWt hΨ L) (castWt hΨ Fp) T) (h0 : 0 < p0) (h1 : p0 < r)
    (hg1 : GapsGe p0 L 1) (hg2 : PairGe L (1.9 * T))
    (hg3 : GapsGe p0 (Fp - kLog Ψ r - (nd X.toData + 2) • L) 0)
    (hg4 : PairGe (Fp - kLog Ψ r - (nd X.toData + 2) • L) 1) (hs : Even s) (hsT : s ≤ T)
    (u : Frame Ψ r → ℂ) (hu : (fun y => u (castFrame hΨ y)) ∈ X.SS (castWt hΨ (deMul Ψ r p0 s)))
    (hu0 : ∃ y ∈ X.dom, u (castFrame hΨ y) ≠ 0) :
    ∃ δ : ℕ, (2 ≤ nd X.toData ∧ 11 * nd X.toData ^ 2 ≤ T) ∧ UpC X.toData hΨ G p0 (Fp + T • L) (δ * (T + 2 * nd X.toData + 6).choose (nd X.toData)) ∧
      UpC X.toData hΨ G p0 (Fp + T • L - deMul Ψ r p0 s) (δ * (T + 2 * nd X.toData + 6).choose (nd X.toData)) ∧
      UpC X.toData hΨ G p0 (Fp + T • L + 2 • deMul Ψ r p0 s)
        (δ * (T + 3 * nd X.toData + 10).choose (nd X.toData)) ∧
      LowC X.toData hΨ G p0 (Fp + T • L - deMul Ψ r p0 s) (δ * (T + nd X.toData).choose (nd X.toData)) := by
  subst hΨ hG hp
  obtain ⟨Xa, hL, hF, hT, hm, ⟨Fl⟩⟩ := hA
  change Xa.L = L at hL
  change Xa.Fp = Fp at hF
  subst hL hF hT
  obtain ⟨c1, c2, c3, g, hg, hgi⟩ := compX X Xa Fl hm h0 h1 hg1 hg2 hg3 hg4 s hs hsT u hu hu0
  exact ⟨Fl.δ, ⟨Xa.n_ge, Xa.T_ge⟩, fun m f hf hli => c1 m f hf ((li_iff f).1 hli), fun m f hf hli => c2 m f hf ((li_iff f).1 hli),
    fun m f hf hli => c3 m f hf ((li_iff f).1 hli), g, hg, (li_iff g).2 hgi⟩

theorem exists_pull_ne {U' C : Type} [Group U'] [Fintype U'] [DecidableEq U'] [MulAction U' C]
    (M : TwoLevels E r U' C) {F : C → Frame M.Ψ r → ℂ} {c : C} {x : Frame M.Ψ r} (h : M.detTr F c x ≠ 0) :
    ∃ g : U', M.pull g F c x ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  unfold TwoLevels.detTr
  have e : (Matrix.of fun g g' : U' => M.pull (g * g') F c x) = 0 := by
    ext g g'
    simp [hc]
  haveI : Nonempty U' := ⟨1⟩
  rw [e, Matrix.det_zero]

theorem tr_one_mem {U' C : Type} [Group U'] [MulAction U' C] (M : TwoLevels E r U' C) (c : C) :
    M.tr 1 c ∈ (M.comp c).Γ := by
  have h := M.tr_mul 1 1 c
  simp only [mul_one, one_smul] at h
  have e : M.tr 1 c * (M.tr 1 c * M.tr 1 c)⁻¹ = (M.tr 1 c)⁻¹ := by group
  rw [e] at h
  exact (Subgroup.inv_mem_iff _).1 h

theorem nd_comp {U' C : Type} [Group U'] [MulAction U' C] (M : TwoLevels E r U' C) (c : C) :
    nd (M.comp c).toData = M.dimY := by
  unfold nd TwoLevels.dimY
  rw [Fintype.card_prod, Fintype.card_coe, GlobalTheory.ChartCount.card_strictLower]
  rw [M.comp_Ψ c]

theorem nzT (X : Data E r) {Ψ : Finset (E →+* ℂ)} (hΨ : X.Ψ = Ψ) (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (hG : X.Gm = G) (hp : X.p0 = p0) (F : Frame Ψ r → ℂ) {la : Wt X.Ψ r}
    (hF : X.IsSec la (fun y => F (castFrame hΨ y))) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (hχ : X.χ la γ = 1)
    (x : Frame Ψ r) (hx : x ∈ GG Ψ G p0) (h : F (lact γ x) ≠ 0) : ∃ y ∈ X.dom, F (castFrame hΨ y) ≠ 0 := by
  subst hΨ hG hp
  refine ⟨x, hx, fun h0 => h ?_⟩
  have := hF.2.2 γ hγ x hx
  rw [hχ, one_mul] at this
  exact this.trans h0

section Cusp

variable {U C : Type} [Group U] [MulAction U C]

theorem upper_cusp [Finite C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (N : C → ℕ)
    (h : ∀ c, UpC (M.comp c).toData (M.comp_Ψ c) M.Gm M.p0 la (N c)) :
    Module.Finite ℂ (M.cusp la) ∧ finrank ℂ (M.cusp la) ≤ ∑ᶠ c, N c := by
  refine span_upper _ N fun c m g hg hli => ?_
  choose F hF hFg using hg
  refine h c m (fun q => F q c) (fun q => hF q c) ?_
  have e : (fun q => g q c) = fun q (x : GG M.Ψ M.Gm M.p0) => F q c x.1 := by
    funext q x
    rw [← hFg q]
    rfl
  rw [← e]
  exact hli

theorem lower_cusp [Finite C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) [Module.Finite ℂ (M.cusp la)] (N : C → ℕ)
    (h : ∀ c, LowC (M.comp c).toData (M.comp_Ψ c) M.Gm M.p0 la (N c)) :
    ∑ᶠ c, N c ≤ finrank ℂ (M.cusp la) := by
  classical
  refine lower_of_comps _ N fun c => ?_
  obtain ⟨g, hg, hli⟩ := h c
  let F : Fin (N c) → C → Frame M.Ψ r → ℂ := fun q c' => if c' = c then g q else 0
  have hF : ∀ q, F q ∈ M.SS la := by
    intro q c'
    by_cases hc : c' = c
    · subst hc
      simpa [F] using hg q
    · simp only [F, if_neg hc]
      exact (ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds r (M.comp c').toData _ 0 0).1.1
  refine ⟨fun q => M.res (F q), fun q => Submodule.subset_span ⟨F q, hF q, rfl⟩, ?_, ?_⟩
  · intro q c' hc'
    funext x
    simp [TwoLevels.res, F, hc']
  · have e : (fun q => M.res (F q) c) = fun q (x : GG M.Ψ M.Gm M.p0) => g q x.1 := by
      funext q x
      simp [TwoLevels.res, F]
    show LinearIndependent ℂ (fun q => M.res (F q) c)
    rw [e]
    exact hli

end Cusp

theorem ranks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U]
    [Finite C] [MulAction U C] (M : TwoLevels E r U C), LevelHyp (sub M ⊥) → 0 < M.p0 → M.p0 < r →
    ∀ (ka : Wt M.Ψ r) (T : ℕ), ArchOn M ka T → sOf M ≤ T →
      Ranks M ka (sOf M) ((M.dimY : ℝ) * (M.dimY + 6) / T) 2 := by
  intro E _ _ _ r U C _ _ _ _ M hLev h0 h1 ka T hArch hsT
  classical
  obtain ⟨L, Fp, rfl, hg1, hg2, hg3, hg4, hA⟩ := hArch
  haveI : Fintype (⊥ : Subgroup U) := Fintype.ofFinite _
  obtain ⟨u0, hu0, hnz⟩ :=
    GlobalTheory.T.exists_cuspForm_independent_translates E r (⊥ : Subgroup U) C (sub M ⊥) hLev (sOf M) (even_sOf M) (le_sOf M)
  have hc : ∀ c, ∃ δ : ℕ, (2 ≤ M.dimY ∧ 11 * M.dimY ^ 2 ≤ T) ∧
      UpC (M.comp c).toData (M.comp_Ψ c) M.Gm M.p0 (Fp + T • L)
        (δ * (T + 2 * M.dimY + 6).choose M.dimY) ∧
      UpC (M.comp c).toData (M.comp_Ψ c) M.Gm M.p0 (Fp + T • L - deMul M.Ψ r M.p0 (sOf M))
        (δ * (T + 2 * M.dimY + 6).choose M.dimY) ∧
      UpC (M.comp c).toData (M.comp_Ψ c) M.Gm M.p0 (Fp + T • L + 2 • deMul M.Ψ r M.p0 (sOf M))
        (δ * (T + 3 * M.dimY + 10).choose M.dimY) ∧
      LowC (M.comp c).toData (M.comp_Ψ c) M.Gm M.p0 (Fp + T • L - deMul M.Ψ r M.p0 (sOf M))
        (δ * (T + M.dimY).choose M.dimY) := by
    intro c
    have hnd := nd_comp M c
    have hg3' := hg3
    have hg4' := hg4
    rw [← hnd] at hg3' hg4'
    obtain ⟨x, hx, hdx⟩ := hnz c
    obtain ⟨h, hh⟩ := exists_pull_ne (sub M ⊥) hdx
    have hh1 : (h : U) = 1 := Subgroup.mem_bot.1 h.2
    change u0 ((h : U) • c) (lact (M.tr (h : U) c) x) ≠ 0 at hh
    rw [hh1, one_smul] at hh
    have hγ := tr_one_mem M c
    obtain ⟨y, hy, hy0⟩ := nzT (M.comp c).toData (M.comp_Ψ c) M.Gm M.p0 (M.comp_Gm c) (M.comp_basePoint c) (u0 c)
      (hu0 c).1.1 hγ (M.χ_one c _ _ hγ) x hx hh
    obtain ⟨δ, hn, c1, c2, c3, c4⟩ := compT (M.comp c) (M.comp_Ψ c) M.Gm M.p0 (M.comp_Gm c) (M.comp_basePoint c) L Fp T
      (sOf M) (hA c) h0 h1 hg1 hg2 hg3' hg4' (even_sOf M) hsT (u0 c) (hu0 c) ⟨y, hy, hy0⟩
    rw [hnd] at hn c1 c2 c3 c4
    exact ⟨δ, hn, c1, c2, c3, c4⟩
  choose δ hn c1 c2 c3 c4 using hc
  obtain ⟨f0, r0⟩ := upper_cusp M _ _ c1
  obtain ⟨fm, -⟩ := upper_cusp M _ _ c2
  obtain ⟨f2, r2⟩ := upper_cusp M _ _ c3
  have l0 := lower_cusp M _ _ c4
  haveI : Fintype C := Fintype.ofFinite C
  rw [finsum_eq_sum_of_fintype] at r0 r2 l0
  set n := M.dimY with hn_def
  have hb : ∀ c, (T + 3 * n + 10).choose n ≤ 2 * (T + n).choose n ∧
      (1 - (n : ℝ) * (n + 6) / T) * ((T + 2 * n + 6).choose n : ℕ) ≤ ((T + n).choose n : ℕ) :=
    fun c => GlobalTheory.T.two_binomial_ratio_bounds T n (hn c).1 (hn c).2
  refine ⟨f0, f2, ?_, ?_, fm⟩
  · by_cases hε : 1 - (n : ℝ) * (n + 6) / T ≤ 0
    · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hε (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    · push_neg at hε
      have r0' : (finrank ℂ (M.cusp (Fp + T • L)) : ℝ) ≤ ∑ c, (δ c : ℝ) * ((T + 2 * n + 6).choose n : ℕ) := by
        exact_mod_cast r0
      have l0' : ∑ c, (δ c : ℝ) * ((T + n).choose n : ℕ) ≤
          (finrank ℂ (M.cusp (Fp + T • L - deMul M.Ψ r M.p0 (sOf M))) : ℝ) := by
        exact_mod_cast l0
      calc (1 - (n : ℝ) * (n + 6) / T) * finrank ℂ (M.cusp (Fp + T • L))
          ≤ (1 - (n : ℝ) * (n + 6) / T) * ∑ c, (δ c : ℝ) * ((T + 2 * n + 6).choose n : ℕ) :=
            mul_le_mul_of_nonneg_left r0' hε.le
        _ = ∑ c, (δ c : ℝ) * ((1 - (n : ℝ) * (n + 6) / T) * ((T + 2 * n + 6).choose n : ℕ)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun c _ => ?_
            ring
        _ ≤ ∑ c, (δ c : ℝ) * ((T + n).choose n : ℕ) :=
            Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hb c).2 (Nat.cast_nonneg _)
        _ ≤ _ := l0'
  · have key : finrank ℂ (M.cusp (Fp + T • L + 2 • deMul M.Ψ r M.p0 (sOf M))) ≤
        2 * finrank ℂ (M.cusp (Fp + T • L - deMul M.Ψ r M.p0 (sOf M))) := by
      calc _ ≤ ∑ c, δ c * (T + 3 * n + 10).choose n := r2
        _ ≤ ∑ c, δ c * (2 * (T + n).choose n) :=
            Finset.sum_le_sum fun c _ => Nat.mul_le_mul_left _ (hb c).1
        _ = 2 * ∑ c, δ c * (T + n).choose n := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun c _ => ?_
            ring
        _ ≤ _ := Nat.mul_le_mul_left _ l0
    exact_mod_cast key

end GlobalTheory.ShareRanks

end
