import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TraceClassRank

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FormTies GlobalTheory.OnTies
open Formalism.HermitianLatticesTheory (localization₂)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Trace

variable {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (ι : Fin D.R.m)
  (ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l))
  (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ)

def traceLat : Submodule (𝓞 D.what₂.LL) (Fin (R.nW ι) → D.what₂.LL) :=
  Submodule.span (𝓞 D.what₂.LL)
    ((fun f : U → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) =>
        ∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo h fw ι (f u)) ''
      {f | IsOrbitFamily (T.Q.Xo ((ι : ℕ) + 1)) T.Q.c (badN D) (wtA (κ ι)) (T.dδ ((ι : ℕ) + 1) (κ ι).n) (fun u : U => ℓ u)
        fun u => ((f u).1 : T.R ((ι : ℕ) + 1))})

def CompareAt (lam : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  localization₂ lam.asIdeal (traceLat h fw ι ℓ U ψ) ≤ localization₂ lam.asIdeal (thetaBase R ι U ψ ph v p)

def CompareOffOwn : Prop := ∀ lam, Formalism.EigenvalueLevelCeiling.plc lam ≠ p → CompareAt h fw ι ℓ U ψ ph v p lam

def CompareSpan : Prop :=
  Submodule.span D.what₂.LL (traceLat h fw ι ℓ U ψ : Set (Fin (R.nW ι) → D.what₂.LL)) =
    Submodule.span D.what₂.LL (thetaBase R ι U ψ ph v p : Set (Fin (R.nW ι) → D.what₂.LL))

def CompareAtOwn : Prop := ∀ lam, Formalism.EigenvalueLevelCeiling.plc lam = p → CompareAt h fw ι ℓ U ψ ph v p lam

variable {h fw ι ℓ U ψ ph v p} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
    {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
    {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    {O : OnObj S P oc} {i : Bs.J}
    {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
    {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
    {inc : P →* G}
    {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}

theorem traceLat_le (h1 : CompareOffOwn h fw ι ℓ U ψ ph v p) (h2 : CompareAtOwn h fw ι ℓ U ψ ph v p) :
    traceLat h fw ι ℓ U ψ ≤ thetaBase R ι U ψ ph v p :=
  Formalism.DivisionValues.GluingInclusion.le_of_forall_localized_le_of_not_isField (RingOfIntegers.not_isField _) _ _ fun lam =>
    (em (Formalism.EigenvalueLevelCeiling.plc lam = p)).elim (h2 lam) (h1 lam)

def comapEquiv {P G : Type} [Group P] [Group G] {inc : P →* G} (hi : Function.Injective inc) {U : Subgroup G}
    (hU : U ≤ inc.range) : U.comap inc ≃ U :=
  Equiv.ofBijective (fun u => ⟨inc u, u.2⟩) ⟨fun _ _ e => Subtype.ext (hi (congrArg Subtype.val e)), fun u => by
    obtain ⟨g, hg⟩ := hU u.2
    exact ⟨⟨g, show inc g ∈ U from hg ▸ u.2⟩, Subtype.ext hg⟩⟩

theorem isOrbitFamily_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {bad : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {d : DeltaDat Xo c n} {I I' : Type}
    {m : I → (LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l)} {m' : I' → (LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l)}
    {f : I → Rul Xo c} (hf : IsOrbitFamily Xo c bad a d m f) (e : I' → I) (he : ∀ u, m' u = m (e u)) :
    IsOrbitFamily Xo c bad a d m' fun u => f (e u) := by
  obtain ⟨Λ, N, x₀, P, x, h1, h2, h3, h4, h5, h6, h7⟩ := hf
  exact ⟨Λ, N, x₀, P, fun u => x (e u), h1, h2, h3, h4, h5, h6, fun u => he u ▸ h7 (e u)⟩

abbrev coordEquiv (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (ι : Fin D.R.m) {n : ℕ}
    (z : (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL]
      D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)) :
    (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (R.nW ι) → D.what₂.LL) :=
  LinearEquiv.ofBijective (toForms h fw ι z) (toForms_bijective h fw ι z)

theorem Th0_eq_comap (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (hi : Function.Injective inc)
    (hU : U ≤ inc.range) :
    O.Th0 v i = (traceLat h fw ι ℓ U ψ).comap ((toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) := by
  have hm : (O.Th0 v i).map ((toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) = traceLat h fw ι ℓ U ψ := by
    rw [t.Th0_eq, t.U_eq]
    unfold thetaEig traceSpan traceLat
    rw [Submodule.map_span, Set.image_image]
    have key : ∀ f : U → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι),
        (toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)
          (∑ᶠ u : U.comap inc, O.ψ (u : P) • z.symm (1 ⊗ₜ[(recB h.toLawsCore).KO] f (comapEquiv hi hU u))) =
        ∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo h fw ι (f u) := fun f => by
      rw [map_finsum _ (Set.toFinite _), ← finsum_comp_equiv (comapEquiv hi hU)]
      refine finsum_congr fun u => ?_
      rw [map_smul, LinearMap.restrictScalars_apply, toForms_tmul, one_smul, ← algebraMap_smul D.what₂.LL]
      exact congrArg (· • _) (t.ψ_eq u u.2)
    congr 1
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine ⟨fun u => f ((comapEquiv hi hU).symm u), isOrbitFamily_comp hf _ (fun u => ?_), ?_⟩
      · exact congrArg (fun a : U => ℓ a) ((comapEquiv hi hU).apply_symm_apply u).symm
      · refine (key _).symm.trans ?_
        simp only [Equiv.symm_apply_apply]
    · rintro ⟨f, hf, rfl⟩
      exact ⟨fun u => f (comapEquiv hi hU u), isOrbitFamily_comp hf _ fun u => rfl, key f⟩
  rw [← hm]
  exact (Submodule.comap_map_eq_of_injective (f := (toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL))
    (toForms_bijective h fw ι z).1 _).symm

theorem Zg_eq_comap (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (ha : ActionPin h fw ι ℓ)
    (hU : U ≤ inc.range) (hχ : ∀ u : U, (R.FW ι).chi u = 1) :
    O.Zg i = (goodType R ι U ψ).comap (toForms h fw ι z) := by
  have hb := toForms_bijective h fw ι z
  ext x
  refine and_congr ?_ ?_
  · change x ∈ Formalism.EigenvalueLevelCeiling.eig _ _ _ ↔ ∀ u : U, _
    unfold Formalism.EigenvalueLevelCeiling.eig
    rw [t.U_eq]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero]
    constructor
    · intro hx u
      obtain ⟨g, hg⟩ := hU u.2
      have hg' : inc g ∈ U := hg ▸ u.2
      obtain rfl : u = ⟨inc g, hg'⟩ := Subtype.ext hg.symm
      rw [hχ, one_mul, ← t.rho_eq_of_actionPin ha, hx ⟨g, hg'⟩, map_smul, t.ψ_eq g hg']
    · intro hx u
      apply hb.1
      rw [t.rho_eq_of_actionPin ha, hx ⟨inc u, u.2⟩, hχ, one_mul, map_smul, t.ψ_eq u u.2]
  · change x ∈ O.V₀ i ↔ _
    rw [t.V₀_eq]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, (t.e_eOp a).symm⟩
    · rintro ⟨a, ha⟩
      obtain ⟨b, rfl⟩ := hb.2 a
      exact ⟨b, hb.1 ((t.e_eOp b).trans ha)⟩

theorem isLatIn_eJ (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (ha : ActionPin h fw ι ℓ)
    (hU : U ≤ inc.range) (hχ : ∀ u : U, (R.FW ι).chi u = 1) (hd : FormsDetermined R ι)
    (hM : SpanOverClasses R ι U ψ ph v p) (hR : ClassFullRank R ι U ψ ph v p) : Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg i) (O.eJ v i) := by
  unfold OnObj.eJ
  rw [Zg_eq_comap t ha hU hχ, t.ThJ_eq]
  exact isLatIn_comap (coordEquiv h fw ι z) t.e_eOp ⟨(thetaBase_fg hd hM).map _, hR⟩

theorem theta_lattice_full_rank (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (ha : ActionPin h fw ι ℓ)
    (hi : Function.Injective inc) (hU : U ≤ inc.range) (hχ : ∀ u : U, (R.FW ι).chi u = 1)
    (hR : ClassFullRank R ι U ψ ph v p) (hC : CompareSpan h fw ι ℓ U ψ ph v p) (hfg : (O.Th0 v i).FG) :
    Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg i) ((O.Th0 v i).map ((O.e i).restrictScalars (𝓞 D.what₂.LL))) := by
  have hb := toForms_bijective h fw ι z
  have e := Th0_eq_comap t hi hU
  have hfg' : (traceLat h fw ι ℓ U ψ).FG := by
    have := hfg.map ((toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL))
    rwa [e, Submodule.map_comap_eq_of_surjective (f := (toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) hb.2] at this
  rw [Zg_eq_comap t ha hU hχ, e]
  exact isLatIn_comap (coordEquiv h fw ι z) t.e_eOp ⟨hfg'.map _, (span_map_congr _ hC).trans hR⟩

theorem trace_lattice_le_theta_lattice_at_place (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (hi : Function.Injective inc)
    (hU : U ≤ inc.range) {n : ℕ} (hp : RunPin R ι n v p) (hA : CompareOffOwn h fw ι ℓ U ψ ph v p) :
    localization₂ v.asIdeal (O.Th0 v i) ≤ localization₂ v.asIdeal (O.ThJ v i) := by
  rw [Th0_eq_comap t hi hU, t.ThJ_eq]
  refine localization_comap_le v _ (hA v fun e => ?_)
  have h1 := hp.1
  split_ifs at h1 with h2
  · exact D.host.pde_ne (h2.symm.trans (e.trans h1))
  · exact h2 (e.trans h1)

theorem Th0_le_ThJ (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (hi : Function.Injective inc)
    (hU : U ≤ inc.range) (hd : FormsDetermined R ι) (hM : SpanOverClasses R ι U ψ ph v p)
    (hA : CompareOffOwn h fw ι ℓ U ψ ph v p) (hO : CompareAtOwn h fw ι ℓ U ψ ph v p) :
    O.Th0 v i ≤ O.ThJ v i ∧ (O.Th0 v i).FG := by
  have hle : O.Th0 v i ≤ O.ThJ v i := by
    rw [Th0_eq_comap t hi hU, t.ThJ_eq]
    exact Submodule.comap_mono (traceLat_le hA hO)
  refine ⟨hle, Submodule.FG.of_le ?_ hle⟩
  have hb := toForms_bijective h fw ι z
  refine Submodule.fg_of_fg_map_injective ((toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) hb.1 ?_
  rw [t.ThJ_eq, Submodule.map_comap_eq_of_surjective (f := (toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) hb.2]
  exact thetaBase_fg hd hM

end Trace

section Place

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type}
  [Group P] [Finite P] {c : OnConst}

def RankAtPlaces (O : OnObj S P c) : Prop :=
  AtPair S fun v => ∀ j, Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K))) ∧
    Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) (O.eJ v j) ∧ localization₂ v.asIdeal (O.Th0 v j) ≤ localization₂ v.asIdeal (O.ThJ v j)

def fillJ (O : OnObj S P c) : OnObj S P c := { O with ThJ := fun v j => O.ThJ v j ⊔ O.Th0 v j }

theorem rankAtPlaces_of {O : OnObj S P c} (h : LeafRankJ O) : RankAtPlaces O := fun w hw =>
  ⟨fun j => ⟨((h w hw).1 j).1, ((h w hw).1 j).2.1, Formalism.HermitianLatticesTheory.locBasic_locS_mono _ ((h w hw).1 j).2.2⟩,
    fun j => ⟨((h w hw).2 j).1, ((h w hw).2 j).2.1, Formalism.HermitianLatticesTheory.locBasic_locS_mono _ ((h w hw).2 j).2.2⟩⟩

theorem leafRankJ_fillJ {O : OnObj S P c} (h : RankAtPlaces O) : LeafRankJ (fillJ O) := by
  have key : ∀ v j, Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K))) →
      Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) (O.eJ v j) → Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((fillJ O).eJ v j) := fun v j a b => by
    change Formalism.EigenvalueLevelCeiling.IsLatIn _ ((O.ThJ v j ⊔ O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K)))
    rw [Submodule.map_sup]
    refine ⟨b.1.sup a.1, le_antisymm (Submodule.span_le.2 ?_) ?_⟩
    · change _ ≤ (O.Zg j).restrictScalars (𝓞 K)
      exact sup_le (fun x hx => b.2.le (Submodule.subset_span hx)) fun x hx => a.2.le (Submodule.subset_span hx)
    · exact b.2.ge.trans (Submodule.span_mono (show O.eJ v j ≤ _ from le_sup_left))
  exact fun w hw =>
    ⟨fun j => ⟨((h w hw).1 j).1, key _ j ((h w hw).1 j).1 ((h w hw).1 j).2.1, le_sup_right⟩,
      fun j => ⟨((h w hw).2 j).1, key _ j ((h w hw).2 j).1 ((h w hw).2 j).2.1, le_sup_right⟩⟩

theorem lix_fillJ {O : OnObj S P c} {v : HeightOneSpectrum (𝓞 K)} {j : Bs.J}
    (h : localization₂ v.asIdeal (O.Th0 v j) ≤ localization₂ v.asIdeal (O.ThJ v j)) (M : Submodule (𝓞 K) (Fin (O.nZ j) → K)) :
    Formalism.EigenvalueLevelCeiling.lix v M ((fillJ O).eJ v j) = Formalism.EigenvalueLevelCeiling.lix v M (O.eJ v j) := by
  have h1 : O.ThJ v j ⊔ O.Th0 v j ≤ localization₂ v.asIdeal (O.ThJ v j) :=
    sup_le (Formalism.HermitianLatticesTheory.locBasic_le_locS _ _) ((Formalism.HermitianLatticesTheory.locBasic_le_locS _ _).trans h)
  have h2 : (fillJ O).eJ v j ≤ localization₂ v.asIdeal (O.eJ v j) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hsx⟩ := h1 hx
    exact ⟨s, hs, _, hsx, map_smul ((O.e j).restrictScalars (𝓞 K)) s x⟩
  have h3 : localization₂ v.asIdeal ((fillJ O).eJ v j) = localization₂ v.asIdeal (O.eJ v j) :=
    le_antisymm ((Formalism.HermitianLatticesTheory.locBasic_locS_mono _ h2).trans (Formalism.HermitianLatticesTheory.locBasic_locS_idem _ _).le)
      (Formalism.HermitianLatticesTheory.locBasic_locS_mono _ (Submodule.map_mono le_sup_left))
  exact (Formalism.EigenvalueLevelCeiling.lix_locP v M _).trans ((congrArg _ h3).trans (Formalism.EigenvalueLevelCeiling.lix_locP v M _).symm)

theorem leafTW1_fillJ {O : OnObj S P c} (h : RankAtPlaces O) (h1 : LeafTW1 O) : LeafTW1 (fillJ O) :=
  ⟨fun w hw =>
    ⟨fun j => ⟨((h1.1 w hw).1 j).1, ((h1.1 w hw).1 j).2.trans_eq
        (congrArg (fun a : ℤ => (a : ℝ) + _) (lix_fillJ ((h w hw).1 j).2.2 _).symm)⟩,
      fun j => ⟨((h1.1 w hw).2 j).1, ((h1.1 w hw).2 j).2.trans_eq
        (congrArg (fun a : ℤ => (a : ℝ) + _) (lix_fillJ ((h w hw).2 j).2.2 _).symm)⟩⟩, h1.2⟩

theorem on_core_atPlaces (N : IndefNum Bs) (O : OnObj S P c) (CE : ℝ) (hRk : RankRows S)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : RankAtPlaces O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : LeafTW1 O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood N O) (hR : LeafDepthRam N O) (h2p : LeafDepth2 N O) (hL : LeafDepthLevel N O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp N O) (hCE : c.CE ≤ CE) (tE1 : ErrorConstantMatchesDefinition N O CE) : ONwith S N O.errOn :=
  on_core N (fillJ O) CE hRk hMk hSup hProj hC hSp hS hT0 hD (leafRankJ_fillJ hJ) hI h2 (leafTW1_fillJ hJ h1) hSh hIU hBS hUn
    hG hR h2p hL hPg hSz hX hBad hJS hJE hCE tE1

end Place

section Row

variable {T : HeightOneSpectrum (𝓞 D.what₂.LL) → Full D} [inst : ∀ v, Algebra (T v).J.Q.c.F D.what₂.LL]
  {R : ∀ v, RealDat D A (T v).J.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ v (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), ((R v).MW i σ).Vec}
  {h : ∀ v, LawsP (T v).toTop} {fw : ∀ v, FWTie (T v).J (R v) κ (v₀ v)} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {ι : Bs.J → Fin D.R.m} {wL wF : ∀ i, WeightFamilies.Wt D ((ι i : ℕ) + 1)} {nT : ℕ}
  {z : ∀ v i, (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB (h v).toLawsCore).KO] (recB (h v).toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i))}
  {act : ∀ v i, P → (recB (h v).toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i)) →
    (recB (h v).toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i))}
  {inc : P →* G}
  {ℓ : ∀ v i, G → (LaMod ((T v).Q.Dw ((ι i : ℕ) + 1)) (T v).Q.l ≃ₗ[𝓞 D.host.E] LaMod ((T v).Q.Dw ((ι i : ℕ) + 1)) (T v).Q.l)}
  {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.J → ℂ}
  {y : ∀ v i, (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A (ι i) ((R v).mu v) U ψ) → D.what₂.LL)}

theorem rankAtPlaces_of_tie
    (t : AtPair S fun v => ∀ i, OnTie (h v) (fw v) hinj EX (p v) (ι i) (wL i) (wF i) nT O v i (z v i) (act v i) inc (ℓ v i) U ψ
      (ph v i) (y v i))
    (ha : AtPair S fun v => ∀ i, ActionPin (h v) (fw v) (ι i) (ℓ v i))
    (hp : AtPair S fun v => ∀ i, RunPin (R v) (ι i) (κ (ι i)).n v (p v))
    (hi : Function.Injective inc) (hU : U ≤ inc.range)
    (hχ : AtPair S fun v => ∀ i (u : U), ((R v).FW (ι i)).chi u = 1)
    (hd : AtPair S fun v => ∀ i, FormsDetermined (R v) (ι i))
    (hK : LeafSpan O)
    (hM : AtPair S fun v => ∀ i, SpanOverClasses (R v) (ι i) U ψ (ph v i) v (p v))
    (hR : AtPair S fun v => ∀ i, ClassFullRank (R v) (ι i) U ψ (ph v i) v (p v))
    (hA : AtPair S fun v => ∀ i, CompareOffOwn (h v) (fw v) (ι i) (ℓ v i) U ψ (ph v i) v (p v))
    (hC : AtPair S fun v => ∀ i, CompareSpan (h v) (fw v) (ι i) (ℓ v i) U ψ (ph v i) v (p v)) :
    RankAtPlaces O := by
  have hn : ∀ v (i : Fin D.R.m), (κ i).n = D.R.nV := fun v i =>
    ((fw v).kap i (D.eTau.symm ⟨1, Subgroup.one_mem _⟩)).2.2
  intro w hw
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have t := (t w hw).1 i
    exact ⟨theta_lattice_full_rank t ((ha w hw).1 i) hi hU ((hχ w hw).1 i) ((hR w hw).1 i) ((hC w hw).1 i)
        (((hK w hw).1 i).2.1.of_le (t.Th0_le_ThK (hn w _))),
      isLatIn_eJ t ((ha w hw).1 i) hU ((hχ w hw).1 i) ((hd w hw).1 i) ((hM w hw).1 i) ((hR w hw).1 i),
      trace_lattice_le_theta_lattice_at_place t hi hU ((hp w hw).1 i) ((hA w hw).1 i)⟩
  · have t := (t w hw).2 i
    exact ⟨theta_lattice_full_rank t ((ha w hw).2 i) hi hU ((hχ w hw).2 i) ((hR w hw).2 i) ((hC w hw).2 i)
        (((hK w hw).2 i).2.1.of_le (t.Th0_le_ThK (hn w _))),
      isLatIn_eJ t ((ha w hw).2 i) hU ((hχ w hw).2 i) ((hd w hw).2 i) ((hM w hw).2 i) ((hR w hw).2 i),
      trace_lattice_le_theta_lattice_at_place t hi hU ((hp w hw).2 i) ((hA w hw).2 i)⟩

theorem leafRankJ_of_tie
    (t : AtPair S fun v => ∀ i, OnTie (h v) (fw v) hinj EX (p v) (ι i) (wL i) (wF i) nT O v i (z v i) (act v i) inc (ℓ v i) U ψ
      (ph v i) (y v i))
    (ha : AtPair S fun v => ∀ i, ActionPin (h v) (fw v) (ι i) (ℓ v i))
    (hi : Function.Injective inc) (hU : U ≤ inc.range)
    (hχ : AtPair S fun v => ∀ i (u : U), ((R v).FW (ι i)).chi u = 1)
    (hd : AtPair S fun v => ∀ i, FormsDetermined (R v) (ι i))
    (hM : AtPair S fun v => ∀ i, SpanOverClasses (R v) (ι i) U ψ (ph v i) v (p v))
    (hR : AtPair S fun v => ∀ i, ClassFullRank (R v) (ι i) U ψ (ph v i) v (p v))
    (hA : AtPair S fun v => ∀ i, CompareOffOwn (h v) (fw v) (ι i) (ℓ v i) U ψ (ph v i) v (p v))
    (hC : AtPair S fun v => ∀ i, CompareSpan (h v) (fw v) (ι i) (ℓ v i) U ψ (ph v i) v (p v))
    (hO : AtPair S fun v => ∀ i, CompareAtOwn (h v) (fw v) (ι i) (ℓ v i) U ψ (ph v i) v (p v)) :
    LeafRankJ O := by
  intro w hw
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have t := (t w hw).1 i
    have k := Th0_le_ThJ t hi hU ((hd w hw).1 i) ((hM w hw).1 i) ((hA w hw).1 i) ((hO w hw).1 i)
    exact ⟨theta_lattice_full_rank t ((ha w hw).1 i) hi hU ((hχ w hw).1 i) ((hR w hw).1 i) ((hC w hw).1 i) k.2,
      isLatIn_eJ t ((ha w hw).1 i) hU ((hχ w hw).1 i) ((hd w hw).1 i) ((hM w hw).1 i) ((hR w hw).1 i), k.1⟩
  · have t := (t w hw).2 i
    have k := Th0_le_ThJ t hi hU ((hd w hw).2 i) ((hM w hw).2 i) ((hA w hw).2 i) ((hO w hw).2 i)
    exact ⟨theta_lattice_full_rank t ((ha w hw).2 i) hi hU ((hχ w hw).2 i) ((hR w hw).2 i) ((hC w hw).2 i) k.2,
      isLatIn_eJ t ((ha w hw).2 i) hU ((hχ w hw).2 i) ((hd w hw).2 i) ((hM w hw).2 i) ((hR w hw).2 i), k.1⟩

end Row

end GlobalTheory.TraceClassRank
