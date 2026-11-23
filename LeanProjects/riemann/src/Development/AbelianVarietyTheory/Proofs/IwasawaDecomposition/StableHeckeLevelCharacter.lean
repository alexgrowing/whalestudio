import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBlockTriangularTwoBlockSizesOfLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadWMemGoodW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DescentJointEigenvectorsComplexReadingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodLineIffEigenSpanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenSpanInclusionInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeDataSplitPlaceStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EigSpanDesc

section Core

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem spanC_core (R : RealDat3 D A3 Ks) (F : Face3 D A3) {X0 : BaseLevelRowSide D} (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0)
    (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (Sb : Finset (PlE D.host))
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (hI : Rows.IsotInternal D.what₂) (hG : GlobalTheory.EigRows.OccGood D)
    (htie : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ v : (ratDatR R cG kKs hk).WL j, v ∈ goodL D (ratDatR R cG kKs hk) θ j ↔
      iotaR R (idxOf D j) v ∈ GlobalTheory.EigRows.goodW R.toRealDat F.lv2 (idxOf D j))
    (hinj : ∀ i, Function.Injective (iotaR R i))
    (hhk : ∀ (i : Fin D.R.m) (k : ℕ) (Pl : PlE D.host), 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host Pl → Pl ∉ Sb →
      ∃ α Rr, HkDat R Sb i k Pl α Rr)
    (hRd : HeckeRd R cG kKs hk Sb hL) (hEig : EigAd Y Sb eig) :
    SpanC (ratDatR R cG kKs hk) Sb θ hL eig := by
  intro j hj1 hj2
  classical
  have hjj : ((idxOf D j : Fin D.R.m) : ℕ) + 1 = j := by
    show min (j - 1) (D.R.m - 1) + 1 = j
    omega
  have hsg : ∀ c : D.what₂.LL, D.what₂.embLL c = sg0 D A3.A c := fun c =>
    (congrArg (fun g : D.what₂.LL →+* ℂ => g c) (GlobalTheory.SeriesTie.ActProof.sg0_eq_embLL R)).symm
  let I : Set (ℕ × PlE D.host) := {t | 1 ≤ t.1 ∧ t.1 ≤ D.R.r ∧ IsSplitPl D.host t.2 ∧ t.2 ∉ Sb}
  have ex : ∀ t : I, ∃ α Rr, HkDat R Sb (idxOf D j) t.1.1 t.1.2 α Rr := fun t =>
    hhk (idxOf D j) t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2
  choose α Rr hD using ex
  let T' : ℕ × PlE D.host → Module.End ℂ (Formalism.IndefR.Mult.MMap (R.MW (idxOf D j) (sg0 D A3.A))) := fun t =>
    if h : t ∈ I then hkNorm R (idxOf D j) t.1 t.2 • Formalism.IndefR.Mult.heckeOn (R.MW (idxOf D j) (sg0 D A3.A)) (Rr ⟨t, h⟩)
    else 0
  let Part : D.what₂.FT → Submodule ℂ (Formalism.IndefR.Mult.MMap (R.MW (idxOf D j) (sg0 D A3.A))) := fun σ =>
    (D.what₂.isot ((idxOf D j : ℕ) + 1) σ).map (GlobalTheory.EigRows.readW Y (idxOf D j))
  let s : Set D.what₂.FT := {σ | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}
  have hT : ∀ t ∈ I, ∀ u : Fin (R.nW (idxOf D j)) → D.what₂.LL,
      iotaR R (idxOf D j) (hL j t.1 t.2 u) = T' t (iotaR R (idxOf D j) u) := by
    intro t ht u
    simp only [T', dif_pos ht, LinearMap.smul_apply, iotaR_apply]
    exact hRd j t.1 t.2 (α ⟨t, ht⟩) (Rr ⟨t, ht⟩) hj1 hj2 (hD ⟨t, ht⟩) u
  have hPa : ∀ σ ∈ s, ∀ t ∈ I, ∀ z ∈ Part σ, T' t z = sg0 D A3.A ((eig j σ t.1 t.2 : ↥D.LL0) : D.what₂.LL) • z := by
    rintro σ hσ t ht _ ⟨y, hy, rfl⟩
    simp only [T', dif_pos ht, LinearMap.smul_apply]
    have h1 := hEig (idxOf D j) σ t.1 t.2 (α ⟨t, ht⟩) (Rr ⟨t, ht⟩) (hD ⟨t, ht⟩) hσ.2 y hy
    have h2 : eig ((idxOf D j : ℕ) + 1) σ t.1 t.2 = eig j σ t.1 t.2 := by rw [hjj]
    rw [h2, hsg] at h1
    exact h1
  have hGa : ∀ u, iotaR R (idxOf D j) u ∈ ⨆ σ ∈ s, Part σ → u ∈ goodL D (ratDatR R cG kKs hk) θ j := by
    intro u hu
    refine (htie j hj1 hj2 u).2 ?_
    have hle : (⨆ σ ∈ s, Part σ) ≤ GlobalTheory.EigRows.goodW R.toRealDat F.lv2 (idxOf D j) :=
      iSup₂_le fun σ _ => Submodule.map_le_iff_le_comap.2 fun y _ => readW_mem_goodW Y (idxOf D j) y
    exact hle hu
  intro v hv
  have hv' : iotaR R (idxOf D j) v ∈ ⨆ σ ∈ s, Part σ :=
    goodW_le_parts Y hI hG (idxOf D j) j hjj ((htie j hj1 hj2 v).1 hv)
  have hd := GlobalTheory.T.descent_joint_eigenvectors_complex_reading (sg0 D A3.A) (iotaR R (idxOf D j)) (goodL D (ratDatR R cG kKs hk) θ j)
    (fun u _ h0 => hinj (idxOf D j) (h0.trans (map_zero _).symm)) (fun t => hL j t.1 t.2) T' I hT Part s
    (fun σ t => ((eig j σ t.1 t.2 : ↥D.LL0) : D.what₂.LL)) hPa hGa v hv'
  have hle : (⨆ σ ∈ s, goodL D (ratDatR R cG kKs hk) θ j ⊓ ⨅ t ∈ I,
      Module.End.eigenspace (hL j t.1 t.2) ((eig j σ t.1 t.2 : ↥D.LL0) : D.what₂.LL)) ≤
      ⨆ σ ∈ {σ | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}, goodL D (ratDatR R cG kKs hk) θ j ⊓
        ⨅ (k : ℕ) (P : PlE D.host) (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ Sb),
          Module.End.eigenspace (hL j k P) ((eig j σ k P : ↥D.LL0) : D.what₂.LL) :=
    iSup₂_mono fun σ _ => inf_le_inf_left _ (le_iInf fun k => le_iInf fun Pl => le_iInf fun h =>
      iInf₂_le (f := fun t (_ : t ∈ I) => Module.End.eigenspace (hL j t.1 t.2) ((eig j σ t.1 t.2 : ↥D.LL0) : D.what₂.LL))
        (k, Pl) h)
  exact hle hd

end Core

theorem spanC_of_state : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x →
    Rows.IsotInternal (Dof x).what₂ → GlobalTheory.EigRows.OccGood (Dof x) →
    ∀ (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ)
      (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), (∀ kk, θ kk ≠ 1) →
      LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → StabC (SOf x) hL' → (∀ j Pl, hL' j 0 Pl = 1) →
      HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' →
      ∀ eig : ℕ → (Dof x).what₂.FT → ℕ → PlE (Dof x).host → ↥(Dof x).LL0, EigAd x.r.Y (SbD (Dof x)) eig →
        SpanC (SOf x) (SbD (Dof x)) θ hL' eig := by
  intro hL
  refine (((GlobalTheory.T.good_line_iff_eigen_span hL).and (GlobalTheory.T.eigen_span_inclusion_injective hL)).and (GlobalTheory.T.exists_hecke_data_split_place hL)).trans (StepW.of_all fun K B f T w _ _ h => ?_)
  obtain ⟨⟨htie, hinj⟩, hhk⟩ := h
  intro P x hLA hI hG θ hL' hθ hlv _ _ hRd eig hEig
  exact spanC_core x.m.z.R x.m.z.F x.r.Y x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) θ hL' eig hI hG
    (htie P x hLA θ hθ hlv) (hinj P x hLA) (hhk P x hLA) hRd hEig

end GlobalTheory.EigSpanDesc
