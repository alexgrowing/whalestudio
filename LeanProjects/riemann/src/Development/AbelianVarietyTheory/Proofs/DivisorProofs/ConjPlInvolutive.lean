import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat

namespace GlobalTheory.SumSize.OppConj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coef

variable {ι : Type} [Fintype ι] {n : ℕ}

def mapF {K L : Type} [Field K] [Field L] (φ : K →+* L) (lam : ι → DomWeight n) (x : VV K lam) : VV L lam :=
  ⟨MvPolynomial.map φ x.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ lam _ x.2⟩

theorem mapVV_mapF {K L : Type} [Field K] [Field L] (φ : K →+* L) (ψ : L →+* ℂ) (lam : ι → DomWeight n) (x : VV K lam) :
    GlobalTheory.CoefModel.mapVV ψ lam (mapF φ lam x) = GlobalTheory.CoefModel.mapVV (ψ.comp φ) lam x :=
  Subtype.ext (by
    change MvPolynomial.map ψ (MvPolynomial.map φ x.1) = MvPolynomial.map (ψ.comp φ) x.1
    rw [MvPolynomial.map_map])

theorem mapVV_mapVV {K : Type} [Field K] (φ : K →+* ℂ) (ψ : ℂ →+* ℂ) (lam : ι → DomWeight n) (x : VV K lam) :
    GlobalTheory.CoefModel.mapVV ψ lam (GlobalTheory.CoefModel.mapVV φ lam x) = GlobalTheory.CoefModel.mapVV (ψ.comp φ) lam x :=
  Subtype.ext (by
    change MvPolynomial.map ψ (MvPolynomial.map φ x.1) = MvPolynomial.map (ψ.comp φ) x.1
    rw [MvPolynomial.map_map])

theorem mapVV_id (lam : ι → DomWeight n) (v : VV ℂ lam) : GlobalTheory.CoefModel.mapVV (RingHom.id ℂ) lam v = v :=
  Subtype.ext (by
    change MvPolynomial.map (RingHom.id ℂ) v.1 = v.1
    rw [MvPolynomial.map_id])

theorem conj_comp_conj : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ :=
  RingHom.ext fun z => Complex.conj_conj z

theorem mapVV_conj_conj (lam : ι → DomWeight n) (v : VV ℂ lam) :
    GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam (GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam v) = v := by
  rw [mapVV_mapVV, conj_comp_conj, mapVV_id]

def conjMap {n' : ℕ} {lam : ι → DomWeight n} {lam' : ι → DomWeight n'} (K : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (v : VV ℂ lam) : VV ℂ lam' :=
  GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam' (K (GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam v))

end Coef

section Places

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def conjPl (q : InfinitePlace K) : InfinitePlace K := InfinitePlace.mk (q.embedding.comp (starRingEnd K))

variable {K}

theorem conjugate_comp (φ : K →+* ℂ) (f : K →+* K) :
    (ComplexEmbedding.conjugate φ).comp f = ComplexEmbedding.conjugate (φ.comp f) :=
  RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]

theorem conjPl_mk (φ : K →+* ℂ) : conjPl K (InfinitePlace.mk φ) = InfinitePlace.mk (φ.comp (starRingEnd K)) := by
  unfold conjPl
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h, conjugate_comp, InfinitePlace.mk_conjugate_eq]

theorem star_comp_star : (starRingEnd K).comp (starRingEnd K) = RingHom.id K :=
  RingHom.ext fun x => by simp

theorem conjPl_conjPl (q : InfinitePlace K) : conjPl K (conjPl K q) = q := by
  change conjPl K (InfinitePlace.mk (q.embedding.comp (starRingEnd K))) = q
  rw [conjPl_mk, RingHom.comp_assoc, star_comp_star, RingHom.comp_id, InfinitePlace.mk_embedding]

theorem conjPl_involutive : Function.Involutive (conjPl K) := conjPl_conjPl

theorem meanInf_conjPl (g : InfinitePlace K → ℝ) : Formalism.PairingDivisionLocalBalance.meanInf K (fun q => g (conjPl K q)) = Formalism.PairingDivisionLocalBalance.meanInf K g := by
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  congr 1
  exact Equiv.sum_comp (conjPl_involutive.toPerm _) g

end Places

section Nrm

variable {D : D7} {n : ℕ} (lam : D.what₂.Tau → DomWeight n)

theorem nrm_conj (v : VV ℂ lam) :
    nrm lam (fun _ => 1) (GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam v) = nrm lam (fun _ => 1) v := by
  have h := GlobalTheory.CoefModel.pairK_mapVV (starRingEnd ℂ) lam (fun _ => rfl) (fun _ : D.what₂.Tau => (1 : Matrix (Fin n) (Fin n) ℂ)) v v
  simp only [Matrix.map_one _ (map_zero _) (map_one _)] at h
  simp only [nrm, h, Complex.conj_re]

theorem nrmLe_conj_iff (σ : D.what₂.LL →+* ℂ) (v : VV ℂ lam) (B : ℝ) :
    NrmLe lam ((starRingEnd ℂ).comp σ) v B ↔ NrmLe lam σ v B := by
  constructor
  · rintro ⟨u, hu, hB⟩
    refine ⟨u, hu, ?_⟩
    rwa [← mapVV_mapVV, nrm_conj] at hB
  · rintro ⟨u, hu, hB⟩
    refine ⟨u, hu, ?_⟩
    rwa [← mapVV_mapVV, nrm_conj]

theorem nrmLe_mk_iff (φ : D.what₂.LL →+* ℂ) (v : VV ℂ lam) (B : ℝ) :
    NrmLe lam (InfinitePlace.mk φ).embedding v B ↔ NrmLe lam φ v B := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · have e : ComplexEmbedding.conjugate φ = (starRingEnd ℂ).comp φ :=
      RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
    rw [h, e, nrmLe_conj_iff]

end Nrm

section Transfer

variable {D : D7} {n n' : ℕ} {lam : D.what₂.Tau → DomWeight n} {lam' : D.what₂.Tau → DomWeight n'}

theorem embLL_comp_star : D.what₂.embLL.comp (starRingEnd D.what₂.LL) = (starRingEnd ℂ).comp D.what₂.embLL :=
  RingHom.ext fun x => D.starLL_cx x

theorem nrmLe_of_conjMap (σ : D.what₂.LL →+* ℂ) (K : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (c : ℝ)
    (h : ∀ B v, NrmLe lam (σ.comp (starRingEnd D.what₂.LL)) v B →
      NrmLe lam' (σ.comp (starRingEnd D.what₂.LL)) (conjMap K v) (c * B))
    (B : ℝ) (v : VV ℂ lam) (hv : NrmLe lam σ v B) : NrmLe lam' σ (K v) (c * B) := by
  obtain ⟨u, hu, hB⟩ := hv
  have h1 : NrmLe lam (σ.comp (starRingEnd D.what₂.LL)) (GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam v) B := by
    refine ⟨mapF (starRingEnd D.what₂.LL) lam u, ?_, ?_⟩
    · rw [mapVV_mapF, embLL_comp_star, ← mapVV_mapVV, hu]
    · rwa [mapVV_mapF, RingHom.comp_assoc, star_comp_star, RingHom.comp_id]
  obtain ⟨u', hu', hB'⟩ := h B _ h1
  refine ⟨mapF (starRingEnd D.what₂.LL) lam' u', ?_, ?_⟩
  · rw [mapVV_mapF, embLL_comp_star, ← mapVV_mapVV, hu', conjMap, mapVV_conj_conj, mapVV_conj_conj]
  · rwa [mapVV_mapF]

end Transfer

section Std

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C b : ℝ)

def PairStdAt : Prop := ∃ g : InfinitePlace D.what₂.LL → ℝ, Formalism.PairingDivisionLocalBalance.meanInf _ g ≤ aOne ch.G C b ∧
  ∀ (p : InfinitePlace D.what₂.LL) Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β),
    (∀ (j : Fin D.R.m) B v, NrmLe _ p.embedding v B →
      NrmLe _ p.embedding (ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) v) (Real.exp (g p) * B)) ∧
    ∀ (i : Fin D.R.m) B v, NrmLe _ p.embedding v B →
      NrmLe _ p.embedding (conjMap (ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1))) v) (Real.exp (g p) * B)

theorem infRowAt_of (h : PairStdAt ch C b) : InfRowAt ch C b := by
  obtain ⟨g, hg, h⟩ := h
  refine ⟨fun p => g (conjPl _ p), by rwa [meanInf_conjPl], ?_⟩
  intro p Φ β d hO c i B v hv
  have key := (h (conjPl _ p) Φ β d hO c).2 i
  refine nrmLe_of_conjMap p.embedding _ _ (fun B' v' hv' => ?_) B v hv
  exact (nrmLe_mk_iff _ (p.embedding.comp (starRingEnd D.what₂.LL)) _ _).1
    (key B' v' ((nrmLe_mk_iff _ (p.embedding.comp (starRingEnd D.what₂.LL)) _ _).2 hv'))

end Std

def PairStdK : Prop := BigC fun _ ch C b => PairStdAt ch C b

theorem bigC_mono {Q Q' : ChQ} (h : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (F : Face D A) (ch : Choice R) (C b : ℝ),
    Q F ch C b → Q' F ch C b) : BigC Q → BigC Q' := by
  rintro ⟨CF0, h0⟩
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, h1⟩ := h0 CF hCF
  refine ⟨C0, fun ε C hC => ?_⟩
  obtain ⟨x0, h2⟩ := h1 ε C hC
  exact ⟨x0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h3 h4 h5 =>
    h F ch C large₂.sc.b (h2 D large₂ he hx Γ Pl0 T A Ks R F hS ch h3 h4 h5)⟩

theorem infRowK_of (h : PairStdK) : InfRowK := bigC_mono (fun _ ch C b => infRowAt_of ch C b) h

end GlobalTheory.SumSize.OppConj

end
