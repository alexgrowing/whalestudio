import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColPtInvMemStdLatIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenLevelInner
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColShiftVacEqSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacRowScalar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOMemLatOOfHat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionSumProdLastVertexMovedEqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmEqSumLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfFunctionProductSumsEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastVertexTensor

open GlobalTheory.LastVertexMove

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem lat_col (S : GridChoice W U) {t : T} (ht : t ∈ U) (k : FinPt G (.grid D.R.m D.R.m))
    (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl)
    (x : WO (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D)))) :
    actO _ _ (colPt S t (finEmb G.sp.topDec k)).1⁻¹ (colPt S t (finEmb G.sp.topDec k)).2⁻¹ x ∈ stdLat S (.top t (lastIx D)) ↔
      x ∈ stdLat S (.top t (lastIx D)) :=
  GlobalTheory.LastColLat.colPt_inv_mem_stdLat_iff S ht k hk x

theorem lat_row (S : GridChoice W U) {t : T} (ht : t ∈ U) (k : FinPt G (.grid D.R.m D.R.m))
    (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl)
    (x : WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T))) :
    actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ x ∈ stdLat S (.chi (lastIx D) D.R.m) ↔ x ∈ stdLat S (.chi (lastIx D) D.R.m) :=
  GlobalTheory.LastRowLat.rowPt_mem_stdLat S ht k hk x

theorem vac_col (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m))
    (hlat : ∀ x, actO _ _ (colPt S t g).1⁻¹ (colPt S t g).2⁻¹ x ∈ stdLat S (.top t (lastIx D)) ↔ x ∈ stdLat S (.top t (lastIx D))) :
    ∃ c : ℂ, colShift S t g (S.Z.vac (.top t (lastIx D))) = c • S.Z.vac (.top t (lastIx D)) :=
  GlobalTheory.LastVertexVac.colShift_vac_eq_smul S t g hlat

theorem vac_row (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m))
    (hlat : ∀ x, actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ x ∈ stdLat S (.chi (lastIx D) D.R.m) ↔
      x ∈ stdLat S (.chi (lastIx D) D.R.m)) :
    ∃ c : ℂ, rowShift S k (S.Z.vac (.chi (lastIx D) D.R.m)) = c • S.Z.vac (.chi (lastIx D) D.R.m) :=
  GlobalTheory.LastRowVac.vac_row_scalar S k hlat

theorem sb_std (S : GridChoice W U) {t : T} (ht : t ∈ U) {p : Pair T} (hp : DefPair D.R.m p) (d : FinDatum G t p)
    (hP : d.P = locPl G t) : IsSBHalf d.e (stdLat S p) d.fn :=
  GlobalTheory.LastVertexMove.isSBHalf_stdLat S ht hp d hP

theorem loc (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T}
    (hL : L.Is μ₀) (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (ht : t ∈ U) (hβ : β ∈ S.supp t Φ) (hexp : S.IsExpansion t Φ β τ)
    (hvec : ∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i))
    (k : FinPt G (.grid D.R.m D.R.m)) (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl) (cc cr : ℂ)
    (hcc : colShift S t (finEmb G.sp.topDec k) (S.Z.vac (.top t (lastIx D))) = cc • S.Z.vac (.top t (lastIx D)))
    (hcr : rowShift S k (S.Z.vac (.chi (lastIx D) D.R.m)) = cr • S.Z.vac (.chi (lastIx D) D.R.m))
    (x : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
    (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    (τ.sum fun d a => a *
      (∏ j, Function.update (fun j => (d.1 j).fn) (lastIx D)
        (cc • moveFn (colPt S t (finEmb G.sp.topDec k)) (d.1 (lastIx D)).fn) j (x j)) *
      ∏ i, Function.update (fun i => (d.2 i).fn) (lastIx D) (cr • moveFn (rowPt S k) (d.2 (lastIx D)).fn) i (y i)) =
    τ.sum fun d a => a * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i) :=
  GlobalTheory.T.expansion_sumProd_lastVertex_moved_eq S hL hde hc ht hβ hexp hvec k hk cc cr hcc hcr x y

end GlobalTheory.LastVertexTensor

namespace GlobalTheory.LastVertexTensor

open GlobalTheory.LastVertexMove

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem vec_eq_model (S : GridChoice W U) {t : T} {p : Pair T} (d : FinDatum G t p) (h : S.Z.HasVec d) (hz : d.z = 1)
    (Tm : (WO (G.pS p) (G.pT p) → ℂ) →ₗ[ℂ] (WO (G.pS p) (G.pT p) → ℂ))
    (hT : IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) d.e (stdLat S p) 1 (S.Z.vac p) Tm) : S.Z.vec d = Tm d.fn := by
  obtain ⟨f, hf⟩ := h
  rw [Normal.vec, FinDatum.vec_eq W hf, hz, Prod.mk_one_one, map_one, Module.End.one_apply]
  exact hf.2 Tm hT

theorem selfDual_std (S : GridChoice W U) {p : Pair T} (hp : DefPair D.R.m p) :
    IsSelfDualC (G.pS p) (S.N.latS p) ∧ IsSelfDualC (G.pT p) (S.N.latT p) := by
  have key : ∀ X, DefNode D.R.m X → IsSelfDualC (G.V X) (colLat (S.N.fr X)) := fun X hX =>
    OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on X hX)
  have hn := hp.nodes
  cases p with
  | chi i j => exact ⟨isSelfDualC_neg (key _ hn.2), key _ hn.1⟩
  | mu _ i j => exact (by simp [DefPair] at hp)
  | core i => exact (by simp [DefPair] at hp)
  | top _ j => exact ⟨key _ hn.1, key _ hn.2⟩

theorem om_model (S : GridChoice W U) {p : Pair T} (hp : DefPair D.R.m p) (hIn : p.InRange D.R.m) {e : AE D} {P : Finset (Pl D.host.E)}
    (he : IsIdemSum e P) (Tm : (WO (G.pS p) (G.pT p) → ℂ) →ₗ[ℂ] (WO (G.pS p) (G.pT p) → ℂ))
    (hT : IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLat S p) 1 (S.Z.vac p) Tm) (q : GA D (G.pS p) × GA D (G.pT p))
    (c : ℂ) (hlat : ∀ x, actO _ _ q.1⁻¹ q.2⁻¹ x ∈ stdLat S p ↔ x ∈ stdLat S p) (heig : W.om p q (S.Z.vac p) = c • S.Z.vac p)
    (Φ : WO (G.pS p) (G.pT p) → ℂ) (hΦ : IsSBHalf e (stdLat S p) Φ) : W.om p q (Tm Φ) = c • Tm (moveFn q Φ) := by
  have hind : (fun x => halfInd e (stdLat S p) (actO _ _ q.1⁻¹ q.2⁻¹ x)) = (1 : ℂ) • halfInd e (stdLat S p) := by
    funext x
    rw [Pi.smul_apply, one_smul]
    unfold halfInd
    by_cases h : x ∈ stdLat S p ∧ IsHalf e x
    · rw [if_pos ((and_congr (hlat x) (GlobalTheory.SchrMove.isHalf_actO_iff _ _ _)).2 h), if_pos h]
    · rw [if_neg (fun h' => h ((and_congr (hlat x) (GlobalTheory.SchrMove.isHalf_actO_iff _ _ _)).1 h')), if_neg h]
  have hc : W.om p (q.1, q.2) (S.Z.vac p) = c • Tm (fun x => halfInd e (stdLat S p) (actO _ _ q.1⁻¹ q.2⁻¹ x)) := by
    rw [hind, hT.vac, Prod.mk.eta]
    exact heig
  have := GlobalTheory.SplitLinear.om_model_of_base D W.ψ _ _ _ _ (W.om p) (S.N.latS p) (S.N.latT p) e (S.Z.vac p) Tm (W.om_is p hIn)
    (selfDual_std S hp).1 (selfDual_std S hp).2 (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he)
    (S.Z.vac_is p hp).2.theta hT q.1 q.2 c hc Φ hΦ
  rw [Prod.mk.eta] at this
  exact this

end GlobalTheory.LastVertexTensor

namespace GlobalTheory.LastVertexTensor

open GlobalTheory.LastVertexMove

def prodForm {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {X : ι → Type} {Y : κ → Type}
    (A : ∀ i, (X i → ℂ) →ₗ[ℂ] (X i → ℂ)) (B : ∀ j, (Y j → ℂ) →ₗ[ℂ] (Y j → ℂ)) (x : ∀ i, X i) (y : ∀ j, Y j) :
    MultilinearMap ℂ (fun i => (⊤ : Submodule ℂ (X i → ℂ))) (MultilinearMap ℂ (fun j => (⊤ : Submodule ℂ (Y j → ℂ))) ℂ) :=
  ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap fun i =>
      (LinearMap.proj (R := ℂ) (φ := fun _ : X i => ℂ) (x i)) ∘ₗ A i ∘ₗ (⊤ : Submodule ℂ (X i → ℂ)).subtype).smulRight
    ((MultilinearMap.mkPiAlgebra ℂ κ ℂ).compLinearMap fun j =>
      (LinearMap.proj (R := ℂ) (φ := fun _ : Y j => ℂ) (y j)) ∘ₗ B j ∘ₗ (⊤ : Submodule ℂ (Y j → ℂ)).subtype)

theorem prodForm_apply {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {X : ι → Type} {Y : κ → Type}
    (A : ∀ i, (X i → ℂ) →ₗ[ℂ] (X i → ℂ)) (B : ∀ j, (Y j → ℂ) →ₗ[ℂ] (Y j → ℂ)) (x : ∀ i, X i) (y : ∀ j, Y j)
    (f : ∀ i, (⊤ : Submodule ℂ (X i → ℂ))) (g : ∀ j, (⊤ : Submodule ℂ (Y j → ℂ))) :
    prodForm A B x y f g = (∏ i, A i (f i) (x i)) * ∏ j, B j (g j) (y j) := by
  simp [prodForm, MultilinearMap.smulRight_apply, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem productFn_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ k : FinPt G (.grid D.R.m D.R.m), finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
    ∀ (w : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
      (v : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
    (τ.sum fun d a => a *
      (∏ j, Function.update (fun j => S.Z.vec (d.1 j)) (lastIx D)
        (colShift S t (finEmb G.sp.topDec k) (S.Z.vec (d.1 (lastIx D)))) j (w j)) *
      ∏ i, Function.update (fun i => S.Z.vec (d.2 i)) (lastIx D) (rowShift S k (S.Z.vec (d.2 (lastIx D)))) i (v i)) =
    τ.sum fun d a => a * (∏ j, S.Z.vec (d.1 j) (w j)) * ∏ i, S.Z.vec (d.2 i) (v i) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL hde hc ht hβ hexp hvec k hk w v
  obtain ⟨e, he, hdat, -⟩ := id hexp
  obtain ⟨cc, hcc⟩ := vac_col S t (finEmb G.sp.topDec k) (lat_col S ht k hk)
  obtain ⟨cr, hcr⟩ := vac_row S k (lat_row S ht k hk)
  have hloc := loc S hL hde hc ht hβ hexp hvec k hk cc cr hcc hcr
  rcases τ.support.eq_empty_or_nonempty with h0 | ⟨d₀, hd₀⟩
  · simp [Finsupp.sum, h0]
  have hTc : ∀ j : Fin D.R.m, ∃ Tm, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLat S (.top t j)) 1
      (S.Z.vac (.top t j)) Tm := by
    intro j
    obtain ⟨f, hf⟩ := (hvec d₀ hd₀).1 j
    have h1 := hf.1
    rw [((hdat d₀ hd₀).1 j).2.1] at h1
    exact h1
  have hTr : ∀ i : Fin D.R.m, ∃ Tm, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLat S (.chi i D.R.m)) 1
      (S.Z.vac (.chi i D.R.m)) Tm := by
    intro i
    obtain ⟨f, hf⟩ := (hvec d₀ hd₀).2 i
    have h1 := hf.1
    rw [((hdat d₀ hd₀).2 i).2.1] at h1
    exact h1
  choose Tc hTc using hTc
  choose Tr hTr using hTr
  have hvc : ∀ d ∈ τ.support, ∀ j, S.Z.vec (d.1 j) = Tc j (d.1 j).fn := fun d hd j =>
    vec_eq_model S (d.1 j) ((hvec d hd).1 j) ((hdat d hd).1 j).2.2 (Tc j) (by rw [((hdat d hd).1 j).2.1]; exact hTc j)
  have hvr : ∀ d ∈ τ.support, ∀ i, S.Z.vec (d.2 i) = Tr i (d.2 i).fn := fun d hd i =>
    vec_eq_model S (d.2 i) ((hvec d hd).2 i) ((hdat d hd).2 i).2.2 (Tr i) (by rw [((hdat d hd).2 i).2.1]; exact hTr i)
  have hsc : ∀ d ∈ τ.support, colShift S t (finEmb G.sp.topDec k) (S.Z.vec (d.1 (lastIx D))) =
      Tc (lastIx D) (cc • moveFn (colPt S t (finEmb G.sp.topDec k)) (d.1 (lastIx D)).fn) := by
    intro d hd
    have hsb := sb_std S ht (defPair_top t (lastIx D)) (d.1 (lastIx D)) ((hdat d hd).1 (lastIx D)).1
    rw [((hdat d hd).1 (lastIx D)).2.1] at hsb
    rw [hvc d hd, map_smul, colShift_eq]
    exact om_model S (defPair_top t (lastIx D)) (inRange_top t (lastIx D)) he (Tc (lastIx D)) (hTc (lastIx D)) _ cc
      (lat_col S ht k hk) hcc _ hsb
  have hsr : ∀ d ∈ τ.support, rowShift S k (S.Z.vec (d.2 (lastIx D))) =
      Tr (lastIx D) (cr • moveFn (rowPt S k) (d.2 (lastIx D)).fn) := by
    intro d hd
    have hsb := sb_std S ht (defPair_chi (lastIx D)) (d.2 (lastIx D)) ((hdat d hd).2 (lastIx D)).1
    rw [((hdat d hd).2 (lastIx D)).2.1] at hsb
    rw [hvr d hd, map_smul, rowShift_eq]
    exact om_model S (defPair_chi (lastIx D)) (inRange_chi (lastIx D)) he (Tr (lastIx D)) (hTr (lastIx D)) _ cr
      (lat_row S ht k hk) hcr _ hsb
  have key := GlobalTheory.funProd_multilinear_sum_eq (prodForm Tc Tr w v) τ
    (fun d j => ⟨Function.update (fun j => (d.1 j).fn) (lastIx D)
      (cc • moveFn (colPt S t (finEmb G.sp.topDec k)) (d.1 (lastIx D)).fn) j, Submodule.mem_top⟩)
    (fun d j => ⟨(d.1 j).fn, Submodule.mem_top⟩)
    (fun d i => ⟨Function.update (fun i => (d.2 i).fn) (lastIx D) (cr • moveFn (rowPt S k) (d.2 (lastIx D)).fn) i,
      Submodule.mem_top⟩)
    (fun d i => ⟨(d.2 i).fn, Submodule.mem_top⟩) hloc
  simp only [prodForm_apply] at key
  rw [Finsupp.sum, Finsupp.sum] at key ⊢
  refine (Finset.sum_congr rfl fun d hd => ?_).trans (key.trans (Finset.sum_congr rfl fun d hd => ?_))
  · rw [mul_assoc]
    congr 2
    · refine Finset.prod_congr rfl fun j _ => ?_
      rw [show (fun j => S.Z.vec (d.1 j)) = fun j => Tc j (d.1 j).fn from funext (hvc d hd), hsc d hd,
        ← Function.apply_update (fun j => ⇑(Tc j)) (fun j => (d.1 j).fn) (lastIx D)]
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [show (fun i => S.Z.vec (d.2 i)) = fun i => Tr i (d.2 i).fn from funext (hvr d hd), hsr d hd,
        ← Function.apply_update (fun i => ⇑(Tr i)) (fun i => (d.2 i).fn) (lastIx D)]
  · rw [mul_assoc]
    congr 2
    · exact Finset.prod_congr rfl fun j _ => by rw [hvc d hd]
    · exact Finset.prod_congr rfl fun i _ => by rw [hvr d hd]

end GlobalTheory.LastVertexTensor
