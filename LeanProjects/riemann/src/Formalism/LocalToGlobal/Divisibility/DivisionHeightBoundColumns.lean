import Mathlib
import Formalism.LocalToGlobal.Divisibility.LiftLatInst
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.LocalToGlobal.Columns.RowFormsRat
import Formalism.LocalToGlobal.Columns.WmLemmas
import Formalism.LocalToGlobal.Columns.AnisotropicOfPositiveDefinite
import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2.Indef

section Conj

variable {K : Type} [Field K] {M M₂ : Type} [AddCommGroup M] [Module K M] [AddCommGroup M₂] [Module K M₂]
  (e : M ≃ₗ[K] M₂)

theorem conjE_one : e.conj (1 : Module.End K M) = 1 := by
  ext x
  simp [LinearEquiv.conj_apply]

theorem conjE_commute {f g : Module.End K M} (hfg : Commute f g) : Commute (e.conj f) (e.conj g) := by
  rw [commute_iff_eq]
  ext x
  simpa [LinearEquiv.conj_apply] using congrArg e (LinearMap.congr_fun hfg.eq (e.symm x))

theorem conjE_sub_pow (f : Module.End K M) (μ : K) (k : ℕ) :
    (e.conj f - μ • (1 : Module.End K M₂)) ^ k = e.conj ((f - μ • (1 : Module.End K M)) ^ k) := by
  have hsub : e.conj f - μ • (1 : Module.End K M₂) = e.conj (f - μ • (1 : Module.End K M)) := by
    ext x
    simp [LinearEquiv.conj_apply]
  rw [hsub]
  induction k with
  | zero => rw [pow_zero, pow_zero, conjE_one]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    ext x
    simp [LinearEquiv.conj_apply]

theorem conjE_maxGen (f : Module.End K M) (μ : K) :
    (e.conj f).maxGenEigenspace μ = (f.maxGenEigenspace μ).map (e : M →ₗ[K] M₂) := by
  ext y
  simp only [Module.End.mem_maxGenEigenspace, Submodule.mem_map, conjE_sub_pow]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨e.symm y, ⟨k, ?_⟩, by simp⟩
    simpa [LinearEquiv.conj_apply] using hk
  · rintro ⟨x, ⟨k, hk⟩, rfl⟩
    exact ⟨k, by simp [LinearEquiv.conj_apply, hk]⟩

theorem conjE_iSup_maxGen (f : Module.End K M) (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤) :
    ⨆ μ, (e.conj f).maxGenEigenspace μ = ⊤ := by
  simp only [conjE_maxGen]
  rw [← Submodule.map_iSup, hf, Submodule.map_top]
  exact LinearEquiv.range e

end Conj

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}
  {ST SG' : Finset (HeightOneSpectrum (𝓞 E))}
  (S : Col.GSD K) (h : S.Ok) (c : Col.DecoPts S E n ST SG') (SG : Finset (HeightOneSpectrum (𝓞 E)))
  (S0 : Set (HeightOneSpectrum (𝓞 E)))

theorem heckeCSD_zero (P : offSub ST SG SG' S0) : heckeCSD S h c SG S0 (P, 0) = 1 := by
  unfold heckeCSD
  dsimp only
  first
    | (simp only [Col.heckeFam_zero]; ext x; simp [LinearEquiv.conj_apply])
    | (erw [Col.heckeFam_zero]; ext x; simp [LinearEquiv.conj_apply])
    | (ext x; simp [LinearEquiv.conj_apply, Col.heckeFam_zero])

theorem heckeCSD_comm (hc : Col.HeckeComm c S0) : Col.PairComm (heckeCSD S h c SG S0) := by
  intro x y
  exact conjE_commute _ (hc _ _)

theorem heckeCSD_split (hs : Col.HeckeFieldsIn c S0) : Col.SplitOver (heckeCSD S h c SG S0) := by
  intro x
  exact conjE_iSup_maxGen (S.res h) _ (hs _)

theorem heckeCSD_rat (R : S.Rat) (x : offSub ST SG SG' S0 × ℕ) (a b : Fin (S.toCSD h).dim) :
    LinearMap.toMatrix (S.toCSD h).basis (S.toCSD h).basis (heckeCSD S h c SG S0 x) a b ∈ cmMax K := by
  have hR : (S.toCSD h).Rat := S.toCSDOf_rat h R S.outSec
  have hb := Col.csd_hasRatBasis _ hR
  rw [LinearMap.toMatrix_apply]
  refine Col.CSDRat.repr_mem _ hR hb (S.det_H_ne_zero R h) _ ?_ a
  intro cl i
  have hf := (S.toCSD h).basis_rat hb b
  show S.bV.repr ((((Col.heckeD c x.1.1.1.asIdeal x.2).op ((S.res h).symm ((S.toCSD h).basis b)) : S.EqFun) :
    S.D → S.V) (S.outSec.rep cl)) i ∈ cmMax K
  rw [Col.heckeD_op_apply]
  simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine sum_mem fun e _ => ?_
  show S.bV.repr (S.ρ (S.outSec.mv e) ((((S.toCSD h).basis b).1 : S.Cl → S.V) (S.cls e))) i ∈ cmMax K
  exact S.rho_mem R _ _ (hf _) i

theorem heckeCSD_adj (x : offSub ST SG SG' S0 × ℕ) :
    ∃ y, ∀ f g : (S.toCSD h).Forms,
      (S.toCSD h).csum (heckeCSD S h c SG S0 x f : (S.toCSD h).Cl → (S.toCSD h).V) (g : (S.toCSD h).Cl → (S.toCSD h).V) =
        (S.toCSD h).csum (f : (S.toCSD h).Cl → (S.toCSD h).V)
          (heckeCSD S h c SG S0 y g : (S.toCSD h).Cl → (S.toCSD h).V) := by
  let P' : Col.LevOff ST SG' S0 := Col.conjugateSplitOff ⟨x.1.1.1, x.1.2⟩
  let Q : Col.LevOff ST SG S0 := Col.conjugateSplitOff x.1.1
  have hQ : Q ∈ offSub ST SG SG' S0 := P'.2
  refine ⟨(⟨Q, hQ⟩, x.2), fun f g => ?_⟩
  have e := Col.heckeOperator_adjoint_conj c h x.1.1.1 x.2 ((S.res h).symm f) ((S.res h).symm g)
  conv_lhs => rw [← LinearEquiv.apply_symm_apply (S.res h) g]
  conv_rhs => rw [← LinearEquiv.apply_symm_apply (S.res h) f]
  exact e

end Gen

section Tr

variable {X : Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : Col.CoefPk X n (Col.DecoSet X.E n ST SG)) (Λ : Col.LevFam X.E X.K n SG)

theorem heckeFam_formPts_apply (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (y : Col.LevOff ST SG S0 × ℕ)
    (φ : (Col.formGSD C Λ).EqFun) :
    ((Col.heckeFam (formPts C Λ) S0 y φ : (Col.formGSD C Λ).EqFun) : Col.DecoSet X.E n ST SG → C.V) =
      Col.nbFun X.K C.V y.1.1.asIdeal y.2 (φ : Col.DecoSet X.E n ST SG → C.V) := by
  funext d
  simp only [Col.heckeFam, Col.heckeD]
  erw [Col.LocOp.ofNbr_op_apply]
  simp only [Col.DecoPts.nb, Finset.sum_map, LinearMap.id_apply]
  rfl

theorem heckeFam_comm_trRep {A : Type} [Group A] (ι : A →* Col.GLG X.E n SG) (hι : ∀ a w, (Λ w).NormBy (ι a w))
    (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (y : Col.LevOff ST SG S0 × ℕ) (a : A) :
    Commute (Col.trRep C Λ ι hι a) (Col.heckeFam (formPts C Λ) S0 y) := by
  rw [commute_iff_eq]
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  have key : ∀ ψ : (Col.formGSD C Λ).EqFun,
      ((Col.trRep C Λ ι hι a ψ : (Col.formGSD C Λ).EqFun) : Col.DecoSet X.E n ST SG → C.V) =
        Col.trF X n ST SG C.V (ι a) (ψ : Col.DecoSet X.E n ST SG → C.V) := fun ψ => rfl
  rw [Module.End.mul_apply, Module.End.mul_apply, key, heckeFam_formPts_apply, heckeFam_formPts_apply, key,
    Col.trF_nbFun]

theorem heckeCSD_comm_trRep (h : (Col.formGSD C Λ).Ok) {A : Type} [Group A] (ι : A →* Col.GLG X.E n SG)
    (hι : ∀ a w, (Λ w).NormBy (ι a w)) (SG0 : Finset (HeightOneSpectrum (𝓞 X.E)))
    (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (x : offSub ST SG0 SG S0 × ℕ) (a : A) :
    Commute (heckeCSD (Col.formGSD C Λ) h (formPts C Λ) SG0 S0 x)
      ((Col.formGSD C Λ).repCSD h (Col.trRep C Λ ι hι) a) := by
  have hc := heckeFam_comm_trRep C Λ ι hι S0 (⟨x.1.1.1, x.1.2⟩, x.2) a
  have hr : (Col.formGSD C Λ).repCSD h (Col.trRep C Λ ι hι) a =
      ((Col.formGSD C Λ).res h).conj (Col.trRep C Λ ι hι a) := by
    apply LinearMap.ext
    intro f
    simp [Col.GSD.repCSD, LinearEquiv.conj_apply]
  rw [hr]
  exact conjE_commute ((Col.formGSD C Λ).res h) hc.symm

end Tr

section Inst

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}

abbrev rowPts (mu : Tup X.F X.E X.K S) :
    Col.DecoPts (Col.mtildeKGSD W Ch sel mu) X.E (R.N R.m - 1) ∅ (Col.rowSG Pr sel mu) := formPts _ _

abbrev liftPts (mu : Tup X.F X.E X.K S) (j : ℕ) :
    Col.DecoPts (Col.mtKGSD W Ch sel mu j) X.E R.nV ∅ (Col.rowSG Pr sel mu) := formPts _ _

structure ColHyp (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
    (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E))) : Prop where

  conj : IsConjAt v0

  irr : ∀ χ ∈ Xg, IsAbsIrrChar χ

  commR : ∀ τ : TupF TU, Col.HeckeComm (rowPts W Ch sel τ.1) S0

  splitR : ∀ τ : TupF TU, Col.HeckeFieldsIn (rowPts W Ch sel τ.1) S0

  commL : ∀ (j : Fin R.m) (τ : TupF TU), Col.HeckeComm (liftPts W Ch sel τ.1 (j.1 + 1)) S0

  splitL : ∀ (j : Fin R.m) (τ : TupF TU), Col.HeckeFieldsIn (liftPts W Ch sel τ.1 (j.1 + 1)) S0

theorem exists_isConjAt (hX : X.Ok) : ∃ v0 : InfinitePlace X.K, IsConjAt v0 := by
  obtain ⟨σ₀, h⟩ := hX.conjK
  refine ⟨InfinitePlace.mk σ₀, ?_⟩
  intro a
  rcases InfinitePlace.embedding_mk_eq σ₀ with h1 | h1
  · rw [h1]
    exact h a
  · rw [h1, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, h a]

variable (hX : X.Ok) (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)

theorem colFam_rows_ok (commR : ∀ τ : TupF TU, Col.HeckeComm (rowPts W Ch sel τ.1) S0)
    (splitR : ∀ τ : TupF TU, Col.HeckeFieldsIn (rowPts W Ch sel τ.1) S0) (τ : TupF TU) :
    ((colFam W Ch sel hX v0 TU Xg S0 xiVal).R τ).Ok 1 where
  good := Col.MtildeKCSD_good W Ch sel τ.1 hX _
  hrat := Col.CSDRat.H_mem _ (Col.MtildeKCSD_rat W Ch sel τ.1 hX _)
    (Col.csd_hasRatBasis _ (Col.MtildeKCSD_rat W Ch sel τ.1 hX _))
  hpos := fun v => (Col.mtildeK_rat W Ch sel τ.1 hX).posH _ v
  act := Col.unipotentActionForms_good W Ch sel τ.1 hX _
  actRat := Col.unipotentActionForms_rational W Ch sel τ.1 hX _
  comm := heckeCSD_comm _ _ _ _ _ (commR τ)
  split := heckeCSD_split _ _ _ _ _ (splitR τ)
  opG := fun i g => heckeCSD_comm_trRep _ _ _ _ _ _ _ i g
  blocks := Col.blockOk_firstValB (fun j (P : ↥(offSub ∅ Pr.vGs (Col.rowSG Pr sel τ.1) S0)) =>
      Ch.muVal j P.1.1 * xiVal τ.1 P.1.1) (q := fun P => Col.SplitOff.q P.1) R.r R.t_odd.pos
    (by have := R.two_le_m; omega) (fun P => Col.SplitOff.q_ne_zero P.1)
  q_pos := fun P => Nat.pos_of_ne_zero (Col.SplitOff.q_ne_zero P.1)
  pl_inj := Subtype.val_injective

theorem colFam_lifts_ok (commL : ∀ (j : Fin R.m) (τ : TupF TU), Col.HeckeComm (liftPts W Ch sel τ.1 (j.1 + 1)) S0)
    (splitL : ∀ (j : Fin R.m) (τ : TupF TU), Col.HeckeFieldsIn (liftPts W Ch sel τ.1 (j.1 + 1)) S0)
    (j : Fin R.m) (τ : TupF TU) :
    ((colFam W Ch sel hX v0 TU Xg S0 xiVal).L j τ).Ok 1 where
  good := Col.MtKCSD_good W Ch sel τ.1 hX (j.1 + 1) _
  hrat := Col.CSDRat.H_mem _ (Col.MtKCSD_rat W Ch sel τ.1 hX (j.1 + 1) _)
    (Col.csd_hasRatBasis _ (Col.MtKCSD_rat W Ch sel τ.1 hX (j.1 + 1) _))
  hpos := fun v => (Col.mtK_rat W Ch sel τ.1 hX (j.1 + 1)).posH _ v
  act := Col.unipotentActionClassSum_good W Ch sel τ.1 hX (j.1 + 1) _
  actRat := Col.unipotentActionClassSum_rational W Ch sel τ.1 hX (j.1 + 1) _
  comm := heckeCSD_comm _ _ _ _ _ (commL j τ)
  split := heckeCSD_split _ _ _ _ _ (splitL j τ)
  opG := fun i g => heckeCSD_comm_trRep _ _ _ _ _ _ _ i g
  blocks := Col.blockOk_firstValA (fun (P : ↥(offSub ∅ Pr.vGs (Col.rowSG Pr sel τ.1) S0)) =>
      Ch.muVal j P.1.1 * xiVal τ.1 P.1.1) (fun P => Ch.etaVal P.1.1) (q := fun P => Col.SplitOff.q P.1) R.r
    R.t_odd.pos (fun P => Col.SplitOff.q_ne_zero P.1)
  q_pos := fun P => Nat.pos_of_ne_zero (Col.SplitOff.q_ne_zero P.1)
  pl_inj := Subtype.val_injective

theorem colFam_ok (hH : ColHyp W Ch sel v0 TU Xg S0) : (colFam W Ch sel hX v0 TU Xg S0 xiVal).Ok 1 where
  conj := hH.conj
  tup_fin := tupF_finite TU
  irr := hH.irr
  what₂ := colFam_rows_ok W Ch sel hX v0 TU Xg S0 xiVal hH.commR hH.splitR
  lifts := colFam_lifts_ok W Ch sel hX v0 TU Xg S0 xiVal hH.commL hH.splitL

theorem colFam_okH_rows (τ : TupF TU) : ((colFam W Ch sel hX v0 TU Xg S0 xiVal).R τ).OkH where
  rat := fun i a b => heckeCSD_rat _ _ _ _ _ (Col.mtildeK_rat W Ch sel τ.1 hX) i a b
  adj := fun i => heckeCSD_adj _ _ _ _ _ i

theorem colFam_okH_lifts (j : Fin R.m) (τ : TupF TU) : ((colFam W Ch sel hX v0 TU Xg S0 xiVal).L j τ).OkH where
  rat := fun i a b => heckeCSD_rat _ _ _ _ _ (Col.mtK_rat W Ch sel τ.1 hX (j.1 + 1)) i a b
  adj := fun i => heckeCSD_adj _ _ _ _ _ i

theorem colFam_okH :
    (∀ τ, ((colFam W Ch sel hX v0 TU Xg S0 xiVal).R τ).OkH) ∧
      ∀ j τ, ((colFam W Ch sel hX v0 TU Xg S0 xiVal).L j τ).OkH :=
  ⟨fun τ => colFam_okH_rows W Ch sel hX v0 TU Xg S0 xiVal τ,
    fun j τ => colFam_okH_lifts W Ch sel hX v0 TU Xg S0 xiVal j τ⟩

theorem colFam_typesSep : (colFam W Ch sel hX v0 TU Xg S0 xiVal).TypesSep := by
  unfold colFam
  refine FamIn.typesSep_of' (A := colIn W Ch sel hX v0 TU Xg S0 xiVal) (fun P => ?_) (fun P => ?_)
  · first
      | exact Col.SplitOff.q_ne_zero _
      | exact_mod_cast Col.SplitOff.q_ne_zero _
  · exact heckeCSD_zero _ _ _ _ _ P

end Inst

section Xi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

def IsUnifIdele (P : HeightOneSpectrum (𝓞 E)) (u : (AfE F E)ˣ) : Prop :=
  ∃ (v : HeightOneSpectrum (𝓞 F)) (hu : (u : AfE F E) ∈ RInt F E) (b : 𝓞 E),
    P.asIdeal.under (𝓞 F) = v.asIdeal ∧ u ∈ suppAt E v ∧ b ∈ P.asIdeal ∧ b ∉ P.asIdeal ^ 2 ∧
    (⟨(u : AfE F E), hu⟩ : RInt F E) - toRInt F E b ∈ (P.asIdeal ^ 2).map (toRInt F E) ∧
    ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → (⟨(u : AfE F E), hu⟩ : RInt F E) - 1 ∈ P'.asIdeal.map (toRInt F E)

open Classical in

def unifVal (ξ : Chr F E L) (P : HeightOneSpectrum (𝓞 E)) : Lˣ :=
  if h : ∃ u, IsUnifIdele (F := F) P u then ξ h.choose else 1

theorem unifVal_of (ξ : Chr F E L) (P : HeightOneSpectrum (𝓞 E)) (h : ∃ u, IsUnifIdele (F := F) P u) :
    unifVal ξ P = ξ h.choose ∧ IsUnifIdele P h.choose := by
  refine ⟨?_, h.choose_spec⟩
  rw [unifVal, dif_pos h]

theorem tilde_character_norm_quotient (σ : E →ₐ[F] E) (ξ : Chr F E L) (hξ : (h90 σ).ker ≤ ξ.ker) (u : (AfE F E)ˣ) :
    tilde σ ξ ((h90 σ).rangeRestrict u) = ξ u := by
  unfold tilde
  rw [dif_pos hξ]
  first
    | exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ u
    | exact MonoidHom.liftOfSurjective_comp_apply _ _ _ u
    | simp

theorem det_twist_of_norm_quotient (σ : E →ₐ[F] E) (ξ : Chr F E L) (hξ : (h90 σ).ker ≤ ξ.ker) {n : ℕ}
    (g : GL (Fin n) (AfE F E)) (u : (AfE F E)ˣ) (hg : Matrix.GeneralLinearGroup.det g = h90 σ u) :
    detTw σ ξ g = ξ u := by
  have hmem : Matrix.GeneralLinearGroup.det g ∈ (h90 σ).range := ⟨u, hg.symm⟩
  unfold detTw
  rw [dif_pos hmem]
  have hsub : (⟨_, hmem⟩ : (h90 σ).range) = (h90 σ).rangeRestrict u := Subtype.ext hg
  rw [hsub, tilde_character_norm_quotient σ ξ hξ u]

end Xi

section XiCol

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}

def xiVal (τ : Tup X.F X.E X.K S) (P : HeightOneSpectrum (𝓞 X.E)) : X.Kˣ := unifVal (τ : Chr X.F X.E X.K) P

variable (hX : X.Ok) (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))

def colInX : FamIn X.K (Col.G0 X.E Pr.vGs R.r) (Col.LevOff ∅ Pr.vGs S0) (TupF TU) R.m :=
  colIn W Ch sel hX v0 TU Xg S0 xiVal

theorem colInX_ok (hH : ColHyp W Ch sel v0 TU Xg S0) : (colInX W Ch sel hX v0 TU Xg S0).fam.Ok 1 :=
  colFam_ok W Ch sel hX v0 TU Xg S0 xiVal hH

theorem colInX_typesSep : (colInX W Ch sel hX v0 TU Xg S0).fam.TypesSep :=
  colFam_typesSep W Ch sel hX v0 TU Xg S0 xiVal

end XiCol

section LinkCol

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok) (v0 : InfinitePlace X.K)
  (TU : Finset (Tup X.F X.E X.K S)) (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))

open Formalism.L2.Col in

theorem division_height_bound_columns (hH : ColHyp W Ch sel v0 TU Xg S0)
    (P0 : Subgroup (Col.G0 X.E Pr.vGs R.r)) (ψ0 : P0 →* X.Kˣ) (P1 : Subgroup (Col.G0 X.E Pr.vGs R.r)) (ψ1 : P1 →* X.Kˣ)
    {P : LevFam X.E X.K R.r Pr.vGs} {m2 : ℕ} {Gc : ChGlob X R.m}
    {Sg : Set ℕ} (mu : (colInX W Ch sel hX v0 TU Xg S0).fam.base.Tup → Tup X.F X.E X.K Sg) (cst : ∀ t, LocCst X (rowSG Pr sel (mu t)))
    (L : ∀ t, ChIdx X Pr R (QE sel (mu t : Chr X.F X.E X.K))) (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) Gc m2)
    (hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (L t).β (m2 + 1))
    (hY : ∀ t x, YbHyp (R := R) sel (mu t) (cst t) (L t) (wd x) m2 (b t x))
    (Ak : ∀ t x, ChKer W Ch sel (mu t) (cst t) (L t) P (wd x) m2 (b t x) (hY t x))
    (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok) (hE : ∀ x, (evGSD W Ch sel (mu (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0) P (wd x)).Ok)
    (ev : ∀ (Zs : DefSub (colInX W Ch sel hX v0 TU Xg S0).fam.amb) t, (Fin (((colInX W Ch sel hX v0 TU Xg S0).side P1 ψ1 Zs).nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg P)
    (Sp : ∀ Zs : DefSub (colInX W Ch sel hX v0 TU Xg S0).fam.amb, SPer (colFace hX ((colInX W Ch sel hX v0 TU Xg S0).side P1 ψ1 Zs) Xg mu cst L hL hP Mem wd b hY Ak hF (ev Zs)))
    (Zsc : DefSub (colInX W Ch sel hX v0 TU Xg S0).fam.amb → IndefScale (colInX W Ch sel hX v0 TU Xg S0).fam.base) (C CH : ℝ)
    (Pk : IndefPkg (colInX W Ch sel hX v0 TU Xg S0).fam.amb
      (faceOf (colInX W Ch sel hX v0 TU Xg S0) P0 ψ0 P1 ψ1 (fun Zs => colFace hX ((colInX W Ch sel hX v0 TU Xg S0).side P1 ψ1 Zs) Xg mu cst L hL hP Mem wd b hY Ak hF (ev Zs)) Sp Zsc) C CH)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (Rn : RecNums (colInX W Ch sel hX v0 TU Xg S0).fam.base.J Pl) (x : Mem)
    (Nu : Submodule (𝓞 X.K) (Fin (ramDim W Ch hX (wd x)) → X.K)) (sg : HeightOneSpectrum (𝓞 X.K) → ℝ)
    (I : DivInputs Pk.core Rn x Nu sg)
    (hQ : ChainTie I.ch (memQ (A := Ak) (hF := hF) hE (x := x))) (h0 : FirstCols hE hQ) (hPL : LastPer hE hQ) :
    DivClauses Pk.core Rn x Nu sg ∧
      (∀ y : Fin (I.ch.c 0) → X.K,
        hQ.coL ((chainMat I.ch.Kj ⟨(memQ (A := Ak) (hF := hF) hE (x := x)).n + 1, by have := hQ.hmm; omega⟩).mulVec y) =
          colC (Ak (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0 x) (hF (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0 x) (hL (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0)
            (colOfCoord W Ch hX (wd x) fun i => y (Fin.cast I.ch.c0.symm i))) ∧
      ∀ (φ : Fin (ramDim W Ch hX (wd x)) → X.K) (F : Fin (((colInX W Ch sel hX v0 TU Xg S0).side P1 ψ1 Pk.Zs).nV (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0) → X.K),
        I.ch.PtL ((chainMat I.ch.Kj (Fin.last I.ch.mm)).mulVec fun i => φ (Fin.cast I.ch.c0 i)) F =
          colPerL (hP (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0) Xg (wd x) (ev Pk.Zs (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0)
            (colC (Ak (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0 x) (hF (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0 x) (hL (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0) (colOfCoord W Ch hX (wd x) φ)) F := by
  haveI := hX.cplxK
  exact division_height_bound (colInX W Ch sel hX v0 TU Xg S0) (colInX_ok W Ch sel hX v0 TU Xg S0 hH)
    (colInX_typesSep W Ch sel hX v0 TU Xg S0) P0 ψ0 P1 ψ1 hX Xg mu cst L hL hP Mem wd b hY Ak hF hE ev Sp Zsc C CH Pk
    Rn x Nu sg I hQ h0 hPL

end LinkCol

end Formalism.L2.DIV
