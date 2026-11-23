import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertNeighboursLiftsDoubleCosetTranslates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharEqOneInertPrimeOffLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdentityIntegralUnitaryFrameCoordinatesOfUnitGra
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.RowAd.Inert

theorem conj_heckeFamI_apply {X : Formalism.L2.Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (C : Formalism.L2.Col.CoefPk X n (Formalism.L2.Col.DecoSet X.E n ST SG)) (Λ : Formalism.L2.Col.LevFam X.E X.K n SG)
    (hS : (Formalism.L2.Col.formGSD C Λ).Ok) (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (y : Formalism.L2.Col.LevOffI ST SG S0 × List ℕ)
    (f : ((Formalism.L2.Col.formGSD C Λ).toCSD hS).Forms) (d : Formalism.L2.Col.DecoSet X.E n ST SG) :
    ((((Formalism.L2.Col.formGSD C Λ).res hS).symm ((((Formalism.L2.Col.formGSD C Λ).res hS).conj
      (Formalism.L2.Col.heckeFamI (Formalism.L2.DIV.formPts C Λ) S0 y)) f) : (Formalism.L2.Col.formGSD C Λ).EqFun) :
        Formalism.L2.Col.DecoSet X.E n ST SG → C.V) d =
      ∑ e ∈ d.inertNb y.1.1.asIdeal y.2, ((((Formalism.L2.Col.formGSD C Λ).res hS).symm f : (Formalism.L2.Col.formGSD C Λ).EqFun) :
        Formalism.L2.Col.DecoSet X.E n ST SG → C.V) e := by
  rw [LinearEquiv.conj_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [Formalism.L2.Col.heckeFamI_formPts_apply]
  rfl

theorem colIn3_heckeRI_apply {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R)
    (Ch : Formalism.L2.Col.Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
    (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
    (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
    (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
    (trIv : Fin R.m → (Formalism.L2.Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Formalism.L2.Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)
    (τ : TupF TU) (q : ↑((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).okI τ) × List ℕ)
    (f : ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.MtildeCSD τ).Forms) (d : (Formalism.L2.Col.mtildeKGSD W Ch sel τ.1).D) :
    (((Formalism.L2.Col.mtildeKGSD W Ch sel τ.1).res (Formalism.L2.Col.mtildeKOk W Ch sel τ.1 hX)).symm
      ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).heckeRI τ q f)).1 d =
      ∑ e ∈ Formalism.L2.Col.DecoSet.inertNb q.1.1.1.asIdeal q.2 d,
        (((Formalism.L2.Col.mtildeKGSD W Ch sel τ.1).res (Formalism.L2.Col.mtildeKOk W Ch sel τ.1 hX)).symm f).1 e :=
  conj_heckeFamI_apply _ _ (Formalism.L2.Col.mtildeKOk W Ch sel τ.1 hX) S0 (offSubI.lev q.1, q.2) f d

theorem opEq (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (t : TupU I U) (cX : CoefA X.toD7.sp.X') {J : Subgroup (Bridge.Gf X.toD7.sp.X')} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ J χ)
    (hP : ReadsDeco X I hX Xg tr cX t P)
    (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (R : Finset (Bridge.Gf X.toD7.sp.X'))
    (hN : ∀ (M : Type) [AddCommMonoid M] (ψ : Formalism.L2.Col.DecoSet X.B.fields.E (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) → M) (g : Bridge.Gf X.toD7.sp.X'),
        ∑ a ∈ R, ψ (decoAd X I t (g * a)) =
          ∑ e ∈ Formalism.L2.Col.DecoSet.inertNb (q.1.1 : PlI X.B px).1.asIdeal q.2 (decoAd X I t g : Formalism.L2.Col.DecoSet X.B.fields.E (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)), ψ e)
    (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) :
    P.ext ((((famR X I hX U Xg tr).heckeRI t q f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) :
        ((famR X I hX U Xg tr).A.MtildeCSD t).Cl → ((famR X I hX U Xg tr).A.MtildeCSD t).V)) =
      Bridge.dcOp R (P.ext (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Cl → ((famR X I hX U Xg tr).A.MtildeCSD t).V)) := by
  obtain ⟨m, hm⟩ := hP
  funext g
  have e1 := hm ((famR X I hX U Xg tr).heckeRI t q f) g
  have e2 := colIn3_heckeRI_apply (X := X.B.fields) (Pr := X.B.primes px) X.B.wts I.Ch I.sel hX (InfinitePlace.mk X.B.embLL) (tuOf I U)
    Xg ∅ (xiValOf I) tr t q f (decoAd X I t g)
  have e3 := hN _ (fun e => m ((((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1 e)) g
  refine e1.trans ?_
  refine (congrArg m e2).trans ?_
  refine (map_sum m _ _).trans ?_
  refine e3.symm.trans ?_
  exact (Finset.sum_congr rfl (fun a _ => hm f (g * a))).symm

theorem chi_eq_one {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (Q : Pl D.host.E)
    (hQc : Formalism.L2.Col.conjPrime₂ Q = Q) (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ Q) (j : (levEnv V β L).J)
    (hj : IsLocElt V Q (j : Bridge.Gf V)) : (levEnv V β L).χ j = 1 := by
  have e : (levEnv V β L).χ j = Formalism.L2.DIV.levFn β (flag1L L) (Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1) := rfl
  have hm : Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1 ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flag1L L) := j.2
  have hSt := Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hm)
  have hloc := LiftInertChi.locAt_of_isLocElt V _ _ hj
  have hconj : Formalism.DivisionValues.conjPl Q = Q := GlobalTheory.InertNbr.conjPl_eq_of_conjP hQc
  have hred : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q →
      Formalism.L2.DIV.redFn β PP (Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1) = 1 := fun PP hPP =>
    LiftInertChi.redFn_eq_one_of_locAt _ _ hSt _ hloc PP (fun hu => by
      rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with h | h
      · exact hoff PP hPP h
      · exact hoff PP hPP (h.trans hconj))
  have hr1 : Formalism.L2.DIV.rTup β (flag1L L) (Formalism.UG.bc (swapAE D) (j : Bridge.Gf V).1) = 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn _ PP.1 _) = 1
    rw [hred PP.1 (Or.inl PP.2)]
    exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  rw [e]
  unfold Formalism.L2.DIV.levFn
  rw [hr1, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hPP
    rw [hred PP (Or.inr hPP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hPP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [hred PP (Or.inl hPP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]

theorem gram_eq_one (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hI : I.Ok) : X.toD7.sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  change X.B.sp.X'.gram = 1
  rw [h2]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

theorem off_level (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) {U : Set I.ι}
    {L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)} (hL : LevOf X I U L) (t : TupU I U) (Q : PlI X.B px) :
    ∀ PP, PP ∈ (L.datXt t).Pg ∨ PP ∈ (L.datXt t).Q → PP ≠ Q.1 := by
  rintro PP (h | h) rfl
  · have h' : Q.1 ∈ L.Pg := h
    rw [hL.Pg] at h'
    exact Q.2.2.2 (Or.inr h')
  · refine (hL.is.Q_pl t _ h).2 _ h ?_
    exact GlobalTheory.InertNbr.isConjPl_self (D := X.toD7) Q.2.1

theorem inert_neighbours (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) {U : Set I.ι}
    {L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)} (hI : I.Ok) (hL : LevOf X I U L) (t : TupU I U) (Q : PlI X.B px)
    (hQ : Q.1 ∉ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) (s : List ℕ) (hs : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank s) :
    ∃ (x : Bridge.Gf X.toD7.sp.X') (A : Finset (Bridge.Gf X.toD7.sp.X')), IsLabElt X.toD7.sp.X' Q.1 (labIn X.toD7.sp.X'.rank s) x ∧
      (∀ a ∈ A, IsLocElt X.toD7.sp.X' Q.1 a) ∧ Bridge.IsDC (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J x A ∧
      ∀ (M : Type) [AddCommMonoid M] (ψ : Formalism.L2.Col.DecoSet X.B.fields.E (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) → M) (g : Bridge.Gf X.toD7.sp.X'),
        ∑ a ∈ A, ψ (decoAd X I t (g * a)) =
          ∑ e ∈ Formalism.L2.Col.DecoSet.inertNb Q.1.asIdeal s (decoAd X I t g : Formalism.L2.Col.DecoSet X.B.fields.E (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)), ψ e := by
  obtain ⟨m, hm⟩ := hL.is.βX
  rw [one_pow] at hm
  have hβ := hL.beta.2
  rw [hβ] at hm
  have key := GlobalTheory.InertNbr.exists_hecke X.toD7.sp.X' (n := X.B.R.N X.B.R.m - 1) (rank_X' X).symm L.ΛX (L.datXt t) hm Q.1 Q.2.1
    (off_level X I hL t Q) hQ 1 1 (one_mem _)
    (fun x => by
      rw [gram_eq_one X I hI, one_mul, inv_one, mul_one]
      exact (LiftBrg.castGL_mem_UA_one X.toD7.sp.cm (rank_X' X).symm x).symm)
    (one_mem _) (one_mem _) s hs
  simp only [inv_one, one_mul, mul_one] at key
  rw [hβ]
  exact key

theorem exists_inertTie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      Nonempty (Bridge.HeckeTie (Bridge.ratF X.toD7.sp.X') P ((famR X I hX U Xg tr).heckeRI t)
        (fun i => Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank i.2)
        (fun i => IsLabElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1 (labIn X.toD7.sp.X'.rank i.2))
        fun i => IsLocElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1) := by
  intro X px I hX U Xg tr L eG hI _ hL _ cX gramR c0R _ _ _ _ t P hP
  classical
  have hN := fun (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (hq : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank q.2) =>
    inert_neighbours X I hI hL t (q.1.1 : PlI X.B px) (fun h => q.1.2 (Or.inr h)) q.2 hq
  exact ⟨{
    hx := fun q => if hq : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank q.2 then (hN q hq).choose else 1
    hA := fun q => if hq : Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank q.2 then (hN q hq).choose_spec.choose else ∅
    hx_ok := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.1
    hA_loc := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.2.1
    chi_loc := fun q _ j hj => chi_eq_one X.toD7.sp.X' L.βX (L.datXt t) (q.1.1 : PlI X.B px).1 (q.1.1 : PlI X.B px).2.1
      (off_level X I hL t (q.1.1 : PlI X.B px)) j hj
    hDC := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.2.2.1
    op_eq := fun q hq f => by
      simp only [dif_pos hq]
      exact opEq X I hX U Xg tr t cX P hP q _ (hN q hq).choose_spec.choose_spec.2.2.2 f }⟩

end GlobalTheory.Mem.R3.RowAd.Inert
