import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Formalism.LocalToGlobal.Columns.ToHLatLemmas

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

noncomputable section

namespace GlobalTheory.ColFirstIso

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S S' : GSD K}

def clEquiv (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D) (hs : ∀ g d, eD (g • d) = eG g • eD d) : S'.Cl ≃ S.Cl :=
  Quotient.congr eD fun a b => by
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨eG g, (hs g b).symm⟩
    · rintro ⟨g, hg⟩
      refine ⟨eG.symm g, eD.injective ?_⟩
      have hg' : g • eD b = eD a := hg
      show eD (eG.symm g • b) = eD a
      rw [hs, MulEquiv.apply_symm_apply, hg']

theorem clEquiv_cls (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D) (hs : ∀ g d, eD (g • d) = eG g • eD d) (d : S'.D) :
    clEquiv eG eD hs (S'.cls d) = S.cls (eD d) := rfl

theorem card_stab (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D) (hs : ∀ g d, eD (g • d) = eG g • eD d) (d : S'.D) :
    Nat.card (MulAction.stabilizer S'.G d) = Nat.card (MulAction.stabilizer S.G (eD d)) := by
  refine Nat.card_congr (eG.toEquiv.subtypeEquiv fun g => ?_)
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  show _ ↔ eG g • eD d = eD d
  rw [← hs, eD.injective.eq_iff]

theorem ipAt_transport (R : S.Rat) (h : S.Ok) (h' : S'.Ok) (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D)
    (hs : ∀ g d, eD (g • d) = eG g • eD d) (v : InfinitePlace K) (φ : S.EqFun) (φ' : S'.D → S'.V)
    (hp : ∀ d, S'.pairAt v (φ' d) (φ' d) = S.pairAt v ((φ : S.D → S.V) (eD d)) ((φ : S.D → S.V) (eD d))) :
    S'.ipAt h' v φ' φ' = S.ipAt h v φ φ := by
  let e := clEquiv eG eD hs
  let s : S.Sec :=
    { rep := fun c => eD (S'.outSec.rep (e.symm c))
      spec := fun c => by
        rw [← clEquiv_cls eG eD hs, S'.outSec.spec]
        exact e.apply_symm_apply c }
  rw [R.ipAt_indep h s v φ φ]
  let _ := h.fintypeCl
  let _ := h'.fintypeCl
  unfold GSD.ipAt
  refine Fintype.sum_equiv e _ _ fun c => ?_
  have h1 : s.rep (e c) = eD (S'.outSec.rep c) := by
    show eD (S'.outSec.rep (e.symm (e c))) = _
    rw [e.symm_apply_apply]
  rw [h1, S'.wt_eq h' S'.outSec c, card_stab eG eD hs, hp]

end Generic

section Frames

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

def decoEquiv (hQ : Q = ∅) : DecoF X.E n ST SG Q ≃ DecoSet X.E n ST SG where
  toFun := DecoF.deco
  invFun d := ⟨(d, fun _ => 1), fun P => absurd P.2 (by simp [hQ])⟩
  left_inv p := Subtype.ext (Prod.ext rfl (funext fun P => absurd P.2 (by simp [hQ])))
  right_inv _ := rfl

def grpEquiv (hQ : Q = ∅) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) : FrmG Λ Θ ≃* FormG Λ where
  toFun g := (g.1, g.2.1)
  invFun g := (g.1, g.2, 1)
  left_inv g := Prod.ext rfl (Prod.ext rfl (Subtype.ext (funext fun P => absurd P.2 (by simp [hQ]))))
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem ipAt_frm (hQ : Q = ∅) (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ Λ' : LevFam X.E X.K n SG) (hΛ : Λ' = Λ)
    (Θ : LevQFam X.E X.K n Q) (R : (formGSD C Λ).Rat) (h : (formGSD C Λ).Ok)
    (h' : (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ' Θ).Ok) (v : InfinitePlace X.K) (φ : (formGSD C Λ).EqFun) :
    (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ' Θ).ipAt h' v (fun p => (φ : _ → C.V) (DecoF.deco p))
      (fun p => (φ : _ → C.V) (DecoF.deco p)) = (formGSD C Λ).ipAt h v φ φ := by
  subst hΛ
  exact ipAt_transport R h h' (grpEquiv hQ Λ' Θ) (decoEquiv hQ) (fun _ _ => rfl) v φ _ fun _ => rfl

end Frames

theorem qe_one {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} :
    QE sel ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
  have h : Qprime ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
    change Qprime (1 : Chr X.F X.E X.K) = ∅
    ext v
    simp [Qprime, MonoidHom.ker_one]
  unfold QE
  split_ifs with hf
  · rw [(Set.Finite.toFinset_eq_empty (h := hf)).2 h]
    rfl
  · rfl

theorem colsIn_isometry : ∀ (X : Fields) (hX : X.Ok) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (hL : I.Ok Ch sel mu cst G m2) (u : Pr.Word) (h : (chF W sel mu I u 0).Ok), mu = 1 → (∀ v, IsUnit ((MramH W Ch hX u).X v).det) ∧ ∀ (v : InfinitePlace X.K) (x : Fin (ramDim W Ch hX u) → X.K), ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K (Fin (ramDim W Ch hX u))) (MramH W Ch hX u).X v x ^ 2 : ℝ) : ℂ) = famIpAt (chF W sel mu I u 0) h v (colsIn W Ch hX sel mu cst I hL u x) (colsIn W Ch hX sel mu cst I hL u x) := by
  intro X hX Pr R W Ch sel Sg mu cst I G m2 hL u h hmu
  refine ⟨(colPosH W Ch hX u 0).frameOK_sub (MramV W Ch u) (MramL W Ch u), fun v x => ?_⟩
  have hQ : QE sel (mu : Chr X.F X.E X.K) = ∅ := by
    subst hmu
    exact qe_one sel
  obtain ⟨b, hb⟩ := hL.zero_uniq
  have h1 : famIpAt (chF W sel mu I u 0) h v (colsIn W Ch hX sel mu cst I hL u x) (colsIn W Ch hX sel mu cst I hL u x) =
      (colGSD W Ch u 0).ipAt (colOk W Ch hX u 0) v (colOfCoord W Ch hX u x) (colOfCoord W Ch hX u x) := by
    unfold famIpAt
    rw [Fintype.sum_eq_single b fun b' hb' => absurd (hb b') hb']
    exact ipAt_frm hQ (colVal W u 0 (Pr.vT u) Pr.vGs) (colLev Ch 0) (I.levG 0 b) (hL.zero_G b) (I.levQ 0 b)
      (colRat W Ch hX u 0) (colOk W Ch hX u 0) (h b) v (colOfCoord W Ch hX u x)
  rw [h1, ← (colRat W Ch hX u 0).maj_eq]
  have h2 := (colPosH W Ch hX u 0).sub_maj (MramV W Ch u) v ((ramBas W Ch hX u).equivFun.symm x)
    ((ramBas W Ch hX u).equivFun.symm x)
  rw [thl_majAt_coord, LinearEquiv.apply_symm_apply] at h2
  refine Eq.trans ?_ h2
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity)), Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rfl

end GlobalTheory.ColFirstIso
