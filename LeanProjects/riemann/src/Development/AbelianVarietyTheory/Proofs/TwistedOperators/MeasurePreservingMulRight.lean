import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSizesNR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPermOfCardFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitVacuumStandardLatticesDefinitePair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefNodeIsV
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMeasureUniformInTupleOfThetaLiftScalar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsRealFnNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section RealPoint

variable {D : D7}

def infMatHom (V : HSp D) (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) : GA D V →* Matrix (Fin V.rank) (Fin V.rank) ℂ where
  toFun := infMat D.sp.cm.sig V.gram φ
  map_one' := GlobalTheory.PointAtPlaceHom.infMat_one V φ
  map_mul' := GlobalTheory.PointAtPlaceHom.infMat_mul V φ

theorem list_prod_map_ite {α M : Type} [Monoid M] [DecidableEq α] (a : M) (σ : α) :
    ∀ l : List α, l.Nodup → σ ∈ l → (l.map fun ρ => if ρ = σ then a else 1).prod = a
  | [], _, h => by simp at h
  | x :: l, hn, h => by
    rw [List.map_cons, List.prod_cons]
    rw [List.nodup_cons] at hn
    by_cases hx : x = σ
    · subst hx
      rw [if_pos rfl, List.prod_eq_one, mul_one]
      intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      exact if_neg fun (e : z = x) => hn.1 (e ▸ hz)
    · rw [if_neg hx, one_mul]
      exact list_prod_map_ite a σ l hn.2 ((List.mem_cons.1 h).resolve_left fun e => hx e.symm)

def IsRealAll (θ : InfFam D) (V : HSp D) (M : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : GA D V) : Prop :=
  h ∈ GinfC V ∧ ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) h = M ρ

variable {θ : InfFam D} {V : HSp D}

theorem exists_isRealAll (hθ : IsInfFam θ) (M : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hM : ∀ ρ, M ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ)) : ∃ h, IsRealAll θ V M h := by
  classical
  let l := (Finset.univ : Finset D.what₂.Tau).toList
  refine ⟨(l.map fun ρ => atTau θ V ρ (M ρ)).prod, ?_, fun σ => ?_⟩
  · refine Subgroup.list_prod_mem (GinfC V) fun x hx => ?_
    obtain ⟨ρ, -, rfl⟩ := List.mem_map.1 hx
    exact GlobalTheory.PointAtPlaceHom.atTau_mem V ρ (M ρ)
  · have e := map_list_prod (infMatHom V (θ σ)) (l.map fun ρ => atTau θ V ρ (M ρ))
    rw [List.map_map] at e
    have key : ((infMatHom V (θ σ)) ∘ fun ρ => atTau θ V ρ (M ρ)) = fun ρ => if ρ = σ then M σ else 1 := by
      funext ρ
      have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V ρ (hM ρ)
      by_cases hρ : ρ = σ
      · subst hρ
        rw [if_pos rfl]
        exact hs.2.1
      · rw [if_neg hρ]
        exact hs.2.2 σ (Ne.symm hρ)
    rw [key] at e
    exact e.trans (list_prod_map_ite _ _ l (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ _)))

theorem IsRealAll.unique (hθ : IsInfFam θ) {M : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {h h' : GA D V}
    (hh : IsRealAll θ V M h) (hh' : IsRealAll θ V M h') : h = h' := by
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have k : ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) (h' * h⁻¹) = 1 := fun ρ => by
    rw [GlobalTheory.PointAtPlaceHom.infMat_mul, hh'.2 ρ, ← hh.2 ρ, ← GlobalTheory.PointAtPlaceHom.infMat_mul, mul_inv_cancel,
      GlobalTheory.PointAtPlaceHom.infMat_one]
  have hc : IsAtTau θ V τ 1 (h' * h⁻¹) := ⟨mul_mem hh'.1 (inv_mem hh.1), k τ, fun ρ _ => k ρ⟩
  have h1 : IsAtTau θ V τ 1 (1 : GA D V) :=
    ⟨one_mem _, GlobalTheory.PointAtPlaceHom.infMat_one V _, fun _ _ => GlobalTheory.PointAtPlaceHom.infMat_one V _⟩
  have e := (GlobalTheory.PointAtPlace.existsUnique_isAtTau V τ θ hθ 1 (GlobalTheory.PointAtPlaceHom.one_mem_UH _)).unique hc h1
  exact (mul_inv_eq_one.1 e).symm

variable (θ V) in
open Classical in

def realAll (M : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  if h : ∃ x, IsRealAll θ V M x then h.choose else 1

theorem realAll_mem (M : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : realAll θ V M ∈ GinfC V := by
  unfold realAll
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_mem _

theorem realAll_spec (hθ : IsInfFam θ) {M : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hM : ∀ ρ, M ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ)) : IsRealAll θ V M (realAll θ V M) := by
  have h := exists_isRealAll hθ M hM
  unfold realAll
  rw [dif_pos h]
  exact h.choose_spec

theorem realAll_eq (hθ : IsInfFam θ) {M : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hM : ∀ ρ, M ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ)) {h : GA D V} (hh : IsRealAll θ V M h) : realAll θ V M = h :=
  (realAll_spec hθ hM).unique hθ hh

theorem compAt_realAll (hθ : IsInfFam θ) {M : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hM : ∀ ρ, M ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ)) (ρ : D.what₂.Tau) : compAt θ ρ (mt V (realAll θ V M)) = M ρ :=
  (realAll_spec hθ hM).2 ρ

theorem realAll_one (hθ : IsInfFam θ) : realAll θ V 1 = 1 :=
  realAll_eq hθ (fun _ => GlobalTheory.PointAtPlaceHom.one_mem_UH _) ⟨one_mem _, fun _ => GlobalTheory.PointAtPlaceHom.infMat_one V _⟩

theorem realAll_mul (hθ : IsInfFam θ) {M M' : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hM : ∀ ρ, M ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ)) (hM' : ∀ ρ, M' ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ)) :
    realAll θ V (M * M') = realAll θ V M * realAll θ V M' := by
  refine realAll_eq hθ (fun ρ => GlobalTheory.PointAtPlaceHom.mul_mem_UH (hM ρ) (hM' ρ))
    ⟨mul_mem (realAll_spec hθ hM).1 (realAll_spec hθ hM').1, fun ρ => ?_⟩
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, (realAll_spec hθ hM).2 ρ, (realAll_spec hθ hM').2 ρ]

open Classical in

theorem realAll_eq_atTau_mul (hθ : IsInfFam θ) {M : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hM : ∀ ρ, M ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ)) (τ : D.what₂.Tau) :
    realAll θ V M = atTau θ V τ (M τ) * realAll θ V (Function.update M τ 1) := by
  classical
  have hM1 : ∀ ρ, Function.update M τ 1 ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := fun ρ => by
    by_cases h : ρ = τ
    · subst h
      rw [Function.update_self]
      exact GlobalTheory.PointAtPlaceHom.one_mem_UH _
    · rw [Function.update_of_ne h]
      exact hM ρ
  have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ (hM τ)
  refine realAll_eq hθ hM ⟨mul_mem (GlobalTheory.PointAtPlaceHom.atTau_mem V τ _) (realAll_spec hθ hM1).1, fun ρ => ?_⟩
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, (realAll_spec hθ hM1).2 ρ]
  by_cases h : ρ = τ
  · subst h
    rw [hs.2.1, Function.update_self, Matrix.mul_one]
  · rw [hs.2.2 ρ h, Function.update_of_ne h, Matrix.one_mul]

end RealPoint

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Unitary

theorem conj_mem_UH {n : ℕ} {G B u : Matrix (Fin n) (Fin n) ℂ} (hB : Bᴴ * G * B = 1)
    (hu : u ∈ Matrix.unitaryGroup (Fin n) ℂ) : B * u * B⁻¹ ∈ Formalism.QuantumDeterminants.UH G := by
  have hd : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
  have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h2 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ hd
  have hu' : uᴴ * u = 1 := Matrix.mem_unitaryGroup_iff'.1 hu
  have hG : G = (B⁻¹)ᴴ * B⁻¹ := by
    calc G = (B * B⁻¹)ᴴ * G * (B * B⁻¹) := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      _ = (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hB, Matrix.mul_one]
  show (B * u * B⁻¹)ᴴ * G * (B * u * B⁻¹) = G
  rw [hG]
  calc (B * u * B⁻¹)ᴴ * ((B⁻¹)ᴴ * B⁻¹) * (B * u * B⁻¹)
      = (B⁻¹)ᴴ * (uᴴ * ((B⁻¹ * B)ᴴ * (B⁻¹ * B)) * u) * B⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (B⁻¹)ᴴ * B⁻¹ := by rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hu', Matrix.mul_one]

end Unitary

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def PosOnb (W : G.Weil) (X : Node) : Prop :=
  ∀ τ, (W.onb X τ)ᴴ * gramAt D (G.V X) τ * W.onb X τ = 1

theorem posOnb_of_sig (W : G.Weil) {X : Node} (hX : DefNode D.R.m X) (h0 : ∀ τ, ((G.V X).sig (tauE D τ)).2 = 0) :
    PosOnb W X := fun τ => by
  obtain ⟨ε, h1, -⟩ := W.onb_is X hX.inRange τ
  have hc := GlobalTheory.GridJoin.card_false_of_gram (hX.sigOK G) τ h1
  rw [h0 τ, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hc
  have hJ : Formalism.REAL.Jm ε = 1 := by
    rw [Formalism.REAL.Jm, ← Matrix.diagonal_one]
    congr 1; funext a
    have := hc (Finset.mem_univ a)
    cases hε : ε a <;> simp_all
  rw [h1, hJ]

theorem posOnb_of_defNode (W : G.Weil) (μ0 : T) (hL : L.Is μ0) {X : Node} (hX : DefNode D.R.m X) : PosOnb W X :=
  posOnb_of_sig W hX fun τ => by rw [(defNode_isV G μ0 hL X hX).sig (tauE D τ)]

def castU {n n' : ℕ} (h : n = n') : Matrix.unitaryGroup (Fin n) ℂ →* Matrix.unitaryGroup (Fin n') ℂ := by
  subst h
  exact MonoidHom.id _

theorem castU_coe {n n' : ℕ} (h : n = n') (u : Matrix.unitaryGroup (Fin n) ℂ) :
    ((castU h u : Matrix.unitaryGroup (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) =
      (u : Matrix (Fin n) (Fin n) ℂ).submatrix (Fin.cast h.symm) (Fin.cast h.symm) := by
  subst h
  rfl

def onbConj (W : G.Weil) (X : Node) (u : UG D.what₂.Tau (G.V X).rank) (τ : D.what₂.Tau) :
    Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ :=
  W.onb X τ * (u τ : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) * (W.onb X τ)⁻¹

theorem onbConj_mem {W : G.Weil} {X : Node} (hX : PosOnb W X) (u : UG D.what₂.Tau (G.V X).rank) (τ : D.what₂.Tau) :
    onbConj W X u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V X) τ) :=
  conj_mem_UH (hX τ) (u τ).2

theorem onbConj_one {W : G.Weil} {X : Node} (hX : PosOnb W X) : onbConj W X 1 = 1 := by
  funext τ
  have hd : IsUnit (W.onb X τ).det := Matrix.isUnit_det_of_left_inverse (hX τ)
  simp only [onbConj, Pi.one_apply, OneMemClass.coe_one, Matrix.mul_one]
  exact Matrix.mul_nonsing_inv _ hd

theorem onbConj_mul {W : G.Weil} {X : Node} (hX : PosOnb W X) (u v : UG D.what₂.Tau (G.V X).rank) :
    onbConj W X (u * v) = onbConj W X u * onbConj W X v := by
  funext τ
  have hd : IsUnit (W.onb X τ).det := Matrix.isUnit_det_of_left_inverse (hX τ)
  have h2 : (W.onb X τ)⁻¹ * W.onb X τ = 1 := Matrix.nonsing_inv_mul _ hd
  simp only [onbConj, Pi.mul_apply, Submonoid.coe_mul]
  calc W.onb X τ * ((u τ : Matrix _ _ ℂ) * (v τ : Matrix _ _ ℂ)) * (W.onb X τ)⁻¹
      = W.onb X τ * (u τ : Matrix _ _ ℂ) * ((W.onb X τ)⁻¹ * W.onb X τ) * (v τ : Matrix _ _ ℂ) * (W.onb X τ)⁻¹ := by
        rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

open Classical in

def vtxPt (W : G.Weil) (X : Node) : UG D.what₂.Tau (G.V X).rank →* GA D (G.V X) where
  toFun u := if PosOnb W X then realAll W.θ (G.V X) (onbConj W X u) else 1
  map_one' := by
    split_ifs with h
    · rw [onbConj_one h]
      exact realAll_one W.θ_is
    · rfl
  map_mul' u v := by
    split_ifs with h
    · rw [onbConj_mul h]
      exact realAll_mul W.θ_is (onbConj_mem h u) (onbConj_mem h v)
    · rw [mul_one]

theorem vtxPt_eq {W : G.Weil} {X : Node} (hX : PosOnb W X) (u : UG D.what₂.Tau (G.V X).rank) :
    vtxPt W X u = realAll W.θ (G.V X) (onbConj W X u) := by
  simp only [vtxPt, MonoidHom.coe_mk, OneHom.coe_mk]
  exact if_pos hX

theorem vtxPt_of_not {W : G.Weil} {X : Node} (hX : ¬ PosOnb W X) (u : UG D.what₂.Tau (G.V X).rank) : vtxPt W X u = 1 := by
  simp only [vtxPt, MonoidHom.coe_mk, OneHom.coe_mk]
  exact if_neg hX

theorem vtxPt_mem (W : G.Weil) (X : Node) (u : UG D.what₂.Tau (G.V X).rank) : vtxPt W X u ∈ GinfC (G.V X) := by
  by_cases h : PosOnb W X
  · rw [vtxPt_eq h]; exact realAll_mem _
  · rw [vtxPt_of_not h]; exact one_mem _

theorem compAt_vtxPt {W : G.Weil} {X : Node} (hX : PosOnb W X) (u : UG D.what₂.Tau (G.V X).rank) (τ : D.what₂.Tau) :
    compAt W.θ τ (mt (G.V X) (vtxPt W X u)) =
      W.onb X τ * (u τ : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) * (W.onb X τ)⁻¹ := by
  rw [vtxPt_eq hX]
  exact compAt_realAll W.θ_is (onbConj_mem hX u) τ

end Grid

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Kappa

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

variable (G) in

def rowU (j : Fin D.R.m) : Gc D.what₂.Tau (rowSizes D) →* UG D.what₂.Tau (G.V (.top j)).rank :=
  (MonoidHom.compLeft (castU (rank_top G (j := j) j.2.le).symm) D.what₂.Tau).comp
    ((Pi.evalMonoidHom (fun j : Fin (rowSizes D).m => UG D.what₂.Tau ((rowSizes D).nR j)) j).comp (MonoidHom.fst _ _))

variable (G) in

def colU (i : Fin (D.R.m + 1)) : Gc D.what₂.Tau (rowSizes D) →* UG D.what₂.Tau (G.V (.grid i D.R.m)).rank :=
  (MonoidHom.compLeft (castU (rank_gridM G (i := i) (Nat.lt_succ_iff.1 i.2)).symm) D.what₂.Tau).comp
    ((Pi.evalMonoidHom (fun i : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nC i)) i).comp (MonoidHom.snd _ _))

theorem rowU_coe (g : Gc D.what₂.Tau (rowSizes D)) (j : Fin D.R.m) (τ : D.what₂.Tau) :
    ((rowU G j g τ : Matrix.unitaryGroup (Fin (G.V (.top j)).rank) ℂ) : Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ) =
      ((g.1 j τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (rank_top G (j := j) j.2.le))
        (Fin.cast (rank_top G (j := j) j.2.le)) :=
  castU_coe _ _

theorem colU_coe (g : Gc D.what₂.Tau (rowSizes D)) (i : Fin (D.R.m + 1)) (τ : D.what₂.Tau) :
    ((colU G i g τ : Matrix.unitaryGroup (Fin (G.V (.grid i D.R.m)).rank) ℂ) :
        Matrix (Fin (G.V (.grid i D.R.m)).rank) (Fin (G.V (.grid i D.R.m)).rank) ℂ) =
      ((g.2 i τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (rank_gridM G (i := i) (Nat.lt_succ_iff.1 i.2)))
        (Fin.cast (rank_gridM G (i := i) (Nat.lt_succ_iff.1 i.2))) :=
  castU_coe _ _

def kappa (W : G.Weil) : Gc D.what₂.Tau (rowSizes D) →*
    (∀ j : Fin D.R.m, GA D (G.V (.top j))) × (∀ i : Fin (D.R.m + 1), GA D (G.V (.grid i D.R.m))) :=
  (Pi.monoidHom fun j : Fin D.R.m => (vtxPt W (.top j)).comp (rowU G j)).prod
    (Pi.monoidHom fun i : Fin (D.R.m + 1) => (vtxPt W (.grid i D.R.m)).comp (colU G i))

theorem kappa_fst (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (j : Fin D.R.m) :
    (kappa W g).1 j = vtxPt W (.top j) (rowU G j g) := rfl

theorem kappa_snd (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (i : Fin (D.R.m + 1)) :
    (kappa W g).2 i = vtxPt W (.grid i D.R.m) (colU G i g) := rfl

theorem kappa_fst_mem (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (j : Fin D.R.m) :
    (kappa W g).1 j ∈ GinfC (G.V (.top j)) := vtxPt_mem _ _ _

theorem kappa_snd_mem (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (i : Fin (D.R.m + 1)) :
    (kappa W g).2 i ∈ GinfC (G.V (.grid i D.R.m)) := vtxPt_mem _ _ _

theorem compAt_kappa_fst {W : G.Weil} (g : Gc D.what₂.Tau (rowSizes D)) (j : Fin D.R.m) (hW : PosOnb W (.top j))
    (τ : D.what₂.Tau) : compAt W.θ τ (mt (G.V (.top j)) ((kappa W g).1 j)) =
      W.onb (.top j) τ * ((g.1 j τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix
        (Fin.cast (rank_top G (j := j) j.2.le)) (Fin.cast (rank_top G (j := j) j.2.le)) * (W.onb (.top j) τ)⁻¹ := by
  rw [kappa_fst, compAt_vtxPt hW, rowU_coe]

theorem compAt_kappa_snd {W : G.Weil} (g : Gc D.what₂.Tau (rowSizes D)) (i : Fin (D.R.m + 1))
    (hW : PosOnb W (.grid i D.R.m)) (τ : D.what₂.Tau) : compAt W.θ τ (mt (G.V (.grid i D.R.m)) ((kappa W g).2 i)) =
      W.onb (.grid i D.R.m) τ * ((g.2 i τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix
        (Fin.cast (rank_gridM G (i := i) (Nat.lt_succ_iff.1 i.2)))
        (Fin.cast (rank_gridM G (i := i) (Nat.lt_succ_iff.1 i.2))) * (W.onb (.grid i D.R.m) τ)⁻¹ := by
  rw [kappa_snd, compAt_vtxPt hW, colU_coe]

def kappaTop (W : G.Weil) : Gc D.what₂.Tau (rowSizes D) →* GA D (G.V (.top D.R.m)) where
  toFun g := stabilizerEmbedding G.sp.topDec ((kappa W g).2 (Fin.last D.R.m))
  map_one' := by
    have e := GlobalTheory.RealType.unitaryEmbedding_mul G.sp.topDec 1 1
    rw [mul_one] at e
    rw [map_one, Prod.snd_one, Pi.one_apply]
    exact left_eq_mul.1 e
  map_mul' g h := by
    rw [map_mul, Prod.snd_mul, Pi.mul_apply]
    exact GlobalTheory.RealType.unitaryEmbedding_mul G.sp.topDec _ _

theorem kappaTop_mem (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) : kappaTop W g ∈ GinfC (G.V (.top D.R.m)) :=
  GlobalTheory.RealType.Emb_mem_inf G.sp.topDec (kappa_snd_mem W g (Fin.last D.R.m))

theorem kappaTop_apply (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) :
    kappaTop W g = stabilizerEmbedding G.sp.topDec ((kappa W g).2 (Fin.last D.R.m)) := rfl

end Kappa

section Measure

variable {D : D7}

theorem map_mul_right_of_finE {V : HSp D} {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))} {μ : Measure (GA D V)}
    (hμ : Lev.IsMeasLevDef V K μ) {k : GA D V} (hk : Lev.finE V k ∈ K) : μ.map (fun g => g * k) = μ := by
  obtain ⟨i1, i2, i3, i4, i5, -, -, -⟩ := GlobalTheory.RealMeasOne.ginfC_facts V
  haveI := hμ.1
  have h := Measure.map_right_mul_eq_modularCharacterFun_smul μ k
  have hT : μ (K.comap (Lev.finE V) : Set (GA D V)) = 1 := GlobalTheory.Mass.Levels.measure_comap_finE hμ
  have hkT : k ∈ K.comap (Lev.finE V) := hk
  have e1 : μ.map (fun g => g * k) (K.comap (Lev.finE V) : Set (GA D V)) = 1 := by
    rw [show (fun g : GA D V => g * k) = ⇑(MeasurableEquiv.mulRight k) from rfl, MeasurableEquiv.map_apply,
      show ⇑(MeasurableEquiv.mulRight k) ⁻¹' (K.comap (Lev.finE V) : Set (GA D V)) = K.comap (Lev.finE V) from
        Set.ext fun x => (K.comap (Lev.finE V)).mul_mem_cancel_right hkT]
    exact hT
  rw [h, Measure.coe_nnreal_smul_apply, hT, mul_one] at e1
  have h1 : Measure.modularCharacterFun k = 1 := by exact_mod_cast e1
  rw [h, h1, one_smul]

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem neg_eq_zero_of_defNode {X : Node} (hX : DefNode D.R.m X) : X.neg D.R.m = 0 := by
  rcases X with ⟨i, j⟩ | i | j
  · obtain ⟨-, rfl⟩ := hX
    simp [Node.neg]
  · exact hX.elim
  · rfl

theorem measurePreserving_mul_right {M : Vol G} {X : Node} {K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))}
    (hM : M.IsAt X K) (hX : X.neg D.R.m = 0) {k : GA D (G.V X)} (hk : k ∈ GinfC (G.V X)) :
    MeasurePreserving (fun g : GA D (G.V X) => g * k) (M.ν X) (M.ν X) := by
  obtain ⟨i1, i2, i3, i4, i5, -, -, -⟩ := GlobalTheory.RealMeasOne.ginfC_facts (G.V X)
  have hd : IsMeasDef (G.V X) K (M.ν X) (M.fd X) := by
    unfold Vol.IsAt at hM
    rwa [if_pos hX] at hM
  have hfin : Lev.finE (G.V X) k = 1 := by
    have h1 : finHom (G.V X) k = 1 := hk
    simp only [Lev.finE, MonoidHom.comp_apply, h1, map_one]
  exact ⟨measurable_mul_const k, map_mul_right_of_finE hd.1 (by rw [hfin]; exact one_mem K)⟩

theorem measurable_mul_inv_right (X : Node) (k : GA D (G.V X)) : Measurable (fun g : GA D (G.V X) => g * k⁻¹) := by
  obtain ⟨i1, i2, i3, i4, i5, -, -, -⟩ := GlobalTheory.RealMeasOne.ginfC_facts (G.V X)
  exact measurable_mul_const k⁻¹

theorem kappa_fst_move (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (j : Fin D.R.m) {M : Vol G}
    {K : Subgroup (GL (Fin (G.V (.top j)).rank) (Lev.EAf D))} (hM : M.IsAt (.top j) K) :
    MeasurePreserving (fun h : GA D (G.V (.top j)) => h * (kappa W g).1 j) (M.ν (.top j)) (M.ν (.top j)) ∧
      Measurable (fun h : GA D (G.V (.top j)) => h * ((kappa W g).1 j)⁻¹) :=
  ⟨measurePreserving_mul_right hM rfl (kappa_fst_mem W g j), measurable_mul_inv_right _ _⟩

theorem kappa_snd_move (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (i : Fin (D.R.m + 1)) {M : Vol G}
    {K : Subgroup (GL (Fin (G.V (.grid i D.R.m)).rank) (Lev.EAf D))} (hM : M.IsAt (.grid i D.R.m) K) :
    MeasurePreserving (fun h : GA D (G.V (.grid i D.R.m)) => h * (kappa W g).2 i) (M.ν (.grid i D.R.m))
        (M.ν (.grid i D.R.m)) ∧
      Measurable (fun h : GA D (G.V (.grid i D.R.m)) => h * ((kappa W g).2 i)⁻¹) :=
  ⟨measurePreserving_mul_right hM (neg_eq_zero_of_defNode (X := .grid i D.R.m) ⟨Nat.lt_succ_iff.1 i.2, rfl⟩)
    (kappa_snd_mem W g i), measurable_mul_inv_right _ _⟩

end Measure

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Inhabit

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem archM_kappaTop (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (τ : D.what₂.Tau) :
    Formalism.L2.Pj.archM (G.V (.top D.R.m)) (W.θ τ) (kappaTop W g) *
              (frameMat (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι).map (tauE D τ) =
      (frameMat (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι).map (tauE D τ) *
        Formalism.L2.Pj.archM (G.V (.grid D.R.m D.R.m)) (W.θ τ) ((kappa W g).2 (Fin.last D.R.m)) ∧
    Formalism.L2.Pj.archM (G.V (.top D.R.m)) (W.θ τ) (kappaTop W g) * G.sp.topDec.a.map (tauE D τ) =
      G.sp.topDec.a.map (tauE D τ) :=
  GlobalTheory.RealType.archM_Emb G.sp.topDec W.θ_is _ τ

end Inhabit

end GlobalTheory.RowReal
