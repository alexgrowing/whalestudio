import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceIdempotentCmEmbeddingCompat
import Formalism.LocalRingCardinality.FactDelDualNabla
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KerTieServed
open MvPowerSeries

section Lin
variable {p : ℕ} [Fact p.Prime] {σ σ' : Type*} [Fintype σ] [Fintype σ']

theorem hasSubst_linear {κ : Type*} [Fintype κ] (c : σ → κ → ℂ_[p]) :
    HasSubst (fun k : σ => ∑ x : κ, algebraMap ℂ_[p] (MvPowerSeries κ ℂ_[p]) (c k x) * X x) :=
  hasSubst_of_constantCoeff_zero fun k => by simp

theorem linAt_comp {κ : Type*} [Fintype κ] (c₁ : σ → σ' → ℂ_[p]) (c₂ : σ' → κ → ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) :
    linAt c₂ (linAt c₁ F) = linAt (fun k x => ∑ j, c₁ k j * c₂ j x) F := by
  unfold linAt
  rw [subst_comp_subst_apply (hasSubst_linear c₁) (hasSubst_linear c₂)]
  congr 1
  funext k
  rw [← coe_substAlgHom (hasSubst_linear c₂)]
  simp only [map_sum, map_mul, AlgHom.commutes, substAlgHom_X, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

theorem linAt_delta [DecidableEq σ] (F : MvPowerSeries σ ℂ_[p]) :
    linAt (fun k x : σ => if k = x then (1 : ℂ_[p]) else 0) F = F := by
  unfold linAt
  have e : (fun k : σ => ∑ x : σ, algebraMap ℂ_[p] (MvPowerSeries σ ℂ_[p]) (if k = x then (1 : ℂ_[p]) else 0) * X x) =
      X := by
    funext k
    simp [apply_ite]
  rw [e, subst_self]
  rfl

end Lin

section Mat
variable {K : Type*} [Field K] {T J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

def blk (ev : T → Prop) [DecidablePred ev] (A : T → Matrix J J K) (e : I ≃ J) (τ : T) : Matrix J I K :=
  if ev τ then (A τ).submatrix id e else ((A τ)⁻¹).transpose.submatrix id e

def blkInv (ev : T → Prop) [DecidablePred ev] (A : T → Matrix J J K) (e : I ≃ J) (τ : T) : Matrix I J K :=
  if ev τ then ((A τ)⁻¹).submatrix e id else (A τ).transpose.submatrix e id

theorem blkInv_mul_blk (ev : T → Prop) [DecidablePred ev] (A : T → Matrix J J K) (e : I ≃ J)
    (hA : ∀ τ, IsUnit (A τ).det) (τ : T) : blkInv ev A e τ * blk ev A e τ = 1 := by
  unfold blk blkInv
  split_ifs
  · rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.nonsing_inv_mul _ (hA τ),
      Matrix.submatrix_one_equiv]
  · rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ (hA τ), Matrix.transpose_one,
      Matrix.submatrix_one_equiv]

end Mat

section Sum
variable {K : Type*} [CommRing K] {S T J₁ J₂ I₁ I₂ : Type*} [Fintype T] [DecidableEq T] [Fintype J₁] [Fintype J₂]
  [DecidableEq S] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq J₁] [DecidableEq J₂]

def coef (t : S → T) (P : T → Matrix J₂ I₂ K) (Q : T → Matrix I₁ J₁ K) : T × J₂ × J₁ → S × I₁ × I₂ → K :=
  fun k x => if t x.1 = k.1 then P k.1 k.2.1 x.2.2 * Q k.1 x.2.1 k.2.2 else 0

def coefInv (t : S → T) (P' : T → Matrix I₂ J₂ K) (Q' : T → Matrix J₁ I₁ K) : S × I₁ × I₂ → T × J₂ × J₁ → K :=
  fun x k => if t x.1 = k.1 then P' k.1 x.2.2 k.2.1 * Q' k.1 k.2.2 x.2.1 else 0

theorem sum_coefInv_coef (t : S → T) (ht : Function.Injective t) (P : T → Matrix J₂ I₂ K) (Q : T → Matrix I₁ J₁ K)
    (P' : T → Matrix I₂ J₂ K) (Q' : T → Matrix J₁ I₁ K) (hP : ∀ τ, P' τ * P τ = 1) (hQ : ∀ τ, Q τ * Q' τ = 1)
    (x x' : S × I₁ × I₂) :
    ∑ k, coefInv t P' Q' x k * coef t P Q k x' = if x = x' then 1 else 0 := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (t x.1)]
  · unfold coef coefInv
    simp only [if_true]
    by_cases hxx : t x'.1 = t x.1
    · have h1 : x'.1 = x.1 := ht hxx
      simp only [hxx, if_true]
      have e : ∀ y : J₂ × J₁, P' (t x.1) x.2.2 y.1 * Q' (t x.1) y.2 x.2.1 * (P (t x.1) y.1 x'.2.2 * Q (t x.1) x'.2.1 y.2) =
          (P' (t x.1) x.2.2 y.1 * P (t x.1) y.1 x'.2.2) * (Q (t x.1) x'.2.1 y.2 * Q' (t x.1) y.2 x.2.1) := fun y => by ring
      rw [Finset.sum_congr rfl fun y _ => e y, Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      have e1 := congrFun (congrFun (hP (t x.1)) x.2.2) x'.2.2
      have e2 := congrFun (congrFun (hQ (t x.1)) x'.2.1) x.2.1
      rw [Matrix.mul_apply] at e1 e2
      rw [e1, e2, Matrix.one_apply, Matrix.one_apply]
      obtain ⟨a, b, c⟩ := x
      obtain ⟨a', b', c'⟩ := x'
      simp only at h1 ⊢
      subst h1
      rcases eq_or_ne b b' with rfl | hb <;> rcases eq_or_ne c c' with rfl | hc <;>
        first | (simp; done) | (simp [hb, hb.symm]; done) | (simp [hc, hc.symm]; done) | simp [hb, hb.symm, hc, hc.symm]
    · have hne : x ≠ x' := fun hx => hxx (by rw [hx])
      simp only [hxx, if_false, mul_zero, Finset.sum_const_zero, hne]
  · intro τ _ hτ
    refine Finset.sum_eq_zero fun y _ => ?_
    unfold coefInv
    rw [if_neg (Ne.symm hτ), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

end Sum

section Main

theorem isUnit_det_rhoMat {D : D7} {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : G.Fills (D.gat u w h)} {Lv : G.Levels Fl}
    {Ch : G.Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w h Ch) (j : ℕ) (τ : D.what₂.Tau)
    (g : ∀ v, Matrix (Fin ((Fl.Pj j).m + 1)) (Fin ((Fl.Pj j).m + 1)) ((Fl.Pj j).Qq v)) (hg : ∀ v, IsUnit (g v).det) :
    IsUnit (rhoMat Kp j τ g).det := by
  unfold rhoMat
  have e := RingHom.map_det (Kp.iK.comp (((Fl.Pj j).ι ((posJ Gt u w h Fl j).symm τ).1).comp
    (RingEquiv.toRingHom (((Fl.Pj j).σ ((posJ Gt u w h Fl j).symm τ).1) ^ ((posJ Gt u w h Fl j).symm τ).2.val))))
    (g ((posJ Gt u w h Fl j).symm τ).1)
  rw [RingHom.mapMatrix_apply] at e
  have hu := (hg ((posJ Gt u w h Fl j).symm τ).1).map (Kp.iK.comp (((Fl.Pj j).ι ((posJ Gt u w h Fl j).symm τ).1).comp
    (RingEquiv.toRingHom (((Fl.Pj j).σ ((posJ Gt u w h Fl j).symm τ).1) ^ ((posJ Gt u w h Fl j).symm τ).2.val))))
  rw [e] at hu
  exact hu

open Classical in

theorem exists_th_served : ∀ {D : D7} {Dx : DivX D} (Gt : GatTies D) {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : G.Fills (D.gat u w h)} {Lv : G.Levels Fl}
    (KD : Formalism.L2.G.Cmp.KerData D c Tw u w h Lv) (E : KerEnt D Dx Tw), KD.lam = E.lam w →
    ∃ Th, ThAtServed (Formalism.L2.G.Cmp.kerAtP_of Gt { KD with Th := Th }) E := by
  intro D Dx Gt c Tw u w h Fl Lv KD E hlam
  let g : ∀ (j : ℕ) (_ : Lv.comp j × (Fl.Pj j).Tup) (v : Fin (Fl.Pj j).nV),
      Matrix (Fin ((Fl.Pj j).m + 1)) (Fin ((Fl.Pj j).m + 1)) ((Fl.Pj j).Qq v) :=
    fun j La v => if hL : (Fl.Pj j).IsLatTup La.2 then (hL v).choose else 1
  have hg : ∀ j La v, IsUnit (g j La v).det := by
    intro j La v
    by_cases hL : (Fl.Pj j).IsLatTup La.2
    · simp only [g, dif_pos hL]; exact (hL v).choose_spec.1
    · simp only [g, dif_neg hL, Matrix.det_one]; exact isUnit_one
  let K0 := Formalism.L2.G.Cmp.kerAtP_of Gt KD
  let ev : ℕ → D.what₂.Tau → Prop := fun j τ => Formalism.MainNotions.G.IsTypeV ((posJ Gt u w h Fl j).symm τ).2
  let Th : ∀ j, Lv.comp j × (Fl.Pj j).Tup → Lv.comp (j + 1) × (Fl.Pj (j + 1)).Tup →
      MvPowerSeries (D.what₂.Tau × Fin ((Fl.Pj (j + 1)).m + 1) × Fin ((Fl.Pj j).m + 1)) ℂ_[D.what₂.places.resChar w] :=
    fun j La La' => if hh : (Fl.Pj j).m + 1 = D.R.N j ∧ (Fl.Pj (j + 1)).m + 1 = D.R.N (j + 1) then
      linAt (coefInv (Formalism.BasicNotions.tauPl D)
          (blkInv (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hh.2.symm))
          (blk (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hh.1.symm)))
        (E.Th u (D.what₂.muAt w) w j (KD.cls j La.1 La.2) (KD.cls (j + 1) La'.1 La'.2))
    else 0
  refine ⟨Th, hlam, g, ?_, ?_⟩
  · intro j _ La hL v
    refine ⟨hg j La v, ?_⟩
    simp only [g, dif_pos hL]
    exact (hL v).choose_spec.2
  · intro j _ hN hN' La La' _ _
    refine ⟨fun _ => 1, fun _ => norm_one, ?_⟩
    have hTh : Th j La La' = linAt (coefInv (Formalism.BasicNotions.tauPl D)
          (blkInv (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
          (blk (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm)))
        (E.Th u (D.what₂.muAt w) w j (KD.cls j La.1 La.2) (KD.cls (j + 1) La'.1 La'.2)) := by
      simp only [Th, dif_pos (And.intro hN hN')]
    have hC : (fun (k : D.what₂.Tau × Fin ((Fl.Pj (j + 1)).m + 1) × Fin ((Fl.Pj j).m + 1))
              (x : (Bool × G.HH D) × Fin (D.R.N j) × Fin (D.R.N (j + 1))) =>
            if Formalism.BasicNotions.tauPl D x.1 = k.1 then
              (if Formalism.MainNotions.G.IsTypeV ((posJ Gt u w h Fl j).symm k.1).2 then
                (fun _ => (1 : ℂ_[D.what₂.places.resChar w])) k.1 * (rhoMat K0 (j + 1) k.1 (g (j + 1) La')) k.2.1 (Fin.cast hN'.symm x.2.2) *
                  ((rhoMat K0 j k.1 (g j La))⁻¹) (Fin.cast hN.symm x.2.1) k.2.2
              else
                (fun _ => (1 : ℂ_[D.what₂.places.resChar w])) k.1 * (((rhoMat K0 (j + 1) k.1 (g (j + 1) La'))⁻¹).transpose) k.2.1 (Fin.cast hN'.symm x.2.2) *
                  ((rhoMat K0 j k.1 (g j La)).transpose) (Fin.cast hN.symm x.2.1) k.2.2)
            else 0) =
        coef (Formalism.BasicNotions.tauPl D) (blk (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
          (blkInv (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm)) := by
      funext k x
      simp only [coef, blk, blkInv, ev]
      split_ifs <;> simp [Matrix.submatrix_apply, Matrix.transpose_apply]
    have hS := sum_coefInv_coef (Formalism.BasicNotions.tauPl D) (Formalism.BasicNotions.tauPl_bij D).1
      (blk (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
      (blkInv (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm))
      (blkInv (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
      (blk (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm))
      (blkInv_mul_blk _ _ _ fun τ => isUnit_det_rhoMat K0 (j + 1) τ _ (hg (j + 1) La'))
      (blkInv_mul_blk _ _ _ fun τ => isUnit_det_rhoMat K0 j τ _ (hg j La))
    have key : E.Th u (D.what₂.muAt w) w j (KD.cls j La.1 La.2) (KD.cls (j + 1) La'.1 La'.2) =
        linAt (coef (Formalism.BasicNotions.tauPl D) (blk (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
          (blkInv (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm))) (Th j La La') := by
      rw [hTh, linAt_comp]
      simp only [hS]
      exact (linAt_delta _).symm
    rw [← hC] at key
    exact key

end Main

end GlobalTheory.KerTieServed
