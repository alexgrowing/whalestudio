import Mathlib
import Formalism.LocalToGlobal.HermitianForms.TiedTwGen
import Formalism.LocalToGlobal.Columns.RecLevelTop
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff

noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open scoped TensorProduct

section Level

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  (S : StepLevel F E σ J T f bad)

def basePts : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) where
  carrier := {k | k ∈ levelAfL σ J S.Lb ∧ ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) k = 1}
  one_mem' := ⟨one_mem _, fun _ _ => map_one _⟩
  mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, fun v h => by rw [map_mul, ha.2 v h, hb.2 v h, mul_one]⟩
  inv_mem' := fun ha => ⟨inv_mem ha.1, fun v h => by rw [map_inv, ha.2 v h, inv_one]⟩

theorem mem_basePts_iff (k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : k ∈ basePts S ↔
    k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧ (∀ v, bc (prV (E := E) v) k ∈ levelVL σ J v S.Lb) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) k = 1 := by
  rw [← and_assoc, ← GlobalTheory.LatticeStabLocal.mem_levelAfL_iff F E σ n J S.Lb S.Lb_fin k]
  rfl

variable {S} (k : basePts S)

def basePtU : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨k.1, k.2.1.1⟩

theorem basePt_loc (v : HeightOneSpectrum (𝓞 F)) : bc (prV (E := E) v) k.1 ∈ levelVL σ J v S.Lb :=
  ((mem_basePts_iff S k.1).1 k.2).2.1 v

theorem conj_mem_iff {G : Type} [Group G] {H : Subgroup G} {a : G} (ha : a ∈ H) (x : G) : a * x * a⁻¹ ∈ H ↔ x ∈ H := by
  rw [H.mul_mem_cancel_right (inv_mem ha), H.mul_mem_cancel_left ha]

def moveLev : StepLevel F E σ J T f bad :=
  { S with
    Uloc := fun v => (S.Uloc v).comap (MulAut.conj (bc (prV (E := E) v) k.1)).toMonoidHom
    Uloc_le := fun v x hx => (conj_mem_iff (H := UPts σ J (v.adicCompletion F)) (basePt_loc k v).1 x).1 (S.Uloc_le v hx)
    Uloc_lev := fun v x hx => (conj_mem_iff (basePt_loc k v) x).1 (S.Uloc_lev v hx)
    Uloc_hyp := fun v hv hT => by
      ext x
      rw [S.Uloc_hyp v hv hT]
      exact conj_mem_iff (basePt_loc k v) x
    UlocAlt := fun v h => by
      rw [← S.UlocAlt v h, k.2.2 v h]
      ext x
      simp
    U := S.U.comap (MulAut.conj k.1).toMonoidHom
    U_eq := fun x => by
      show k.1 * x * k.1⁻¹ ∈ S.U ↔ _
      rw [S.U_eq, conj_mem_iff (H := UPts σ J (FiniteAdeleRing (𝓞 F) F)) (a := k.1) (basePtU k).2]
      refine and_congr_right fun _ => forall_congr' fun v => ?_
      rw [map_mul, map_mul, map_inv]
      rfl
    U_compact := by
      letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
      haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
      have hc : Continuous (fun x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) => k.1⁻¹ * x * k.1) :=
        (continuous_const.mul continuous_id).mul continuous_const
      convert S.U_compact.image hc using 1
      ext x
      constructor
      · intro hx
        exact ⟨k.1 * x * k.1⁻¹, hx, by group⟩
      · rintro ⟨y, hy, rfl⟩
        show k.1 * (k.1⁻¹ * y * k.1) * k.1⁻¹ ∈ S.U
        have e : k.1 * (k.1⁻¹ * y * k.1) * k.1⁻¹ = y := by group
        rwa [e]
    U_open := by
      letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
      haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
      haveI : ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)) :=
        inferInstanceAs (ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)).toSubmonoid)
      have hc : Continuous (fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => basePtU k * x * (basePtU k)⁻¹) :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact S.U_open.preimage hc
    chi := S.chi.comp ((MulAut.conj k.1).toMonoidHom.subgroupComap S.U)
    chi_triv := fun x hx => S.chi_triv _ fun v hv => by
      show bc (prV (E := E) v) (k.1 * x.1 * k.1⁻¹) = 1
      rw [map_mul, map_mul, hx v hv, mul_one, ← map_mul, mul_inv_cancel, map_one] }

theorem mem_moveLev (x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : x ∈ (moveLev k).U ↔ k.1 * x * k.1⁻¹ ∈ S.U := Iff.rfl

theorem moveLev_chi (x : (moveLev k).U) : (moveLev k).chi x = S.chi ⟨k.1 * x.1 * k.1⁻¹, x.2⟩ := rfl

def toMoved (κ : S.U) : (moveLev k).U :=
  ⟨k.1⁻¹ * κ.1 * k.1, by
    have e : k.1 * (k.1⁻¹ * κ.1 * k.1) * k.1⁻¹ = κ.1 := by group
    rw [mem_moveLev, e]
    exact κ.2⟩

theorem chi_toMoved (κ : S.U) : (moveLev k).chi (toMoved k κ) = S.chi κ := by
  rw [moveLev_chi]
  congr 1
  apply Subtype.ext
  show k.1 * (k.1⁻¹ * κ.1 * k.1) * k.1⁻¹ = κ.1
  group

theorem basePt_hatStab : HatStab S.Lb k.1 := fun z => ((inv_mem k.2.1).2 z).symm

theorem latAd_basePt [StarRing E] (x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : latAd (x * k.1) S.Lb = latAd x S.Lb :=
  latAd_stab x k.1 S.Lb (basePt_hatStab k)

theorem cls_move_iff (x y : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    (Quotient.mk'' (x * basePtU k) : Cls (moveLev k)) = Quotient.mk'' (y * basePtU k) ↔
      (Quotient.mk'' x : Cls S) = Quotient.mk'' y := by
  refine (DoubleCoset.eq _ _ _ _).trans (Iff.trans ?_ (DoubleCoset.eq _ _ _ _).symm)
  refine exists_congr fun g => and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨κ, hκ, e⟩
    refine ⟨basePtU k * κ * (basePtU k)⁻¹, hκ, ?_⟩
    rw [← mul_inv_cancel_right y (basePtU k), e]
    group
  · rintro ⟨κ, hκ, e⟩
    refine ⟨(basePtU k)⁻¹ * κ * basePtU k, (toMoved k ⟨κ.1, hκ⟩).2, ?_⟩
    rw [e]
    group

theorem mem_hat_move_iff (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    (y⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb ↔
      ((y * k.1)⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F))
        (moveLev k).Lb := by
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  exact (inv_mem k.2.1).2 _

theorem map_conj_move (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    (moveLev k).U.map (MulAut.conj (y * k.1)).toMonoidHom = S.U.map (MulAut.conj y).toMonoidHom := by
  ext g
  constructor
  · rintro ⟨κ, hκ, e⟩
    refine ⟨_, (mem_moveLev k κ).1 hκ, Eq.trans ?_ e⟩
    show y * (k.1 * κ * k.1⁻¹) * y⁻¹ = y * k.1 * κ * (y * k.1)⁻¹
    group
  · rintro ⟨κ, hκ, e⟩
    refine ⟨_, (toMoved k ⟨κ, hκ⟩).2, Eq.trans ?_ e⟩
    show y * k.1 * (k.1⁻¹ * κ * k.1) * (y * k.1)⁻¹ = y * κ * y⁻¹
    group

theorem bij_move {cl : Type} {y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F)} (h : Function.Bijective fun c => (Quotient.mk'' (y c) : Cls S)) :
    Function.Bijective fun c => (Quotient.mk'' (y c * basePtU k) : Cls (moveLev k)) := by
  refine ⟨fun c c' e => h.1 ((cls_move_iff k _ _).1 e), fun q => ?_⟩
  induction q using Quotient.inductionOn' with
  | h x =>
    obtain ⟨c, hc⟩ := h.2 (Quotient.mk'' (x * (basePtU k)⁻¹))
    refine ⟨c, ?_⟩
    have h := (cls_move_iff k _ _).2 hc
    rwa [inv_mul_cancel_right] at h

example : (moveLev (1 : basePts S)).U = S.U := by
  ext x
  simp [mem_moveLev]

example (κ : S.U) (h : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) κ.1 = 1) : κ.1 ∈ basePts S :=
  (mem_basePts_iff S _).2 ⟨((S.U_eq _).1 κ.2).1, fun v => S.Uloc_lev v (((S.U_eq _).1 κ.2).2 v), h⟩

end Level

section Chart

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type}
  {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}

set_option maxHeartbeats 1000000 in

def moveChart (K : LevelChart D T bad i hi stab lat) (k : basePts K.lev) : LevelChart D T bad i hi stab lat where
  lev := moveLev k
  y := fun c => K.y c * basePtU k
  y_bij := bij_move k K.y_bij
  y_lat := fun c x => (K.y_lat c x).trans (mem_hat_move_iff k (K.y c).1 x)
  stabI := K.stabI
  stabI_inj := K.stabI_inj
  stabI_range := fun c γ => (K.stabI_range c γ).trans (SetLike.ext_iff.1 (map_conj_move k (K.y c).1) _).symm

end Chart

end GlobalTheory.TwU

end
