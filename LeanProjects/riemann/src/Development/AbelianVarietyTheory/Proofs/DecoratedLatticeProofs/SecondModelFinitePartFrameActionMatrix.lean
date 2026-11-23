import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointInfiniteMatricesEqOneOfFinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.AdBridge

namespace GlobalTheory.Core.Mi.FinFrame

theorem eq_self_of_rat_of_int (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ι : E ⊗[F] Formalism.MainNotions.S.Af F →+* E ⊗[F] Formalism.MainNotions.S.Af F)
    (hι : ∀ x, ι (Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) x) = Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) x)
    (hO : ∀ a ∈ IntAf F E, ι a ∈ IntAf F E) (a : E ⊗[F] Formalism.MainNotions.S.Af F) : ι a = a := by
  obtain ⟨-, hden, hzero, hdenom, -⟩ := GlobalTheory.St.G.IntAd.integral_adeles_properties F E
  have key : ∀ b ∈ IntAf F E, ι b = b := by
    intro b hb
    rw [← sub_eq_zero]
    refine hzero _ fun m hm => ?_
    obtain ⟨x, t, ht, rfl⟩ := hden b hb m hm
    refine ⟨ι t - t, (IntAf F E).sub_mem (hO _ ht) ht, ?_⟩
    simp only [map_add, map_mul, map_natCast, hι]
    ring
  obtain ⟨m, hm, hma⟩ := hdenom a
  have h := key _ hma
  simp only [map_mul, map_natCast] at h
  have hu : IsUnit (m : E ⊗[F] Formalism.MainNotions.S.Af F) := by
    have : IsUnit (m : F) := (Nat.cast_ne_zero.2 hm.ne').isUnit
    simpa using this.map (algebraMap F (E ⊗[F] Formalism.MainNotions.S.Af F))
  exact hu.mul_left_cancel h

theorem tauF_eq (D : D7) (z : AE D) : tauF (Formalism.L2.SG.InstExistsPf.instOf D) z = toEAf D z := by
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero (toEAf D)).symm
  | tmul a x => exact tauF_tmul (Formalism.L2.SG.InstExistsPf.instOf D) a x
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add (toEAf D) x y).symm)

theorem fmat_iota (D : D7) (g : GA D (D.sp.Y 0)) :
    (Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 = (mt (D.sp.Y 0) g).map (toEAf D) := by
  have hb := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D g)
  have key : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D g) = g :=
    (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply g
  refine (hb.2.trans (congrArg (fun q => ofHAFin (Formalism.IndefR.RationalEmbedding.inst D) q) key)).trans ?_
  ext i j
  exact tauF_eq D _

theorem toEAf_incA (D : D7) (y : D.host.E) :
    toEAf D (incA D y) = Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) y :=
  (tauF_eq D _).symm.trans (tauF_tmul (Formalism.L2.SG.InstExistsPf.instOf D) 1 y)

theorem map_cols {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) {m n : ℕ} (M : Matrix (Fin m) (Fin m) A)
    (N : Matrix (Fin m) (Fin n) A) (P : Matrix (Fin n) (Fin n) A) (h : M * N = N * P) (j : Fin n) :
    M.map f *ᵥ (fun k => f (N k j)) = ∑ i, f (P i j) • fun k => f (N k i) := by
  funext k
  have h3 := congrArg f (congrFun (congrFun h k) j)
  simp only [Matrix.mul_apply, map_sum, map_mul] at h3
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h3]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem embA_cols {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (a : GA D A)
    (j : Fin A.rank) :
    (mt S (embA d o a)).map (toEAf D) *ᵥ
        (fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) ((d.i₀ * o.iA) k j)) =
      ∑ i, toEAf D (mt A a i j) • fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) ((d.i₀ * o.iA) k i) := by
  have h1 : mt S (embA d o a) ⬝ (d.j0 ⬝ o.jA) = (d.j0 ⬝ o.jA) ⬝ mt A a := by
    change mt S (d.emb0 (o.emb (a, 1))) ⬝ (d.j0 ⬝ o.jA) = _
    rw [← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_assoc, o.emb_jA, Matrix.mul_assoc]
  have h2 : d.j0 ⬝ o.jA = (d.i₀ * o.iA).map (incA D) := (Matrix.map_mul (f := incA D)).symm
  rw [h2] at h1
  have h3 := map_cols (toEAf D) _ _ _ h1 j
  simp only [Matrix.map_apply, toEAf_incA] at h3
  exact h3

theorem transport (D : D7) (I : AutInst) (ιE : I.E ≃+* D.host.E) (hId : ∀ y, HEq (ιE y) y)
    (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : (D.sp.Y 0).rank = I.n)
    (ιA : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (hrat : ∀ x : I.E, ιA (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) =
      Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιE x))
    (hint : ∀ a, a ∈ IntAf I.F I.E ↔ ιA a ∈ IntAf D.host.F D.host.E)
    {n : ℕ} (q : Fin n → Fin I.n → I.E) (g : GA D (D.sp.Y 0)) (c : Fin n → GlobalTheory.AdForm.EF D) (j : Fin n)
    (H : (mt (D.sp.Y 0) g).map (toEAf D) *ᵥ
        (fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) (ιE (q j (Fin.cast hr k)))) =
      ∑ i, c i • fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) (ιE (q i (Fin.cast hr k)))) :
    I.fmat (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D g)).2 *ᵥ incl I (q j) = ∑ i, ιA.symm (c i) • incl I (q i) := by
  generalize hI.symm = e
  subst hI
  have hid : ∀ y, ιE y = y := fun y => eq_of_heq (hId y)
  have hA : ∀ a, ιA a = a := eq_self_of_rat_of_int (Formalism.L2.SG.InstExistsPf.instOf D).F (Formalism.L2.SG.InstExistsPf.instOf D).E ιA.toRingHom
    (fun x => (hrat x).trans (congrArg _ (hid x))) (fun a ha => (hint a).1 ha)
  have hA' : ∀ a, ιA.symm a = a := fun a => (hA _).symm.trans (ιA.apply_symm_apply a)
  simp only [hid] at H
  simp only [hA']
  change (Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D g).2 *ᵥ _ = _
  rw [fmat_iota]
  exact H

theorem repM_toH : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (B : SBes X h u ψ (D.sp.X 0)) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F), IdE X → B.Adapted tr.wt → ∀ a : GA D (D.sp.X 0), RepM X tr.wt tr.ιA ((B.toH a).2 : X.B.I.Gf) (GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a) := by
  intro D X h u ψ B F tr hId hAd a j
  have hn := Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)
  refine transport D X.B.I X.ιE hId h (rank_eq X h) tr.ιA tr.ιA_rat tr.ιA_int
    (fun i => X.crd (Formalism.L2.SG.ColDict.qFr tr.wt i)) (embA B.d B.o a)
    (fun i => GlobalTheory.AdForm.finM (D.sp.X 0) hn a i j) j ?_
  have H := embA_cols B.d B.o a (Fin.cast hn.symm j)
  simp only [hAd _ _] at H
  refine H.trans ?_
  exact Fintype.sum_equiv (finCongr hn) _ _ fun i => rfl

end GlobalTheory.Core.Mi.FinFrame
