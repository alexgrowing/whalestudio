import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalCongruenceLevelContained
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Theta
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevCosetFin

open ReciprocityTheory.Aut

section Grp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem natCast_isUnit_AL {d : ℕ} (hd : 0 < d) : IsUnit (d : AL L) := by
  have e : (d : AL L) = algebraMap L (AL L) (d : L) := (map_natCast _ d).symm
  rw [e]
  exact (IsUnit.mk0 (d : L) (Nat.cast_ne_zero.2 hd.ne')).map _

theorem exists_finset_of_bdd (d : ℕ) (hd : 0 < d) (S : Set (GAf L n))
    (hS : ∀ κ ∈ S, ∀ i j, (d : AL L) * (κ.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L ∧
        (d : AL L) * ((κ⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L) :
    ∃ F : Finset (GAf L n), ∀ κ ∈ S, ∃ f ∈ F, f⁻¹ * κ ∈ Umax L n := by
  classical
  obtain ⟨Q, hQ, c, hc⟩ := GlobalTheory.IsotOrth.exists_finite_class (F := NumberField.maximalRealSubfield L) (E := L)
    (d * d) (Nat.mul_pos hd hd)
  haveI := hQ
  let cls : GAf L n → Fin n → Fin n → Q := fun κ i j =>
    if h : (d : AL L) * (κ.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L then c ⟨_, h⟩ else c 0
  have key : ∀ a ∈ S, ∀ b ∈ S, cls a = cls b → a⁻¹ * b ∈ Umax L n := by
    intro a ha b hb hab
    have hdiff : ∀ k l, ∃ y ∈ ALint L, (b.1 : Matrix (Fin n) (Fin n) (AL L)) k l -
        (a.1 : Matrix (Fin n) (Fin n) (AL L)) k l = (d : AL L) * y := by
      intro k l
      have e := congrFun (congrFun hab k) l
      simp only [cls, dif_pos (hS a ha k l).1, dif_pos (hS b hb k l).1] at e
      obtain ⟨z, hz⟩ := hc _ _ e.symm
      refine ⟨z.1, z.2, ?_⟩
      have hz' := congrArg Subtype.val hz
      apply (natCast_isUnit_AL (L := L) hd).mul_left_cancel
      push_cast at hz'
      rw [mul_sub, hz', mul_assoc]
    choose y hy hye using hdiff
    have h0 : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      have : (((a⁻¹ * a).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by simp
      simpa using this
    have h1 : (((a⁻¹ * b).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 +
        ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) *
          ((b.1 : Matrix (Fin n) (Fin n) (AL L)) - (a.1 : Matrix (Fin n) (Fin n) (AL L))) := by
      rw [Matrix.mul_sub, h0, add_sub_cancel]
      rfl
    intro i j
    show (((a⁻¹ * b).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L
    rw [h1, Matrix.add_apply, Matrix.mul_apply]
    refine add_mem ?_ (Subring.sum_mem _ fun k _ => ?_)
    · rw [Matrix.one_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    · rw [Matrix.sub_apply, hye k j, ← mul_assoc, mul_comm _ (d : AL L)]
      exact mul_mem (hS a ha i k).2 (hy k j)
  let T : Set (Fin n → Fin n → Q) := cls '' S
  have hT : T.Finite := Set.toFinite T
  let rep : (Fin n → Fin n → Q) → GAf L n := fun t => if h : t ∈ T then h.choose else 1
  refine ⟨hT.toFinset.image rep, fun κ hκ => ?_⟩
  have ht : cls κ ∈ T := ⟨κ, hκ, rfl⟩
  have hr : rep (cls κ) = ht.choose := dif_pos ht
  refine ⟨rep (cls κ), Finset.mem_image.2 ⟨cls κ, hT.mem_toFinset.2 ht, rfl⟩, ?_⟩
  rw [hr]
  exact key _ ht.choose_spec.1 _ hκ ht.choose_spec.2

end Grp

end GlobalTheory.LevCosetFin

namespace GlobalTheory.LevCosetFin

section Den

variable {D : D7}

theorem comm_mem_intT {x : D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F}
    (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    (Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F)) x ∈ GlobalTheory.LatCongImage.intT D.host.F := by
  induction hx using Subring.closure_induction with
  | mem z hz =>
    apply Subring.subset_closure
    rcases hz with ⟨⟨s, t, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩
    · right
      exact ⟨t, by simp⟩
    · left
      exact ⟨a, ha, by simp⟩
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

end Den

end GlobalTheory.LevCosetFin

namespace GlobalTheory.LevCosetFin

section Den2

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem exists_den (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (P : Formalism.IndefR.principalLevelFrame.RowPsi V n)
    (hF : D.host.F = maximalRealSubfield D.host.E) (hP : Formalism.IndefR.principalLevelFrame.StdPsi hF P)
    (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) :
    ∃ d : ℕ, 0 < d ∧ ∀ κ, (finHom V).rangeRestrict (P.ψ κ) ∈ (levEnv V β Ld).J → ∀ i j,
      (d : AL D.host.E) * (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) i j ∈ ALint D.host.E := by
  obtain ⟨⟨B, B', hBB', hB'B, hmat⟩, -⟩ := hP
  let cmr : D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F →+* FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F)).toAlgHom.toRingHom
  let βs := (β.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)).map cmr
  let βi := ((β⁻¹).1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)).map cmr
  obtain ⟨d, hd, hdm⟩ := GlobalTheory.LatCongImage.exists_nat_mul_mem_family D.host.F
    (fun p : ((Fin V.rank × Fin n) ⊕ (Fin n × Fin V.rank)) ⊕ ((Fin V.rank × Fin V.rank) ⊕ (Fin V.rank × Fin V.rank)) =>
      Sum.elim (Sum.elim (fun q => B q.1 q.2) (fun q => B' q.1 q.2))
        (Sum.elim (fun q => βs q.1 q.2) (fun q => βi q.1 q.2)) p)
  refine ⟨d ^ 4, by positivity, fun κ hκ i j => ?_⟩
  have h1 : Formalism.IndefR.Lev.finE V (P.ψ κ) ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Formalism.IndefR.Lev.flag1L Ld) := hκ
  obtain ⟨y, hy⟩ := Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev h1)
  have hM1 := congrArg (fun g : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) => (g.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) hy
  set Mf := (finHom V (P.ψ κ)).1 with hMf
  have hM2 : β.1 * ((y.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)).map Subtype.val) *
      (β⁻¹).1 = Mf.map (Formalism.IndefR.Lev.swapAE D) := hM1
  let Ym := ((y.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)).map Subtype.val).map cmr
  have hback : (Mf.map (Formalism.IndefR.Lev.swapAE D)).map cmr = Mf := by
    ext a b
    show (Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F))
      ((Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E) (Mf a b)) = Mf a b
    rw [← Algebra.TensorProduct.comm_symm, AlgEquiv.symm_apply_apply]
  have hM3 : Mf = βs * Ym * βi := by
    rw [← hback, ← hM2, Matrix.map_mul, Matrix.map_mul]
  set K := (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm with hK
  have hK2 : K = B' * Mf * B := by
    have e := hmat κ
    have e' : Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (P.ψ κ) = Mf := rfl
    rw [e'] at e
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB'B, Matrix.one_mul, Matrix.mul_assoc, hB'B, Matrix.mul_one]
  have hκij : (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) i j = Formalism.IndefR.principalLevelFrame.tensCastR hF (K i j) := by
    rw [hK, Matrix.map_apply, RingEquiv.apply_symm_apply]
  let Bs' : Matrix (Fin n) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • B'
  let Bs : Matrix (Fin V.rank) (Fin n) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • B
  let βs' : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • βs
  let βi' : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • βi
  let Ms : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := βs' * Ym * βi'
  have hB'1 : ∀ a b, Bs' a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b => by
    show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * B' a b ∈ _; exact hdm (Sum.inl (Sum.inr (a, b)))
  have hB1 : ∀ a b, Bs a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b => by
    show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * B a b ∈ _; exact hdm (Sum.inl (Sum.inl (a, b)))
  have hβs1 : ∀ a b, βs' a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b => by
    show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * βs a b ∈ _; exact hdm (Sum.inr (Sum.inl (a, b)))
  have hβi1 : ∀ a b, βi' a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b => by
    show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * βi a b ∈ _; exact hdm (Sum.inr (Sum.inr (a, b)))
  have hY1 : ∀ a b, Ym a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b =>
    comm_mem_intT (D := D) ((y.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) a b).2
  have hMs : ∀ a b, Ms a b ∈ GlobalTheory.LatCongImage.intT D.host.F :=
    GlobalTheory.LatCongImage.mul_apply_mem _ _ _ (GlobalTheory.LatCongImage.mul_apply_mem _ _ _ hβs1 hY1) hβi1
  have hint : ((d ^ 4 : ℕ) : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * K i j ∈ GlobalTheory.LatCongImage.intT D.host.F := by
    have hK3 : ((d ^ 4 : ℕ) : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • K = Bs' * Ms * Bs := by
      rw [hK2, hM3]
      simp only [Bs', Bs, Ms, βs', βi', Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      congr 1
      push_cast
      ring
    have e := congrFun (congrFun hK3 i) j
    rw [Matrix.smul_apply, smul_eq_mul] at e
    rw [e]
    exact GlobalTheory.LatCongImage.mul_apply_mem _ _ _ (GlobalTheory.LatCongImage.mul_apply_mem _ _ _ hB'1 hMs) hB1 i j
  rw [hκij, ← map_natCast (Formalism.IndefR.principalLevelFrame.tensCastR hF) (d ^ 4), ← map_mul]
  exact GlobalTheory.LatCongImage.swap_mem D.host.F hF hint

end Den2

end GlobalTheory.LevCosetFin

open GlobalTheory.LevCosetFin in

theorem GlobalTheory.LevCosetFin.preimage_levEnv_finite_cosets : ∀ (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hA : GlobalTheory.NJoin.Agree X M rep) (j : Fin D.R.m) (t : X.T), ∃ F : Finset (GAf D.host.E D.R.nV), ∀ κ, (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J → ∃ f ∈ F, f⁻¹ * κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := by
  intro D cf nch tp X M rep hA j t
  obtain ⟨d, hd, hden⟩ := exists_den (Vc D j) D.R.nV (hA.PV j) hA.hF (hA.stdV j) (X.R.βV j) (X.R.datVt j t)
  obtain ⟨F, hF⟩ := exists_finset_of_bdd d hd
    {κ | (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J}
    (fun κ hκ a b => ⟨hden κ hκ a b, hden κ⁻¹ (by
      show (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ⁻¹) ∈ _
      rw [map_inv, map_inv]
      exact inv_mem hκ) a b⟩)
  exact ⟨F, fun κ hκ => hF κ hκ⟩
