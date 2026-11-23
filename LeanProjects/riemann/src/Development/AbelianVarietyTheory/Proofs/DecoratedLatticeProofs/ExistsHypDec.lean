import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.I0M
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.SBesEx

theorem gram_scaled {E : Type} [Field E] [StarRing E] {n k l : Type} [Fintype n] (G : Matrix n n E)
    (A : Matrix n k E) (B : Matrix n l E) (α : k → E) (β : l → E) (x : k → n → E) (y : l → n → E)
    (hA : ∀ i a, A i a = α a * x a i) (hB : ∀ i b, B i b = β b * y b i) (a : k) (b : l) :
    (Aᴴ * G * B) a b = star (α a) * β b * (star (x a) ⬝ᵥ (G *ᵥ y b)) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, conjTranspose_apply, hA, hB, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum,
    star_mul']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_sum {E : Type} [Field E] [StarRing E] {n k l m : Type} [Fintype n] [Fintype k] [Fintype l]
    (G : Matrix n n E) (I : Matrix n k E) (J : Matrix n l E) (P : Matrix k m E) (Q : Matrix l m E)
    (hIJ : Iᴴ * G * J = 0) (hJI : Jᴴ * G * I = 0) :
    (I * P + J * Q)ᴴ * G * (I * P + J * Q) = Pᴴ * (Iᴴ * G * I) * P + Qᴴ * (Jᴴ * G * J) * Q := by
  have e : (I * P + J * Q)ᴴ * G * (I * P + J * Q) =
      Pᴴ * (Iᴴ * G * I) * P + Qᴴ * (Jᴴ * G * J) * Q + Pᴴ * (Iᴴ * G * J) * Q + Qᴴ * (Jᴴ * G * I) * P := by
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  rw [e, hIJ, hJI]
  simp

theorem gram_sum_zero {E : Type} [Field E] [StarRing E] {n k l m p : Type} [Fintype n] [Fintype k] [Fintype l]
    (G : Matrix n n E) (I : Matrix n k E) (J : Matrix n l E) (P : Matrix k m E) (Q : Matrix l m E) (C : Matrix n p E)
    (hI : Iᴴ * G * C = 0) (hJ : Jᴴ * G * C = 0) :
    (I * P + J * Q)ᴴ * G * C = 0 := by
  have e : (I * P + J * Q)ᴴ * G * C = Pᴴ * (Iᴴ * G * C) + Qᴴ * (Jᴴ * G * C) := by
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_assoc]
  rw [e, hI, hJ]
  simp

theorem exists_hypDec : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀) (t lam : D.host.E), t ≠ 0 → lam ≠ 0 → (∀ y y' : (VS D).V, star (GlobalTheory.Core.SBesEx.cY X h y') ⬝ᵥ ((D.sp.Y 0).gram *ᵥ GlobalTheory.Core.SBesEx.cY X h y) = (VS D).hT y' y) → (∀ (i j : Fin (D.sp.X 0).rank) (a : Fin D.R.rS), (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) j)) = (D.sp.X 0).gram i j ∧ (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (X.eX a) = 0 ∧ (VS D).hT (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) (X.fY a) = 0 ∧ (VS D).hT (X.zu u) (Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i)) = 0) → ∀ (L : HSp D), L.rank = 1 → (∀ i j, L.gram i j = star t * t * (VS D).hT (X.zu u) (X.zu u)) → ∀ (V₀ : HSp D) (o : OrthDec V₀ (D.sp.X 0) L), ∃ d : HypDec (D.sp.Y 0) V₀ D.R.rS, d.e = GlobalTheory.Core.SBesEx.eM X h t lam ∧ d.e' = GlobalTheory.Core.SBesEx.e'M X h t lam ∧ d.i₀ = GlobalTheory.Core.SBesEx.i0M X h u tr.wt t o := by
  intro D X h u F₀ tr t lam ht hlam hiso hfr L hL hLg V₀ o
  have hsym : ∀ x y : (VS D).V, (VS D).hT y x = star ((VS D).hT x y) := fun x y =>
    (LinearMap.isSymm_def.1 (VS D).herm x y).symm
  have hs : ∀ a : Fin D.R.rS, star (scl t lam a) ≠ 0 := fun a =>
    star_ne_zero.2 (mul_ne_zero ht (pow_ne_zero _ hlam))
  set q : Fin (D.sp.X 0).rank → (VS D).V := fun i =>
    Formalism.L2.SG.ColDict.qFr tr.wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) i) with hq
  have hE : ∀ i a, eM X h t lam i a = scl t lam a * cY X h (X.eX a) i := fun _ _ => rfl
  have hE' : ∀ i a, e'M X h t lam i a = (star (scl t lam a))⁻¹ * cY X h (X.fY a) i := fun _ _ => rfl
  have hQ : ∀ i a, qM X h tr.wt i a = (1 : D.host.E) * cY X h (q a) i := fun _ _ => (one_mul _).symm
  have hZ : ∀ i a, zM X h u t L i a = t * cY X h (X.zu u) i := fun _ _ => rfl
  have hzq : ∀ i, (VS D).hT (X.zu u) (q i) = 0 := by
    intro i
    rw [hsym, ← tr.wt_isom, tr.weight_z]
    simp only [hq, Formalism.L2.SG.ColDict.qFr, LinearEquiv.apply_symm_apply, Formalism.L2.SG.ColDict.xFr, D7.zmOf, map_smul]
    rw [D.sp.zm_orth, smul_zero, star_zero]
  have hqq : ∀ i j, (VS D).hT (q i) (q j) = (D.sp.X 0).gram i j := by
    intro i j
    rw [← tr.wt_isom]
    simp only [hq, Formalism.L2.SG.ColDict.qFr, LinearEquiv.apply_symm_apply, Formalism.L2.SG.ColDict.xFr]
    rw [D.sp.iXY_isom 0 (lt_of_lt_of_le two_pos D.R.two_le_m)]
    rfl
  have hQZ : (qM X h tr.wt)ᴴ * (D.sp.Y 0).gram * zM X h u t L = 0 := by
    ext a b
    rw [gram_scaled _ _ _ _ (fun _ => t) _ (fun _ => cY X h (X.zu u)) hQ hZ, hiso, hsym, hzq]
    simp
  have hZQ : (zM X h u t L)ᴴ * (D.sp.Y 0).gram * qM X h tr.wt = 0 := by
    ext a b
    rw [gram_scaled _ _ _ (fun _ => t) _ (fun _ => cY X h (X.zu u)) _ hZ hQ, hiso, hzq]
    simp
  have hQQ : (qM X h tr.wt)ᴴ * (D.sp.Y 0).gram * qM X h tr.wt = (D.sp.X 0).gram := by
    ext a b
    rw [gram_scaled _ _ _ _ _ _ _ hQ hQ, hiso, hqq]
    simp
  have hZZ : (zM X h u t L)ᴴ * (D.sp.Y 0).gram * zM X h u t L = L.gram := by
    ext a b
    rw [gram_scaled _ _ _ (fun _ => t) (fun _ => t) (fun _ => cY X h (X.zu u)) (fun _ => cY X h (X.zu u)) hZ hZ,
      hiso, hLg]
  refine ⟨⟨eM X h t lam, e'M X h t lam, i0M X h u tr.wt t o, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl⟩
  · ext a b
    rw [gram_scaled _ _ _ _ _ _ _ hE hE, hiso, X.ee]
    simp
  · ext a b
    rw [gram_scaled _ _ _ _ _ _ _ hE' hE', hiso, X.ff]
    simp
  · ext a b
    rw [gram_scaled _ _ _ _ _ _ _ hE' hE, hiso, hsym, X.ef, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      have := hs a
      rw [star_ne_zero] at this
      simp [this]
    · simp [hab, Ne.symm hab]
  · rw [i0M, gram_sum _ _ _ _ _ hQZ hZQ, hQQ, hZZ]
    have := gram_sum V₀.gram o.iA o.iB o.qA o.qB o.orth' o.orth
    rw [o.iA_qA_add, o.isoA, o.isoB] at this
    rw [← this]
    simp
  · refine gram_sum_zero _ _ _ _ _ _ ?_ ?_
    · ext a b
      rw [gram_scaled _ _ _ _ _ _ _ hQ hE, hiso, (hfr a a b).2.1]
      simp
    · ext a b
      rw [gram_scaled _ _ _ (fun _ => t) _ (fun _ => cY X h (X.zu u)) _ hZ hE, hiso, hsym, (X.zu_orth u b).1]
      simp
  · refine gram_sum_zero _ _ _ _ _ _ ?_ ?_
    · ext a b
      rw [gram_scaled _ _ _ _ _ _ _ hQ hE', hiso, (hfr a a b).2.2.1]
      simp
    · ext a b
      rw [gram_scaled _ _ _ (fun _ => t) _ (fun _ => cY X h (X.zu u)) _ hZ hE', hiso, hsym, (X.zu_orth u b).2]
      simp
  · have h1 := o.rank_add
    have h2 := D.sp.X_rank 0 (Nat.zero_le _)
    have h3 := D.sp.Y_rank 0 (Nat.zero_le _)
    have h4 := D.R.two_le_m
    obtain ⟨c, hc⟩ := D.R.m_even
    simp only [Ranks.N, Ranks.rankY, Ranks.r, Ranks.rS, zero_mul, add_zero] at h2 h3 ⊢
    omega

end GlobalTheory.Core.SBesEx

end
