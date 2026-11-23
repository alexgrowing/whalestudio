import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IpEqZeroOfHeisEigen

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CosetOrth.Pairing

variable {D : D7}

theorem cA_fin_mul (e : D.host.E) (σ : AE D) (hσ : infPart D σ = 0) :
    cA D ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] e) * σ = incA D (star e) * σ := by
  refine sub_eq_zero.1 (GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_)
  · rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, hσ, mul_zero, mul_zero, sub_self]
  · have e1 : finPart D (cA D ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] e)) = finPart D (incA D (star e)) := rfl
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, e1, sub_self]

theorem hO_of_gram_one (S T : HSp D) (hS : S.gram = 1) (hT : T.gram = 1) (x y : WO S T) :
    hO S T x y = ∑ a, ∑ c, cA D (y c a) * x c a := by
  unfold hO
  rw [hS, hT, inv_one]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single c]
    · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, one_mul, mul_one]
    · intro d _ hd
      rw [Matrix.one_apply_ne (Ne.symm hd), RingHom.map_zero, mul_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    rw [Matrix.one_apply_ne (Ne.symm hb), RingHom.map_zero, zero_mul, zero_mul, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

def rowMat (S T : HSp D) (p : Fin T.rank) (f : Fin S.rank → AE D) : WO S T :=
  Matrix.of fun c a => if c = p then f a else 0

theorem hO_rowMat (S T : HSp D) (hS : S.gram = 1) (hT : T.gram = 1) (r : D.host.E) (o : ℕ) (j : Fin S.rank)
    (p : Fin T.rank) (hp : p.1 = o + j.1) (f : Fin S.rank → AE D) (hf : ∀ a, infPart D (f a) = 0) :
    hO S T (rowMat S T p f) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank)) =
      -(incA D (star r⁻¹) * f j) := by
  rw [hO_of_gram_one S T hS hT]
  have h1 : ∀ a, (∑ c, cA D (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank) c a) * rowMat S T p f c a) =
      incA D (star (-(r⁻¹ * if p.1 = o + a.1 then 1 else 0))) * f a := by
    intro a
    rw [Finset.sum_eq_single p]
    · have : rowMat S T p f p a = f a := if_pos rfl
      rw [this]
      exact cA_fin_mul _ _ (hf a)
    · intro c _ hc
      have : rowMat S T p f c a = 0 := if_neg hc
      rw [this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_eq_single j]
  · rw [if_pos hp, mul_one, star_neg, RingHom.map_neg, neg_mul]
  · intro a _ ha
    have : ¬ p.1 = o + a.1 := fun h => ha (Fin.ext (by omega))
    rw [if_neg this, mul_zero, neg_zero, star_zero, RingHom.map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem actO_rowMat (S T : HSp D) (g : GA D S) (p : Fin T.rank) (i : Fin S.rank) (σ : AE D) :
    actO S T g 1 (rowMat S T p (Pi.single i σ)) = rowMat S T p fun a => σ * mt S g⁻¹ i a := by
  have h1 : mt T 1 = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [MonoidHom.map_one]; rfl
  unfold actO
  rw [h1, Matrix.one_mul]
  funext c a
  rw [Matrix.mul_apply]
  by_cases hc : c = p
  · have e : ∀ k, rowMat S T p (Pi.single i σ) c k = (Pi.single i σ : Fin S.rank → AE D) k := fun k => if_pos hc
    have e' : rowMat S T p (fun a => σ * mt S g⁻¹ i a) c a = σ * mt S g⁻¹ i a := if_pos hc
    rw [e', Finset.sum_eq_single i]
    · rw [e, Pi.single_eq_same]
    · intro k _ hk
      rw [e, Pi.single_eq_of_ne hk, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have e : ∀ k, rowMat S T p (Pi.single i σ) c k = 0 := fun k => if_neg hc
    have e' : rowMat S T p (fun a => σ * mt S g⁻¹ i a) c a = 0 := if_neg hc
    rw [e']
    exact Finset.sum_eq_zero fun k _ => by rw [e, zero_mul]

theorem two_smul_rowMat (S T : HSp D) (p : Fin T.rank) (i : Fin S.rank) (σ : AE D) :
    2 • rowMat S T p (Pi.single i σ) = rowMat S T p (Pi.single i (2 * σ)) := by
  funext c a
  show 2 • (if c = p then (Pi.single i σ : Fin S.rank → AE D) a else 0) =
    if c = p then (Pi.single i (2 * σ) : Fin S.rank → AE D) a else 0
  by_cases hc : c = p
  · rw [if_pos hc, if_pos hc]
    by_cases ha : a = i
    · rw [ha, Pi.single_eq_same, Pi.single_eq_same, two_nsmul, two_mul]
    · rw [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne ha, nsmul_zero]
  · rw [if_neg hc, if_neg hc, nsmul_zero]

theorem hatPt_rowMat (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (p : Fin T.rank)
    (f : Fin S.rank → AE D) (h0 : ∀ a, infPart D (f a) = 0) (h1 : ∀ a, InHat I (algebraMap D.host.E (FA D) r * fe D (f a))) :
    HatPt r I (rowMat S T p f) := by
  refine ⟨?_, fun c a => ?_⟩
  · funext c a
    show infPart D (if c = p then f a else 0) = 0
    split_ifs
    · exact h0 a
    · exact RingHom.map_zero _
  · show InHat I (algebraMap D.host.E (FA D) r * fe D (if c = p then f a else 0))
    split_ifs
    · exact h1 a
    · rw [RingHom.map_zero, mul_zero]; exact inHat_zero I

theorem units_mul_relation_rearrange_commRing {R : Type} [CommRing R] (x y s a b : R) : x * (y * (s * (a - b))) = x * -(y * (s * b)) + -(x * -(y * (s * a))) := by
  ring

theorem addChar_linearMap_neg_add_eq_one {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (ψ : AddChar R ℂ) (t : M →ₗ[R] R) (A B : M)
    (h : ψ (t A) = ψ (t B)) : ψ (t (B + -A)) = 1 := by
  rw [map_add, map_neg, AddChar.map_add_eq_mul, ← h, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]

theorem symplO_rowMat (S T : HSp D) (hS : S.gram = 1) (hT : T.gram = 1) (r : D.host.E) (o : ℕ) (j : Fin S.rank)
    (p : Fin T.rank) (hp : p.1 = o + j.1) (f : Fin S.rank → AE D) (hf : ∀ a, infPart D (f a) = 0) :
    symplO S T (rowMat S T p f) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank)) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * -(incA D (star r⁻¹) * f j)) :=
  congrArg (fun z => Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * z)) (hO_rowMat S T hS hT r o j p hp f hf)

theorem single_inf {n : ℕ} (i : Fin n) (s : AE D) (hs : infPart D s = 0) (a : Fin n) :
    infPart D ((Pi.single i s : Fin n → AE D) a) = 0 := by
  by_cases ha : a = i
  · rw [ha, Pi.single_eq_same]; exact hs
  · rw [Pi.single_eq_of_ne ha]; exact RingHom.map_zero _

theorem hatPt_single (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (p : Fin T.rank)
    (i : Fin S.rank) (σ : AE D) (hσ : infPart D σ = 0) (h1 : InHat I (algebraMap D.host.E (FA D) r * fe D σ)) :
    HatPt r I (rowMat S T p (Pi.single i σ)) :=
  hatPt_rowMat S T r I p _ (single_inf i σ hσ) fun a => by
    by_cases ha : a = i
    · rw [ha, Pi.single_eq_same]; exact h1
    · rw [Pi.single_eq_of_ne ha, RingHom.map_zero, mul_zero]; exact inHat_zero I

theorem hatPt_act (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (p : Fin T.rank) (g : GA D S)
    (i : Fin S.rank) (σ : AE D) (hσ : infPart D σ = 0)
    (h2 : ∀ k, InHat I (algebraMap D.host.E (FA D) r * fe D σ * fe D (mt S g⁻¹ i k))) :
    HatPt r I (actO S T g 1 (rowMat S T p (Pi.single i σ))) := by
  rw [actO_rowMat]
  refine hatPt_rowMat S T r I p _ (fun a => by rw [RingHom.map_mul, hσ, zero_mul]) fun a => ?_
  rw [RingHom.map_mul, ← mul_assoc]; exact h2 a

theorem single_eq_mul_one {R : Type} [CommRing R] {n : ℕ} (i j : Fin n) (s : R) :
    (Pi.single i s : Fin n → R) j = s * (1 : Matrix (Fin n) (Fin n) R) i j := by
  by_cases ha : j = i
  · rw [ha, Pi.single_eq_same, Matrix.one_apply_eq, mul_one]
  · rw [Pi.single_eq_of_ne ha, Matrix.one_apply_ne (Ne.symm ha), mul_zero]

theorem degree_lower_bound_of_rank_split {R M : Type} [CommRing R] [CommRing M] [Algebra R M] (ψ : AddChar R ℂ) {n : ℕ} (x y s : M) (i j : Fin n)
    (N : Matrix (Fin n) (Fin n) M)
    (h : ψ (Algebra.trace R M (x * -(y * (Pi.single i s : Fin n → M) j))) = ψ (Algebra.trace R M (x * -(y * (s * N i j))))) :
    ψ (Algebra.trace R M (x * (y * (s * (1 - N) i j)))) = 1 := by
  rw [single_eq_mul_one] at h
  rw [Matrix.sub_apply, units_mul_relation_rearrange_commRing]
  exact addChar_linearMap_neg_add_eq_one ψ _ _ _ h

theorem char_trace_eq_one : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
  (o : ℕ) (g : GA D S), S.gram = 1 → T.gram = 1 → o + S.rank ≤ T.rank →
  (∀ u : WO S T, HatPt r I u → HatPt r I (actO S T g 1 u) →
    ψ (symplO S T (2 • u) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank))) =
      ψ (symplO S T (actO S T g 1 (2 • u)) (finPt (S := S) (T := T) rfl rfl r (unitBlock D o S.rank T.rank)))) →
  ∀ (σ : AE D) (i j : Fin S.rank), infPart D σ = 0 → InHat I (algebraMap D.host.E (FA D) r * fe D σ) →
  (∀ k, InHat I (algebraMap D.host.E (FA D) r * fe D σ * fe D (mt S g⁻¹ i k))) →
  ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (incA D (star r⁻¹) * (2 * σ * (1 - mt S g⁻¹) i j)))) = 1 := by
  intro D ψ S T r I o g hS hT ho H σ i j hσ h1 h2
  obtain ⟨p, hp⟩ : ∃ p : Fin T.rank, p.1 = o + j.1 := ⟨⟨o + j.1, by have := j.2; omega⟩, rfl⟩
  have h2σ : infPart D (2 * σ) = 0 := by rw [RingHom.map_mul, hσ, mul_zero]
  have key := H (rowMat S T p (Pi.single i σ)) (hatPt_single S T r I p i σ hσ h1) (hatPt_act S T r I p g i σ hσ h2)
  rw [two_smul_rowMat, actO_rowMat] at key
  have a1 := symplO_rowMat S T hS hT r o j p hp _ (single_inf i _ h2σ)
  have a2 := symplO_rowMat S T hS hT r o j p hp (fun a => 2 * σ * mt S g⁻¹ i a)
    (fun a => by rw [RingHom.map_mul, h2σ, zero_mul])
  exact degree_lower_bound_of_rank_split ψ _ _ _ i j _ ((congrArg ψ a1).symm.trans (key.trans (congrArg ψ a2)))

end GlobalTheory.CosetOrth.Pairing
