import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralBasisOfLatticeAtPlaceStable
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsDvdCoprimeMulPow
import Formalism.SharpRestriction.CuspSpanNormBounds.JExistsNatSmulMemL

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FinPtsGen.UnitPow

theorem exists_pow_sub_one {A R : Type} [CommRing A] [CommRing R] (ι : R →+* A) (O : Subring A) (M : ℕ)
    [Finite (R ⧸ Ideal.span {(M : R)})] (hι : ∀ u, ι u ∈ O)
    (hd : ∀ z ∈ O, ∃ u : R, ∃ w ∈ O, z = ι u + (M : A) * w) (x y : A) (hx : x ∈ O) (hy : y ∈ O)
    (hxy : x * y = 1) : ∃ m : ℕ, 0 < m ∧ ∃ r ∈ O, x ^ m - 1 = (M : A) * r := by
  choose u w hw e using fun k : ℕ => hd (x ^ k) (pow_mem hx k)
  have key : ∀ k l : ℕ, k < l →
      Ideal.Quotient.mk (Ideal.span {(M : R)}) (u k) = Ideal.Quotient.mk (Ideal.span {(M : R)}) (u l) →
      ∃ m : ℕ, 0 < m ∧ ∃ r ∈ O, x ^ m - 1 = (M : A) * r := by
    intro k l hkl h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h.symm)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkl.le
    refine ⟨m, by omega, y ^ k * (ι c + w (k + m) - w k),
      mul_mem (pow_mem hy k) (sub_mem (add_mem (hι c) (hw _)) (hw _)), ?_⟩
    have h1 : x ^ k * y ^ k = 1 := by rw [← mul_pow, hxy, one_pow]
    have h2 : ι c * (M : A) = ι (u (k + m)) - ι (u k) := by
      rw [← map_sub, ← hc, map_mul, map_natCast]
    have h3 := e (k + m)
    have h4 := e k
    rw [pow_add] at h3
    linear_combination (1 - x ^ m) * h1 + y ^ k * h3 - y ^ k * h4 - y ^ k * h2
  obtain ⟨k, l, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite
    fun k : ℕ => Ideal.Quotient.mk (Ideal.span {(M : R)}) (u k)
  rcases lt_or_gt_of_ne hne with hl | hl
  · exact key k l hl h
  · exact key l k hl h.symm

theorem exists_unit_pow_congr_one : ∀ {D : D7} (t s : Af D.host.F ⊗[D.host.F] D.host.E), t ∈ intAE D → s ∈ intAE D → (1 + t) * (1 + s) = 1 →
    ∀ M : ℕ, 0 < M → ∃ m : ℕ, 0 < m ∧ ∃ r ∈ intAE D, (1 + t) ^ m - 1 = (M : Af D.host.F ⊗[D.host.F] D.host.E) * r := by
  intro D t s ht hs hts M hM
  have hone : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D :=
    AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, 1, rfl⟩
  let O : Subring (Af D.host.F ⊗[D.host.F] D.host.E) :=
    { carrier := intAE D
      mul_mem' := fun ha hb => GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha hb
      one_mem' := hone
      add_mem' := fun ha hb => add_mem ha hb
      zero_mem' := zero_mem _
      neg_mem' := fun ha => neg_mem ha }
  let ι : 𝓞 D.host.E →+* Af D.host.F ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F) (B := D.host.E)).toRingHom.comp
      (algebraMap (𝓞 D.host.E) D.host.E)
  have hι : ∀ u, ι u = (1 : Af D.host.F) ⊗ₜ[D.host.F] (u : D.host.E) := fun _ => rfl
  have : Finite (𝓞 D.host.E ⧸ Ideal.span {(M : 𝓞 D.host.E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hM.ne')
  refine exists_pow_sub_one ι O M (fun u => ?_) (fun z hz => ?_) (1 + t) (1 + s) (add_mem hone ht) (add_mem hone hs) hts
  · exact AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, u, hι u⟩
  · obtain ⟨u, w, hw, e⟩ := GlobalTheory.IwaPlace.FreeAt.intAE_dense M hM hz
    exact ⟨u, w, hw, by rw [hι, ← nsmul_eq_mul]; exact e⟩

end GlobalTheory.FinPtsGen.UnitPow

section
open scoped Matrix

namespace GlobalTheory.FinPtsGen.Cong

theorem mul_mem_latHat {D : D7} {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    ∀ a ∈ intAE D, ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E)),
      (fun i => a * y i) ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E)) := by
  intro a ha y hy
  change y ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) at hy
  change _ ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E))
  induction ha using AddSubgroup.closure_induction with
  | mem a ha =>
    obtain ⟨s, hs, o, rfl⟩ := ha
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨s * t, fun v => mul_mem (hs v) (ht v), o • x,
        Λ.smul_mem o hx, ?_⟩
      funext i
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      rfl
    | zero =>
      simp only [Pi.zero_apply, mul_zero]
      exact zero_mem _
    | add u w _ _ hu hw =>
      simp only [Pi.add_apply, mul_add]
      exact add_mem hu hw
    | neg u _ hu =>
      simp only [Pi.neg_apply, mul_neg]
      exact neg_mem hu
  | zero =>
    simp only [zero_mul]
    exact zero_mem _
  | add u w _ _ hu hw =>
    simp only [add_mul]
    exact add_mem hu hw
  | neg u _ hu =>
    simp only [neg_mul]
    exact neg_mem hu

theorem exists_nat_smul_mem_of_fg {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ Q : Submodule (𝓞 E) (Fin n → E)) (hspan : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (hQ : Q.FG) :
    ∃ d : ℕ, 0 < d ∧ ∀ q ∈ Q, d • q ∈ Λ := by
  classical
  obtain ⟨s, rfl⟩ := hQ
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, one_pos, fun q hq => ?_⟩
    rw [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hq
    subst hq
    rw [smul_zero]
    exact zero_mem _
  | insert a s _ ih =>
    obtain ⟨d, hd, hds⟩ := ih
    obtain ⟨e, he, hea⟩ := Formalism.MainNotions.LatticeGluingRadicals.j_exists_nat_smul_memL Λ (x := a) (by rw [hspan]; trivial)
    refine ⟨e * d, Nat.mul_pos he hd, fun q hq => ?_⟩
    rw [Finset.coe_insert, Submodule.mem_span_insert] at hq
    obtain ⟨o, z, hz, rfl⟩ := hq
    rw [smul_add]
    refine add_mem ?_ ?_
    · have h1 : (e * d) • (o • a) = o • (d • (e • a)) := by
        rw [← mul_smul, mul_comm d e, smul_comm]
      rw [h1]
      exact Λ.smul_mem o (nsmul_mem hea d)
    · rw [mul_smul]
      exact nsmul_mem (hds z hz) e

theorem mul_rearr {A : Type} [CommRing A] (n d r w : A) : n * d * r * w = n * (r * (d * w)) := by ring

theorem mulVec_natCast_smul_map {D : D7} {n : ℕ} (P : Matrix (Fin n) (Fin n) D.host.E) (d : ℕ)
    (z : Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :
    ((d : D.host.E) • P).map (inclR (F := D.host.F) (Af D.host.F)) *ᵥ z =
      fun i => (d : Af D.host.F ⊗[D.host.F] D.host.E) * (P.map (inclR (F := D.host.F) (Af D.host.F)) *ᵥ z) i := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast,
    Finset.mul_sum, mul_assoc]

theorem finCong_of_eq_one_add : ∀ {D : D7} (V : HSp D) (P : Matrix (Fin V.rank) (Fin V.rank) D.host.E), ∃ d : ℕ, 0 < d ∧
    ∀ (N : ℕ) (r : Af D.host.F ⊗[D.host.F] D.host.E), r ∈ intAE D → ∀ x : GA D V,
      ((finHom V x : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _) =
        1 + (((N * d : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * r) • P.map (inclR (F := D.host.F) (Af D.host.F)) →
      GlobalTheory.Member.FinCong V N x := by
  intro D V P
  obtain ⟨hlat, -, hfg, hspan, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  let f : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
    (Matrix.mulVecLin P).restrictScalars (𝓞 D.host.E)
  obtain ⟨d, hd, hdm⟩ := exists_nat_smul_mem_of_fg (GlobalTheory.Member.latC V) ((GlobalTheory.Member.latC V).map f) hspan (hfg.map f)
  refine ⟨d, hd, fun N r hr x hx z hz => ?_⟩
  have hPx : ∀ v ∈ (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)),
      ((d : D.host.E) • P) *ᵥ v ∈ (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := fun v hv => by
    rw [Matrix.smul_mulVec, Nat.cast_smul_eq_nsmul]
    exact hdm _ (Submodule.mem_map_of_mem hv)
  have hz' : z ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
    change z ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
    rw [← hlat]; exact hz
  have hw := GlobalTheory.Ker.DCos.mulVec_mem_latHat hPx hz'
  rw [mulVec_natCast_smul_map] at hw
  have hy := mul_mem_latHat (GlobalTheory.Member.latC V) r hr _ hw
  refine ⟨fun i => r * ((d : Af D.host.F ⊗[D.host.F] D.host.E) *
    (P.map (inclR (F := D.host.F) (Af D.host.F)) *ᵥ z) i), ?_, ?_⟩
  · rw [hlat]; exact hy
  · rw [hx, Matrix.add_mulVec, Matrix.one_mulVec, add_sub_cancel_left]
    funext i
    simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Nat.cast_mul, nsmul_eq_mul]
    exact mul_rearr _ _ _ _

end GlobalTheory.FinPtsGen.Cong

end

namespace GlobalTheory.FinPtsGen

section Split

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts IsDedekindDomain NumberField
open GlobalTheory.IdemModTwo GlobalTheory.Member GlobalTheory.UnRep GlobalTheory.UnitarySplit GlobalTheory.SplitCharTrivial
open scoped TensorProduct

variable {D : D7} {V : HSp D} (H : Subgroup (GA D V))

theorem mem_of_finset (hs : ∀ e, IsSplitIdem D e → ∀ g, Formalism.L2.Theta.SuppAt e V g → g ∈ H)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (hS : ∀ v ∈ S, SplitPl (cF D) v) :
    ∀ g : GA D V, (∑ v ∈ S, pl D v) • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 → g ∈ H := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro g hg
    rw [Finset.sum_empty, zero_smul] at hg
    rw [show g = 1 from mt_ext (sub_eq_zero.1 hg.symm)]
    exact one_mem H
  | insert v S hv ih =>
    intro g hg
    obtain ⟨e, he⟩ := GlobalTheory.MovedSplit.exists_splitAt D v (hS v (Finset.mem_insert_self _ _))
    have hp : pl D v * pl D v = pl D v := by
      rw [← map_mul, singleV_mul, GlobalTheory.SplitIdem.evalV_singleV_same, one_mul]
    have hp' : (1 - pl D v) * (1 - pl D v) = 1 - pl D v := by linear_combination hp
    have hσ : cA D (pl D v) = pl D v := cA_fj D _
    have hσ' : cA D (1 - pl D v) = 1 - pl D v := by rw [map_sub, map_one, hσ]
    have hq : pl D v * ∑ w ∈ S, pl D w = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun w hw => pl_mul_pl fun h => hv (h ▸ hw)
    rw [Finset.sum_insert hv] at hg
    rw [← cutA_mul V _ hp hσ hp' hσ' g]
    refine mul_mem (hs e ((isSplitIdem_iff e).2 ⟨v, he⟩) _ ?_)
      (ih (fun w hw => hS w (Finset.mem_insert_of_mem hw)) _ ?_)
    · intro i j
      rw [mt_cutA, add_sub_cancel_left, he.2.2, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hp]
    · rw [mt_cutA, add_sub_cancel_left, smul_smul]
      conv_rhs => rw [← hg, smul_smul]
      congr 1
      linear_combination hp

theorem mem_of_idem (hs : ∀ e, IsSplitIdem D e → ∀ g, Formalism.L2.Theta.SuppAt e V g → g ∈ H) (e : Af D.host.F)
    (h1 : e * e = e) (h2 : {v | e v ≠ 0}.Finite) (h3 : ∀ v, e v ≠ 0 → SplitPl (cF D) v) (g : GA D V)
    (hg : fj D e • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1) : g ∈ H := by
  refine mem_of_finset H hs h2.toFinset (fun v hv => h3 v (h2.mem_toFinset.1 hv)) g ?_
  rw [← map_sum, ← GlobalTheory.SplitReps.idem_eq_sum e h1 h2.toFinset (fun v => h2.mem_toFinset), hg]

theorem mem_of_suppSplit (hs : ∀ e, IsSplitIdem D e → ∀ g, Formalism.L2.Theta.SuppAt e V g → g ∈ H) {N : ℕ}
    {h : GA D V} (hh : h ∈ GfC V) (h0 : SuppSplit (cF D) N (finHom V h).1) : h ∈ H := by
  obtain ⟨e, h1, h2, h3, h4⟩ := h0
  refine mem_of_idem H hs e h1 h2 (fun v hv => (h3 v hv).1) h ?_
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  refine parts_inj D _ _ ?_ ?_
  · have h6 : (Formalism.L2.Theta.mt V h).map (infPart D) = 1 := congrArg Units.val (show infHom V h = 1 from hh)
    rw [RingHom.map_mul, map_sub_one, h6, sub_self, Matrix.zero_apply, mul_zero]
  · rw [RingHom.map_mul, map_sub_one]
    exact congrFun (congrFun h4 i) j

end Split

section Key

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts IsDedekindDomain NumberField
open GlobalTheory.IdemModTwo GlobalTheory.Member GlobalTheory.UnRep GlobalTheory.UnitarySplit GlobalTheory.SplitCharTrivial
open scoped TensorProduct

variable {D : D7} {V : HSp D}

theorem fj_one_idem : fj D 1 * fj D 1 = fj D 1 := by rw [← map_mul, mul_one]

def pFin (V : HSp D) : GA D V →* GA D V := cutA V (fj D 1) fj_one_idem (cA_fj D 1)

theorem pFin_mul_pInf (g : GA D V) : pFin V g * pInf V g = g :=
  cutA_mul V (fj D 1) fj_one_idem (cA_fj D 1) idem_inf conj_inf g

theorem map_one_add_smul {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (c : R)
    (M : Matrix (Fin n) (Fin n) R) : (1 + c • M).map f = 1 + f c • M.map f := by
  ext i j
  simp [Matrix.one_apply, apply_ite f]

variable {P : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (hP : P * P = P)
  (hJ : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P * V.gram = V.gram * P)
include hP hJ

theorem rfA_congr {a b : Formalism.L2.Theta.AE D} (h : a = b) (ha : a * cA D a = 1) (hb : b * cA D b = 1) :
    rfA hP hJ a ha = rfA hP hJ b hb := by
  subst h
  rfl

theorem mt_pow_rfA (a : Formalism.L2.Theta.AE D) (ha : a * cA D a = 1) (m : ℕ) :
    Formalism.L2.Theta.mt V (rfA hP hJ a ha ^ m) = 1 + (a ^ m - 1) • P.map (incA D) := by
  have hP' : P.map (incA D) * P.map (incA D) = P.map (incA D) := by rw [← Matrix.map_mul, hP]
  induction m with
  | zero =>
    rw [pow_zero, pow_zero, sub_self, zero_smul, add_zero]
    exact congrArg Units.val (map_one (matHom V))
  | succ m ih =>
    rw [pow_succ, mt_mul, ih, mt_rfA, proj_mul _ hP', pow_succ]

end Key

section Reflection

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts IsDedekindDomain NumberField
open GlobalTheory.IdemModTwo GlobalTheory.Member GlobalTheory.UnRep GlobalTheory.UnitarySplit GlobalTheory.SplitCharTrivial
open scoped TensorProduct

variable {D : D7} {V : HSp D} (H : Subgroup (GA D V))

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem mem_refl {N : ℕ} (hN : 0 < N) (hroot : ∀ g ∈ GfC V, ∀ m : ℕ, 0 < m → g ^ m ∈ H → g ∈ H)
    (hcong : ∀ k ∈ GfC V, FinCong V N k → k ∈ H)
    (hs : ∀ e, IsSplitIdem D e → ∀ g, Formalism.L2.Theta.SuppAt e V g → g ∈ H)
    {P : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (hP : P * P = P)
    (hJ : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P * V.gram = V.gram * P)
    {u : D.host.E} (hu : u * cF D u = 1) : pFin V (rfA hP hJ _ (norm_incA hu)) ∈ H := by
  obtain ⟨-, -, -, -, c2, -, c1, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) u
  obtain ⟨e, he1, he2, he3, a, ha, b, hab⟩ := exists_cut (cF D) c2 1 one_pos (x - 1) (y - 1)
    (by rw [Nat.cast_one, one_mul, add_sub_cancel]; exact nonZeroDivisors.ne_zero hy) u
    (by rw [← hxy]; simp only [Nat.cast_one, one_mul, RingOfIntegers.coe_eq_algebraMap, map_sub, map_one,
      add_sub_cancel]) hu
  rw [one_smul] at hab
  have hε : fj D e * fj D e = fj D e := by rw [← map_mul, he1]
  have hσ : cA D (fj D e) = fj D e := cA_fj D e
  have hε' : (1 - fj D e) * (1 - fj D e) = 1 - fj D e := by linear_combination hε
  have hσ' : cA D (1 - fj D e) = 1 - fj D e := by rw [map_sub, map_one, hσ]
  rw [← cutA_mul V _ hε hσ hε' hσ' (pFin V _)]
  refine mul_mem (mem_of_idem H hs e he1 he2 he3 _ (by rw [mt_cutA, add_sub_cancel_left, smul_smul, hε])) ?_
  have hee : (1 - e) * (1 - e) = 1 - e := by linear_combination he1
  have hn : (1 + fj D (1 - e) * (incA D u - 1)) * cA D (1 + fj D (1 - e) * (incA D u - 1)) = 1 :=
    norm_cut (cA D) _ (by rw [← map_mul, hee]) (cA_fj D _) _ (norm_incA hu)
  have hy' : cutA V (1 - fj D e) hε' hσ' (pFin V (rfA hP hJ _ (norm_incA hu))) =
      rfA hP hJ (1 + fj D (1 - e) * (incA D u - 1)) hn := by
    unfold pFin
    rw [cutA_rfA, cutA_rfA]
    refine rfA_congr hP hJ ?_ _ _
    have hs1 : (1 - fj D e) * fj D 1 = fj D (1 - e) := by
      rw [sub_mul, one_mul (fj D 1), ← map_mul (fj D) e 1, mul_one, map_sub (fj D) 1 e]
    rw [add_sub_cancel_left, ← mul_assoc (1 - fj D e), hs1]
  rw [hy']
  have hinf : infPart D (1 + fj D (1 - e) * (incA D u - 1)) = 1 := by
    rw [map_add, map_one, map_mul, inf_fj, zero_mul, add_zero]
  have hG : rfA hP hJ _ hn ∈ GfC V := by
    refine MonoidHom.mem_ker.2 (Units.ext ?_)
    change (Formalism.L2.Theta.mt V (rfA hP hJ _ hn)).map (infPart D) = 1
    rw [mt_rfA, map_one_add_smul, map_sub, hinf, map_one, sub_self, zero_smul, add_zero]
  have hfin : finPart D (1 + fj D (1 - e) * (incA D u - 1)) = 1 + a ⊗ₜ[D.host.F] (b : D.host.E) := by
    rw [← hab, map_add (finPart D), map_one (finPart D), map_mul (finPart D), fin_fj, map_sub (finPart D), map_one (finPart D)]
    congr 1
    change (1 - e) ⊗ₜ[D.host.F] (1 : D.host.E) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] u - 1) = _
    rw [Algebra.TensorProduct.one_def, ← TensorProduct.tmul_sub, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul]
  set cb : 𝓞 D.host.E := RingOfIntegers.mapRingEquiv (cF D).toRingEquiv b with hcbdef
  have hcb : (cb : D.host.E) = cF D (b : D.host.E) := rfl
  have hab' : (1 - e) ⊗ₜ[D.host.F] (cF D u - 1) = a ⊗ₜ[D.host.F] (cb : D.host.E) := by
    have := congrArg (Algebra.TensorProduct.map (AlgHom.id D.host.F (Af D.host.F))
      (cF D : D.host.E →ₐ[D.host.F] D.host.E)) hab
    simpa [hcb] using this
  have hinv : (1 + a ⊗ₜ[D.host.F] (b : D.host.E)) * (1 + a ⊗ₜ[D.host.F] (cb : D.host.E)) = 1 := by
    rw [← hab, ← hab']
    have e1 : ∀ y z : D.host.E, (1 + (1 - e) ⊗ₜ[D.host.F] y) * (1 + (1 - e) ⊗ₜ[D.host.F] z) =
        1 + (1 - e) ⊗ₜ[D.host.F] (y + z + y * z) := by
      intro y z
      rw [add_mul, one_mul, mul_add, mul_one, Algebra.TensorProduct.tmul_mul_tmul, hee, TensorProduct.tmul_add,
        TensorProduct.tmul_add]
      abel
    rw [e1, show u - 1 + (cF D u - 1) + (u - 1) * (cF D u - 1) = 0 by linear_combination hu,
      TensorProduct.tmul_zero, add_zero]
  obtain ⟨d, hd, hfc⟩ := Cong.finCong_of_eq_one_add V P
  obtain ⟨m, hm, r, hr, hpow⟩ := UnitPow.exists_unit_pow_congr_one (a ⊗ₜ[D.host.F] (b : D.host.E)) (a ⊗ₜ[D.host.F] (cb : D.host.E))
    (AddSubgroup.subset_closure ⟨a, ha, b, rfl⟩) (AddSubgroup.subset_closure ⟨a, ha, cb, rfl⟩) hinv (N * d)
    (Nat.mul_pos hN hd)
  refine hroot _ hG m hm (hcong _ (pow_mem hG m) (hfc N r hr _ ?_))
  change (Formalism.L2.Theta.mt V (rfA hP hJ _ hn ^ m)).map (finPart D) = _
  rw [mt_pow_rfA hP hJ, map_one_add_smul, map_sub (finPart D), map_pow (finPart D), hfin, map_one (finPart D), hpow, Matrix.map_map]
  rfl

end Reflection

section Rat

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts IsDedekindDomain NumberField
open GlobalTheory.IdemModTwo GlobalTheory.Member GlobalTheory.UnRep GlobalTheory.UnitarySplit GlobalTheory.SplitCharTrivial
open scoped TensorProduct

variable {D : D7} {V : HSp D} (H : Subgroup (GA D V))

theorem mem_rat {N : ℕ} (hN : 0 < N) (hroot : ∀ g ∈ GfC V, ∀ m : ℕ, 0 < m → g ^ m ∈ H → g ∈ H)
    (hcong : ∀ k ∈ GfC V, FinCong V N k → k ∈ H)
    (hs : ∀ e, IsSplitIdem D e → ∀ g, Formalism.L2.Theta.SuppAt e V g → g ∈ H)
    (l : List ((Fin V.rank → D.host.E) × D.host.E))
    (hl : ∀ p ∈ l, hermE (cF D) (Matrix.transpose V.gram) p.1 p.1 ≠ 0 ∧ p.2 * cF D p.2 = 1) :
    ∀ γ : GA D V, Formalism.L2.Theta.mt V γ = (l.map fun p => GlobalTheory.UnRep.refl (cF D) (Matrix.transpose V.gram) p.1 p.2).prod.map (incA D) →
      pFin V γ ∈ H := by
  induction l with
  | nil =>
    intro γ h
    rw [List.map_nil, List.prod_nil, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)] at h
    rw [show γ = 1 from mt_ext h, map_one]
    exact one_mem H
  | cons p l ih =>
    intro γ h
    obtain ⟨hx, hu⟩ := hl p List.mem_cons_self
    obtain ⟨P, hP, hJ, hr⟩ := exists_proj V p.1 hx
    rw [List.map_cons, List.prod_cons, Matrix.map_mul, hr, ← mt_rfA_rat hP hJ hu] at h
    have h1 := mem_refl H hN hroot hcong hs hP hJ hu
    generalize rfA hP hJ _ (norm_incA hu) = r at h h1
    have h2 := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (r⁻¹ * γ) (by
      rw [mt_mul, h, ← mul_assoc, ← mt_mul, inv_mul_cancel]
      exact one_mul _)
    rw [← mul_inv_cancel_left r γ, map_mul]
    exact mul_mem h1 h2

theorem mem_GQ {N : ℕ} (hN : 0 < N) (hroot : ∀ g ∈ GfC V, ∀ m : ℕ, 0 < m → g ^ m ∈ H → g ∈ H)
    (hcong : ∀ k ∈ GfC V, FinCong V N k → k ∈ H)
    (hs : ∀ e, IsSplitIdem D e → ∀ g, Formalism.L2.Theta.SuppAt e V g → g ∈ H) (γ : GA D V) (hγ : γ ∈ GQ V) :
    pFin V γ ∈ H := by
  obtain ⟨-, -, -, -, c2, -, c1, gh, gd, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨r1, r2, -⟩ := GlobalTheory.Member.RatElt.rational_elements D V
  obtain ⟨γ', hγ'⟩ := (r1 γ).1 hγ
  obtain ⟨l, hl, e⟩ := GlobalTheory.UnRep.isUnE_eq_prod_refl _ _ (cF D) V.rank (Matrix.transpose V.gram) ⟨c2, c1, gh, gd⟩ γ'.1 fun x y => by
    have := r2 γ γ' hγ' x y
    rwa [GlobalTheory.UnRep.Space.herm_neg_eq, GlobalTheory.UnRep.Space.herm_neg_eq, neg_inj] at this
  exact mem_rat H hN hroot hcong hs l hl γ (by rw [← e]; exact congrArg Units.val hγ')

theorem mul_eq_pFin {γ a : GA D V} (ha : a ∈ GinfC V) (h : γ * a ∈ GfC V) : γ * a = pFin V γ := by
  have hq : pInf V γ * a = 1 := by
    refine ga_ext V ?_ ?_
    · rw [map_mul, infHom_pInf, ← map_mul, map_one]
      exact h
    · rw [map_mul, finHom_pInf, one_mul, map_one]
      exact ha
  calc γ * a = pFin V γ * (pInf V γ * a) := by rw [← mul_assoc, pFin_mul_pInf]
    _ = pFin V γ := by rw [hq, mul_one]

end Rat

theorem mem_of_level_of_split : ∀ {D : D7} (V : HSp D) (H : Subgroup (GA D V)) (N : ℕ), 0 < N → (∀ g ∈ GfC V, ∀ m : ℕ, 0 < m → g ^ m ∈ H → g ∈ H) →
    (∀ k ∈ GfC V, GlobalTheory.Member.FinCong V N k → k ∈ H) → (∀ e, IsSplitIdem D e → ∀ g, Formalism.L2.Theta.SuppAt e V g → g ∈ H) → ∀ g ∈ GfC V, g ∈ H := by
  intro D V H N hN hroot hcong hs g hg
  obtain ⟨γ, hγ, a, ha, h, hh, k, hk, e, hc, hsp⟩ := GlobalTheory.UnRep.Space.exists_rep_suppSplit D V N hN g
  have hga : γ * a ∈ GfC V := by
    have : γ * a = g * k⁻¹ * h⁻¹ := by rw [e]; group
    rw [this]
    exact mul_mem (mul_mem hg (inv_mem hk)) (inv_mem hh)
  rw [e, mul_eq_pFin ha hga]
  exact mul_mem (mul_mem (mem_GQ H hN hroot hcong hs γ hγ) (mem_of_suppSplit H hs hh hsp)) (hcong k hk hc)

end GlobalTheory.FinPtsGen

end
