import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ScaledFiniteMatrixMemLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.PlaceVec

open GlobalTheory.PlaceModel GlobalTheory.AdelicLatMove

theorem eq_zero_of_mul_idem_sum {A ι : Type} [CommRing A] (tf : ∀ (n : ℕ) (z : A), 0 < n → n * z = 0 → z = 0)
    (p : ι → A) (s : Finset ι) (hp : ∀ i ∈ s, p i * p i = p i) :
    ∀ (n : ℕ) (z : A), 0 < n → z * (n + ∑ i ∈ s, p i) = 0 → z = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => intro n z hn h; exact tf n z hn (by simpa [mul_comm] using h)
  | insert a s ha ih =>
    intro n z hn h
    rw [Finset.sum_insert ha] at h
    have h1 := hp a (Finset.mem_insert_self _ _)
    have ih' := ih fun i hi => hp i (Finset.mem_insert_of_mem hi)
    have h2 : z * p a = 0 := ih' (n + 1) _ n.succ_pos (by
      push_cast
      linear_combination (p a) * h - z * h1)
    exact ih' n z hn (by linear_combination h - h2)

theorem idem_eq_zero_of_sum {A ι : Type} [CommRing A] (tf : ∀ (n : ℕ) (z : A), 0 < n → n * z = 0 → z = 0)
    (p : ι → A) (s : Finset ι) (hp : ∀ i ∈ s, p i * p i = p i) (h : ∑ i ∈ s, p i = 0) : ∀ i ∈ s, p i = 0 := by
  intro i hi
  classical
  rw [← Finset.add_sum_erase s p hi] at h
  refine eq_zero_of_mul_idem_sum tf p (s.erase i) (fun j hj => hp j (Finset.mem_of_mem_erase hj)) 1 _ one_pos ?_
  push_cast
  linear_combination (p i) * h - hp i hi

theorem sum_idem_mul_self {A ι : Type} [CommRing A] (tf : ∀ (n : ℕ) (z : A), 0 < n → n * z = 0 → z = 0)
    (σ : A →+* A) (p : ι → A) (s : Finset ι) (hp : ∀ i ∈ s, p i * p i = p i)
    (h0 : (∑ i ∈ s, p i) * σ (∑ i ∈ s, p i) = 0)
    (h : ∀ i ∈ s, ∀ j ∈ s, j ≠ i → p i * σ (p j) = 0 → p j * σ (p i) = 0 → p i * p j = 0) :
    (∑ i ∈ s, p i) * (∑ i ∈ s, p i) = ∑ i ∈ s, p i := by
  rw [map_sum, Finset.sum_mul_sum, ← Finset.sum_product'] at h0
  have hz := idem_eq_zero_of_sum tf (fun x : ι × ι => p x.1 * σ (p x.2)) _ (fun i hi => by
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hi
    rw [mul_mul_mul_comm, ← map_mul, hp _ h1, hp _ h2]) h0
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j hj hji => ?_) (fun h => absurd hi h), hp i hi]
  exact h i hi j hj hji (hz (i, j) (Finset.mem_product.2 ⟨hi, hj⟩)) (hz (j, i) (Finset.mem_product.2 ⟨hj, hi⟩))

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tmul_mem_int {α : FiniteAdeleRing (𝓞 F) F} (hα : α ∈ Formalism.UG.intAd F) (o : 𝓞 E) :
    (o : E) ⊗ₜ[F] α ∈ Formalism.L2.Herm.intAf F E := by
  have h1 : (1 : E) ⊗ₜ[F] α ∈ Formalism.L2.Herm.intAf F E :=
    Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)
  have h2 : (o : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) ∈ Formalism.L2.Herm.intAf F E :=
    Subring.subset_closure (Or.inl ⟨⟨o, o, rfl⟩, rfl⟩)
  have := mul_mem h2 h1
  rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this

theorem exists_nsmul_mem_int (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    ∃ d : ℕ, 0 < d ∧ d • z ∈ Formalism.L2.Herm.intAf F E := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩
  | add x y hx hy =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, hy⟩ := hy
    refine ⟨N * M, mul_pos hN hM, ?_⟩
    rw [nsmul_add]
    refine add_mem ?_ ?_
    · rw [mul_nsmul]; exact nsmul_mem hx M
    · rw [mul_nsmul']; exact nsmul_mem hy N
  | tmul y a =>
    obtain ⟨x, b, hb, rfl⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos a
    obtain ⟨N, hN, o, ho⟩ := GlobalTheory.AdIdem.exists_nat_mul_integral E y
    obtain ⟨M, hM, o', ho'⟩ := GlobalTheory.AdIdem.exists_nat_mul_integral E (x • y)
    refine ⟨N * M, mul_pos hN hM, ?_⟩
    rw [TensorProduct.tmul_add, nsmul_add, one_smul, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
    refine add_mem ?_ ?_
    · rw [mul_nsmul', TensorProduct.smul_tmul', nsmul_eq_mul M, ← ho']
      exact nsmul_mem (tmul_mem_int (one_mem _) o') N
    · rw [mul_nsmul, TensorProduct.smul_tmul', nsmul_eq_mul N, ← ho]
      exact nsmul_mem (tmul_mem_int hb o) M

end

variable {D : D7}

theorem natCast_mul_eq_zero (n : ℕ) (z : AE D) (hn : 0 < n) (h : n * z = 0) : z = 0 := by
  have : (n : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have h1 : incA D (n : D.host.E)⁻¹ * n = 1 := by
    rw [← map_natCast (incA D), ← map_mul, inv_mul_cancel₀ this, map_one]
  linear_combination incA D (n : D.host.E)⁻¹ * h - z * h1

theorem splitIdem_eq_or {a b : AE D} (ha : IsSplitIdem D a) (hb : IsSplitIdem D b) (hab : a * cA D b = 0)
    (hba : b * cA D a = 0) : a = b ∨ a * b = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨α, rfl, ha1, ha0⟩, h3⟩ := ha
  obtain ⟨h1', h2', v', ε', ⟨α', rfl, hb1, hb0⟩, h3'⟩ := hb
  by_cases hv : v = v'
  · left
    subst hv
    have : α = α' := by
      refine RestrictedProduct.ext _ _ fun w => ?_
      change evalV D.host.F w α = evalV D.host.F w α'
      by_cases hw : w = v
      · rw [hw, ha1, hb1]
      · rw [ha0 w hw, hb0 w hw]
    subst this
    have h4 : a + cA D a = b + cA D b := h3.trans h3'.symm
    linear_combination (a + b) * h4 - h1 - h2 + hab - hba + h1' + h2'
  · right
    have : α * α' = 0 := by
      refine RestrictedProduct.ext _ _ fun w => ?_
      change evalV D.host.F w (α * α') = evalV D.host.F w 0
      rw [map_mul, map_zero]
      by_cases hw : w = v
      · rw [hb0 w (hw ▸ hv), mul_zero]
      · rw [ha0 w hw, zero_mul]
    have h5 : pairA D.host.F 0 α * pairA D.host.F 0 α' = 0 := Prod.ext (mul_zero _) this
    have h4 : (a + cA D a) * (b + cA D b) = 0 := by rw [h3, h3', ← map_mul, h5, map_zero]
    have e1 : a = a * (a + cA D a) := by rw [mul_add, h1, h2, add_zero]
    have e2 : b = b * (b + cA D b) := by rw [mul_add, h1', h2', add_zero]
    rw [e1, e2, mul_mul_mul_comm, h4, mul_zero]

theorem isIdemAt_inj {e : AE D} {P Q : Formalism.L2.DIV.Pl D.host.E} (hP : Formalism.L2.NTheta.IsIdemAt e P)
    (hQ : Formalism.L2.NTheta.IsIdemAt e Q) : P = Q := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · exact (hP.2 x hx).trans (hQ.2 x hx).symm

theorem idemSum_mul_self {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) : e * e = e := by
  obtain ⟨⟨es, hes, he⟩, h0⟩ := h
  subst he
  refine sum_idem_mul_self (A := AE D) natCast_mul_eq_zero (cA D) es P (fun i hi => (hes i hi).1.1) h0 ?_
  intro i hi j hj hji h1 h2
  rcases splitIdem_eq_or (hes i hi).1 (hes j hj).1 h1 h2 with hij | h
  · exact absurd (isIdemAt_inj (hes j hj) (hij ▸ hes i hi)) hji
  · exact h

theorem idemSum_infPart {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) : infPart D e = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  rw [map_sum]
  exact Finset.sum_eq_zero fun i hi => GlobalTheory.SplitScalar.infPart_splitIdem (hes i hi).1

theorem infPart_cA {a : AE D} (h : infPart D a = 0) : infPart D (cA D a) = 0 := by
  have h1 := GlobalTheory.SplitScalar.realIdem_mul_of_fin h
  have h2 := congrArg (fun z => infPart D (cA D z)) h1
  simp only [map_mul, GlobalTheory.SplitScalar.cA_realIdem, GlobalTheory.SplitScalar.infPart_realIdem, one_mul, map_zero] at h2
  exact h2

theorem cF_mem_int {z : EAf D} (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    cF D z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have : Formalism.L2.Herm.intAf D.host.F D.host.E ≤ (Formalism.L2.Herm.intAf D.host.F D.host.E).comap (cF D) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨β, hβ⟩, rfl⟩)
    · have hb : IsIntegral ℤ (star (b : D.host.E)) := b.2.map (starRingEnd D.host.E).toIntAlgHom
      exact tmul_mem_int (one_mem (Formalism.UG.intAd D.host.F)) ⟨_, hb⟩
    · have := cF_tmul (1 : D.host.E) β
      rw [star_one] at this
      refine Subring.mem_comap.2 (this ▸ ?_)
      exact Subring.subset_closure (Or.inr ⟨⟨β, hβ⟩, rfl⟩)
  exact this hz

theorem finPart_mem_intAE {w : AE D} (hw : toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    finPart D w ∈ intAE D := by
  let c := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm
  have key : ∀ z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, c z ∈ intAE D := by
    intro z hz
    induction hz using Subring.closure_induction with
    | mem r hr =>
      rcases hr with ⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨β, hβ⟩, rfl⟩
      · exact AddSubgroup.subset_closure ⟨1, one_mem (Formalism.UG.intAd D.host.F), b, rfl⟩
      · exact AddSubgroup.subset_closure ⟨β, hβ, 1, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | one => rw [map_one]; exact AddSubgroup.subset_closure ⟨1, one_mem (Formalism.UG.intAd D.host.F), 1, rfl⟩
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | neg a _ ha => rw [map_neg]; exact neg_mem ha
    | mul a b _ _ ha hb => rw [map_mul]; exact GlobalTheory.HeckeConj.mul_mem_intAE D ha hb
  have := key _ hw
  rwa [show c (toEAf D w) = finPart D w from
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm_apply_apply _] at this

theorem exists_common_nsmul {G ι : Type} [AddCommGroup G] [Finite ι] (H : AddSubgroup G) (g : ι → G)
    (h : ∀ i, ∃ d : ℕ, 0 < d ∧ d • g i ∈ H) : ∃ d : ℕ, 0 < d ∧ ∀ i, d • g i ∈ H := by
  classical
  have := Fintype.ofFinite ι
  choose d hd hg using h
  refine ⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul]
  exact nsmul_mem (hg i) _

theorem exists_nsmul_mul_int {a b c d : ℕ} (A : Matrix (Fin a) (Fin b) (EAf D)) (B : Matrix (Fin c) (Fin d) (EAf D)) :
    ∃ k : ℕ, 0 < k ∧ ∀ N : Matrix (Fin b) (Fin c) (EAf D), IsIntM N → IsIntM (k • (A * N * B)) := by
  obtain ⟨k, hk, hA⟩ := exists_common_nsmul (Formalism.L2.Herm.intAf D.host.F D.host.E).toAddSubgroup
    (fun p : Fin a × Fin b => A p.1 p.2) fun p => exists_nsmul_mem_int _
  obtain ⟨l, hl, hB⟩ := exists_common_nsmul (Formalism.L2.Herm.intAf D.host.F D.host.E).toAddSubgroup
    (fun p : Fin c × Fin d => B p.1 p.2) fun p => exists_nsmul_mem_int _
  refine ⟨k * l, mul_pos hk hl, fun N hN i j => ?_⟩
  have : (k * l) • (A * N * B) = (k • A) * N * (l • B) := by
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [this]
  simp only [Matrix.mul_apply]
  exact sum_mem fun p _ => mul_mem (sum_mem fun q _ => mul_mem (hA (i, q)) (hN q p)) (hB (p, j))

variable {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem isIntM_nsmul {a b : ℕ} {N : Matrix (Fin a) (Fin b) (EAf D)} (h : IsIntM N) (k : ℕ) : IsIntM (k • N) :=
  fun i j => nsmul_mem (h i j) k

theorem map_toEAf_nsmul {a b : ℕ} (k : ℕ) (x : Mx D a b) : (k • x).map (toEAf D) = k • x.map (toEAf D) :=
  Matrix.ext fun i j => (toEAf D).toAddMonoidHom.map_nsmul k (x i j)

theorem exists_nsmul_latO_int (hS : ΛS.FG) (hT : ΛT.FG) : ∃ k : ℕ, 0 < k ∧
    ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True,
      IsIntM (k • u.map (toEAf D)) := by
  obtain ⟨A, hA, -, hA2⟩ := GlobalTheory.LatFinMod.exists_int_gen (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl _)
  obtain ⟨B, hB, -, hB2⟩ := GlobalTheory.LatFinMod.exists_int_gen ΛS hS
  obtain ⟨C, hC, -, hC2⟩ := GlobalTheory.LatFinMod.exists_int_gen ΛT hT
  set G := (fun p : _ × _ × _ => GlobalTheory.LatVac.genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C) with hGd
  have hG : G.Finite := (hA.prod (hB.prod hC)).image _
  have := hG.to_subtype
  let O : AddSubgroup D.host.E := (algebraMap (𝓞 D.host.E) D.host.E).range.toAddSubgroup
  obtain ⟨k, hk, hO⟩ := exists_common_nsmul O (fun p : G × Fin T.rank × Fin S.rank => p.1.1 p.2.1 p.2.2) fun p => by
    obtain ⟨d, hd, h⟩ := GlobalTheory.AdIdem.exists_nat_mul_integral D.host.E (p.1.1 p.2.1 p.2.2)
    exact ⟨d, hd, by rw [nsmul_eq_mul]; exact h⟩
  have hsp : ∀ M ∈ Submodule.span ℤ G, ∀ i j, k • M i j ∈ O := by
    intro M hM i j
    induction hM using Submodule.span_induction with
    | mem x hx => exact hO (⟨x, hx⟩, i, j)
    | zero => rw [Matrix.zero_apply, smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [Matrix.add_apply, smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [Matrix.smul_apply, smul_comm]; exact zsmul_mem hx c
  refine ⟨k, hk, fun u hu i j => ?_⟩
  change k • toEAf D (u i j) ∈ _
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    obtain ⟨o, ho⟩ := hsp _ (GlobalTheory.LatFinMod.genMap_mem_span S T (hA2 a ha) (hB2 s hs) (hC2 t ht)) i j
    have h1 := tmul_mem_int (F := D.host.F) hα o
    rw [show (o : D.host.E) = _ from ho, ← TensorProduct.smul_tmul'] at h1
    exact h1
  | zero => rw [Matrix.zero_apply, RingHom.map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.add_apply, RingHom.map_add, smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.neg_apply, RingHom.map_neg, smul_neg]; exact neg_mem hx

theorem exists_nsmul_int_mem_latO (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT) :
    ∃ k : ℕ, 0 < k ∧ ∀ x : WO S T, x.map (infPart D) = 0 → IsIntM (x.map (toEAf D)) →
      k • x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  obtain ⟨k, hk, h⟩ := exists_common_nsmul _
    (fun p : Fin T.rank × Fin S.rank => GlobalTheory.VacUnique.finRat S T (Matrix.single p.1 p.2 1))
    fun p => GlobalTheory.VacUnique.Den.exists_nsmul_finRat_mem D S T ΛS ΛT hS hT _
  refine ⟨k, hk, fun x hx hi => ?_⟩
  have e : x = ∑ p : Fin T.rank × Fin S.rank, x p.1 p.2 • GlobalTheory.VacUnique.finRat S T (Matrix.single p.1 p.2 1) := by
    ext i j
    rw [Matrix.sum_apply, Finset.sum_eq_single (i, j) (fun p _ hp => ?_) (fun h => absurd (Finset.mem_univ _) h)]
    · change _ = x i j * (_ ⊗ₜ _)
      rw [Matrix.single_apply_same]
      have h0 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
      refine GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, h0, zero_mul]) ?_
      rw [RingHom.map_mul]
      exact (mul_one _).symm
    · change x p.1 p.2 * (_ ⊗ₜ _) = 0
      rw [Matrix.single_apply_of_ne _ _ _ _ _ fun h => hp (Prod.ext h.1 h.2), TensorProduct.tmul_zero, mul_zero]
  rw [e, Finset.smul_sum]
  refine sum_mem fun p _ => ?_
  rw [smul_comm]
  exact GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_mem_intAE (hi p.1 p.2)) _ (h p)

theorem exists_nsmul_mem_latO (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT)
    (x : WO S T) (hx : x.map (infPart D) = 0) : ∃ k : ℕ, 0 < k ∧
      k • x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  obtain ⟨k, hk, h⟩ := exists_nsmul_int_mem_latO hS hT
  obtain ⟨l, hl, h'⟩ := exists_common_nsmul (Formalism.L2.Herm.intAf D.host.F D.host.E).toAddSubgroup
    (fun p : Fin T.rank × Fin S.rank => toEAf D (x p.1 p.2)) fun p => exists_nsmul_mem_int _
  refine ⟨k * l, mul_pos hk hl, ?_⟩
  rw [mul_smul]
  refine h _ (Matrix.ext fun i j => ?_) ?_
  · have h0 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    exact ((infPart D).toAddMonoidHom.map_nsmul l (x i j)).trans ((congrArg (l • ·) h0).trans (nsmul_zero l))
  · rw [map_toEAf_nsmul]
    exact fun i j => h' (i, j)

theorem mem_waveSpan {G : Type} [AddCommGroup G] {χ : G → G → ℂ} {X Y L L' : AddSubgroup G} (h : IsBichar χ)
    (hL : L ≤ X) (hL' : L' ≤ Y) (hLL' : ∀ u ∈ L, ∀ y ∈ L', χ u y = 1)
    (hX : ∀ x ∈ X, (∀ y ∈ L', χ x y = 1) → x ∈ L)
    (dX : ∀ k : ℕ, 0 < k → ∀ x ∈ X, ∃ x' ∈ X, k • x' = x) (dY : ∀ k : ℕ, 0 < k → ∀ y ∈ Y, ∃ y' ∈ Y, k • y' = y)
    (tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : G => k • t)
    (hfin : ∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L, ∃ r ∈ R, ∃ u ∈ L, t = r + k • u)
    (Φ : G → ℂ) (h1 : ∀ t, Φ t ≠ 0 → t ∈ X) (k : ℕ) (hk : 0 < k) (h2 : ∀ u ∈ L, ∀ t, Φ (t + k • u) = Φ t)
    (h3 : ∀ t, Φ t ≠ 0 → k • t ∈ L) : Φ ∈ waveSpan χ X Y L := by
  obtain ⟨R, hR, hR'⟩ := hfin k hk
  obtain ⟨R2, hR2, hR2'⟩ := hfin (k * k) (Nat.mul_pos hk hk)
  have hP : ((fun t : G => k • t) ⁻¹' R2).Finite := hR2.preimage (tf k hk).injOn
  refine mem_of_finite_cosets (K := L.map (nsmulAddMonoidHom k))
    (ind_nsmul_mem h hL hL' hLL' hX (dX k hk) (dY k hk) R hR hR') hP.toFinset Φ h1 ?_ fun t ht => ?_
  · rintro _ ⟨u, hu, rfl⟩
    exact h2 u hu
  · obtain ⟨r, hr, u, hu, e⟩ := hR2' _ (h3 t ht)
    refine ⟨t - k • u, hP.mem_toFinset.2 ?_, k • u, ⟨u, hu, rfl⟩, by abel⟩
    change k • (t - k • u) ∈ R2
    rwa [smul_sub, e, smul_smul, add_sub_cancel_right]

theorem half_infPart {a : AE D} (ha : infPart D a = 0) {u : WO S T} (hu : u ∈ half S T a) :
    u.map (infPart D) = 0 := by
  ext i j
  show infPart D (u i j) = 0
  rw [← (isHalf_iff S T).2 hu i j, RingHom.map_mul, ha, zero_mul]

theorem placeModel_unique {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) {a : AE D} (ha : a * a = a) (hinf : infPart D a = 0) {f₀ : WO S T → ℂ}
    {T₁ T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ T₁)
    (h₂ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ T₂)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ) : T₁ Φ = T₂ Φ := by
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have hmul := exists_nsmul_mem_latO hS.1 hT.1
  have hsm : ∀ {b : AE D}, b * b = b → ∀ u ∈ (latO S T ΛS ΛT fun _ => True),
      b • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T b := fun {b} hb u hu =>
    ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ b
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hb])) u hu,
      (mem_half S T).2 (by rw [smul_smul, hb])⟩
  generalize (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) = Λ at *
  have ha' : cA D a * cA D a = cA D a := by rw [← RingHom.map_mul, ha]
  have hb := isBichar_symplO S T ψ
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk x y hxy => by
    rw [← inv_smul_nsmul S T hk x, ← inv_smul_nsmul S T hk y]
    exact congrArg _ hxy
  have hLL' : ∀ u ∈ Λ ⊓ half S T a, ∀ y ∈ Λ, ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (half_infPart hinf hu.2)).1 hu.1 y hy
  have hmem := mem_waveSpan (X := half S T a) (Y := half S T (cA D a)) (L := Λ ⊓ half S T a)
    (L' := Λ ⊓ half S T (cA D a)) hb inf_le_right inf_le_right (fun u hu y hy => hLL' u hu y hy.1)
    (fun x hx h => ⟨(hdual x (half_infPart hinf hx)).2 fun u hu => by
      have := h _ (hsm ha' u hu)
      rwa [← symplO_smul, (mem_half S T).1 hx] at this, hx⟩)
    (half_div S T a) (half_div S T _) tf (fun k hk => by
      obtain ⟨R, hR, h⟩ := hfin k hk
      refine ⟨(fun r => a • r) '' R, hR.image _, fun t ht => ?_⟩
      obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
      refine ⟨_, ⟨r, hr, rfl⟩, a • u, hsm ha u hu, ?_⟩
      have := (mem_half S T).1 ht.2
      rw [← this, htr, smul_add, smul_comm a k u])
    Φ (fun t ht => (isHalf_iff S T).1 (hΦ.1 t ht)) _ hΦ.2.choose_spec.1
      (fun u hu => hΦ.2.choose_spec.2.1 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨hΦ.2.choose_spec.2.2 t ht, (half S T a).nsmul_mem ((isHalf_iff S T).1 (hΦ.1 t ht)) _⟩
  have hsub : waveSpan (fun x y => ψ (symplO S T x y)) (half S T a) (half S T (cA D a)) (Λ ⊓ half S T a) ≤
      LinearMap.eqLocus T₁ T₂ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have hSB : IsSBHalf a Λ fun t => ψ (symplO S T t y) * halfInd a Λ t := by
      obtain ⟨k, hk, hky⟩ := hmul y (half_infPart (infPart_cA hinf) hy)
      have hne : ∀ t, ψ (symplO S T t y) * halfInd a Λ t ≠ 0 → t ∈ Λ ⊓ half S T a := fun t ht => by
        by_contra hn
        rw [halfInd_eq_ind, ind, if_neg hn, mul_zero] at ht
        exact ht rfl
      refine ⟨fun t ht => (isHalf_iff S T).2 (hne t ht).2, k, hk, fun u hu hu' t => ?_,
        fun t ht => nsmul_mem (hne t ht).1 k⟩
      have hu'' : u ∈ Λ ⊓ half S T a := ⟨hu, (isHalf_iff S T).1 hu'⟩
      have e1 := hb.left t (k • u) y
      have e2 := hb.nsmul k u y
      beta_reduce at e1 e2 ⊢
      rw [e1, e2, hLL' u hu'' _ hky, mul_one, halfInd_eq_ind, ind_add _ _ (nsmul_mem hu'' k)]
    have key : ∀ T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀ T₀ →
        T₀ (wave (fun x y => ψ (symplO S T x y)) (Λ ⊓ half S T a) x y) = heisO ψ S T x (heisO ψ S T y f₀) := by
      intro T₀ h₀
      have e1 := h₀.trans _ hSB x ((isHalf_iff S T).2 hx)
      have e2 := h₀.modul _ (GlobalTheory.isSBHalf_halfInd a Λ) y ((isHalf_iff S T).2 hy)
      have e3 := h₀.vac
      rw [one_smul] at e3
      rw [e2, e3, halfInd_eq_ind] at e1
      exact e1
    exact (key T₁ h₁).trans (key T₂ h₂).symm
  exact hsub hmem

theorem exists_isThetaAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) {a : AE D} (ha : a * a = a) (hinf : infPart D a = 0) {f₀ : WO S T → ℂ}
    (h : ∃ T₁, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ T₁)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ) :
    ∃ f, IsThetaAt ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Φ f := by
  obtain ⟨T₁, h₁⟩ := h
  exact ⟨T₁ Φ, ⟨T₁, h₁⟩, fun T₂ h₂ => placeModel_unique hψ hS hT ha hinf h₁ h₂ hΦ⟩

theorem exists_nat_mem_places (P : Finset (Formalism.L2.DIV.Pl D.host.E)) :
    ∃ n : ℕ, 0 < n ∧ ∀ PP ∈ P, (n : 𝓞 D.host.E) ∈ PP.asIdeal := by
  refine ⟨∏ PP ∈ P, Ideal.absNorm PP.asIdeal, Finset.prod_pos fun PP _ =>
    Nat.pos_of_ne_zero fun h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), fun PP h => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun PP : Formalism.L2.DIV.Pl D.host.E => Ideal.absNorm PP.asIdeal) h
  rw [hc, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

theorem redM_add_nsmul {b c : ℕ} (PP : Formalism.L2.DIV.Pl D.host.E) {n : ℕ} (hn : (n : 𝓞 D.host.E) ∈ PP.asIdeal)
    {N N' : Matrix (Fin b) (Fin c) (EAf D)} (h : IsIntM N) (h' : IsIntM N') : redM PP (N + n • N') = redM PP N := by
  funext i j
  have h2 : (N + n • N') i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := add_mem (h i j) (nsmul_mem (h' i j) n)
  unfold redM
  rw [dif_pos h2, dif_pos (h i j)]
  have e : (⟨_, h2⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, h i j⟩ + n • ⟨_, h' i j⟩ := rfl
  have h0 : (n : Formalism.L2.DIV.kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hn
  rw [e, RingHom.map_add, nsmul_eq_mul, RingHom.map_mul, map_natCast, h0, zero_mul, add_zero]

open Classical in

theorem isSBHalf_of_red (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT) {a : AE D}
    (hinf : infPart D a = 0) {b c : ℕ} (G : WO S T → Matrix (Fin b) (Fin c) (EAf D))
    (hG : ∀ x y, G (x + y) = G x + G y)
    (hup : ∃ k : ℕ, 0 < k ∧ ∀ x : WO S T, IsIntM (x.map (toEAf D)) → IsIntM (k • G x))
    (hdown : ∃ k : ℕ, 0 < k ∧ ∀ x : WO S T, IsIntM (G x) → IsIntM (k • x.map (toEAf D)))
    (P : Finset (Formalism.L2.DIV.Pl D.host.E))
    (ω : (∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin c) (Formalism.L2.DIV.kP PP)) → ℂ)
    (hω : ∀ y y', (∀ PP ∈ P, y PP = y' PP) → ω y = ω y') :
    IsSBHalf a (latO S T ΛS ΛT fun _ => True)
      fun x => if IsHalf a x ∧ IsIntM (G x) then ω (fun PP => redM PP (G x)) else 0 := by
  obtain ⟨k₁, hk₁, h₁⟩ := hup
  obtain ⟨k₂, hk₂, h₂⟩ := hdown
  obtain ⟨k₃, hk₃, h₃⟩ := exists_nsmul_latO_int (S := S) (T := T) hS.fg hT.fg
  obtain ⟨k₄, hk₄, h₄⟩ := exists_nsmul_int_mem_latO hS hT
  obtain ⟨n, hn, hP⟩ := exists_nat_mem_places P
  have hGn : ∀ (k : ℕ) x, G (k • x) = k • G x := fun k x => (AddMonoidHom.mk' G hG).map_nsmul k x
  have hne : ∀ t : WO S T, (if IsHalf a t ∧ IsIntM (G t) then ω (fun PP => redM PP (G t)) else 0) ≠ 0 →
      IsHalf a t ∧ IsIntM (G t) := fun t ht => by
    by_contra h
    exact ht (if_neg h)
  refine ⟨fun t ht => (hne t ht).1, n * (k₄ * k₂) * (k₁ * k₃), by positivity, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · have hi : IsIntM ((k₄ * k₂) • k₁ • G (k₃ • u)) := isIntM_nsmul (h₁ _ (by rw [map_toEAf_nsmul]; exact h₃ u hu)) _
    have e : G (t + (n * (k₄ * k₂) * (k₁ * k₃)) • u) = G t + n • (k₄ * k₂) • k₁ • G (k₃ • u) := by
      rw [hG, hGn, hGn, smul_smul, smul_smul, smul_smul, mul_assoc (n * _)]
    have hh : IsHalf a (t + (n * (k₄ * k₂) * (k₁ * k₃)) • u) ↔ IsHalf a t := by
      rw [isHalf_iff, isHalf_iff]
      exact add_mem_cancel_right (nsmul_mem ((isHalf_iff S T).1 hu') _)
    have hI : IsIntM (G t + n • (k₄ * k₂) • k₁ • G (k₃ • u)) ↔ IsIntM (G t) :=
      forall_congr' fun i => forall_congr' fun j => add_mem_cancel_right (isIntM_nsmul hi n i j)
    beta_reduce
    rw [e]
    by_cases ht : IsHalf a t ∧ IsIntM (G t)
    · rw [if_pos ht, if_pos ⟨hh.2 ht.1, hI.2 ht.2⟩]
      exact hω _ _ fun PP hPP => redM_add_nsmul PP (hP PP hPP) ht.2 hi
    · rw [if_neg ht, if_neg fun h => ht ⟨hh.1 h.1, hI.1 h.2⟩]
  · obtain ⟨h1, h2⟩ := hne t ht
    have := h₄ (k₂ • t) (half_infPart hinf (nsmul_mem ((isHalf_iff S T).1 h1) _))
      (by rw [map_toEAf_nsmul]; exact h₂ t h2)
    rw [show n * (k₄ * k₂) * (k₁ * k₃) = n * (k₁ * k₃) * (k₄ * k₂) by ring, mul_smul, mul_smul k₄]
    exact nsmul_mem this _

theorem omegaQ_congr {a b : ℕ} (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (r : ℕ)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (k : ℤ)
    {y y' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)} (h : ∀ PP ∈ Q, y PP = y' PP) :
    omegaQ Q r ξ k y = omegaQ Q r ξ k y' := by
  have hiff : (∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det) ↔
      ∀ PP ∈ Q, LowZero r (y' PP) ∧ IsUnit (topL r (y' PP)).det :=
    forall_congr' fun PP => forall_congr' fun hPP => by rw [h PP hPP]
  unfold omegaQ
  by_cases h1 : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
  · rw [dif_pos h1, dif_pos (hiff.1 h1)]
    refine Finset.prod_congr rfl fun PP _ => ?_
    congr 3
    exact Units.ext (by rw [IsUnit.unit_spec, IsUnit.unit_spec, h PP.1 PP.2])
  · rw [dif_neg h1, dif_neg fun h2 => h1 (hiff.2 h2)]

theorem omegaK_congr {a b : ℕ} (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    {y y' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)} (h : ∀ PP ∈ Pg, y PP = y' PP) :
    omegaK Pg y = omegaK Pg y' := by
  have hiff : (∀ PP ∈ Pg, LowZero a (y PP) ∧ topL a (y PP) = 1) ↔ ∀ PP ∈ Pg, LowZero a (y' PP) ∧ topL a (y' PP) = 1 :=
    forall_congr' fun PP => forall_congr' fun hPP => by rw [h PP hPP]
  unfold omegaK
  by_cases h1 : ∀ PP ∈ Pg, LowZero a (y PP) ∧ topL a (y PP) = 1
  · rw [if_pos h1, if_pos (hiff.1 h1)]
  · rw [if_neg h1, if_neg fun h2 => h1 (hiff.2 h2)]

end GlobalTheory.PlaceVec

end
