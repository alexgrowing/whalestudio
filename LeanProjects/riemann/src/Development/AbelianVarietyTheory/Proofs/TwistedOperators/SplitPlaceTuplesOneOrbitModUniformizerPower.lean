import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralBasisCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceMatrixEqOfAgreeWithFramedGL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSplitPlaceHermitianFrameGLEmbedding
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMaximalCompactUnnComponentStandardCartanIn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.AscFin.OneOrbitAt

theorem mem_idOff_iff_pr {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) (a : AE D) :
    a ∈ idOff D (· = p.v) ↔ p.pr a = 0 ∧ p.pr (cA D a) = 0 := by
  classical
  obtain ⟨ε, ⟨α, rfl, hαv, hαo⟩, hsum⟩ := p.above
  have hsplit := p.split
  have hsplitc := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isSplitIdem_cA hsplit
  set E' := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) with hE'
  have hE'tm : E' = pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  have hcomp : ∀ w, GlobalTheory.FinPl.compAt D w E' = if w = p.v then 1 else 0 := by
    intro w
    rw [hE'tm, GlobalTheory.FinPlLoc.compAt_pair]
    split_ifs with hw
    · subst hw
      rw [hαv]
      exact Algebra.TensorProduct.one_def.symm
    · rw [hαo w hw, TensorProduct.zero_tmul]
  have hinf : infPart D E' = 0 := by
    rw [← hsum, map_add, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_of_splitIdem hsplit,
      Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_of_splitIdem hsplitc, add_zero]
  have hoff : a ∈ idOff D (· = p.v) ↔ GlobalTheory.FinPl.compAt D p.v a = 0 := by
    simp only [GlobalTheory.FinPl.idOff, Submodule.mem_iInf, RingHom.mem_ker]
    exact ⟨fun h => h ⟨p.v, rfl⟩, fun h w => by obtain ⟨w, rfl⟩ := w; exact h⟩
  have hkey : GlobalTheory.FinPl.compAt D p.v a = 0 ↔ E' * a = 0 := by
    constructor
    · intro h
      refine GlobalTheory.FinPlLoc.eq_zero_of_comp _ (by rw [map_mul, hinf, zero_mul]) fun w => ?_
      rw [map_mul, hcomp]
      split_ifs with hw
      · subst hw
        rw [h, mul_zero]
      · rw [zero_mul]
    · intro h
      have h' := congrArg (GlobalTheory.FinPl.compAt D p.v) h
      rwa [map_mul, hcomp, if_pos rfl, one_mul, map_zero] at h'
  have hpr : ∀ x, p.pr x = 0 ↔ p.e * x = 0 := fun x =>
    ⟨fun h => by rw [← p.sec_pr, h, map_zero],
     fun h => by rw [← p.pr_sec (p.pr x), p.sec_pr, h, map_zero]⟩
  have hprc : p.pr (cA D a) = 0 ↔ cA D p.e * a = 0 := by
    rw [hpr]
    constructor
    · intro h
      have h' := congrArg (cA D) h
      rwa [map_mul, cA_cA, map_zero] at h'
    · intro h
      have h' := congrArg (cA D) h
      rwa [map_mul, cA_cA, map_zero] at h'
  obtain ⟨hee, hec, -⟩ := hsplit
  have h1 : p.e * E' = p.e := by rw [← hsum, mul_add, hee, hec, add_zero]
  have h2 : cA D p.e * E' = cA D p.e := by
    rw [← hsum, mul_add, mul_comm (cA D p.e) p.e, hec, zero_add, ← map_mul, hee]
  rw [hoff, hkey, hpr, hprc]
  constructor
  · intro h
    exact ⟨by rw [← h1, mul_assoc, h, mul_zero], by rw [← h2, mul_assoc, h, mul_zero]⟩
  · rintro ⟨h, h'⟩
    rw [← hsum, add_mul, h, h', add_zero]

theorem fix_last {k : Type} [CommRing k] {ρ : ℕ} (G U Uc : Matrix (Fin (ρ + 1)) (Fin (ρ + 1)) k)
    (hU : ∀ j, U (Fin.last ρ) j = if j = Fin.last ρ then 1 else 0)
    (hUc : ∀ j, Uc (Fin.last ρ) j = if j = Fin.last ρ then 1 else 0)
    (hG : ∀ q p, ¬ (p = Fin.last ρ ∧ q = Fin.last ρ) → G q p = 0) : Ucᵀ * G * U = G := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last ρ)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last ρ)]
    · rw [Matrix.transpose_apply, hU, hUc]
      by_cases hi : i = Fin.last ρ
      · by_cases hj : j = Fin.last ρ
        · subst hi
          subst hj
          simp
        · rw [if_neg hj, mul_zero, hG i j (fun h => hj h.1)]
      · rw [if_neg hi, zero_mul, zero_mul, hG i j (fun h => hi h.2)]
    · intro a _ ha
      rw [hG a (Fin.last ρ) (fun h => ha h.2), mul_zero]
    · simp
  · intro b _ hb
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro a _
    rw [hG a b (fun h => hb h.1), mul_zero]
  · simp

theorem core_coord {O k : Type} [CommRing O] [Field k] [Algebra O k] (hinj : Function.Injective (algebraMap O k))
    (I : Ideal O) (hI : I ≤ Ideal.jacobson ⊥) {N ρ : ℕ}
    (P PA : Matrix (Fin N) (Fin (ρ + 1)) k) (Q QA : Matrix (Fin (ρ + 1)) (Fin N) k)
    (U Uc : Matrix (Fin (ρ + 1)) (Fin (ρ + 1)) k)
    (hU : ∀ j, U (Fin.last ρ) j = if j = Fin.last ρ then 1 else 0)
    (hUc : ∀ j, Uc (Fin.last ρ) j = if j = Fin.last ρ then 1 else 0)
    (hG : (Q + QA) * (P + PA) = Ucᵀ * (Q * P) * U)
    (ι ι' : Fin (ρ + 1) → Fin N) (s t : Fin (ρ + 1) → k) (hι : Function.Injective ι) (hι' : Function.Injective ι')
    (hx : ∀ a b, ι' b = ι a → a = Fin.last ρ ∧ b = Fin.last ρ)
    (h1 : ∀ q i, s q * P i q = if i = ι q then 1 else 0)
    (h2 : ∀ q i, t q * Q q i = if i = ι' q then 1 else 0)
    (ha1 : ∀ q i, ∃ z ∈ I, algebraMap O k z = s q * PA i q)
    (ha2 : ∀ q i, ∃ z ∈ I, algebraMap O k z = t q * QA q i) :
    ∃ k₀ : GL (Fin N) O, (∀ i j, (k₀.1 - 1) i j ∈ I) ∧ k₀.1.map (algebraMap O k) * P = P + PA ∧
      (Q + QA) * k₀.1.map (algebraMap O k) = Q := by
  choose z1 hz1I hz1 using ha1
  choose z2 hz2I hz2 using ha2
  have hs : ∀ q, s q ≠ 0 := fun q h => by
    have h' := h1 q (ι q)
    rw [h, zero_mul, if_pos rfl] at h'
    exact zero_ne_one h'
  have ht : ∀ q, t q ≠ 0 := fun q h => by
    have h' := h2 q (ι' q)
    rw [h, zero_mul, if_pos rfl] at h'
    exact zero_ne_one h'
  have hP : ∀ i q, P i q = (s q)⁻¹ * (if i = ι q then 1 else 0) := by
    intro i q
    rw [← h1, ← mul_assoc, inv_mul_cancel₀ (hs q), one_mul]
  have hQ : ∀ q i, Q q i = (t q)⁻¹ * (if i = ι' q then 1 else 0) := by
    intro q i
    rw [← h2, ← mul_assoc, inv_mul_cancel₀ (ht q), one_mul]
  have hQP : ∀ q p, ¬ (p = Fin.last ρ ∧ q = Fin.last ρ) → (Q * P) q p = 0 := by
    intro q p hqp
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hQ, hP]
    by_cases hi : i = ι' q
    · by_cases hi' : i = ι p
      · exact absurd (hx p q (hi.symm.trans hi')) hqp
      · rw [if_neg hi', mul_zero, mul_zero]
    · rw [if_neg hi, mul_zero, zero_mul]
  have hpair : (Q + QA) * (P + PA) = Q * P := hG.trans (fix_last (Q * P) U Uc hU hUc hQP)
  obtain ⟨ξ, hξd⟩ : ∃ ξ : Fin (ρ + 1) → Fin N → O, ∀ p i, ξ p i = (if i = ι p then 1 else 0) + z1 p i :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨η, hηd⟩ : ∃ η : Fin (ρ + 1) → Fin N → O, ∀ q i, η q i = (if i = ι' q then 1 else 0) + z2 q i :=
    ⟨_, fun _ _ => rfl⟩
  have hξ : ∀ p i, algebraMap O k (ξ p i) = s p * (P + PA) i p := by
    intro p i
    rw [hξd, map_add, hz1, Matrix.add_apply, mul_add, h1]
    split_ifs <;> simp
  have hη : ∀ q i, algebraMap O k (η q i) = t q * (Q + QA) q i := by
    intro q i
    rw [hηd, map_add, hz2, Matrix.add_apply, mul_add, h2]
    split_ifs <;> simp
  have hξI : ∀ p i, ξ p i - (if i = ι p then 1 else 0) ∈ I := by
    intro p i
    rw [hξd, add_sub_cancel_left]
    exact hz1I p i
  have hηI : ∀ q i, η q i - (if i = ι' q then 1 else 0) ∈ I := by
    intro q i
    rw [hηd, add_sub_cancel_left]
    exact hz2I q i
  have hsum1 : ∀ q p, t q * s p * ((Q + QA) * (P + PA)) q p =
      ∑ i, algebraMap O k (η q i) * algebraMap O k (ξ p i) := by
    intro q p
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hη, hξ]
    ring
  have hsum2 : ∀ q p, t q * s p * (Q * P) q p = if ι' q = ι p then 1 else 0 := by
    intro q p
    rw [Matrix.mul_apply, Finset.mul_sum, Finset.sum_eq_single (ι' q)]
    · rw [show t q * s p * (Q q (ι' q) * P (ι' q) p) = (t q * Q q (ι' q)) * (s p * P (ι' q) p) by ring,
        h2, h1, if_pos rfl, one_mul]
    · intro i _ hi
      rw [show t q * s p * (Q q i * P i p) = (t q * Q q i) * (s p * P i p) by ring, h2, if_neg hi, zero_mul]
    · simp
  have hdot : ∀ p q, η q ⬝ᵥ ξ p = if ι' q = ι p then 1 else 0 := by
    intro p q
    apply hinj
    have e1 : algebraMap O k (η q ⬝ᵥ ξ p) = ∑ i, algebraMap O k (η q i) * algebraMap O k (ξ p i) := by
      simp [dotProduct, map_sum]
    rw [e1, ← hsum1, hpair, hsum2]
    split_ifs <;> simp
  obtain ⟨K, hKI, hKcol, hKrow⟩ :=
    GlobalTheory.AscFin.exists_gl_congr_cols_rows O I hI (Fin N) (Fin (ρ + 1)) (Fin (ρ + 1)) ι ι' hι hι' ξ η hξI hηI hdot
  refine ⟨K, hKI, ?_, ?_⟩
  · ext i p
    rw [Matrix.mul_apply, Finset.sum_eq_single (ι p)]
    · rw [Matrix.map_apply, hKcol, hξ, hP, if_pos rfl, mul_one, mul_comm, ← mul_assoc,
        inv_mul_cancel₀ (hs p), one_mul]
    · intro j _ hj
      rw [hP, if_neg hj, mul_zero, mul_zero]
    · simp
  · ext q j
    have hr := congrFun (hKrow q) j
    simp only [Matrix.vecMul, dotProduct] at hr
    have hQA' : ∀ i, (Q + QA) q i = (t q)⁻¹ * algebraMap O k (η q i) := by
      intro i
      rw [hη, ← mul_assoc, inv_mul_cancel₀ (ht q), one_mul]
    rw [Matrix.mul_apply, hQ]
    calc ∑ i, (Q + QA) q i * (K.1.map (algebraMap O k)) i j
        = (t q)⁻¹ * algebraMap O k (∑ i, η q i * K.1 i j) := by
          rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hQA', Matrix.map_apply, map_mul, mul_assoc]
      _ = (t q)⁻¹ * (if j = ι' q then 1 else 0) := by
          rw [hr]
          split_ifs <;> simp

theorem core_basis {O k : Type} [CommRing O] [Field k] [Algebra O k] (hinj : Function.Injective (algebraMap O k))
    (I : Ideal O) (hI : I ≤ Ideal.jacobson ⊥) {N ρ : ℕ} (J b b' : Matrix (Fin N) (Fin N) k)
    (hbb' : b * b' = 1) (hb'b : b' * b = 1) (hJ : IsUnit J.det)
    (X Xc A Ac : Matrix (Fin N) (Fin (ρ + 1)) k)
    (U Uc : Matrix (Fin (ρ + 1)) (Fin (ρ + 1)) k)
    (hU : ∀ j, U (Fin.last ρ) j = if j = Fin.last ρ then 1 else 0)
    (hUc : ∀ j, Uc (Fin.last ρ) j = if j = Fin.last ρ then 1 else 0)
    (hG : (Xc + Ac)ᵀ * J * (X + A) = Ucᵀ * (Xcᵀ * J * X) * U)
    (ι ι' : Fin (ρ + 1) → Fin N) (s t : Fin (ρ + 1) → k) (hι : Function.Injective ι) (hι' : Function.Injective ι')
    (hx : ∀ a b, ι' b = ι a → a = Fin.last ρ ∧ b = Fin.last ρ)
    (h1 : ∀ q, s q • (b' *ᵥ fun i => X i q) = Pi.single (ι q) 1)
    (h2 : ∀ q, t q • ((fun i => Xc i q) ᵥ* (J * b)) = Pi.single (ι' q) 1)
    (ha1 : ∀ q i, ∃ z ∈ I, algebraMap O k z = s q * (b' *ᵥ fun j => A j q) i)
    (ha2 : ∀ q i, ∃ z ∈ I, algebraMap O k z = t q * ((fun j => Ac j q) ᵥ* (J * b)) i) :
    ∃ k₀ : GL (Fin N) O, (∀ i j, (k₀.1 - 1) i j ∈ I) ∧ b * k₀.1.map (algebraMap O k) * b' * X = X + A ∧
      ∀ Kc : Matrix (Fin N) (Fin N) k, Kcᵀ * J * (b * k₀.1.map (algebraMap O k) * b') = J → Kc * Xc = Xc + Ac := by
  have e3 : ∀ Y Z : Matrix (Fin N) (Fin (ρ + 1)) k, Yᵀ * J * b * (b' * Z) = Yᵀ * J * Z := by
    intro Y Z
    rw [Matrix.mul_assoc (Yᵀ * J) b, ← Matrix.mul_assoc b b' Z, hbb', Matrix.one_mul]
  have hG' : (Xcᵀ * J * b + Acᵀ * J * b) * (b' * X + b' * A) =
      Ucᵀ * (Xcᵀ * J * b * (b' * X)) * U := by
    rw [← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.transpose_add, ← Matrix.mul_add, e3, e3, hG]
  have h1' : ∀ q i, s q * (b' * X) i q = if i = ι q then 1 else 0 := by
    intro q i
    have h := congrFun (h1 q) i
    rw [Pi.smul_apply, smul_eq_mul, Pi.single_apply] at h
    exact h
  have h2' : ∀ q i, t q * (Xcᵀ * J * b) q i = if i = ι' q then 1 else 0 := by
    intro q i
    have h := congrFun (h2 q) i
    rw [Pi.smul_apply, smul_eq_mul, Pi.single_apply] at h
    rw [Matrix.mul_assoc]
    exact h
  have ha1' : ∀ q i, ∃ z ∈ I, algebraMap O k z = s q * (b' * A) i q := fun q i => ha1 q i
  have ha2' : ∀ q i, ∃ z ∈ I, algebraMap O k z = t q * (Acᵀ * J * b) q i := by
    intro q i
    rw [Matrix.mul_assoc]
    exact ha2 q i
  obtain ⟨K, hKI, hKP, hKQ⟩ := core_coord hinj I hI (b' * X) (b' * A) (Xcᵀ * J * b) (Acᵀ * J * b) U Uc hU hUc hG'
    ι ι' s t hι hι' hx h1' h2' ha1' ha2'
  refine ⟨K, hKI, ?_, ?_⟩
  · calc b * K.1.map (algebraMap O k) * b' * X = b * (K.1.map (algebraMap O k) * (b' * X)) := by
          simp only [Matrix.mul_assoc]
      _ = X + A := by rw [hKP, ← Matrix.mul_add, ← Matrix.mul_assoc, hbb', Matrix.one_mul]
  · intro Kc hKc
    have hKK : K.1.map (algebraMap O k) * (K⁻¹).1.map (algebraMap O k) = 1 := by
      rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have hMM : (b * K.1.map (algebraMap O k) * b') * (b * (K⁻¹).1.map (algebraMap O k) * b') = 1 := by
      calc (b * K.1.map (algebraMap O k) * b') * (b * (K⁻¹).1.map (algebraMap O k) * b')
          = b * (K.1.map (algebraMap O k) * (b' * b) * (K⁻¹).1.map (algebraMap O k)) * b' := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hb'b, Matrix.mul_one, hKK, Matrix.mul_one, hbb']
    have hN : J * (b * K.1.map (algebraMap O k) * b') * ((b * (K⁻¹).1.map (algebraMap O k) * b') * J⁻¹) = 1 := by
      calc J * (b * K.1.map (algebraMap O k) * b') * ((b * (K⁻¹).1.map (algebraMap O k) * b') * J⁻¹)
          = J * ((b * K.1.map (algebraMap O k) * b') * (b * (K⁻¹).1.map (algebraMap O k) * b')) * J⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hMM, Matrix.mul_one, Matrix.mul_nonsing_inv J hJ]
    have hA : (Xc + Ac)ᵀ * (J * (b * K.1.map (algebraMap O k) * b')) = Xcᵀ * J := by
      calc (Xc + Ac)ᵀ * (J * (b * K.1.map (algebraMap O k) * b'))
          = ((Xcᵀ * J * b + Acᵀ * J * b) * K.1.map (algebraMap O k)) * b' := by
            rw [Matrix.transpose_add]
            simp only [Matrix.add_mul, Matrix.mul_assoc]
        _ = Xcᵀ * J * b * b' := by rw [hKQ]
        _ = Xcᵀ * J := by rw [Matrix.mul_assoc, hbb', Matrix.mul_one]
    have hB : (Kc * Xc)ᵀ * (J * (b * K.1.map (algebraMap O k) * b')) = Xcᵀ * J := by
      rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Kcᵀ J, hKc]
    have hT : (Xc + Ac)ᵀ = (Kc * Xc)ᵀ := by
      calc (Xc + Ac)ᵀ = (Xc + Ac)ᵀ * (J * (b * K.1.map (algebraMap O k) * b')) *
            ((b * (K⁻¹).1.map (algebraMap O k) * b') * J⁻¹) := by
            rw [Matrix.mul_assoc, hN, Matrix.mul_one]
        _ = (Kc * Xc)ᵀ * (J * (b * K.1.map (algebraMap O k) * b')) *
            ((b * (K⁻¹).1.map (algebraMap O k) * b') * J⁻¹) := by rw [hA, hB]
        _ = (Kc * Xc)ᵀ := by rw [Matrix.mul_assoc, hN, Matrix.mul_one]
    exact (Matrix.transpose_injective hT).symm

theorem gram_tuple {D : D7} (W : HSp D) {n : ℕ} (h : GA D W) (z : Matrix (Fin W.rank) (Fin n) (AE D)) :
    ((mt W h ⬝ z).map (cA D))ᵀ ⬝ W.gram.map (incA D) ⬝ (mt W h ⬝ z) = (z.map (cA D))ᵀ ⬝ W.gram.map (incA D) ⬝ z := by
  have hu : ((mt W h).map (cA D))ᵀ * W.gram.map (incA D) * mt W h = W.gram.map (incA D) :=
    GlobalTheory.FrameCont.unitary_mt h
  calc ((mt W h ⬝ z).map (cA D))ᵀ ⬝ W.gram.map (incA D) ⬝ (mt W h ⬝ z)
      = (z.map (cA D))ᵀ * (((mt W h).map (cA D))ᵀ * W.gram.map (incA D) * mt W h) * z := by
        rw [Matrix.map_mul, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = (z.map (cA D))ᵀ ⬝ W.gram.map (incA D) ⬝ z := by rw [hu]

theorem gram_tuple_pr {D : D7} {k : Type} [Field k] (π : AE D →+* k) (W : HSp D) {n : ℕ}
    (z : Matrix (Fin W.rank) (Fin n) (AE D)) :
    ((z.map (cA D))ᵀ ⬝ W.gram.map (incA D) ⬝ z).map π =
      (z.map (π.comp (cA D)))ᵀ ⬝ W.gram.map (fun c => π (incA D c)) ⬝ z.map π := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_map]
  rfl

theorem uni_last {D : D7} {ρ : ℕ} (u : UX D (ρ + 1)) (j : Fin (ρ + 1)) :
    u.1.1 (Fin.last ρ) j = if j = Fin.last ρ then 1 else 0 := by
  have hu : ∀ i j : Fin (ρ + 1), (j < i → u.1.1 i j = 0) ∧ u.1.1 i i = 1 := u.2
  split_ifs with hj
  · subst hj
    exact (hu (Fin.last ρ) (Fin.last ρ)).2
  · exact (hu (Fin.last ρ) j).1 (lt_of_le_of_ne (Fin.le_last j) hj)

set_option maxHeartbeats 1000000 in
theorem one_orbit : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k) (W : HSp D) (ρ : ℕ) (β : GlobalTheory.FinPl.Frame p W (Fin W.rank)) (x : Mx D W.rank (ρ + 1))
  (ι ι' : Fin (ρ + 1) → Fin W.rank) (s t : Fin (ρ + 1) → k) (e : ℕ), 0 < e → Function.Injective ι → Function.Injective ι' →
  (∀ a b, ι' b = ι a → a = Fin.last ρ ∧ b = Fin.last ρ) →
  (∀ q, s q • (β.b' *ᵥ fun i => p.pr (x i q)) = Pi.single (ι q) 1) →
  (∀ q, t q • ((fun i => p.pr (cA D (x i q))) ᵥ* (W.gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (ι' q) 1) →
  ∀ g ∈ grpAt W (· = p.v), ∀ (u : UX D (ρ + 1)) (a : Mx D W.rank (ρ + 1)),
  (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ e, (z : k) = s q * (β.b' *ᵥ fun j => p.pr (a j q)) i) →
  (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ e,
    (z : k) = t q * ((fun j => p.pr (cA D (a j q))) ᵥ* (W.gram.map (fun c => p.pr (incA D c)) * β.b)) i) →
  MxOff (· = p.v) (mt W g⁻¹ ⬝ (x ⬝ u.1.1) - x - a) →
  ∃ k₀ : GL (Fin W.rank) 𝒪[k], (∀ i j, (k₀.1 - 1) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ e) ∧
    MxOff (· = p.v) (mt W (β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)) ⬝ x - mt W g⁻¹ ⬝ (x ⬝ u.1.1)) := by
  intro D k _ _ _ _ p W ρ β x ι ι' s t e he hι hι' hx h1 h2 g hg u a ha1 ha2 hoff
  have hE : (mt W g⁻¹ ⬝ (x ⬝ u.1.1)).map p.pr = x.map p.pr + a.map p.pr := by
    ext i j
    have h := ((mem_idOff_iff_pr p _).1 (hoff i j)).1
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, map_sub] at h
    rw [Matrix.map_apply, Matrix.add_apply, Matrix.map_apply, Matrix.map_apply]
    linear_combination h
  have hEc : (mt W g⁻¹ ⬝ (x ⬝ u.1.1)).map (p.pr.comp (cA D)) =
      x.map (p.pr.comp (cA D)) + a.map (p.pr.comp (cA D)) := by
    ext i j
    have h := ((mem_idOff_iff_pr p _).1 (hoff i j)).2
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, map_sub, map_sub, map_sub] at h
    simp only [Matrix.map_apply, Matrix.add_apply, RingHom.coe_comp, Function.comp_apply]
    linear_combination h
  have hGr : (x.map (p.pr.comp (cA D)) + a.map (p.pr.comp (cA D)))ᵀ * W.gram.map (fun c => p.pr (incA D c)) *
      (x.map p.pr + a.map p.pr) = (u.1.1.map (p.pr.comp (cA D)))ᵀ *
      ((x.map (p.pr.comp (cA D)))ᵀ * W.gram.map (fun c => p.pr (incA D c)) * x.map p.pr) * u.1.1.map p.pr := by
    have h0 := congrArg (fun N => Matrix.map N p.pr) (gram_tuple W g⁻¹ (x ⬝ u.1.1))
    rw [gram_tuple_pr, gram_tuple_pr, hE, hEc, Matrix.map_mul, Matrix.map_mul] at h0
    rw [h0, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  have hinj : Function.Injective (algebraMap 𝒪[k] k) := fun _ _ h => Subtype.ext h
  have hI : IsLocalRing.maximalIdeal 𝒪[k] ^ e ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp he)
  have hJ : IsUnit (W.gram.map (fun c => p.pr (incA D c))).det := by
    have h := (GlobalTheory.FrameCont.gram_det_isUnit W).map (p.pr.comp (incA D))
    rw [RingHom.map_det] at h
    exact h
  have hU : ∀ j, u.1.1.map p.pr (Fin.last ρ) j = if j = Fin.last ρ then 1 else 0 := by
    intro j
    rw [Matrix.map_apply, uni_last, apply_ite p.pr, map_one, map_zero]
  have hUc : ∀ j, u.1.1.map (p.pr.comp (cA D)) (Fin.last ρ) j = if j = Fin.last ρ then 1 else 0 := by
    intro j
    rw [Matrix.map_apply, uni_last, apply_ite (p.pr.comp (cA D)), map_one, map_zero]
  obtain ⟨K, hKI, hKX, hKc⟩ := core_basis hinj _ hI (W.gram.map (fun c => p.pr (incA D c))) β.b β.b' β.bb' β.b'b hJ
    (x.map p.pr) (x.map (p.pr.comp (cA D))) (a.map p.pr) (a.map (p.pr.comp (cA D)))
    (u.1.1.map p.pr) (u.1.1.map (p.pr.comp (cA D))) hU hUc hGr ι ι' s t hι hι' hx h1 h2 ha1 ha2
  have hγ : (mt W (β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) K))).map p.pr =
      β.b * K.1.map (algebraMap 𝒪[k] k) * β.b' := GlobalTheory.FrameAt.gl_map β _
  have hu0 : ((mt W (β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) K))).map (cA D))ᵀ *
      W.gram.map (incA D) * mt W (β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) K)) =
      W.gram.map (incA D) := GlobalTheory.FrameCont.unitary_mt _
  have hu := congrArg (fun N => Matrix.map N p.pr) hu0
  simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at hu
  rw [hγ] at hu
  have hpr1 : (mt W (β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) K)) ⬝ x).map p.pr =
      x.map p.pr + a.map p.pr := by
    rw [Matrix.map_mul, hγ, hKX]
  have hpr2 : (mt W (β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) K)) ⬝ x).map (p.pr.comp (cA D)) =
      x.map (p.pr.comp (cA D)) + a.map (p.pr.comp (cA D)) := by
    rw [Matrix.map_mul]
    exact hKc _ hu
  refine ⟨K, hKI, fun i j => (mem_idOff_iff_pr p _).2 ⟨?_, ?_⟩⟩
  · have e1 := congrFun (congrFun hpr1 i) j
    have e2 := congrFun (congrFun hE i) j
    rw [Matrix.sub_apply, map_sub]
    simp only [Matrix.map_apply] at e1 e2
    rw [e1, e2, sub_self]
  · have e1 := congrFun (congrFun hpr2 i) j
    have e2 := congrFun (congrFun hEc i) j
    rw [Matrix.sub_apply, map_sub, map_sub]
    simp only [Matrix.map_apply, RingHom.coe_comp, Function.comp_apply] at e1 e2
    rw [e1, e2, sub_self]

end GlobalTheory.AscFin.OneOrbitAt
