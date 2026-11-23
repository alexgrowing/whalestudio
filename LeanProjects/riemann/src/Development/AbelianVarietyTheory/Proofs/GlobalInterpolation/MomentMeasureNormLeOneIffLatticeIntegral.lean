import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDualBasisOfUnimodularLatticeAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetsAreBoundedMeasureMomentsPadicIntMatrixChange
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsOfSpanImagQuadraticStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasureEqOfMoments
open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate

noncomputable section
namespace GlobalTheory.MomN.Bridge

variable {g : ℕ}

theorem im_hf_int (S : Setup g) (hOk : S.Ok) (x y : Fin g → ℂ) (hx : x ∈ S.La) (hy : y ∈ S.La) :
    ∃ z : ℤ, (hf S.Hm x y).im = z := by
  obtain ⟨hdp, -, -, -, -, -, hbeta, -⟩ := hOk
  obtain ⟨u, v, huv⟩ := hbeta x hx y hy
  have h := congrArg Complex.im huv
  simp [beta, w0, rtd, Complex.mul_im] at h
  have hd : (0 : ℝ) < Real.sqrt S.d := Real.sqrt_pos.2 (by exact_mod_cast hdp.pos)
  refine ⟨v, ?_⟩
  field_simp at h
  nlinarith [h]

theorem hf_smul_left (Hm : Matrix (Fin g) (Fin g) ℂ) (s : ℕ) (x t : Fin g → ℂ) :
    hf Hm ((s : ℂ) • x) t = hf Hm x ((s : ℂ) • t) := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hf_zero_right (Hm : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → ℂ) : hf Hm x 0 = 0 := by
  simp [hf]

theorem opW_zero (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (G : (Fin g → ℂ) → ℂ) : opW d Hm 0 G = G := by
  funext z
  simp [opW, opU, beta, hf]

variable {q : ℕ} [Fact q.Prime]

theorem lamA_eq (ι : ℂ ≃+* ℂ_[q]) (lam : Qbar →+* ℂ_[q]) (hι : ∀ z : Qbar, ι (z : ℂ) = lam z) (x : ℂ) (hx : x ∈ Qbar) :
    lamA lam x = ι x := by
  unfold lamA
  rw [dif_pos hx, ← hι ⟨x, hx⟩]

theorem natCast_mem_Qbar (s : ℕ) : (s : ℂ) ∈ Qbar := (algebraicClosure ℚ ℂ).natCast_mem s

theorem lamA_nat (ι : ℂ ≃+* ℂ_[q]) (lam : Qbar →+* ℂ_[q]) (hι : ∀ z : Qbar, ι (z : ℂ) = lam z) (s : ℕ) :
    lamA lam (s : ℂ) = (s : ℂ_[q]) := by
  rw [lamA_eq ι lam hι _ (natCast_mem_Qbar s), map_natCast]

end GlobalTheory.MomN.Bridge

namespace GlobalTheory.MomN.Bridge
variable {g : ℕ} {q : ℕ} [Fact q.Prime]

theorem jet_trivialTorsion_eq_latticeMomentIntegral (ι : ℂ ≃+* ℂ_[q]) (lam : Qbar →+* ℂ_[q]) (hι : ∀ z : Qbar, ι (z : ℂ) = lam z)
    (δ₀ : ℂ) (Ω : ℂ_[q]) (S : Setup g) (hOk : S.Ok) {r : ℕ} (b : Fin r → Fin g → ℂ) (hbLa : ∀ i, b i ∈ S.La)
    (t : Fin g → ℂ) (ht : S.PrimeTo q t) (G : (Fin g → ℂ) → ℂ) (μ : C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q])
    (hM : MomentProperty lam Ω δ₀ S b (fun _ : Fin 1 => t) μ G)
    (k : ℕ) (ys : Fin k → Fin g → ℂ) (hys : ∀ j, ys j ∈ S.La) (f : C(Fin r → ℤ_[q], ℂ_[q]))
    (hf' : ∀ a, f a = ∏ j, pairD lam Ω S.d S.Hm b (ys j) a) :
    ι (iteratedFDeriv ℂ k G 0 fun j => δ₀⁻¹ • ys j) = μ f := by
  obtain ⟨s, hs0, -, hst⟩ := ht
  have hid : IsIdem lam S.d 0 (s : ℂ) := by
    refine ⟨⟨s, 0, by simp⟩, ?_, ?_⟩
    · rw [lamA_nat ι lam hι]
      simp only [CharP.cast_eq_zero, neg_zero, zpow_zero]
      rw [← Nat.cast_pred hs0]
      exact IsUltrametricDist.norm_natCast_le_one ℂ_[q] _
    · rw [map_natCast, lamA_nat ι lam hι]
      simpa using IsUltrametricDist.norm_natCast_le_one ℂ_[q] s
  have hint : ∀ (l : Fin 1) (i : Fin r), ∃ z : ℤ, (hf S.Hm ((s : ℂ) • b i) t).im = z := by
    intro _ i
    rw [hf_smul_left]
    exact im_hf_int S hOk _ _ (hbLa i) hst
  let y0 : Fin r → Fin (q ^ 0) := fun _ => ⟨0, by simp⟩
  have hlift : liftY q 0 (s : ℂ) b y0 = 0 := by simp [liftY, y0]
  have hdir : ∀ j, S.AlgDir (ys j) := by
    intro j
    refine ⟨1, fun _ => 1, fun _ => ys j, fun _ => (algebraicClosure ℚ ℂ).one_mem, fun _ => hys j, by simp⟩
  have hf2 : ∀ a, f a = lamA lam (kap S.Hm (vecA 0 b a) (liftY q 0 (s : ℂ) b y0)) *
      ∏ j, pairD lam Ω S.d S.Hm b (ys j) a := by
    intro a
    rw [hlift, hf' a]
    have : kap S.Hm (vecA (q := q) 0 b a) 0 = ((1 : ℕ) : ℂ) := by simp [kap, hf_zero_right]
    rw [this, lamA_nat ι lam hι]; simp
  obtain ⟨hQ, heq⟩ := hM 0 0 (s : ℂ) hid le_rfl hint y0 k ys hdir f hf2
  rw [hlift, opW_zero] at hQ heq
  rw [← heq, lamA_eq ι lam hι _ hQ]
  rfl

end GlobalTheory.MomN.Bridge

namespace GlobalTheory.MomN.Bridge
variable {g : ℕ} {q : ℕ} [Fact q.Prime]

theorem pairD_dual (ι : ℂ ≃+* ℂ_[q]) (lam : Qbar →+* ℂ_[q]) (hι : ∀ z : Qbar, ι (z : ℂ) = lam z) (Ω : ℂ_[q])
    (S : Setup g) {r : ℕ} (b : Fin r → Fin g → ℂ) (s' : ℕ) (c : Fin r → Fin g → ℂ)
    (hcb : ∀ i j, beta S.d S.Hm (c j) (b i) = if i = j then (s' : ℂ) else 0) (j : Fin r) (a : Fin r → ℤ_[q]) :
    pairD lam Ω S.d S.Hm b (c j) a = Ω⁻¹ * ((s' : ℂ_[q]) * zc (a j)) := by
  unfold pairD
  congr 1
  have : ∀ i, zc (a i) * lamA lam (beta S.d S.Hm (c j) (b i)) = if i = j then (s' : ℂ_[q]) * zc (a j) else 0 := by
    intro i
    rw [hcb]
    split_ifs with h
    · subst h; rw [lamA_nat ι lam hι]; ring
    · rw [show (0 : ℂ) = ((0 : ℕ) : ℂ) by simp, lamA_nat ι lam hι]; simp
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_ite_eq']
  simp

theorem isMom_dual (ι : ℂ ≃+* ℂ_[q]) (lam : Qbar →+* ℂ_[q]) (hι : ∀ z : Qbar, ι (z : ℂ) = lam z)
    (δ₀ : ℂ) (hδ : δ₀ ≠ 0) (Ω : ℂ_[q]) (hΩ : Ω ≠ 0) (S : Setup g) (hOk : S.Ok) {r : ℕ} (b : Fin r → Fin g → ℂ)
    (hbLa : ∀ i, b i ∈ S.La) (t : Fin g → ℂ) (ht : S.PrimeTo q t) (G : (Fin g → ℂ) → ℂ)
    (μ : C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]) (hM : MomentProperty lam Ω δ₀ S b (fun _ : Fin 1 => t) μ G)
    (s' : ℕ) (hs' : s' ≠ 0) (c : Fin r → Fin g → ℂ) (hcLa : ∀ j, c j ∈ S.La)
    (hcb : ∀ i j, beta S.d S.Hm (c j) (b i) = if i = j then (s' : ℂ) else 0) :
    IsMom ι (fun j => (ι.symm (Ω / ι δ₀) / (s' : ℂ)) • c j) G μ := by
  intro k j f hf
  have hs'q : (s' : ℂ_[q]) ≠ 0 := Nat.cast_ne_zero.2 hs'
  have hιδ : ι δ₀ ≠ 0 := by simpa using hδ
  let f' : C(Fin r → ℤ_[q], ℂ_[q]) := ((Ω⁻¹ * s') ^ k) • f
  have hf' : ∀ a, f' a = ∏ l, pairD lam Ω S.d S.Hm b (c (j l)) a := by
    intro a
    simp only [f', ContinuousMap.smul_apply, smul_eq_mul, hf a, pairD_dual ι lam hι Ω S b s' c hcb,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
    rw [mul_assoc]; rfl
  have hA := jet_trivialTorsion_eq_latticeMomentIntegral ι lam hι δ₀ Ω S hOk b hbLa t ht G μ hM k (fun l => c (j l)) (fun l => hcLa _) f' hf'
  have e1 : (iteratedFDeriv ℂ k G 0 fun l => δ₀⁻¹ • c (j l)) = δ₀⁻¹ ^ k • iteratedFDeriv ℂ k G 0 fun l => c (j l) := by
    rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have e2 : (iteratedFDeriv ℂ k G 0 fun l => (ι.symm (Ω / ι δ₀) / (s' : ℂ)) • c (j l)) =
      (ι.symm (Ω / ι δ₀) / (s' : ℂ)) ^ k • iteratedFDeriv ℂ k G 0 fun l => c (j l) := by
    rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [e1, smul_eq_mul, map_mul, map_pow, map_inv₀] at hA
  simp only [f', ContinuousLinearMap.map_smul, smul_eq_mul] at hA
  rw [e2, smul_eq_mul, map_mul, map_pow, map_div₀, RingEquiv.apply_symm_apply, map_natCast]
  set J := ι (iteratedFDeriv ℂ k G 0 fun l => c (j l))
  have hJ : J = (ι δ₀) ^ k * ((Ω⁻¹ * s') ^ k * μ f) := by
    rw [← hA, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hιδ, one_pow, one_mul]
  rw [hJ, ← mul_assoc, ← mul_assoc, ← mul_pow, ← mul_pow]
  have h1 : Ω / ι δ₀ / (s' : ℂ_[q]) * ι δ₀ * (Ω⁻¹ * s') = 1 := by field_simp
  rw [h1, one_pow, one_mul]

end GlobalTheory.MomN.Bridge

namespace GlobalTheory.MomN.Bridge
variable {q : ℕ} [Fact q.Prime]

theorem exists_zc_inv (s : ℕ) (hs : Nat.Coprime s q) : ∃ u : ℤ_[q], zc u = ((s : ℂ_[q]))⁻¹ := by
  have hn : ‖(s : ℤ_[q])‖ = 1 := by
    rw [PadicInt.norm_def, PadicInt.coe_natCast, Padic.norm_natCast_eq_one_iff]; exact hs.symm
  refine ⟨(s : ℤ_[q]).inv, ?_⟩
  have hm : (s : ℤ_[q]) * (s : ℤ_[q]).inv = 1 := PadicInt.mul_inv hn
  have h2 : zc (s : ℤ_[q]) * zc (s : ℤ_[q]).inv = 1 := by
    simp only [zc]
    rw [← map_mul, ← PadicInt.coe_mul, hm, PadicInt.coe_one, map_one]
  rw [show zc (s : ℤ_[q]) = (s : ℂ_[q]) by simp [zc]] at h2
  exact eq_inv_of_mul_eq_one_right h2

end GlobalTheory.MomN.Bridge

namespace GlobalTheory.MomN

open Bridge in

theorem norm_le_one_iff_latInt : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (lam : Qbar →+* ℂ_[q]) (δ₀ : ℂ) (Ω : ℂ_[q])
    (g : ℕ) (S : Setup g) (r : ℕ) (b : Fin r → Fin g → ℂ) (t : Fin g → ℂ) (G : (Fin g → ℂ) → ℂ)
    (μ : C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]), (∀ z : Qbar, ι (z : ℂ) = lam z) → δ₀ ≠ 0 → ‖Ω‖ = 1 → S.Ok →
    GlobalTheory.MomOne.Split S.d q → S.NNBasis q b → S.PrimeTo q t → ContDiff ℂ ⊤ G →
    MomentProperty lam Ω δ₀ S b (fun _ : Fin 1 => t) μ G → (‖μ‖ ≤ 1 ↔ LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup G) := by
  intro q _ ι lam δ₀ Ω g S r b t G μ hι hδ hΩ hOk hsplit hb ht _ hM
  have hΩ0 : Ω ≠ 0 := by rintro rfl; simp at hΩ
  obtain ⟨s', c, hs'q, hcLa, hcb, hsp⟩ := GlobalTheory.T.exists_dualBasis_of_unimodular_lattice_at_prime q g S r b hOk hb
  have hs'0 : s' ≠ 0 := by
    rintro rfl
    exact (Fact.out : q.Prime).one_lt.ne' (Nat.coprime_zero_left q |>.1 hs'q)
  have hmom := isMom_dual ι lam hι δ₀ hδ Ω hΩ0 S hOk b hb.1 t ht G μ hM s' hs'0 c hcLa hcb
  obtain ⟨hdp, hd16, -, -, -, -, hbeta, -⟩ := hOk
  constructor
  · intro hμ
    have hM' : MomInt ι (fun j => ι.symm (Ω / ι δ₀) • ((s' : ℂ)⁻¹ • c j)) G := by
      refine ⟨μ, hμ, ?_⟩
      have e : (fun j => ι.symm (Ω / ι δ₀) • ((s' : ℂ)⁻¹ • c j)) =
          fun j => (ι.symm (Ω / ι δ₀) / (s' : ℂ)) • c j := by
        funext j; simp only [smul_smul, div_eq_mul_inv]
      rw [e]; exact hmom
    refine GlobalTheory.T.latticeJetsAreBoundedMoments_of_span_imagQuadratic q ι (Fin g → ℂ) S.d (Ω / ι δ₀) S.La.toAddSubgroup (Fin r) (fun j => (s' : ℂ)⁻¹ • c j) G
      hdp hd16 hsplit ?_ hM'
    intro x hx
    rw [Submodule.mem_toAddSubgroup] at hx
    refine ⟨1, Nat.coprime_one_left q, fun i => beta S.d S.Hm x (b i), fun i => ?_, ?_⟩
    · obtain ⟨u, v, huv⟩ := hbeta x hx (b i) (hb.1 i)
      exact ⟨u, v, huv⟩
    · have hs'C : (s' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hs'0
      rw [Nat.cast_one, one_smul]
      calc x = (s' : ℂ)⁻¹ • ((s' : ℂ) • x) := by rw [smul_smul, inv_mul_cancel₀ hs'C, one_smul]
        _ = ∑ i, beta S.d S.Hm x (b i) • (s' : ℂ)⁻¹ • c i := by
          rw [hsp x hx, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, smul_smul, mul_comm]
  · intro hL
    have h1 := hL (Fin r) c (fun j => by simpa using hcLa j)
    obtain ⟨u, hu⟩ := exists_zc_inv s' hs'q
    have h2 := GlobalTheory.MomN.momInt_push q ι (Fin g → ℂ) (Fin r) (Fin r) (fun i => ι.symm (Ω / ι δ₀) • c i)
      (fun i => (ι.symm (Ω / ι δ₀) / (s' : ℂ)) • c i) (fun i j => if i = j then (s' : ℂ)⁻¹ else 0)
      (fun i j => if i = j then u else 0) G ?_ ?_ h1
    · obtain ⟨μ', hμ', hmom'⟩ := h2
      have he := GlobalTheory.MomN.measure_eq_of_moments q (Fin r) μ μ'
        (fun k j f hf => by rw [← hmom k j f hf, ← hmom' k j f hf])
      rw [he]; exact hμ'
    · intro i j
      split_ifs
      · rw [map_inv₀, map_natCast, ← hu]; rfl
      · simp [GlobalTheory.MomOne.zc]
    · intro i
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
      simp only [if_true]
      rw [smul_smul, div_eq_mul_inv, mul_comm]

end GlobalTheory.MomN
