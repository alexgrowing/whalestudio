import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeAutomorphismLcm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DGamCoprime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeLeSuccOfDvdMinkM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntSmulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardDvdSumTracePow

noncomputable section

namespace GlobalTheory.DGamPrimeToLevel

open Formalism.BasicNotions Formalism.MainNotions NumberField GlobalTheory.IndefiniteRowSideFullHecke.LatticeAutomorphismLcm

theorem minkMult_minkM (hM : Formalism.HermitianLatticeCounting.S6.MinkowskiBound) (n : ℕ) : MinkMult n (minkM n) := by
  intro H hH
  let e : Matrix.GeneralLinearGroup (Fin n) ℚ ≃* ((Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ)) :=
    Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv ℚ (Fin n → ℚ))
  let G : Subgroup ((Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ)) := H.map e.toMonoidHom
  have e' : H ≃* G := e.subgroupMap H
  have hG : Finite G := Finite.of_equiv _ e'.toEquiv
  let v : G × Fin n → (Fin n → ℚ) := fun p => p.1.1 (Pi.basisFun ℚ (Fin n) p.2)
  let Λ : Submodule (𝓞 ℚ) (Fin n → ℚ) := Submodule.span (𝓞 ℚ) (Set.range v)
  have hfg : Λ.FG := Submodule.fg_span (Set.finite_range v)
  have hsp : Submodule.span ℚ (Λ : Set (Fin n → ℚ)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℚ (Fin n)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨(1, i), rfl⟩
  have hst : ∀ g ∈ G, ∀ x ∈ Λ, g x ∈ Λ := by
    intro g hg x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨h, i⟩, rfl⟩ := hx
      exact Submodule.subset_span ⟨(⟨g, hg⟩ * h, i), rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Λ.add_mem hx hy
    | smul a x _ hx =>
      rw [← algebraMap_smul ℚ a x, map_smul, algebraMap_smul]
      exact Λ.smul_mem a hx
  have h := GlobalTheory.AutLattice.card_dvd_minkM hM ℚ (Fin n → ℚ) Λ hfg hsp G hG hst
  rw [Nat.card_congr e'.toEquiv]
  simpa using h

def PrimesLarge (D : D7) : Prop :=
  (∀ u, minkRank D + 1 < (D.mem u).A.T) ∧ (∀ a, minkRank D + 1 < D.host.g a) ∧
    minkRank D + 1 < D.host.q ∧ minkRank D + 1 < D.host.d

theorem primeToLevel_of_dvd {D : D7} (h : PrimesLarge D) {n : ℕ} (hn : n ∣ minkM (minkRank D)) :
    PrimeToLevel D n := by
  have hp : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ minkRank D + 1 := fun p hp hpn =>
    GlobalTheory.prime_le_succ_of_dvd_minkM _ p hp (hpn.trans hn)
  have key : ∀ p : ℕ, p.Prime → minkRank D + 1 < p → Nat.Coprime n p := by
    intro p hpp hlt
    refine ((Nat.Prime.coprime_iff_not_dvd hpp).2 fun h => ?_).symm
    have := hp p hpp h
    omega
  obtain ⟨g1, g2, g3, g4⟩ := h
  exact ⟨hn, hp, key _ D.host.hyp.1 g3, key _ D.host.hyp.2.1 g4,
    fun a => key _ (D.host.g_prime a) (g2 a), fun u => key _ (D.mem u).A.T_prime (g1 u)⟩

theorem minkRank_le {D : D7} (L : SizeData₂ D) (hN : (D.R.N D.R.m : ℝ) ≤ L.sc.x ^ (L.Ct + 1))
    (hx : 2 ≤ L.sc.x) : ((minkRank D + 1 : ℕ) : ℝ) ≤ L.sc.x ^ (2 * L.Ct + 5) := by
  have hf : D.R.f ≤ D.R.N D.R.m := le_trans (show D.R.f ≤ D.R.k from D.R.f_le_k) (Nat.le_add_right _ _)
  have h1 : 1 ≤ D.R.N D.R.m := by
    have := D.R.m_add_three_le_k
    unfold Ranks.N
    omega
  have hf' : (D.R.f : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast hf
  have h1' : (1 : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast h1
  have hx0 : 0 < L.sc.x := by linarith
  have e : L.sc.x ^ (2 * L.Ct + 5) = (L.sc.x ^ (L.Ct + 1)) ^ 2 * L.sc.x ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    congr 1
    push_cast
    ring
  have h8 : (2 : ℝ) ^ 3 ≤ L.sc.x ^ 3 := by gcongr
  have h2 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (L.sc.x ^ (L.Ct + 1)) ^ 2 := by gcongr
  have h3 : (D.R.N D.R.m : ℝ) ^ 2 * 2 ^ 3 ≤ (L.sc.x ^ (L.Ct + 1)) ^ 2 * L.sc.x ^ 3 := by gcongr
  rw [e]
  unfold minkRank
  push_cast
  nlinarith

theorem primesLarge_of_sizesUsed {D : D7} (L : SizeData₂ D) (h : SizesUsed L) : PrimesLarge D := by
  obtain ⟨⟨P⟩, hN, hT, hx⟩ := h
  have h0 := minkRank_le L hN hx
  have hq : minkRank D + 1 < D.host.q := by exact_mod_cast h0.trans_lt P.qd_pow.1
  have hd : minkRank D + 1 < D.host.d := by exact_mod_cast h0.trans_lt P.qd_pow.2
  have hC : SizeCond L := by
    have := P.condE_le
    unfold SizeCond szCond
    rw [Real.sqrt_eq_rpow]
    unfold LevelStarExponents.condE at this
    push_cast at this
    exact this
  have hs := GlobalTheory.DGamCoprime.q_le_sqrt_b L hC (by omega) (by omega)
  have hb := GlobalTheory.DGamCoprime.one_le_b L
  have hsb : Real.sqrt L.sc.b ≤ L.sc.b := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hqb : (D.host.q : ℝ) ≤ L.sc.b := hs.trans hsb
  refine ⟨fun u => ?_, fun a => ?_, hq, hd⟩
  · have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
    have h1 : L.sc.b ^ (1 : ℝ) ≤ L.sc.b ^ ((D.R.m : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hb (by linarith)
    rw [Real.rpow_one] at h1
    have : (D.host.q : ℝ) ≤ ((D.mem u).A.T : ℝ) := hqb.trans (h1.trans (hT u))
    have : D.host.q ≤ (D.mem u).A.T := by exact_mod_cast this
    omega
  · obtain ⟨Y, hY, -, -, hg⟩ := P.g_Y
    have hk : (1 : ℝ) ≤ D.R.k := by
      have := D.R.m_add_three_le_k
      exact_mod_cast (show 1 ≤ D.R.k by omega)
    have h1 : L.sc.b ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
    have h2 : (D.R.k : ℝ) * L.sc.b ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 := le_self_pow₀ (hb.trans h1) (by norm_num)
    have : (D.host.q : ℝ) ≤ (D.host.g a : ℝ) := hqb.trans (h1.trans (h2.trans (hY.trans (hg a).1)))
    have : D.host.q ≤ D.host.g a := by exact_mod_cast this
    omega

theorem primeToLevelAt_of (hM : Formalism.HermitianLatticeCounting.S6.MinkowskiBound) {D : D7} (h : PrimesLarge D) (hD : DGamDef D)
    (hC : DGamChoice_at D) : PrimeToLevelAt D := by
  intro u μ
  rw [hD.one u u μ]
  exact primeToLevel_of_dvd h (hC _ (minkMult_minkM hM _) u)

theorem primesLarge_family {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x ∧ ∀ i : Fm.Ix x, PrimesLarge (Fm.D x i) := by
  obtain ⟨x0, hT⟩ := hT
  refine ⟨max x0 (Fm.x1 + 1), fun x hx => ?_⟩
  have hx1 : Fm.x1 < x := by linarith [(le_max_right _ _).trans hx]
  exact ⟨hx1, fun i => GlobalTheory.DGamCoprime.primes_gt (Fm.L x i) (Fm.sizes x hx1 i)
    (hT x ((le_max_left _ _).trans hx) i).1⟩

theorem row_of_minkowski (hM : Formalism.HermitianLatticeCounting.S6.MinkowskiBound) : Row := by
  refine ⟨fun D L hS hD hC => primeToLevelAt_of hM (primesLarge_of_sizesUsed L hS) hD hC,
    fun eps Fm hC hT => ?_⟩
  obtain ⟨x0, hP⟩ := primesLarge_family Fm hT
  obtain ⟨x0', hC⟩ := hC
  refine ⟨max x0 x0', fun x hx i => ?_⟩
  obtain ⟨hx1, hP⟩ := hP x ((le_max_left _ _).trans hx)
  exact primeToLevelAt_of hM (hP i) (Fm.ex x hx1 i).err.dgam (hC x ((le_max_right _ _).trans hx) i)

theorem row : Row := row_of_minkowski GlobalTheory.MinkowskiExact.minkowskiBound

end GlobalTheory.DGamPrimeToLevel

end
