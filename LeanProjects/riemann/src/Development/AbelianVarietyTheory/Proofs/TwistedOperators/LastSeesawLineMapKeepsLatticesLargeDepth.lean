import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.LastLineLat

variable {D : D7}

theorem of_tmul_eq (p : AF D.host.F) {m n : ℕ} (y : Fin m → Fin n → D.host.E) :
    (Matrix.of fun i j => p ⊗ₜ[D.host.F] y i j : Mx D m n) = (p ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • rat (Matrix.of y) := by
  ext i j
  simp only [rat, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  change _ = _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] y i j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem cA_tmul_one (p : AF D.host.F) : cA D (p ⊗ₜ[D.host.F] (1 : D.host.E)) = p ⊗ₜ[D.host.F] (1 : D.host.E) := by
  simp [cA, sigR]

theorem adj_rat {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : adj (rat M : Mx D m n) = rat Mᴴ := by
  ext i j
  simp [adj, rat, Matrix.conjTranspose_apply, GlobalTheory.DualPairCheck.cA_incA]

theorem rat_smul' {m n : ℕ} (c : D.host.E) (M : Matrix (Fin m) (Fin n) D.host.E) :
    (rat (c • M) : Mx D m n) = incA D c • rat M := by
  ext i j
  simp [rat]

theorem kap_gen {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) {c0 : D.host.E} (hτ : ∀ i k, τ i k = c0)
    (V : HSp D) (p : AF D.host.F) (a : D.host.E) (s : Fin V.rank → D.host.E)
    (t : Fin L''.rank → D.host.E) :
    kap τ V (Matrix.of fun i j => p ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * V.gram k j)) =
      Matrix.of fun i j => p ⊗ₜ[D.host.F] (s i * star (D.host.xi0⁻¹ * c0 * ∑ l, a * t l) * ∑ k, L.gram k j) := by
  have hy : (Matrix.of fun i j => a * t i * ∑ k, star (s k) * V.gram k j) =
      Matrix.vecMulVec (fun i => a * t i) (star s) * V.gram := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Finset.mul_sum, mul_assoc]
  have h1 := of_tmul_eq (D := D) p (fun i j => a * t i * ∑ k, star (s k) * V.gram k j)
  rw [hy] at h1
  have h2 := of_tmul_eq (D := D) p (fun i j => s i * star (D.host.xi0⁻¹ * c0 * ∑ l, a * t l) * ∑ k, L.gram k j)
  beta_reduce at h1 h2
  rw [h1, h2]
  unfold GlobalTheory.FinPl.kap GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  have he := cA_tmul_one (D := D) p
  generalize (p ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) = e at he ⊢
  rw [Matrix.mul_smul, adj_smul, he]
  rw [rat_mul (Matrix.vecMulVec (fun i => a * t i) (star s)) V.gram, ← Matrix.mul_assoc (rat τ), ← rat_mul τ,
    show (rat V.gram : Mx D V.rank V.rank) = gA V from rfl, adj_mul, adj_gA, adj_rat, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc, giA_gA_cancel, show gA L = (rat L.gram : Mx D L.rank L.rank) from rfl, ← rat_mul, smul_comm,
    ← rat_smul']
  congr 2
  ext i j
  congr 1
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, hτ,
    Pi.star_apply, Matrix.of_apply, smul_eq_mul, star_sum, star_mul', star_star, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg,
    Finset.mul_sum, Finset.sum_mul, inv_neg]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.LastLineLat

namespace GlobalTheory.LastLineLat

variable {D : D7}

theorem kap_add' {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) (w w' : WO S L'') :
    kap τ S (w + w') = kap τ S w + kap τ S w' := by
  have hadj : ∀ x y : Mx D L.rank S.rank, adj (x + y) = adj x + adj y := fun x y => by
    ext i j
    simp [adj]
  unfold GlobalTheory.FinPl.kap GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  rw [Matrix.mul_add (rat τ) w w', hadj, Matrix.add_mul, Matrix.mul_add, smul_add]

theorem line_mem {L V : HSp D} (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (hJ : D.host.AA ≤ D.host.AAbar * J)
    (Λ : Set (Fin V.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (α : Af D.host.F)
    (hα : α ∈ intAf D.host.F) (hP : ∀ v, ¬ P v → evalV D.host.F v α = 0) (s : Fin V.rank → D.host.E) (hs : s ∈ Λ)
    (c : D.host.E) (hc : c ∈ D.host.AA) :
    (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star c * ∑ k, L.gram k j) : Mx D V.rank L.rank) ∈
      latO L V (GlobalTheory.RowShape.latPi L J : Set _) Λ P := by
  have hc' : c ∈ D.host.AAbar * J := hJ hc
  refine FractionalIdeal.mul_induction_on (C := fun c => (Matrix.of fun i j =>
      pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star c * ∑ k, L.gram k j) : Mx D V.rank L.rank) ∈
      latO L V (GlobalTheory.RowShape.latPi L J : Set _) Λ P) hc' ?_ ?_
  · intro b hb e he
    refine AddSubgroup.subset_closure ⟨α, hα, hP, star b, ?_, fun _ => e, ?_, s, hs, ?_⟩
    · rw [bridge_star_holds D.R D.host b]; exact Formalism.L2.Pj.conj_mem_AA D hb
    · exact Submodule.mem_pi.2 fun _ _ => he
    · ext i j
      simp only [Matrix.of_apply, star_mul', Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun _ _ => by ring
  · intro x y hx hy
    have : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star (x + y) * ∑ k, L.gram k j) :
        Mx D V.rank L.rank) = (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star x * ∑ k, L.gram k j)) +
        (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star y * ∑ k, L.gram k j)) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.add_apply, star_add, mul_add, add_mul, TensorProduct.tmul_add]
    rw [this]
    exact add_mem hx hy

theorem AA_le_lineId (D : D7) (j : ℕ) (hj : j + 2 = D.R.m) :
    D.host.AA ≤ D.host.AAbar * GlobalTheory.RowShape.lineId D j := by
  have hb : D.host.AAbar ≠ 0 := by
    intro h
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [h] at h1
    simp at h1
  unfold GlobalTheory.RowShape.lineId
  rw [show (D.R.m - 2 - j) / 2 + 1 = 1 by omega, pow_one, pow_one, mul_comm D.host.AA, ← mul_assoc,
    mul_inv_cancel₀ hb, one_mul]

theorem mul_mem_AA {a : D.host.E} (ha : a ∈ D.host.AA) {t : D.host.E}
    (ht : t ∈ ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) : a * t ∈ D.host.AA := by
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff] at ht
  obtain ⟨y, rfl⟩ := ht
  rw [mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ y ha

end GlobalTheory.LastLineLat

namespace GlobalTheory.LastLineLat

theorem kap_latO (D : D7) (V : HSp D) (Λ : Set (Fin V.rank → D.host.E)) (j : ℕ) (hj : j + 2 = D.R.m)
    (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∀ w ∈ latO V (pLine D) Λ (GlobalTheory.RowShape.topL D : Set _) (· = v),
      kap lastTau V w ∈ latO (Model.nLine D) V (GlobalTheory.RowShape.lineL D j : Set _) Λ (· = v) := by
  have hle : latO V (pLine D) Λ (GlobalTheory.RowShape.topL D : Set _) (· = v) ≤
      (latO (Model.nLine D) V (GlobalTheory.RowShape.lineL D j : Set _) Λ (· = v)).comap (AddMonoidHom.mk' (kap lastTau V) (kap_add' lastTau V)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.mk'_apply]
    rw [kap_gen lastTau (c0 := -D.host.xi0) (fun _ _ => rfl)]
    refine line_mem _ (AA_le_lineId D j hj) Λ _ α hα hP s hs _ ?_
    have hx := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
    rw [show D.host.xi0⁻¹ * -D.host.xi0 = -1 by rw [mul_neg, inv_mul_cancel₀ hx], neg_one_mul]
    have ht' : t ∈ GlobalTheory.RowShape.latPi (pLine D) 1 := ht
    exact Submodule.neg_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) (Submodule.sum_mem _ fun l _ => mul_mem_AA ha (Submodule.mem_pi.1 ht' l (Set.mem_univ _)))
  exact fun w hw => hle hw

end GlobalTheory.LastLineLat

theorem GlobalTheory.LastLineLat.kap_lastTau_latO : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j, j + 2 = D.R.m → ∀ v, ∀ w ∈ latO (ch.G.V (.top (j + 1))) (pLine D) (ch.G.Λ (.top (j + 1)) : Set _) (GlobalTheory.RowShape.topL D : Set _) (· = v),
    GlobalTheory.FinPl.kap lastTau _ w ∈ latO (GlobalTheory.SeeSaw.Model.nLine D) (ch.G.V (.top (j + 1))) (GlobalTheory.RowShape.lineL D j : Set _) (ch.G.Λ (.top (j + 1)) : Set _) (· = v) := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R _ _ ch _ _ j hj v
  exact GlobalTheory.LastLineLat.kap_latO D _ _ j hj v
