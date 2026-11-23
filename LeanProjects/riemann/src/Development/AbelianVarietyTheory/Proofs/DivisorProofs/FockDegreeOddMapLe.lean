import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuaTripleProportionalToNonzero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFock

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.FockParity

open GlobalTheory.RealLift GlobalTheory.FockCompactW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

variable (F) in

def sgnAd : AF F := ((-1 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))

theorem sgnAd_mul_self : sgnAd F * sgnAd F = 1 := by
  refine Prod.ext ?_ ?_
  · show (-1 : InfiniteAdeleRing F) * (-1) = 1
    ring
  · show (1 : FiniteAdeleRing (𝓞 F) F) * 1 = 1
    ring

theorem mul_sgnAd {u : AF F} (hu : evI F u = 0) : u * sgnAd F = u := by
  have h0 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  refine Prod.ext ?_ ?_
  · show u.1 * (-1 : InfiniteAdeleRing F) = u.1
    rw [h0, zero_mul]
  · show u.2 * (1 : FiniteAdeleRing (𝓞 F) F) = u.2
    rw [mul_one]

theorem evI_sgnAd_add_one : evI F (sgnAd F + 1) = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F ((-1 : InfiniteAdeleRing F) + 1) = 0
  rw [neg_add_cancel, map_zero]

theorem evI_neg' (a : AF F) : evI F (-a) = -evI F a :=
  map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1

theorem exists_neg_one_kInf (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ k ∈ KInf σ Y τ, ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → mat k * u = -u := by
  have hss : (sgnAd F • (1 : Matrix (Fin n) (Fin n) (AE F E))) * (sgnAd F • 1) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sgnAd_mul_self, one_smul, Matrix.one_mul]
  have hmap : (sgnAd F • (1 : Matrix (Fin n) (Fin n) (AE F E))).map (cA σ) = sgnAd F • 1 := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  refine ⟨⟨⟨sgnAd F • 1, sgnAd F • 1, hss, hss⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · show (sgnAd F • (1 : Matrix (Fin n) (Fin n) (AE F E)))ᵀ * incM F Y.J * (sgnAd F • (1 : Matrix (Fin n) (Fin n) (AE F E))).map (cA σ) = incM F Y.J
    rw [hmap, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      sgnAd_mul_self, one_smul, Matrix.one_mul, Matrix.mul_one]
  · intro u hu
    show u • (sgnAd F • (1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0
    rw [smul_sub, smul_smul, mul_sgnAd hu, sub_self]
  · intro w
    have e : (sgnAd F • (1 : Matrix (Fin n) (Fin n) (AE F E))).map (piInf (τ w)) =
        piInf (τ w) (sgnAd F • (1 : AE F E)) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    show Commute ((sgnAd F • (1 : Matrix (Fin n) (Fin n) (AE F E))).map (piInf (τ w))) (Y.θ w)
    rw [e]
    exact (Commute.one_left _).smul_left _
  · intro u hu
    show (sgnAd F • (1 : Matrix (Fin n) (Fin n) (AE F E))) * u = -u
    have h := hu _ evI_sgnAd_add_one
    rw [add_smul, one_smul] at h
    rw [Matrix.smul_mul, Matrix.one_mul]
    exact eq_neg_of_add_eq_zero_left h

theorem sd_intertwine_left {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} {χ₁ χ₂ : Chr F E} {om : Rep σ Y W}
    (hw : M.IsWeil ψ χ₁ χ₂ om) (k : UA σ Y.J) {f f₁ g g₁ : SInf F (Fin n × Fin d)}
    (hf : Acts (evI F) (om (k, 1)) f g) (hf₁ : Acts (evI F) (om (k, 1)) f₁ g₁) {u : Matrix (Fin n) (Fin d) (AE F E)}
    (hD : SD (M.heisLine ψ u) f f₁) : SD (M.heisLine ψ (mat k * u)) g g₁ := by
  have hS := IsUWeilPair.isUSplitting hw
  intro r hr l hl
  have h1 := hD r hr _ (hS.adm (k, 1) l hl)
  simp only [LinearMap.comp_apply] at h1
  rw [sa_of_acts hf₁ r hr] at h1
  refine h1.congr_of_eventuallyEq (.of_forall fun t => ?_)
  have h2 := hS.impl (k, 1) (realAd F t • u) (pureA F f r) (Submodule.subset_span ⟨f, r, hr, rfl⟩)
  have h3 : actAB (cA σ) ((k, 1) : UA σ Y.J × UA σ W.J) (realAd F t • u) = realAd F t • (mat k * u) := by
    change mat k * (realAd F t • u) * (1 : Matrix (Fin d) (Fin d) (AE F E))ᵀ = _
    rw [Matrix.transpose_one, Matrix.mul_one, Matrix.mul_smul]
  rw [h3, sa_of_acts hf r hr] at h2
  exact congrArg l h2.symm

def fockLt (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ℕ → Submodule ℂ (SInf F (Fin n × Fin d))
  | 0 => ⊥
  | k + 1 => fockDeg M ψ τ k

theorem fockLt_le (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (k : ℕ) :
    fockLt M ψ τ k ≤ fockDeg M ψ τ k := by
  cases k with
  | zero => exact bot_le
  | succ k => exact fockDeg_mono M ψ τ (Nat.le_succ k)

theorem exists_parity_op {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} {χ₁ χ₂ : Chr F E} {om : Rep σ Y W}
    (hψ : IsStd ψ) (hw : M.IsWeil ψ χ₁ χ₂ om) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (hline : ∀ f₀, f₀ ≠ 0 → M.IsGauss ψ τ f₀ → ∀ g, M.IsGauss ψ τ g → ∃ c : ℂ, g = c • f₀) :
    ∃ k ∈ KInf σ Y τ, ∃ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
      (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) (⇑f) (⇑(A f))) ∧ ∃ c : ℂ, ∀ m : ℕ,
        ∀ f ∈ fockDeg M ψ τ m, A f - (c * (-1) ^ m) • f ∈ fockLt M ψ τ m := by
  obtain ⟨k, hk, hku⟩ := exists_neg_one_kInf (σ := σ) (Y := Y) (d := d) τ
  have h1 : (1 : UA σ W.J) ∈ UAt σ W (evI F) := by
    intro u _
    simp [mat]
  obtain ⟨A, hA⟩ := exists_op_of_UAt hψ hw (k, 1) hk.1 h1
  obtain ⟨D, hD⟩ := GlobalTheory.HeisDer.derEx F E σ _ _ _ ψ _ _ M.co hψ
  have hL := actsLaws F (Fin n × Fin d)
  have hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine ψ u) φ (D u φ) := fun u hu φ => (hD u hu φ).1
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (heisLine_zero M ψ u) (hSD u hu φ)
  have hneg : ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) (-u) := fun u hu v hv => by
    rw [smul_neg, hu v hv, neg_zero]
  have hDneg : ∀ u, At (evI F) u → ∀ φ, D (-u) φ = -D u φ := by
    intro u hu φ
    refine DFunLike.ext _ _ fun x => ?_
    rw [SchwartzMap.neg_apply, (hD _ (hneg u hu) φ).2 x, (hD u hu φ).2 x, map_neg]
    have e1 : (fun i => evI F ((-M.co.e u).1 i)) = -fun i => evI F ((M.co.e u).1 i) := by
      funext i
      exact evI_neg' _
    have e2 : ∑ i, x i * evI F ((-M.co.e u).2 i) = -∑ i, x i * evI F ((M.co.e u).2 i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_neg, ← evI_neg']
      rfl
    rw [e1, e2, map_neg, map_neg]
    push_cast
    ring
  have hanti : ∀ u, At (evI F) u → ∀ φ, A (D u φ) = -D u (A φ) := by
    intro u hu φ
    have h := sd_intertwine_left hw k (hA φ) (hA _) (hSD u hu φ)
    rw [hku u hu] at h
    rw [← hDneg u hu]
    exact (hL _ _ _).2.2.2.2 _ h (hSD _ (hneg u hu) _)
  have hgauss : ∀ f₀, M.IsGauss ψ τ f₀ → M.IsGauss ψ τ (A f₀) := by
    rintro f₀ ⟨ε, hε⟩
    refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
    have e1 := (hL _ _ _).2.2.1 _ hg (hAD u hu _)
    have e2 := (hL _ _ _).2.2.1 _ hg' (hAD u' hu' _)
    have key := hε u u' hu hu' huu _ _ (hAD u hu f₀) (hAD u' hu' f₀)
    have a1 := hanti u hu f₀
    have a2 := hanti u' hu' f₀
    rw [key, map_smul, a1, smul_neg, neg_inj] at a2
    rw [e1, e2, a2]
  have hc : ∃ c : ℂ, ∀ f₀, M.IsGauss ψ τ f₀ → A f₀ = c • f₀ := by
    by_cases h0 : ∃ f₀, f₀ ≠ 0 ∧ M.IsGauss ψ τ f₀
    · obtain ⟨f₀, hne, hg⟩ := h0
      obtain ⟨c, hc⟩ := hline f₀ hne hg _ (hgauss f₀ hg)
      refine ⟨c, fun g hg' => ?_⟩
      obtain ⟨b, rfl⟩ := hline f₀ hne hg g hg'
      rw [map_smul, hc, smul_comm]
    · refine ⟨0, fun g hg => ?_⟩
      have : g = 0 := by
        by_contra hne
        exact h0 ⟨g, hne, hg⟩
      rw [this, map_zero, smul_zero]
  obtain ⟨c, hc⟩ := hc
  have hDdeg : ∀ m u, At (evI F) u → ∀ φ ∈ fockDeg M ψ τ m, D u φ ∈ fockDeg M ψ τ (m + 1) := fun m u hu φ hφ =>
    Submodule.mem_sup_right (Submodule.subset_span ⟨u, hu, φ, hφ, hAD u hu φ⟩)
  have hDlt : ∀ m u, At (evI F) u → ∀ φ ∈ fockLt M ψ τ m, D u φ ∈ fockLt M ψ τ (m + 1) := by
    intro m u hu φ hφ
    cases m with
    | zero =>
      have : φ = 0 := (Submodule.mem_bot ℂ).1 hφ
      rw [this, map_zero]
      exact zero_mem _
    | succ m => exact hDdeg m u hu φ hφ
  refine ⟨k, hk, A, hA, c, fun m => ?_⟩
  suffices h : fockDeg M ψ τ m ≤ (fockLt M ψ τ m).comap (A - (c * (-1) ^ m) • LinearMap.id) from fun f hf => h hf
  induction m with
  | zero =>
    rw [fockDeg_zero]
    refine Submodule.span_le.2 fun f₀ hf₀ => ?_
    show A f₀ - (c * (-1) ^ 0) • f₀ ∈ (⊥ : Submodule ℂ _)
    rw [hc f₀ hf₀, pow_zero, mul_one, sub_self]
    exact zero_mem _
  | succ m ih =>
    rw [fockDeg_succ]
    refine sup_le (fun f hf => ?_) (Submodule.span_le.2 ?_)
    · show A f - (c * (-1) ^ (m + 1)) • f ∈ fockDeg M ψ τ m
      have h2 : A f - (c * (-1) ^ m) • f ∈ fockDeg M ψ τ m := fockLt_le M ψ τ m (ih hf)
      have e : A f - (c * (-1) ^ (m + 1)) • f = (A f - (c * (-1) ^ m) • f) + (c * (-1) ^ m - c * (-1) ^ (m + 1)) • f := by
        rw [sub_smul]; abel
      rw [e]
      exact add_mem h2 (Submodule.smul_mem _ _ hf)
    · rintro φ₁ ⟨u, hu, φ, hφ, hd⟩
      have e : φ₁ = D u φ := (hL _ _ _).2.2.1 _ hd (hAD u hu φ)
      subst e
      show A (D u φ) - (c * (-1) ^ (m + 1)) • D u φ ∈ fockLt M ψ τ (m + 1)
      have h2 : A φ - (c * (-1) ^ m) • φ ∈ fockLt M ψ τ m := ih hφ
      have h3 := neg_mem (hDlt m u hu _ h2)
      have e : A (D u φ) - (c * (-1) ^ (m + 1)) • D u φ = -D u (A φ - (c * (-1) ^ m) • φ) := by
        rw [hanti u hu, map_sub, map_smul, pow_succ, ← mul_assoc, mul_neg_one, neg_smul]
        abel
      rw [e]
      exact h3

theorem map_fockDeg_odd_le : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ j : ℕ, (fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j + 1)).map R.p ≤
        (fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j)).map R.p := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' R Rf hM j
  obtain ⟨k, hk, A, hA, c, hc⟩ := exists_parity_op hM.triple.base.std hM.triple.weil B.emb
    (GlobalTheory.GaussLine.gauss_eq_smul B G X om om' hM.triple)
  have hp : ∀ m, ∀ f ∈ fockDeg G.M B.ψ B.emb m,
      (1 - c * (-1) ^ m) • R.p f ∈ (fockLt G.M B.ψ B.emb m).map R.p := by
    intro m f hf
    refine ⟨_, hc m f hf, ?_⟩
    rw [map_sub, map_smul, hM.real.quot.cpt k hk f (fockDeg_le_pol _ _ _ _ hf) _ (hA f), sub_smul, one_smul]
  rintro _ ⟨f, hf, rfl⟩
  by_cases hf0 : R.p f = 0
  · rw [hf0]
    exact zero_mem _
  have hne : {m | ∃ f ∈ fockDeg G.M B.ψ B.emb m, R.p f ≠ 0}.Nonempty := ⟨_, f, hf, hf0⟩
  obtain ⟨g, hg, hpg⟩ : ∃ g ∈ fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p), R.p g ≠ 0 := Nat.sInf_mem hne
  have hlow : ∀ m, m ≤ lowDegInf B G.M R.p → ∀ φ ∈ fockLt G.M B.ψ B.emb m, R.p φ = 0 := by
    intro m hm φ hφ
    cases m with
    | zero => rw [(Submodule.mem_bot ℂ).1 hφ, map_zero]
    | succ m =>
      by_contra h
      exact Nat.notMem_of_lt_sInf (s := {m | ∃ f ∈ fockDeg G.M B.ψ B.emb m, R.p f ≠ 0}) (Nat.lt_of_succ_le hm) ⟨φ, hφ, h⟩
  have hone : c * (-1) ^ lowDegInf B G.M R.p = 1 := by
    obtain ⟨φ, hφ, e⟩ := hp _ g hg
    rw [hlow _ le_rfl φ hφ] at e
    exact (sub_eq_zero.1 ((smul_eq_zero.1 e.symm).resolve_right hpg)).symm
  have h2 := hp _ f hf
  have e : (1 - c * (-1) ^ (lowDegInf B G.M R.p + 2 * j + 1) : ℂ) = 2 := by
    rw [pow_succ, pow_add, pow_mul, ← mul_assoc, ← mul_assoc, hone]
    norm_num
  rw [e] at h2
  exact (Submodule.smul_mem_iff _ two_ne_zero).1 h2

end GlobalTheory.FockParity

end
