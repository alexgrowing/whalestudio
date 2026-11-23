import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.AbsoluteL2Bound
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.AffineGL.GenSpace
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GlRelationsDerivativePreserved
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantCoefficientsExpansion
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.JacquetBasis
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ConjQdet

noncomputable section

open Polynomial

namespace GlobalTheory.CompanionTheory.PolyNilGrad

open Formalism.REAL (GlRel qdet)
open GlobalTheory.SmGL (stdBlocks modExp blk)
open GlobalTheory.CompanionTheory.Dblock.CentreBlocks (sumPoly sumPoly_monic sumPoly_coeff sumPoly_eval)
open GlobalTheory.CompanionTheory.Dblock.CentreManyBlocks (isIntegral_coeff_of_shifted_prod)

section Abstract

variable {V : Type} [AddCommGroup V] [Module ℂ V] {c N : ℕ}

def upperImg (n : Fin c → ℕ) (h : ∑ i, n i = N) (Xf : Fin N → Fin N → Module.End ℂ V) : Submodule ℂ V :=
  Submodule.span ℂ {y | ∃ (p q : Fin N) (w : V),
    blk (stdBlocks n h) p < blk (stdBlocks n h) q ∧ y = Xf p q w}

theorem apply_mem_upperImg (n : Fin c → ℕ) (h : ∑ i, n i = N) (Xf : Fin N → Fin N → Module.End ℂ V)
    {y : Module.End ℂ V}
    (hy : y ∈ Submodule.span ℂ {y : Module.End ℂ V | ∃ (p q : Fin N) (w : Module.End ℂ V),
      blk (stdBlocks n h) p < blk (stdBlocks n h) q ∧ y = Xf p q * w}) (x : V) :
    y x ∈ upperImg n h Xf := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, q, w, hpq, rfl⟩ := hy
    exact Submodule.subset_span ⟨p, q, w x, hpq, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => simpa using Submodule.add_mem _ ha hb
  | smul r a _ ha => simpa using Submodule.smul_mem _ r ha

theorem exists_monic_trace (n : Fin c → ℕ) (h : ∑ i, n i = N) (Xf : Fin N → Fin N → Module.End ℂ V)
    (hX : GlRel Xf) (Pc : ℂ → ℂ)
    (hP : ∀ Y : ℂ, ∃ k : ℕ, (qdet Xf (Y + ((N : ℂ) - 1) / 2) - Pc Y • (1 : Module.End ℂ V)) ^ k = 0)
    (r : Fin c → ℂ) :
    ∃ q : ℂ[X], q.Monic ∧ ∀ x : V, aeval (∑ i, r i • ∑ p : Fin (n i),
      Xf (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, p⟩)) q x ∈ upperImg n h Xf := by
  classical
  let Xi : ∀ i, Fin (n i) → Fin (n i) → Module.End ℂ V :=
    fun i p q => Xf (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩)
  have hinj : ∀ i : Fin c, Function.Injective fun p : Fin (n i) => stdBlocks n h ⟨i, p⟩ :=
    fun i => (stdBlocks n h).injective.comp sigma_mk_injective
  have hne : ∀ (i j : Fin c) (p : Fin (n i)) (r : Fin (n j)), i ≠ j →
      stdBlocks n h ⟨i, p⟩ ≠ stdBlocks n h ⟨j, r⟩ := by
    intro i j p r hij e
    exact hij (congrArg Sigma.fst ((stdBlocks n h).injective e))
  have hglr : ∀ i, GlRel (Xi i) := fun i => GlobalTheory.CapHC.glRel_restrict hX _ (hinj i)
  have hcm : ∀ i j, i ≠ j → ∀ p q r v, Commute (Xi i p q) (Xi j r v) := by
    intro i j hij p q r v
    have := hX (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩) (stdBlocks n h ⟨j, r⟩) (stdBlocks n h ⟨j, v⟩)
    rw [if_neg (hne _ _ _ _ hij), if_neg (hne _ _ _ _ (Ne.symm hij)), sub_self] at this
    exact sub_eq_zero.1 this
  obtain ⟨a, ha1, hform, htr, hcomm⟩ := GlobalTheory.CompanionTheory.RgCOBlock.capelli_coef_commute V c n Xi hglr hcm
  let s : Set (Module.End ℂ V) := Set.range fun p : Fin c × ℕ => a p.1 p.2
  have hcs : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact (hcomm _ _ _ _).eq
  letI : CommRing (Algebra.adjoin ℂ s) := Algebra.adjoinCommRingOfComm ℂ hcs
  let I := upperImg n h Xf
  let Yd : Ideal (Algebra.adjoin ℂ s) :=
    { carrier := {x | ∀ F, (x : Module.End ℂ V) F ∈ I}
      add_mem' := fun {x y} hx hy F => by
        simpa using I.add_mem (hx F) (hy F)
      zero_mem' := fun F => by simp
      smul_mem' := fun b x hx F => by
        show ((b * x : Algebra.adjoin ℂ s) : Module.End ℂ V) F ∈ I
        rw [mul_comm, Subalgebra.coe_mul, Module.End.mul_apply]
        exact hx _ }
  let π := Ideal.Quotient.mkₐ ℂ Yd
  have hamem : ∀ i k, a i k ∈ Algebra.adjoin ℂ s := fun i k => Algebra.subset_adjoin ⟨(i, k), rfl⟩
  have hRmem : ∀ i t, qdet (Xi i) t ∈ Algebra.adjoin ℂ s := fun i t => by
    rw [hform]
    exact sum_mem fun k _ => Subalgebra.smul_mem _ (hamem i k) _
  let Pp : Fin c → (Algebra.adjoin ℂ s ⧸ Yd)[X] := fun i =>
    sumPoly (fun k => π ⟨a i k, hamem i k⟩) (n i)
  have hPm : ∀ i, (Pp i).Monic := fun i => sumPoly_monic _ _ (by
    have : (⟨a i (n i), hamem i (n i)⟩ : Algebra.adjoin ℂ s) = 1 := Subtype.ext (ha1 i)
    simp only [this, map_one])
  have hPev : ∀ i (t : ℂ), (Pp i).eval (algebraMap ℂ _ t) = π ⟨qdet (Xi i) t, hRmem i t⟩ := by
    intro i t
    have : (⟨qdet (Xi i) t, hRmem i t⟩ : Algebra.adjoin ℂ s)
        = ∑ k ∈ Finset.range (n i + 1), t ^ k • (⟨a i k, hamem i k⟩ : Algebra.adjoin ℂ s) :=
      Subtype.ext (by simp [hform])
    rw [this, map_sum, sumPoly_eval]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Algebra.smul_def, map_pow, mul_comm]
  let φ : Algebra.adjoin ℂ s →* Module.End ℂ V :=
    { toFun := Subtype.val, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let sh : Fin c → ℂ := fun i => ((n i : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) i : ℂ) / 2
  have hDR : ∀ v i t, Commute (qdet Xf v) (qdet (Xi i) t) := fun v i t =>
    GlobalTheory.CompanionTheory.CTFin.CapComm.commute_qdet_of (fun p q => Formalism.REAL.qDetCentral _ _ Xf hX v _ _) t
  have hprod : ∀ u : ℂ, IsIntegral ℂ
      (∏ i ∈ Finset.univ, (Pp i).eval (algebraMap ℂ (Algebra.adjoin ℂ s ⧸ Yd) (u + sh i))) := by
    intro u
    let b : Algebra.adjoin ℂ s := ∏ i, ⟨qdet (Xi i) (u + sh i), hRmem i _⟩
    have hb : (b : Module.End ℂ V) = (List.ofFn fun i => qdet (Xi i) (u + sh i)).prod := by
      show φ (∏ i, (⟨qdet (Xi i) (u + sh i), hRmem i _⟩ : Algebra.adjoin ℂ s)) = _
      rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
      rfl
    have hval : ∏ i ∈ Finset.univ, (Pp i).eval (algebraMap ℂ (Algebra.adjoin ℂ s ⧸ Yd) (u + sh i)) = π b := by
      simp_rw [hPev]
      rw [← map_prod]
    obtain ⟨k, hk⟩ := hP u
    set D := qdet Xf (u + ((N : ℂ) - 1) / 2) with hD
    have hspan := GlobalTheory.T.capelliDet_block_levi_congr_mod_upperBlockIdeal (Module.End ℂ V) n h Xf hX u
    have hspan' : D - (b : Module.End ℂ V) ∈ Submodule.span ℂ {y : Module.End ℂ V | ∃ (p q : Fin N) (w : Module.End ℂ V),
        blk (stdBlocks n h) p < blk (stdBlocks n h) q ∧ y = Xf p q * w} := by
      rw [hb]
      simpa only [sh, Xi, add_sub_assoc] using hspan
    have hDb : Commute D (b : Module.End ℂ V) := by
      rw [hb]
      exact Commute.list_prod_right _ _ (fun y hy => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
        exact hDR _ _ _)
    let Fb : Module.End ℂ V := (b : Module.End ℂ V) - Pc u • 1
    let Dz : Module.End ℂ V := D - Pc u • 1
    have hs : ∀ z : Module.End ℂ V, Commute z (Pc u • (1 : Module.End ℂ V)) :=
      fun z => (Commute.one_right z).smul_right _
    have hc : Commute Fb Dz :=
      (hDb.symm.sub_right (hs _)).sub_left ((hs D).symm.sub_right (hs _))
    have hpow : (b - algebraMap ℂ _ (Pc u)) ^ k ∈ Yd := by
      intro x
      have e1 : (((b - algebraMap ℂ (Algebra.adjoin ℂ s) (Pc u)) ^ k : Algebra.adjoin ℂ s) : Module.End ℂ V) = Fb ^ k := by
        simp [Fb, Algebra.algebraMap_eq_smul_one]
      have e2 := hc.mul_geom_sum₂ k
      rw [show Dz ^ k = 0 from hk, sub_zero] at e2
      rw [e1, ← e2]
      have e3 : Fb - Dz = -(D - (b : Module.End ℂ V)) := by simp [Fb, Dz]
      rw [e3, Module.End.mul_apply, LinearMap.neg_apply]
      exact I.neg_mem (apply_mem_upperImg n h Xf hspan' _)
    rw [hval]
    refine ⟨(X - C (Pc u)) ^ k, (monic_X_sub_C _).pow k, ?_⟩
    have e4 : π ((b - algebraMap ℂ _ (Pc u)) ^ k) = 0 := by
      rw [Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hpow
    rw [map_pow, map_sub, AlgHom.commutes] at e4
    simp only [eval₂_pow, eval₂_sub, eval₂_X, eval₂_C]
    exact e4
  have hcoef := isIntegral_coeff_of_shifted_prod Pp sh Finset.univ (fun i _ => hPm i) hprod
  have htrace : ∀ i, ∃ hm : (∑ p, Xi i p p) ∈ Algebra.adjoin ℂ s, IsIntegral ℂ (π ⟨∑ p, Xi i p p, hm⟩) := by
    intro i
    by_cases h0 : 1 ≤ n i
    · have e : ∑ p, Xi i p p = a i (n i - 1) + (((n i : ℂ) * ((n i : ℂ) - 1) / 2)) • (1 : Module.End ℂ V) := by
        rw [htr i h0]; abel
      have hm : (∑ p, Xi i p p) ∈ Algebra.adjoin ℂ s := by
        rw [e]
        exact add_mem (hamem _ _) (Subalgebra.smul_mem _ (Subalgebra.one_mem _) _)
      refine ⟨hm, ?_⟩
      have e2 : (⟨∑ p, Xi i p p, hm⟩ : Algebra.adjoin ℂ s) =
          ⟨a i (n i - 1), hamem _ _⟩ + algebraMap ℂ _ ((n i : ℂ) * ((n i : ℂ) - 1) / 2) :=
        Subtype.ext (by simp [e, Algebra.algebraMap_eq_smul_one])
      rw [e2, map_add, AlgHom.commutes]
      refine IsIntegral.add ?_ isIntegral_algebraMap
      have := hcoef i (Finset.mem_univ i) (n i - 1)
      simp only [Pp, sumPoly_coeff] at this
      rwa [if_pos (by omega)] at this
    · have hz : n i = 0 := by omega
      have hE : IsEmpty (Fin (n i)) := by rw [hz]; infer_instance
      have e : ∑ p, Xi i p p = 0 := Finset.sum_of_isEmpty _
      have hm : (∑ p, Xi i p p) ∈ Algebra.adjoin ℂ s := by rw [e]; exact zero_mem _
      refine ⟨hm, ?_⟩
      have e2 : (⟨∑ p, Xi i p p, hm⟩ : Algebra.adjoin ℂ s) = 0 := Subtype.ext e
      rw [e2, map_zero]
      exact isIntegral_zero
  choose hm hI using htrace
  let Tb : Algebra.adjoin ℂ s := ∑ i, r i • (⟨∑ p, Xi i p p, hm i⟩ : Algebra.adjoin ℂ s)
  have hTb : (Tb : Module.End ℂ V) = ∑ i, r i • ∑ p : Fin (n i),
      Xf (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, p⟩) := by
    simp [Tb, Xi]
  have hint : IsIntegral ℂ (π Tb) := by
    simp only [Tb, map_sum, map_smul]
    exact IsIntegral.sum _ fun i _ => (hI i).smul _
  obtain ⟨q, hqm, hq0⟩ := hint
  refine ⟨q, hqm, fun x => ?_⟩
  rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem] at hq0
  have := hq0 x
  rwa [Polynomial.aeval_subalgebra_coe, hTb] at this

end Abstract

section Grading

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec.J

local notation "aM" => ReciprocityTheory.ChartRestriction.DS.actM

section Act

variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

def actL (E : Fin n → Fin n → Module.End ℂ V) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ V where
  toFun := aM E
  map_add' P Q := by
    simp only [ReciprocityTheory.ChartRestriction.DS.actM, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [ReciprocityTheory.ChartRestriction.DS.actM, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
      RingHom.id_apply]

theorem actL_apply (E : Fin n → Fin n → Module.End ℂ V) (P : Matrix (Fin n) (Fin n) ℂ) :
    actL E P = aM E P := rfl

theorem actM_bracket (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (P Q : Matrix (Fin n) (Fin n) ℂ) :
    aM E P * aM E Q - aM E Q * aM E P = aM E (P * Q - Q * P) := by
  classical
  have h1 : aM E P * aM E Q - aM E Q * aM E P =
      ∑ a, ∑ b, ∑ c, ∑ d, (P a b * Q c d) • ((if b = c then E a d else 0) - (if d = a then E c b else 0)) := by
    have hmul : ∀ f g : Fin n → Fin n → Module.End ℂ V, (∑ a, ∑ b, f a b) * (∑ c, ∑ d, g c d) =
        ∑ a, ∑ b, ∑ c, ∑ d, f a b * g c d := by
      intro f g
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
    have hmul' : ∀ f g : Fin n → Fin n → Module.End ℂ V, (∑ c, ∑ d, g c d) * (∑ a, ∑ b, f a b) =
        ∑ a, ∑ b, ∑ c, ∑ d, g c d * f a b := by
      intro f g
      simp only [Finset.mul_sum]
      simp only [Finset.sum_mul]
    simp only [ReciprocityTheory.ChartRestriction.DS.actM]
    rw [hmul, hmul']
    simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [← hE a b c d, smul_mul_smul_comm, smul_mul_smul_comm, smul_sub, mul_comm (Q c d)]
  have t1 : ∑ a, ∑ b, ∑ c, ∑ d, (P a b * Q c d) • (if b = c then E a d else 0) =
      ∑ x, ∑ y, (∑ k, P x k * Q k y) • E x y := by
    refine Finset.sum_congr rfl fun a _ => ?_
    have e : ∀ b, ∑ c, ∑ d, (P a b * Q c d) • (if b = c then E a d else 0) =
        ∑ d, (P a b * Q b d) • E a d := by
      intro b
      rw [Finset.sum_eq_single b]
      · simp
      · intro c _ hc
        simp [Ne.symm hc]
      · simp
    simp only [e, Finset.sum_smul]
    exact Finset.sum_comm
  have t2 : ∑ a, ∑ b, ∑ c, ∑ d, (P a b * Q c d) • (if d = a then E c b else 0) =
      ∑ x, ∑ y, (∑ k, Q x k * P k y) • E x y := by
    have e : ∀ a b c, ∑ d, (P a b * Q c d) • (if d = a then E c b else 0) = (P a b * Q c a) • E c b := by
      intro a b c
      simp
    simp only [e, Finset.sum_smul]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]
  rw [h1]
  simp only [smul_sub, Finset.sum_sub_distrib, t1, t2]
  simp only [ReciprocityTheory.ChartRestriction.DS.actM, Matrix.sub_apply, Matrix.mul_apply, sub_smul, Finset.sum_sub_distrib]

end Act

variable {n : ℕ}

theorem conj_mul {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) (M M' : Matrix (Fin n) (Fin n) ℂ) :
    (B.U * M * B.Ui) * (B.U * M' * B.Ui) = B.U * (M * M') * B.Ui := by
  calc _ = B.U * M * (B.Ui * B.U) * M' * B.Ui := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [B.hUi, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem glRel_Eb (X : GMod n) {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) : GlRel (Eb X B) := by
  classical
  intro a b c d
  have hs := fun a b c d : Fin n => conj_mul B (Matrix.single a b (1 : ℂ)) (Matrix.single c d 1)
  have hm : ∀ a b c d : Fin n, Matrix.single a b (1 : ℂ) * Matrix.single c d 1 =
      if b = c then Matrix.single a d 1 else 0 := by
    intro a b c d
    split_ifs with h
    · subst h; simp
    · exact Matrix.single_mul_single_of_ne _ _ _ _ h _
  show aM X.E _ * aM X.E _ - aM X.E _ * aM X.E _ = _
  rw [actM_bracket X.E X.gl, hs, hs, hm, hm]
  rw [← actL_apply, map_sub]
  have hz : aM X.E 0 = 0 := map_zero (actL X.E)
  by_cases h1 : b = c <;> by_cases h2 : d = a <;>
    simp [h1, h2, Eb, actL_apply, hz]

def dG {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) (p : Fin n) : ℂ := (![-1, 0, 1] : Fin 3 → ℂ) (bl B p)

theorem A_eq {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) : A = B.U * Matrix.diagonal (dG B) * B.Ui := B.eq

theorem actM_grading (X : GMod n) {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) :
    CompanionTheory.RgExh.Dec.L.actM X A = ∑ i, (![-1, 0, 1] : Fin 3 → ℂ) i • ∑ p : Fin (dims n B.j i),
      Eb X B (GlobalTheory.SmGL.stdBlocks (dims n B.j) B.hj ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks (dims n B.j) B.hj ⟨i, p⟩) := by
  classical
  have hd : Matrix.diagonal (dG B) = ∑ p, dG B p • Matrix.single p p (1 : ℂ) := by
    ext a b
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply]
    by_cases h : a = b
    · subst h
      simp
    · rw [if_neg h]
      symm
      refine Finset.sum_eq_zero fun c _ => ?_
      have : ¬(c = a ∧ c = b) := fun e => h (e.1.symm.trans e.2)
      simp [this]
  have h1 : CompanionTheory.RgExh.Dec.L.actM X A = ∑ p, dG B p • Eb X B p p := by
    show aM X.E A = _
    rw [← actL_apply]
    conv_lhs => rw [A_eq B, hd]
    rw [Finset.mul_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, map_smul]
    rfl
  rw [h1, ← Equiv.sum_comp (GlobalTheory.SmGL.stdBlocks (dims n B.j) B.hj), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [dG, bl]

theorem mem_nilpC {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) {p q : Fin n} (h : bl B p < bl B q) :
    B.U * Matrix.single p q 1 * B.Ui ∈ CompanionTheory.RgExh.Dec.L.nilpC A := by
  classical
  set Y := B.U * Matrix.single p q 1 * B.Ui with hY
  have hc : A * Y - Y * A = (dG B p - dG B q) • Y := by
    have hD1 : Matrix.diagonal (dG B) * Matrix.single p q (1 : ℂ) = dG B p • Matrix.single p q (1 : ℂ) := by
      ext i j
      rw [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
      split_ifs with hh
      · rw [hh.1]
      · simp
    have hD2 : Matrix.single p q (1 : ℂ) * Matrix.diagonal (dG B) = dG B q • Matrix.single p q (1 : ℂ) := by
      ext i j
      rw [Matrix.mul_diagonal, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
      split_ifs with hh
      · rw [hh.2, one_mul, mul_one]
      · simp
    have e1 : A * Y = dG B p • Y := by
      have e0 : A * Y = (B.U * Matrix.diagonal (dG B) * B.Ui) * Y := congrArg (· * Y) (A_eq B)
      rw [e0, hY, conj_mul, hD1, Matrix.mul_smul, Matrix.smul_mul]
    have e2 : Y * A = dG B q • Y := by
      have e0 : Y * A = Y * (B.U * Matrix.diagonal (dG B) * B.Ui) := congrArg (Y * ·) (A_eq B)
      rw [e0, hY, conj_mul, hD2, Matrix.mul_smul, Matrix.smul_mul]
    rw [e1, e2, sub_smul]
  have key : ∀ i j : Fin 3, i < j → (![-1, 0, 1] : Fin 3 → ℂ) i - (![-1, 0, 1] : Fin 3 → ℂ) j = -1 ∨
      (![-1, 0, 1] : Fin 3 → ℂ) i - (![-1, 0, 1] : Fin 3 → ℂ) j = -2 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> norm_num
  rcases key _ _ h with e | e
  · refine ⟨Y, 0, by simp, ?_, by simp⟩
    rw [hc]
    simp only [dG, e, neg_smul, one_smul]
  · refine ⟨0, Y, by simp, by simp, ?_⟩
    rw [hc]
    simp only [dG, e, neg_smul]

theorem exists_sum_of_mem_upperImg (X : GMod n) {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) {u : X.V}
    (hu : u ∈ upperImg (dims n B.j) B.hj (Eb X B)) :
    ∃ (m : ℕ) (Y : Fin m → Matrix (Fin n) (Fin n) ℂ) (v : Fin m → X.V),
      (∀ k, Y k ∈ CompanionTheory.RgExh.Dec.L.nilpC A) ∧ u = ∑ k, CompanionTheory.RgExh.Dec.L.actM X (Y k) (v k) := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, q, w, hpq, rfl⟩ := hy
    exact ⟨1, fun _ => B.U * Matrix.single p q 1 * B.Ui, fun _ => w, fun _ => mem_nilpC B hpq, by
      simp; rfl⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, Y, v, hY, rfl⟩ := ha
    obtain ⟨m', Y', v', hY', rfl⟩ := hb
    refine ⟨m + m', Fin.append Y Y', Fin.append v v', fun k => ?_, ?_⟩
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
      · rw [Fin.append_left]; exact hY k
      · rw [Fin.append_right]; exact hY' k
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
  | smul r a _ ha =>
    obtain ⟨m, Y, v, hY, rfl⟩ := ha
    exact ⟨m, Y, fun k => r • v k, hY, by simp [Finset.smul_sum]⟩

theorem polyNilPath_of (hB : Basis) (hC : ConjQdet) : CompanionTheory.RgExh.Dec.L.PolyNilPath := by
  intro n ε X χ A hχ hA
  obtain ⟨B⟩ := hB n ε A hA
  obtain ⟨k, hk⟩ := hχ
  obtain ⟨q, hqm, hq⟩ := exists_monic_trace (dims n B.j) B.hj (Eb X B) (glRel_Eb X B) (Formalism.QuantumDeterminants.capP χ)
    (fun Y => ⟨k, by
      have e : qdet (Eb X B) (Y + ((n : ℂ) - 1) / 2) = qdet X.E (Y + ((n : ℂ) - 1) / 2) :=
        hC n X B.U B.Ui B.hU B.hUi _
      rw [e]
      exact hk Y⟩) ![-1, 0, 1]
  refine ⟨q, hqm, fun u => ?_⟩
  have h := hq u
  rw [← actM_grading X B] at h
  exact exists_sum_of_mem_upperImg X B h

end Grading

theorem polyNilPath : CompanionTheory.RgExh.Dec.L.PolyNilPath :=
  polyNilPath_of GlobalTheory.CompanionTheory.GradEig.basis GlobalTheory.CompanionTheory.RgConjQdet.conjQdet

end GlobalTheory.CompanionTheory.PolyNilGrad
