import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.Columns.LocWLemmas
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanLocalIff

open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix Pointwise

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

section Gen

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

def nbGen (S : ι → Set (MvPolynomial (Fin n × Fin n) K)) : Set (Pol K ι n) :=
  {P | ∃ f : ι → MvPolynomial (Fin n × Fin n) K, (∀ τ, f τ ∈ S τ) ∧ P = ten f}

theorem nb_tensorLat_span (R : Type) [CommRing R] [Algebra R K] (S : ι → Set (MvPolynomial (Fin n × Fin n) K)) :
    Formalism.GradedWeylDivisibility.tensorLat R K (fun τ => Submodule.span R (S τ)) = Submodule.span R (nbGen S) := by
  apply le_antisymm
  · unfold Formalism.GradedWeylDivisibility.tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    have h1 : ∀ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (F τ) ∈
        Submodule.span R ((fun f => Formalism.GradedWeylDivisibility.blockEmb K (S := ι) τ f) '' S τ) := by
      intro τ
      have h := Submodule.mem_map_of_mem
        (f := ((Formalism.GradedWeylDivisibility.blockEmb K (S := ι) (k := n) (n := n) τ).toLinearMap.restrictScalars R)) (hF τ)
      rw [Submodule.map_span] at h
      exact h
    have h2 : ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (F τ) ∈
        Submodule.span R (∏ τ, ((fun f => Formalism.GradedWeylDivisibility.blockEmb K (S := ι) τ f) '' S τ)) := by
      rw [← Submodule.prod_span]
      exact Formalism.L2.Col.prod_mem_prod_sub _ _ _ fun τ _ => h1 τ
    refine Submodule.span_mono ?_ h2
    intro x hx
    rw [Set.mem_finsetProd] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    have hg' : ∀ τ, ∃ f ∈ S τ, Formalism.GradedWeylDivisibility.blockEmb K (S := ι) τ f = g τ := fun τ => hg (Finset.mem_univ τ)
    choose f hf hfg using hg'
    exact ⟨f, hf, by simp only [ten, hfg]⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨f, fun τ => Submodule.subset_span (hf τ), rfl⟩

def bideterminantsOfShape (K : Type) [Field K] {n : ℕ} (ν : Fin n → ℕ) : Set (MvPolynomial (Fin n × Fin n) K) :=
  {f | ∃ (N : ℕ) (sz : Fin N → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin n),
    Formalism.GradedWeylDivisibility.shapeDeg sz = ν ∧ f = Formalism.GradedWeylDivisibility.bideterminant K sz hsz I}

def nbWord (K : Type) [Field K] {n : ℕ} (ν : Fin n → ℕ) : Set (MvPolynomial (Fin n × Fin n) K) :=
  Set.range fun w : List (Fin n × Fin n × ℕ) => Formalism.GradedWeylDivisibility.applyWord K w (Formalism.GradedWeylDivisibility.hw K le_rfl ν)

theorem nb_map_nablaSq (R : Type) [CommRing R] [IsDomain R] [Algebra R K] (lam : DomWeight n) :
    (nablaSq R n lam).map (mapAlgHom (σ := Fin n × Fin n) (Algebra.ofId R K)).toLinearMap =
      Submodule.span R (bideterminantsOfShape K lam.natW) := by
  unfold nablaSq
  rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain R n n lam.natW, Submodule.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨N, sz, hsz, I, h, rfl⟩, rfl⟩
    exact ⟨N, sz, hsz, I, h, Formalism.GradedWeylDivisibility.ldlat_map_bidet _ _ _ _⟩
  · rintro ⟨N, sz, hsz, I, h, rfl⟩
    exact ⟨_, ⟨N, sz, hsz, I, h, rfl⟩, Formalism.GradedWeylDivisibility.ldlat_map_bidet _ _ _ _⟩

theorem nb_map_delSq (R : Type) [CommRing R] [Algebra R K] (lam : DomWeight n) :
    (delSq R n lam).map (mapAlgHom (σ := Fin n × Fin n) (Algebra.ofId R K)).toLinearMap =
      Submodule.span R (nbWord K lam.natW) := by
  unfold delSq Formalism.GradedWeylDivisibility.weyl
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1
  unfold nbWord
  congr 1
  funext w
  show MvPolynomial.map (algebraMap R K) _ = _
  rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]

end Gen

section Loc

variable {K : Type} [Field K] [NumberField K]

local notation "Ow" => Formalism.L2.Col.Ow

theorem nb_mk'_smul {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K)) [Module (Ow w) V]
    [IsScalarTower (𝓞 K) (Ow w) V] (a : 𝓞 K) (t : w.asIdeal.primeCompl) (x : V) :
    (t : 𝓞 K) • ((IsLocalization.mk' (Ow w) a t) • x) = a • x := by
  rw [← algebraMap_smul (Ow w) (t : 𝓞 K), smul_smul, IsLocalization.mk'_spec', algebraMap_smul]

theorem nb_mem_span_ow {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K)) [Module (Ow w) V]
    [IsScalarTower (𝓞 K) (Ow w) V] (T : Set V) (x : V) :
    x ∈ Submodule.span (Ow w) T ↔ x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) T) := by
  first | exact GlobalTheory.LocalSpanCriterion.span_local_iff .. | (apply GlobalTheory.LocalSpanCriterion.span_local_iff <;> assumption) | (intros; apply GlobalTheory.LocalSpanCriterion.span_local_iff <;> assumption) | (apply @GlobalTheory.LocalSpanCriterion.span_local_iff <;> assumption) | (intros; apply @GlobalTheory.LocalSpanCriterion.span_local_iff <;> assumption) | (apply @GlobalTheory.LocalSpanCriterion.span_local_iff <;> first | assumption | infer_instance) | exact @GlobalTheory.LocalSpanCriterion.span_local_iff K ‹_› ‹_› V ‹_› ‹_› w ‹_› ‹_› T x | exact @GlobalTheory.LocalSpanCriterion.span_local_iff K ‹_› ‹_› V ‹_› ‹_› w ‹_› ‹_› T | exact @GlobalTheory.LocalSpanCriterion.span_local_iff K ‹_› ‹_› V ‹_› ‹_› w ‹_› ‹_› | exact @GlobalTheory.LocalSpanCriterion.span_local_iff K ‹_› ‹_› V ‹_› ‹_› w ‹_› | exact @GlobalTheory.LocalSpanCriterion.span_local_iff K ‹_› ‹_› V ‹_› ‹_› w | exact @GlobalTheory.LocalSpanCriterion.span_local_iff K ‹_› ‹_› V ‹_› ‹_› | exact @GlobalTheory.LocalSpanCriterion.span_local_iff K ‹_› ‹_› V ‹_› | exact @GlobalTheory.LocalSpanCriterion.span_local_iff K ‹_› ‹_› V | exact @GlobalTheory.LocalSpanCriterion.span_local_iff K ‹_› ‹_› | exact @GlobalTheory.LocalSpanCriterion.span_local_iff K ‹_› | exact @GlobalTheory.LocalSpanCriterion.span_local_iff K

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem nb_nabStd_eq (lam : ι → DomWeight n) :
    nabStd K lam = Submodule.span (𝓞 K) (nbGen fun τ => bideterminantsOfShape K (lam τ).natW) := by
  have h : (fun τ => (nablaSq (𝓞 K) n (lam τ)).map (toK K _)) =
      fun τ => Submodule.span (𝓞 K) (bideterminantsOfShape K (lam τ).natW) := funext fun τ => nb_map_nablaSq (𝓞 K) (lam τ)
  rw [nabStd, h, nb_tensorLat_span]

theorem nb_delStd_eq (lam : ι → DomWeight n) :
    delStd K lam = Submodule.span (𝓞 K) (nbGen fun τ => nbWord K (lam τ).natW) := by
  have h : (fun τ => (delSq (𝓞 K) n (lam τ)).map (toK K _)) =
      fun τ => Submodule.span (𝓞 K) (nbWord K (lam τ).natW) := funext fun τ => nb_map_delSq (𝓞 K) (lam τ)
  rw [delStd, h, nb_tensorLat_span]

def nbNabW (w : HeightOneSpectrum (𝓞 K)) (lam : ι → DomWeight n) : Submodule (Ow w) (Pol K ι n) :=
  Formalism.GradedWeylDivisibility.tensorLat (Ow w) K fun τ =>
    (nablaSq (Ow w) n (lam τ)).map (mapAlgHom (σ := Fin n × Fin n) (Algebra.ofId (Ow w) K)).toLinearMap

def nbDelW (w : HeightOneSpectrum (𝓞 K)) (lam : ι → DomWeight n) : Submodule (Ow w) (Pol K ι n) :=
  Formalism.GradedWeylDivisibility.tensorLat (Ow w) K fun τ =>
    (delSq (Ow w) n (lam τ)).map (mapAlgHom (σ := Fin n × Fin n) (Algebra.ofId (Ow w) K)).toLinearMap

theorem nb_mem_nabW (w : HeightOneSpectrum (𝓞 K)) (lam : ι → DomWeight n) (x : Pol K ι n) :
    x ∈ nbNabW w lam ↔ x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
  have h : (fun τ => (nablaSq (Ow w) n (lam τ)).map
      (mapAlgHom (σ := Fin n × Fin n) (Algebra.ofId (Ow w) K)).toLinearMap) =
      fun τ => Submodule.span (Ow w) (bideterminantsOfShape K (lam τ).natW) := funext fun τ => nb_map_nablaSq (Ow w) (lam τ)
  rw [nbNabW, h, nb_tensorLat_span, nb_nabStd_eq, nb_mem_span_ow]

theorem nb_mem_delW (w : HeightOneSpectrum (𝓞 K)) (lam : ι → DomWeight n) (x : Pol K ι n) :
    x ∈ nbDelW w lam ↔ x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (delStd K lam) := by
  have h : (fun τ => (delSq (Ow w) n (lam τ)).map
      (mapAlgHom (σ := Fin n × Fin n) (Algebra.ofId (Ow w) K)).toLinearMap) =
      fun τ => Submodule.span (Ow w) (nbWord K (lam τ).natW) := funext fun τ => nb_map_delSq (Ow w) (lam τ)
  rw [nbDelW, h, nb_tensorLat_span, nb_delStd_eq, nb_mem_span_ow]

end Loc

section Stab

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem nb_stab_gen (R : Type) [CommRing R] [Algebra R K] (lam : ι → DomWeight n)
    (M : ι → Submodule R (MvPolynomial (Fin n × Fin n) K)) (g : ι → GL (Fin n) K)
    (h : ∀ τ, ∀ f ∈ M τ, sqAct K n (lam τ) (g τ) f ∈ M τ) (x : Pol K ι n) (hx : x ∈ Formalism.GradedWeylDivisibility.tensorLat R K M) :
    actP lam g x ∈ Formalism.GradedWeylDivisibility.tensorLat R K M := by
  unfold Formalism.GradedWeylDivisibility.tensorLat at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun τ => sqAct K n (lam τ) (g τ) (F τ), fun τ => h τ _ (hF τ), ?_⟩
    exact actTen K ι n lam g F
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ hx

theorem nb_map_detPow {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (g : GL (Fin n) R) (e : ℤ) :
    φ (detPow R n g e) = detPow S n (Formalism.UG.bc φ g) e := by
  have h : Matrix.GeneralLinearGroup.det (Formalism.UG.bc φ g) = Units.map (φ : R →* S) (Matrix.GeneralLinearGroup.det g) := by
    apply Units.ext
    simp [Formalism.UG.bc, RingHom.map_det]
  unfold detPow
  rw [h, ← map_zpow (Units.map (φ : R →* S))]
  rfl

theorem nb_map_sqAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (lam : DomWeight n) (g : GL (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) :
    MvPolynomial.map φ (sqAct R n lam g f) = sqAct S n lam (Formalism.UG.bc φ g) (MvPolynomial.map φ f) := by
  unfold sqAct
  rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul, nb_map_detPow, Formalism.GradedWeylDivisibility.ldtwist_map_rowAct]
  congr 2

end Stab

section Scale

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem nb_rowAct_smul (c : K) (A : Matrix (Fin n) (Fin n) K) (ν : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) K)
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl K n n ν) :
    Formalism.GradedWeylDivisibility.rowAct K (c • A) f = c ^ (∑ t, ν t) • Formalism.GradedWeylDivisibility.rowAct K A f := by
  have hcs := Formalism.GradedWeylDivisibility.colSums K n n ν f hf
  have h1 : (fun v : Fin n × Fin n => ∑ b : Fin n, (C ((c • A) v.1 b) * X (b, v.2) : MvPolynomial (Fin n × Fin n) K)) =
      fun v => C c * ∑ b : Fin n, C (A v.1 b) * X (b, v.2) := by
    funext v
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul, C_mul, mul_assoc]
  unfold Formalism.GradedWeylDivisibility.rowAct
  rw [h1, aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h2 : ∑ v : Fin n × Fin n, m v = ∑ t, ν t := by
    rw [Fintype.sum_prod_type_right]
    exact Finset.sum_congr rfl fun t _ => hcs m hm t
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h2]
  rw [smul_eq_C_mul, C_pow]
  ring

theorem nb_blockAct_smul (lam : ι → DomWeight n) (c : K) (A : ι → Matrix (Fin n) (Fin n) K) (x : Pol K ι n)
    (hx : x ∈ VV K lam) :
    Formalism.GradedWeylDivisibility.blockAct K (fun τ => c • A τ) x = c ^ (∑ τ, ∑ t, (lam τ).natW t) • Formalism.GradedWeylDivisibility.blockAct K A x := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    rw [map_prod, map_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_smul]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [(Formalism.GradedWeylDivisibility.blockActTensor K K ι n n _).1 τ (F τ), (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n _).1 τ (F τ),
      nb_rowAct_smul c (A τ) _ _ (hF τ), map_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, smul_add]
  | smul r x _ hx => rw [map_smul, map_smul, hx, smul_comm]

end Scale

section Main

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

local notation "Ow" => Formalism.L2.Col.Ow

theorem nb_osmul {σ : Type} (r : 𝓞 K) (F : MvPolynomial σ K) : r • F = (algebraMap (𝓞 K) K r) • F :=
  (algebraMap_smul K r F).symm

theorem nb_wsmul {σ : Type} (w : HeightOneSpectrum (𝓞 K)) (r : Ow w) (F : MvPolynomial σ K) :
    r • F = (algebraMap (Ow w) K r) • F :=
  (algebraMap_smul K r F).symm

theorem nb_one_smul {σ : Type} (x : MvPolynomial σ K) : (1 : 𝓞 K) • x = x := one_smul _ _

theorem nb_mul_smul {σ : Type} (a b : 𝓞 K) (x : MvPolynomial σ K) : (a * b) • x = a • b • x := mul_smul _ _ _

theorem nb_smul_comm {σ : Type} (a b : 𝓞 K) (x : MvPolynomial σ K) : a • b • x = b • a • x := smul_comm _ _ _

theorem nb_mem_locP {σ : Type} (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) (MvPolynomial σ K))
    (x : MvPolynomial σ K) : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ L :=
  lc_mem_locP w L x

theorem smul_mem_locP_iff_of_notMem {σ : Type} (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) (MvPolynomial σ K))
    {s : 𝓞 K} (hs : s ∉ w.asIdeal) (x : MvPolynomial σ K) :
    s • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L ↔ x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L :=
  smul_mem_localized_iff w L hs x

theorem nb_smul_mem {σ : Type} (L : Submodule (𝓞 K) (MvPolynomial σ K)) (r : 𝓞 K) {x : MvPolynomial σ K}
    (hx : x ∈ L) : r • x ∈ L := L.smul_mem r hx

def NbStab (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n)) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 K)) (u : ι → GL (Fin n) (Ow w)) (g : ι → GL (Fin n) K),
    (∀ τ, (u τ : Matrix (Fin n) (Fin n) (Ow w)).map (algebraMap (Ow w) K) = (g τ : Matrix (Fin n) (Fin n) K)) →
    ∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T, actP lam g x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T

theorem nb_stab_nab (lam : ι → DomWeight n) : NbStab lam (nabStd K lam) := by
  intro w u g hg x hx
  rw [← nb_mem_nabW] at hx ⊢
  refine nb_stab_gen (Ow w) lam _ g ?_ x hx
  rintro τ _ ⟨f0, hf0, rfl⟩
  have hg' : g τ = Formalism.UG.bc (algebraMap (Ow w) K) (u τ) := Units.ext (hg τ).symm
  refine ⟨sqAct (Ow w) n (lam τ) (u τ) f0, (factSqStable (Ow w) n (lam τ) (u τ)).1 f0 hf0, ?_⟩
  rw [hg']
  exact nb_map_sqAct (algebraMap (Ow w) K) (lam τ) (u τ) f0

theorem nb_stab_del (lam : ι → DomWeight n) : NbStab lam (delStd K lam) := by
  intro w u g hg x hx
  rw [← nb_mem_delW] at hx ⊢
  refine nb_stab_gen (Ow w) lam _ g ?_ x hx
  rintro τ _ ⟨f0, hf0, rfl⟩
  have hg' : g τ = Formalism.UG.bc (algebraMap (Ow w) K) (u τ) := Units.ext (hg τ).symm
  refine ⟨sqAct (Ow w) n (lam τ) (u τ) f0, (factSqStable (Ow w) n (lam τ) (u τ)).2 f0 hf0, ?_⟩
  rw [hg']
  exact nb_map_sqAct (algebraMap (Ow w) K) (lam τ) (u τ) f0

theorem nb_indep {lam : ι → DomWeight n} {T : Submodule (𝓞 K) (Pol K ι n)} (hT : NbStab lam T)
    (w : HeightOneSpectrum (𝓞 K)) (M : ι → Submodule (𝓞 K) (Fin n → K)) (B B' : ι → GL (Fin n) K)
    (hB : ∀ τ, IsBasisAt w (M τ) (B τ)) (hB' : ∀ τ, IsBasisAt w (M τ) (B' τ)) (F : Pol K ι n)
    (h : actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T) : actP lam B'⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T := by
  choose u hu using fun τ => lc_unitOw w (hB τ) (hB' τ)
  have h1 := hT w u (B'⁻¹ * B) hu _ h
  rwa [← polyAction_mul, mul_assoc, mul_inv_cancel, mul_one] at h1

theorem nablaIndependence_holds : NabIndep := by
  intro K _ _ ι _ n lam w M B B' hB hB' F
  exact ⟨nb_indep (nb_stab_nab lam) w M B B' hB hB' F, nb_indep (nb_stab_nab lam) w M B' B hB' hB F⟩

theorem deltaIndependence_holds : DelIndep := by
  intro K _ _ ι _ n lam w M B B' hB hB' F
  exact ⟨nb_indep (nb_stab_del lam) w M B B' hB hB' F, nb_indep (nb_stab_del lam) w M B' B hB' hB F⟩

theorem nb_mem_transLat (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n))
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (F : Pol K ι n) :
    F ∈ transLat lam T M ↔ ∀ (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (M τ) (B τ)) →
      actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T := by
  simp only [transLat, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]

theorem nb_free {lam : ι → DomWeight n} {T : Submodule (𝓞 K) (Pol K ι n)} (hT : NbStab lam T)
    (B : ι → GL (Fin n) K) :
    transLat lam T (fun τ => colLat (B τ)) = T.map ((actP lam B).restrictScalars (𝓞 K)) := by
  ext F
  rw [nb_mem_transLat]
  constructor
  · intro h
    refine ⟨actP lam B⁻¹ F, ?_, ?_⟩
    · have h1 : actP lam B⁻¹ F ∈ ⨅ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T := by
        rw [Submodule.mem_iInf]
        exact fun w => h w B fun _ => rfl
      rwa [lc_iInf_locP] at h1
    · rw [LinearMap.coe_restrictScalars, ← polyAction_mul, mul_inv_cancel, polyAction_one₂]
  · rintro ⟨F0, hF0, rfl⟩ w B' hB'
    refine nb_indep hT w (fun τ => colLat (B τ)) B B' (fun _ => rfl) hB' _ ?_
    rw [LinearMap.coe_restrictScalars, ← polyAction_mul, inv_mul_cancel, polyAction_one₂]
    exact lc_le_locP w T hF0

theorem nablaDeltaFree_holds : NabDelFree := by
  intro K _ _ ι _ n lam B
  exact ⟨nb_free (nb_stab_nab lam) B, nb_free (nb_stab_del lam) B⟩

end Main

section Sandwich

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

local notation "Ow" => Formalism.L2.Col.Ow

theorem nb_nabW_le_VV (w : HeightOneSpectrum (𝓞 K)) (lam : ι → DomWeight n) (x : Pol K ι n) (hx : x ∈ nbNabW w lam) :
    x ∈ VV K lam := by
  unfold nbNabW Formalism.GradedWeylDivisibility.tensorLat at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    refine Submodule.subset_span ⟨F, fun τ => ?_, rfl⟩
    obtain ⟨f0, hf0, h⟩ := hF τ
    rw [← h]
    exact Formalism.GradedWeylDivisibility.dualWeylMap (Ow w) K (algebraMap (Ow w) K) n n _ f0 hf0
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [nb_wsmul]; exact Submodule.smul_mem _ _ hx

theorem nb_det_pow_mem (w : HeightOneSpectrum (𝓞 K)) (d : K) (h : Matrix (Fin n) (Fin n) K)
    (h1 : ∀ a b, d * h a b ∈ (algebraMap (Ow w) K).range) (k : ℕ) :
    d ^ (n * k) * h.det ^ k ∈ (algebraMap (Ow w) K).range := by
  choose U hU using h1
  have e : d • h = (Matrix.of U).map (algebraMap (Ow w) K) := by
    ext a b
    simp [hU]
  have e2 : d ^ (n * k) * h.det ^ k = (d • h).det ^ k := by
    rw [Matrix.det_smul, Fintype.card_fin, mul_pow, pow_mul]
  rw [e2, e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact Subring.pow_mem _ (RingHom.mem_range_self _ _) k

theorem nb_det_scale (w : HeightOneSpectrum (𝓞 K)) (d : K) (g : GL (Fin n) K)
    (h1 : ∀ a b, d * (g : Matrix (Fin n) (Fin n) K) a b ∈ (algebraMap (Ow w) K).range)
    (h2 : ∀ a b, d * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ∈ (algebraMap (Ow w) K).range) (e : ℤ) :
    d ^ (n * e.natAbs) * detPow K n g e ∈ (algebraMap (Ow w) K).range := by
  obtain ⟨k, rfl | rfl⟩ := e.eq_nat_or_neg
  · have : detPow K n g (k : ℤ) = (g : Matrix (Fin n) (Fin n) K).det ^ k := by
      simp [detPow]
    rw [this, Int.natAbs_natCast]
    exact nb_det_pow_mem w d _ h1 k
  · have : detPow K n g (-(k : ℤ)) = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ^ k := by
      unfold detPow
      rw [zpow_neg, ← inv_zpow, ← map_inv, zpow_natCast, Units.val_pow_eq_pow_val,
        Matrix.GeneralLinearGroup.val_det_apply]
    rw [this, Int.natAbs_neg, Int.natAbs_natCast]
    exact nb_det_pow_mem w d _ h2 k

def nbN (lam : ι → DomWeight n) : ℕ := (∑ τ, ∑ t, (lam τ).natW t) + ∑ τ, n * (lam τ).detShift.natAbs

theorem nb_scaleW (w : HeightOneSpectrum (𝓞 K)) (lam : ι → DomWeight n) (d : K) (g : ι → GL (Fin n) K)
    (h1 : ∀ τ a b, d * (g τ : Matrix (Fin n) (Fin n) K) a b ∈ (algebraMap (Ow w) K).range)
    (h2 : ∀ τ a b, d * (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ∈ (algebraMap (Ow w) K).range)
    (x : Pol K ι n) (hx : x ∈ nbNabW w lam) : d ^ nbN lam • actP lam g x ∈ nbNabW w lam := by
  have hxV := nb_nabW_le_VV w lam x hx
  have e1 : d ^ nbN lam • actP lam g x =
      ((∏ τ, d ^ (n * (lam τ).detShift.natAbs) * detPow K n (g τ) (lam τ).detShift)) •
        Formalism.GradedWeylDivisibility.blockAct K (fun τ => d • ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ) x := by
    rw [nb_blockAct_smul lam d _ x hxV, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    simp only [actP, trAct, detTwK, nbN, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_smul, pow_add]
    congr 1
    ring
  rw [e1]
  have h3 : (∏ τ, d ^ (n * (lam τ).detShift.natAbs) * detPow K n (g τ) (lam τ).detShift) ∈
      (algebraMap (Ow w) K).range :=
    Subring.prod_mem _ fun τ _ => nb_det_scale w d (g τ) (h1 τ) (h2 τ) _
  obtain ⟨r, hr⟩ := h3
  rw [← hr, ← nb_wsmul]
  refine Submodule.smul_mem _ r ?_
  refine (Formalism.GradedWeylDivisibility.blockActTensor (Ow w) K ι n n _).2 _ _ ?_ x hx
  rintro τ _ ⟨f0, hf0, rfl⟩
  choose U hU using h1 τ
  have e : d • ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = ((Matrix.of U)ᵀ).map (algebraMap (Ow w) K) := by
    ext a b
    simp [hU]
  refine ⟨Formalism.GradedWeylDivisibility.rowAct (Ow w) (Matrix.of U)ᵀ f0, Formalism.GradedWeylDivisibility.dualWeylRowStable (Ow w) n n _ _ f0 hf0, ?_⟩
  rw [e]
  exact Formalism.GradedWeylDivisibility.ldtwist_map_rowAct (algebraMap (Ow w) K) _ f0

theorem nb_scale (w : HeightOneSpectrum (𝓞 K)) (lam : ι → DomWeight n) (d : 𝓞 K) (g : ι → GL (Fin n) K)
    (h1 : ∀ τ a b, algebraMap (𝓞 K) K d * (g τ : Matrix (Fin n) (Fin n) K) a b ∈
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (1 : Submodule (𝓞 K) K))
    (h2 : ∀ τ a b, algebraMap (𝓞 K) K d * (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ∈
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (1 : Submodule (𝓞 K) K))
    (x : Pol K ι n) (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam)) :
    d ^ nbN lam • actP lam g x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
  rw [← nb_mem_nabW] at hx ⊢
  rw [nb_osmul, map_pow]
  exact nb_scaleW w lam _ g (fun τ a b => (mem_localized_one_iff w _).1 (h1 τ a b))
    (fun τ a b => (mem_localized_one_iff w _).1 (h2 τ a b)) x hx

theorem nb_sandwich_fam (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ τ, (∀ x ∈ M τ, d • x ∈ colLat (1 : GL (Fin n) K)) ∧
      (∀ x ∈ colLat (1 : GL (Fin n) K), d • x ∈ M τ) := by
  classical
  choose d hd0 hd1 hd2 using fun τ => lc_sandwich (M τ) (hM τ)
  refine ⟨∏ τ, d τ, Finset.prod_ne_zero_iff.mpr fun τ _ => hd0 τ, fun τ => ⟨fun x hx => ?_, fun x hx => ?_⟩⟩
  · rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ), mul_smul]
    exact Submodule.smul_mem _ _ (hd1 τ x hx)
  · rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ), mul_smul]
    exact Submodule.smul_mem _ _ (hd2 τ x hx)

theorem nb_entries (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) (Fin n → K)) (B : GL (Fin n) K)
    (hB : IsBasisAt w M B) (d : 𝓞 K) (h1 : ∀ x ∈ M, d • x ∈ colLat (1 : GL (Fin n) K))
    (h2 : ∀ x ∈ colLat (1 : GL (Fin n) K), d • x ∈ M) :
    (∀ a b, algebraMap (𝓞 K) K d * (B : Matrix (Fin n) (Fin n) K) a b ∈
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)) ∧
    (∀ a b, algebraMap (𝓞 K) K d * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ∈
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)) := by
  have h0 : IsBasisAt w (colLat (1 : GL (Fin n) K)) 1 := rfl
  constructor
  · intro a b
    have := lc_entries w hB h0 d (fun x hx => lc_le_locP w _ (h1 x hx)) a b
    rwa [inv_one, one_mul] at this
  · intro a b
    have := lc_entries w h0 hB d (fun x hx => lc_le_locP w _ (h2 x hx)) a b
    rwa [mul_one] at this

end Sandwich

section Lattice

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

local notation "Ow" => Formalism.L2.Col.Ow

theorem nb_nabStd_le_VV (lam : ι → DomWeight n) (x : Pol K ι n) (hx : x ∈ nabStd K lam) : x ∈ VV K lam := by
  obtain ⟨w⟩ := Formalism.L2.Col.nonempty_places K
  exact nb_nabW_le_VV w lam x ((nb_mem_nabW w lam x).2 (lc_le_locP w _ hx))

theorem nb_VV_eq_bid (lam : ι → DomWeight n) :
    VV K lam = Submodule.span K (nbGen fun τ => bideterminantsOfShape K (lam τ).natW) := by
  have h : (fun τ => nablaSq K n (lam τ)) = fun τ => Submodule.span K (bideterminantsOfShape K (lam τ).natW) :=
    funext fun τ => Formalism.GradedWeylDivisibility.standardMonomialSpanDomain K n n (lam τ).natW
  rw [VV, h, nb_tensorLat_span]

theorem nb_VV_eq_word (lam : ι → DomWeight n) :
    VV K lam = Submodule.span K (nbGen fun τ => nbWord K (lam τ).natW) := by
  have h : (fun τ => nablaSq K n (lam τ)) = fun τ => Submodule.span K (nbWord K (lam τ).natW) :=
    funext fun τ => Formalism.L2.Col.nablaSq_eq_delSq K (lam τ)
  rw [VV, h, nb_tensorLat_span]

theorem nb_nabStd_fg (lam : ι → DomWeight n) : (nabStd K lam).FG := by
  have hs := fun τ => (Formalism.GradedWeylDivisibility.sSBasis (𝓞 K) n n (lam τ).natW).choose_spec.1.2.1
  have h : (fun τ => (nablaSq (𝓞 K) n (lam τ)).map (toK K _)) = fun τ => Submodule.span (𝓞 K)
      (Set.range fun i => toK K _ ((Formalism.GradedWeylDivisibility.sSBasis (𝓞 K) n n (lam τ).natW).choose i)) := by
    funext τ
    unfold nablaSq
    rw [← hs τ, Submodule.map_span, ← Set.range_comp]
    rfl
  rw [nabStd, h, nb_tensorLat_span]
  apply Submodule.fg_span
  have : ∀ τ, Finite (Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW) := fun _ => (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  refine ((Set.Finite.pi' fun τ => Set.finite_range fun i =>
    toK K _ ((Formalism.GradedWeylDivisibility.sSBasis (𝓞 K) n n (lam τ).natW).choose i)).image fun f => ten f).subset ?_
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨f, hf, rfl⟩

theorem nb_common {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (A B : Submodule (𝓞 K) V) (hA : A.FG)
    (h : ∀ x ∈ A, ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ B) : ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ x ∈ A, c • x ∈ B := by
  classical
  obtain ⟨S, rfl⟩ := hA
  have h' : ∀ x : S, ∃ d : 𝓞 K, d ≠ 0 ∧ d • (x : V) ∈ B := fun x => h x (Submodule.subset_span x.2)
  choose d hd0 hd using h'
  refine ⟨∏ x : S, d x, Finset.prod_ne_zero_iff.mpr fun x _ => hd0 x, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨x, hx⟩ : S)), mul_smul]
    exact Submodule.smul_mem _ _ (hd ⟨x, hx⟩)
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

def NbComm (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n)) : Prop :=
  ∃ c : 𝓞 K, c ≠ 0 ∧ (∀ x ∈ nabStd K lam, c • x ∈ T) ∧ T ≤ nabStd K lam

theorem nb_comm_nab (lam : ι → DomWeight n) : NbComm lam (nabStd K lam) :=
  ⟨1, one_ne_zero, fun x hx => by rwa [nb_one_smul], le_rfl⟩

theorem nb_comm_del (lam : ι → DomWeight n) : NbComm lam (delStd K lam) := by
  obtain ⟨c, hc, h⟩ := nb_common (nabStd K lam) (delStd K lam) (nb_nabStd_fg lam) (fun x hx => by
    refine lc_exists_smul_mem (delStd K lam) ?_
    rw [nb_delStd_eq, Submodule.span_span_of_tower, ← nb_VV_eq_word]
    exact nb_nabStd_le_VV lam x hx)
  exact ⟨c, hc, h, delStd_le_nabStd K lam⟩

def nbAt (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n)) (M : ι → Submodule (𝓞 K) (Fin n → K))
    (w : HeightOneSpectrum (𝓞 K)) : Submodule (𝓞 K) (Pol K ι n) :=
  ⨅ (B : ι → GL (Fin n) K) (_ : ∀ τ, IsBasisAt w (M τ) (B τ)),
    (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T).comap ((actP lam B⁻¹).restrictScalars (𝓞 K))

theorem nb_transLat_eq (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n))
    (M : ι → Submodule (𝓞 K) (Fin n → K)) : transLat lam T M = ⨅ w, nbAt lam T M w := rfl

theorem nb_mem_at (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n))
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (w : HeightOneSpectrum (𝓞 K)) (F : Pol K ι n) :
    F ∈ nbAt lam T M w ↔ ∀ B : ι → GL (Fin n) K, (∀ τ, IsBasisAt w (M τ) (B τ)) →
      actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T := by
  simp only [nbAt, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]

theorem actP_smul₂ (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (r : 𝓞 K) (F : Pol K ι n) :
    actP lam g (r • F) = r • actP lam g F := LinearMap.map_smul_of_tower _ r F

theorem nb_at_closed (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n))
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (w : HeightOneSpectrum (𝓞 K)) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nbAt lam T M w) = nbAt lam T M w := by
  refine le_antisymm ?_ (lc_le_locP w _)
  intro x hx
  obtain ⟨s, hs, hx⟩ := (nb_mem_locP w _ x).1 hx
  rw [nb_mem_at] at hx ⊢
  intro B hB
  have := hx B hB
  rwa [actP_smul₂, smul_mem_locP_iff_of_notMem w _ hs] at this

theorem nb_at_comm {lam : ι → DomWeight n} {T : Submodule (𝓞 K) (Pol K ι n)} (hc : NbComm lam T)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ)) :
    ∃ e : 𝓞 K, e ≠ 0 ∧
      (∀ w, ∀ x ∈ nbAt lam T M w, e • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam)) ∧
      (∀ w, ∀ x ∈ nabStd K lam, e • x ∈ nbAt lam T M w) := by
  obtain ⟨c, hc0, hc1, hc2⟩ := hc
  obtain ⟨d, hd0, hd⟩ := nb_sandwich_fam M hM
  refine ⟨c * d ^ nbN lam, mul_ne_zero hc0 (pow_ne_zero _ hd0), fun w x hx => ?_, fun w x hx => ?_⟩
  · choose B hB using fun τ => latticeBasisExists_holds K n (M τ) (hM τ) w
    have h1 := localization_mono w.asIdeal hc2 ((nb_mem_at lam T M w x).1 hx B hB)
    have h2 := nb_scale w lam d B (fun τ => (nb_entries w (M τ) (B τ) (hB τ) d (hd τ).1 (hd τ).2).1)
      (fun τ => (nb_entries w (M τ) (B τ) (hB τ) d (hd τ).1 (hd τ).2).2) _ h1
    rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂] at h2
    rw [nb_mul_smul]
    exact nb_smul_mem _ c h2
  · rw [nb_mem_at]
    intro B hB
    have h2 := nb_scale w lam d B⁻¹ (fun τ => (nb_entries w (M τ) (B τ) (hB τ) d (hd τ).1 (hd τ).2).2)
      (fun τ a b => by
        have := (nb_entries w (M τ) (B τ) (hB τ) d (hd τ).1 (hd τ).2).1 a b
        simpa using this) x (lc_le_locP w _ hx)
    rw [nb_mul_smul, actP_smul₂, actP_smul₂]
    obtain ⟨s, hs, h3⟩ := (nb_mem_locP w _ _).1 h2
    refine (nb_mem_locP w _ _).2 ⟨s, hs, ?_⟩
    rw [nb_smul_comm]
    exact hc1 _ h3

theorem nb_loc {lam : ι → DomWeight n} {T : Submodule (𝓞 K) (Pol K ι n)} (hT : NbStab lam T) (hc : NbComm lam T)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ))
    (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K) (hB : ∀ τ, IsBasisAt w (M τ) (B τ)) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (transLat lam T M) =
      (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T).map ((actP lam B).restrictScalars (𝓞 K)) := by
  obtain ⟨e, he, h1, h2⟩ := nb_at_comm hc M hM
  rw [nb_transLat_eq, localized_iInf (nbAt lam T M) (nabStd K lam) e he (nb_at_closed lam T M) h1 h2 w]
  ext F
  rw [nb_mem_at]
  constructor
  · intro h
    refine ⟨actP lam B⁻¹ F, h B hB, ?_⟩
    rw [LinearMap.coe_restrictScalars, ← polyAction_mul, mul_inv_cancel, polyAction_one₂]
  · rintro ⟨F0, hF0, rfl⟩ B' hB'
    refine nb_indep hT w M B B' hB hB' _ ?_
    rw [LinearMap.coe_restrictScalars, ← polyAction_mul, inv_mul_cancel, polyAction_one₂]
    exact hF0

theorem nablaDeltaLocal_holds : NabDelLoc := by
  intro K _ _ ι _ n lam M hM w B hB
  exact ⟨nb_loc (nb_stab_nab lam) (nb_comm_nab lam) M hM w B hB, nb_loc (nb_stab_del lam) (nb_comm_del lam) M hM w B hB⟩

theorem nb_global {lam : ι → DomWeight n} {T : Submodule (𝓞 K) (Pol K ι n)} (hc : NbComm lam T)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ)) :
    ∃ e : 𝓞 K, e ≠ 0 ∧ (∀ x ∈ transLat lam T M, e • x ∈ nabStd K lam) ∧
      (∀ x ∈ nabStd K lam, e • x ∈ transLat lam T M) := by
  obtain ⟨e, he, h1, h2⟩ := nb_at_comm hc M hM
  refine ⟨e, he, fun x hx => ?_, fun x hx => ?_⟩
  · rw [nb_transLat_eq, Submodule.mem_iInf] at hx
    have : e • x ∈ ⨅ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
      rw [Submodule.mem_iInf]
      exact fun w => h1 w x (hx w)
    rwa [lc_iInf_locP] at this
  · rw [nb_transLat_eq, Submodule.mem_iInf]
    exact fun w => h2 w x hx

theorem nb_le_VV {lam : ι → DomWeight n} {T : Submodule (𝓞 K) (Pol K ι n)} (hc : NbComm lam T)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ)) (F : Pol K ι n)
    (hF : F ∈ transLat lam T M) : F ∈ VV K lam := by
  obtain ⟨e, he, h1, -⟩ := nb_global hc M hM
  have h := nb_nabStd_le_VV lam _ (h1 F hF)
  rw [nb_osmul] at h
  have he' : algebraMap (𝓞 K) K e ≠ 0 := by
    rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  have := (VV K lam).smul_mem (algebraMap (𝓞 K) K e)⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ he', one_smul] at this

theorem nablaLeVV_holds : NabLeVV := by
  intro K _ _ ι _ n lam M hM F hF
  exact nb_le_VV (nb_comm_nab lam) M hM F hF

theorem nb_lattice {lam : ι → DomWeight n} {T : Submodule (𝓞 K) (Pol K ι n)} (hc : NbComm lam T)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ)) :
    Submodule.IsLattice K ((transLat lam T M).comap ((VV K lam).subtype.restrictScalars (𝓞 K))) := by
  obtain ⟨e, he, h1, h2⟩ := nb_global hc M hM
  have he' : algebraMap (𝓞 K) K e ≠ 0 := by
    rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  constructor
  · let φ : VV K lam →ₗ[𝓞 K] Pol K ι n := e • ((VV K lam).subtype.restrictScalars (𝓞 K))
    have hφ : Function.Injective φ := by
      intro x y hxy
      apply Subtype.ext
      have h3 : e • (x : Pol K ι n) = e • (y : Pol K ι n) := hxy
      rw [nb_osmul, nb_osmul] at h3
      exact smul_right_injective _ he' h3
    refine Submodule.fg_of_fg_map_injective φ hφ (Submodule.FG.of_le (nb_nabStd_fg lam) ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact h1 _ hx
  · apply Submodule.map_injective_of_injective (f := (VV K lam).subtype) (VV K lam).injective_subtype
    rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    · refine le_trans (le_of_eq (nb_VV_eq_bid lam)) ?_
      rw [Submodule.span_le]
      intro P hP
      have hP1 : P ∈ nabStd K lam := by
        rw [nb_nabStd_eq]
        exact Submodule.subset_span hP
      have hP2 := h2 P hP1
      have hP3 : e • P ∈ VV K lam := nb_le_VV hc M hM _ hP2
      have hP4 : e • P ∈ Submodule.span K ((VV K lam).subtype ''
          ((transLat lam T M).comap ((VV K lam).subtype.restrictScalars (𝓞 K)) : Set (VV K lam))) :=
        Submodule.subset_span ⟨⟨e • P, hP3⟩, hP2, rfl⟩
      have := Submodule.smul_mem _ (algebraMap (𝓞 K) K e)⁻¹ hP4
      rwa [nb_osmul, smul_smul, inv_mul_cancel₀ he', one_smul] at this

theorem nablaDeltaLattice_holds : NabDelLattice := by
  intro K _ _ ι _ n lam M hM
  exact ⟨nb_lattice (nb_comm_nab lam) M hM, nb_lattice (nb_comm_del lam) M hM⟩

end Lattice

end Formalism.L2.DIV
