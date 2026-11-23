import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAlgOfFinite

noncomputable section

namespace GlobalTheory.Mem.Col2.JetEx.VacEqPf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx

variable {D : D7} {X : Fields} (s : Seam D X)

theorem star_conj (x : D.host.E) : (letI := D.host.cmStar; star x) = D.host.conj x := by
  have := D.host.isCMField_hostE
  apply D.host.φ₀.injective
  change D.host.φ₀ (NumberField.IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

def vec {n : ℕ} (x : Sp X.E n) : Fin n → D.host.E := fun i => s.iE (x i)

theorem int_iff (z : X.E) : s.iE z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ z ∈ (algebraMap (𝓞 X.E) X.E).range := by
  have h1 : ∀ w : D.host.E, w ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ IsIntegral ℤ w := fun w =>
    (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).symm
  have h2 : ∀ w : X.E, w ∈ (algebraMap (𝓞 X.E) X.E).range ↔ IsIntegral ℤ w := fun w =>
    (IsIntegralClosure.isIntegral_iff (A := 𝓞 X.E)).symm
  rw [h1, h2]
  constructor
  · intro h
    have := map_isIntegral_int s.iE.symm.toRingHom h
    simpa using this
  · intro h
    exact map_isIntegral_int s.iE.toRingHom h

theorem vec_add {n : ℕ} (x y : Sp X.E n) : vec s (x + y) = vec s x + vec s y := by
  funext i
  simp [vec]

theorem vec_smulE {n : ℕ} (c : X.E) (x : Sp X.E n) : vec s (c • x) = s.iE c • vec s x := by
  funext i
  simp [vec]

theorem vec_smulO {n : ℕ} (r : 𝓞 X.E) (r' : 𝓞 D.host.E) (h : s.iE (r : X.E) = (r' : D.host.E)) (x : Sp X.E n) : vec s (r • x) = r' • vec s x := by
  funext i
  show s.iE ((r • x) i) = (r' • vec s x) i
  rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
  show s.iE (r : X.E) * _ = (r' : D.host.E) * _
  rw [h]
  rfl

theorem vec_span {n : ℕ} (T : Set (Sp X.E n)) {x : Sp X.E n} (hx : x ∈ Submodule.span (𝓞 X.E) T) :
    vec s x ∈ Submodule.span (𝓞 D.host.E) (vec s '' T) := by
  induction hx using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩
  | zero =>
    have : vec s (0 : Sp X.E n) = 0 := by funext i; simp [vec]
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [vec_add s]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    obtain ⟨r', hr'⟩ := (int_iff s (r : X.E)).2 ⟨r, rfl⟩
    rw [vec_smulO s r r' hr'.symm]
    exact Submodule.smul_mem _ _ hx

theorem vec_spanE {n : ℕ} (T : Set (Sp X.E n)) {x : Sp X.E n} (hx : x ∈ Submodule.span X.E T) :
    vec s x ∈ Submodule.span D.host.E (vec s '' T) := by
  induction hx using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩
  | zero =>
    have : vec s (0 : Sp X.E n) = 0 := by funext i; simp [vec]
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [vec_add s]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [vec_smulE s]; exact Submodule.smul_mem _ _ hx

theorem vec_surj {n : ℕ} (y : Fin n → D.host.E) : vec s (fun i => s.iE.symm (y i) : Sp X.E n) = y := by
  funext i
  simp [vec]

theorem mem_lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (y : Fin n → D.host.E) : y ∈ s.lat N ↔ ∃ x ∈ N, vec s x = y := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y h => exact h
    | zero => exact ⟨0, N.zero_mem, by funext i; simp [vec]⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨x', hx', rfl⟩ := hy'
      exact ⟨x + x', N.add_mem hx hx', vec_add s x x'⟩
    | smul r y _ hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨r₀, hr₀⟩ := (int_iff s (s.iE.symm (r : D.host.E))).1 ⟨r, by simp⟩
      refine ⟨r₀ • x, N.smul_mem _ hx, vec_smulO s r₀ r ?_ x⟩
      show s.iE (algebraMap (𝓞 X.E) X.E r₀) = _
      rw [hr₀]
      simp
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, hx, rfl⟩

theorem stdH_vec (hok : s.Ok) {n : ℕ} (x y : Sp X.E n) :
    (letI := D.host.cmStar; stdH D.host.E n (vec s x) (vec s y)) = s.iE (hStd X.E n x y) := by
  show ∑ i, (letI := D.host.cmStar; star (s.iE (x i))) * s.iE (y i) = s.iE (∑ i, star (x i) * y i)
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hok.2, star_conj]

theorem sd_lat (hok : s.Ok) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    (letI := D.host.cmStar; IsSDLat D.host.E n (s.lat N)) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨S, hS⟩ := hN.1.fg
    have h : s.lat N = Submodule.span (𝓞 D.host.E) (vec s '' (S : Set (Sp X.E n))) := by
      apply le_antisymm
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨x, hx, rfl⟩
        exact vec_span s _ (by rw [hS]; exact hx)
      · refine Submodule.span_mono (Set.image_mono ?_)
        rw [← hS]
        exact Submodule.subset_span
    rw [h]
    exact Submodule.fg_span (S.finite_toSet.image _)
  · rw [eq_top_iff]
    intro y _
    have h1 : (fun i => s.iE.symm (y i) : Sp X.E n) ∈ Submodule.span X.E (N : Set (Sp X.E n)) := by
      rw [hN.1.span_eq_top]; trivial
    have h2 := vec_spanE s _ h1
    rw [vec_surj s] at h2
    exact Submodule.span_mono (fun z hz => Submodule.subset_span hz) h2
  · intro y
    constructor
    · intro hy x hx
      obtain ⟨y₀, hy₀, rfl⟩ := (mem_lat s N y).1 hy
      obtain ⟨x₀, hx₀, rfl⟩ := (mem_lat s N x).1 hx
      rw [stdH_vec s hok, int_iff s]
      have h1 : y₀ ∈ dual (hStd X.E n) N := by rw [hN.2]; exact hy₀
      exact Submodule.mem_one.1 ((mem_dual N y₀).1 h1 x₀ hx₀)
    · intro h
      refine (mem_lat s N y).2 ⟨fun i => s.iE.symm (y i), ?_, vec_surj s y⟩
      have hd : IsUnimodular (hStd X.E n) N := hN.2
      unfold IsUnimodular at hd
      rw [← hd, mem_dual]
      intro x₀ hx₀
      have h1 := h (vec s x₀) ((mem_lat s N _).2 ⟨x₀, hx₀, rfl⟩)
      rw [← vec_surj s y, stdH_vec s hok, int_iff s] at h1
      exact Submodule.mem_one.2 h1

def matOf {n : ℕ} (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) : Matrix (Fin n) (Fin n) D.host.E :=
  fun i j => s.iE (γ (Pi.single j 1) i)

theorem apply_eq_sum {n : ℕ} (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (x : Sp X.E n) (i : Fin n) :
    γ x i = ∑ j, γ (Pi.single j 1) i * x j := by
  have h : x = ∑ j, x j • (Pi.single j 1 : Sp X.E n) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h, map_sum]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem matOf_mulVec {n : ℕ} (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (x : Sp X.E n) :
    (matOf s γ).mulVec (vec s x) = vec s (γ x) := by
  funext i
  show ∑ j, s.iE (γ (Pi.single j 1) i) * s.iE (x j) = s.iE (γ x i)
  rw [apply_eq_sum γ x i, map_sum]
  simp only [map_mul]

theorem smulLat_matOf {n : ℕ} (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    (letI := D.host.cmStar; SDLat.smulLat (matOf s γ) (s.lat N)) = s.lat (gmap γ N) := by
  ext y
  rw [mem_lat s]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (mem_lat s N w).1 hw
    exact ⟨γ x, ⟨x, hx, rfl⟩, (matOf_mulVec s γ x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨vec s x, (mem_lat s N _).2 ⟨x, hx, rfl⟩, matOf_mulVec s γ x⟩

theorem symm_single {n : ℕ} (γ : UF X.E n) (i k : Fin n) :
    γ.1.symm (Pi.single k 1) i = star (γ.1 (Pi.single i 1) k) := by
  have h : ∑ l, star (γ.1 (Pi.single i 1) l) * γ.1 (γ.1.symm (Pi.single k 1)) l =
      ∑ l, star ((Pi.single i 1 : Sp X.E n) l) * γ.1.symm (Pi.single k 1) l := γ.2 (Pi.single i 1) (γ.1.symm (Pi.single k 1))
  rw [LinearEquiv.apply_symm_apply] at h
  simpa [Pi.single_apply, apply_ite star] using h.symm

theorem matOf_unitary (hok : s.Ok) {n : ℕ} (γ : UF X.E n) :
    letI := D.host.cmStar
    matOf s γ.1 ∈ Matrix.unitaryGroup (Fin n) D.host.E := by
  letI := D.host.cmStar
  rw [Matrix.mem_unitaryGroup_iff']
  refine Matrix.ext fun i j => ?_
  have h1 := stdH_vec s hok (γ.1 (Pi.single i 1)) (γ.1 (Pi.single j 1))
  rw [γ.2] at h1
  have h2 : hStd X.E n (Pi.single i 1) (Pi.single j 1) = if i = j then 1 else 0 := by
    show ∑ l, star ((Pi.single i 1 : Sp X.E n) l) * (Pi.single j 1 : Sp X.E n) l = _
    simp [Pi.single_apply, apply_ite star, eq_comm]
  rw [h2] at h1
  rw [Matrix.one_apply]
  have h3 : s.iE (if i = j then 1 else 0) = if i = j then 1 else 0 := by split_ifs <;> simp
  rw [h3] at h1
  exact h1

theorem vacEq_ambOf : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), s.Ok → B.EqP χ → Even a → Even b → VacEq (ambOf s B χ cD) a b := by
  intro D X s cc δ B χ cD a b hok hE ha hb γ γ' N N' hN hN' z
  letI := D.host.cmStar
  have h := hE.1 a b ⟨s.lat N, sd_lat s hok hN⟩ ⟨s.lat N', sd_lat s hok hN'⟩ ha hb
    ⟨matOf s γ.1, matOf_unitary s hok γ⟩ ⟨matOf s γ'.1, matOf_unitary s hok γ'⟩
  have h1 := smulLat_matOf s γ.1 N
  have h2 := smulLat_matOf s γ'.1 N'
  show B.eNat χ a b (s.lat (gmap γ.1 N)) (s.lat (gmap γ'.1 N')) (fun τ => z (s.iT.symm τ)) =
    B.eNat χ a b (s.lat N) (s.lat N') (fun τ => (ambOf s B χ cD : Amb X).pullV a b γ.1 γ'.1 z (s.iT.symm τ))
  rw [← h1, ← h2]
  refine (congrFun h _).symm.trans ?_
  show B.eNat χ a b (s.lat N) (s.lat N') _ = _
  congr 1
  funext τ i j
  show ∑ l, (∑ k, star (TaylorLogMetric.embT D τ (s.iE (γ'.1 (Pi.single i 1) k))) * z (s.iT.symm τ) k l) * TaylorLogMetric.embT D τ (s.iE (γ.1 (Pi.single j 1) l)) =
    ∑ k : Fin b, ∑ l : Fin a, s.σ₀ (X.emb (s.iT.symm τ) (γ'.1.symm (Pi.single k 1) i)) * z (s.iT.symm τ) k l *
      s.σ₀ (X.emb (s.iT.symm τ) (γ.1 (Pi.single j 1) l))
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hok.1, hok.1, Equiv.apply_symm_apply, symm_single, hok.2,
    show ∀ x, TaylorLogMetric.embT D τ (D.host.conj x) = starRingEnd ℂ (TaylorLogMetric.embT D τ x) from
      D.host.conjE_apply (TaylorLogMetric.embT D τ)]
  rfl

end GlobalTheory.Mem.Col2.JetEx.VacEqPf

end
