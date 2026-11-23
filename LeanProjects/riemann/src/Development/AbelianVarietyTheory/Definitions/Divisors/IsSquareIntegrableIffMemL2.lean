import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.AutomorphicL2Unitary (LeftInv MemL2Quotient stdDom isFundamentalDomain_stdDom)
open GlobalTheory.Cusp (Cocompact constTermOn)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ContDiff

namespace GlobalTheory.UAut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def IsSm (f : GAd σ J → ℂ) : Prop :=
  ∀ (k : ℕ) (γ : Fin k → ℝ → GAd σ J), (∀ i, IsRealLine σ J (γ i)) → ∀ g,
    ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod)

variable {σ J} in

def dop (z : List (ℝ → GAd σ J) →₀ ℂ) (f : GAd σ J → ℂ) : GAd σ J → ℂ :=
  fun g => z.sum fun l c => c * l.foldr lineDer f g

def IsCentral (z : List (ℝ → GAd σ J) →₀ ℂ) : Prop :=
  (∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ) ∧
    ∀ f, IsSm σ J f → ∀ a ∈ infPts σ J, ∀ g, dop z (fun x => f (x * a)) g = dop z f (g * a)

def IsMaxCpt (K : Subgroup (GAd σ J)) : Prop :=
  Maximal (fun K' : Subgroup (GAd σ J) => K' ≤ infPts σ J ∧ IsCompact (K' : Set (GAd σ J))) K

structure IsAut (K : Subgroup (GAd σ J)) (φ : GAd σ J → ℂ) : Prop where
  mod : IsSmoothModerate σ J φ
  kfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun g => φ (g * k)))
  zfin : FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ})

structure IsAutOn (H K : Subgroup (GAd σ J)) (φ : GAd σ J → ℂ) : Prop where
  left : LeftInv H φ
  level : ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g
  cont : Continuous φ
  smooth : IsSm σ J φ
  growth : ∃ N : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
    ∃ C : ℝ, ∀ g, ‖l.foldr lineDer φ g‖ ≤ C * (height σ J g : ℝ) ^ N
  kfin : GlobalTheory.Doubling.IsKFinite K φ
  zfin : FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ})

def IsConstTerm {r : ℕ} (C : Matrix (Fin n) (Fin r) E) (φ c : GAd σ J → ℂ) : Prop :=
  ∀ (μ : Measure (unipRad σ J C)) (𝓕 : Set (unipRad σ J C)), μ.IsHaarMeasure →
    IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J C)) 𝓕 μ → μ 𝓕 = 1 →
    ∀ g, c g = ∫ u in 𝓕, φ ((u : GAd σ J) * g) ∂μ

def IsConstTermOn (N : Subgroup (GAd σ J)) (φ c : GAd σ J → ℂ) : Prop :=
  ∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf N) 𝓕 μ → μ 𝓕 = 1 →
    ∀ g, c g = ∫ u in 𝓕, φ ((u : GAd σ J) * g) ∂μ

def IsSqInt (φ : GAd σ J → ℂ) : Prop :=
  ∀ (μ : Measure (GAd σ J)) (𝓕 : Set (GAd σ J)), μ.IsHaarMeasure → IsFundamentalDomain (ratPts σ J) 𝓕 μ →
    IntegrableOn (fun g => ‖φ g‖ ^ 2) 𝓕 μ

variable {σ J} {r : ℕ} {H H' K K' N : Subgroup (GAd σ J)} {φ c c' : GAd σ J → ℂ} {C : Matrix (Fin n) (Fin r) E}

omit [NumberField E] in

theorem kfin_iff : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun g => φ (g * k))) ↔
    GlobalTheory.Doubling.IsKFinite K φ := by
  rw [show (Set.range fun k : K => fun g => φ (g * k)) = {Ψ | ∃ k ∈ K, Ψ = fun g => φ (g * k)} from
    Set.ext fun Ψ => ⟨fun ⟨k, e⟩ => ⟨k, k.2, e.symm⟩, fun ⟨k, hk, e⟩ => ⟨⟨k, hk⟩, e.symm⟩⟩]
  rfl

theorem isAut_iff_isAutOn : IsAut σ J K φ ↔ IsAutOn σ J (ratPts σ J) K φ :=
  ⟨fun h => ⟨h.mod.left, h.mod.level, h.mod.cont, h.mod.smooth, h.mod.growth, kfin_iff.1 h.kfin, h.zfin⟩,
    fun h => ⟨⟨h.left, h.level, h.cont, h.smooth, h.growth⟩, kfin_iff.2 h.kfin, h.zfin⟩⟩

theorem IsAutOn.mono (h : IsAutOn σ J H K φ) (hH : H' ≤ H) (hK : K' ≤ K) : IsAutOn σ J H' K' φ :=
  ⟨fun γ hγ => h.left γ (hH hγ), h.level, h.cont, h.smooth, h.growth,
    let ⟨W, hW, e⟩ := GlobalTheory.Doubling.isKFinite_iff.1 h.kfin
    GlobalTheory.Doubling.isKFinite_iff.2 ⟨W, hW, fun k hk => e k (hK hk)⟩, h.zfin⟩

omit [NumberField E] in

theorem foldr_lineDer_char (hφ : ∀ g h, φ (g * h) = φ g * φ h) (a : ℂ) (l : List (ℝ → GAd σ J)) :
    ∃ b : ℂ, l.foldr lineDer (a • φ) = b • φ := by
  induction l with
  | nil => exact ⟨a, rfl⟩
  | cons γ l ih =>
    obtain ⟨b, h⟩ := ih
    refine ⟨b * deriv (fun t => φ (γ t)) 0, ?_⟩
    rw [List.foldr_cons, h]
    funext g
    simp only [lineDer, Pi.smul_apply, smul_eq_mul, hφ, ← mul_assoc, deriv_const_mul_field']
    ring

theorem isAut_of_char (K : Subgroup (GAd σ J)) (hφ : ∀ g h, φ (g * h) = φ g * φ h) (a : ℂ)
    (hm : IsSmoothModerate σ J (a • φ)) : IsAut σ J K (a • φ) := by
  refine ⟨hm, ?_, ?_⟩ <;> refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
  · rintro _ ⟨k, rfl⟩
    exact Submodule.mem_span_singleton.2 ⟨a * φ k, funext fun g => by simp only [Pi.smul_apply, smul_eq_mul, hφ]; ring⟩
  · rintro _ ⟨z, -, rfl⟩
    choose b hb using foldr_lineDer_char hφ a
    exact Submodule.mem_span_singleton.2 ⟨z.sum fun l x => x * b l, funext fun g => by
      simp [dop, hb, Finsupp.sum, Finset.sum_mul, mul_assoc]⟩

variable (σ J) in

theorem isAut_const (K : Subgroup (GAd σ J)) (a : ℂ) : IsAut σ J K fun _ => a := by
  have e : (fun _ => a) = a • fun _ : GAd σ J => (1 : ℂ) := funext fun _ => by simp
  exact e ▸ isAut_of_char K (by simp) a (e ▸ isSmoothModerate_const σ J a)

variable (σ J) in

theorem isAutOn_const (H K : Subgroup (GAd σ J)) (a : ℂ) : IsAutOn σ J H K fun _ => a :=
  { isAut_iff_isAutOn.1 (isAut_const σ J K a) with left := fun _ _ _ => rfl }

example : IsCentral σ J (Finsupp.single [] 1) :=
  ⟨by simp, fun f _ a _ g => by simp [dop]⟩

omit [NumberField E] in

theorem isMaxCpt_infPts (h : IsCompact (infPts σ J : Set (GAd σ J))) : IsMaxCpt σ J (infPts σ J) :=
  ⟨⟨le_rfl, h⟩, fun _ hK _ => hK.1⟩

theorem le_one_of_pow_mul_le {t a M : ℝ} (ha : 0 < a) (h : ∀ k : ℕ, t ^ k * a ≤ M) : t ≤ 1 := by
  by_contra ht
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (not_le.1 ht)).atTop_mul_const ha).eventually_gt_atTop M |>.exists
  exact hk.not_ge (h k)

open scoped ComplexOrder in

theorem eq_one_of_powers_compact {b Q : Matrix (Fin n) (Fin n) ℂ} {S : Set (Matrix (Fin n) (Fin n) ℂ)} (hS : IsCompact S)
    (hQ : Q * (bᴴ * b) = 1) (h1 : ∀ k : ℕ, (bᴴ * b) ^ k ∈ S) (h2 : ∀ k : ℕ, Q ^ k ∈ S) : bᴴ * b = 1 := by
  have hP := Matrix.posSemidef_conjTranspose_mul_self b
  have key : ∀ (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (v : Fin n → ℂ), (∀ k : ℕ, A ^ k ∈ S) → v ≠ 0 → A *ᵥ v = t • v →
      t ≤ 1 := fun A t v hA hv e => by
    obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn (f := fun X => X *ᵥ v)
      (continuous_id.matrix_mulVec continuous_const).continuousOn
    have hk : ∀ k : ℕ, A ^ k *ᵥ v = t ^ k • v := fun k => by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
    refine (le_abs_self t).trans (le_one_of_pow_mul_le (M := M) (norm_pos_iff.2 hv) fun k => ?_)
    have := hM _ (hA k)
    rwa [hk, norm_smul, norm_pow, Real.norm_eq_abs] at this
  have hev : ∀ j, hP.1.eigenvalues j = 1 := fun j => by
    have e := hP.1.mulVec_eigenvectorBasis j
    have hv : (hP.1.eigenvectorBasis j).ofLp ≠ 0 := fun h =>
      hP.1.eigenvectorBasis.orthonormal.ne_zero j ((WithLp.ofLp_eq_zero 2).1 h)
    have e2 := congrArg (Q *ᵥ ·) e
    simp only [Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec, Matrix.mulVec_smul] at e2
    have h0 : hP.1.eigenvalues j ≠ 0 := fun h => hv (by rw [e2, h, zero_smul])
    have hpos := lt_of_le_of_ne (hP.eigenvalues_nonneg j) h0.symm
    have e3 : Q *ᵥ (hP.1.eigenvectorBasis j).ofLp = (hP.1.eigenvalues j)⁻¹ • (hP.1.eigenvectorBasis j).ofLp := by
      conv_rhs => rw [e2, inv_smul_smul₀ h0]
    exact le_antisymm (key _ _ _ h1 hv e) ((inv_le_one₀ hpos).1 (key _ _ _ h2 hv e3))
  rw [hP.1.spectral_theorem, show hP.1.eigenvalues = fun _ => 1 from funext hev]
  simp [Function.comp_def]

theorem conj_mem_UJ {R : Type} [CommRing R] {s : R →+* R} {A D : Matrix (Fin n) (Fin n) R} {c : GL (Fin n) R}
    (hc : Formalism.UG.cT s c.1 * A * c.1 = D) (g : GL (Fin n) R) : c⁻¹ * g * c ∈ Formalism.UG.UJ s D ↔ g ∈ Formalism.UG.UJ s A := by
  have h1 : Formalism.UG.cT s (c⁻¹).1 * Formalism.UG.cT s c.1 = 1 := by rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
  have e : Formalism.UG.cT s (c⁻¹ * g * c).1 * D * (c⁻¹ * g * c).1 = Formalism.UG.cT s c.1 * (Formalism.UG.cT s g.1 * A * g.1) * c.1 := by
    rw [← hc]
    simp only [Units.val_mul, Formalism.UG.cT_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
    rw [← Matrix.mul_assoc (Formalism.UG.cT s (c⁻¹).1), h1, Matrix.one_mul]
  change Formalism.UG.cT s _ * D * _ = D ↔ Formalism.UG.cT s g.1 * A * g.1 = A
  rw [e, ← hc]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have := congrArg (fun X => Formalism.UG.cT s (c⁻¹).1 * X * (c⁻¹).1) h
  simpa only [← Matrix.mul_assoc, h1, Matrix.one_mul, Units.mul_inv_cancel_right] using this

variable (σ J) in

def majCpt (c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)) : Subgroup (GAd σ J) :=
  infPts σ J ⊓ ⨅ w, (stabArch σ J w (c w)).comap (projArch σ J w)

theorem mem_majCpt {c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)} {g : GAd σ J} :
    g ∈ majCpt σ J c ↔ g ∈ infPts σ J ∧ ∀ w, projArch σ J w g ∈ stabArch σ J w (c w) := by
  simp [majCpt, Subgroup.mem_iInf]

theorem isMaxCpt_majCpt (h : IsCMExt F E σ) {c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)}
    (hc : ∀ w, ∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) (c w).1 * JR w.Completion J * (c w).1 =
      Matrix.diagonal fun i => if ε i then 1 else -1) : IsMaxCpt σ J (majCpt σ J c) := by
  refine ⟨⟨inf_le_left, ?_⟩, fun K' hK' hle g hg => mem_majCpt.2 ⟨hK'.1 hg, fun w => ?_⟩⟩
  · convert (isCompact_univ_pi fun w => Frames.isCompact_stabArch h J w (c w)).image
      ((continuous_ofInf σ J).comp (continuous_embArchPi σ J)) using 1
    ext g
    refine ⟨fun hg => ⟨fun w => projArch σ J w g, fun w _ => (mem_majCpt.1 hg).2 w, GAd_ext σ J (fun w => by simp) fun v => ?_⟩, ?_⟩
    · simp [mem_infPts_iff_forall.1 hg.1 v]
    · rintro ⟨x, hx, rfl⟩
      exact mem_majCpt.2 ⟨mem_infPts.2 (projFin_ofInf _ _ _), fun w => by simpa using hx w trivial⟩
  obtain ⟨ε, hε⟩ := hc w
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  set D : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E) := Matrix.diagonal fun i => if ε i then 1 else -1 with hD
  have hDD : D * D = 1 := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; split_ifs <;> simp
  have hcD : Formalism.UG.cT (sigR _ σ) D = D := by
    rw [hD, Formalism.UG.cT, diagonal_map (map_zero _), diagonal_transpose]
    congr 1; funext i; split_ifs <;> simp only [map_one, map_neg]
  let u : GL (Fin n) (w.Completion ⊗[F] E) := ⟨D, D, hDD, hDD⟩
  have hu : (c w)⁻¹ * (c w * u * (c w)⁻¹) * c w = u := by group
  let s₀ : GArch σ J w := ⟨c w * u * (c w)⁻¹, (conj_mem_UJ hε _).1 (hu.symm ▸ show _ * D * D = D by rw [hcD, hDD, one_mul])⟩
  have hs : embArch σ J w s₀ ∈ K' := hle (mem_majCpt.2 ⟨mem_infPts.2 (projFin_embArch _ _ _ _), fun v => by
    by_cases e : v = w
    · subst e
      rw [projArch_embArch_self, mem_stabArch]
      exact hu.symm ▸ show _ * 1 * D = 1 by rw [hcD, mul_one, hDD]
    · rw [projArch_embArch_ne σ J e]; exact one_mem _⟩)
  let m : GAd σ J →* GL (Fin n) (w.Completion ⊗[F] E) :=
    (MulAut.conj (c w)⁻¹).toMonoidHom.comp ((matHom _ σ J).comp (projArch σ J w))
  have hm : ∀ x, m x = (c w)⁻¹ * matHom _ σ J (projArch σ J w x) * c w := fun x => by simp [m]
  let f : GAd σ J →* Matrix (Fin n) (Fin n) ℂ := (infEmb τ).mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp m)
  have hf : Continuous f := by
    have : IsTopologicalRing (w.Completion ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
    have e : f = fun x => (((c w)⁻¹).1 * (matHom _ σ J (projArch σ J w x)).1 * (c w).1).map (infEmb τ) :=
      funext fun x => congrArg (fun y : GL (Fin n) _ => y.1.map (infEmb τ)) (hm x)
    rw [e]
    exact ((continuous_const.matrix_mul (Units.continuous_val.comp ((isEmbedding_matHom _ σ J).continuous.comp
      (continuous_projArch σ J w)))).matrix_mul continuous_const).matrix_map (GlobalTheory.Orb.continuous_infEmb τ)
  have h1 : Formalism.UG.cT (sigR _ σ) (m g).1 * D * (m g).1 = D := hm g ▸ (conj_mem_UJ hε _).2 (projArch σ J w g).2
  let p := embArch σ J w s₀ * g⁻¹ * embArch σ J w s₀ * g
  have hp : p ∈ K' := mul_mem (mul_mem (mul_mem hs (inv_mem hg)) hs) hg
  have h2 : (m p).1 = Formalism.UG.cT (sigR _ σ) (m g).1 * (m g).1 := by
    have e : m (embArch σ J w s₀) = u := by rw [hm, projArch_embArch_self]; exact hu
    simp only [p, map_mul, map_inv, e, Units.val_mul]
    congr 1
    have e2 : D * ((m g)⁻¹).1 = Formalism.UG.cT (sigR _ σ) (m g).1 * D := by
      conv_lhs => rw [← h1, Units.mul_inv_cancel_right]
    exact (congrArg (· * D) e2).trans (by rw [Matrix.mul_assoc, hDD, Matrix.mul_one])
  have h3 : f p = (f g)ᴴ * f g := by
    change (m p).1.map (infEmb τ) = ((m g).1.map (infEmb τ))ᴴ * (m g).1.map (infEmb τ)
    rw [h2, Matrix.map_mul, Frames.map_cT_sigR h]
  have h4 : f p = 1 := h3 ▸ eq_one_of_powers_compact (Q := f p⁻¹) (hK'.2.image hf)
    (by rw [← h3, ← map_mul, inv_mul_cancel, map_one]) (fun k => ⟨p ^ k, pow_mem hp k, by rw [map_pow, h3]⟩)
    fun k => ⟨p⁻¹ ^ k, pow_mem (inv_mem hp) k, map_pow _ _ _⟩
  rw [mem_stabArch, ← hm]
  change Formalism.UG.cT _ (m g).1 * 1 * (m g).1 = 1
  rw [mul_one, ← h2]
  exact Matrix.map_injective (infEmb_bijective h τ).1 (h4.trans (Matrix.map_one _ (map_zero _) (map_one _)).symm)

theorem exists_isMaxCpt (h : IsCMExt F E σ) (hJ : IsHermND σ J) : ∃ K, IsMaxCpt σ J K := by
  choose c ε hc using Frames.exists_arch_frame h hJ
  exact ⟨_, isMaxCpt_majCpt h fun w => ⟨ε w, hc w⟩⟩

example (ξ : E) (hξ : σ ξ = -ξ) : ∃ g ∈ ratPts σ !![0, 1; 1, 0] ⊓
    unipFlag σ !![0, 1; 1, 0] (!![1; 0] : Matrix (Fin 2) (Fin 1) E) fun _ => 0,
      (matHom _ σ _ g).1 = adMat F !![1, ξ; 0, 1] := by
  let γ : GRat σ (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) := ⟨⟨!![1, ξ; 0, 1], !![1, -ξ; 0, 1], by simp [one_fin_two],
    by simp [one_fin_two]⟩, show _ * _ * _ = _ by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Formalism.UG.cT, Matrix.mul_apply, Fin.sum_univ_two, hξ]⟩
  have e : (matHom _ σ _ (ratEmb σ _ γ)).1 = adMat F !![1, ξ; 0, 1] := rfl
  refine ⟨ratEmb σ _ γ, ⟨range_ratEmb σ _ ▸ ⟨γ, rfl⟩, Subgroup.subset_closure ⟨fun i => ⟨0, fun _ _ => rfl, ?_⟩,
    fun x _ => ⟨fun _ => inclR (AF F) (ξ * x 1), ?_⟩⟩⟩, e⟩ <;> rw [e] <;> funext k <;> fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Subsingleton.elim _ (0 : Fin 1)]

omit [NumberField E] in

theorem isConstTerm_iff : IsConstTerm σ J C φ c ↔ IsConstTermOn σ J (unipRad σ J C) φ c := Iff.rfl

theorem isConstTerm_iff_unipFlag : IsConstTerm σ J C φ c ↔ IsConstTermOn σ J (unipFlag σ J C fun _ => 0) φ c := by
  rw [unipFlag_const]; rfl

omit [NumberField E] in

theorem isConstTermOn_const (N : Subgroup (GAd σ J)) (a : ℂ) : IsConstTermOn σ J N (fun _ => a) fun _ => a :=
  fun μ 𝓕 _ _ h _ => by simp [Measure.real, h]

theorem isConstTermOn_constTermOn [LocallyCompactSpace N] (hφ : LeftInv (ratPts σ J ⊓ N) φ) :
    IsConstTermOn σ J N φ (constTermOn (ratPts σ J) N φ) := fun μ 𝓕 _ h h1 g => by
  have hl : LeftInv ((ratPts σ J).subgroupOf N) fun u : N => φ (u * g) := fun γ hγ u => by
    simp only [Subgroup.coe_mul, mul_assoc]; exact hφ _ ⟨hγ, γ.2⟩ _
  rw [constTermOn, GlobalTheory.Cusp.probMeasure_eq μ, integral_smul_measure, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h,
    GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h, h1, inv_one, ENNReal.toReal_one, one_smul]
  exact integral_congr_ae (.of_forall hl.descend_mk)

theorem exists_mass_one [LocallyCompactSpace N] (hc : Cocompact (ratPts σ J) N) : ∃ (μ : Measure N) (𝓕 : Set N),
    μ.IsHaarMeasure ∧ IsFundamentalDomain ((ratPts σ J).subgroupOf N) 𝓕 μ ∧ μ 𝓕 = 1 := by
  have h := isFundamentalDomain_stdDom ((ratPts σ J).subgroupOf N) (Measure.haar : Measure N)
  have h0 := h.measure_ne_zero (NeZero.ne _)
  have h1 := hc.measure_ne_top h
  exact ⟨(Measure.haar (stdDom ((ratPts σ J).subgroupOf N)))⁻¹ • Measure.haar, _,
    Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0),
    h.mono Measure.smul_absolutelyContinuous, by simp [ENNReal.inv_mul_cancel h0 h1]⟩

theorem IsConstTermOn.unique [LocallyCompactSpace N] (hc : Cocompact (ratPts σ J) N) (h : IsConstTermOn σ J N φ c)
    (h' : IsConstTermOn σ J N φ c') : c = c' :=
  let ⟨μ, 𝓕, h1, h2, h3⟩ := exists_mass_one hc
  funext fun g => (h μ 𝓕 h1 h2 h3 g).trans (h' μ 𝓕 h1 h2 h3 g).symm

theorem isConstTermOn_iff [LocallyCompactSpace N] (hc : Cocompact (ratPts σ J) N) (hφ : LeftInv (ratPts σ J ⊓ N) φ) :
    IsConstTermOn σ J N φ c ↔ c = constTermOn (ratPts σ J) N φ :=
  ⟨fun h => h.unique hc (isConstTermOn_constTermOn hφ), fun h => h ▸ isConstTermOn_constTermOn hφ⟩

instance discreteTopology_ratPts_inf (P : Subgroup (GAd σ J)) : DiscreteTopology (ratPts σ J ⊓ P : Subgroup (GAd σ J)) :=
  .of_continuous_injective (f := Subgroup.inclusion (inf_le_left : ratPts σ J ⊓ P ≤ ratPts σ J))
    (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective _)

section Flag

variable (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hC : IsIsoCols σ J C)
include h hJ hC

theorem existsUnique_isConstTermOn (d : Fin r → ℕ) (hφ : LeftInv (ratPts σ J ⊓ unipFlag σ J C d) φ) :
    ∃! c, IsConstTermOn σ J (unipFlag σ J C d) φ c :=
  haveI := locallyCompact_unipFlag hJ (sigma_sigma h) hC d
  ⟨_, isConstTermOn_constTermOn hφ, fun _ hc =>
    (isConstTermOn_iff (cocompact_unipFlag hJ (sigma_sigma h) hC d) hφ).1 hc⟩

theorem locallyCompact_unipRad : LocallyCompactSpace (unipRad σ J C) :=
  unipFlag_const (σ := σ) (J := J) C 0 ▸ locallyCompact_unipFlag hJ (sigma_sigma h) hC _

theorem cocompact_unipRad : Cocompact (ratPts σ J) (unipRad σ J C) :=
  unipFlag_const (σ := σ) (J := J) C 0 ▸ cocompact_unipFlag hJ (sigma_sigma h) hC _

theorem existsUnique_isConstTerm (hφ : LeftInv (ratPts σ J) φ) : ∃! c, IsConstTerm σ J C φ c := by
  simp only [isConstTerm_iff_unipFlag]
  exact existsUnique_isConstTermOn h hJ hC _ fun γ hγ => hφ γ hγ.1

theorem IsConstTermOn.eq_constTermOn_par {d : Fin r → ℕ} (hc : IsConstTermOn σ J (unipFlag σ J C d) φ c)
    (hφ : LeftInv (ratPts σ J ⊓ parFlag σ J C d) φ) [LocallyCompactSpace (unipFlag σ J C d)] :
    Cocompact (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) ∧
      c = constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) φ := by
  have hco := cocompact_unipFlag hJ (sigma_sigma h) hC d
  have e : (ratPts σ J ⊓ parFlag σ J C d).subgroupOf (unipFlag σ J C d) = (ratPts σ J).subgroupOf (unipFlag σ J C d) :=
    Subgroup.ext fun u => and_iff_left (unipFlag_le_parFlag hJ (sigma_sigma h) hC d u.2)
  obtain ⟨μ, 𝓕, h1, h2, h3⟩ := exists_mass_one hco
  refine ⟨by rw [Cocompact, e]; exact hco, funext fun g => (hc μ 𝓕 h1 h2 h3 g).trans ?_⟩
  exact (GlobalTheory.Cusp.constTermOn_eq_of_measure_eq_one (e ▸ h2) h3 hφ g).symm

theorem IsConstTermOn.leftInv {d : Fin r → ℕ} (hc : IsConstTermOn σ J (unipFlag σ J C d) φ c)
    (hφ : LeftInv (ratPts σ J ⊓ parFlag σ J C d) φ) : LeftInv (leftGrp σ J C d) c := by
  haveI := locallyCompact_unipFlag hJ (sigma_sigma h) hC d
  obtain ⟨hco, e⟩ := hc.eq_constTermOn_par h hJ hC hφ
  let S : Subgroup (GAd σ J) := MulAction.stabilizer (GAd σ J)ᵈᵐᵃ c |>.comap ((MulEquiv.inv' (GAd σ J)).toMonoidHom)
  have hS : ∀ γ, γ ∈ S ↔ ∀ g, c (γ⁻¹ * g) = c g := fun γ => funext_iff
  have : leftGrp σ J C d ≤ S := sup_le (fun u hu => (hS u).2 (e ▸ hco.constTermOn_mul_left hφ (inv_mem hu)))
    fun γ hγ => (hS γ).2 (e ▸ GlobalTheory.Cusp.constTermOn_mul_left_of_normalizer hφ (inv_mem hγ) fun u =>
      ⟨conj_mem_unipFlag hJ (sigma_sigma h) hC d (inv_mem hγ.2), fun hu => by
        simpa [mul_assoc] using conj_mem_unipFlag hJ (sigma_sigma h) hC d hγ.2 hu⟩)
  exact fun γ hγ g => by simpa using (hS _).1 (this (inv_mem hγ)) g

theorem IsConstTermOn.continuous {d : Fin r → ℕ} (hc : IsConstTermOn σ J (unipFlag σ J C d) φ c)
    (hφ : LeftInv (ratPts σ J ⊓ parFlag σ J C d) φ) (hφc : Continuous φ) : Continuous c := by
  haveI := locallyCompact_unipFlag hJ (sigma_sigma h) hC d
  obtain ⟨hco, e⟩ := hc.eq_constTermOn_par h hJ hC hφ
  exact e ▸ hco.continuous_constTermOn hφ hφc

end Flag

omit [NumberField F] [NumberField E] in

theorem isIsoCols_of_isWittFrame {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ J X Y) (hσ : ∀ x, σ (σ x) = x)
    (hJ : IsHermND σ J) {k : ℕ} (hk : k ≤ r) : IsIsoCols σ J (X.submatrix id (Fin.castLE hk)) := by
  have yx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (Formalism.UG.cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, show Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) X) = X from
      Matrix.ext fun i j => hσ _, cT_form hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  have hX : LinearIndependent E Xᵀ := Matrix.mulVec_injective_iff.1 fun a b e => by
    simpa only [Matrix.mulVec_mulVec, yx, Matrix.one_mulVec] using congrArg ((Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ ·) e
  exact ⟨hX.comp _ (Fin.castLE_injective hk), Matrix.ext fun i j => congrFun (congrFun hW.xx _) _⟩

example (h : IsCMExt F E σ) (a : ℂ) (c : GAd σ !![0, 1; 1, 0] → ℂ) :
    IsConstTerm σ !![0, 1; 1, 0] ((!![1; 0] : Matrix (Fin 2) (Fin 1) E).submatrix id (Fin.castLE le_rfl)) (fun _ => a) c ↔
      c = fun _ => a := by
  have hJ : IsHermND σ (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) :=
    ⟨fun i j => by fin_cases i <;> fin_cases j <;> simp, by simp⟩
  exact ⟨fun hc => (existsUnique_isConstTerm h hJ (isIsoCols_of_isWittFrame isWittFrame_plane (sigma_sigma h) hJ le_rfl)
    fun _ _ _ => rfl).unique hc (isConstTermOn_const _ a), fun e => e ▸ isConstTermOn_const _ a⟩

example : ∃ (μ : Measure (GAd σ J)) (𝓕 : Set (GAd σ J)), μ.IsHaarMeasure ∧ IsFundamentalDomain (ratPts σ J) 𝓕 μ :=
  ⟨Measure.haar, _, inferInstance, isFundamentalDomain_stdDom _ _⟩

end GlobalTheory.UAut

end
