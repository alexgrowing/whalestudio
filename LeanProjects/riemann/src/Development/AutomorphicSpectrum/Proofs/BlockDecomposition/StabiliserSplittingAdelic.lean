import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActWOneApply
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsetFinTwoEqCases
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleQuotientCompactRepresentatives

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Struct

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

section Cont

theorem continuous_rowv {A X : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace X] {M : ℕ} {s : A →+* A} (hs : Continuous s) (J : Matrix (Fin M) (Fin M) A)
    {w : X → Fin M → A} (hw : Continuous w) (b : Fin M) : Continuous fun x => rowv s J (w x) b :=
  continuous_finset_sum _ fun a _ =>
    (hs.comp ((continuous_apply a).comp hw)).mul continuous_const

theorem continuous_hv {A X : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace X] {M : ℕ} {s : A →+* A} (hs : Continuous s) (J : Matrix (Fin M) (Fin M) A)
    {w v : X → Fin M → A} (hw : Continuous w) (hv' : Continuous v) :
    Continuous fun x => hv s J (w x) (v x) :=
  continuous_finset_sum _ fun b _ =>
    (continuous_rowv hs J hw b).mul ((continuous_apply b).comp hv')

theorem continuous_nM {A X : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace X] {M : ℕ} {s : A →+* A} (hs : Continuous s) (J : Matrix (Fin M) (Fin M) A)
    {w : X → Fin M → A} {z : X → A} (hw : Continuous w) (hz : Continuous z) :
    Continuous fun x => nM s J (w x) (z x) := by
  refine continuous_mat2 (f := fun x => nM s J (w x) (z x)) continuous_const hz continuous_const
    continuous_const (fun j => (continuous_rowv hs J hw j).neg) (fun _ => continuous_const)
    (fun _ => continuous_const) (fun i => show Continuous fun x => w x i from (continuous_apply i).comp hw)
    (fun _ _ => continuous_const)

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem continuous_stab_iff {X : Type} [TopologicalSpace X] {f : X → stabilizer₂ R σ J} :
    Continuous f ↔ Continuous (fun x => matP R σ J (f x)) ∧
      Continuous (fun x => matP R σ J (f x)⁻¹) := by
  have h : Continuous f ↔ Continuous (fun x => ((f x : stabilizer₂ R σ J) : HA R σ (hypOne J))) :=
    Topology.IsInducing.subtypeVal.continuous_iff
  rw [h, continuous_HA_iff]
  rfl

variable {R σ J}

theorem lift_hz {w : Fin M → E} {z : E} (hz : z + σ z + hv (σ : E →+* E) J w w = 0) :
    inclR R z + sigR R σ (inclR R z) +
      hv (sigR R σ) (JR R J) (fun i => inclR R (w i)) (fun i => inclR R (w i)) = 0 := by
  have h := congrArg (inclR (F := F) (E := E) R) hz
  rw [map_add, map_add, hv_map (inclR R) (s := (σ : E →+* E)) (s' := sigR R σ)
    (fun x => (sigR_incl R σ x).symm), map_zero] at h
  rw [sigR_incl]
  exact h

theorem exists_move_w [CharZero E] (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j)
    {C : Set (R ⊗[F] E)} (hCc : ∀ a, ∃ α : E, a - inclR R α ∈ C)
    (w : Fin M → R ⊗[F] E) (z : R ⊗[F] E) (hz : z + sigR R σ z + hv (sigR R σ) (JR R J) w w = 0) :
    ∃ γ ∈ ratP R σ J, γ ∈ (piR R σ J).ker ∧ ∃ (w₁ : Fin M → R ⊗[F] E) (z₁ : R ⊗[F] E)
      (hz₁ : z₁ + sigR R σ z₁ + hv (sigR R σ) (JR R J) w₁ w₁ = 0),
      γ * nP hσ hJ w z hz = nP hσ hJ w₁ z₁ hz₁ ∧ ∀ i, w₁ i ∈ C := by
  choose α hα using fun i => hCc (w i)
  have hE2 : (2⁻¹ : E) + 2⁻¹ = 1 := by norm_num
  have hEs : (σ : E →+* E) (2⁻¹ : E) = 2⁻¹ := by
    rw [map_inv₀, map_ofNat]
  have hz₀ := z_half (s := (σ : E →+* E)) (J := J) hσ hJ hE2 hEs (t := 0) (by simp) (-α)
  have hz₀' := lift_hz (R := R) hz₀
  have hk₀ := nP_mem_ker (R := R) hσ hJ _ _ hz₀'
  have hm₁ := mul_mem hk₀ (nP_mem_ker hσ hJ w z hz)
  obtain ⟨hz₁, e₁⟩ := nM_form hσ hJ hm₁ (by rw [toMatrix_mul₂, toMatrix_unipotent, toMatrix_unipotent, nM_mul])
  refine ⟨_, nP_mem_ratP hσ hJ _ _ hz₀ hz₀', hk₀, _, _, hz₁, e₁, fun i => ?_⟩
  have h : ((fun i => inclR (F := F) R ((-α) i)) + w) i = w i - inclR R (α i) := by
    change inclR R ((-α) i) + w i = _
    rw [Pi.neg_apply, map_neg]
    ring
  rw [h]
  exact hα i

theorem exists_move_alt [CharZero E] (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j)
    (h2 : Module.finrank F E = 2) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    {C₀ : Set R} (hC₀c : ∀ a, ∃ x : F, a - algebraMap F R x ∈ C₀)
    (w : Fin M → R ⊗[F] E) (z : R ⊗[F] E) (hz : z + sigR R σ z + hv (sigR R σ) (JR R J) w w = 0) :
    ∃ γ ∈ ratP R σ J, γ ∈ (piR R σ J).ker ∧ ∃ c ∈ C₀, ∀ hz₁,
      γ * nP hσ hJ w z hz =
        nP hσ hJ w (c ⊗ₜ[F] δ - halfR F E R * hv (sigR R σ) (JR R J) w w) hz₁ := by
  have hsR := HaarCoord.sigR_sigR R hσ
  have hJR := JR_herm R σ J hJ
  have hH := halfR_add (F := F) (E := E) R
  have hHs := sigR_halfR (F := F) (E := E) R σ
  have hskt : sigR R σ (z + halfR F E R * hv (sigR R σ) (JR R J) w w) =
      -(z + halfR F E R * hv (sigR R σ) (JR R J) w w) := by
    rw [map_add, map_mul, hHs, s_hv hsR hJR]
    linear_combination hz + (hv (sigR R σ) (JR R J) w w) * hH
  obtain ⟨b, hb⟩ := eq_tmul_of_skew R h2 hδ hσδ hskt
  obtain ⟨x, hx⟩ := hC₀c b
  have hz₂ : -(x • δ) + σ (-(x • δ)) + hv (σ : E →+* E) J 0 0 = 0 := by
    have : hv (σ : E →+* E) J 0 0 = 0 := by simp [hv, rowv]
    rw [this, map_neg, Algebra.smul_def, map_mul, AlgHom.commutes, hσδ]
    ring
  have hz₂' := lift_hz (R := R) hz₂
  refine ⟨_, nP_mem_ratP hσ hJ _ _ hz₂ hz₂', nP_mem_ker hσ hJ _ _ hz₂', _, hx, fun hz₁ => ?_⟩
  apply stabilizer_ext
  rw [toMatrix_mul₂, toMatrix_unipotent, toMatrix_unipotent, toMatrix_unipotent, nM_mul]
  have h0 : (fun i => inclR (F := F) R ((0 : Fin M → E) i)) = 0 := by
    funext i
    simp
  have hv0 : hv (sigR R σ) (JR R J) (0 : Fin M → R ⊗[F] E) w = 0 := by simp [hv, rowv]
  have hx' : inclR R (x • δ) = (algebraMap F R x) ⊗ₜ[F] δ := by
    change (1 : R) ⊗ₜ[F] (x • δ) = _
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]
  rw [h0, hv0, zero_add, map_neg, hx', TensorProduct.sub_tmul, ← hb]
  congr 1
  ring

theorem exists_cover [CharZero E] [IsTopologicalRing (R ⊗[F] E)] [ContinuousSMul R (R ⊗[F] E)]
    (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (h2 : Module.finrank F E = 2)
    {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ) (hsc : Continuous (sigR R σ))
    {C : Set (R ⊗[F] E)} (hC : IsCompact C) (hCc : ∀ a, ∃ α : E, a - inclR R α ∈ C)
    {C₀ : Set R} (hC₀ : IsCompact C₀) (hC₀c : ∀ a, ∃ x : F, a - algebraMap F R x ∈ C₀) :
    ∃ K : Set (stabilizer₂ R σ J), IsCompact K ∧ ∀ m ∈ (piR R σ J).ker,
      ∃ γ ∈ ratP R σ J, piR R σ J γ = 1 ∧ γ * m ∈ K := by
  have hsR := HaarCoord.sigR_sigR R hσ
  have hJR := JR_herm R σ J hJ
  have hH := halfR_add (F := F) (E := E) R
  have hHs := sigR_halfR (F := F) (E := E) R σ
  have hskew : ∀ c : R, sigR R σ (c ⊗ₜ[F] δ) = -(c ⊗ₜ[F] δ) := fun c => by
    rw [HaarCoord.sigR_tmul, hσδ, TensorProduct.tmul_neg]
  let f : (Fin M → R ⊗[F] E) × R → stabilizer₂ R σ J := fun q =>
    nP hσ hJ q.1 (q.2 ⊗ₜ[F] δ - halfR F E R * hv (sigR R σ) (JR R J) q.1 q.1)
      (z_half hsR hJR hH hHs (hskew q.2) q.1)
  have hfst : Continuous fun q : (Fin M → R ⊗[F] E) × R => q.1 := continuous_fst
  have hcz : Continuous fun q : (Fin M → R ⊗[F] E) × R =>
      q.2 ⊗ₜ[F] δ - halfR F E R * hv (sigR R σ) (JR R J) q.1 q.1 := by
    have h1 : Continuous fun q : (Fin M → R ⊗[F] E) × R => q.2 ⊗ₜ[F] δ := by
      have e : (fun q : (Fin M → R ⊗[F] E) × R => q.2 ⊗ₜ[F] δ) =
          fun q => q.2 • ((1 : R) ⊗ₜ[F] δ) := by
        funext q
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e]
      exact (continuous_snd : Continuous fun q : (Fin M → R ⊗[F] E) × R => q.2).smul
        (continuous_const (y := (1 : R) ⊗ₜ[F] δ))
    have h3 : Continuous fun q : (Fin M → R ⊗[F] E) × R => hv (sigR R σ) (JR R J) q.1 q.1 :=
      continuous_hv hsc _ hfst hfst
    exact h1.sub (continuous_const.mul h3)
  have hf : Continuous f := by
    rw [continuous_stab_iff]
    exact ⟨continuous_nM hsc _ hfst hcz, continuous_nM hsc _ hfst.neg (hsc.comp hcz)⟩
  refine ⟨f '' ((Set.univ.pi fun _ => C) ×ˢ C₀),
    ((isCompact_univ_pi fun _ => hC).prod hC₀).image hf, fun m hm => ?_⟩
  obtain ⟨w, z, hz, rfl⟩ := exists_nP hσ hJ hm
  obtain ⟨γ₀, hr₀, hk₀, w₁, z₁, hz₁, e₁, hw₁⟩ := exists_move_w hσ hJ hCc w z hz
  obtain ⟨γ₁, hr₁, hk₁, c, hc, e₂⟩ := exists_move_alt hσ hJ h2 hδ hσδ hC₀c w₁ z₁ hz₁
  refine ⟨γ₁ * γ₀, mul_mem hr₁ hr₀, by
    rw [map_mul, MonoidHom.mem_ker.1 hk₀, MonoidHom.mem_ker.1 hk₁, mul_one], ?_⟩
  refine ⟨(w₁, c), ⟨fun i _ => hw₁ i, hc⟩, ?_⟩
  rw [mul_assoc, e₁, e₂]

end Cont

section Surj

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem exists_left_inv {k : ℕ} (hdet : J.det ≠ 0) (Y : Fin k → Fin M → E)
    (hY : LinearIndependent E Y) :
    ∃ C : Matrix (Fin k) (Fin M) E, ∀ j, C *ᵥ (J *ᵥ Y j) = Pi.single j 1 := by
  classical
  have hinj := linearIndependent_iff_injective_fintypeLinearCombination.1 hY
  obtain ⟨g, hg⟩ := (Fintype.linearCombination E Y).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g * J⁻¹, fun j => ?_⟩
  have hu : IsUnit J.det := isUnit_iff_ne_zero.2 hdet
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one,
    LinearMap.toMatrix'_mulVec]
  have h := LinearMap.congr_fun hg (Pi.single j 1)
  simpa [Fintype.linearCombination_apply_single] using h

theorem exists_ker_top [CharZero E] (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j)
    {k : ℕ} {Y : Fin k → Fin M → E} {C : Matrix (Fin k) (Fin M) E}
    (hC : ∀ j, C *ᵥ (J *ᵥ Y j) = Pi.single j 1) (t : Fin k → R ⊗[F] E) :
    ∃ m : (piR R σ J).ker, ∀ j, topRow (matP R σ J m.1) (fun i => inclR R (Y j i)) = t j := by
  classical
  have hsR := HaarCoord.sigR_sigR R hσ
  have hJR := JR_herm R σ J hJ
  let u : Fin M → R ⊗[F] E := fun a => -∑ j, t j * inclR R (C j a)
  let w : Fin M → R ⊗[F] E := fun a => sigR R σ (u a)
  have hz := z_half hsR hJR (halfR_add (F := F) (E := E) R) (sigR_halfR (F := F) (E := E) R σ)
    (t := 0) (by simp) w
  refine ⟨⟨nP hσ hJ w _ hz, nP_mem_ker hσ hJ _ _ hz⟩, fun j' => ?_⟩
  change topRow (nM (sigR R σ) (JR R J) w _) _ = _
  rw [topRow_nM]
  have hsw : ∀ a, sigR R σ (w a) = u a := fun a => hsR _
  have e1 : hv (sigR R σ) (JR R J) w (fun i => inclR R (Y j' i)) =
      ∑ a, u a * inclR R ((J *ᵥ Y j') a) := by
    simp only [hv, rowv, hsw, Finset.sum_mul, Matrix.mulVec, dotProduct, map_sum, map_mul,
      Finset.mul_sum, JR, Matrix.map_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have e2 : ∀ v : Fin M → E, ∑ a, u a * inclR R (v a) = -∑ j, t j * inclR R ((C *ᵥ v) j) := by
    intro v
    simp only [u, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul, Matrix.mulVec, dotProduct,
      map_sum, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine congrArg Neg.neg (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
    ring
  rw [e1, e2, hC, neg_neg]
  simp [Pi.single_apply, apply_ite]

theorem topRow_rat {p : stabilizer₂ R σ J} (h : p ∈ ratP R σ J) (v : Fin M → E) :
    ∃ c : E, topRow (matP R σ J p) (fun i => inclR R (v i)) = inclR R c := by
  obtain ⟨g, hg⟩ := exists_ratH R σ (hypOne J) p.1 h
  have hm : matP R σ J p =
      ((g : GL (Fin (M + 2)) E) : Matrix (Fin (M + 2)) (Fin (M + 2)) E).map (inclR R) := by
    change ((HA.mat R σ (hypOne J) p.1 : GL _ _) : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)) = _
    rw [hg, mat_ratH]
    rfl
  refine ⟨topRow ((g : GL (Fin (M + 2)) E) : Matrix (Fin (M + 2)) (Fin (M + 2)) E) v, ?_⟩
  rw [hm]
  simp [topRow]

end Surj

theorem stab_structure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ (ι : HA (AF F) σ J →* stabilizer₂ (AF F) σ J) (π : stabilizer₂ (AF F) σ J →* HA (AF F) σ J), Continuous ι ∧ Continuous π ∧ (∀ u, π (ι u) = u) ∧ (∀ u ∈ HFinIn (AF F) σ J, ι u ∈ ratP (AF F) σ J) ∧ (∀ p ∈ ratP (AF F) σ J, π p ∈ HFinIn (AF F) σ J) ∧ (∃ K : Set (stabilizer₂ (AF F) σ J), IsCompact K ∧ ∀ m ∈ π.ker, ∃ γ ∈ ratP (AF F) σ J, π γ = 1 ∧ γ * m ∈ K) ∧ (∀ (k : ℕ) (u : HA (AF F) σ J) (a : Fin 1 → Fin k → AF F ⊗[F] E) (Y : Fin k → Fin M → AF F ⊗[F] E), actW (AF F) σ (hypOne J) (ι u : HA (AF F) σ (hypOne J)) (consA a Y) = consA a (actW (AF F) σ J u Y)) ∧ ∀ (k : ℕ) (Y : Fin k → Fin M → E), LinearIndependent E Y → ∃ l : π.ker → Fin 1 → Fin k → AF F ⊗[F] E, Continuous l ∧ (∀ x y, l (x * y) = l x + l y) ∧ Function.Surjective l ∧ (∀ m : π.ker, (m : stabilizer₂ (AF F) σ J) ∈ ratP (AF F) σ J → l m ∈ ratA (F := F) (E := E) k) ∧ ∀ (m : π.ker) (a : Fin 1 → Fin k → AF F ⊗[F] E), actW (AF F) σ (hypOne J) ((m : stabilizer₂ (AF F) σ J) : HA (AF F) σ (hypOne J)) (consA a (ratTup (AF F) Y)) = consA (a + l m) (ratTup (AF F) Y) := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := i1
  haveI := i2
  haveI := i3
  obtain ⟨t1, -, -, -, t5, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (AF F)
  haveI := t1
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := IsModuleTopology.toContinuousSMul (AF F) _
  obtain ⟨hinv, δ, hδ, hσδ⟩ := HaarCoord.conj_facts hσ
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  obtain ⟨C, hC, hCc⟩ := GlobalTheory.AdeleCocompactExt.exists_compact_adele_ext F E
  obtain ⟨C₀, hC₀, hC₀c⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  refine ⟨iotaR (AF F) σ J, piR (AF F) σ J, continuous_iotaR _ σ J, continuous_piR _ σ J,
    piR_iotaR _ σ J, fun u hu => iotaR_rat _ σ J hu, fun p hp => piR_rat _ σ J hinj hp,
    exists_cover hinv hJ.1 hσ.2.2.1 hδ hσδ t5 hC hCc hC₀ hC₀c, actW_iotaR _ σ J, ?_⟩
  intro k Y hY
  obtain ⟨D, hD⟩ := exists_left_inv hJ.2 Y hY
  refine ⟨fun m _ j => topRow (matP (AF F) σ J m.1) (ratTup (AF F) Y j), ?_, ?_, ?_, ?_, ?_⟩
  · have hm : Continuous fun m : (piR (AF F) σ J).ker => matP (AF F) σ J m.1 :=
      (continuous_matStab (AF F) σ J).1.comp continuous_subtype_val
    refine continuous_pi fun _ => continuous_pi fun j => ?_
    exact continuous_finset_sum _ fun i _ => (hm.matrix_elem _ _).mul continuous_const
  · intro x y
    funext _ j
    exact topRow_ker_mul (AF F) σ J x y _
  · intro t
    obtain ⟨m, hm⟩ := exists_ker_top (R := AF F) hinv hJ.1 hD (t 0)
    refine ⟨m, ?_⟩
    funext a j
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    exact hm j
  · intro m hm
    choose c hc using fun j => topRow_rat hm (Y j)
    exact ⟨fun _ => c, by funext _ j; exact (hc j).symm⟩
  · intro m a
    exact actW_ker (AF F) σ J m a _

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Struct
