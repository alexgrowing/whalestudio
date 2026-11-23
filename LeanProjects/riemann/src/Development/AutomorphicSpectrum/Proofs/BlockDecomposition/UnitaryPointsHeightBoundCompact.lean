import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvecSurjective

set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor isTopologicalRing_tensor

namespace GlobalTheory.CompanionTheory.RedCov.MahlerU

theorem exists_isCompact_centralizer_reduction_set {K : Type*} [Field K] [NumberField K] {n : ℕ} {m : Type*}
    [Finite m] (L : m → Matrix (Fin n) (Fin n) K)
    (G : Set (AdelicGLn.AdelicGL K n)) (hG1 : ∀ g ∈ G, g ∈ Reduction.normOneGL K n)
    (hGL : ∀ g ∈ G, g ∈ adelicCentralizer L) {ε : ℝ} (hε : 0 < ε)
    (hh : ∀ g ∈ G, ∀ x : Fin n → K, x ≠ 0 → ε ≤ Reduction.height g x) :
    ∃ C : Set (AdelicGLn.AdelicGL K n), IsCompact C ∧ ∀ g ∈ G, ∃ γ : GL (Fin n) K,
      (∀ k, (γ : Matrix (Fin n) (Fin n) K) * L k = L k * γ) ∧
        (AdelicGLn.diagonal K n γ)⁻¹ * g ∈ C := by
  classical
  obtain ⟨C, hC, hC'⟩ := Reduction.exists_isCompact_forall_of_pos_le_height (K := K) (n := n) hε
  let Lm : m → Matrix (Fin n) (Fin n) 𝔸[K] := fun k => (L k).map (algebraMap K 𝔸[K])
  let Φ : AdelicGLn.AdelicGL K n → m → Matrix (Fin n) (Fin n) 𝔸[K] :=
    fun g k => (g : Matrix (Fin n) (Fin n) 𝔸[K]) * Lm k *
      ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])
  have hΦ : ∀ g g', Φ g = Φ g' ↔ g⁻¹ * g' ∈ adelicCentralizer L := by
    intro g g'
    rw [funext_iff]
    exact forall_congr' fun k => conj_eq_conj_iff g g' (Lm k)
  have hΦc : Continuous Φ := continuous_pi fun k =>
    ((Units.continuous_val.matrix_mul continuous_const).matrix_mul Units.continuous_coe_inv)
  let ψ : (m → Matrix (Fin n) (Fin n) K) → m → Matrix (Fin n) (Fin n) 𝔸[K] :=
    fun r k => (r k).map (algebraMap K 𝔸[K])
  have hψfin : {r | ψ r ∈ Φ '' C}.Finite := by
    refine finite_of_isCompact_coords (hC.image hΦc) ψ
      (fun p : m × Fin n × Fin n => fun M => M p.1 p.2.1 p.2.2)
      (fun p => (continuous_apply p.1).matrix_elem p.2.1 p.2.2)
      (fun r p => r p.1 p.2.1 p.2.2) ?_ (fun r p => rfl)
    intro r r' h
    funext k i j
    exact congrFun h (k, i, j)
  have hfin : (Φ '' C ∩ Φ '' (AdelicGLn.rationalGL K n : Set (AdelicGLn.AdelicGL K n))).Finite := by
    refine (hψfin.image ψ).subset ?_
    rintro _ ⟨hC1, _, ⟨γ, rfl⟩, rfl⟩
    have e : Φ (AdelicGLn.diagonal K n γ) = ψ fun k => (γ : Matrix (Fin n) (Fin n) K) * L k *
        ((γ⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      funext k
      simp only [ψ, Φ, Lm, ← map_inv]
      rw [Matrix.map_mul, Matrix.map_mul]
      rfl
    rw [e] at hC1 ⊢
    exact ⟨_, hC1, rfl⟩
  obtain ⟨T, hTΓ, hT⟩ := exists_finset_of_orbit Φ (adelicCentralizer L) (AdelicGLn.rationalGL K n)
    hΦ C hfin
  refine ⟨⋃ δ ∈ T, (fun c => δ⁻¹ * c) '' C,
    T.isCompact_biUnion fun δ _ => hC.image (continuous_const.mul continuous_id), ?_⟩
  intro g hg
  obtain ⟨_, ⟨γ₀, rfl⟩, c, hc, hgc⟩ := hC' g (hG1 g hg) (hh g hg)
  obtain ⟨δ, hδT, hγδ, hδc⟩ := hT g (hGL g hg) _ ⟨γ₀, rfl⟩ c hc hgc.symm
  obtain ⟨δ₀, rfl⟩ := hTΓ δ hδT
  refine ⟨γ₀ * δ₀, ?_, ?_⟩
  · rw [← diagonal_mem_adelicCentralizer_iff, map_mul]
    exact hγδ
  · refine Set.mem_biUnion hδT ⟨c, hc, ?_⟩
    rw [map_mul, ← hgc, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]

section Unitary

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)

local notation "𝒩'" => Fintype.card (ι × Fin (Module.finrank K E))

variable [NumberField K]

theorem exists_isCompact_trHom_set {d : ℕ} (b : Module.Basis (Fin d) K E) (hH : IsUnit H.det)
    (Y : Set (unitaryPoints K E H 𝔸[K])) {ε : ℝ} (hε : 0 < ε)
    (hh : ∀ u ∈ Y, ∀ x : Fin (Fintype.card (ι × Fin d)) → K, x ≠ 0 →
      ε ≤ Reduction.height (trHom b 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E))) x) :
    ∃ C : Set (GL (Fin (Fintype.card (ι × Fin d))) 𝔸[K]), IsCompact C ∧ ∀ u ∈ Y,
      ∃ M : GL ι (K ⊗[K] E), trHom b 𝔸[K]
        ((diagGL (Algebra.ofId K 𝔸[K]) M)⁻¹ * (u : GL ι (𝔸[K] ⊗[K] E))) ∈ C := by
  classical
  let G : Set (AdelicGLn.AdelicGL K (Fintype.card (ι × Fin d))) :=
    (fun u : unitaryPoints K E H 𝔸[K] => trHom b 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E))) '' Y
  have hG1 : ∀ g ∈ G, g ∈ Reduction.normOneGL K (Fintype.card (ι × Fin d)) := by
    rintro _ ⟨u, -, rfl⟩
    rw [Reduction.mem_normOneGL]
    set a := AdelicGLn.det K (Fintype.card (ι × Fin d)) (trHom b 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E)))
    have ha : a * a = 1 := by
      ext
      simpa [a] using det_trHom_mul_self b 𝔸[K] H hH u
    have h2 : (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) *
        (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) = 1 := by
      have h3 := congrArg (GroundTheory.Global.IdeleGroup.ideleModule K) ha
      rw [map_mul, map_one] at h3
      simpa using congrArg Subtype.val h3
    have hpos := (GroundTheory.Global.IdeleGroup.ideleModule K a).2
    nlinarith
  have hGL : ∀ g ∈ G, g ∈ adelicCentralizer (resScalar (ι := ι) b) := by
    rintro _ ⟨u, -, rfl⟩ j
    have e := resScalar_map (ι := ι) b (Algebra.ofId K 𝔸[K]) j
    change _ * (resScalar (ι := ι) b j).map (Algebra.ofId K 𝔸[K]) =
      (resScalar (ι := ι) b j).map (Algebra.ofId K 𝔸[K]) * _
    rw [e]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [trHom_val]
    exact resHom_commute_scalar b 𝔸[K] _ _
  obtain ⟨C, hC, hred⟩ := exists_isCompact_centralizer_reduction_set (resScalar (ι := ι) b) G hG1 hGL hε
    (by rintro _ ⟨u, hu, rfl⟩ x hx; exact hh u hu x hx)
  refine ⟨C, hC, fun u hu => ?_⟩
  obtain ⟨γ, hγ, hγC⟩ := hred _ ⟨u, hu, rfl⟩
  obtain ⟨M, hM⟩ := exists_resHom_eq_of_commute b γ hγ
  refine ⟨inside₂ (K ⊗[K] E) M, ?_⟩
  have e : trHom b 𝔸[K] (diagGL (Algebra.ofId K 𝔸[K]) (inside₂ (K ⊗[K] E) M)) =
      AdelicGLn.diagonal K (Fintype.card (ι × Fin d)) γ := by
    ext : 1
    rw [← invTr_diagGL, trHom_invTr, diagGL_val, resHom_baseMap, hM]
    rfl
  rw [map_mul, map_inv, e]
  exact hγC

theorem exists_isCompact_unitary_set (hH : IsUnit H.det)
    (Y : Set (unitaryPoints K E H 𝔸[K])) {ε : ℝ} (hε : 0 < ε)
    (hh : ∀ u ∈ Y, ∀ x : Fin 𝒩' → K, x ≠ 0 →
      ε ≤ Reduction.height (trHom (Module.finBasis K E) 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E))) x) :
    ∃ Ω : Set (unitaryPoints K E H 𝔸[K]), IsCompact Ω ∧ ∀ u ∈ Y,
      ∃ θ ∈ (unitaryDiagonal K H).range, θ⁻¹ * u ∈ Ω := by
  classical
  let b := Module.finBasis K E
  obtain ⟨C, hC, hred⟩ := exists_isCompact_trHom_set H b hH Y hε hh
  set α := Algebra.ofId K 𝔸[K] with hα
  set Hb := baseMatrix K H 𝔸[K] with hHb
  let Ψ : GL ι (𝔸[K] ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E) := fun x =>
    cstar (x : Matrix ι ι (𝔸[K] ⊗[K] E)) * Hb * x
  let Φ : GL ι (𝔸[K] ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E) := fun g => Ψ g⁻¹
  have hΨmul : ∀ x y, Ψ (x * y) = cstar (y : Matrix ι ι (𝔸[K] ⊗[K] E)) * Ψ x * y := by
    intro x y
    simp only [Ψ, Units.val_mul, cstar_mul, Matrix.mul_assoc]
  have hΨone : Ψ 1 = Hb := by
    simp [Ψ, cstar_one]
  have hcancel : ∀ (z : GL ι (𝔸[K] ⊗[K] E)) (X : Matrix ι ι (𝔸[K] ⊗[K] E)),
      cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        (cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) * X *
          ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))) *
        (z : Matrix ι ι (𝔸[K] ⊗[K] E)) = X := by
    intro z X
    have h1 : cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) = 1 := by
      rw [← cstar_mul, z.inv_mul, cstar_one]
    have h2 : ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        (z : Matrix ι ι (𝔸[K] ⊗[K] E)) = 1 := z.inv_mul
    calc _ = (cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) *
          cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))) * X *
          (((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
            (z : Matrix ι ι (𝔸[K] ⊗[K] E))) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  have hΦ : ∀ g g', Φ g = Φ g' ↔ g⁻¹ * g' ∈ unitaryPoints K E H 𝔸[K] := by
    intro g g'
    have e1 : Φ g = cstar ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        Ψ (g⁻¹ * g') * ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) := by
      show Ψ g⁻¹ = _
      rw [← hΨmul, mul_inv_cancel_right]
    have e2 : Φ g' = cstar ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        Hb * ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) := by
      show Ψ g'⁻¹ = _
      rw [← hΨone, ← hΨmul, one_mul]
    rw [e1, e2]
    constructor
    · intro he
      have h := congrArg (fun X => cstar (g' : Matrix ι ι (𝔸[K] ⊗[K] E)) * X *
        (g' : Matrix ι ι (𝔸[K] ⊗[K] E))) he
      simp only [hcancel] at h
      exact h
    · intro hu
      have h : Ψ (g⁻¹ * g') = Hb := hu
      rw [h]
  let Γ : Subgroup (GL ι (𝔸[K] ⊗[K] E)) := (diagGL (ι := ι) α).range
  let C₂ : Set (GL ι (𝔸[K] ⊗[K] E)) := {w | trHom b 𝔸[K] w ∈ C}
  let Ψ' : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] → Matrix ι ι (𝔸[K] ⊗[K] E) := fun A =>
    cstar (readoff b 𝔸[K] A)ᵀ * Hb * (readoff b 𝔸[K] A)ᵀ
  have hΨ'c : Continuous Ψ' := by
    have h1 : Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] => (readoff (ι := ι) b 𝔸[K] A)ᵀ :=
      (continuous_readoff b 𝔸[K]).matrix_transpose
    have h2 : Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] =>
        cstar (readoff (ι := ι) b 𝔸[K] A)ᵀ := by
      show Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] =>
        (((readoff (ι := ι) b 𝔸[K] A)ᵀ).map (conjBase K E 𝔸[K]))ᵀ
      exact (h1.matrix_map (continuous_conjBase 𝔸[K])).matrix_transpose
    exact (h2.matrix_mul continuous_const).matrix_mul h1
  have hC₂ : ∀ w ∈ C₂, Φ w = Ψ' (trHom b 𝔸[K] w : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K]) := by
    intro w _
    show Ψ w⁻¹ = _
    simp only [Ψ, Ψ', trHom_val, readoff_resHom, transpose_transpose]
  have hX : IsCompact (Ψ' '' (Units.val '' C)) := (hC.image Units.continuous_val).image hΨ'c
  let ψ : Matrix ι ι (K ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E) := fun V => V.map (baseMap α)
  have hΓ : ∀ M : GL ι (K ⊗[K] E), Φ (diagGL α M) =
      ψ (cstar ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K *
        ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E))) := by
    intro M
    show Ψ (diagGL α M)⁻¹ = _
    rw [← map_inv]
    simp only [Ψ, ψ, diagGL_val]
    rw [cstar_mul_baseMatrix_map]
  have hfinV : {V | ψ V ∈ Ψ' '' (Units.val '' C)}.Finite := by
    refine finite_of_isCompact_coords hX ψ
      (fun p : ι × ι × Fin (Module.finrank K E) => fun X => coords b 𝔸[K] (X p.1 p.2.1) p.2.2)
      (fun p => (continuous_apply _).comp ((continuous_coords b 𝔸[K]).comp
        (continuous_id.matrix_elem _ _)))
      (fun V p => coords b K (V p.1 p.2.1) p.2.2) ?_ ?_
    · intro V V' h
      ext i j
      apply (coords b K).injective
      funext k
      exact congrFun h (i, j, k)
    · intro V p
      simp only [ψ, Matrix.map_apply, coords_baseMap]
      rfl
  have hfin : (Φ '' C₂ ∩ Φ '' (Γ : Set (GL ι (𝔸[K] ⊗[K] E)))).Finite := by
    refine (hfinV.image ψ).subset ?_
    rintro _ ⟨⟨w, hw, rfl⟩, _, ⟨M, rfl⟩, he⟩
    refine ⟨cstar ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K *
        ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)), ?_, ?_⟩
    · show ψ _ ∈ Ψ' '' (Units.val '' C)
      rw [← hΓ M, he, hC₂ w hw]
      exact ⟨_, ⟨_, hw, rfl⟩, rfl⟩
    · rw [← hΓ M, he]
  obtain ⟨T, hTΓ, hT⟩ := exists_finset_of_orbit Φ (unitaryPoints K E H 𝔸[K]) Γ hΦ C₂ hfin
  let C₃ : Set (GL (Fin 𝒩') 𝔸[K]) := ⋃ δ ∈ T, (fun c => (trHom b 𝔸[K] δ)⁻¹ * c) '' C
  have hC₃ : IsCompact C₃ :=
    T.isCompact_biUnion fun δ _ => hC.image (continuous_const.mul continuous_id)
  let Ω : Set (unitaryPoints K E H 𝔸[K]) := {v | trHom b 𝔸[K] (v : GL ι (𝔸[K] ⊗[K] E)) ∈ C₃}
  refine ⟨Ω, ?_, ?_⟩
  · have hΩcl : IsClosed Ω :=
      hC₃.isClosed.preimage ((continuous_trHom b 𝔸[K]).comp continuous_subtype_val)
    let F : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] → ι × ι × Fin (Module.finrank K E) → 𝔸[K] :=
      fun A p =>
      coords b 𝔸[K] ((readoff (ι := ι) b 𝔸[K] A)ᵀ p.1 p.2.1) p.2.2
    have hFc : Continuous F := continuous_pi fun p => (continuous_apply _).comp
      ((continuous_coords b 𝔸[K]).comp
        (((continuous_readoff b 𝔸[K]).matrix_transpose).matrix_elem _ _))
    set D := (unitaryCoords H 𝔸[K] b) ⁻¹' (F '' (Units.val '' C₃)) with hD
    have hDc : IsCompact D := (isClosedEmbedding_unitaryCoords H 𝔸[K] b hH).isCompact_preimage
      ((hC₃.image Units.continuous_val).image hFc)
    have hsub : Ω ⊆ D⁻¹ := by
      intro v hv
      show v⁻¹ ∈ D
      refine ⟨_, ⟨_, hv, rfl⟩, ?_⟩
      funext p
      simp only [F, trHom_val, readoff_resHom, transpose_transpose]
      rfl
    exact hDc.inv.of_isClosed_subset hΩcl hsub
  · intro u huY
    obtain ⟨M, hM⟩ := hred u huY
    obtain ⟨δ, hδT, hηδ, -⟩ := hT u u.2 (diagGL α M) ⟨M, rfl⟩
      ((diagGL α M)⁻¹ * (u : GL ι (𝔸[K] ⊗[K] E))) hM (by rw [mul_inv_cancel_left])
    obtain ⟨m, rfl⟩ := hTΓ δ hδT
    rw [← map_mul] at hηδ
    have hU := mem_unitaryPoints_of_diagGL H hηδ
    refine ⟨unitaryDiagonal K H ⟨M * m, hU⟩, ⟨_, rfl⟩, ?_⟩
    have e : ((unitaryDiagonal K H ⟨M * m, hU⟩ : unitaryPoints K E H 𝔸[K]) :
        GL ι (𝔸[K] ⊗[K] E)) = diagGL α (M * m) := Units.ext rfl
    show trHom b 𝔸[K] (((unitaryDiagonal K H ⟨M * m, hU⟩)⁻¹ * u : unitaryPoints K E H 𝔸[K]) :
      GL ι (𝔸[K] ⊗[K] E)) ∈ C₃
    rw [Subgroup.coe_mul, Subgroup.coe_inv, e]
    refine Set.mem_biUnion hδT ⟨_, hM, ?_⟩
    simp only [map_mul, map_inv, _root_.mul_inv_rev, mul_assoc]

end Unitary

theorem mahler_unitary_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E), IsUnit H.det → ∀ (Y : Set (unitaryPoints F E H 𝔸[F])) (ε : ℝ), 0 < ε → (∀ u ∈ Y, ∀ x : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F, x ≠ 0 → ε ≤ Reduction.height (trHom (ι := Fin n) (Module.finBasis F E) 𝔸[F] (u : GL (Fin n) (𝔸[F] ⊗[F] E))) x) → ∃ Ω : Set (unitaryPoints F E H 𝔸[F]), IsCompact Ω ∧ ∀ u ∈ Y, ∃ θ ∈ (unitaryDiagonal F H).range, θ⁻¹ * u ∈ Ω := by
  intro F E _ _ _ _ _ _ n H hH Y ε hε hh
  exact exists_isCompact_unitary_set H hH Y hε hh

end GlobalTheory.CompanionTheory.RedCov.MahlerU
