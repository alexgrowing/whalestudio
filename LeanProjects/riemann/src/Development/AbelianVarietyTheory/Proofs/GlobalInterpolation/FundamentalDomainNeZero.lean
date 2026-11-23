import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold

noncomputable section

namespace GlobalTheory.UnfoldingCompare

open NumberField MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped ENNReal TensorProduct

theorem allSome_congr {α : Sort*} {P Q Q' : α → Prop} (h : ∀ a, P a → (Q a ↔ Q' a)) :
    AllSome P Q ↔ AllSome P Q' :=
  and_congr_right fun _ => forall_congr' fun a => imp_congr_right (h a)

def IsChoice {α : Type} (T : (α → Prop) → Prop) : Prop :=
  ∃ S : Set α, (∀ K, T K ↔ T (fun _ => True) ∧ ∀ f ∈ S, K f) ∧ (T (fun _ => True) → S.Nonempty)

theorem isChoice_eval {α : Type} (a : α) : IsChoice fun K => K a :=
  ⟨{a}, fun K => by simp, fun _ => ⟨a, rfl⟩⟩

theorem isChoice_allSome {α β : Type} (P : β → Prop) (T : β → (α → Prop) → Prop)
    (h : ∀ b, IsChoice (T b)) : IsChoice fun K => AllSome P fun b => T b K := by
  choose S hS hne using h
  refine ⟨{f | ∃ b, P b ∧ f ∈ S b}, fun K => ⟨fun hK => ⟨⟨hK.1, fun b hb => ((hS b K).1 (hK.2 b hb)).1⟩, ?_⟩,
    fun hK => ⟨hK.1.1, fun b hb => (hS b K).2 ⟨hK.1.2 b hb, fun f hf => hK.2 f ⟨b, hb, hf⟩⟩⟩⟩, ?_⟩
  · rintro f ⟨b, hb, hf⟩
    exact ((hS b K).1 (hK.2 b hb)).2 f hf
  · rintro ⟨⟨b, hb⟩, hT⟩
    obtain ⟨f, hf⟩ := hne b (hT b hb)
    exact ⟨f, b, hb, hf⟩

theorem IsChoice.value_iff {X : Type} {T : ((X → ℝ≥0∞) → Prop) → Prop} (hT : IsChoice T)
    (p : X → Prop) (x₀ : X) (h₀ : p x₀) (L : X → ℝ≥0∞) {m : ℝ≥0∞} (hm : m ≠ 0) (hm' : m ≠ ⊤) :
    T (fun f => ∀ x, p x → L x = m * f x) ↔
      ∀ x, p x → ∃ I, T (fun f => f x = I) ∧ L x = m * I := by
  obtain ⟨S, hS, hne⟩ := hT
  constructor
  · intro h x hx
    obtain ⟨h1, h2⟩ := (hS _).1 h
    obtain ⟨f₀, hf₀⟩ := hne h1
    refine ⟨f₀ x, (hS _).2 ⟨h1, fun f hf => ?_⟩, h2 f₀ hf₀ x hx⟩
    exact (ENNReal.mul_right_inj hm hm').1 ((h2 f hf x hx).symm.trans (h2 f₀ hf₀ x hx))
  · intro h
    obtain ⟨I₀, hI₀, -⟩ := h x₀ h₀
    refine (hS _).2 ⟨((hS _).1 hI₀).1, fun f hf x hx => ?_⟩
    obtain ⟨I, hI, hL⟩ := h x hx
    rw [hL, ((hS _).1 hI).2 f hf]

section Stab

variable {P Q P' Q' : ℕ}

theorem Jpq_mul_self (P Q : ℕ) : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, fromBlocks_multiply]

theorem Jpq_conjTranspose (P Q : ℕ) : (Formalism.UG.Jpq P Q)ᴴ = Formalism.UG.Jpq P Q := by
  simp [Formalism.UG.Jpq, fromBlocks_conjTranspose]

theorem mat_unitary (g : UpqT P Q) : (UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat g = Formalism.UG.Jpq P Q :=
  (show Formalism.UG.Upq P Q from g).2

theorem mat_injective {g h : UpqT P Q} (e : UpqT.mat g = UpqT.mat h) : g = h :=
  Subtype.ext (Units.ext e)

theorem exists_frame_inv (hc : P' + Q' + 1 = P + Q) {x : Fin P ⊕ Fin Q → ℂ}
    (hx : star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x ≠ 0) {C : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ}
    (h1 : Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.UG.Jpq P' Q') (h2 : (Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x = 0) :
    ∃ (N : Matrix ((Fin P' ⊕ Fin Q') ⊕ Unit) (Fin P ⊕ Fin Q) ℂ) (B : Matrix Unit Unit ℂ),
      N * fromCols C (replicateCol Unit x) = 1 ∧ fromCols C (replicateCol Unit x) * N = 1 ∧
      (fromCols C (replicateCol Unit x))ᴴ * Formalism.UG.Jpq P Q * fromCols C (replicateCol Unit x) =
        fromBlocks (Formalism.UG.Jpq P' Q') 0 0 B := by
  set b := star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x with hb
  have h3 : Cᴴ * Formalism.UG.Jpq P Q * replicateCol Unit x = 0 := by
    rw [← replicateCol_mulVec, h2]; rfl
  have h4 : (replicateCol Unit x)ᴴ * Formalism.UG.Jpq P Q * C = 0 := by
    have := congrArg conjTranspose h3
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Jpq_conjTranspose,
      conjTranspose_zero, ← Matrix.mul_assoc] at this
  have h5 : (replicateCol Unit x)ᴴ * Formalism.UG.Jpq P Q * replicateCol Unit x = b • (1 : Matrix Unit Unit ℂ) := by
    rw [Matrix.mul_assoc, ← replicateCol_mulVec, conjTranspose_replicateCol]
    ext i j
    simp [hb]
  have hG : (fromCols C (replicateCol Unit x))ᴴ * Formalism.UG.Jpq P Q * fromCols C (replicateCol Unit x) =
      fromBlocks (Formalism.UG.Jpq P' Q') 0 0 (b • (1 : Matrix Unit Unit ℂ)) := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols, h1, h3, h4, h5]
  have hN : (fromBlocks (Formalism.UG.Jpq P' Q') 0 0 (b⁻¹ • (1 : Matrix Unit Unit ℂ)) *
      ((fromCols C (replicateCol Unit x))ᴴ * Formalism.UG.Jpq P Q)) * fromCols C (replicateCol Unit x) = 1 := by
    rw [Matrix.mul_assoc, hG, fromBlocks_multiply]
    simp [Jpq_mul_self, smul_smul, hx]
  have e : ((Fin P' ⊕ Fin Q') ⊕ Unit) ≃ (Fin P ⊕ Fin Q) := Fintype.equivOfCardEq (by simpa using hc)
  exact ⟨_, _, hN, (Matrix.mul_eq_one_comm_of_equiv e).1 hN, hG⟩

theorem eq_of_frame (hc : P' + Q' + 1 = P + Q) {x : Fin P ⊕ Fin Q → ℂ}
    (hx : star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x ≠ 0) {C : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ}
    (h1 : Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.UG.Jpq P' Q') (h2 : (Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x = 0)
    {g h : UpqT P Q} (eC : UpqT.mat g * C = UpqT.mat h * C) (ex : UpqT.mat g *ᵥ x = UpqT.mat h *ᵥ x) :
    g = h := by
  obtain ⟨N, B, -, hN, -⟩ := exists_frame_inv hc hx h1 h2
  apply mat_injective
  have : UpqT.mat g * fromCols C (replicateCol Unit x) = UpqT.mat h * fromCols C (replicateCol Unit x) := by
    rw [mul_fromCols, mul_fromCols, eC, ← replicateCol_mulVec, ← replicateCol_mulVec, ex]
  rw [← Matrix.mul_one (UpqT.mat g), ← Matrix.mul_one (UpqT.mat h), ← hN, ← Matrix.mul_assoc, this,
    Matrix.mul_assoc]

theorem exists_stab_hom (hc : P' + Q' + 1 = P + Q) {x : Fin P ⊕ Fin Q → ℂ}
    (hx : star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x ≠ 0) {C : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ}
    (h1 : Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.UG.Jpq P' Q') (h2 : (Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x = 0) :
    ∃ j : UpqT P' Q' →* UpqT P Q,
      ∀ g, UpqT.mat (j g) *ᵥ x = x ∧ UpqT.mat (j g) * C = C * UpqT.mat g := by
  obtain ⟨N, B, hN, hN', hG⟩ := exists_frame_inv hc hx h1 h2
  set M := fromCols C (replicateCol Unit x) with hM
  let blk : UpqT P' Q' → Matrix ((Fin P' ⊕ Fin Q') ⊕ Unit) ((Fin P' ⊕ Fin Q') ⊕ Unit) ℂ :=
    fun g => fromBlocks (UpqT.mat g) 0 0 1
  have blk_mul : ∀ g h, blk (g * h) = blk g * blk h := fun g h => by
    simp [blk, fromBlocks_multiply, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_mul]
  have blk_one : blk 1 = 1 := by simp [blk, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_one]
  have blk_un : ∀ g, (blk g)ᴴ * fromBlocks (Formalism.UG.Jpq P' Q') 0 0 B * blk g =
      fromBlocks (Formalism.UG.Jpq P' Q') 0 0 B := fun g => by
    simp [blk, fromBlocks_multiply, fromBlocks_conjTranspose, mat_unitary]
  let φ : UpqT P' Q' →* Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
    { toFun := fun g => M * blk g * N
      map_one' := by rw [blk_one, Matrix.mul_one, hN']
      map_mul' := fun g h => by
        rw [blk_mul]
        calc M * (blk g * blk h) * N = M * (blk g * (N * M) * blk h) * N := by rw [hN, Matrix.mul_one]
          _ = _ := by simp only [Matrix.mul_assoc] }
  have hφ : ∀ g, (φ g)ᴴ * Formalism.UG.Jpq P Q * φ g = Formalism.UG.Jpq P Q := fun g => by
    calc (φ g)ᴴ * Formalism.UG.Jpq P Q * φ g
        = Nᴴ * ((blk g)ᴴ * (Mᴴ * Formalism.UG.Jpq P Q * M) * blk g) * N := by
          change (M * blk g * N)ᴴ * Formalism.UG.Jpq P Q * (M * blk g * N) = _
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Nᴴ * (Mᴴ * Formalism.UG.Jpq P Q * M) * N := by rw [hG, blk_un]
      _ = (M * N)ᴴ * Formalism.UG.Jpq P Q * (M * N) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hN']; simp
  let j : UpqT P' Q' →* Formalism.UG.Upq P Q := φ.toHomUnits.codRestrict (Formalism.UG.Upq P Q) fun g => hφ g
  refine ⟨j, fun g => ?_⟩
  have e : φ g * M = fromCols (C * UpqT.mat g) (replicateCol Unit x) := by
    change M * blk g * N * M = _
    rw [Matrix.mul_assoc, hN, Matrix.mul_one, hM]
    simp [blk, fromCols_mul_fromBlocks]
  rw [hM, mul_fromCols, fromCols_ext_iff, ← replicateCol_mulVec] at e
  exact ⟨replicateCol_injective e.2, e.1⟩

end Stab

section Arch

variable {P Q P' Q' : ℕ} {T : Type}

theorem arch_iff (hc : P' + Q' + 1 = P + Q) (xr : T → Fin P ⊕ Fin Q → ℂ)
    (hx : ∀ ρ, star (xr ρ) ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ xr ρ ≠ 0)
    (m' : Measure (T → UpqT P' Q')) (m : Measure (T → UpqT P Q)) {Y : Type} (R : Y → Prop)
    (K : ∀ j : (T → UpqT P' Q') →* (T → UpqT P Q), Measure (IndefiniteRowSideFullHecke.LatticeTensorUnfolding.RCosets j) → Y → Prop) :
    (AllSome (fun j : T → (UpqT P' Q' →* UpqT P Q) => ∀ ρ, IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.IsStabEmb (xr ρ) (j ρ)) fun j =>
      AllSome (IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.IsQuotientMeasure (IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.piEmb j) m' m) fun ν =>
      AllSome R fun y => K (IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.piEmb j) ν y) ↔
    (AllSome (fun C : T → Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ =>
      ∀ ρ, (C ρ)ᴴ * Formalism.UG.Jpq P Q * C ρ = Formalism.UG.Jpq P' Q' ∧
        ((C ρ)ᴴ * Formalism.UG.Jpq P Q) *ᵥ xr ρ = 0) fun C =>
      AllSome (fun j : (T → UpqT P' Q') →* (T → UpqT P Q) =>
        ∀ b ρ, UpqT.mat (j b ρ) * C ρ = C ρ * UpqT.mat (b ρ) ∧
          UpqT.mat (j b ρ) *ᵥ xr ρ = xr ρ) fun j =>
      AllSome R fun y => AllSome (IndefiniteRowSideFullHecke.LatticeTensorUnfolding.IsQuotMeasure j m m') fun ν => K j ν y) := by
  constructor
  · rintro ⟨⟨j₀, hj₀⟩, H⟩
    choose C₀ hC₀ using hj₀
    refine ⟨⟨C₀, fun ρ => ⟨(hC₀ ρ).1, (hC₀ ρ).2.1⟩⟩, fun C hC => ?_⟩
    choose j₁ hj₁ using fun ρ => exists_stab_hom hc (hx ρ) (hC ρ).1 (hC ρ).2
    refine ⟨⟨IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.piEmb j₁, fun b ρ => ⟨(hj₁ ρ (b ρ)).2, (hj₁ ρ (b ρ)).1⟩⟩, fun j hj => ?_⟩
    have e : j = IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.piEmb j₁ := by
      ext b ρ
      exact eq_of_frame hc (hx ρ) (hC ρ).1 (hC ρ).2 ((hj b ρ).1.trans (hj₁ ρ (b ρ)).2.symm)
        ((hj b ρ).2.trans (hj₁ ρ (b ρ)).1.symm)
    subst e
    obtain ⟨⟨ν₀, hν₀⟩, H'⟩ := H j₁ fun ρ => ⟨C ρ, (hC ρ).1, (hC ρ).2, hj₁ ρ⟩
    exact ⟨(H' ν₀ hν₀).1, fun y hy => ⟨⟨ν₀, hν₀⟩, fun ν hν => (H' ν hν).2 y hy⟩⟩
  · rintro ⟨⟨C₀, hC₀⟩, H⟩
    choose j₀ hj₀ using fun ρ => exists_stab_hom hc (hx ρ) (hC₀ ρ).1 (hC₀ ρ).2
    refine ⟨⟨j₀, fun ρ => ⟨C₀ ρ, (hC₀ ρ).1, (hC₀ ρ).2, hj₀ ρ⟩⟩, fun j hj => ?_⟩
    choose C hC using hj
    obtain ⟨⟨y₀, hy₀⟩, H'⟩ := (H C fun ρ => ⟨(hC ρ).1, (hC ρ).2.1⟩).2 (IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.piEmb j)
      fun b ρ => ⟨((hC ρ).2.2 (b ρ)).2, ((hC ρ).2.2 (b ρ)).1⟩
    exact ⟨(H' y₀ hy₀).1, fun ν hν => ⟨⟨y₀, hy₀⟩, fun y hy => (H' y hy).2 ν hν⟩⟩

end Arch

theorem norm_coords {E : Type} [Field E] [NumberField E] [StarRing E] (W : HSpace E) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = star (τ a)) {P Q : ℕ} (A : Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ)
    (hA : Aᴴ * Formalism.UG.Jpq P Q * A = W.gram.map τ) (x : W.V) :
    star (A *ᵥ fun i => τ (W.frame.repr x i)) ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ (A *ᵥ fun i => τ (W.frame.repr x i)) =
      τ (W.hT x x) := by
  rw [star_mulVec, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, hA]
  conv_rhs => rw [← W.frame.sum_repr x]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul,
    RingHom.id_apply, dotProduct, mulVec, Matrix.map_apply, HSpace.gram, Pi.star_apply, starRingEnd_apply, hτ,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem emb_star (D : D7) (τ : D.host.E →+* ℂ) (a : D.host.E) :
    letI := D.host.cmStar; τ (star a) = star (τ a) := by
  haveI := D.host.isCMField_hostE
  exact IsCMField.complexEmbedding_complexConj D.host.E τ a

theorem fundamentalDomain_ne_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J)) [μ.IsHaarMeasure]
    {𝓕 : Set (HA (AF F) σ J)} (h : IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ) : μ 𝓕 ≠ 0 := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA σ J
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : Countable Γ := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma σ J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  exact IsFundamentalDomain.measure_ne_zero (G := Γ) (NeZero.ne μ) h

theorem unfoldAt_iff (D : D7) : letI := D.host.cmStar
    ∀ (W W' : HSpace D.host.E) (P Q P' Q' : ℕ) (s : Bool) (x : W.V), P' + Q' + 1 = P + Q →
      W.hT x x = (if s then 1 else -1) →
      (IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.UnfoldAt D W W' P Q P' Q' (if s then 1 else -1) x ↔
        IndefiniteRowSideFullHecke.LatticeTensorUnfolding.UnfoldAt D W W' P Q P' Q' s x) := by
  letI := D.host.cmStar
  intro W W' P Q P' Q' s x hc hx
  have key : ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram))
      (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) (m : ℝ≥0∞), m ≠ 0 → m ≠ ⊤ →
      ((AllSome (fun θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) =>
        ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ)) fun θ =>
      AllSome (fun A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ =>
        ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ)) fun A =>
      AllSome (fun j : D.what₂.Tau → (UpqT P' Q' →* UpqT P Q) =>
        ∀ ρ, IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.IsStabEmb (A ρ *ᵥ fun i => embOf D ρ (IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.coordTup W x 0 i)) (j ρ)) fun j =>
      AllSome (IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.IsQuotientMeasure (IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.piEmb j) (Measure.pi fun _ => D.cd.cd P' Q')
        (Measure.pi fun _ => D.cd.cd P Q)) fun ν =>
      AllSome (fun pt : (D.what₂.Tau → UpqT P Q) →
          (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) =>
        ∀ g ρ, IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.infCoord (θ ρ) (A ρ) (pt g) =
          UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => embOf D ρ (IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.coordTup W x 0 i))) fun pt =>
      ∀ Φi : (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℝ≥0∞, Measurable Φi →
        ∫⁻ h in 𝓕, ∑' x' : {x' : W.V // W.hT x' x' = (if s then 1 else -1)},
            IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.atInv D.sp.cm.sig W.gram (IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.phiLat (L0c D W) Φi) h
              (IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.coordTup W x'.1) ∂μ =
          m * ∫⁻ c, Φi (pt (Quotient.out c)) ∂ν) ↔
      ∀ Φi : (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℝ≥0∞, Measurable Φi →
        ∃ I : ℝ≥0∞, IndefiniteRowSideFullHecke.LatticeTensorUnfolding.IsInfQuotIntegral D W P Q P' Q' x Φi I ∧
          ∫⁻ h in 𝓕, ∑' x' : {x' : W.V // W.hT x' x' = (if s then 1 else -1)},
            IndefiniteRowSideFullHecke.LatticeTensorUnfolding.atInv D.sp.cm.sig W.gram (IndefiniteRowSideFullHecke.LatticeTensorUnfolding.latTensor (L0c D W) Φi) h
              (IndefiniteRowSideFullHecke.LatticeTensorUnfolding.coords W x'.1) ∂μ = m * I) := by
    intro μ 𝓕 m hm hm'
    refine Iff.trans (allSome_congr fun θ _ => allSome_congr fun A hA =>
      arch_iff hc (fun ρ => A ρ *ᵥ fun i => embOf D ρ (IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.coordTup W x 0 i)) (fun ρ => ?_) _ _ _
        (fun j ν (pt : (D.what₂.Tau → UpqT P Q) →
          (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E)) =>
          ∀ Φi : (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℝ≥0∞, Measurable Φi →
            ∫⁻ h in 𝓕, ∑' x' : {x' : W.V // W.hT x' x' = (if s then 1 else -1)},
              IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.atInv D.sp.cm.sig W.gram (IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.phiLat (L0c D W) Φi) h
                (IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.coordTup W x'.1) ∂μ =
            m * ∫⁻ c, Φi (pt (Quotient.out c)) ∂ν)) ?_
    · have := norm_coords W (embOf D ρ) (emb_star D _) (A ρ) (hA ρ) x
      refine fun h0 => ?_
      have h1 := this.symm.trans h0
      rw [hx] at h1
      cases s <;> simp at h1
    · exact IsChoice.value_iff
        (isChoice_allSome _ _ fun θ => isChoice_allSome _ _ fun A => isChoice_allSome _ _ fun C =>
          isChoice_allSome _ _ fun (j : (D.what₂.Tau → UpqT P' Q') →* (D.what₂.Tau → UpqT P Q)) =>
          isChoice_allSome _ _ fun (o : (D.what₂.Tau → UpqT P Q) →
            (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E)) =>
          isChoice_allSome _ _ fun ν =>
          isChoice_eval (fun Φi : (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℝ≥0∞ =>
            ∫⁻ c : IndefiniteRowSideFullHecke.LatticeTensorUnfolding.RCosets j, Φi (o c.out) ∂ν))
        Measurable (fun _ => 0) measurable_const _ hm hm'
  constructor
  · intro h μ μ' hμ hμ' 𝓕 𝓕' h1 h2 h3 h4
    haveI := hμ'.1
    exact (key μ 𝓕 _ (fundamentalDomain_ne_zero _ _ μ' h2) h4.ne).1 (h μ μ' 𝓕 𝓕' hμ hμ' h1 h2 h3 h4)
  · intro h μ μ' 𝓕 𝓕' hμ hμ' h1 h2 h3 h4
    haveI := hμ'.1
    exact (key μ 𝓕 _ (fundamentalDomain_ne_zero _ _ μ' h2) h4.ne).2 (h μ μ' hμ hμ' 𝓕 𝓕' h1 h2 h3 h4)

theorem setting_iff (D : D7) : letI := D.host.cmStar
    ∀ R : ∀ (W W' : HSpace D.host.E), (W'.V →ₗ[D.host.E] W.V) → Prop,
    (∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 3 ≤ W.rank →
      ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) →
      ∀ x : W.V, W.hT x x = (if s then 1 else -1) → x ∈ W.L0 →
      ∀ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
        HSpace.IsIsomEmb W' W ι → LinearMap.range ι = LinearMap.ker (W.hT x) → W'.SigOK →
        (∀ τ, W'.sig τ = (if s then (P - 1, Q) else (P, Q - 1))) → R W W' ι →
        IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.UnfoldAt D W W' P Q (if s then P - 1 else P) (if s then Q else Q - 1)
          (if s then 1 else -1) x) ↔
    ∀ (W W' : HSpace D.host.E) (P Q P' Q' : ℕ) (s : Bool) (x : W.V) (ι : W'.V →ₗ[D.host.E] W.V),
      IndefiniteRowSideFullHecke.LatticeTensorUnfolding.HidaSetting W W' P Q P' Q' s x ι → R W W' ι → IndefiniteRowSideFullHecke.LatticeTensorUnfolding.UnfoldAt D W W' P Q P' Q' s x := by
  letI := D.host.cmStar
  intro R
  constructor
  · rintro h W W' P Q P' Q' s x ι ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ hR
    cases s
    · obtain ⟨rfl, rfl⟩ : P = P' ∧ Q = Q' + 1 := by simpa using h4
      exact (unfoldAt_iff D W W' P (Q' + 1) P Q' false x rfl h5).1
        (h W P (Q' + 1) h1 h2 h3 false (by simp) x h5 h6 W' ι h7 h8 h9 h10 hR)
    · obtain ⟨rfl, rfl⟩ : P = P' + 1 ∧ Q = Q' := by simpa using h4
      exact (unfoldAt_iff D W W' (P' + 1) Q P' Q true x (by omega) h5).1
        (h W (P' + 1) Q h1 h2 h3 true (by simp) x h5 h6 W' ι h7 h8 h9 h10 hR)
  · intro h W P Q h1 h2 h3 s h4 x h5 h6 W' ι h7 h8 h9 h10 hR
    cases s
    · have h4' : 1 ≤ Q := by simpa using h4
      exact (unfoldAt_iff D W W' P Q P (Q - 1) false x (by omega) h5).2
        (h W W' P Q P (Q - 1) false x ι ⟨h1, h2, h3, by simp; omega, h5, h6, h7, h8, h9, h10⟩ hR)
    · have h4' : 1 ≤ P := by simpa using h4
      exact (unfoldAt_iff D W W' P Q (P - 1) Q true x (by omega) h5).2
        (h W W' P Q (P - 1) Q true x ι ⟨h1, h2, h3, by simp; omega, h5, h6, h7, h8, h9, h10⟩ hR)

theorem unfolding_iff (D : D7) : IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.Unfolding D ↔ IndefiniteRowSideFullHecke.LatticeTensorUnfolding.Unfolding D :=
  letI := D.host.cmStar
  setting_iff D fun W W' ι => ∀ y : W'.V, y ∈ W'.L0 ↔ ι y ∈ W.L0

end GlobalTheory.UnfoldingCompare
