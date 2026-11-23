import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsRationalDblCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAdeleE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteClassSetHermitianUnitaryOpenLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassBotBotOfInfinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantStabilizerIwasawaLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSig
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteCompactArchimedeanMaximal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenStabOfDefinite
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cont

namespace GlobalTheory.DefDoubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem commute_theta_of_definite {σ : E →ₐ[F] E} {B : Base F E} {n : ℕ} {X : Spc F E n}
    (hX : X.IsHerm σ B n 0 ∨ X.IsHerm σ B 0 n) (w : InfinitePlace F) (A : Matrix (Fin n) (Fin n) ℂ) :
    Commute A (X.θ w) := by
  rcases hX with h | h
  · rw [GlobalTheory.DefiniteCartan.eq_one_of_hasSig (h.sig w) (h.cartan w)]
    exact Commute.one_right A
  · rw [GlobalTheory.DefiniteStab.eq_neg_one_of_hasSig (h.sig w) (h.cartan w)]
    exact (Commute.one_right A).neg_right

theorem mem_of_latHat {σ : E →ₐ[F] E} {B : Base F E} {n : ℕ} {X : Spc F E n}
    (hX : X.IsHerm σ B n 0 ∨ X.IsHerm σ B 0 n) {K : Subgroup (UA σ X.J)} (hK : IsStab B K) (g : UA σ X.J)
    (h1 : ∀ z ∈ latHat X, mat g *ᵥ z ∈ latHat X) (h2 : ∀ z ∈ latHat X, mat g⁻¹ *ᵥ z ∈ latHat X) : g ∈ K :=
  (hK g).2 ⟨fun w => commute_theta_of_definite hX w _, fun z hz => ⟨h1 z hz, h2 z hz⟩⟩

end GlobalTheory.DefDoubling

namespace GlobalTheory.DefDoubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mulVec_mem_latHat_of_fin_one {σ : E →ₐ[F] E} {n : ℕ} (X : Spc F E n)
    {π : HA (AF F) σ X.Jᵀ →* HA (Af F) σ X.Jᵀ} (hπ : GlobalTheory.Mass.IsFinProj σ X.Jᵀ π) {g : GAd σ X.Jᵀ} (hg : π g = 1)
    {z : Fin n → AE F E} (hz : z ∈ latHat X) : (matHom (AF F) σ X.Jᵀ g).1 *ᵥ z ∈ latHat X := by
  have hm : ((matHom (AF F) σ X.Jᵀ g).1).map (GlobalTheory.KBridge.finT F E) = 1 := by
    have h := congrArg Units.val (hπ g)
    rw [hg] at h
    exact h.symm
  rw [GlobalTheory.KBridge.mem_latHat_iff] at hz ⊢
  obtain ⟨hi, hf⟩ := hz
  refine ⟨fun i => ?_, ?_⟩
  · have e : ((GlobalTheory.KBridge.infT F E).toRingHom ∘ z) = 0 := funext fun j => hi j
    refine (RingHom.map_mulVec (GlobalTheory.KBridge.infT F E).toRingHom (matHom (AF F) σ X.Jᵀ g).1 z i).trans ?_
    rw [e, Matrix.mulVec_zero]
    rfl
  · have e : (fun i => GlobalTheory.KBridge.finT F E (((matHom (AF F) σ X.Jᵀ g).1 *ᵥ z) i)) =
        ((matHom (AF F) σ X.Jᵀ g).1.map (GlobalTheory.KBridge.finT F E)) *ᵥ fun i => GlobalTheory.KBridge.finT F E (z i) :=
      funext fun i => RingHom.map_mulVec (GlobalTheory.KBridge.finT F E).toRingHom _ _ i
    rw [e, hm, Matrix.one_mulVec]
    exact hf

theorem exists_finite_doubleCosets : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ {B : Base F E} {n : ℕ} {X : Spc F E n},
    (X.IsHerm σ B n 0 ∨ X.IsHerm σ B 0 n) → ∀ {K : Subgroup (UA σ X.J)}, IsStab B K →
    ∃ A : Finset (UA σ X.J), ∀ x, ∃ a ∈ A, ∃ γ ∈ ratU σ X.J, ∃ k ∈ K, x = γ * a * k := by
  intro F E _ _ _ _ _ σ hcm B n X hX K hK
  classical
  obtain ⟨hL, hJ'⟩ : X.L.IsLattice E ∧ IsHermND σ X.Jᵀ := by
    rcases hX with h | h
    exacts [⟨h.lat, GlobalTheory.IwLine.isHermND_transpose h⟩, ⟨h.lat, GlobalTheory.IwLine.isHermND_transpose h⟩]
  haveI : X.L.IsLattice E := hL
  haveI : IsTopologicalGroup (HA (AF F) σ X.Jᵀ) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ X.Jᵀ))
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj σ X.Jᵀ
  let e := GlobalTheory.IwLine.ofGAd σ X.J
  let K₀ : Subgroup (GAd σ X.Jᵀ) := K.comap e.toMonoidHom
  have hmem : ∀ g : GAd σ X.Jᵀ, (∀ z ∈ latHat X, (matHom (AF F) σ X.Jᵀ g).1 *ᵥ z ∈ latHat X) →
      (∀ z ∈ latHat X, (matHom (AF F) σ X.Jᵀ g⁻¹).1 *ᵥ z ∈ latHat X) → g ∈ K₀ := by
    intro g h1 h2
    refine GlobalTheory.DefDoubling.mem_of_latHat hX hK (e g) (fun z hz => ?_) (fun z hz => ?_)
    · rw [GlobalTheory.IwLine.mat_ofGAd]; exact h1 z hz
    · rw [← map_inv, GlobalTheory.IwLine.mat_ofGAd]; exact h2 z hz
  have hlev : levelOpen σ X.Jᵀ X.L ≤ K₀ := fun g hg =>
    hmem g (fun z hz => GlobalTheory.KBridge.mulVec_mem_latHat σ X hL.fg hg hz)
      (fun z hz => GlobalTheory.KBridge.mulVec_mem_latHat σ X hL.fg (inv_mem hg) hz)
  have hK₀ : IsOpen (K₀ : Set (GAd σ X.Jᵀ)) := Subgroup.isOpen_mono hlev (isOpen_levelOpen σ X.Jᵀ X.L)
  have hker : ∀ g, π g = 1 → g ∈ K₀ := fun g hg =>
    hmem g (fun z hz => mulVec_mem_latHat_of_fin_one X hπ hg hz)
      (fun z hz => mulVec_mem_latHat_of_fin_one X hπ (by rw [map_inv, hg, inv_one]) hz)
  have hback : ∀ g, π g ∈ K₀.map π → g ∈ K₀ := by
    rintro g ⟨k, hk, hkg⟩
    have h : k⁻¹ * g ∈ K₀ := hker _ (by rw [map_mul, map_inv, hkg, inv_mul_cancel])
    simpa using K₀.mul_mem hk h
  have hK' : IsOpen ((K₀.map π : Subgroup (HA (Af F) σ X.Jᵀ)) : Set (HA (Af F) σ X.Jᵀ)) :=
    GlobalTheory.Mass.Model.isOpen_of_comap hπ (Subgroup.isOpen_mono (Subgroup.le_comap_map π K₀) hK₀)
  obtain ⟨S, hS⟩ := GlobalTheory.Mem.ClassFinite.exists_finset_classes F E σ hcm n X.Jᵀ hJ' _ hK'
  obtain ⟨sec, -, hsec⟩ := GlobalTheory.Mass.Model.exists_section hπ
  refine ⟨S.image (fun s => e (sec s)), fun x => ?_⟩
  obtain ⟨γ, s, hs, k, hk, hx⟩ := hS (π (e.symm x))
  have hγ : (γ.1 : HA (Af F) σ X.Jᵀ) ∈ (GlobalTheory.Mass.ratIn (AF F) σ X.Jᵀ).map π := by
    rw [hπ.map_ratIn]; exact γ.2
  obtain ⟨γ₀, hγ₀, hγπ⟩ := hγ
  have hw : (γ₀ * sec s)⁻¹ * e.symm x ∈ K₀ := by
    refine hback _ ?_
    let γ' : HA (Af F) σ X.Jᵀ := γ.1
    have hx' : π (e.symm x) = γ' * (s * k) := hx
    rw [map_mul, map_inv, map_mul, hγπ, hsec, hx', show (γ' * s)⁻¹ * (γ' * (s * k)) = k by group]
    exact hk
  refine ⟨e (sec s), Finset.mem_image_of_mem _ hs, e γ₀, ?_, e ((γ₀ * sec s)⁻¹ * e.symm x), hw, ?_⟩
  · obtain ⟨u, -, hu⟩ := hγ₀
    exact ⟨u, hu⟩
  · rw [← map_mul, ← map_mul, ← mul_assoc, mul_inv_cancel, one_mul, MulEquiv.apply_symm_apply]

end GlobalTheory.DefDoubling
