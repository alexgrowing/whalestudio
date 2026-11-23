import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

namespace GlobalTheory.AnisoCocompact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev finP : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

abbrev infP : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom

abbrev ratQ (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J

abbrev matA {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : HA (AF F) σ J) :
    Matrix (Fin M) (Fin M) (AF F ⊗[F] E) := (HA.mat (AF F) σ J g).1

theorem exists_finite_part (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) : ∃ C : Set (Af F ⊗[F] E), IsCompact C ∧
    ∀ g : HA (AF F) σ J, ∃ γ ∈ ratQ σ J, ∀ B : Matrix (Fin M) (Fin M) E, (∀ a b, IsIntegral ℤ (B a b)) →
      ∀ a b, finP ((matA (g * γ) * B.map (inclR (F := F) (AF F))) a b) ∈ C := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj σ J
  obtain ⟨S, hS⟩ := GlobalTheory.Mem.ClassFinite.exists_finset_classes F E σ hcm M J hJ _ (GlobalTheory.Mass.isOpen_stdLevel σ J)
  obtain ⟨C, hC, hCe⟩ := (GlobalTheory.Mass.intTens_open_compact F E).2
  obtain ⟨C₁, hC₁, hCe₁⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact_mul hC
    (S.finite_toSet.image fun s => (HA.mat (Af F) σ J s⁻¹).1)
  refine ⟨C₁, hC₁, fun g => ?_⟩
  obtain ⟨γ₀, s, hs, k, hk, e⟩ := hS (π g⁻¹)
  obtain ⟨γ, hγ, hγe⟩ : (γ₀.1 : HA (Af F) σ J) ∈ (GlobalTheory.Mass.ratIn (AF F) σ J).map π := by
    rw [hπ.map_ratIn]; exact γ₀.2
  refine ⟨γ, hγ, fun B hBi a b => ?_⟩
  have e' : π (g * γ) = k⁻¹ * s⁻¹ := by
    have e1 : π g⁻¹ = π γ * (s * k) := by rw [hγe]; exact e
    rw [map_mul, ← inv_inv g, map_inv, e1]; group
  generalize g * γ = x at e'
  have e3 : (matA x).map finP = (HA.mat (Af F) σ J k⁻¹).1 * (HA.mat (Af F) σ J s⁻¹).1 := by
    have := congrArg Units.val (hπ x)
    rw [e'] at this
    exact this.symm
  have e4 : finP ((matA x * B.map (inclR (F := F) (AF F))) a b) =
      ((matA x).map finP * (B.map (inclR (F := F) (AF F))).map finP) a b :=
    congrFun (congrFun (Matrix.map_mul (L := matA x) (M := B.map (inclR (F := F) (AF F))) (f := finP)) a) b
  rw [e4, e3]
  refine hCe₁ _ ⟨s, hs, rfl⟩ _ _ (fun a b => hCe _ ((GlobalTheory.Mass.mem_stdLevel _ _ _).1 (inv_mem hk) a b).1)
    (fun a b => hCe _ ?_) a b
  exact Subring.subset_closure (Or.inl ⟨⟨B a b, ⟨_, hBi a b⟩, rfl⟩, rfl⟩)

theorem exists_real_part (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : J.det ≠ 0) (han : ∀ x, x ≠ 0 → Formalism.UG.hform (σ : E →+* E) J x x ≠ 0)
    {I : Type} [Fintype I] {τ : I → (E →+* ℂ)} (hτ : GlobalTheory.Mem.Vol.IsCMFam τ)
    {θ : I → (Ainf F ⊗[F] E →+* ℂ)} (hθ : ∀ ρ, Formalism.MainNotions.StandardLattice.IsInfEmb (τ ρ) (θ ρ)) :
    ∃ (R : ℝ) (𝓒 : Set (Matrix (Fin M) (Fin M) E)), 𝓒.Finite ∧ ∀ x : HA (AF F) σ J,
      ∃ u ∈ ratQ σ J, ∃ B : Matrix (Fin M) (Fin M) E, ∃ N ∈ 𝓒,
        matA u = (B * N).map (inclR (F := F) (AF F)) ∧ (∀ a b, IsIntegral ℤ (B a b)) ∧
        ∀ a b ρ, ‖θ ρ (infP ((matA x * B.map (inclR (F := F) (AF F))) a b))‖ ≤ R := by
  haveI := hcm.2.1
  obtain ⟨R, 𝓒, h𝓒, H⟩ := GlobalTheory.Mem.AnisoQuotient.exists_bounded_unitary (σ := (σ : E →+* E)) hτ
    (fun ρ x => hcm.2.2.2 _ x) hJ han
  refine ⟨R, 𝓒, h𝓒, fun x => ?_⟩
  let p : AF F ⊗[F] E →+* (I → ℂ) := Pi.ringHom fun ρ => (θ ρ).comp infP
  have hp : ∀ N : Matrix (Fin M) (Fin M) E, (N.map (inclR (F := F) (AF F))).map p = N.map (Pi.ringHom τ) :=
    fun N => by ext i j ρ; exact (hθ ρ).1 _
  have hev : ∀ (ρ : I) (X : Matrix (Fin M) (Fin M) (I → ℂ)), X.map (Pi.evalRingHom (fun _ => ℂ) ρ) = X.map (fun z => z ρ) :=
    fun _ _ => rfl
  obtain ⟨u, hu, B, N, hN, hum, hBi, hBR⟩ := H ((matA x).map p) (by
    ext i j ρ
    have h1 := congrFun (congrFun (GlobalTheory.Mem.VolExists.infMat_unitary J hcm (hθ ρ) x) i) j
    have h2 : ((Formalism.UG.cT (starRingEnd (I → ℂ)) ((matA x).map p) * J.map (Pi.ringHom τ) * (matA x).map p).map
        (Pi.evalRingHom (fun _ => ℂ) ρ)) = (Formalism.MainNotions.StandardLattice.infMat σ J (θ ρ) x).conjTranspose * J.map (τ ρ) *
        Formalism.MainNotions.StandardLattice.infMat σ J (θ ρ) x := by
      have e1 : ((matA x).map p).map (Pi.evalRingHom (fun _ => ℂ) ρ) = Formalism.MainNotions.StandardLattice.infMat σ J (θ ρ) x := by
        ext a b; rfl
      have e2 : (Formalism.UG.cT (starRingEnd (I → ℂ)) ((matA x).map p)).map (Pi.evalRingHom (fun _ => ℂ) ρ) =
          (Formalism.MainNotions.StandardLattice.infMat σ J (θ ρ) x).conjTranspose := by
        rw [← e1]; ext a b; rfl
      have e3 : (J.map (Pi.ringHom τ)).map (Pi.evalRingHom (fun _ => ℂ) ρ) = J.map (τ ρ) := by
        ext a b; rfl
      rw [Matrix.map_mul, Matrix.map_mul, e1, e2, e3]
    have h3 := congrFun (congrFun h2 i) j
    simp only [Matrix.map_apply, Pi.evalRingHom_apply] at h3
    rw [h3, h1]
    rfl)
  refine ⟨⟨_, GlobalTheory.Mem.ClassFinite.baseChange_mem (AF F) σ J u hu⟩, ⟨u, hu, rfl⟩, B, N, hN,
    congrArg (fun X => X.map (inclR (F := F) (AF F))) hum, hBi, fun a b ρ => ?_⟩
  have := hBR a b
  rw [← hp, ← Matrix.map_mul] at this
  exact (norm_le_pi_norm (p ((matA x * B.map (inclR (F := F) (AF F))) a b)) ρ).trans this

theorem exists_compact (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (han : ∀ x, x ≠ 0 → Formalism.UG.hform (σ : E →+* E) J x x ≠ 0) :
    ∃ K : Set (HA (AF F) σ J), IsCompact K ∧ ∀ g, ∃ γ ∈ ratQ σ J, ∃ k ∈ K, g = γ * k := by
  haveI := hcm.1
  let τ : InfinitePlace E → (E →+* ℂ) := fun w => w.embedding
  have hτ : GlobalTheory.Mem.Vol.IsCMFam τ := by
    have : (fun w => InfinitePlace.mk (τ w)) = id := funext fun w => InfinitePlace.mk_embedding w
    unfold GlobalTheory.Mem.Vol.IsCMFam; rw [this]; exact Function.bijective_id
  choose θ hθ1 hθ2 using fun ρ => GlobalTheory.InfAdeleCM.exists_hom (F := F) (τ ρ)
  have hθ : ∀ ρ, Formalism.MainNotions.StandardLattice.IsInfEmb (τ ρ) (θ ρ) := fun ρ => ⟨hθ1 ρ, hθ2 ρ⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (HA (AF F) σ J) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ J))
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨C₁, hC₁, H₁⟩ := exists_finite_part σ hcm J hJ
  obtain ⟨R, 𝓒, h𝓒, H₂⟩ := exists_real_part σ hcm J hJ.2 han hτ hθ
  obtain ⟨C₂, hC₂, hCe₂⟩ := GlobalTheory.Mem.VolExists.exists_compact_adele hcm hτ hθ R C₁ hC₁
  obtain ⟨C₃, hC₃, hCe₃⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact_mul ((hC₂.insert 0).insert 1)
    (h𝓒.image fun N => N.map (inclR (F := F) (AF F)))
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF F) σ J hJ.2 C₃ hC₃
  refine ⟨K⁻¹, hK.inv, fun g => ?_⟩
  obtain ⟨γ, hγ, h₁⟩ := H₁ g⁻¹
  obtain ⟨u, hu, B, N, hN, hum, hBi, hBR⟩ := H₂ (g⁻¹ * γ)
  refine ⟨γ * u, mul_mem hγ hu, (g⁻¹ * γ * u)⁻¹, Set.inv_mem_inv.2 (hKe _ fun a b => ?_), by group⟩
  have e : matA (g⁻¹ * γ * u) = matA (g⁻¹ * γ) * B.map (inclR (F := F) (AF F)) *
      N.map (inclR (F := F) (AF F)) * 1 := by
    rw [show matA (g⁻¹ * γ * u) = matA (g⁻¹ * γ) * matA u from rfl, hum, Matrix.map_mul, Matrix.mul_one,
      Matrix.mul_assoc]
  change matA (g⁻¹ * γ * u) a b ∈ C₃
  rw [e]
  refine hCe₃ _ ⟨N, hN, rfl⟩ _ _ (fun a b => Or.inr (Or.inr (hCe₂ _ (h₁ B hBi a b) (hBR a b)))) (fun a b => ?_) a b
  rw [Matrix.one_apply]
  split_ifs
  exacts [Or.inl rfl, Or.inr (Or.inl rfl)]

end GlobalTheory.AnisoCocompact
