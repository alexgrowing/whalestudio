import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat

noncomputable section

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.ThK.SoPolSplit

theorem exists_interp {α : Type} (K : Submodule ℂ (α → ℂ)) [FiniteDimensional ℂ K] :
    ∃ (r : ℕ) (p : Fin r → α) (e : Fin r → α → ℂ), (∀ s, e s ∈ K) ∧ ∀ f ∈ K, f = ∑ s, f (p s) • e s := by
  classical
  let ev : α → K →ₗ[ℂ] ℂ := fun x => (LinearMap.proj x).comp K.subtype
  let W : Finset α → Submodule ℂ K := fun s => ⨅ x ∈ s, LinearMap.ker (ev x)
  have hW : ∀ s (v : K), v ∈ W s ↔ ∀ x ∈ s, (v : α → ℂ) x = 0 := by
    intro s v
    simp [W, ev, Submodule.mem_iInf, LinearMap.mem_ker]
  obtain ⟨M, ⟨s, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal (Set.range W) ⟨_, ⟨∅, rfl⟩⟩
  have hbot : ∀ v : K, v ∈ W s → v = 0 := by
    intro v hv
    ext x
    have hle : W (insert x s) ≤ W s := fun w hw =>
      (hW _ _).2 fun y hy => (hW _ _).1 hw y (Finset.mem_insert_of_mem hy)
    have heq : W (insert x s) = W s := by
      by_contra hne
      exact hmin _ ⟨_, rfl⟩ (lt_of_le_of_ne hle hne)
    have hv' : v ∈ W (insert x s) := heq ▸ hv
    simpa using (hW _ _).1 hv' x (Finset.mem_insert_self x s)
  let p : Fin s.card → α := fun i => (s.equivFin.symm i : α)
  let R : K →ₗ[ℂ] (Fin s.card → ℂ) := LinearMap.pi fun i => ev (p i)
  have hker : LinearMap.ker R = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    apply hbot
    rw [hW]
    intro x hx
    have := congrFun hv (s.equivFin ⟨x, hx⟩)
    simpa [R, ev, p] using this
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hker
  refine ⟨s.card, p, fun i => (L (Pi.single i 1) : α → ℂ), fun i => (L _).2, ?_⟩
  intro f hf
  have h1 : (⟨f, hf⟩ : K) = L (R ⟨f, hf⟩) := by
    rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
  have h2 : R ⟨f, hf⟩ = ∑ i, f (p i) • (Pi.single i 1 : Fin s.card → ℂ) := by
    ext j
    simp [R, ev, Finset.sum_apply, Pi.single_apply]
  have h3 := congrArg Subtype.val h1
  rw [h2, map_sum] at h3
  simpa [map_smul, Submodule.coe_sum] using h3

end GlobalTheory.ThK.SoPolSplit

namespace GlobalTheory.ThK.SoPolSplit

variable {F : Type} [Field F] [NumberField F]

def finPart {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (x : κ → AF F) : ℂ :=
  ∏ᶠ v, φ v fun i => evFin F v (x i)

def glue {κ : Type} (a : κ → mixedEmbedding.mixedSpace F) (y : κ → AF F) : κ → AF F :=
  fun i => (show Ainf F × Af F from
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), (y i).2))

theorem evI_glue {κ : Type} (a : κ → mixedEmbedding.mixedSpace F) (y : κ → AF F) :
    (fun i => evI F (glue a y i)) = a := by
  funext i
  simp [glue, evI]

theorem finPart_glue {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (a : κ → mixedEmbedding.mixedSpace F)
    (y : κ → AF F) : finPart φ (glue a y) = finPart φ y := rfl

theorem glue_self {κ : Type} (x : κ → AF F) : glue (fun i => evI F (x i)) x = x := by
  funext i
  change (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1),
    (x i).2) : Ainf F × Af F) = x i
  rw [RingEquiv.symm_apply_apply]
  rfl

theorem pure_eq {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (x : κ → AF F) :
    pure f φ x = f (fun i => evI F (x i)) * finPart φ x := rfl

end GlobalTheory.ThK.SoPolSplit

namespace GlobalTheory.ThK.SoPolSplit

variable {F : Type} [Field F] [NumberField F]

theorem pure_smul {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    pure (c • f) φ = c • pure f φ := by
  funext y
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem exists_sum_of_mem_span {κ : Type} [Fintype κ] (P : SInf F κ → Prop) (Q : (∀ v : Pl F, (κ → Fv F v) → ℂ) → Prop)
    (hP : ∀ (c : ℂ) f, P f → P (c • f)) (S : Set ((κ → AF F) → ℂ))
    (hS : ∀ Φ ∈ S, ∃ f φ, P f ∧ Q φ ∧ Φ = pure f φ) {Φ : (κ → AF F) → ℂ} (h : Φ ∈ Submodule.span ℂ S) :
    ∃ (m : ℕ) (f : Fin m → SInf F κ) (φ : Fin m → ∀ v : Pl F, (κ → Fv F v) → ℂ),
      (∀ i, P (f i) ∧ Q (φ i)) ∧ Φ = ∑ i, pure (f i) (φ i) := by
  obtain ⟨n, c, x, hx⟩ := Submodule.mem_span_set'.1 h
  choose f φ hf hφ hpure using fun i => hS _ (x i).2
  refine ⟨n, fun i => c i • f i, φ, fun i => ⟨hP _ _ (hf i), hφ i⟩, ?_⟩
  rw [← hx]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hpure i, pure_smul]

theorem sch_sum_apply {κ : Type} [Fintype κ] {ι : Type} (s : Finset ι) (g : ι → SInf F κ) (y : κ → mixedEmbedding.mixedSpace F) :
    (∑ i ∈ s, g i) y = ∑ i ∈ s, g i y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, SchwartzMap.add_apply, ih]

theorem exists_sum_pure_pol_so : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∃ (m : ℕ) (f : Fin m → SInf F (Fin a' × Fin (a + a')))
      (φ : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (∀ i, f i ∈ G.M'.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ i v = G.M'.vac v) ∧
        φ i B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁) ∧ Φ = ∑ i, pure (f i) (φ i) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' _ Φ hΦ
  classical
  rw [Submodule.mem_inf] at hΦ
  obtain ⟨hPol, hSo⟩ := hΦ

  obtain ⟨m₁, f₁, φ₁, hf₁, hΦ₁⟩ := exists_sum_of_mem_span (fun f => f ∈ G.M'.Pol B.ψ B.emb) (fun _ => True)
    (fun c f hf => Submodule.smul_mem _ c hf) _
    (fun Φ hΦ => by obtain ⟨f, hf, φ, _, _, h⟩ := hΦ; exact ⟨f, φ, hf, trivial, h⟩) hPol

  obtain ⟨m₂, h₂, ψ₂, hψ₂, hΦ₂⟩ := exists_sum_of_mem_span (fun _ => True)
    (fun φ => (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) ∧
      φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁)
    (fun _ _ _ => trivial) _ (fun Φ hΦ => by obtain ⟨f, φ, h1, h2, h3, h⟩ := hΦ; exact ⟨f, φ, trivial, ⟨h1, h2, h3⟩, h⟩) hSo

  let k : Fin m₂ → (Fin a' × Fin (a + a') → AF F) → ℂ := fun j => finPart (ψ₂ j)
  let K := Submodule.span ℂ (Set.range k)
  haveI : FiniteDimensional ℂ K := FiniteDimensional.span_of_finite ℂ (Set.finite_range k)
  obtain ⟨r, p, e, he, hrep⟩ := exists_interp K
  choose c hc using fun s => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (he s)
  let H : Fin r → SInf F (Fin a' × Fin (a + a')) := fun s => ∑ i, finPart (φ₁ i) (p s) • f₁ i
  have hH : ∀ s, H s ∈ G.M'.Pol B.ψ B.emb := fun s =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hf₁ i).1
  have key : ∀ x, Φ x = ∑ s, H s (fun i => evI F (x i)) * e s x := by
    intro x
    have hmemK : (fun y => Φ (glue (fun i => evI F (x i)) y)) ∈ K := by
      have : (fun y => Φ (glue (fun i => evI F (x i)) y)) = ∑ j, h₂ j (fun i => evI F (x i)) • k j := by
        funext y
        rw [hΦ₂]
        simp only [Finset.sum_apply, pure_eq, evI_glue, finPart_glue, Pi.smul_apply, smul_eq_mul, k]
      rw [this]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have h1 := congrFun (hrep _ hmemK) x
    simp only [glue_self, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    rw [hΦ₁]
    simp only [Finset.sum_apply, pure_eq, evI_glue, finPart_glue, H, sch_sum_apply, SchwartzMap.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine ⟨r * m₂, fun t => c (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2 • H (finProdFinEquiv.symm t).1,
    fun t => ψ₂ (finProdFinEquiv.symm t).2, fun t => ⟨Submodule.smul_mem _ _ (hH _), (hψ₂ _).2⟩, ?_⟩
  funext x
  rw [key x, Finset.sum_apply]
  rw [Fintype.sum_equiv finProdFinEquiv.symm _ (fun q : Fin r × Fin m₂ => pure (c q.1 q.2 • H q.1) (ψ₂ q.2) x)
    (fun t => rfl), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← hc s]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, pure_eq, SchwartzMap.smul_apply, k]
  exact Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.ThK.SoPolSplit
