import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanCommutant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineMemInfPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeCommTranslateStatement

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ZFinAssembly

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

omit [NumberField E] in

theorem foldr_mem (A : Submodule ℂ (GAd σ J → ℂ)) (hD : ∀ β, IsRealLine σ J β → ∀ ψ ∈ A, lineDer β ψ ∈ A)
    {l : List (ℝ → GAd σ J)} (hl : ∀ γ ∈ l, IsRealLine σ J γ) {ψ : GAd σ J → ℂ} (hψ : ψ ∈ A) :
    l.foldr lineDer ψ ∈ A := by
  induction l with
  | nil => exact hψ
  | cons γ l ih => exact hD γ (hl γ (by simp)) _ (ih fun δ hδ => hl δ (by simp [hδ]))

omit [NumberField E] in

theorem dop_mem (A : Submodule ℂ (GAd σ J → ℂ)) (hD : ∀ β, IsRealLine σ J β → ∀ ψ ∈ A, lineDer β ψ ∈ A)
    {z : List (ℝ → GAd σ J) →₀ ℂ} (hz : ∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ) {ψ : GAd σ J → ℂ} (hψ : ψ ∈ A) :
    dop z ψ ∈ A := by
  have e : dop z ψ = ∑ l ∈ z.support, z l • l.foldr lineDer ψ := by
    funext g
    simp [dop, Finsupp.sum, Finset.sum_apply]
  rw [e]
  exact A.sum_mem fun l hl => A.smul_mem _ (foldr_mem A hD (hz l hl) hψ)

theorem dop_lineDer {z : List (ℝ → GAd σ J) →₀ ℂ} (hz : IsCentral σ J z) {ψ : GAd σ J → ℂ} (hψ : IsSm σ J ψ)
    {β : ℝ → GAd σ J} (hβ : IsRealLine σ J β) : lineDer β (dop z ψ) = dop z (lineDer β ψ) := by
  funext g
  have e : (fun t => dop z ψ (g * β t)) = fun t => dop z (fun x => ψ (x * β t)) g :=
    funext fun t => (hz.2 ψ hψ (β t) (GlobalTheory.T.real_line_mem_inf_points F E σ n J β hβ t) g).symm
  have hd : HasDerivAt (fun t => dop z (fun x => ψ (x * β t)) g) (dop z (lineDer β ψ) g) 0 := by
    simp only [dop, Finsupp.sum]
    exact HasDerivAt.fun_sum fun l hl =>
      (GlobalTheory.T.line_derivative_comm_translate F E σ n J ψ hψ l (hz.1 l hl) β hβ g).const_mul (z l)
  show deriv (fun t => dop z ψ (g * β t)) 0 = _
  rw [e]
  exact hd.deriv

def derOp (A : Submodule ℂ (GAd σ J → ℂ)) (hS : ∀ ψ ∈ A, IsSm σ J ψ)
    (hD : ∀ β, IsRealLine σ J β → ∀ ψ ∈ A, lineDer β ψ ∈ A) (β : ℝ → GAd σ J) (hβ : IsRealLine σ J β) :
    Module.End ℂ A where
  toFun x := ⟨lineDer β x, hD β hβ x x.2⟩
  map_add' x y := Subtype.ext (lineDer_add (hS x x.2) (hS y y.2) hβ)
  map_smul' a x := Subtype.ext (lineDer_smul a x β)

def trOp (A : Submodule ℂ (GAd σ J → ℂ)) (k : GAd σ J) (hT : ∀ ψ ∈ A, (fun x => ψ (x * k)) ∈ A) :
    Module.End ℂ A where
  toFun x := ⟨fun g => (x : GAd σ J → ℂ) (g * k), hT x x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cenOp (A : Submodule ℂ (GAd σ J → ℂ)) (hS : ∀ ψ ∈ A, IsSm σ J ψ)
    (hD : ∀ β, IsRealLine σ J β → ∀ ψ ∈ A, lineDer β ψ ∈ A) (z : List (ℝ → GAd σ J) →₀ ℂ)
    (hz : IsCentral σ J z) : Module.End ℂ A where
  toFun x := ⟨dop z x, dop_mem A hD hz.1 x.2⟩
  map_add' x y := Subtype.ext (dop_add hz.1 (hS x x.2) (hS y y.2))
  map_smul' a x := Subtype.ext (dop_smul z a x)

theorem finiteDimensional_span_dop : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (A : Submodule ℂ (GAd σ J → ℂ)) (K : Set (GAd σ J)), (∀ k ∈ K, k ∈ infPts σ J) →
    (∀ ψ ∈ A, IsSm σ J ψ) → (∀ β, IsRealLine σ J β → ∀ ψ ∈ A, lineDer β ψ ∈ A) →
    (∀ k ∈ K, ∀ ψ ∈ A, (fun x => ψ (x * k)) ∈ A) → Module.rank ℂ A ≤ Cardinal.aleph0 →
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GAd σ J → ℂ)), StrictMono N → (∀ i, N i ≤ A) →
      (∀ i β, IsRealLine σ J β → ∀ ψ ∈ N i, lineDer β ψ ∈ N i) → (∀ i, ∀ k ∈ K, ∀ ψ ∈ N i, (fun x => ψ (x * k)) ∈ N i) →
      m ≤ L) →
    ∀ ψ₀ ∈ A, FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z ψ₀}) := by
  intro F E _ _ _ _ _ σ n J A K hK hS hD hT hr ⟨L, hL⟩ ψ₀ h₀
  let S : Set (Module.End ℂ A) :=
    {s | (∃ β, ∃ hβ : IsRealLine σ J β, s = derOp A hS hD β hβ) ∨ ∃ k, ∃ hk : k ∈ K, s = trOp A k (hT k hk)}
  have hL' : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ A), StrictMono N →
      (∀ i, ∀ s ∈ S, ∀ x ∈ N i, s x ∈ N i) → m ≤ L := by
    refine ⟨L, fun m N hN hst => hL m (fun i => (N i).map A.subtype) (fun i j hij => lt_of_le_of_ne
      (Submodule.map_mono (hN hij).le)
      (fun e => (hN hij).ne (Submodule.map_injective_of_injective A.injective_subtype e)))
      (fun i => Submodule.map_subtype_le _ _) ?_ ?_⟩
    · intro i β hβ ψ hψ
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hψ
      exact Submodule.mem_map.2 ⟨derOp A hS hD β hβ x, hst i _ (Or.inl ⟨β, hβ, rfl⟩) x hx, rfl⟩
    · intro i k hk ψ hψ
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hψ
      exact Submodule.mem_map.2 ⟨trOp A k (hT k hk) x, hst i _ (Or.inr ⟨k, hk, rfl⟩) x hx, rfl⟩
  have hcomm : ∀ z (hz : IsCentral σ J z), ∀ s ∈ S, s * cenOp A hS hD z hz = cenOp A hS hD z hz * s := by
    rintro z hz s (⟨β, hβ, rfl⟩ | ⟨k, hk, rfl⟩) <;> refine LinearMap.ext fun x => Subtype.ext ?_
    · exact dop_lineDer hz (hS x x.2) hβ
    · exact funext fun g => (hz.2 x (hS x x.2) k (hK k hk) g).symm
  haveI := GlobalTheory.FiniteLengthCommutant.finiteDimensional_span_commutant A S hr hL' ⟨ψ₀, h₀⟩
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ {w : A | ∃ T : Module.End ℂ A,
    (∀ s ∈ S, s * T = T * s) ∧ T ⟨ψ₀, h₀⟩ = w}).map A.subtype) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  exact Submodule.mem_map.2 ⟨cenOp A hS hD z hz ⟨ψ₀, h₀⟩,
    Submodule.subset_span ⟨_, hcomm z hz, rfl⟩, rfl⟩

end GlobalTheory.ZFinAssembly
