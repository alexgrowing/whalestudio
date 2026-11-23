import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipAugLeJacKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedLineKernelDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPlaceInducedIntertwinerExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedLocalPlaceExtensionStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock GlobalTheory.JacLineSplit

namespace GlobalTheory.JacLineSplit

section Abstract

variable {Φ I G : Type} [AddCommGroup Φ] [Module ℂ Φ] [AddCommGroup I] [Module ℂ I] [Group G]

theorem mem_of_map_twKer (π : Representation ℂ G I) (N : Subgroup G) (P : Φ →ₗ[ℂ] I) (S J A : Submodule ℂ Φ)
    (hAJ : A ≤ J) (q : G) (hsurj : ∀ f, ∃ φ ∈ S, P φ = f) (hker : ∀ φ ∈ S, P φ = 0 → φ ∈ A)
    (hlift : ∀ n ∈ N, ∀ ψ ∈ S, ∃ ψ₁ ∈ S, ψ₁ - ψ ∈ J ∧ P ψ₁ = π (q * n * q⁻¹) (P ψ)) :
    ∀ z ∈ twKer π N 1, ∀ ψ ∈ S, P ψ = π q z → ψ ∈ J := by
  have hM : twKer π N 1 ≤ ((J ⊓ S).map P).comap (π q) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, f, rfl⟩
    obtain ⟨ψ, hψ, hPψ⟩ := hsurj (π q f)
    obtain ⟨ψ₁, hψ₁, hJ, h1⟩ := hlift n n.2 ψ hψ
    refine ⟨ψ₁ - ψ, ⟨hJ, sub_mem hψ₁ hψ⟩, ?_⟩
    rw [map_sub, h1, hPψ]
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2; group
  intro z hz ψ hψ hPz
  obtain ⟨ζ, ⟨hζj, hζs⟩, hPζ⟩ := hM hz
  have h0 : ψ - ζ ∈ A := hker _ (sub_mem hψ hζs) (by rw [map_sub, hPz, hPζ, sub_self])
  simpa using add_mem (hAJ h0) hζj

theorem map_sub_sub (π : Representation ℂ G I) (P : Φ →ₗ[ℂ] I) (q : G) {φ φa φb : Φ} {fa fb : I}
    (hPa : P φa = π q fa) (hPb : P φb = π q fb) : P (φ - φa - φb) = π q (π q⁻¹ (P φ) - fa - fb) := by
  rw [map_sub, map_sub, hPa, hPb, map_sub, map_sub, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply]

theorem map_eig (π : Representation ℂ G I) (P : Φ →ₗ[ℂ] I) (q s : G) (C : ℂ) {φa φ₁ : Φ} {fa : I}
    (hPa : P φa = π q fa) (h1 : P φ₁ = π (q * s * q⁻¹) (P φa)) : P (φ₁ - C • φa) = π q (π s fa - C • fa) := by
  rw [map_sub, map_smul, h1, hPa, map_sub, map_smul]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2; group

end Abstract

theorem exists_positionOne_eigen : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ v, X.Good v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∃ φa ∈ SB (Fin a × Fin (a + a') → Fv F v), ∃ φb ∈ SB (Fin a × Fin (a + a') → Fv F v), φ - φa - φb ∈ GlobalTheory.JacquetLine.jacKer om H' v ∧ (∀ (x : (w.adicCompletion E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' (locIdele F w x) 1 m → m ∈ UAt σ G.W (evFin F v) → ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, m)) φa φ₁ → φ₁ - ((GlobalTheory.CtTyp.twAbs X.α ((a' : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) • φa ∈ GlobalTheory.JacquetLine.jacKer om H' v) ∧ (∀ (x : (w.adicCompletion E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' (locIdele F w x) 1 m → m ∈ UAt σ G.W (evFin F v) → ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, m)) φb φ₁ → φ₁ - ((GlobalTheory.CtTyp.twAbs X.β ((a : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) • φb ∈ GlobalTheory.JacquetLine.jacKer om H' v) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH' v hv w hw φ hφ
  have h2 : 2 ≤ a + a' := by have := hT.geo.aBig; omega
  obtain ⟨t, c', hlift, hlev⟩ := GlobalTheory.T.triple_adapted_local_place_extension F E σ B a a' G X om om' hT h2 d₁ W₁ H' i₀ i₁ hH' v hv w hw
  obtain ⟨P, c, hsurj, hker, hex, heq⟩ := GlobalTheory.T.good_place_induced_intertwiner_exists hKP F E σ B a a' G X om om' hT v hv t
  have hconj : ∀ g : GL (Fin (a + a')) (Fv F v), c' * g * c'⁻¹ = c * ((c⁻¹ * c') * g * (c⁻¹ * c')⁻¹) * c⁻¹ := by
    intro g; group
  have key := mem_of_map_twKer (indAA (Fv F v) a a' ![chrW X.α t, chrW X.β t]) (unipRad (Fv F v) (linePlace h2)) P
    (SB (Fin a × Fin (a + a') → Fv F v)) (GlobalTheory.JacquetLine.jacKer om H' v) (augAt om v)
    (GlobalTheory.JacquetLine.augAt_le_jacKer om H' v) (c⁻¹ * c') hsurj hker (by
      intro n hn ψ hψ
      obtain ⟨u, hu, huv, hmu⟩ := hlift n hn
      obtain ⟨ψ₁, hψ₁, hact⟩ := hex u huv ψ hψ
      exact ⟨ψ₁, hψ₁, GlobalTheory.JacquetLine.unipAug_le_jacKer om H' v
        (Submodule.subset_span ⟨u, hu, huv, ψ, hψ, ψ₁, hψ₁, hact, rfl⟩),
        heq u huv _ (by rw [hmu, hconj]) ψ hψ ψ₁ hψ₁ hact⟩)
  have hsm : ∀ j, IsSmoothChar ((![chrW X.α t, chrW X.β t] : Fin 2 → (Fv F v)ˣ →* ℂˣ) j) := by
    intro j; fin_cases j
    · exact GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous _
        (GlobalTheory.ChrWSmooth.continuous_chrW hT.chars.heckeα.1 t)
    · exact GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous _
        (GlobalTheory.ChrWSmooth.continuous_chrW hT.chars.heckeβ.1 t)
  have hun : ∀ j, IsUnitaryChar ((![chrW X.α t, chrW X.β t] : Fin 2 → (Fv F v)ˣ →* ℂˣ) j) := by
    intro j; fin_cases j
    · exact GlobalTheory.ChrWSmooth.isUnitaryChar_chrW _ t
    · exact GlobalTheory.ChrWSmooth.isUnitaryChar_chrW _ t
  obtain ⟨fa, fb, hsum, hea, heb⟩ := GlobalTheory.T.induced_line_kernel_decomposition (Fv F v) hKP.geometricLemmaFiltration a a' hT.geo.lt h2
    ![chrW X.α t, chrW X.β t] hsm hun (indAA (Fv F v) a a' ![chrW X.α t, chrW X.β t] (c⁻¹ * c')⁻¹ (P φ))
  obtain ⟨φa, hφa, hPa⟩ := hsurj (indAA (Fv F v) a a' ![chrW X.α t, chrW X.β t] (c⁻¹ * c') fa)
  obtain ⟨φb, hφb, hPb⟩ := hsurj (indAA (Fv F v) a a' ![chrW X.α t, chrW X.β t] (c⁻¹ * c') fb)
  refine ⟨φa, hφa, φb, hφb, ?_, ?_, ?_⟩
  · exact key _ hsum _ (sub_mem (sub_mem hφ hφa) hφb) (map_sub_sub _ P _ hPa hPb)
  · intro x m hm hmv φ₁ hφ₁ hact
    obtain ⟨y, hya, -, hlv⟩ := hlev x
    have h1 := heq m hmv _ (by rw [hlv m hm hmv, hconj]) φa hφa φ₁ hφ₁ hact
    rw [hya]
    exact key _ (hea y) _ (sub_mem hφ₁ (Submodule.smul_mem _ _ hφa)) (map_eig _ P _ _ _ hPa h1)
  · intro x m hm hmv φ₁ hφ₁ hact
    obtain ⟨y, -, hyb, hlv⟩ := hlev x
    have h1 := heq m hmv _ (by rw [hlv m hm hmv, hconj]) φb hφb φ₁ hφ₁ hact
    rw [hyb]
    exact key _ (heb y) _ (sub_mem hφ₁ (Submodule.smul_mem _ _ hφb)) (map_eig _ P _ _ _ hPb h1)

end GlobalTheory.JacLineSplit
