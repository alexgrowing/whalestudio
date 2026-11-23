import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingThird
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverRead.CompIndep

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mul_mem_map_of_prod {R : Type} [CommRing R] [IsDedekindDomain R] (f : R →+* R) (A I : Ideal R) (m p : R) (hm : m ≠ 0)
    (h : A * A.map f = Ideal.span {m}) (h1 : A * I * (A * I).map f = Ideal.span {m * p}) :
    ∀ b ∈ A.map f, p * b ∈ (A * I).map f := by
  intro b hb
  have h0 : Ideal.span {m} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hm
  rw [Ideal.map_mul, ← Ideal.span_singleton_mul_span_singleton, mul_mul_mul_comm, h] at h1
  have h2 := mul_left_cancel₀ h0 h1
  have h3 : p ∈ I.map f := by
    have h4 := Ideal.mem_span_singleton_self p
    rw [← h2] at h4
    exact (Ideal.mul_le_inf h4).2
  rw [Ideal.map_mul, mul_comm p]
  exact Ideal.mul_mem_mul hb h3

theorem smul_pull {R : Type} [CommRing R] {n : ℕ} (κ : Matrix (Fin n) (Fin n) R) (M p : ℕ) (v y : Fin n → R)
    (e : κ *ᵥ (p • v) - p • v = (M * p) • y) : p • (κ *ᵥ v - v) = p • M • y := by
  rw [smul_sub, ← Matrix.mulVec_smul, e, mul_comm M p, mul_smul]

theorem ratio_mul_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (p : ℕ) (I : Ideal (𝓞 E)) (hM : l₂.M = l.M * p) (hI : l₂.Mb = l.Mb * I) :
    ∀ b ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), (p : 𝓞 E) * b ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  have h1 := l₂.prod
  rw [hI, hM, Nat.cast_mul] at h1
  rw [hI]
  refine mul_mem_map_of_prod _ _ _ _ _ (Nat.cast_ne_zero.2 ?_) l.prod h1
  have := l.three_le
  omega

theorem congr_of_marked {D : D7} (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V ι) (M p : ℕ) (hp : p ≠ 0)
    (J J₂ : Ideal (𝓞 D.host.E)) (hJ : ∀ b ∈ J, (p : 𝓞 D.host.E) * b ∈ J₂) (g g' k : GA D V)
    (hk : finHom V k = finHom V (g⁻¹ * g')) (hL : latG V g = latG V g')
    (x : La → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hm : ∀ a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V g,
      x a - (finHom V g).1.mulVec (finVec V (ι a)) = (M * p) • w)
    (hm' : ∀ a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V g',
      x a - (finHom V g').1.mulVec (finVec V (ι a)) = (M * p) • w) :
    ∀ b ∈ J, ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec (halfVec V b z) - halfVec V b z = M • y := by
  refine ((GlobalTheory.Member.AALev.congruences_agree D V k).2 M J).2 fun v hv => ?_
  have hH : latGHat V g' = latGHat V g := by
    rw [GlobalTheory.RecDict.coset_latGHat, GlobalTheory.RecDict.coset_latGHat, hL]
  have hv' : v ∈ (J • (⊤ : Submodule (𝓞 D.host.E) La)).map ι := by
    rw [Submodule.map_smul'', Submodule.map_top, hι.2]
    exact hv
  obtain ⟨a, ha, rfl⟩ := hv'
  have hpa : p • a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La) := by
    refine Submodule.smul_induction_on (p := fun a => p • a ∈ J₂ • (⊤ : Submodule (𝓞 D.host.E) La)) ha
      (fun b hb c _ => ?_) (fun s t hs ht => ?_)
    · rw [← Nat.cast_smul_eq_nsmul (𝓞 D.host.E), smul_smul]
      exact Submodule.smul_mem_smul (hJ b hb) Submodule.mem_top
    · rw [smul_add]
      exact add_mem hs ht
  obtain ⟨w, hw, e⟩ := hm _ hpa
  obtain ⟨w', hw', e'⟩ := hm' _ hpa
  rw [hH] at hw'
  obtain ⟨y, hy, ey⟩ := GlobalTheory.RecDict.coset_fin (latGHat V 1) (latGHat V g) (finHom V g) (finHom V g') 1 (M * p)
    (fun u hu => ((GlobalTheory.MarkCoset.latG_spec D V g).2 u).1 hu) (fun u hu => by simpa using hu)
    (fun u hu => by simpa using hu) _ _ w w' 0 hw hw' (zero_mem _) e e' (by simp)
  refine ⟨y, hy, ?_⟩
  have hf : finVec V (ι (p • a)) = p • finVec V (ι a) := by
    rw [map_nsmul]
    exact AdLat.cap_fv_nsmul D.host.F p _
  rw [hf, one_mul, ← map_inv, ← map_mul, ← hk] at ey
  funext i
  exact GlobalTheory.MarkCoset.nsmul_cancel D.host.F p (Nat.cast_ne_zero.2 hp) (congrFun (smul_pull _ M p _ y ey) i)

theorem comp_eq_of_cover : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ h h' : GA D (T.V j σ), (C.dict₂ h).1 = (C.dict₂ h').1 → (T.dict j σ h).1 = (T.dict j σ h').1 := by
  intro D T hT j hj σ hσ C hC h h' hh
  obtain ⟨⟨-, hM, -, hI, -⟩, -, -, -, -, hr, g, e, F, ik, φ, th, -, -, -, hd⟩ := hC
  obtain ⟨hr', -, -, -, -, -, -, hι, -⟩ := hT.adPin j hj σ hσ
  obtain ⟨th', hr'', -, hQ, hK, ⟨x0, -, hR⟩, -⟩ := hT.dictU j hj σ hσ
  obtain ⟨γ, hγ, hΛ, hm, -⟩ := hd h
  obtain ⟨γ', hγ', hΛ', hm', -⟩ := hd h'
  rw [← hh] at hΛ' hm'
  have hinj : Function.Injective (fun v : Fin (T.V j σ).rank → D.host.E => v ∘ Fin.cast hr.symm) := fun u v huv =>
    funext fun i => congrFun huv (Fin.cast hr i)
  have hL : latG (T.V j σ) (γ * h) = latG (T.V j σ) (γ' * h') :=
    SetLike.coe_injective (hinj.image_injective (hΛ.symm.trans hΛ'))
  obtain ⟨a, ha, k, hk, eak⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (T.V j σ)).1 ((γ * h)⁻¹ * (γ' * h'))
  have hp : C.d.pd ≠ 0 := fun h0 => by
    have := C.d.l₂.three_le
    rw [hM, h0] at this
    omega
  have hk' : k ∈ T.Kf j σ := by
    refine (hT.kfHalf j hj σ hσ k).2 ⟨hk, ?_⟩
    have hm₁ := hm
    have hm₂ := hm'
    rw [hM] at hm₁ hm₂
    exact congr_of_marked (T.V j σ) _ hι _ _ hp _ _ (ratio_mul_mem T.Q.l C.d.l₂ _ _ hM hI) (γ * h) (γ' * h') k
      (by rw [eak, map_mul, show finHom (T.V j σ) a = 1 from ha, one_mul]) hL _ hm₁ hm₂
  have q : ∀ δ ∈ GQ (T.V j σ), ∀ u, (T.dict j σ (δ * u)).1 = (T.dict j σ u).1 := fun δ hδ u => by
    obtain ⟨_, -, e⟩ := hQ δ hδ u
    rw [e]
  have q₁ : (T.dict j σ (γ * h * a * k)).1 = (T.dict j σ (γ * h * a)).1 := by
    obtain ⟨_, -, e⟩ := hK k hk' (γ * h * a)
    rw [e]
  have q₂ : (T.dict j σ (γ * h * a)).1 = (T.dict j σ (γ * h)).1 := by
    obtain ⟨_, -, e⟩ := hR (γ * h) a ha
    rw [e]
  rw [← q γ hγ h, ← q γ' hγ' h', ← q₂, ← q₁, mul_assoc (γ * h), ← eak, mul_inv_cancel_left]

end GlobalTheory.CoverRead.CompIndep
