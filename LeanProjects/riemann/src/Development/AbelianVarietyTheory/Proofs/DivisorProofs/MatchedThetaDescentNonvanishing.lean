import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaExistsDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLocalGlobalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftMatchedVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfMemSpanImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleLocalSymmetryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAveragingProjectionStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.ThKLevel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem finPt_comm_kInf {d : ℕ} {W : Spc F E d} (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {l k : UA σ W.J} (hl : l ∈ GlobalTheory.ThKAdm.FinPt σ W) (hk : k ∈ KInf σ W τ) : l * k = k * l := by
  have hA : ∀ u : AF F, u.2 = 0 → u • (mat l - 1) = 0 := hl
  have hB : ∀ u : AF F, evI F u = 0 → u • (mat k - 1) = 0 := hk.1
  let u₁ : AF F := (1, 0)
  let u₂ : AF F := (0, 1)
  have hsum : u₁ + u₂ = 1 := Prod.ext (add_zero 1) (zero_add 1)
  have h1 : u₁ • (mat l - 1) = 0 := hA u₁ rfl
  have h2 : u₂ • (mat k - 1) = 0 := hB u₂ (by show (InfiniteAdeleRing.ringEquiv_mixedSpace F) 0 = 0; exact map_zero _)
  have hA' : u₂ • (mat l - 1) = mat l - 1 := by
    calc u₂ • (mat l - 1) = u₁ • (mat l - 1) + u₂ • (mat l - 1) := by rw [h1, zero_add]
      _ = mat l - 1 := by rw [← add_smul, hsum, one_smul]
  have hAC : (mat l - 1) * (mat k - 1) = 0 := by
    rw [← hA', Matrix.smul_mul, ← Matrix.mul_smul, h2, Matrix.mul_zero]
  have hCA : (mat k - 1) * (mat l - 1) = 0 := by
    rw [← hA', Matrix.mul_smul, ← Matrix.smul_mul, h2, Matrix.zero_mul]
  have hm : mat l * mat k = mat k * mat l := by
    have e1 : mat l * mat k = (mat l - 1) * (mat k - 1) + (mat l - 1) + (mat k - 1) + 1 := by noncomm_ring
    have e2 : mat k * mat l = (mat k - 1) * (mat l - 1) + (mat l - 1) + (mat k - 1) + 1 := by noncomm_ring
    rw [e1, e2, hAC, hCA]
  exact Subtype.ext (Units.ext hm)

end GlobalTheory.ThKLevel

namespace GlobalTheory.ThKLevel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem closure_stable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (om' : Rep σ Y W) (N : Submodule ℂ (Fn F n d))
    (hN : ∀ v : Pl F, ∀ h ∈ UAt σ W (evFin F v), ∀ x ∈ N, om' (1, h) x ∈ N) {g : UA σ W.J}
    (hg : g ∈ Subgroup.closure (⋃ v : Pl F, UAt σ W (evFin F v))) : ∀ x ∈ N, om' (1, g) x ∈ N := by
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨v, hv⟩ := Set.mem_iUnion.1 hx
    exact hN v x hv
  | inv_mem x hx =>
    obtain ⟨v, hv⟩ := Set.mem_iUnion.1 hx
    exact hN v x⁻¹ (GlobalTheory.ThetaFacCompl.inv_mem_UAt _ hv)
  | one =>
    intro z hz
    show (om' 1) z ∈ N
    rw [map_one]
    exact hz
  | mul x y _ _ ihx ihy =>
    intro z hz
    have e : om' (1, x * y) z = om' (1, x) (om' (1, y) z) := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    rw [e]
    exact ihx _ (ihy _ hz)

end GlobalTheory.ThKLevel

namespace GlobalTheory.ThKLevel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem average_core {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W) (om' : Rep σ Y W)
    (D : Submodule ℂ (Fn F n d)) (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J))
    (hstF : ∀ v : Pl F, ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ D, om' (1, h) Φ ∈ D)
    (hstK : ∀ k ∈ KInf σ W B.emb, ∀ Φ ∈ D, om' (1, k) Φ ∈ D)
    (hlin : ∀ Φ ∈ D, ∀ Ψ ∈ D, ∀ c : ℂ, M.I om' (Φ + c • Ψ) = M.I om' Φ + c • M.I om' Ψ)
    (hrinv : ∀ Φ ∈ D, ∀ Ψ ∈ D, ∀ h : UA σ W.J, ∫ x in 𝓕, M.I om' Φ (x * h) * starRingEnd ℂ (M.I om' Ψ (x * h)) ∂μ =
      ∫ x in 𝓕, M.I om' Φ x * starRingEnd ℂ (M.I om' Ψ x) ∂μ)
    (hsq : ∀ Φ ∈ D, ∀ h : UA σ W.J, MemLp (fun x => M.I om' Φ (x * h)) 2 (μ.restrict 𝓕))
    (Φ : D) (L : Subgroup (UA σ W.J)) (hLfin : (L : Set (UA σ W.J)) ⊆ GlobalTheory.ThKAdm.FinPt σ W)
    (hLΦ : ∀ l ∈ L, om' (1, l) (Φ : Fn F n d) = Φ)
    (hrep : ∀ Ψ ∈ D, ∃ s : Finset (UA σ W.J), (∀ g ∈ s, g ∈ Subgroup.closure (⋃ v : Pl F, UAt σ W (evFin F v))) ∧
      ∀ l ∈ L, ∃ g ∈ s, om' (1, l) Ψ = om' (1, g) Ψ) :
    ∃ P : D →ₗ[ℂ] D, P Φ = Φ ∧ (∀ Ψ, P (P Ψ) = P Ψ) ∧
      (∀ Ψ Ψ' : D, ∫ x in 𝓕, M.I om' ((P Ψ : D) : Fn F n d) x * starRingEnd ℂ (M.I om' ((Ψ' : D) : Fn F n d) x) ∂μ =
        ∫ x in 𝓕, M.I om' ((Ψ : D) : Fn F n d) x * starRingEnd ℂ (M.I om' ((P Ψ' : D) : Fn F n d) x) ∂μ) ∧
      (∀ N : Submodule ℂ (Fn F n d), GlobalTheory.ThetaFac.WStable B om' D N → N ≤ D → ∀ Ψ : D,
        ((Ψ : D) : Fn F n d) ∈ N → ((P Ψ : D) : Fn F n d) ∈ N) ∧
      (∀ Ψ : D, ∀ l ∈ L, om' (1, l) ((P Ψ : D) : Fn F n d) = ((P Ψ : D) : Fn F n d)) ∧
      (∀ k ∈ KInf σ W B.emb, ∀ Ψ Ψ' : D, ((Ψ' : D) : Fn F n d) = om' (1, k) ((Ψ : D) : Fn F n d) →
        ((P Ψ' : D) : Fn F n d) = om' (1, k) ((P Ψ : D) : Fn F n d)) := by
  classical
  let π : UA σ W.J →* Module.End ℂ (Fn F n d) := om'.comp (MonoidHom.inr _ _)
  have hπ : ∀ g x, π g x = om' (1, g) x := fun _ _ => rfl

  have hGD : ∀ g ∈ Subgroup.closure (⋃ v : Pl F, UAt σ W (evFin F v)), ∀ x ∈ D, om' (1, g) x ∈ D :=
    fun g hg => closure_stable om' D hstF hg
  have hLD : ∀ l ∈ L, ∀ x ∈ D, π l x ∈ D := by
    intro l hl x hx
    obtain ⟨s, hs, hsl⟩ := hrep x hx
    obtain ⟨g, hg, e⟩ := hsl l hl
    rw [hπ, e]
    exact hGD g (hs g hg) x hx
  have hfin : ∀ x ∈ D, (Set.range fun l : L => π (l : UA σ W.J) x).Finite := by
    intro x hx
    obtain ⟨s, -, hsl⟩ := hrep x hx
    refine (s.finite_toSet.image fun g => π g x).subset ?_
    rintro _ ⟨l, rfl⟩
    obtain ⟨g, hg, e⟩ := hsl l l.2
    exact ⟨g, hg, e.symm⟩
  obtain ⟨P, hP1, hP2, hP3⟩ := GlobalTheory.T.exists_averaging_projection (UA σ W.J) (Fn F n d) π L D hLD hfin

  have hI0 : M.I om' 0 = 0 := by
    have e := hlin 0 D.zero_mem 0 D.zero_mem 1
    simp only [one_smul, add_zero] at e
    exact (add_eq_left.1 e.symm)
  have hIsmul : ∀ x ∈ D, ∀ c : ℂ, M.I om' (c • x) = c • M.I om' x := by
    intro x hx c
    have e := hlin 0 D.zero_mem x hx c
    rwa [zero_add, hI0, zero_add] at e
  have hIadd : ∀ x ∈ D, ∀ y ∈ D, M.I om' (x + y) = M.I om' x + M.I om' y := by
    intro x hx y hy
    have e := hlin x hx y hy 1
    rwa [one_smul, one_smul] at e
  have hIsum : ∀ (s : Finset (UA σ W.J)) (f : UA σ W.J → Fn F n d), (∀ g ∈ s, f g ∈ D) →
      M.I om' (∑ g ∈ s, f g) = ∑ g ∈ s, M.I om' (f g) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using hI0
    | insert g s hgs ih =>
      rw [Finset.sum_insert hgs, Finset.sum_insert hgs,
        hIadd _ (hf g (Finset.mem_insert_self g s)) _ (D.sum_mem fun i hi => hf i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

  have hint : ∀ x ∈ D, ∀ y ∈ D,
      Integrable (fun t => M.I om' x t * starRingEnd ℂ (M.I om' y t)) (μ.restrict 𝓕) := by
    intro x hx y hy
    have h1 := hsq x hx 1
    have h2 := hsq y hy 1
    simp only [mul_one] at h1 h2
    have := h1.integrable_mul (p := 2) (q := 2) h2.star
    simpa [Pi.mul_def, Pi.star_def] using this
  refine ⟨P, hP1 Φ hLΦ, fun Ψ => hP1 (P Ψ) (hP2 Ψ), ?_, ?_, hP2, ?_⟩
  ·
    intro x y
    obtain ⟨s, f, -, hsL, hPx, hPy, hbij, hf⟩ := hP3 x y
    set c : ℂ := (s.card : ℂ)⁻¹ with hc
    have hcc : starRingEnd ℂ c = c := by simp [hc]
    have hmem : ∀ g ∈ s, ∀ z : D, π g (z : Fn F n d) ∈ D := fun g hg z => hLD g (hsL g hg) _ z.2
    have hterm : ∀ g ∈ s, ∫ t in 𝓕, M.I om' (π g (x : Fn F n d)) t * starRingEnd ℂ (M.I om' y t) ∂μ =
        ∫ t in 𝓕, M.I om' x t * starRingEnd ℂ (M.I om' (π (f g) (y : Fn F n d)) t) ∂μ := by
      intro g hg
      have hy' : π g⁻¹ (y : Fn F n d) ∈ D := hLD _ (L.inv_mem (hsL g hg)) _ y.2
      rw [← hf g hg, ← hrinv x x.2 _ hy' g]
      congr 1
      funext t
      rw [hπ, hπ, GlobalTheory.ThetaFacCompl.I_transl, GlobalTheory.ThetaFacCompl.I_transl, mul_inv_cancel_right]
    have hL : ∫ t in 𝓕, M.I om' ((P x : D) : Fn F n d) t * starRingEnd ℂ (M.I om' y t) ∂μ =
        c * ∑ g ∈ s, ∫ t in 𝓕, M.I om' (π g (x : Fn F n d)) t * starRingEnd ℂ (M.I om' y t) ∂μ := by
      rw [hPx, hIsmul _ (D.sum_mem fun g hg => hmem g hg x), hIsum s _ fun g hg => hmem g hg x,
        ← integral_finsetSum s fun g hg => hint _ (hmem g hg x) _ y.2, ← integral_const_mul]
      congr 1
      funext t
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    have hR : ∫ t in 𝓕, M.I om' x t * starRingEnd ℂ (M.I om' ((P y : D) : Fn F n d) t) ∂μ =
        c * ∑ g ∈ s, ∫ t in 𝓕, M.I om' x t * starRingEnd ℂ (M.I om' (π g (y : Fn F n d)) t) ∂μ := by
      rw [hPy, hIsmul _ (D.sum_mem fun g hg => hmem g hg y), hIsum s _ fun g hg => hmem g hg y,
        ← integral_finsetSum s fun g hg => hint _ x.2 _ (hmem g hg y), ← integral_const_mul]
      congr 1
      funext t
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, map_mul, map_sum, hcc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      ring
    rw [hL, hR, Finset.sum_congr rfl hterm]
    congr 1
    exact Finset.sum_nbij f (fun a ha => hbij.mapsTo ha) hbij.injOn hbij.surjOn (fun _ _ => rfl)
  ·
    intro N hN hND Ψ hΨ
    obtain ⟨s, f, -, hsL, hPx, -⟩ := hP3 Ψ Ψ
    rw [hPx]
    refine N.smul_mem _ (N.sum_mem fun g hg => ?_)
    obtain ⟨s', hs', hsl⟩ := hrep Ψ Ψ.2
    obtain ⟨g', hg', e⟩ := hsl g (hsL g hg)
    rw [hπ, e]
    exact closure_stable om' N hN.fin (hs' g' hg') _ hΨ
  ·
    intro k hk Ψ Ψ' e
    obtain ⟨s, f, -, hsL, hPx, hPy, -⟩ := hP3 Ψ Ψ'
    rw [hPy, hPx, e, map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [hπ, hπ, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk,
      Prod.mk_mul_mk, one_mul, finPt_comm_kInf B.emb (hLfin (hsL g hg)) hk]

end GlobalTheory.ThKLevel

namespace GlobalTheory.ThKLevel

theorem level_average : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ (μ : MeasureTheory.Measure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)) (𝓕 : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)), μ.IsHaarMeasure → MeasureTheory.IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU σ G.W.J) 𝓕 μ → ∀ Φ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∃ L : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J), GlobalTheory.ThKAdm.IsLevel G.W L ∧ ∃ P : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) →ₗ[ℂ] ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), P Φ = Φ ∧ (∀ Ψ, P (P Ψ) = P Ψ) ∧ (∀ Ψ Ψ' : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∫ x in 𝓕, G.M'.I om' ((P Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) x * starRingEnd ℂ (G.M'.I om' ((Ψ' : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) x) ∂μ = ∫ x in 𝓕, G.M'.I om' ((Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) x * starRingEnd ℂ (G.M'.I om' ((P Ψ' : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) x) ∂μ) ∧ (∀ N : Submodule ℂ (GlobalTheory.ThK.Fn F a' (a + a')), GlobalTheory.ThetaFac.WStable B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) N → N ≤ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) → ∀ Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ((Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) ∈ N → ((P Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) ∈ N) ∧ (∀ Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ l ∈ L, om' (1, l) ((P Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) = ((P Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a'))) ∧ (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W B.emb, ∀ Ψ Ψ' : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ((Ψ' : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) = om' (1, k) ((Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) → ((P Ψ' : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a')) = om' (1, k) ((P Ψ : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) : GlobalTheory.ThK.Fn F a' (a + a'))) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 Φ
  obtain ⟨L, hL, hLΦ, hrep⟩ := GlobalTheory.T.matched_triple_local_symmetry hKP F E σ B a a' G X om om' R Rf hM Φ Φ.2
  obtain ⟨hstF, hstK⟩ := GlobalTheory.T.matched_pair_theta_exists_data hKP F E σ B a a' G X om om' R Rf hM
  exact ⟨L, hL, average_core B G.M' om' _ μ 𝓕 hstF hstK (GlobalTheory.T.matched_pair_theta_local_global hKP F E σ B a a' G X om om' R Rf hM)
    (GlobalTheory.T.matched_pair_theta_finite_places hKP F E σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕)
    (GlobalTheory.T.theta_lift_matched_vanishing hKP F E σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕) Φ L hL.1 hLΦ hrep⟩

end GlobalTheory.ThKLevel
