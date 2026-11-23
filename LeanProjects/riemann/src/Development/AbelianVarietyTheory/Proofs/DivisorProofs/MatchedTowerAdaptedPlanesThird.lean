import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftMemLiftSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLocalRealPlaceScalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeHyperbolicPlaneResidueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldLP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalSphericalValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleIsotropicTowerStepTen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarModelUnitaryAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarModelUnitaryActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesGoodModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceEmbeddingExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxSymplecticHermitianSkewStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicIntegrableOnDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSpanLocalTensorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalDarbouxFixesThetaDistributionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantInducedIrreducibleAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothUnitaryHomSpaceDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroInvariantTrilinearForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantSubmoduleInImageSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneGramOfComplementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionFactorizesAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorSchwartzBruhatStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar GlobalTheory.ThK.LiftConst
open GlobalTheory.ThK.SplitInv

noncomputable section

namespace GlobalTheory.ThK.SplitQuot

section Abstract

variable {H Γ Γ' A U : Type} [Group H] [Group Γ] [Group Γ'] [AddCommGroup A] [Module ℂ A] [AddCommGroup U] [Module ℂ U]

def rtL (k : H) : (H → ℂ) →ₗ[ℂ] (H → ℂ) := LinearMap.funLeft ℂ ℂ (fun g => g * k)

theorem quotTriv_of_pairings (L : Γ →* H) (G₀ : Subgroup H) (hL : ∀ g, L g ∈ G₀) (hL' : ∀ k ∈ G₀, ∃ g, L g = k)
    (S : Submodule ℂ (H → ℂ)) (hS : RStable G₀ S) (rel : Γ → Γ' → A → A → Prop) (π : Representation ℂ Γ' U)
    (howe : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V), ρ.IsIrreducible →
      ∀ P : A →ₗ[ℂ] U →ₗ[ℂ] V, P ≠ 0 → (∀ g h a a', rel g h a a' → ∀ u, P a' (π h u) = ρ g (P a u)) → ∀ g w, ρ g w = w)
    (Ps : Set (A →ₗ[ℂ] U →ₗ[ℂ] (H → ℂ))) (hmem : ∀ Q ∈ Ps, ∀ a u, Q a u ∈ S)
    (hlaw : ∀ Q ∈ Ps, ∀ g h a a', rel g h a a' → ∀ u, Q a' (π h u) = rt (L g) (Q a u))
    (hspan : S ≤ Submodule.span ℂ {y | ∃ Q ∈ Ps, ∃ a u, y = Q a u}) : QuotTriv G₀ S := by
  intro N hNS hN hne hmax φ hφ k hk
  let N' : Submodule ℂ S := N.comap S.subtype
  let r : Γ → S →ₗ[ℂ] S := fun g => (rtL (L g)).restrict (fun ψ hψ => hS ψ hψ _ (hL g))
  have hr : ∀ g, N' ≤ N'.comap (r g) := fun g ψ hψ => hN _ hψ _ (hL g)
  let ρ : Representation ℂ Γ (S ⧸ N') :=
    { toFun := fun g => N'.mapQ N' (r g) (hr g)
      map_one' := by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun ψ => ?_)
        show Submodule.Quotient.mk (r 1 ψ) = Submodule.Quotient.mk ψ
        congr 1
        exact Subtype.ext (by show rt (L 1) ψ.1 = ψ.1; rw [map_one, rt_one])
      map_mul' := fun g g' => by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun ψ => ?_)
        show Submodule.Quotient.mk (r (g * g') ψ) = Submodule.Quotient.mk (r g (r g' ψ))
        congr 1
        exact Subtype.ext (by show rt (L (g * g')) ψ.1 = rt (L g) (rt (L g') ψ.1); rw [map_mul, rt_rt]) }
  have hρ : ∀ g (ψ : S), ρ g (Submodule.Quotient.mk ψ) = Submodule.Quotient.mk (r g ψ) := fun _ _ => rfl
  have hirr : ρ.IsIrreducible := by
    have hex : ∃ ψ ∈ S, ψ ∉ N := by
      by_contra hc
      push_neg at hc
      exact hne (le_antisymm hNS hc)
    obtain ⟨ψ₀, hψ₀, hψ₀N⟩ := hex
    haveI : Nontrivial (Subrepresentation ρ) := ⟨⊥, ⊤, fun h => by
      have h1 : (Submodule.Quotient.mk ⟨ψ₀, hψ₀⟩ : S ⧸ N') ∈ (⊤ : Subrepresentation ρ).toSubmodule := trivial
      rw [← h] at h1
      exact hψ₀N ((Submodule.Quotient.mk_eq_zero N').1 h1)⟩
    refine ⟨fun D => ?_⟩
    let D' : Submodule ℂ (H → ℂ) := (D.toSubmodule.comap N'.mkQ).map S.subtype
    have hD : ∀ ψ : S, ψ.1 ∈ D' ↔ (Submodule.Quotient.mk ψ : S ⧸ N') ∈ D.toSubmodule := fun ψ =>
      ⟨fun ⟨χ, h1, h2⟩ => by rw [← show χ = ψ from Subtype.ext h2]; exact h1, fun h => ⟨ψ, h, rfl⟩⟩
    have h1 : RStable G₀ D' := by
      rintro _ ⟨χ, h1, rfl⟩ k hk
      obtain ⟨g, rfl⟩ := hL' k hk
      exact (hD (r g χ)).2 (D.apply_mem_toSubmodule g h1)
    have h2 : N ≤ D' := fun ψ hψ => (hD ⟨ψ, hNS hψ⟩).2 (by
      rw [(Submodule.Quotient.mk_eq_zero N').2 hψ]; exact zero_mem _)
    have h3 : D' ≤ S := by
      rintro _ ⟨χ, -, rfl⟩
      exact χ.2
    rcases hmax D' h1 h2 h3 with e | e
    · left
      refine Subrepresentation.toSubmodule_injective ?_
      refine (Submodule.eq_bot_iff _).2 fun w hw => ?_
      obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective N' w
      exact (Submodule.Quotient.mk_eq_zero N').2 (show ψ.1 ∈ N from e ▸ (hD ψ).2 hw)
    · right
      refine Subrepresentation.toSubmodule_injective ?_
      refine Submodule.eq_top_iff'.2 fun w => ?_
      obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective N' w
      exact (hD ψ).1 (e.symm ▸ ψ.2)
  by_cases hall : ∀ Q ∈ Ps, ∀ a u, Q a u ∈ N
  · refine absurd (le_antisymm hNS (hspan.trans (Submodule.span_le.2 ?_))) hne
    rintro _ ⟨Q, hQ, a, u, rfl⟩
    exact hall Q hQ a u
  · push_neg at hall
    obtain ⟨Q, hQ, a, u, hau⟩ := hall
    let P : A →ₗ[ℂ] U →ₗ[ℂ] (S ⧸ N') := LinearMap.mk₂ ℂ (fun a u => Submodule.Quotient.mk ⟨Q a u, hmem Q hQ a u⟩)
      (fun a a' u => by rw [← Submodule.Quotient.mk_add]; congr 1; exact Subtype.ext (by simp))
      (fun c a u => by rw [← Submodule.Quotient.mk_smul]; congr 1; exact Subtype.ext (by simp))
      (fun a u u' => by rw [← Submodule.Quotient.mk_add]; congr 1; exact Subtype.ext (by simp))
      (fun c a u => by rw [← Submodule.Quotient.mk_smul]; congr 1; exact Subtype.ext (by simp))
    have hP : P ≠ 0 := fun h0 => hau ((Submodule.Quotient.mk_eq_zero N').1
      (LinearMap.congr_fun (LinearMap.congr_fun h0 a) u))
    obtain ⟨g, rfl⟩ := hL' k hk
    have key := howe _ ρ hirr P hP (fun g h a a' hrel u => by
      show Submodule.Quotient.mk _ = Submodule.Quotient.mk (r g _)
      congr 1
      exact Subtype.ext (hlaw Q hQ g h a a' hrel u)) g (Submodule.Quotient.mk ⟨φ, hφ⟩)
    rw [hρ] at key
    exact (Submodule.Quotient.eq N').1 key

end Abstract

section LocType

open GlobalTheory.SplitUnitLift GlobalTheory.LocTypeGood

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem notRealPow_good : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ τ : E →ₐ[F] Fv F v, NotRealPow τ X.α X.β := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv τ t ht
  have hnr := GlobalTheory.NuGood.not_root_of_unity F E σ B a a' G X om om' hT v hv τ
  have hdiv : chrW X.ν τ = chrW X.α τ * (chrW X.β τ)⁻¹ := by
    ext x
    simp [Chars.ν, chrW, locChar, div_eq_mul_inv]
  have hval : ((chrW X.ν τ (unifAt v) : ℂˣ) : ℂ) =
      ((GlobalTheory.SplitWeil.nabs (Fv F v) (unifAt v) ^ t : ℝ) : ℂ) := by
    rw [hdiv, ht, GlobalTheory.SmGL.val_absPow_ofReal]
  have hn : ‖((chrW X.ν τ (unifAt v) : ℂˣ) : ℂ)‖ = 1 := by
    simp only [chrW, locChar, MonoidHom.coe_comp, Function.comp_apply]
    first | exact Circle.norm_coe _ | exact Circle.abs_coe _ | simp
  have hpos : 0 < GlobalTheory.SplitWeil.nabs (Fv F v) (unifAt v) ^ t :=
    Real.rpow_pos_of_pos (GlobalTheory.SmGL.nabs_pos' _ _) t
  have h1 : GlobalTheory.SplitWeil.nabs (Fv F v) (unifAt v) ^ t = 1 := by
    rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at hn
    exact hn
  apply hnr 1 one_ne_zero
  apply Units.ext
  rw [zpow_one, hval, h1]
  simp

theorem locType_lev : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
      (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))), H'.IsAdapted σ B G.W (sp 0) i₀ i₁ →
      (∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) → ∀ c : ℂ,
      BetaZero (sp 0) H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (Diffs B G X om om' R Rf c) →
      (∀ j < G.p, BetaZero (sp (j + 1)) (pl j) X.α X.β ((a' : ℝ) / 2) (zb a j) (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) j)) →
      ∀ i < G.p, ∀ (v : Pl F), X.Good v → ∀ (τ : E →ₐ[F] Fv F v) (hcm : IsCMExt F E σ) (ε : F)
        (herm : ∀ k l, σ ((sp i).J l k) = algebraMap F E ε * (sp i).J k l) (hJ : IsUnit ((sp i).J.map τ).det)
        (e : Fin (a - 2 * (i + 1) + a') ≃ Fin (d₁ - 2 * i)),
        ∀ f ∈ Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) i,
          HasLocType hcm τ (sp i).J ε herm hJ e (chrW X.α τ) (chrW X.β τ) f := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM _hq d₁ H' i₀ i₁ sp pl hH hiso c h0 hj i hi v hv τ hcm ε herm hJ e f hf
  have hT := hM.triple
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hT.base.cm
  have hsk := GlobalTheory.ThK.DescB.NextStep.skew_sp (p := G.p) hσ B hT.geo.hW.skew hH hiso
  have hgen := notRealPow_good F E σ B a a' G X om om' hT v hv τ
  have hreg := GlobalTheory.ThK.DescB.Nondeg.lev_reg hK hM hH hiso c h0 hj
  have hdreg := GlobalTheory.ThK.DescB.Nondeg.diffs_reg hK hM c
  have hrank : a + a' = d₁ + 2 := hH.rank
  let w0 := Classical.arbitrary (InfinitePlace F)
  have hJW : IsUnit (G.W.J.map τ).det :=
    isUnit_det_of_cartan G.W.J τ (B.emb w0).1 Complex.I Complex.I_ne_zero _ (hT.geo.hW.cartan w0)
  have hermW : ∀ k l, σ (G.W.J l k) = algebraMap F E (-1) * G.W.J k l := fun k l => by
    rw [hT.geo.hW.skew k l, map_neg, map_one, neg_one_mul]
  have hJsp : ∀ j < G.p, IsUnit (((sp j).J).map τ).det := fun j hj' =>
    isUnit_det_of_cartan (sp j).J τ (B.emb w0).1 Complex.I Complex.I_ne_zero _ ((hiso j hj').2.2.2.2.2.2.1 w0)
  have hermSp : ∀ j ≤ G.p, ∀ k l, σ ((sp j).J l k) = algebraMap F E (-1) * (sp j).J k l := fun j hj' k l => by
    rw [hsk j hj' k l, map_neg, map_one, neg_one_mul]
  suffices P : ∀ j, j < G.p → ∀ g ∈ Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) j, ∀ x, x + 2 * (j + 1) = a →
      ∀ (ε : F) (herm : ∀ k l, σ ((sp j).J l k) = algebraMap F E ε * (sp j).J k l) (hJ : IsUnit ((sp j).J.map τ).det)
        (e : Fin (x + a') ≃ Fin (d₁ - 2 * j)), HasLocType hcm τ (sp j).J ε herm hJ e (chrW X.α τ) (chrW X.β τ) g by
    have hbig : 2 * (G.p + G.q) + 1 < (a - a') / 2 := hT.geo.eBig
    exact P i hi f hf (a - 2 * (i + 1)) (by omega) ε herm hJ e
  have hbig : 2 * (G.p + G.q) + 1 < (a - a') / 2 := hT.geo.eBig
  intro j
  induction j with
  | zero =>
    intro _ g hg x hx ε₁ herm₁ hJ₁ e₁
    have hzb : ((a : ℝ) / 2) = (((x + 2 : ℕ) : ℝ) / 2) := by
      rw [← hx] <;> push_cast <;> ring
    rw [lev_zero, hzb] at hg
    have eW : Fin (x + 2 + a') ≃ Fin (a + a') := finCongr (by omega)
    exact GlobalTheory.T.hecke_hyperbolic_plane_residue hK F E σ hcm X.α X.β v τ hgen hT.chars.heckeα hT.chars.heckeβ a' hT.chars.resα (a + a') (d₁ - 2 * 0) G.W (sp 0) H' (by omega) hH.xx hH.yy hH.xy hH.orth hH.gram
      (-1) hermW hJW ε₁ herm₁ hJ₁ x a' eW e₁ (finK σ G.W B.emb) (Diffs B G X om om' R Rf c) hdreg
      (fun f hf => GlobalTheory.T.matched_local_real_place_scaling hK F E σ B a a' G X om om' R Rf hM c v hv τ hcm (-1) hermW hJW (x + 2) (by omega) eW f hf) g hg
  | succ j ih =>
    intro hj1 g hg x hx ε₁ herm₁ hJ₁ e₁
    have hI := hiso j (by omega)
    have hzb : zb a j = (((x + 2 : ℕ) : ℝ) / 2) := by
      unfold zb; rw [← hx] <;> push_cast <;> ring
    rw [lev_succ, hzb] at hg
    have eW : Fin (x + 2 + a') ≃ Fin (d₁ - 2 * j) := finCongr (by omega)
    exact GlobalTheory.T.hecke_hyperbolic_plane_residue hK F E σ hcm X.α X.β v τ hgen hT.chars.heckeα hT.chars.heckeβ a' hT.chars.resα (d₁ - 2 * j) (d₁ - 2 * (j + 1)) (sp j) (sp (j + 1)) (pl j) hI.1 hI.2.1 hI.2.2.1
      hI.2.2.2.1 hI.2.2.2.2.1 hI.2.2.2.2.2.1 (-1) (hermSp j (by omega)) (hJsp j (by omega)) ε₁ herm₁ hJ₁ x a' eW e₁
      (finK σ (sp j) B.emb) (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) j) (hreg j (by omega))
      (fun f hf => ih (by omega) f hf (x + 2) (by omega) (-1) (hermSp j (by omega)) (hJsp j (by omega)) eW) g hg

end LocType

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem conj_omB {n d : ℕ} {ν α : kˣ →* ℂˣ} (hν : ∀ x, ‖(ν x : ℂ)‖ = 1) (hα : ∀ x, ‖(α x : ℂ)‖ = 1) (g : GL (Fin n) k)
    (h : GL (Fin d) k) (Ψ : Matrix (Fin n) (Fin d) k → ℂ) :
    (fun Y => (starRingEnd ℂ) (GlobalTheory.SplitFlip.omB ν⁻¹ α⁻¹ g h Ψ Y)) =
      GlobalTheory.SplitFlip.omB ν α g h fun Y => (starRingEnd ℂ) (Ψ Y) := by
  have e : ∀ (x : kˣ) (N : ℕ), (starRingEnd ℂ) (GlobalTheory.SplitFlip.apow x ((N : ℂ) / 2)) = GlobalTheory.SplitFlip.apow x ((N : ℂ) / 2) := by
    intro x N
    have h0 : (0 : ℝ) ≤ GlobalTheory.SplitWeil.nabs k x := NNReal.coe_nonneg _
    have h1 : ((N : ℂ) / 2) = (((N : ℝ) / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [GlobalTheory.SplitFlip.apow, h1, ← Complex.ofReal_cpow h0, Complex.conj_ofReal]
  funext Y
  simp only [GlobalTheory.SplitFlip.omB, map_mul, e, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  rw [Complex.inv_eq_conj (hν _), Complex.inv_eq_conj (hα _), Complex.conj_conj, Complex.conj_conj]

theorem howe_trivial (hK : GlobalTheory.ThK.KP) {x x' m : ℕ} (hx : x' ≤ x) (hm : x + x' = m) {α β : kˣ →* ℂˣ}
    (hα : GlobalTheory.KSplit.IsSmU α) (hβ : GlobalTheory.KSplit.IsSmU β) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin x') k) V) (hρ : ρ.IsIrreducible)
    (P : GlobalTheory.SplitWeil.SB (Matrix (Fin x') (Fin m) k) →ₗ[ℂ]
      GlobalTheory.SmGL.IndSp (GlobalTheory.ThK.MidJac.e2 x x') (GlobalTheory.SmGL.ofChar (GlobalTheory.ThK.DetProd.twoDet x x' α β)) →ₗ[ℂ] V) (hP : P ≠ 0)
    (hlaw : ∀ (g : GL (Fin x') k) (h : GL (Fin (x + x')) k) (Ψ Ψ' : GlobalTheory.SplitWeil.SB (Matrix (Fin x') (Fin m) k)),
      (Ψ' : Matrix (Fin x') (Fin m) k → ℂ) =
        GlobalTheory.SplitFlip.omB (α / β)⁻¹ α⁻¹ g (GlobalTheory.LocTypeGood.glReindex (finCongr hm) h) Ψ →
      ∀ u, P Ψ' (GlobalTheory.ThK.MidJac.detInd x x' α β h u) = ρ g (P Ψ u)) (g : GL (Fin x') k) (w : V) : ρ g w = w := by
  subst hm
  have hre : ∀ h : GL (Fin (x + x')) k, GlobalTheory.LocTypeGood.glReindex (finCongr (rfl : x + x' = x + x')) h = h := fun h =>
    Units.ext (Matrix.ext fun i j => rfl)
  simp only [hre] at hlaw
  have hinv : ∀ {χ : kˣ →* ℂˣ}, GlobalTheory.KSplit.IsSmU χ → GlobalTheory.KSplit.IsSmU χ⁻¹ := fun {χ} h =>
    ⟨GlobalTheory.SmGL.IsSmoothChar.inv h.1, fun y => by simp [h.2 y]⟩
  have hdiv : GlobalTheory.KSplit.IsSmU (α / β) := by
    rw [div_eq_mul_inv]
    exact ⟨GlobalTheory.SmGL.IsSmoothChar.mul hα.1 (hinv hβ).1, fun y => by simp [hα.2 y, hβ.2 y]⟩
  obtain ⟨hirr, hadm⟩ := GlobalTheory.T.determinant_induced_irreducible_admissible hK k x x' α β hα hβ
  obtain ⟨P₀, hP₀, hlaw₀⟩ := GlobalTheory.T.exists_nonzero_invariant_trilinear_form k x x' hx α β hα hβ
  obtain ⟨e⟩ := GlobalTheory.T.smooth_unitary_hom_space_dimension hK k x' (x + x') (α / β)⁻¹ α⁻¹ (hinv hdiv) (hinv hα) _ V ℂ _ ρ
    (GlobalTheory.SmGL.ofChar (1 : GL (Fin x') k →* ℂˣ)) hirr hadm hρ (GlobalTheory.SmGL.isIrreducible_ofChar _) P P₀ hP hP₀ hlaw
    (fun g h Ψ Ψ' hΨ u => by rw [hlaw₀ g h Ψ Ψ' hΨ u]; simp)
  have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g w
  apply e.toLinearEquiv.injective
  change e.toIntertwiningMap (ρ g w) = e.toIntertwiningMap w
  rw [h1]
  simp

end Local

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_linear_model (hP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} (hB : B.IsGood σ) {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
    {r s r' s' : ℕ} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
    (hco : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      co.e (incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)))
    {χX χW : Chr F E} (h1 : IsHecke F E χX) (h2 : IsHecke F E χW)
    (r1 : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n)
    (r2 : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d) (om : Rep σ X W)
    (hom : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) co χX χW om) (v : Pl F) (t : E →ₐ[F] Fv F v) :
    ∃ ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ),
      Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _) ∧
      ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (g, h)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.SplitFlip.omB (chrW χW t) (chrW χX t) (GlobalTheory.KSplit.locMat t 1 g) (GlobalTheory.KSplit.locMat t 1 h) (ι φ) := by
  have hcm : IsCMExt F E σ := hB.cm
  obtain ⟨M₀, hM₀⟩ := GlobalTheory.T.exists_good_schrodinger_model F E σ B hB n d X W r s r' s' hX hW
  obtain ⟨-, -, ev, -, -, -, -, hvac, hstd, -⟩ := GlobalTheory.T.darboux_coordinates_good_model F E σ B n d X W M₀ r s r' s' hB hX hW hM₀ co hco
  let M : Model σ X W := ⟨co, fun v => ev v (M₀.vac v), M₀.μ, M₀.dom⟩
  have hpair : IsPair B M χX χW om r s r' s' := ⟨hB, hX, hW, ⟨hco, hvac, hstd, hM₀.haar, hM₀.dom⟩, h1, h2, r1, r2, hom⟩
  have hJX : (X.J.map t).det ≠ 0 := GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_herm hX) t
  have hJW : (W.J.map t).det ≠ 0 := GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_skew hW) t
  let P : GL (Fin n) (Fv F v) := Matrix.nonsingInvUnit (-(X.J.map t)) (isUnit_iff_ne_zero.mpr (by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hJX))
  let Q : GL (Fin d) (Fv F v) := Matrix.nonsingInvUnit (W.J.map t) (isUnit_iff_ne_zero.mpr hJW)
  have hPv : P.1 = -(X.J.map t) := rfl
  have hQv : Q.1 = W.J.map t := rfl
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_linear_witt_model_local hP F E σ B n d X W M χX χW om r s r' s' hpair v (t.comp σ) P⁻¹ Q⁻¹
  have hbar : M.IsLinBar B.ψ t 1 1 ι := by
    unfold Model.IsLinBar
    unfold Model.IsLinW at hι
    rw [GlobalTheory.OppLagr.comp_comp hcm] at hι
    convert hι using 2
    funext u
    simp only [inv_inv, hPv, hQv, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul]
  refine ⟨ι, hι.bij, fun g hg h hh φ hφ => ?_⟩
  obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := (GlobalTheory.T.theta_action_exists hP F E σ B n d X W M χX χW om r s r' s' hpair v).1 g hg h hh φ hφ
  exact ⟨φ₁, hφ₁, hA, GlobalTheory.T.linear_bar_model_unitary_action hP F E σ B n d X W M χX χW om r s r' s' hpair v t 1 1 ι hbar g hg h hh φ hφ φ₁ hφ₁ hA⟩

theorem conj_mem_SB {X : Type} [TopologicalSpace X] {Ψ : X → ℂ} (hΨ : Ψ ∈ GlobalTheory.SplitWeil.SB X) :
    (fun x => (starRingEnd ℂ) (Ψ x)) ∈ GlobalTheory.SplitWeil.SB X :=
  ⟨hΨ.1.comp _, hΨ.2.comp_left (map_zero _)⟩

theorem tens_add {R κ : Type} (ev : AF F → R) (φ₁ φ₂ : (κ → R) → ℂ) (r : (κ → AF F) → ℂ) :
    tens ev (φ₁ + φ₂) r = tens ev φ₁ r + tens ev φ₂ r := by
  funext x; simp [tens, add_mul]

theorem tens_smul {R κ : Type} (ev : AF F → R) (c : ℂ) (φ : (κ → R) → ℂ) (r : (κ → AF F) → ℂ) :
    tens ev (c • φ) r = c • tens ev φ r := by
  funext x; simp [tens, mul_assoc]

set_option maxHeartbeats 1600000 in

theorem quotTriv_of_model (hK : GlobalTheory.ThK.KP) (hcm : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {n m : ℕ}
    (X : Spc F E n) (W : Spc F E m) (hX : ∀ i j, σ (X.J j i) = X.J i j) (hXd : X.J.det ≠ 0)
    (hY : ∀ i j, σ (W.J j i) = -W.J i j) (hYd : W.J.det ≠ 0)
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin m))
    (hco : ∀ x : Matrix (Fin n) (Fin m) E, ∃ y z : Fin n × Fin m → F,
      co.e (incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)))
    (χX χY : Chr F E) (hχX : IsHecke F E χX) (hχY : IsHecke F E χY) (om : Rep σ X W)
    (hom : IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F X.J) (incM F W.J) co χX χY om)
    (f : UA σ W.J → ℂ) (hfc : Continuous f) (hfl : ∀ γ ∈ ratU σ W.J, ∀ h, f (γ * h) = f h)
    (hfd : ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C)
    (Φ : (Fin n × Fin m → AF F) → ℂ) (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J))
    (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (ratU σ W.J) 𝓕 μ) (v : Pl F)
    (ν α : (Fv F v)ˣ →* ℂˣ) (hν : ∀ x, ‖(ν x : ℂ)‖ = 1) (hα : ∀ x, ‖(α x : ℂ)‖ = 1)
    (cX : UA σ X.J → GL (Fin n) (Fv F v)) (cW : UA σ W.J → GL (Fin m) (Fv F v))
    (ι : ((Fin n × Fin m → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin m) (Fv F v) → ℂ))
    (hbij : Set.BijOn ι (SB (Fin n × Fin m → Fv F v) : Set _) (GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v)) : Set _))
    (hmod : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin m → Fv F v),
      ∃ φ₁ ∈ SB (Fin n × Fin m → Fv F v), Acts (evFin F v) (om (g, h)) φ φ₁ ∧
        ι φ₁ = GlobalTheory.SplitFlip.omB ν α (cX g) (cW h) (ι φ))
    (hfact : ∃ (φ : (Fin n × Fin m → Fv F v) → ℂ) (r : (Fin n × Fin m → AF F) → ℂ),
      Rest (evFin F v) φ r ∧ Φ = tens (evFin F v) φ r)
    {Γ' U : Type} [Group Γ'] [AddCommGroup U] [Module ℂ U] (j : Γ' → GL (Fin m) (Fv F v)) (π : Representation ℂ Γ' U)
    (hπ : π.IsIrreducible) (LW : Γ' →* UA σ W.J) (hLW : ∀ h, LW h ∈ UAt σ W (evFin F v) ∧ cW (LW h) = j h)
    (LX : GL (Fin n) (Fv F v) →* UA σ X.J) (hLX : ∀ g, LX g ∈ UAt σ X (evFin F v) ∧ cX (LX g) = g)
    (hLX' : ∀ k ∈ UAt σ X (evFin F v), ∃ g, LX g = k)
    (hloc : ∀ y : UA σ W.J, (fun z => f (z * y)) ∈
      GlobalTheory.LocTypeGood.imgSpan π ((GlobalTheory.PRep.rightReg ℂ (UA σ W.J) ℂ).comp LW))
    (howe : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (Fv F v)) V), ρ.IsIrreducible →
      ∀ P : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v)) →ₗ[ℂ] U →ₗ[ℂ] V, P ≠ 0 →
        (∀ g h (Ψ Ψ' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v))),
          (Ψ' : Matrix (Fin n) (Fin m) (Fv F v) → ℂ) = GlobalTheory.SplitFlip.omB ν⁻¹ α⁻¹ g (j h) Ψ →
          ∀ u, P Ψ' (π h u) = ρ g (P Ψ u)) → ∀ g w, ρ g w = w) :
    QuotTriv (UAtSub σ X (evFin F v)) (liftSpace om Φ μ 𝓕 f v) := by
  classical
  set M : Submodule ℂ (UA σ W.J → ℂ) := Submodule.span ℂ (funAt f v) with hM
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin m), om x Φ ∈ schA F (Fin n × Fin m) := fun x Φ hΦ =>
    (IsUWeilPair.isUSplitting hom).pres x Φ hΦ
  have omg : ∀ (g k : UA σ X.J) (h x : UA σ W.J) Φ, om (g, h) (om (k, x) Φ) = om (g * k, h * x) Φ := fun g k h x Φ => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]
  have thInv : ∀ g, ∀ γ ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin m), ∀ h,
      thetaSum F (om (g, γ * h) Φ) = thetaSum F (om (g, h) Φ) := fun g γ hγ Φ hΦ h => by
    have e : om (g, γ * h) Φ = om (1, γ) (om (g, h) Φ) := by rw [omg, one_mul]
    rw [e]
    exact GlobalTheory.T.weilRep_rationalDarboux_fixes_thetaDistribution F E σ hcm ψ hψ n m X.J W.J hX hXd hY hYd co hco χX χY hχX hχY om hom 1 (one_mem _) γ hγ _
      (pres _ _ hΦ)
  have memL : ∀ u ∈ M, ∀ γ ∈ ratU σ W.J, ∀ h, u (γ * h) = u h := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u h =>
      obtain ⟨a, -, rfl⟩ := h
      intro γ hγ h
      simp only [rt, mul_assoc]
      exact hfl γ hγ _
    | zero => intro γ _ h; rfl
    | add u w _ _ hu hw => intro γ hγ h; simp [hu γ hγ h, hw γ hγ h]
    | smul c u _ hu => intro γ hγ h; simp [hu γ hγ h]
  have stabM : ∀ x ∈ UAt σ W (evFin F v), ∀ u ∈ M, rt x u ∈ M := by
    intro x hx u hu
    refine (Submodule.span_le (p := M.comap (rtL x))).2 ?_ hu
    rintro _ ⟨a, ha, rfl⟩
    exact Submodule.subset_span ⟨x * a, (UAtSub σ W (evFin F v)).mul_mem hx ha, rt_rt x a f⟩
  have intg : ∀ g, ∀ u ∈ M, ∀ Φ ∈ schA F (Fin n × Fin m),
      IntegrableOn (fun h => u h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ))) 𝓕 μ := by
    intro g u hu
    induction hu using Submodule.span_induction with
    | mem u h =>
      obtain ⟨a, -, rfl⟩ := h
      intro Φ hΦ
      have h1 := GlobalTheory.T.darboux_symplectic_hermitian_skew F E σ hK hcm ψ hψ n m X.J W.J hX hXd hY hYd co hco χX χY hχX hχY om hom f hfc hfl hfd
        (om (1, a⁻¹) Φ) (pres _ _ hΦ) g μ 𝓕 hμ h𝓕
      have h2 := (GlobalTheory.T.automorphic_integrable_on_domain F E σ hcm m W.J hY hYd μ 𝓕 hμ h𝓕 _ (fun γ hγ h => by
        rw [hfl γ hγ h, thInv g γ hγ _ (pres _ _ hΦ) h]) a).1 h1
      have e : (fun h => f (h * a) * (starRingEnd ℂ) (thetaSum F (om (g, h * a) (om (1, a⁻¹) Φ)))) =
          fun h => rt a f h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ)) := funext fun h => by
        rw [omg, mul_inv_cancel_right, mul_one]; rfl
      rwa [e] at h2
    | zero => intro Φ _; simp [integrableOn_zero]
    | add u w _ _ hu hw =>
      intro Φ hΦ
      refine ((hu Φ hΦ).add (hw Φ hΦ)).congr (Eventually.of_forall fun h => ?_)
      simp [add_mul]
    | smul c u _ hu =>
      intro Φ hΦ
      refine ((hu Φ hΦ).const_mul c).congr (Eventually.of_forall fun h => ?_)
      simp [mul_assoc]
  set Λ := fun (u : UA σ W.J → ℂ) (Φ : (Fin n × Fin m → AF F) → ℂ) => thLift om Φ μ 𝓕 u with hΛ
  have Λaddu : ∀ u ∈ M, ∀ w ∈ M, ∀ Φ ∈ schA F (Fin n × Fin m), Λ (u + w) Φ = Λ u Φ + Λ w Φ := by
    intro u hu w hw Φ hΦ
    funext g
    simp only [hΛ, Pi.add_apply, thLift_def, theta, ← integral_add (intg g u hu Φ hΦ) (intg g w hw Φ hΦ)]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp [add_mul]
  have Λsmulu : ∀ (c : ℂ) (u : UA σ W.J → ℂ) Φ, Λ (c • u) Φ = c • Λ u Φ := by
    intro c u Φ
    funext g
    simp only [hΛ, Pi.smul_apply, smul_eq_mul, thLift_def, theta, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp [mul_assoc]
  have ΛaddΦ : ∀ u ∈ M, ∀ Φ ∈ schA F (Fin n × Fin m), ∀ Ψ ∈ schA F (Fin n × Fin m), Λ u (Φ + Ψ) = Λ u Φ + Λ u Ψ := by
    intro u hu Φ hΦ Ψ hΨ
    funext g
    simp only [hΛ, Pi.add_apply, thLift_def, theta, ← integral_add (intg g u hu Φ hΦ) (intg g u hu Ψ hΨ)]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp only [map_add]
    rw [thetaSum_add F (pres _ _ hΦ) (pres _ _ hΨ), map_add, mul_add]
  have ΛsmulΦ : ∀ (c : ℂ) u Φ, Λ u (c • Φ) = (starRingEnd ℂ) c • Λ u Φ := by
    intro c u Φ
    funext g
    simp only [hΛ, Pi.smul_apply, smul_eq_mul, thLift_def, theta, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp only [map_smul]
    rw [thetaSum_smul, map_mul]
    ring
  have Λinv : ∀ u ∈ M, ∀ Φ ∈ schA F (Fin n × Fin m), ∀ k x, Λ (rt x u) (om (k, x) Φ) = rt k (Λ u Φ) := by
    intro u hu Φ hΦ k x
    funext g
    have h2 := (GlobalTheory.T.automorphic_integrable_on_domain F E σ hcm m W.J hY hYd μ 𝓕 hμ h𝓕
      (fun h => u h * (starRingEnd ℂ) (thetaSum F (om (g * k, h) Φ)))
      (fun γ hγ h => by rw [memL u hu γ hγ h, thInv _ γ hγ Φ hΦ h]) x).2
    simp only [hΛ, thLift_def, theta, rt, omg]
    exact h2
  have kex : ∀ Ψ : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v)), ∃ φ ∈ SB (Fin n × Fin m → Fv F v),
      ι φ = fun X => (starRingEnd ℂ) ((Ψ : Matrix (Fin n) (Fin m) (Fv F v) → ℂ) X) := fun Ψ => by
    obtain ⟨φ, hφ, e⟩ := hbij.surjOn (conj_mem_SB Ψ.2)
    exact ⟨φ, hφ, e⟩
  choose kap hkapSB hkap using kex
  have kapEq : ∀ (Ψ : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v))) φ, φ ∈ SB (Fin n × Fin m → Fv F v) →
      ι φ = (fun X => (starRingEnd ℂ) ((Ψ : Matrix (Fin n) (Fin m) (Fv F v) → ℂ) X)) → kap Ψ = φ :=
    fun Ψ φ hφ e => hbij.injOn (hkapSB Ψ) hφ ((hkap Ψ).trans e.symm)
  have kapAdd : ∀ Ψ₁ Ψ₂, kap (Ψ₁ + Ψ₂) = kap Ψ₁ + kap Ψ₂ := fun Ψ₁ Ψ₂ =>
    kapEq _ _ (add_mem (hkapSB Ψ₁) (hkapSB Ψ₂)) (by
      rw [map_add, hkap, hkap]; funext X; simp)
  have kapSmul : ∀ (c : ℂ) Ψ, kap (c • Ψ) = (starRingEnd ℂ) c • kap Ψ := fun c Ψ =>
    kapEq _ _ (Submodule.smul_mem _ _ (hkapSB Ψ)) (by
      rw [map_smul, hkap]; funext X; simp)

  let Co : Set ((Fin n × Fin m → AF F) → ℂ) := {r | Φ ≠ 0 ∧ ∃ φ, Rest (evFin F v) φ r ∧ Φ = tens (evFin F v) φ r}
  have restAll : ∀ r ∈ Co, ∀ φ' ∈ SB (Fin n × Fin m → Fv F v), Rest (evFin F v) φ' r := by
    rintro r ⟨h0, φ, hr, e⟩ φ' hφ'
    refine GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v φ φ' r ?_ hφ' hr
    rintro rfl
    exact h0 (e.trans (funext fun x => zero_mul _))
  have hS : ∀ r ∈ Co, ∀ φ' ∈ SB (Fin n × Fin m → Fv F v), ∀ u ∈ M,
      Λ u (tens (evFin F v) φ' r) ∈ liftSpace om Φ μ 𝓕 f v := by
    intro r hr φ' hφ' u hu
    have hsch := (restAll r hr φ' hφ').2
    induction hu using Submodule.span_induction with
    | mem u h =>
      obtain ⟨h0, φ, hφ, e⟩ := hr
      refine Submodule.subset_span ⟨om (1, 1) (tens (evFin F v) φ' r), ⟨1, (UAtSub σ X (evFin F v)).one_mem, 1,
        (UAtSub σ W (evFin F v)).one_mem, _, Or.inr ⟨h0, φ, φ', r, hφ, e, restAll r ⟨h0, φ, hφ, e⟩ φ' hφ', rfl⟩, rfl⟩,
        u, h, ?_⟩
      rw [show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one, Module.End.one_apply]
    | zero =>
      have := Λsmulu 0 0 (tens (evFin F v) φ' r)
      rw [zero_smul, zero_smul] at this
      rw [this]
      exact zero_mem _
    | add u w hu' hw' hu hw => rw [Λaddu u hu' w hw' _ hsch]; exact add_mem hu hw
    | smul c u _ hu => rw [Λsmulu]; exact Submodule.smul_mem _ _ hu
  have mkQ : ∀ r ∈ Co, ∀ T : U →ₗ[ℂ] (UA σ W.J → ℂ), (∀ u, T u ∈ M) →
      ∃ Q : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v)) →ₗ[ℂ] U →ₗ[ℂ] (UA σ X.J → ℂ),
        ∀ Ψ u, Q Ψ u = Λ (T u) (tens (evFin F v) (kap Ψ) r) := by
    intro r hr T hT
    have tmem : ∀ Ψ, tens (evFin F v) (kap Ψ) r ∈ schA F (Fin n × Fin m) := fun Ψ => (restAll r hr _ (hkapSB Ψ)).2
    exact ⟨LinearMap.mk₂ ℂ (fun Ψ u => Λ (T u) (tens (evFin F v) (kap Ψ) r))
      (fun Ψ₁ Ψ₂ u => by
        simp only [kapAdd, tens_add]
        exact ΛaddΦ _ (hT u) _ (tmem Ψ₁) _ (tmem Ψ₂))
      (fun c Ψ u => by
        simp only [kapSmul, tens_smul]
        rw [ΛsmulΦ, Complex.conj_conj])
      (fun Ψ u w => by
        simp only [map_add]
        exact Λaddu _ (hT u) _ (hT w) _ (tmem Ψ))
      (fun c Ψ u => by
        simp only [map_smul]
        exact Λsmulu c _ _), fun _ _ => rfl⟩
  refine quotTriv_of_pairings LX (UAtSub σ X (evFin F v)) (fun g => (hLX g).1) hLX' _ (rStable_liftSpace om Φ μ 𝓕 f v)
    (fun g h (Ψ Ψ' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v))) =>
      (Ψ' : Matrix (Fin n) (Fin m) (Fv F v) → ℂ) = GlobalTheory.SplitFlip.omB ν⁻¹ α⁻¹ g (j h) Ψ) π howe
    {Q | ∃ r ∈ Co, ∃ T : U →ₗ[ℂ] (UA σ W.J → ℂ), (∀ h u, T (π h u) = rt (LW h) (T u)) ∧ (∀ u, T u ∈ M) ∧
      ∀ Ψ u, Q Ψ u = Λ (T u) (tens (evFin F v) (kap Ψ) r)} ?_ ?_ ?_
  · rintro Q ⟨r, hr, T, -, hT, hQ⟩ Ψ u
    rw [hQ]
    exact hS r hr _ (hkapSB Ψ) _ (hT u)
  · rintro Q ⟨r, hr, T, hTe, hT, hQ⟩ g h Ψ Ψ' hΨ u
    obtain ⟨φ₁, hφ₁, hact, e₁⟩ := hmod _ (hLX g).1 _ (hLW h).1 (kap Ψ) (hkapSB Ψ)
    have hk : kap Ψ' = φ₁ := kapEq _ _ hφ₁ (by
      rw [e₁, hkap, (hLX g).2, (hLW h).2, hΨ, conj_omB hν hα])
    rw [hQ, hQ, hk, ← hact r (restAll r hr _ (hkapSB Ψ)), hTe]
    exact Λinv _ (hT u) _ (restAll r hr _ (hkapSB Ψ)).2 _ _
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨k, hk, h, hh, Φ', hΦ', rfl⟩, f', hf', rfl⟩
    by_cases h0 : Φ = 0
    · have e : Φ' = 0 := by
        rcases hΦ' with e | e
        · exact e.trans h0
        · exact absurd h0 e.1
      have := ΛsmulΦ 0 f' 0
      rw [zero_smul, map_zero, zero_smul] at this
      rw [e, map_zero]
      show Λ f' 0 ∈ _
      rw [this]
      exact zero_mem _
    obtain ⟨r, hr, φ', hφ'r, rfl⟩ : ∃ r ∈ Co, ∃ φ', Rest (evFin F v) φ' r ∧ Φ' = tens (evFin F v) φ' r := by
      rcases hΦ' with e | ⟨-, φ, φ', r, h1, h2, h3, h4⟩
      · obtain ⟨φ, r, h1, h2⟩ := hfact
        exact ⟨r, ⟨h0, φ, h1, h2⟩, φ, h1, e.trans h2⟩
      · exact ⟨r, ⟨h0, φ, h1, h2⟩, φ', h3, h4⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      obtain ⟨-, φ, -, e⟩ := hr
      exact h0 (e.trans (funext fun x => mul_zero _))
    have hφ' := GlobalTheory.T.local_factor_schwartz_bruhat F _ v φ' r hφ'r hr0
    obtain ⟨φ₁, hφ₁, hact, -⟩ := hmod k hk h hh φ' hφ'
    have hΨ₀ : (fun X => (starRingEnd ℂ) (ι φ₁ X)) ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v)) :=
      conj_mem_SB (hbij.mapsTo hφ₁)
    have hk₁ : kap ⟨_, hΨ₀⟩ = φ₁ := kapEq _ _ hφ₁ (by funext X; simp)
    rw [hact r hφ'r]
    have hsch := (restAll r hr φ₁ hφ₁).2
    have hf'M : f' ∈ M := Submodule.subset_span hf'
    have hsp := GlobalTheory.T.invariant_submodule_in_image_span Γ' U _ π ((GlobalTheory.PRep.rightReg ℂ (UA σ W.J) ℂ).comp LW) hπ M
      (fun g w hw => stabM _ (hLW g).1 w hw) f' hf'M (by obtain ⟨y, -, rfl⟩ := hf'; exact hloc y)
    clear hf' hf'M
    suffices key : f' ∈ M ∧ Λ f' (tens (evFin F v) φ₁ r) ∈ Submodule.span ℂ
        {y | ∃ Q ∈ {Q : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v)) →ₗ[ℂ] U →ₗ[ℂ] (UA σ X.J → ℂ) |
          ∃ r ∈ Co, ∃ T : U →ₗ[ℂ] (UA σ W.J → ℂ), (∀ h u, T (π h u) = rt (LW h) (T u)) ∧ (∀ u, T u ∈ M) ∧
            ∀ Ψ u, Q Ψ u = Λ (T u) (tens (evFin F v) (kap Ψ) r)}, ∃ a u, y = Q a u} from key.2
    induction hsp using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨T, hTe, hT, u, rfl⟩ := hw
      obtain ⟨Q, hQ⟩ := mkQ r hr T hT
      refine ⟨hT u, Submodule.subset_span ⟨Q, ⟨r, hr, T, fun h u => LinearMap.congr_fun (hTe h) u, hT, hQ⟩,
        ⟨_, hΨ₀⟩, u, ?_⟩⟩
      rw [hQ, hk₁]
    | zero =>
      have := Λsmulu 0 0 (tens (evFin F v) φ₁ r)
      rw [zero_smul, zero_smul] at this
      rw [this]
      exact ⟨zero_mem _, zero_mem _⟩
    | add u w _ _ hu hw => exact ⟨add_mem hu.1 hw.1, by rw [Λaddu u hu.1 w hw.1 _ hsch]; exact add_mem hu.2 hw.2⟩
    | smul c u _ hu => exact ⟨Submodule.smul_mem _ _ hu.1, by rw [Λsmulu]; exact Submodule.smul_mem _ _ hu.2⟩

theorem exists_isSkew_chain {B : Base F E} (hB : B.IsGood σ) {d d₁ p : ℕ} {W : Spc F E d} {r s : ℕ} (hW : W.IsSkew σ B r s)
    {H' : Plane E d d₁} {i₀ i₁ : ℕ} {sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j)}
    {pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))} (hH : H'.IsAdapted σ B W (sp 0) i₀ i₁)
    (hiso : ∀ i < p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) :
    ∀ j < p, ∃ (Z : Spc F E (d₁ - 2 * j)) (r₁ s₁ : ℕ), Z.J = (sp j).J ∧ Z.IsSkew σ B r₁ s₁ := by
  have hdet : ∀ j < p, (sp j).J.det ≠ 0 := fun j hj =>
    Nondeg.det_ne_zero_of_cartan B (sp j) (hiso j hj).2.2.2.2.2.2.1
  intro j
  induction j with
  | zero =>
    intro h0
    exact GlobalTheory.T.skew_plane_gram_of_complement F E σ B hB d d₁ W r s hW H' (sp 0).J hH.rank hH.xx hH.yy hH.xy hH.orth hH.gram (hdet 0 h0)
  | succ j ih =>
    intro hj
    obtain ⟨Z, r₁, s₁, e, hZ⟩ := ih (by omega)
    obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hiso j (by omega)
    rw [← e] at h2 h3 h4 h5 h6
    exact GlobalTheory.T.skew_plane_gram_of_complement F E σ B hB _ _ Z r₁ s₁ hZ (pl j) (sp (j + 1)).J h1 h2 h3 h4 h5 h6 (hdet _ hj)

theorem resEta_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {a b m k : ℕ} (h : ResEtaPow K χ a) (h' : ResEtaPow K χ' b)
    (hm : a + b = m + 2 * k) : ResEtaPow K (χ / χ') m := fun x => by
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x]
  have e : (-1 : ℂ) ^ m = (-1) ^ (a + b) := by rw [hm, pow_add, pow_mul]; norm_num
  split_ifs
  · simp
  · rw [e]; rcases neg_one_pow_eq_or ℂ b with e' | e' <;> simp [pow_add, e', div_neg]

theorem locMat_liftU (hcm : IsCMExt F E σ) {v : Pl F} (τ : E →ₐ[F] Fv F v) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    GlobalTheory.KSplit.locMat τ 1 (GlobalTheory.SplitUnitLift.liftU hcm τ J ε herm hJ g) = g := by
  apply Units.ext
  rw [GlobalTheory.KSplit.locMat_val, GlobalTheory.SplitUnitLift.liftU_piW, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]

theorem quotTriv_liftSpace : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
      (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))), H'.IsAdapted σ B G.W (sp 0) i₀ i₁ →
      (∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) → ∀ c : ℂ,
      BetaZero (sp 0) H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (Diffs B G X om om' R Rf c) →
      (∀ j < G.p, BetaZero (sp (j + 1)) (pl j) X.α X.β ((a' : ℝ) / 2) (zb a j) (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) j)) →
      ∀ i < G.p, ∀ f ∈ Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) i, IsCT (W := sp i) (pl i) f 0 → (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) →
      ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F G.V'.J) (incM F (sp i).J)) (Fin a' × Fin (d₁ - 2 * i)),
        (∀ x : Matrix (Fin a') (Fin (d₁ - 2 * i)) E, ∃ y z : Fin a' × Fin (d₁ - 2 * i) → F,
          co.e (incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
      ∀ om₁ : UA σ G.V'.J × UA σ (sp i).J →* Module.End ℂ ((Fin a' × Fin (d₁ - 2 * i) → AF F) → ℂ),
        IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F (sp i).J) co X.α (X.α / X.β) om₁ →
      ∀ Φ ∈ schA F (Fin a' × Fin (d₁ - 2 * i)), ∀ (μ : Measure (UA σ (sp i).J)) (𝓕 : Set (UA σ (sp i).J)), μ.IsHaarMeasure →
        IsFundamentalDomain (ratU σ (sp i).J) 𝓕 μ →
      ∃ T : Finset (Pl F), ∀ v : Pl F, v ∉ T → SplitsFully E v → QuotTriv (UAtSub σ G.V' (evFin F v)) (liftSpace (X := G.V') (W := sp i) om₁ Φ μ 𝓕 f v) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH hiso c h0 hj i hi f hf _ hdec co hco om₁ hW Φ hΦ
    μ 𝓕 hμ h𝓕
  classical
  have hT := hM.triple
  have hcm := hT.base.cm
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hsk := NextStep.skew_sp hσ B hT.geo.hW.skew hH hiso i hi.le
  have hd := Nondeg.det_ne_zero_of_cartan B (sp i) (hiso i hi).2.2.2.2.2.2.1
  have hdV := GlobalTheory.OppLagr.det_ne_zero_herm hT.geo.hV'
  have hν : IsHecke F E (X.α / X.β) := ⟨hT.chars.heckeα.1.div' hT.chars.heckeβ.1, fun x => by
    rw [MonoidHom.div_apply, hT.chars.heckeα.2 x, hT.chars.heckeβ.2 x, div_one]⟩
  have hrank := hH.rank
  have hrk := (hiso i hi).1
  have hbig := hT.geo.eBig
  have hres : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (X.α / X.β) (d₁ - 2 * i) :=
    resEta_div (k := i + 1) hT.chars.resα hT.chars.resβ (by omega)
  obtain ⟨hfc, hfl⟩ := Nondeg.lev_reg hK hM hH hiso c h0 hj i hi f hf
  obtain ⟨T, hTf⟩ := GlobalTheory.T.schwartz_function_factorizes_almost_all F _ Φ hΦ
  refine ⟨T ∪ X.T, fun v hv hs => ?_⟩
  rw [Finset.mem_union, not_or] at hv
  obtain ⟨τ⟩ := GlobalTheory.T.split_place_embedding_exists F E σ hcm v hs
  obtain ⟨Z, r₁, s₁, eZ, hZ⟩ := exists_isSkew_chain hT.base hT.geo.hW hH hiso i hi
  have hZ' : (⟨(sp i).J, Z.L, Z.θ, Z.bas⟩ : Spc F E (d₁ - 2 * i)).IsSkew σ B r₁ s₁ := by rw [← eZ]; exact hZ
  obtain ⟨ι, hbij, hmod⟩ := exists_linear_model hK.base hT.base hT.geo.hV' hZ' co hco hT.chars.heckeα hν hT.chars.resα hres
    om₁ hW v τ
  have hα := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.α hT.chars.heckeα v τ).1
  have hβ := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.β hT.chars.heckeβ v τ).1
  have hdiv : chrW (X.α / X.β) τ = chrW X.α τ / chrW X.β τ := by
    ext x
    simp [chrW, locChar, div_eq_mul_inv]
  have hermW : ∀ k l, σ ((sp i).J l k) = algebraMap F E (-1) * (sp i).J k l := fun k l => by
    rw [hsk k l, map_neg, map_one, neg_one_mul]
  have hermV : ∀ k l, σ (G.V'.J l k) = algebraMap F E 1 * G.V'.J k l := fun k l => by
    rw [hT.geo.hV'.herm k l, map_one, one_mul]
  have hJW : IsUnit ((sp i).J.map τ).det := isUnit_iff_ne_zero.2 (GlobalTheory.OppLagr.det_map_ne_zero hd τ)
  have hJV : IsUnit (G.V'.J.map τ).det := isUnit_iff_ne_zero.2 (GlobalTheory.OppLagr.det_map_ne_zero hdV τ)
  have hm : a - 2 * (i + 1) + a' = d₁ - 2 * i := by omega
  have hloc := locType_lev hK F E σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH hiso c h0 hj i hi v
    ⟨hv.2, hs⟩ τ hcm (-1) hermW hJW (finCongr hm) f hf
  rw [hdiv] at hmod
  exact quotTriv_of_model hK hcm B.ψ hT.base.std G.V' (sp i) hT.geo.hV'.herm hdV hsk hd co hco X.α (X.α / X.β)
    hT.chars.heckeα hν om₁ hW f hfc hfl hdec Φ μ 𝓕 hμ h𝓕 v (chrW X.α τ / chrW X.β τ) (chrW X.α τ)
    (fun x => by simp [hα.2 x, hβ.2 x]) hα.2 (GlobalTheory.KSplit.locMat τ 1) (GlobalTheory.KSplit.locMat τ 1) ι hbij hmod (hTf v hv.1)
    (GlobalTheory.LocTypeGood.glReindex (finCongr hm)) _ (GlobalTheory.T.determinant_induced_irreducible_admissible hK _ _ _ _ _ hα hβ).1
    ((GlobalTheory.SplitUnitLift.liftU hcm τ (sp i).J (-1) hermW hJW).comp (GlobalTheory.LocTypeGood.glReindex (finCongr hm)))
    (fun h => ⟨GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm τ (sp i) (-1) hermW hJW _, locMat_liftU hcm τ _ _ hermW hJW _⟩)
    (GlobalTheory.SplitUnitLift.liftU hcm τ G.V'.J 1 hermV hJV)
    (fun g => ⟨GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm τ G.V' 1 hermV hJV _, locMat_liftU hcm τ _ _ hermV hJV _⟩)
    (fun k hk => ⟨_, (GlobalTheory.SchurCharV.eq_liftU_of_UAt hcm τ G.V' hermV hJV k hk).symm⟩) hloc
    (fun V _ _ ρ hρ P hP hlaw => howe_trivial hK (by omega) hm hα hβ V ρ hρ P hP hlaw)

end Global

end GlobalTheory.ThK.SplitQuot

end
