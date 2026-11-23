import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedBasisWittFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedBasisLocalBlockFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplMapSplitProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbNormalises
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactBlockParabolicLeviStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactCuspRepBlockEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAutLinTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalComponentConstantTermStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockForms

theorem exists_isCompAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (B g : GL (Fin n) (Fv F v)), ∃ x : GLoc σ J v, IsCompAt σ J t B g x :=
  by
  intro F E _ _ _ _ _ _ σ hcm n J hJ r Xf Yf hW v t B g
  refine ⟨splitLift hcm hJ t (B * g * B⁻¹), ?_⟩
  have := congrArg Units.val (splitHom_splitLift hcm hJ t (B * g * B⁻¹))
  simpa [IsCompAt, splitHom_val] using this

theorem block_forms : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → GlobalTheory.Published.LanglandsLemmaUnitary →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v), ∃ B : GL (Fin n) (Fv F v),
    ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K → ∀ (φ : GAd σ J → ℂ), IsAut σ J K φ →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) (Fv F v)) V), IsSmooth π →
    ∀ (m : ℕ) (T : Fin m → V →ₗ[ℂ] (GAd σ J → ℂ)) (x : Fin m → V), (∀ j, IsIntertw σ J t B π (T j)) →
      φ = ∑ j, T j (x j) → ∀ (S : Finset (Fin r)) (φc : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspComp σ J Xf Yf S K φ φc → φc ≠ 0 →
      ∀ (l d : ℕ), 1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
        (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
        ∃ (hld : l + d ≤ n) (U : Submodule ℂ (Fin m → V)) (Λ : (Fin m → V) →ₗ[ℂ] GlobalTheory.CuspRep.Sm E d),
          (∀ g : GL (Fin d) (Fv F v), ∀ u ∈ U, (fun j => π (GlobalTheory.SmGL.leviEmb (Fv F v) (tripPlace hld) (midHom (Fv F v) l d n g)) (u j)) ∈ U) ∧
          (∃ u ∈ U, Λ u ≠ 0) ∧ (∀ u ∈ U, GlobalTheory.CuspRep.IsCuspForm (Λ u)) ∧
          (∀ g ∈ GlobalTheory.SmGL.unipRad (Fv F v) (tripPlace hld), ∀ u ∈ U, Λ (fun j => π g (u j)) = Λ u) ∧
          ∀ g : GL (Fin d) (Fv F v), ∀ u ∈ U,
            Λ (fun j => π (GlobalTheory.SmGL.leviEmb (Fv F v) (tripPlace hld) (midHom (Fv F v) l d n g)) (u j)) =
              GlobalTheory.CuspRep.finRep E d (GlobalTheory.CuspRep.locGL E d (splitPrime t) (glEquiv d (complEquiv t (splitPrime_under t)) g)) (Λ u) :=
  by
  intro hKP F E _ _ _ _ _ _ σ hcm n J hJ r Xf Yf hW HL v t
  obtain ⟨C, hC⟩ := GlobalTheory.AdaptedBasis.exists_isAdapted F E σ hcm n J hJ r Xf Yf hW
  refine ⟨Matrix.GeneralLinearGroup.map (t : E →+* Fv F v) C, ?_⟩
  intro K hK φ hφ V _ _ π hπ m T x hT hφx S φc hφc hφc0 l d hd hin hk hl
  have hk' := hk
  obtain ⟨k, hkS, hkv⟩ := hk'
  have hlr : l + d ≤ r := by have := k.2; omega
  have hld : l + d ≤ n := by have := hC.le; omega
  obtain ⟨ι, hι⟩ := GlobalTheory.BlockFormsEmb.exists_blockEmb F E σ hcm n J hJ r Xf Yf hW l d hlr
  refine ⟨hld, ?_⟩
  set B := Matrix.GeneralLinearGroup.map (t : E →+* Fv F v) C with hB
  have hN := GlobalTheory.BlockForms.Norm.blockEmb_normalises F E σ hcm n J hJ r Xf Yf hW S l d hlr ι hι hin hk hl

  let Ttot : (Fin m → V) →ₗ[ℂ] (GAd σ J → ℂ) := ∑ j, (T j).comp (LinearMap.proj j)
  have hTtot : ∀ u, Ttot u = ∑ j, T j (u j) := fun u => by simp [Ttot]
  have hTx : Ttot x = φ := by rw [hTtot, hφx]
  have hTπ : ∀ g y, IsCompAt σ J t B g y → ∀ u, Ttot (fun j => π g (u j)) = fun z => Ttot u (z * emb σ J v y) := by
    intro g y hy u
    funext z
    simp only [hTtot, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => hT j g y hy (u j) z

  let L : GL (Fin n) (Fv F v) → (Fin m → V) →ₗ[ℂ] (Fin m → V) := fun g => LinearMap.pi fun j => (π g).comp (LinearMap.proj j)
  have hL : ∀ g u, L g u = fun j => π g (u j) := fun _ _ => rfl
  let U : Submodule ℂ (Fin m → V) := Submodule.span ℂ (Set.range fun g : GL (Fin n) (Fv F v) => L g x)
  have hUst : ∀ g, ∀ u ∈ U, L g u ∈ U := by
    intro g u hu
    have : U ≤ U.comap (L g) := Submodule.span_le.2 (by
      rintro _ ⟨g', rfl⟩
      refine Submodule.subset_span ⟨g * g', ?_⟩
      funext j
      simp only [hL, map_mul, Module.End.mul_apply])
    exact this hu
  have hAut := GlobalTheory.UAut.AutClosed.isAut_lin_transl F E σ hcm n J hJ K hK
  have hAutU : ∀ u ∈ U, IsAut σ J K (Ttot u) := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨g, rfl⟩ := hw
      show IsAut σ J K (Ttot (L g x))
      obtain ⟨y, hy⟩ := exists_isCompAt F E σ hcm n J hJ r Xf Yf hW v t B g
      rw [hL, hTπ g y hy, hTx]
      exact (hAut φ φ hφ hφ).2 v y
    | zero =>
      rw [map_zero]
      exact isAut_const σ J K 0
    | add a b _ _ ha hb =>
      rw [map_add]
      simpa using (hAut _ _ ha hb).1 1 1
    | smul c a _ ha =>
      rw [map_smul]
      simpa using (hAut _ _ ha ha).1 c 0

  have HLe : ∀ f, IsAut σ J K f → ∃! c, GlobalTheory.StdPar.IsCuspComp σ J Xf Yf S K f c := fun f hf =>
    (HL F E σ hcm n J hJ r Xf Yf hW K hK ∅ f (GlobalTheory.StdPar.isAutOn_empty.2 hf)).1 S (Finset.empty_subset S)
  classical
  let cc : (GAd σ J → ℂ) → (GAd σ J → ℂ) := fun f => if hf : IsAut σ J K f then (HLe f hf).exists.choose else 0
  have hcc : ∀ f, IsAut σ J K f → GlobalTheory.StdPar.IsCuspComp σ J Xf Yf S K f (cc f) := fun f hf => by
    simp only [cc, dif_pos hf]; exact (HLe f hf).exists.choose_spec
  have hccu : ∀ f c, IsAut σ J K f → GlobalTheory.StdPar.IsCuspComp σ J Xf Yf S K f c → cc f = c := fun f c hf hc =>
    (HLe f hf).unique (hcc f hf) hc
  have hccl : ∀ f g, IsAut σ J K f → IsAut σ J K g → ∀ a b : ℂ, cc (a • f + b • g) = a • cc f + b • cc g :=
    fun f g hf hg a b => hccu _ _ ((hAut f g hf hg).1 a b)
      ((GlobalTheory.T.cuspidal_component_constant_term F E σ hcm n J hJ r Xf Yf hW K hK S f g (cc f) (cc g) hf hg (hcc f hf) (hcc g hg)).1 a b)
  have hcct : ∀ f, IsAut σ J K f → ∀ y : GLoc σ J v, cc (fun z => f (z * emb σ J v y)) = fun z => cc f (z * emb σ J v y) :=
    fun f hf y => hccu _ _ ((hAut f f hf hf).2 v y)
      ((GlobalTheory.T.cuspidal_component_constant_term F E σ hcm n J hJ r Xf Yf hW K hK S f f (cc f) (cc f) hf hf (hcc f hf) (hcc f hf)).2 v y)
  have hφcc : cc φ = φc := hccu φ φc hφ hφc

  obtain ⟨g, hg⟩ := Function.ne_iff.1 hφc0
  set x₀ := proj σ J v g
  set g' := g * (emb σ J v x₀)⁻¹ with hg'
  have hg'v : proj σ J v g' = 1 := by simp [hg', x₀]
  have hgg : g = g' * emb σ J v x₀ := by simp [hg']
  obtain ⟨u₁, hu₁, hu₁i, y₀, g₀, hg'e, hg₀⟩ :=
    GlobalTheory.T.max_compact_block_parabolic_levi F E σ hcm n J hJ r Xf Yf hW K hK S l d hlr ι hι hd hin hk hl g'
  have hg₀v : proj σ J v g₀ = 1 := by
    have e : g₀ = (ι (GlobalTheory.CuspRep.infGL E d y₀))⁻¹ * u₁⁻¹ * g' := by rw [hg'e]; group
    rw [e, map_mul, map_mul, map_inv, map_inv, mem_infPts_iff_forall.1 hu₁i v, mem_infPts_iff_forall.1 (hN.2 y₀) v, hg'v]
    simp
  have hcomm : ∀ y : GLoc σ J v, g₀ * emb σ J v y = emb σ J v y * g₀ := fun y => ((commute_emb σ J y hg₀v).eq).symm

  have hS8 : ∀ u : U, ∃ f : GlobalTheory.CuspRep.Sm E d, (∀ h, f.1 h = cc (Ttot u) (ι h * g₀)) ∧ GlobalTheory.CuspRep.IsCuspForm f :=
    fun u => GlobalTheory.T.max_compact_cusp_rep_block_embedding hKP F E σ hcm n J hJ r Xf Yf hW K hK S l d hlr ι hι hd hin hk hl _ (hcc _ (hAutU u u.2)).1 g₀ hg₀
  choose fU hfU using hS8
  have hccU : ∀ u w : U, ∀ a b : ℂ, cc (Ttot ((a • u + b • w : U) : Fin m → V)) = a • cc (Ttot u) + b • cc (Ttot w) := by
    intro u w a b
    rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, map_add, map_smul, map_smul]
    exact hccl _ _ (hAutU u u.2) (hAutU w w.2) a b
  let Λ₀ : U →ₗ[ℂ] GlobalTheory.CuspRep.Sm E d :=
    { toFun := fU
      map_add' := fun u w => Subtype.ext (funext fun h => by
        have e := hccU u w 1 1
        simp only [one_smul] at e
        change (fU (u + w)).1 h = (fU u).1 h + (fU w).1 h
        rw [(hfU _).1, (hfU _).1, (hfU _).1, e]
        rfl)
      map_smul' := fun a u => Subtype.ext (funext fun h => by
        have e := hccU u u a 0
        simp only [zero_smul, add_zero] at e
        change (fU (a • u)).1 h = a * (fU u).1 h
        rw [(hfU _).1, (hfU _).1, e]
        rfl) }
  obtain ⟨U', hU'⟩ := Submodule.exists_isCompl U
  let Λ : (Fin m → V) →ₗ[ℂ] GlobalTheory.CuspRep.Sm E d := Λ₀ ∘ₗ Submodule.projectionOnto U U' hU'
  have hΛ : ∀ u (hu : u ∈ U), Λ u = fU ⟨u, hu⟩ := fun u hu => by
    simp only [Λ, LinearMap.comp_apply]
    have e : Submodule.projectionOnto U U' hU' u = ⟨u, hu⟩ := Submodule.projectionOnto_apply_left hU' ⟨u, hu⟩
    rw [e]
    rfl
  have hΛv : ∀ u (hu : u ∈ U) h, (Λ u).1 h = cc (Ttot u) (ι h * g₀) := fun u hu h => by
    rw [hΛ u hu, (hfU _).1]
  refine ⟨U, Λ, fun g u hu => hUst _ u hu, ?_, fun u hu => by rw [hΛ u hu]; exact (hfU _).2, ?_, ?_⟩
  ·
    obtain ⟨g₁, hg₁⟩ : ∃ g₁, IsCompAt σ J t B g₁ x₀ := by
      refine ⟨B⁻¹ * Matrix.GeneralLinearGroup.map (splitProj t) (matHom _ σ J x₀) * B, ?_⟩
      simp only [IsCompAt]
      rw [show B * (B⁻¹ * Matrix.GeneralLinearGroup.map (splitProj t) (matHom _ σ J x₀) * B) * B⁻¹ =
        Matrix.GeneralLinearGroup.map (splitProj t) (matHom _ σ J x₀) by group]
      rfl
    refine ⟨L g₁ x, Submodule.subset_span ⟨g₁, rfl⟩, fun h0 => hg ?_⟩
    have e := congrArg (fun f : GlobalTheory.CuspRep.Sm E d => f.1 (GlobalTheory.CuspRep.infGL E d y₀)) h0
    simp only [hΛv _ (Submodule.subset_span ⟨g₁, rfl⟩)] at e
    rw [hL, hTπ g₁ x₀ hg₁, hTx, hcct φ hφ x₀, hφcc] at e
    rw [hgg, hg'e, mul_assoc, mul_assoc, hφc.1.1.leftN u₁ hu₁, ← mul_assoc]
    exact e
  ·
    intro g hg u hu
    obtain ⟨y, hy⟩ := exists_isCompAt F E σ hcm n J hJ r Xf Yf hW v t B g
    have hyu := GlobalTheory.T.adapted_basis_local_block_form F E σ hcm n J hJ r Xf Yf hW v t C hC S l d hin hk hl hld g hg y hy
    refine Subtype.ext (funext fun h => ?_)
    rw [hΛv (fun j => π g (u j)) (hUst g u hu), hΛv u hu, hTπ g y hy, hcct _ (hAutU u hu)]
    beta_reduce
    rw [mul_assoc, hcomm, ← mul_assoc,
      show ι h * emb σ J v y * g₀ = (ι h * emb σ J v y * (ι h)⁻¹) * (ι h * g₀) by group]
    exact (hcc _ (hAutU u hu)).1.1.leftN _ (hN.1 h _ hyu) _
  ·
    intro g u hu
    obtain ⟨y, hy, hye⟩ := GlobalTheory.BlockForms.LeviLoc.blockEmb_locGL F E σ hcm n J hJ r Xf Yf hW v t C hC l d hlr hld ι hι g
    refine Subtype.ext (funext fun h => ?_)
    rw [hΛv (fun j => π _ (u j)) (hUst _ u hu), hTπ _ y hy, hcct _ (hAutU u hu)]
    beta_reduce
    rw [mul_assoc, hcomm, ← mul_assoc, hye, ← map_mul]
    change _ = (Λ u).1 (h * _)
    rw [hΛv u hu]

end GlobalTheory.BlockForms

end
