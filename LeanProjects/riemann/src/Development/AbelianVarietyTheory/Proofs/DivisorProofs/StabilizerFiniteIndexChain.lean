import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantStabilizerIwasawaLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjStabilizersSelfDualLatticesUnramified
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanMajorantStabilisersConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWittFrameFirstColumnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeAdaptedWittFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCommutesMajorantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMajorantFrameStabilizerStatement
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.GoodPos

theorem stab_conj_levelAll : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n n₁ : ℕ) (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (V₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n₁)
    (r s i₀ i₁ : ℕ) (H : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane E n n₁), B.IsGood σ → V.IsHerm σ B r s → H.IsAdapted σ B V V₁ i₀ i₁ →
    ∀ K : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ V.J), GlobalTheory.ThK.IsStab (X := V) B K →
      ∃ (m : ℕ) (X Y : Matrix (Fin n) (Fin (m + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E))
        (c : GAd σ ((1 : E) • V.J.map σ)),
        IsWittFrame σ ((1 : E) • V.J.map σ) X Y ∧ GlobalTheory.EisLine.IsAdapted σ ((1 : E) • V.J.map σ) X Y L a ∧
        col0 X = Matrix.of (fun i (_ : Fin 1) => H.x i) ∧
        ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ V.J, g ∈ K ↔ ∃ k ∈ levelAll σ ((1 : E) • V.J.map σ) L a,
          (g : GL (Fin n) (AF F ⊗[F] E)) = matHom _ σ _ c * matHom _ σ _ k * (matHom _ σ _ c)⁻¹ := by
  intro F E _ _ _ _ _ σ B n n₁ V V₁ r s i₀ i₁ H hB hV hH K hK
  classical
  have hJ : (1 : E) • V.J.map σ = V.Jᵀ := by
    ext i j; simp [Matrix.transpose_apply, hV.herm j i]
  rw [hJ]
  have hND : IsHermND σ V.Jᵀ := GlobalTheory.IwLine.isHermND_transpose hV
  haveI hLat : V.L.IsLattice E := hV.lat
  have hSD : ∀ v, IsSelfDualAt σ V.Jᵀ V.L v := GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose F E σ B n V r s hB hV
  obtain ⟨m, X, Y, hW, hc0⟩ := GlobalTheory.T.exists_witt_frame_first_column F E σ B n n₁ V V₁ r s i₀ i₁ H hB hV hH
  obtain ⟨L, a, hA⟩ := GlobalTheory.T.exists_lattice_adapted_witt_frame F E σ hB.cm hB.unram n V.Jᵀ hND V.L hLat hSD (m + 1) X Y hW
  haveI : L.IsLattice E := hA.lat
  have hfin : ∀ v, ∃ g : GLoc σ V.Jᵀ v, ∀ k : GLoc σ V.Jᵀ v,
      k ∈ stabLoc σ V.Jᵀ V.L v ↔ g⁻¹ * k * g ∈ stabLoc σ V.Jᵀ L v := fun v =>
    GlobalTheory.SelfDualStabConj.exists_conj_stabLoc F E σ hB.cm hB.unram n V.Jᵀ hND L V.L hA.lat hLat v (hA.dual v) (hSD v)
  choose gf hgf using hfin
  set S := (Filter.eventually_cofinite.1 (eventually_latLoc_eq (F := F) L V.L)).toFinset with hS
  have hoff : ∀ v, v ∉ S → stabLoc σ V.Jᵀ L v = stabLoc σ V.Jᵀ V.L v := fun v hv => by
    have heq : latLoc F L v = latLoc F V.L v := by
      by_contra h
      exact hv ((Set.Finite.mem_toFinset _).2 h)
    unfold stabLoc
    rw [heq]
  obtain ⟨cf, hcf1, hcf2⟩ := GlobalTheory.IwLine.exists_fin_comp σ V.Jᵀ gf S
  obtain ⟨a₀, ha₀, hK₀⟩ := GlobalTheory.T.exists_majorant_frame_stabilizer F E σ B n V r s hB hV
  have harch : ∀ w, ∃ g : GArch σ V.Jᵀ w, ∀ k : GArch σ V.Jᵀ w,
      k ∈ stabArch σ V.Jᵀ w (Formalism.UG.bc (compInf F E w) a₀) ↔ g⁻¹ * k * g ∈ stabArch σ V.Jᵀ w (Formalism.UG.bc (compInf F E w) a) :=
    GlobalTheory.MajorantConj.stabArch_conj F E σ hB.cm n V.Jᵀ hND a a₀ hA.maj ha₀
  choose ga hga using harch
  obtain ⟨ca, hca1, hca2⟩ := GlobalTheory.IwLine.exists_arch_comp σ V.Jᵀ ga
  set c := ca * cf with hc
  have cA : ∀ w, projArch σ V.Jᵀ w c = ga w := fun w => by rw [hc, map_mul, hca2 w, hcf1 w, mul_one]
  have cF : ∀ v, proj σ V.Jᵀ v c = if v ∈ S then gf v else 1 := fun v => by rw [hc, map_mul, hca1 v, hcf2 v, one_mul]
  have key : ∀ g' : GAd σ V.Jᵀ, GlobalTheory.IwLine.ofGAd σ V.J g' ∈ K ↔ c⁻¹ * g' * c ∈ levelAll σ V.Jᵀ L a := by
    intro g'
    rw [(hK _).trans (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B V _).symm, mem_levelAll]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := GlobalTheory.T.stabilizer_commutes_majorant F E σ B n V hLat g' h
      refine ⟨fun v => ?_, fun w => ?_⟩
      · rw [map_mul, map_mul, map_inv, cF v]
        split_ifs with hv
        · exact (hgf v _).1 (h2 v)
        · rw [inv_one, one_mul, mul_one, hoff v hv]; exact h2 v
      · rw [map_mul, map_mul, map_inv, cA w]
        exact (hga w _).1 ((hK₀ w _).2 (h1 w))
    · rintro ⟨h2, h1⟩
      refine GlobalTheory.KBridge.ofGAd_mem_stabK F E σ B n V hLat g' (fun w => ?_) (fun v => ?_)
      · have := h1 w
        rw [map_mul, map_mul, map_inv, cA w] at this
        exact (hK₀ w _).1 ((hga w _).2 this)
      · have := h2 v
        rw [map_mul, map_mul, map_inv, cF v] at this
        split_ifs at this with hv
        · exact (hgf v _).2 this
        · rw [inv_one, one_mul, mul_one, hoff v hv] at this; exact this
  refine ⟨m, X, Y, L, a, c, hW, hA, hc0, fun g => ?_⟩
  set g' := (GlobalTheory.IwLine.ofGAd σ V.J).symm g with hg'
  have key' : g ∈ K ↔ c⁻¹ * g' * c ∈ levelAll σ V.Jᵀ L a := by
    have := key g'
    rwa [hg', MulEquiv.apply_symm_apply] at this
  have hmat : (g : GL (Fin n) (AF F ⊗[F] E)) = matHom (AF F) σ V.Jᵀ g' :=
    Units.ext (GlobalTheory.IwLine.matHom_ofGAd_symm σ V.J g).symm
  rw [key', hmat]
  constructor
  · intro hk
    refine ⟨_, hk, ?_⟩
    simp only [map_mul, map_inv]
    group
  · rintro ⟨k, hk, e⟩
    have : g' = c * k * c⁻¹ := matHom_injective (AF F) σ V.Jᵀ (by rw [e]; simp only [map_mul, map_inv])
    rw [this]
    simpa [mul_assoc] using hk

end GlobalTheory.GoodPos
