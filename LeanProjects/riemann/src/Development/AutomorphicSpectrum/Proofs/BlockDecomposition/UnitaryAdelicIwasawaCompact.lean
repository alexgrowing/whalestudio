import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagTransitiveOfBaseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMaxEvenAdaptedLatticeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianRingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianHasBaseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFormHermitianPerfectStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalWittFrameStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeMaxEvenAlmostAllStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeStabilizerCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxEvenLatticeFlagTransitiveLocalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockTriangularMemMinimalParabolicLocalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockTriangularMemMinimalParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMatrixMapBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMatrixOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxEvenLatticeAdaptedBasisStatement

set_option linter.unusedSectionVars false

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin

open GlobalTheory.CompanionTheory.KFin Filter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem matHom_mapH_kfin {A A' : Type} [CommRing A] [Algebra F A] [TopologicalSpace A] [CommRing A'] [Algebra F A']
    [TopologicalSpace A'] (φ : A →ₐ[F] A') (g : HA A σ J) :
    (matHom A' σ J (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ J φ g)).1 =
      (matHom A σ J g).1.map (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  ext i j
  exact GlobalTheory.AutFunCompare.mat_mapH _ _ _ _ _ _

theorem map_adMat_kfin {A A' : Type} [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A'] (φ : A →ₐ[F] A')
    (X : Matrix (Fin n) (Fin r) E) :
    (X.map (inclR (F := F) A)).map (Algebra.TensorProduct.map φ (AlgHom.id F E)) = X.map (inclR (F := F) A') := by
  ext i j
  simp [inclR]

theorem flag_map_kfin {A A' : Type} [CommRing A] [Algebra F A] [TopologicalSpace A] [CommRing A'] [Algebra F A']
    [TopologicalSpace A'] (φ : A →ₐ[F] A') (g : HA A σ J) (B : Matrix (Fin r) (Fin r) (A ⊗[F] E))
    (h : (matHom A σ J g).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B) :
    (matHom A' σ J (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ J φ g)).1 * X.map (inclR (F := F) A') =
      X.map (inclR (F := F) A') * B.map (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  have := congrArg (fun M : Matrix (Fin n) (Fin r) (A ⊗[F] E) =>
    M.map (Algebra.TensorProduct.map φ (AlgHom.id F E))) h
  rw [Matrix.map_mul, Matrix.map_mul, map_adMat_kfin] at this
  rw [matHom_mapH_kfin]
  exact this

theorem exists_compact_iwasawa_good : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ K : Subgroup (GAd σ J), K ≤ finPts σ J ∧ IsCompact (K : Set (GAd σ J)) ∧ (∀ g ∈ finPts σ J, ∃ p ∈ minPar σ J X, p ∈ finPts σ J ∧ ∃ k ∈ K, g = p * k) ∧ GoodPosition σ J X Y K := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y hW
  obtain ⟨L₀, hL₀, hae⟩ := GlobalTheory.T.lattice_max_even_almost_all hCM hJ hW
  have hT : ∀ v, FlagTransitive (sigR (Fv F v) σ) (intLoc F E v) := fun v => GlobalTheory.T.flag_transitive_of_base _ _ (GlobalTheory.T.local_hermitian_ring hCM v) (GlobalTheory.T.local_hermitian_has_base hCM v)
  have hex : ∀ v, ∃ Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E),
      IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) Λ ∧
      IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) Λ ∧
      (IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F L₀ v) ∧
        IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) (latLoc F L₀ v) → Λ = latLoc F L₀ v) := by
    intro v
    by_cases hg : IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F L₀ v) ∧
        IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) (latLoc F L₀ v)
    · exact ⟨_, hg.1, hg.2, fun _ => rfl⟩
    · obtain ⟨L, h1, h2⟩ := GlobalTheory.T.exists_max_even_adapted_lattice _ (intLoc F E v) (GlobalTheory.T.local_hermitian_ring hCM v) (hR (Fv F v) σ J) (GlobalTheory.T.local_form_hermitian_perfect hCM hJ v).1
        (GlobalTheory.T.local_form_hermitian_perfect hCM hJ v).2 (colV v X) (colV v Y) (GlobalTheory.T.local_witt_frame hCM hJ hW v)
      exact ⟨L, h1, h2, fun h => absurd h hg⟩
  choose Λ hΛ1 hΛ2 hΛ3 using hex
  have hev : ∀ᶠ v in cofinite, Λ v = latLoc F L₀ v := hae.mono fun v h => hΛ3 v h
  have hstab : ∀ v, Λ v = latLoc F L₀ v → (stabLat σ J (Λ v) : Subgroup (GLoc σ J v)) = stabLoc σ J L₀ v := by
    intro v e
    rw [e]
    rfl
  let K : Subgroup (GAd σ J) := finPts σ J ⊓ ⨅ v, (stabLat σ J (Λ v)).comap (proj σ J v)
  have memK : ∀ g, g ∈ K ↔ g ∈ finPts σ J ∧ ∀ v, proj σ J v g ∈ stabLat σ J (Λ v) := fun g => by
    simp [K, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨K, inf_le_left, ?_, ?_, ?_⟩
  ·
    obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, Λ v = latLoc F L₀ v :=
      ⟨(eventually_cofinite.1 hev).toFinset, fun v hv => by simpa using hv⟩
    have hc := (isRestrGroup_GFin σ J L₀).isCompact_cyl S (fun _ => Set.univ)
      (fun v => (stabLat σ J (Λ v) : Set (GLoc σ J v))) (fun e => e.elim)
      (fun v _ => GlobalTheory.T.lattice_stabilizer_compact hCM hJ v (Λ v) (hΛ1 v).1)
    convert hc.image (continuous_ofFin σ J) using 1
    ext g
    rw [SetLike.mem_coe, memK]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ : g ∈ (ofFin σ J).range := by rwa [range_ofFin]
      refine ⟨y, ⟨fun e => e.elim, fun v _ => ?_, fun v hv => ?_⟩, rfl⟩
      · simpa using h2 v
      · rw [← hstab v (hS v hv)]
        simpa using h2 v
    · rintro ⟨y, ⟨-, h1, h2⟩, rfl⟩
      refine ⟨mem_finPts.2 (by simp), fun v => ?_⟩
      rw [proj_ofFin]
      by_cases hv : v ∈ S
      · exact h1 v hv
      · rw [hstab v (hS v hv)]
        exact h2 v hv
  ·
    intro g hg
    have hfin : {v | proj σ J v g ∉ stabLat σ J (Λ v)}.Finite := by
      refine eventually_cofinite.1 ?_
      filter_upwards [hev, eventually_proj_mem_stabLoc σ J L₀ g] with v e hv
      rw [hstab v e]
      exact hv
    let S : Finset (HeightOneSpectrum (𝓞 F)) := hfin.toFinset
    choose pl kl hkl hgl Bl hBl hpl using fun v => GlobalTheory.T.max_even_lattice_flag_transitive_local (X := X) hCM hJ hW v (hT v) (Λ v) (hΛ1 v) (proj σ J v g)
    let x : ∀ v : S, GLoc σ J v := fun v => pl v
    have hp1 : embAt σ J S x ∈ minPar σ J X := by
      have : embAt σ J S x ∈ minParSub X hCM hJ hW := by
        refine Subgroup.noncommProd_mem _ (f := fun v : S => emb σ J v (x v))
          (fun _ _ _ _ h => commute_emb σ J _ (proj_emb_ne σ J (fun e => h (Subtype.ext e)) _)) fun v _ => ?_
        exact GlobalTheory.T.block_triangular_mem_minimal_parabolic_local (Y := Y) v.1 _ (Bl v.1) (hBl v.1) (hpl v.1)
      exact this
    have hp2 := mem_atPts.1 (embAt_mem σ J S x)
    refine ⟨embAt σ J S x, hp1, hp2.1, (embAt σ J S x)⁻¹ * g, (memK _).2 ⟨mul_mem (inv_mem hp2.1) hg, fun v => ?_⟩, by simp⟩
    rw [map_mul, map_inv]
    by_cases hv : v ∈ S
    · have : proj σ J v (embAt σ J S x) = pl v := proj_embAt σ J S x ⟨v, hv⟩
      rw [this, hgl v, inv_mul_cancel_left]
      exact hkl v
    · rw [hp2.2 v hv, inv_one, one_mul]
      by_contra hc
      exact hv (hfin.mem_toFinset.2 hc)
  ·
    rintro p ⟨B, hB, hpB⟩ hpK
    obtain ⟨hpf, hpv⟩ := (memK p).1 hpK
    obtain ⟨m, hm, ⟨d, hd⟩, ⟨d', hd'⟩, ⟨B', hB', hB1, hu⟩, hz⟩ := GlobalTheory.T.block_triangular_mem_minimal_parabolic hCM hJ hW (AF F) p B hB hpB
    have hmf : m ∈ finPts σ J := by
      refine mem_finPts.2 (Subtype.ext (Units.ext ?_))
      have e1 : (matHom _ σ J (projInf σ J m)).1 = 1 := by
        refine (matHom_mapH_kfin (fstA F) m).trans ?_
        rw [hm, ← GlobalTheory.T.levi_matrix_map_base_change]
        have e2 : (matHom _ σ J p).1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 := by
          rw [← matHom_mapH_kfin]
          have := mem_finPts.1 hpf
          change (matHom _ σ J (projInf σ J p)).1 = 1
          rw [this, map_one]
          rfl
        rw [e2]
        exact GlobalTheory.T.levi_matrix_one hCM hJ hW _
      exact e1
    have hmK : m ∈ K := by
      refine (memK m).2 ⟨hmf, fun v => ?_⟩
      refine GlobalTheory.T.max_even_lattice_adapted_basis hCM hJ hW v (Λ v) (hΛ1 v) (hΛ2 v) (proj σ J v p) (proj σ J v m) (hpv v) _
        (hB.map _) (flag_map_kfin (evFin F v) p B hpB) ?_
      refine (matHom_mapH_kfin (evFin F v) m).trans ?_
      rw [hm, ← GlobalTheory.T.levi_matrix_map_base_change, ← matHom_mapH_kfin]
      rfl
    refine ⟨m, ⟨d, d', hd, ?_⟩, hmK, m⁻¹ * p, ⟨B', hB', hB1, hu, fun z hz' => ?_⟩, mul_mem (inv_mem hmK) hpK, by simp⟩
    · exact hd'
    · refine hz _ ?_
      funext i
      refine (RingHom.map_mulVec (inclR (F := F) (AF F)) (cT (σ : E →+* E) X * J) z i).symm.trans ?_
      rw [hz']
      simp

end GlobalTheory.CompanionTheory.KFin

end
