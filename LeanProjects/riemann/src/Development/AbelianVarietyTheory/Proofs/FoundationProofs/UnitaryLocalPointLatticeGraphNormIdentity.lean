import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.GraphHeightLattice
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetSplitPlaceLatticeIntersectionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetInertPlaceLatticeLengthStatement

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)

namespace GlobalTheory.GraphNorm

private theorem pairVec_finSumFinEquiv_injective_eq {X : Type} {n : ℕ} {a b c d : Fin n → X}
    (h : pairVec finSumFinEquiv a b = pairVec finSumFinEquiv c d) : a = c ∧ b = d := by
  constructor
  · funext i
    have h' := congrFun h (finSumFinEquiv (.inl i))
    simpa only [pairVec_inl] using h'
  · funext i
    have h' := congrFun h (finSumFinEquiv (.inr i))
    simpa only [pairVec_inr] using h'
theorem unitaryLocalPoint_latticeGraphNorm_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)) (g : GLoc σ J v) (p : siegelH (Fv F v) σ (dblGram finSumFinEquiv J)) (k : GLoc σ (dblGram finSumFinEquiv J) v), k ∈ KFin σ (dblGram finSumFinEquiv J) L v → ioH (Fv F v) σ rfl (g, 1) = (p : GLoc σ (dblGram finSumFinEquiv J) v) * k → ∀ y : Fin n → Fv F v ⊗[F] E, (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = (leviOf finSumFinEquiv (matHom (Fv F v) σ (dblGram finSumFinEquiv J)) p).1 *ᵥ x := by
  intro F E _ _ _ _ _ σ h n J hJ L _ v g p k hk hpk y
  simp only [KFin] at hk
  unfold GlobalTheory.AdelicU.stabLoc at hk
  rw [Subgroup.mem_comap, latLoc_sumLat] at hk
  simp only [Formalism.UG.stabGL, Subgroup.mem_mk, Set.mem_setOf_eq, Submonoid.mem_mk, Subsemigroup.mem_mk] at hk
  have hmat : (matHom (Fv F v) σ (dblGram finSumFinEquiv J) (p : GLoc σ (dblGram finSumFinEquiv J) v)).1 *
      (matHom (Fv F v) σ (dblGram finSumFinEquiv J) k).1 =
      blkMat finSumFinEquiv (matHom (Fv F v) σ J g).1 1 := by
    have h1 := congrArg (fun x => (matHom (Fv F v) σ (dblGram finSumFinEquiv J) x).1) hpk
    simp only [map_mul, Units.val_mul, matHom_ioH, val_blkGL, map_one, Units.val_one] at h1
    exact h1.symm
  have hkd : KeepsDiag finSumFinEquiv
      (matHom (Fv F v) σ (dblGram finSumFinEquiv J) (p : GLoc σ (dblGram finSumFinEquiv J) v)).1 :=
    mem_siegelOf.mp p.2
  have hkdi : KeepsDiag finSumFinEquiv (matHom (Fv F v) σ (dblGram finSumFinEquiv J)
      ((p⁻¹ : siegelH (Fv F v) σ (dblGram finSumFinEquiv J)) : GLoc σ (dblGram finSumFinEquiv J) v)).1 :=
    mem_siegelOf.mp (p⁻¹).2
  have hPinv : matHom (Fv F v) σ (dblGram finSumFinEquiv J)
      ((p⁻¹ : siegelH (Fv F v) σ (dblGram finSumFinEquiv J)) : GLoc σ (dblGram finSumFinEquiv J) v) =
      (matHom (Fv F v) σ (dblGram finSumFinEquiv J) (p : GLoc σ (dblGram finSumFinEquiv J) v))⁻¹ := by
    rw [Subgroup.coe_inv, map_inv]
  rw [val_leviOf, mem_latMoved]
  set M := matHom (Fv F v) σ (dblGram finSumFinEquiv J) with hM
  set mJ := matHom (Fv F v) σ J with hmJ
  set S := sumLat finSumFinEquiv (latLoc F L v) (latLoc F L v) with hS
  constructor
  · rintro ⟨hy, hyg⟩
    have hw : pairVec finSumFinEquiv ((mJ g⁻¹).1 *ᵥ y) y ∈ S :=
      (pairVec_mem_sumLat finSumFinEquiv).mpr ⟨hyg, hy⟩
    have hz := (hk _).mp hw
    have hPz : (M (p : GLoc σ (dblGram finSumFinEquiv J) v)).1 *ᵥ ((M k).1 *ᵥ pairVec finSumFinEquiv ((mJ g⁻¹).1 *ᵥ y) y) =
        pairVec finSumFinEquiv y y := by
      rw [Matrix.mulVec_mulVec, hmat, blkMat_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul,
        ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]
    have hz_eq : (M k).1 *ᵥ pairVec finSumFinEquiv ((mJ g⁻¹).1 *ᵥ y) y =
        pairVec finSumFinEquiv (leviMat finSumFinEquiv (M ((p⁻¹ : siegelH (Fv F v) σ (dblGram finSumFinEquiv J)) :
          GLoc σ (dblGram finSumFinEquiv J) v)).1 *ᵥ y)
          (leviMat finSumFinEquiv (M ((p⁻¹ : siegelH (Fv F v) σ (dblGram finSumFinEquiv J)) :
          GLoc σ (dblGram finSumFinEquiv J) v)).1 *ᵥ y) := by
      rw [← hkdi.mulVec_diag, ← hPz, Matrix.mulVec_mulVec, hPinv, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hz_eq, pairVec_mem_sumLat] at hz
    refine ⟨_, hz.1, ?_⟩
    have hd := hkd.mulVec_diag (leviMat finSumFinEquiv (M ((p⁻¹ : siegelH (Fv F v) σ (dblGram finSumFinEquiv J)) :
          GLoc σ (dblGram finSumFinEquiv J) v)).1 *ᵥ y)
    rw [← hz_eq, hPz] at hd
    exact (pairVec_finSumFinEquiv_injective_eq hd).1
  · rintro ⟨x, hx, rfl⟩
    have hxx : pairVec finSumFinEquiv x x ∈ S := (pairVec_mem_sumLat finSumFinEquiv).mpr ⟨hx, hx⟩
    obtain ⟨u, hu⟩ : ∃ u, u = (M k⁻¹).1 *ᵥ pairVec finSumFinEquiv x x := ⟨_, rfl⟩
    have hKu : (M k).1 *ᵥ u = pairVec finSumFinEquiv x x := by
      rw [hu, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
        Matrix.one_mulVec]
    have huS : u ∈ S := (hk u).mpr (hKu ▸ hxx)
    have hsplit := (pairVec_eta finSumFinEquiv u).symm
    have hPKu : blkMat finSumFinEquiv (mJ g).1 1 *ᵥ u =
        pairVec finSumFinEquiv (leviMat finSumFinEquiv (M (p : GLoc σ (dblGram finSumFinEquiv J) v)).1 *ᵥ x)
          (leviMat finSumFinEquiv (M (p : GLoc σ (dblGram finSumFinEquiv J) v)).1 *ᵥ x) := by
      rw [← hmat, ← Matrix.mulVec_mulVec, hKu, hkd.mulVec_diag]
    rw [hsplit, blkMat_mulVec, Matrix.one_mulVec] at hPKu
    obtain ⟨h1, h2⟩ := pairVec_finSumFinEquiv_injective_eq hPKu
    rw [hsplit, pairVec_mem_sumLat] at huS
    refine ⟨h2 ▸ huS.2, ?_⟩
    rw [← h1, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
    exact huS.1
private theorem exists_isElemDiv {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    (x : GL (Fin n) (Fv F v)) : ∃ d : Fin n → (Fv F v)ˣ, IsElemDiv x d := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hv : Valued.v ((π : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hπ
  have hϖ0 : ((π : F) : v.adicCompletion F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hmem : ((π : F) : v.adicCompletion F) ∈ Formalism.UG.Ov F v := by
    show _ ∈ v.adicCompletionIntegers F
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hv, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by norm_num)
  obtain ⟨a, -, k₁, hk₁, k₂, hk₂, hx⟩ := Formalism.UG.Final.CartanDecomp F v n _ hmem hv x
  refine ⟨fun i => Units.mk0 (((π : F) : v.adicCompletion F) ^ (a i)) (zpow_ne_zero _ hϖ0), k₁, hk₁, k₂, hk₂, ?_⟩
  rw [hx]
  rfl
private theorem min_self_inv_le_one (a : ℝ≥0) : min a a⁻¹ ≤ 1 := by
  rcases le_total a 1 with h1 | h1
  · exact (min_le_left _ _).trans h1
  · exact (min_le_right _ _).trans (inv_le_one_of_one_le₀ h1)
private theorem natCast_zpow_neg_le_one (N l : ℕ) (hN : 1 ≤ N) : ((N : ℝ≥0)) ^ (-(l : ℤ)) ≤ 1 := by
  rw [zpow_neg, zpow_natCast]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hN))

theorem graphNormFinite : GraphNormFinite := by
  intro F E _ _ _ _ _ σ h n J hJ L _ v hSD
  refine ⟨?_, ?_⟩
  · intro τ β hβ g
    obtain ⟨p, k, hk, hpk⟩ := GlobalTheory.T.graph_element_iwasawa_split_place F E σ h n J hJ L v hSD ⟨τ⟩ g
    have hlat := unitaryLocalPoint_latticeGraphNorm_identity F E σ h n J hJ L v g p k hk hpk
    have hgr : graphHgt σ J L v g = absEv F E v (Matrix.GeneralLinearGroup.det
        (leviOf finSumFinEquiv (matHom (Fv F v) σ (dblGram finSumFinEquiv J)) p)) := by
      rw [graphHgt, hpk, hgtFin_mul p hk]
      rfl
    refine ⟨exists_isElemDiv _, ?_, ?_⟩
    · intro d hd
      rw [hgr]
      exact GlobalTheory.T.doublingNorm_det_splitPlace_lattice_intersection F E σ h n J hJ L v hSD τ β hβ g _ hlat d hd
    · obtain ⟨d, hd⟩ := exists_isElemDiv (splitEquivIn h hJ τ β g)
      rw [hgr, GlobalTheory.T.doublingNorm_det_splitPlace_lattice_intersection F E σ h n J hJ L v hSD τ β hβ g _ hlat d hd]
      exact Finset.prod_le_one (fun _ _ => by positivity) (fun i _ => min_self_inv_le_one _)
  · intro P hP g
    obtain ⟨p, k, hk, hpk⟩ := GlobalTheory.T.graph_element_iwasawa_inert_place F E σ h n J hJ L v hSD P hP g
    have hlat := unitaryLocalPoint_latticeGraphNorm_identity F E σ h n J hJ L v g p k hk hpk
    have hgr : graphHgt σ J L v g = absEv F E v (Matrix.GeneralLinearGroup.det
        (leviOf finSumFinEquiv (matHom (Fv F v) σ (dblGram finSumFinEquiv J)) p)) := by
      rw [graphHgt, hpk, hgtFin_mul p hk]
      rfl
    obtain ⟨l, hl1, hl2⟩ := GlobalTheory.T.doublingNorm_det_inertPlace_lattice_length F E σ h n J hJ L v P hP g _ hlat
    refine ⟨⟨l, hl1, hgr.trans hl2⟩, ?_⟩
    rw [hgr, hl2]
    apply natCast_zpow_neg_le_one
    exact Nat.one_le_iff_ne_zero.mpr (fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))

end GlobalTheory.GraphNorm

end
