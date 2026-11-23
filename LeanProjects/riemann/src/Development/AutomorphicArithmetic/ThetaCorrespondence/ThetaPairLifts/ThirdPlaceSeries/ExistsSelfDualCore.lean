import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureRelation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CoreLat
variable {D : D7}
end GlobalTheory.CoreLat
namespace GlobalTheory.CoreLat
variable {D : D7}
end GlobalTheory.CoreLat
namespace GlobalTheory.CoreLat
end GlobalTheory.CoreLat
namespace GlobalTheory.CoreLat
variable {D : D7}
end GlobalTheory.CoreLat
namespace GlobalTheory.CoreLat
theorem exists_selfDual_core_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀))) (o : TDat (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = PP.under (𝓞 D.host.F)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (_root_.GlobalTheory.Fam.pk_z W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ j ρ h, ∃ L : GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀, IsSelfDualC (y.bes j ρ h).V₀ L := by
  intro D Ld hT Gi Gl Kc Yd cX ex W u hPk a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hζ hvτ hNT hoζ hLT hgP htP hdisj hPre hLZ
    hbas FY sc hFY
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have hsξ : star D.host.xi0 ≠ 0 := star_ne_zero.2 hξ
  have hline : ∀ σ j (h : j + 2 * σ + 2 = D.R.m), ∃ Λ : Submodule (𝓞 D.host.E) (Fin (y.bes j σ h).L.rank → D.host.E),
      SelfDualFor (y.bes j σ h).L.gram Λ := by
    intro σ
    induction σ with
    | zero =>
      intro j h
      obtain ⟨hg, hv⟩ := hTau j h
      have hl := (y.bes j 0 h).line
      have hlam0 : (-D.host.xi0 ^ (D.R.m / 2) : D.host.E) ≠ 0 := neg_ne_zero.2 (pow_ne_zero _ hξ)
      have hc : (-(D.host.xi0 * star D.host.xi0) : D.host.E) ≠ 0 := neg_ne_zero.2 (mul_ne_zero hξ hsξ)
      have hval := quad_mul (y.τ j h) (y.bes j 0 h).L.gram a.ζ₀
      rw [hg, hv, quad_smul, quad_smul_mat, hζ] at hval
      have hT0 : (D.mem u).A.T ≠ 0 := by
        intro h0
        rw [h0, Nat.cast_zero, mul_zero] at hval
        exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 hlam0) hlam0) hl.2 hval.symm
      have hr1 : a.Lz.rank ≤ 1 := by
        have hu : IsUnit ((-(D.host.xi0 * star D.host.xi0)) • a.Lz.gram) := by
          rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
          exact ((isUnit_iff_ne_zero.2 hc).pow _).mul (gram_isUnit_det _)
        have hrk := Matrix.rank_of_isUnit _ hu
        rw [← hg, Fintype.card_fin] at hrk
        calc a.Lz.rank = ((y.τ j h)ᴴ * ((y.bes j 0 h).L.gram * y.τ j h)).rank := hrk.symm
          _ ≤ ((y.bes j 0 h).L.gram * y.τ j h).rank := Matrix.rank_mul_le_right _ _
          _ ≤ (y.τ j h).rank := Matrix.rank_mul_le_right _ _
          _ ≤ Fintype.card (Fin (y.bes j 0 h).L.rank) := Matrix.rank_le_card_height _
          _ = 1 := by rw [Fintype.card_fin, hl.1]
      have hr0 : a.Lz.rank ≠ 0 := by
        intro h0
        haveI : IsEmpty (Fin a.Lz.rank) := ⟨fun i => by have := i.2; omega⟩
        have : star a.ζ₀ ⬝ᵥ (a.Lz.gram *ᵥ a.ζ₀) = 0 := by simp [dotProduct]
        rw [hζ] at this
        exact hT0 (by exact_mod_cast this)
      obtain ⟨x, hx⟩ := exists_prime_not_mem D.host.F hT0
      have hxt : x ∉ v.tP := by rw [htP]; exact hx
      obtain ⟨LZ, hLZsd, -⟩ := hLZ D.R.m rfl x hxt
      refine ⟨_, selfDualFor_map (D.host.xi0⁻¹ • y.τ j h) (s := -1) (Or.inr rfl) ?_ (gram_isUnit_det _) ?_
        ((isSelfDualC_iff _ _).1 hLZsd)⟩
      · simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
        rw [hg, smul_smul]
        convert (one_smul D.host.E a.Lz.gram).symm using 2
        rw [star_inv₀]; field_simp
      · rw [Fintype.card_fin, Fintype.card_fin, hl.1]; omega
    | succ σ ih =>
      intro j h
      obtain ⟨Λ', hΛ'⟩ := ih (j + 1 + 1) (idx_step h)
      have lk := y.lnk j σ h
      have hl := (y.bes j (σ + 1) h).line
      have hl' := (y.bes (j + 1 + 1) σ (idx_step h)).line
      refine ⟨_, selfDualFor_map (D.host.xi0⁻¹ • lk.τ) (s := 1) (Or.inl rfl) ?_ (gram_isUnit_det _) ?_ hΛ'⟩
      · refine line_mat_eq (by rw [Fintype.card_fin, hl'.1]) hl'.2 ?_
        rw [one_smul, Matrix.mul_assoc, quad_mul, Matrix.smul_mulVec, lk.map, smul_neg, ← neg_smul, quad_smul]
        change _ = star (-D.host.xi0⁻¹) * -D.host.xi0⁻¹ *
          (star (y.bes j (σ + 1) h).ζ ⬝ᵥ ((y.bes j (σ + 1) h).L.gram *ᵥ (y.bes j (σ + 1) h).ζ))
        rw [show star (y.bes j (σ + 1) h).ζ ⬝ᵥ ((y.bes j (σ + 1) h).L.gram *ᵥ (y.bes j (σ + 1) h).ζ) = _ from lk.norm,
          star_neg, star_inv₀]
        field_simp
      · rw [Fintype.card_fin, Fintype.card_fin, hl.1, hl'.1]
  intro j ρ h
  obtain ⟨ΛL, hΛL⟩ := hline ρ j h
  have hA : SelfDualFor (D.sp.X j).gram (a.x j).L := (isSelfDualC_iff _ _).1 (hIs.x j (by omega)).sd
  have hs := selfDualFor_sum hA hΛL
  have hmap := selfDualFor_map (G' := (y.bes j ρ h).V₀.gram) (Matrix.fromCols (y.bes j ρ h).o.iA (y.bes j ρ h).o.iB)
    (s := 1) (Or.inl rfl) ?_ ?_ ?_ hs
  · exact ⟨_, (isSelfDualC_iff _ _).2 hmap⟩
  · rw [one_smul, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
      (y.bes j ρ h).o.isoA, (y.bes j ρ h).o.isoB, (y.bes j ρ h).o.orth, (y.bes j ρ h).o.orth']
  · rw [Matrix.det_fromBlocks_zero₂₁]
    exact (gram_isUnit_det _).mul (gram_isUnit_det _)
  · rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, (y.bes j ρ h).o.rank_add]
end GlobalTheory.CoreLat
end
end
