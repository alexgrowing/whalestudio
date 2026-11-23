import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionCoreProjMulCoreEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.SeeSaw.SplitLat

variable {D : D7}

theorem pair_eq_dot {n : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_i₀ {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x : Fin S.rank → D.host.E) (y : Fin S₀.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * S.gram i j * (d.i₀ *ᵥ y) j = ∑ i, ∑ j, star ((d.q0 *ᵥ x) i) * S₀.gram i j * y j := by
  have hG : S.gram * d.i₀ = d.q0ᴴ * S₀.gram := by
    rw [gram_eq d]
    simp only [Matrix.add_mul, Matrix.mul_assoc, qX_i₀, qY_i₀, wittDecomposition_coreProj_mul_core_eq_one, Matrix.mul_zero, Matrix.mul_one, add_zero,
      zero_add]
  rw [pair_eq_dot, pair_eq_dot, Matrix.mulVec_mulVec, hG, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.star_mulVec]

theorem mulVec_eq_sum_cols {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (w : Fin n → D.host.E) :
    M *ᵥ w = ∑ i, fun r => w i * M r i := by
  funext r
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem colProj_mulVec' {S : HSp D} {ρ m : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E)
    (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ) (x : Fin m → D.host.E) :
    colProj q f i *ᵥ x = fun r => (q *ᵥ x) i * f r i := by
  funext k
  simp only [colProj, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem selfDual_core_monoAt (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (hL : IsSelfDualC S L)
    (hcol : ∀ y ∈ L, ∀ i, (fun r => (d.qX *ᵥ y) i * d.e r i) ∈ L ∧ (fun r => (d.qY *ᵥ y) i * d.e' r i) ∈ L) :
    IsSelfDualC S₀ (coreLat d L) ∧ ∀ v : GlobalTheory.FinPl.Pl D, MonoAt d L (coreLat d L) v := by

  have hcore : ∀ y ∈ L, d.q0 *ᵥ y ∈ coreLat d L := by
    intro y hy
    rw [mem_coreLat]
    have hdec : y = d.e *ᵥ (d.qX *ᵥ y) + d.i₀ *ᵥ (d.q0 *ᵥ y) + d.e' *ᵥ (d.qY *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
        d.sum_eq_one_rat, Matrix.one_mulVec]
    have hX : d.e *ᵥ (d.qX *ᵥ y) ∈ L := by
      rw [mulVec_eq_sum_cols]; exact sum_mem fun i _ => (hcol y hy i).1
    have hY : d.e' *ᵥ (d.qY *ᵥ y) ∈ L := by
      rw [mulVec_eq_sum_cols]; exact sum_mem fun i _ => (hcol y hy i).2
    have key : ∀ a b c z : Fin S.rank → D.host.E, z = a + b + c → b = z - a - c := by
      intro a b c z hz; rw [hz]; abel
    have h : d.i₀ *ᵥ (d.q0 *ᵥ y) = y - d.e *ᵥ (d.qX *ᵥ y) - d.e' *ᵥ (d.qY *ᵥ y) := key _ _ _ _ hdec
    rw [h]
    exact sub_mem (sub_mem hy hX) hY
  have hinj : Function.Injective ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) := by
    intro x x' hxx
    have h := congrArg (fun z => d.q0 *ᵥ z) hxx
    simpa only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_core_eq_one,
      Matrix.one_mulVec] using h
  refine ⟨⟨⟨?_, ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩, fun v => ?_⟩
  ·
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    have hLfg : L.FG := hL.1.fg
    haveI : IsNoetherian (𝓞 D.host.E) L := isNoetherian_of_fg_of_noetherian L hLfg
    have hle : (coreLat d L).map ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) ≤ L :=
      Submodule.map_comap_le _ _
    have h1 : (((coreLat d L).map ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E))).comap L.subtype).FG :=
      IsNoetherian.noetherian _
    have h2 := h1.map L.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2
  ·
    rw [eq_top_iff]
    intro x _
    have hx : d.i₀ *ᵥ x ∈ Submodule.span D.host.E (L : Set (Fin S.rank → D.host.E)) := by
      rw [hL.1.span_eq_top]; exact Submodule.mem_top
    have hm := Submodule.mem_map_of_mem (f := Matrix.mulVecLin d.q0) hx
    rw [Submodule.map_span, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_core_eq_one, Matrix.one_mulVec] at hm
    refine Submodule.span_mono ?_ hm
    rintro _ ⟨z, hz, rfl⟩
    exact hcore z hz
  ·
    obtain ⟨b, hb⟩ := (hL.2 (d.i₀ *ᵥ y)).1 hy (d.i₀ *ᵥ x) hx
    refine ⟨b, ?_⟩
    rw [hb, pair_i₀, Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_core_eq_one, Matrix.one_mulVec]
  ·
    rw [mem_coreLat]
    refine (hL.2 (d.i₀ *ᵥ y)).2 fun x hx => ?_
    obtain ⟨b, hb⟩ := h (d.q0 *ᵥ x) (hcore x hx)
    exact ⟨b, hb.trans (pair_i₀ d x y).symm⟩
  ·
    have hX : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qX d.e i *ᵥ x ∈ L := fun i x hx => by
      rw [colProj_mulVec']; exact (hcol x hx i).1
    have hY : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qY d.e' i *ᵥ x ∈ L := fun i x hx => by
      rw [colProj_mulVec']; exact (hcol x hx i).2
    intro y
    constructor
    · intro hy
      refine ⟨fun i => ?_, fun i => ?_, ?_⟩
      · change colMul (rat d.e) i ((rat d.qX *ᵥ y) i) ∈ _
        rw [colMul_rat]
        exact rat_mulVec_mem_latV _ (hX i) _ hy
      · change colMul (rat d.e') i ((rat d.qY *ᵥ y) i) ∈ _
        rw [colMul_rat]
        exact rat_mulVec_mem_latV _ (hY i) _ hy
      · exact rat_mulVec_mem_latV d.q0 hcore _ hy
    · rintro ⟨h1, h3, h2⟩
      have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
          d.sum_eq_one, Matrix.one_mulVec]
      rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
      refine add_mem (add_mem (sum_mem fun i _ => h1 i) ?_) (sum_mem fun i _ => h3 i)
      exact rat_mulVec_mem_latV d.i₀ (fun x hx => hx) _ h2

end GlobalTheory.Core.Mi.LatMatch

end
