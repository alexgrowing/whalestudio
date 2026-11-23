import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.MassLinkSD

open Formalism.BasicNotions.TH Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gram_det_ne {D : D7} (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have hx : ∀ y, V.hT y (∑ j, v j • V.frame j) = 0 := by
    intro y
    rw [← V.frame.sum_repr y]
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrFun h0 i
    simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at this
    calc _ = (starRingEnd _) (V.frame.repr y i) * ∑ j, V.hT (V.frame i) (V.frame j) * v j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [this, mul_zero]
  have := V.nondeg.2 _ hx
  exact hv (funext (Fintype.linearIndependent_iff.1 V.frame.linearIndependent v this))

theorem herm_eq {D : D7} (V : HSp D) {r : ℕ} (h : V.rank = r) (x y : Fin r → D.host.E) :
    letI : IsCMField D.host.E := D.host.isCMField_hostE
    ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.transpose (V.gram.submatrix (Fin.cast h.symm) (Fin.cast h.symm))) x y =
      ∑ i, ∑ j, star (y (Fin.cast h i)) * V.gram i j * x (Fin.cast h j) := by
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  unfold ReciprocityTheory.ChartRestriction.G.FD.herm
  rw [Finset.sum_comm]
  symm
  refine Fintype.sum_equiv (finCongr h) _ _ fun i => ?_
  refine Fintype.sum_equiv (finCongr h) _ _ fun j => ?_
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  rw [show star (y (Fin.cast h i)) = ReciprocityTheory.ChartRestriction.G.FD.cc (y (Fin.cast h i)) from rfl]
  ring

end GlobalTheory.MassLinkSD

namespace GlobalTheory.MassLinkSD

open Formalism.BasicNotions.TH Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem selfDualLat_of {D : D7} (V : HSp D) {r : ℕ} (h : V.rank = r)
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : IsSelfDualC V Λ) :
    letI : IsCMField D.host.E := D.host.isCMField_hostE
    GlobalTheory.UCls.SelfDualLat (Matrix.transpose (V.gram.submatrix (Fin.cast h.symm) (Fin.cast h.symm)))
      (Λ.comap (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast h))) := by
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨hlat, hsd⟩ := hΛ
  let eO : (Fin r → D.host.E) ≃ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
    LinearEquiv.funCongrLeft (𝓞 D.host.E) D.host.E (finCongr h)
  let eE : (Fin r → D.host.E) ≃ₗ[D.host.E] (Fin V.rank → D.host.E) :=
    LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr h)
  have hc : Λ.comap (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast h)) = Λ.map (eO.symm : _ →ₗ[𝓞 D.host.E] _) := by
    rw [← Submodule.comap_equiv_eq_map_symm]; rfl
  have hset : ((Λ.comap (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast h)) : Submodule _ _) : Set (Fin r → D.host.E)) =
      (eE.symm : (Fin V.rank → D.host.E) → (Fin r → D.host.E)) '' (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [LinearEquiv.image_symm_eq_preimage]; rfl
  refine ⟨fun a b => ?_, ?_, ?_, ?_, fun x => ?_⟩
  · simp only [Matrix.transpose_apply, Matrix.submatrix_apply, HSpace.gram]
    exact V.herm.eq _ _
  · rw [Matrix.det_transpose]
    have := Matrix.det_submatrix_equiv_self (finCongr h.symm) V.gram
    rw [show (Fin.cast h.symm : Fin r → Fin V.rank) = finCongr h.symm from rfl, this]
    exact gram_det_ne V
  · rw [hc]; exact hlat.fg.map _
  · rw [hset, show (⇑eE.symm : (Fin V.rank → D.host.E) → (Fin r → D.host.E)) = ⇑(eE.symm : (Fin V.rank → D.host.E) →ₗ[D.host.E] (Fin r → D.host.E)) from rfl,
      Submodule.span_image, hlat.span_eq_top, Submodule.map_top, LinearEquiv.range]
  · rw [Submodule.mem_comap, hsd]
    constructor
    · intro H x' hx'
      have hy : LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast h.symm) x' ∈
          Λ.comap (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast h)) := by
        rw [Submodule.mem_comap]
        convert hx' using 1
        funext j
        simp only [LinearMap.funLeft_apply, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self]
      have hb := H _ hy
      rw [herm_eq V h] at hb
      have e : (∑ i, ∑ j, star ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast h.symm) x') (Fin.cast h i)) *
            V.gram i j * x (Fin.cast h j)) =
          ∑ i, ∑ j, star (x' i) * V.gram i j * (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast h) x) j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [LinearMap.funLeft_apply, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self]
      rw [e] at hb
      exact ⟨⟨_, hb⟩, rfl⟩
    · intro H y hy
      obtain ⟨b, hb⟩ := H _ hy
      have hb' : (b : D.host.E) = ∑ i, ∑ j, star (y (Fin.cast h i)) * V.gram i j * x (Fin.cast h j) := hb
      rw [herm_eq V h, ← hb']
      exact b.isIntegral_coe

end GlobalTheory.MassLinkSD

namespace GlobalTheory.MassLinkSD

theorem base_selfDualLat : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; GlobalTheory.UCls.SelfDualLat (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i) := by
  intro D Tu Cl t0 hC i
  exact selfDualLat_of (Wc D i) (rank_Wc i) (Cl.ΛW i)
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.βW i))

end GlobalTheory.MassLinkSD
