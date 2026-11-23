import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BlockTriangularOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PerFrLact
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagDomainModelsOfFamilyUniformisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsUnf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankEqOfInjectiveOfSpan
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PrincipalLevelGroupFiniteIndexUnitaryStabiliserStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PrincipalGroupActsFreelyOnFlagsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TransvectionMemPrincipalCongruenceGroupStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtensionStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ImNegOfFramePeriodVector
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnfFamily

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.EqCovol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def reGrp (X : Data E r) (Γ : Subgroup (GL (Fin r) E)) (m : ℕ)
    (hs : ∀ γ ∈ Γ, IsUStab X.Gm X.Λ γ)
    (hi : ∃ S : Finset (GL (Fin r) E), ∀ γ, IsUStab X.Gm X.Λ γ → ∃ s ∈ S, s⁻¹ * γ ∈ Γ)
    (hf : ∀ γ ∈ Γ, ∀ x ∈ GG X.Ψ X.Gm X.p0, ∀ b ∈ Bor X.Ψ r, lact γ x = rmul x b → γ = 1)
    (hm : 0 < m)
    (ht : ∀ ξ ∈ X.Λ, herm X.Gm ξ ξ = 0 → ∀ s : E, cc s = s → IsIntegral ℤ s →
      ∃ γ ∈ Γ, (γ : Matrix (Fin r) (Fin r) E) = transvMat X.Gm ξ ((m : E) * s * X.κ0)) : Data E r :=
  { X with
    Γ := Γ
    Γ_stab := hs
    Γ_index := hi
    Γ_free := hf
    χ := fun _ _ => 1
    χ_mul := fun _ _ _ _ _ => (mul_one 1).symm
    χ_add := fun _ _ _ _ => (mul_one 1).symm
    χ_fin := fun _ => ⟨1, one_pos, fun _ _ => one_pow 1⟩
    m := m
    m_pos := hm
    transv := ht }

theorem covol_reGrp (X : Data E r) (Γ : Subgroup (GL (Fin r) E)) (m : ℕ) (hs hi hf hm ht)
    (h : ∀ x ∈ X.dom, ∀ x' ∈ X.dom, (∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x' = rmul (lact γ x) b) ↔
      ∃ γ ∈ Γ, ∃ b ∈ Bor X.Ψ r, x' = rmul (lact γ x) b) :
    GlobalTheory.TrueCx.covol X = GlobalTheory.TrueCx.covol (reGrp X Γ m hs hi hf hm ht) := by
  have ho := GlobalTheory.TrueCx.isOrth_x0F X
  obtain ⟨FF, hF⟩ := GlobalTheory.MetricWeightTest.exists_fundSet_orth X ho
  have hF' : IsFundSet (reGrp X Γ m hs hi hf hm ht) (x0F X) FF := by
    refine ⟨hF.1, hF.2.1, fun z hz z' hz' γ hγ b hb e => ?_, ?_⟩
    · obtain ⟨γ', hγ', b', hb', e'⟩ := (h _ (hF.2.1 hz) _ (hF.2.1 hz')).2
        ⟨γ, hγ, b, hb, e.trans (KU.lact_rmul' X _ _ _)⟩
      exact hF.2.2.1 z hz z' hz' γ' hγ' b' hb' (e'.trans (KU.lact_rmul' X _ _ _).symm)
    · have h4 := hF.2.2.2
      refine h4.mono ?_
      rintro z ⟨z', hz', γ, hγ, b, hb, e⟩
      have hd : cpt X (x0F X) z ∈ X.dom := by
        rw [e]
        exact Formalism.L2.Pj.dom_lact X (Formalism.L2.Pj.dom_rmul X (hF.2.1 hz') hb) (X.Γ_stab γ hγ)
      obtain ⟨γ', hγ', b', hb', e'⟩ := (h _ (hF.2.1 hz') _ hd).1
        ⟨γ, hγ, b, hb, e.trans (KU.lact_rmul' X _ _ _)⟩
      exact ⟨z', hz', γ', hγ', b', hb', e'.trans (KU.lact_rmul' X _ _ _).symm⟩
  rw [(GlobalTheory.TrueCx.covol_eq X ho hF).2, (GlobalTheory.TrueCx.covol_eq (reGrp X Γ m hs hi hf hm ht) ho hF').2]
  rfl

section Fam

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}

theorem fib_single {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (hσ : GoodEmb c σ) (hr : r = Dw.p + Dw.q) (k : Fin F.n) (Y : Data E r) (φ : (F.Di k).La ≃ₗ[𝓞 E] Y.Λ)
    (hty : Y.p0 = Dw.q ∧ ∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0)
    (hchi : ∀ la γ, Y.χ la γ = 1)
    (hef : ∀ a b, (((F.Di k).EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ E (-Y.ξ0 * herm Y.Gm (φ a : Fin r → E) (φ b)))
    (hgam : ∀ γ : GL (Fin r) E, γ ∈ Y.Γ ↔ IsUStab Y.Gm Y.Λ γ ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ b : (F.Di k).La,
        (γ : Matrix (Fin r) (Fin r) E).mulVec (φ a : Fin r → E) =
          (φ a : Fin r → E) + (l.M : ℕ) • (φ b : Fin r → E)) ∧
      ∀ a : (F.Di k).La, ∃ b : (F.Di k).La,
        (γ : Matrix (Fin r) (Fin r) E).mulVec (φ a : Fin r → E) = (φ a : Fin r → E) + (l.A : ℕ) • (φ b : Fin r → E))
    (hneg : ∀ τ ∈ Y.Ψ, (τ Y.ξ0).im < 0) :
    ∀ (x x' : Y.dom) (Pm Pm' : (F.Di k).La →+ (Fin g → ℂ))
      (v v' : ∀ τ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)),
      (∀ a j, Pm a j = perFr Y x.1 (φ a : Fin r → E) (relab c σ (e j).1) (e j).2) →
      (∀ a j, Pm' a j = perFr Y x'.1 (φ a : Fin r → E) (relab c σ (e j).1) (e j).2) →
      F.u k Pm = F.u k Pm' →
      (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (v τ i)) →
      (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k Pm' z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
        (v' τ i)) →
      (∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → CAt σ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
        IsCombAt (F.u k Pm) (v τ) cf (v' τ i)) →
      ∃ γ ∈ Y.Γ, ∃ b ∈ Bor Y.Ψ r, x'.1 = rmul (lact γ x.1) b := by
  classical
  obtain ⟨ξ₀, hcc, hne, him⟩ := GlobalTheory.IsUnfEx.exists_xi H
  have hcc' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hcc ⊢
    rw [map_neg, hcc]
  obtain ⟨Gm, φ0, hφ0⟩ := GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ₀) hcc' (neg_ne_zero.2 hne) r hr
  obtain ⟨M0, hM0, hN0, -⟩ := GlobalTheory.ModelsExist.exists_modelsOf GlobalTheory.T.hasse_norm_theorem_quadratic_extension E H Dw l Xo _ _ _ F r ξ₀ Gm φ0 hcc him hφ0
  let Good : ∀ i : Fin F.n, (Σ X : Data E r, (F.Di i).La ≃ₗ[𝓞 E] X.Λ) → Prop := fun i p =>
    (p.1.p0 = Dw.q ∧ ∀ τ : E →+* ℂ, τ ∈ p.1.Ψ ↔ τ (H.rt : E) = H.rt0) ∧ (∀ la γ, p.1.χ la γ = 1) ∧
    (∀ a b, (((F.Di i).EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ E (-p.1.ξ0 * herm p.1.Gm (p.2 a : Fin r → E) (p.2 b))) ∧
    (∀ γ : GL (Fin r) E, γ ∈ p.1.Γ ↔ IsUStab p.1.Gm p.1.Λ γ ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di i).La), ∃ b : (F.Di i).La,
        (γ : Matrix (Fin r) (Fin r) E).mulVec (p.2 a : Fin r → E) =
          (p.2 a : Fin r → E) + (l.M : ℕ) • (p.2 b : Fin r → E)) ∧
      ∀ a : (F.Di i).La, ∃ b : (F.Di i).La,
        (γ : Matrix (Fin r) (Fin r) E).mulVec (p.2 a : Fin r → E) =
          (p.2 a : Fin r → E) + (l.A : ℕ) • (p.2 b : Fin r → E)) ∧
    ∀ τ ∈ p.1.Ψ, (τ p.1.ξ0).im < 0
  obtain ⟨f, hf, hk⟩ : ∃ f : ∀ i : Fin F.n, (Σ X : Data E r, (F.Di i).La ≃ₗ[𝓞 E] X.Λ),
      (∀ i, Good i (f i)) ∧ f k = ⟨Y, φ⟩ := by
    refine ⟨Function.update (fun i => ⟨M0.X i, M0.φ i⟩) k ⟨Y, φ⟩, ?_, Function.update_self ..⟩
    rw [Function.forall_update_iff _ Good]
    exact ⟨⟨hty, hchi, hef, hgam, hneg⟩, fun i _ => ⟨hM0.type i, hM0.chi i, hM0.ef i, hM0.gam i, hN0 i⟩⟩
  let M : ModelsOf F r := ⟨fun i => (f i).1, fun i => (f i).2⟩
  have hM : ModelBase M :=
    { rank := hr
      type := fun i => (hf i).1
      chi := fun i => (hf i).2.1
      ef := fun i => (hf i).2.2.1
      gam := fun i => (hf i).2.2.2.1
      domStab := fun i x hx => ⟨fun b hb => Formalism.L2.Pj.dom_rmul _ hx hb,
        fun γ hγ => Formalism.L2.Pj.dom_lact _ hx ((M.X i).Γ_stab γ hγ)⟩ }
  have hT := GlobalTheory.FibreFlag.fibTri E H Dw l Xo c σ g e F r M hσ hM fun i => (hf i).2.2.2.2
  have key : ∀ (x x' : (f k).1.dom) (Pm Pm' : (F.Di k).La →+ (Fin g → ℂ))
      (v v' : ∀ τ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)),
      (∀ a j, Pm a j = perFr (f k).1 x.1 ((f k).2 a : Fin r → E) (relab c σ (e j).1) (e j).2) →
      (∀ a j, Pm' a j = perFr (f k).1 x'.1 ((f k).2 a : Fin r → E) (relab c σ (e j).1) (e j).2) →
      F.u k Pm = F.u k Pm' →
      (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (v τ i)) →
      (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k Pm' z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
        (v' τ i)) →
      (∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → CAt σ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
        IsCombAt (F.u k Pm) (v τ) cf (v' τ i)) →
      ∃ γ ∈ (f k).1.Γ, ∃ b ∈ Bor (f k).1.Ψ r, x'.1 = rmul (lact γ x.1) b := by
    intro x x' Pm Pm' v v' h1 h2 h3 h4 h5 h6
    obtain ⟨γ, hγ, b, hb, h⟩ := hT k k x x' Pm Pm' v v' h1 h2 h3 h4 h5 h6
    exact ⟨γ, hγ, b, hb, eq_of_heq (Sigma.mk.inj_iff.1 h).2⟩
  generalize f k = p at key hk
  subst hk
  exact key

end Fam

set_option maxHeartbeats 800000 in

theorem exists_levGrp_covol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k : U.Comp, ∃ Y : ReciprocityTheory.ChartRestriction.G.FD.Data E r, Y.Ψ = (U.X k).Ψ ∧ Y.p0 = (U.X k).p0 ∧ Y.Gm = (U.X k).Gm ∧ Y.Λ = (U.X k).Λ ∧ Y.ξ0 = (U.X k).ξ0 ∧ GlobalTheory.EqCovol.IsLevGrp l Y ∧ GlobalTheory.EqCovol.IsSelfDualTr Y ∧ GlobalTheory.TrueCx.covol (U.X k) = GlobalTheory.TrueCx.covol Y := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU _ hp _ k
  classical
  obtain ⟨hr, hty, -, h4, -, g, e, F, ik, φ, hef, hun⟩ := hU
  obtain ⟨φ0, hφe⟩ : ∃ φ0 : (F.Di (ik k)).La →ₗ[𝓞 E] (Fin r → E), ∀ a, φ0 a = (φ k a : Fin r → E) :=
    ⟨(U.X k).Λ.subtype ∘ₗ (φ k).toLinearMap, fun _ => rfl⟩
  have hΛ : LinearMap.range φ0 = (U.X k).Λ := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      rw [hφe]
      exact (φ k a).2
    · intro hy
      exact ⟨(φ k).symm ⟨y, hy⟩, by rw [hφe, LinearEquiv.apply_symm_apply]⟩
  have hlat : Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧
      (∀ a b, cc ((U.X k).Gm a b) = (U.X k).Gm b a) ∧ (U.X k).Gm.det ≠ 0 ∧
      ∀ x y, (((F.Di (ik k)).EF x y : ℤ) : ℚ) =
        Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ0 x) (φ0 y)) := by
    refine ⟨fun a b hab => ?_, ?_, (U.X k).Gm_herm, (U.X k).Gm_det, fun x y => ?_⟩
    · rw [hφe, hφe] at hab
      exact (φ k).injective (Subtype.ext hab)
    · rw [← LinearMap.coe_range, hΛ]
      exact (U.X k).Λ_span
    · rw [hφe, hφe]
      exact hef k x y
  have hξ := (U.X k).ξ0_im
  have hξ' : cc (-(U.X k).ξ0) = -(-(U.X k).ξ0) := by
    unfold cc at hξ ⊢
    rw [map_neg, hξ]
  have hneg : ∀ τ ∈ (U.X k).Ψ, (τ (U.X k).ξ0).im < 0 := by
    obtain ⟨x, hx⟩ := GlobalTheory.UnifFamily.dom_nonempty (U.X k)
    obtain ⟨Pm, h1, h2, -⟩ := hun k ⟨x, hx⟩
    exact GlobalTheory.FrameSign.im_neg_of_isPeriod E H Dw l c σ g e _ r (U.X k) (φ k) hσ hr (hty k).1 (hty k).2 (hef k)
      x hx Pm h1 h2 (by omega)
  obtain ⟨m, hm, ht⟩ := GlobalTheory.T.transvection_mem_principalCongruenceGroup E H l _ r _ _ φ0 hξ hlat
  have hi := GlobalTheory.T.principalLevelGroup_finiteIndex_unitaryStabiliser E H l _ r _ _ φ0 hξ hlat
  have hf := GlobalTheory.T.principalGroup_acts_freely_on_flags E H l _ r _ _ φ0 hξ hlat (U.X k).Ψ (U.X k).p0 (hty k).2
  have hmem : ∀ γ : GL (Fin r) E, γ ∈ princ l (U.X k).Gm (F.Di (ik k)) φ0 ↔ IsUStab (U.X k).Gm (U.X k).Λ γ ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di (ik k)).La), ∃ b : (F.Di (ik k)).La,
        (γ : Matrix (Fin r) (Fin r) E).mulVec (φ k a : Fin r → E) =
          (φ k a : Fin r → E) + (l.M : ℕ) • (φ k b : Fin r → E)) ∧
      ∀ a : (F.Di (ik k)).La, ∃ b : (F.Di (ik k)).La,
        (γ : Matrix (Fin r) (Fin r) E).mulVec (φ k a : Fin r → E) =
          (φ k a : Fin r → E) + (l.A : ℕ) • (φ k b : Fin r → E) := by
    intro γ
    simp only [← hφe]
    rw [← hΛ]
    exact Iff.rfl
  have hs : ∀ γ ∈ princ l (U.X k).Gm (F.Di (ik k)) φ0, IsUStab (U.X k).Gm (U.X k).Λ γ :=
    fun γ hγ => ((hmem γ).1 hγ).1
  rw [hΛ] at hi ht
  refine ⟨reGrp (U.X k) _ m hs hi hf hm (ht _ (U.X k).κ0_xi), rfl, rfl, rfl, rfl, rfl, fun γ => ?_, fun x => ?_,
    covol_reGrp _ _ _ _ _ _ _ _ fun x hx x' hx' => ⟨?_, ?_⟩⟩
  · refine (hmem γ).trans (and_congr Iff.rfl (and_congr ?_ ?_))
    · have hI : (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (U.X k).Λ =
          (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di (ik k)).La)).map φ0 := by
        rw [Submodule.map_smul'', Submodule.map_top, hΛ]
      show _ ↔ ∀ x ∈ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (U.X k).Λ, ∃ y ∈ (U.X k).Λ, _
      rw [hI]
      simp only [← hφe]
      rw [← hΛ]
      constructor
      · rintro h _ ⟨a, ha, rfl⟩
        obtain ⟨b, hb⟩ := h a ha
        exact ⟨_, ⟨b, rfl⟩, sub_eq_iff_eq_add'.2 hb⟩
      · intro h a ha
        obtain ⟨_, ⟨b, rfl⟩, hb⟩ := h _ ⟨a, ha, rfl⟩
        exact ⟨b, sub_eq_iff_eq_add'.1 hb⟩
    · show _ ↔ ∀ x ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ, _
      simp only [← hφe]
      rw [← hΛ]
      constructor
      · rintro h _ ⟨a, rfl⟩
        obtain ⟨b, hb⟩ := h a
        exact ⟨_, ⟨b, rfl⟩, sub_eq_iff_eq_add'.2 hb⟩
      · intro h a
        obtain ⟨_, ⟨b, rfl⟩, hb⟩ := h _ ⟨a, rfl⟩
        exact ⟨b, sub_eq_iff_eq_add'.1 hb⟩
  · have hd := (GlobalTheory.HermModel.rank_integral_selfDual E H _ r _ _ φ0 hξ' hlat).2.2.2 x
    show x ∈ (U.X k).Λ ↔ ∀ y ∈ (U.X k).Λ, ∃ n : ℤ,
      Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm x y) = n
    rw [← hΛ, ← hd]
    constructor
    · rintro h _ ⟨y, rfl⟩
      exact h y
    · exact fun h y => h _ ⟨y, rfl⟩
  · rintro ⟨γ, hγ, b, hb, hxx⟩
    obtain ⟨t, hx0, hu, -⟩ := (h4 k k ⟨x, hx⟩ ⟨x', hx'⟩).2 ⟨γ, hγ, b, hb, by rw [← hxx]⟩
    obtain ⟨Pm, hPm, -, hxP, hd, -⟩ := hun k ⟨x, hx⟩
    obtain ⟨Pm', hPm', -, hxP', hd', -⟩ := hun k ⟨x', hx'⟩
    refine fib_single e F hσ hr (ik k) (reGrp (U.X k) _ m hs hi hf hm (ht _ (U.X k).κ0_xi)) (φ k) (hty k)
      (fun _ _ => rfl) (hef k) hmem hneg ⟨x, hx⟩ ⟨x', hx'⟩ Pm Pm' _ _ hPm hPm'
      (hxP.symm.trans (hx0.symm.trans hxP')) hd hd' fun τ i => ?_
    obtain ⟨cf, hcf, htri, hcomb⟩ := hu τ i
    refine ⟨cf, by rw [hcf]; exact Units.isUnit _, htri, ?_⟩
    rw [hxP] at hcomb
    exact hcomb
  · rintro ⟨γ, hγ, b, hb, hxx⟩
    obtain ⟨⟨hUn, hS⟩, hM, hA⟩ := (hmem γ).1 hγ
    have hxg : lact γ x ∈ (U.X k).dom := Formalism.L2.Pj.dom_lact _ hx ⟨hUn, hS⟩
    obtain ⟨t2, ht2⟩ := (h4 k k ⟨_, hxg⟩ ⟨x', hx'⟩).2 ⟨1, one_mem _, b, hb, by rw [KU.lact_one, ← hxx]⟩
    obtain ⟨Pm, hPm, p, hxP, hd, -⟩ := hun k ⟨x, hx⟩
    obtain ⟨Pm', hPm', p', hxP', hd', -⟩ := hun k ⟨_, hxg⟩
    obtain ⟨f, hf'⟩ := PerGam.exists_equiv _ γ hS
    let gam : (F.Di (ik k)).La ≃ₗ[𝓞 E] (F.Di (ik k)).La := (φ k).trans (f.trans (φ k).symm)
    have hg : ∀ a, (φ k (gam a) : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (φ k a : Fin r → E) := by
      intro a
      rw [← hf']
      simp [gam]
    have key : ∀ (n : ℕ) (a b : (F.Di (ik k)).La),
        (γ : Matrix (Fin r) (Fin r) E) *ᵥ (φ k a : Fin r → E) =
          (φ k a : Fin r → E) + n • (φ k b : Fin r → E) → gam a = a + n • b := by
      intro n a b h
      apply (φ k).injective
      apply Subtype.ext
      rw [hg, h, map_add, map_nsmul]
      rfl
    obtain ⟨-, hpt, hex⟩ := FamRigid.ex_eq_of_level_group latMinkowski E H Dw l Xo _ g _ F (ik k) Pm Pm' gam 1 p p'
      (fun a b => by
        have h1 := hef k (gam a) (gam b)
        rw [hg, hg, hUn, ← hef k a b] at h1
        exact_mod_cast h1)
      (fun a ha => (hM a ha).imp fun b hb => key _ a b hb) (fun a => (hA a).imp fun b hb => key _ a b hb)
      (fun a => by
        funext j
        rw [Matrix.one_mulVec, hPm', hPm, hg, PerGam.perFr_lact _ γ hUn])
    simp only [Matrix.one_mulVec] at hex
    have hu : ∀ τ i, (U.un k ⟨_, hxg⟩).u τ i = (U.un k ⟨x, hx⟩).u τ i := fun τ i => by
      have h1 := hd' τ i
      simp only [hex] at h1
      exact ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ _ p).2.1 _).unique h1 (hd τ i)
    obtain ⟨t1, ht1⟩ := (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k ⟨x, hx⟩) (U.un k ⟨_, hxg⟩)
      (U.un k ⟨x, hx⟩)).2.1 (hxP'.trans (hpt.symm.trans hxP.symm)) fun τ i => by
        refine ⟨(1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) i, by simp,
          fun j hij => Matrix.one_apply_ne hij.ne, ?_⟩
        rw [hu]
        exact (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c (CAt σ) (U.un k ⟨x, hx⟩) (U.un k ⟨x, hx⟩) (U.un k ⟨x, hx⟩)).1.2.1 τ i
    obtain ⟨γ', hγ', b', hb', h'⟩ := (h4 k k ⟨x, hx⟩ ⟨x', hx'⟩).1
      ⟨t2 * t1, (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) _ _ _).2.2.1 t1 t2 ht1 ht2⟩
    exact ⟨γ', hγ', b', hb', eq_of_heq (Sigma.mk.inj_iff.1 h').2⟩

end GlobalTheory.EqCovol
