import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoversOfLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLeOfDetEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionMemCuspFormsOfActionLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelAtEachIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelLiftModuliLawsOfCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGalois
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivAtRecordOfEquivRow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullActLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreConstantIffCoveringGroupInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverCuspFormPullbackInjectiveDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypeFrameCoverLevelMapsReductionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelCharacterEqProdSuperdiagonalSum

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.TypeLattice

theorem mem_span_image_eigen {K L V W Γ G : Type} [Field K] [Field L] [CharZero L] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module L W] [Group G] {σ : K →+* L} (π : V →ₛₗ[σ] W) (ρ : G → V →ₗ[K] V) (hρ : ∀ g h v, ρ (g * h) v = ρ g (ρ h v))
    (τ : Γ → W →ₗ[L] W) (θ : Γ → G) (hc : ∀ γ v, τ γ (π v) = π (ρ (θ γ) v)) (P : Subgroup G) [Finite P] (lam : P →* Kˣ)
    (hs : ∀ u ∈ P, ∃ γ, θ γ = u) {w : W} (hw : w ∈ Submodule.span L (Set.range π))
    (he : ∀ γ (h : θ γ ∈ P), τ γ w = σ (lam ⟨θ γ, h⟩ : Kˣ) • w) :
    w ∈ Submodule.span L (π '' {v | ∀ u : P, ρ u v = ((lam u : Kˣ) : K) • v}) := by
  haveI := Fintype.ofFinite P
  choose s hs using fun u : P => hs u u.2
  let T : W →ₗ[L] W := ∑ u : P, σ ((lam u)⁻¹ : Kˣ) • τ (s u)
  have h1 : T w = (Fintype.card P : L) • w := by
    rw [LinearMap.sum_apply, Finset.sum_congr rfl (g := fun _ => w) fun u _ => ?_]
    · simp [Nat.cast_smul_eq_nsmul]
    · rw [LinearMap.smul_apply, he (s u) (hs u ▸ u.2), smul_smul, ← map_mul,
        show (⟨θ (s u), hs u ▸ u.2⟩ : P) = u from Subtype.ext (hs u), Units.inv_mul, map_one, one_smul]
  have h2 : Submodule.span L (Set.range π) ≤
      (Submodule.span L (π '' {v | ∀ u : P, ρ u v = ((lam u : Kˣ) : K) • v})).comap T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, rfl⟩
    refine Submodule.subset_span ⟨∑ u : P, (((lam u)⁻¹ : Kˣ) : K) • ρ u v, fun x => ?_, ?_⟩
    · rw [map_sum, Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun u => ?_
      rw [map_smul, ← hρ, smul_smul, Equiv.coe_mulLeft, map_mul, Subgroup.coe_mul]
      congr 1
      rw [mul_inv, Units.val_mul, Units.mul_inv_cancel_left]
    · rw [map_sum, LinearMap.sum_apply]
      exact Finset.sum_congr rfl fun u _ => by rw [map_smulₛₗ, LinearMap.smul_apply, hc, hs]
  have h3 := h2 hw
  rw [Submodule.mem_comap, h1] at h3
  exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)).1 h3

section Forms

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.LevPull (CongMod)
open GlobalTheory.LevDesc (transl)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldBC

set_option maxHeartbeats 1000000 in

theorem mem_span_pull_iff : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (G : Type) [Group G] (lev : G → (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La), ActLev (Xo := T.Q.Xo j) T.Q.c (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))) → (∀ g, ∀ f ∈ T.cuspA j a n, actLev (Xo := T.Q.Xo j) T.Q.c (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))) g f ∈ T.cuspA j a n) → ∀ (P : Subgroup G) [Finite P] (lam : P →* (T.Q.c.F)ˣ) (θ : LevelAut (T.Q.Dw j) Y.d.l₂ →* G), (∀ γ, CongMod T.Q.l.Mb (liftLa γ) (lev (θ γ))) → (∀ γ, CongMod T.Q.l.Mb (liftLa γ) LinearMap.id → θ γ = 1) → (∀ u ∈ P, ∃ γ, θ γ = u) → ∀ g ∈ Y.V (wtZ a n), g ∈ Submodule.span Y.d.c₂.F {g | ∃ f ∈ {f : T.R j | f ∈ T.cuspA j a n ∧ ∀ u : P, actLev (Xo := T.Q.Xo j) T.Q.c (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))) (u : G) f = ((lam u : (T.Q.c.F)ˣ) : T.Q.c.F) • f}, Y.Pull f g} ↔ ∀ γ (h : θ γ ∈ P), transl Y.d.Xo₂ Y.d.c₂ γ g = ((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle)) ((lam ⟨θ γ, h⟩ : (T.Q.c.F)ˣ) : T.Q.c.F) • g := by
  intro D T j Y e o hT hj hG a n hD G _ lev hact hkeep P _ lam θ hθ hker hs g hg
  obtain ⟨hL₂, hgal, hP⟩ := GlobalTheory.DeepLaws.laws_galois_pull D T j Y e o hT hj hG hG.unit hG.modelW
  have hL := (GlobalTheory.LevGeo.laws_of_coreJ D T j hT hj).1
  have hpq : (T.Q.Dw j).p ≠ (T.Q.Dw j).q ∧ 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hj
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW]
    omega
  obtain ⟨π, p1, -, -, -, p5, -⟩ := GlobalTheory.T.levelCover_cuspForm_pullback_injective_descent D j _ _ _ _ _ Y.c' Y.hle _ _ Y.d _ _ hL hL₂ hG.lev.1 hgal a n hD hD.2
  have hC : ∀ {f}, f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n) ↔ f ∈ T.cuspA j a n := fun {f} => by rw [cuspW_wtZ]
  have s₁ : ∀ {f}, f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n) → f ∈ sec (T.Q.Xo j) T.Q.c a n :=
    fun h => cusp_le_sec _ _ _ a n (hC.1 h)
  have s₂ : ∀ {f}, f ∈ Y.V (wtZ a n) → f ∈ sec Y.d.Xo₂ Y.d.c₂ a n := fun h => by
    rw [Deep.V, cuspW_wtZ] at h
    exact cusp_le_sec _ _ _ a n h
  have hact₂ : ActLev (Xo := Y.d.Xo₂) Y.d.c₂ (GlobalTheory.FormTies.levFull (T.Q.Dw j) Y.d.l₂) :=
    GlobalTheory.FullLevelAction.actLaws_levFull Y.d.Xo₂ Y.d.c₂ hpq.2 (hG.lev.2 ▸ Nat.coprime_one_left _)
  obtain ⟨hact', hbc⟩ := GlobalTheory.FieldBC.actLev_and_actBC D _ _ _ _ _ Y.c' Y.hle G _ hact
  have hO : GlobalTheory.CoverSec.AllOver Y.d := GlobalTheory.CoverSec.allOver_of_overBase Y.d hG.lev.1.1.2.2
    (GlobalTheory.ClsVal.Cmp.overBase_of_ne hpq.1 hL.levA Y.d)

  have geo : ∀ {f f' : Rul (T.Q.Xo j) Y.c'} {u u' : Rul Y.d.Xo₂ Y.d.c₂}, GlobalTheory.LevPull.Pull Y.d f u → GlobalTheory.LevPull.Pull Y.d f' u' →
      f = f' → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra Y.d.c₂.F k] (y : FrPt Y.d.Xo₂ Y.d.c₂ k),
        evR Y.d.Xo₂ Y.d.c₂ u y = evR Y.d.Xo₂ Y.d.c₂ u' y := by
    rintro f _ u u' h h' rfl k _ _ _ y₂
    letI := GlobalTheory.CoverSec.algBelow Y.d k
    obtain ⟨y, hy⟩ := GlobalTheory.CoverSec.exists_frOver_below Y.d (fun _ => rfl) y₂ (hO k (fun _ => rfl) y₂)
    rw [h k (fun _ => rfl) y₂ y hy, h' k (fun _ => rfl) y₂ y hy]
  let act := actLev (Xo := T.Q.Xo j) T.Q.c (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)))
  let ρ : G → cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n) →ₗ[T.Q.c.F] cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n) :=
    fun x => (act x).restrict fun f hf => hC.2 (hkeep x f (hC.1 hf))
  let π' := (Y.V (wtZ a n)).subtype.comp π
  have hc : ∀ γ v, (transl Y.d.Xo₂ Y.d.c₂ γ).toLinearMap (π' v) = π' (ρ (θ γ) v) := by
    intro γ v
    have hv := ((GlobalTheory.T.ruleBaseChange_section_values_semilinear _ _ _ _ _ _ _ Y.hle).1 a n _ (s₁ v.2)).1
    have h1 := GlobalTheory.LevPullEquiv.pull_actLev D j _ _ _ _ _ Y.d hpq.2 hG.lev.1 hG.lev.2
      (GlobalTheory.ClsVal.Cmp.overBase_of_ne hpq.1 hL.levA Y.d) G _ lev liftLa hact' hact₂ (θ γ) γ (hθ γ) a n _ hv _
      (s₂ (π v).2) (p1 v)
    refine GlobalTheory.CoverSec.eq_of_geometric (GlobalTheory.LevelEquivCompare.actLev_mem_sec hact₂ γ (s₂ (π v).2)).1 (s₂ (π _).2).1 (geo h1 (p1 (ρ (θ γ) v)) ?_)
    refine GlobalTheory.CoverSec.eq_of_geometric (GlobalTheory.LevelEquivCompare.actLev_mem_sec hact' _ hv).1
      ((GlobalTheory.T.ruleBaseChange_section_values_semilinear _ _ _ _ _ _ _ Y.hle).1 a n _ (s₁ (ρ (θ γ) v).2)).1.1 fun k _ _ _ y => ?_
    letI := resAlg Y.hle k
    exact (hbc a n (θ γ) 1 _ _ _ hv (fun _ => s₁ v.2) (GlobalTheory.LevelEquivCompare.isBC_rulBC Y.hle (s₁ v.2)) k (fun _ => rfl) y).trans
      (GlobalTheory.LevelEquivCompare.isBC_rulBC Y.hle (s₁ (ρ (θ γ) v).2) k (fun _ => rfl) y).symm
  constructor
  · intro h
    have key : ∃ u ∈ Submodule.span Y.d.c₂.F (π' '' {v | ∀ x : P, ρ x v = ((lam x : (T.Q.c.F)ˣ) : T.Q.c.F) • v}),
        ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra Y.d.c₂.F k] (y : FrPt Y.d.Xo₂ Y.d.c₂ k),
          evR Y.d.Xo₂ Y.d.c₂ g y = evR Y.d.Xo₂ Y.d.c₂ u y := by
      clear hg
      induction h using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨f, ⟨hf, hf'⟩, hu⟩ := hu
        exact ⟨_, Submodule.subset_span ⟨⟨f, hC.2 hf⟩, fun x => Subtype.ext (hf' x), rfl⟩,
          geo ((hP a n f (s₁ (hC.2 hf)) u).1 hu) (p1 ⟨f, hC.2 hf⟩) rfl⟩
      | zero => exact ⟨0, zero_mem _, fun _ _ _ _ _ => rfl⟩
      | add u u' _ _ h h' =>
        obtain ⟨w, hw, h⟩ := h
        obtain ⟨w', hw', h'⟩ := h'
        exact ⟨w + w', add_mem hw hw', fun k _ _ _ y => (evalAt_add _ _ u u' y).trans
          ((congrArg₂ (· + ·) (h k y) (h' k y)).trans (evalAt_add _ _ w w' y).symm)⟩
      | smul t u _ h =>
        obtain ⟨w, hw, h⟩ := h
        exact ⟨t • w, Submodule.smul_mem _ t hw, fun k _ _ _ y => (evalAt_smul _ _ t u y).trans
          ((congrArg _ (h k y)).trans (evalAt_smul _ _ t w y).symm)⟩
    obtain ⟨u, hu, h'⟩ := key
    have hu' : u ∈ Y.V (wtZ a n) := Submodule.span_le.2 (by rintro _ ⟨v, -, rfl⟩; exact (π v).2) hu
    obtain rfl : g = u := GlobalTheory.CoverSec.eq_of_geometric (s₂ hg).1 (s₂ hu').1 h'
    intro γ hγ
    refine (Submodule.span_le (p := LinearMap.eqLocus (transl Y.d.Xo₂ Y.d.c₂ γ).toLinearMap ((((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle)) ((lam ⟨θ γ, hγ⟩ : (T.Q.c.F)ˣ) : T.Q.c.F)) •
        (LinearMap.id : Rul Y.d.Xo₂ Y.d.c₂ →ₗ[Y.d.c₂.F] Rul Y.d.Xo₂ Y.d.c₂)))).2 ?_ hu
    rintro _ ⟨v, hv, rfl⟩
    exact (hc γ v).trans ((congrArg π' (hv ⟨θ γ, hγ⟩)).trans (map_smulₛₗ π' _ _))
  · intro h
    have h1 : GlobalTheory.LevPull.FibConst Y.d g := by
      refine (GlobalTheory.T.fibreConstant_iff_coveringGroup_invariant D j _ _ _ _ _ Y.d hpq.2 hG.lev.1 hG.lev.2 (Or.inl ⟨hpq.1, hL.levA⟩) liftLa (fun γ => LinearMap.ext (liftLa_spec γ)) a n g
        (s₂ hg)).2 fun γ hγ => ?_
      have h0 := h γ (hker γ hγ ▸ P.one_mem)
      rw [show (⟨θ γ, hker γ hγ ▸ P.one_mem⟩ : P) = 1 from Subtype.ext (hker γ hγ), map_one, Units.val_one, map_one,
        one_smul] at h0
      exact h0
    have h2 : g ∈ Submodule.span Y.d.c₂.F (Set.range π') := by
      have := Submodule.mem_map_of_mem (f := (Y.V (wtZ a n)).subtype) ((p5 ⟨g, hg⟩).2 h1)
      rwa [Submodule.map_span, ← Set.range_comp] at this
    refine Submodule.span_mono ?_ (mem_span_image_eigen π' ρ
      (fun x y v => Subtype.ext (actL_mul _ _ _ hact.total hact.func hact.mul x y (s₁ v.2).1))
      (fun γ => (transl Y.d.Xo₂ Y.d.c₂ γ).toLinearMap) θ hc P lam hs h2 h)
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, ⟨hC.1 v.2, fun x => congrArg Subtype.val (hv x)⟩, (hP a n _ (s₁ v.2) _).2 (p1 v)⟩

end Forms

end GlobalTheory.CovTop.TypeLattice

namespace GlobalTheory.CovTop.TypeLattice

section Point

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.BigTop GlobalTheory.AllWt
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed grpHR latN chiHR genChar transl)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU)

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem eigen_iff {K M R V : Type} [Field K] [Field M] [Algebra K M] [AddCommGroup R] [Module K R] [AddCommGroup V] [Module K V]
    [Module M V] [IsScalarTower K M V] {C : Submodule K R} {W : Submodule K V} (e : C ≃ₗ[K] W) (f : C) {g : R} (hg : g ∈ C) {y : V}
    (he : (e ⟨g, hg⟩ : V) = y) {a : K} {b : M} (hb : algebraMap K M a = b) : y = b • (e f : V) ↔ g = a • (f : R) := by
  rw [← he, ← hb, algebraMap_smul, ← Submodule.coe_smul, ← map_smul, Subtype.coe_inj, e.injective.eq_iff, Subtype.ext_iff]
  rfl

theorem exists_root (p : PtAt ex Csz) (k : Fin 2) : ∃ ζ : p.T.Q.c.F, IsPrimitiveRoot ζ (D.host.g k) := by
  have hN0 : p.T.Q.l.M' ≠ 0 := Nat.lcm_ne_zero (by have := p.T.Q.l.three_le; omega) p.T.Q.l.A_pos.ne'
  have hM : p.T.Q.l.M = D.host.g 0 * D.host.g 1 := p.fw.laws.pins.2.1.1
  have hz : IsPrimitiveRoot (⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta p.T.Q.l.M', p.T.Q.c.zeta_mem⟩ : p.T.Q.c.F) p.T.Q.l.M' :=
    IsPrimitiveRoot.of_map_of_injective (f := p.T.Q.c.F.val) (Complex.isPrimitiveRoot_exp _ hN0) Subtype.val_injective
  obtain ⟨c, hc⟩ : D.host.g k ∣ p.T.Q.l.M' :=
    dvd_trans (hM ▸ GlobalTheory.LevDesc.g_dvd k) (Nat.dvd_lcm_left p.T.Q.l.M p.T.Q.l.A)
  exact ⟨_, hz.pow (Nat.pos_of_ne_zero hN0) (hc.trans (mul_comm _ _))⟩

set_option maxHeartbeats 1000000 in

theorem typeK_eq (p : PtAt ex Csz) (i : Fin D.R.m) (lam : (p.F.lv2.lvl false).P →* (p.T.Q.c.F)ˣ)
    (hlam : ∀ u : (p.F.lv2.lvl false).P, algebraMap p.T.Q.c.F D.what₂.LL (lam u : (p.T.Q.c.F)ˣ) =
      (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL)) :
    typeK p.fw p.F.lv2 i = {f : p.T.R ((i : ℕ) + 1) | f ∈ p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n ∧
      ∀ u : (p.F.lv2.lvl false).P, actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (p.O i).lev2 u f =
        ((lam u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • f} := by
  have hk : ActKeeps (κ := p.κ) p.O i := fun g =>
    GlobalTheory.LevelCusp.actLev_mem_cuspA_of_actLev p.T p.κ i _ p.fw.laws (p.pins i).2.act.1 g fun _ => rfl
  have key : ∀ (f : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n) (u : (p.F.lv2.lvl false).P),
      (p.R.toRealDat.FW i).ρ u ((p.fw.e i f : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL) =
        (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) •
          ((p.fw.e i f : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL) ↔
      actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (p.O i).lev2 u f = ((lam u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • (f : p.T.R ((i : ℕ) + 1)) := by
    intro f u
    obtain ⟨hf, he⟩ := (p.rhoGeo i).1 hk u f
    exact eigen_iff (p.fw.e i) f hf he (hlam u)
  ext f
  exact ⟨fun ⟨h, hf⟩ => ⟨h, fun u => (key ⟨f, h⟩ u).1 (hf u)⟩, fun ⟨h, hf⟩ => ⟨h, fun u => (key ⟨f, h⟩ u).2 (hf u)⟩⟩

set_option maxHeartbeats 1000000 in

theorem latDeep_eq_latN (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i) {e : ℕ} {o : ℝ} (hY : Y.Good e o) :
    ∃ (fr : TypeFrame (dat p i) Y.d.l₂) (ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) Y.d.c₂.F),
      (∀ v, ψ v ≠ 1) ∧ IsTypeLevel Y.d.l₂ ∧ latDeep p i Y = latN fr Y.U (Gk p i) ψ := by
  have hJ := p.fw.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.succ_pos _, i.2⟩
  have hM : p.T.Q.l.M = D.host.g 0 * D.host.g 1 := hJ.pins.2.1.1
  have hA : p.T.Q.l.A = 1 := hJ.pins.2.1.2
  have hl₂ : IsTypeLevel Y.d.l₂ :=
    (GlobalTheory.LevDesc.isTypeLevel_of_eq hY.lev.2 (hY.lev.1.2.1.trans (by rw [hM])) (hM ▸ hY.lev.1.2.2.1.symm)).1
  have hMb := ((p.pins i).2.tuple ()).half.1
  have hr : (dat p i).p + (dat p i).q = D.R.r := (GlobalTheory.Member.exists_iotaOK D p.T.Q hJ.pins _ hj).2.1
  have hle : Y.d.l₂.Mb ≤ p.T.Q.l.Mb := hY.lev.1.2.2.2.1.le.trans Ideal.mul_le_left
  obtain ⟨fr, ε, iso, h1, h2⟩ := GlobalTheory.T.exists_typeFrame_cover_levelMaps_reductions D _ _ _ _ _ p.R.toRealDat i (p.charW.base.lev.βW i) _ (dat p i) _ Y.d.l₂ _
    (GlobalTheory.LevelAction.latEmb_iotaW p.T hJ i) hr hA hM hl₂ hle hMb _ (p.pins i).2.lift.lev
  obtain ⟨t, ψ, t1, t2, t3, t4⟩ := GlobalTheory.TypeBase.base_level_unip_char D _ _ _ _ _ p.R.toRealDat p.F.lv2 p.charW.base.grp.levels p.charW.base.grp.chiW
    (exists_root p) ε iso
  let j : p.T.Q.c.F →+* Y.d.c₂.F := (Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF p.T.Q.c Y.c' Y.hle)
  let s : (p.F.lv2.lvl false).P →* levelU D.host :=
    (t.symm.toMonoidHom.comp (p.F.lv2.lvl false).P.subtype).codRestrict _ fun u => (t3 _).1 (by simp)
  let lam : (p.F.lv2.lvl false).P →* (p.T.Q.c.F)ˣ := ((genChar ψ).comp s)⁻¹
  have hv : ∀ u (h : t u ∈ (p.F.lv2.lvl false).P), ((lam ⟨t u, h⟩ : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) = (psiU ψ u)⁻¹ := by
    intro u h
    show (((genChar ψ (s ⟨t u, h⟩))⁻¹ : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) = _
    rw [Units.val_inv_eq_inv_val, GlobalTheory.LevDesc.genChar_apply]
    exact congrArg (fun x => (psiU ψ x)⁻¹) (t.symm_apply_apply u)
  have hlam : ∀ u : (p.F.lv2.lvl false).P, algebraMap p.T.Q.c.F D.what₂.LL (lam u : (p.T.Q.c.F)ˣ) =
      (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) := by
    rintro ⟨u, h⟩
    obtain ⟨u, rfl⟩ := t.surjective u
    rw [hv, map_inv₀, (t4 u h).1, (t4 u h).2 i, one_mul, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  let ψ' : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) Y.d.c₂.F := fun v => j.toMonoidHom.compAddChar (ψ v)
  have hψ : ∀ u, psiU ψ' u = j (psiU ψ u) := fun u => by
    unfold psiU
    rw [map_prod]
    rfl
  refine ⟨fr, ψ', fun v h => t2 v (AddChar.ext _ _ fun x => j.injective ?_), hl₂, Submodule.ext fun F => ?_⟩
  · rw [AddChar.one_apply, map_one]
    exact DFunLike.congr_fun h x
  refine and_congr_right fun _ => ?_
  have H := mem_span_pull_iff D p.T _ Y e o hJ hj hY _ _ (dom_wtA (p.κ i)) _ (p.O i).lev (p.pins i).2.act.1
    (fun g => GlobalTheory.LevelCusp.actLev_mem_cuspA_of_actLev p.T p.κ i _ hJ (p.pins i).2.act.1 g fun _ => rfl)
    (p.F.lv2.lvl false).P lam (t.toMonoidHom.comp (typeRed fr)) (fun γ => h1 γ _ (t1 _))
    (fun γ h => by rw [MonoidHom.comp_apply, h2 γ h, map_one])
    (fun u _ => ⟨GlobalTheory.LevDesc.typeEmb hl₂ fr (t.symm u), by
      rw [MonoidHom.comp_apply, GlobalTheory.LevDesc.typeRed_typeEmb]; exact t.apply_symm_apply u⟩) F F.2
  rw [← typeK_eq p i lam hlam] at H
  refine H.trans (Iff.trans ?_ GlobalTheory.LevDesc.mem_levEigen_iff_transl.symm)
  have hc : ∀ (γ : LevelAut (dat p i) Y.d.l₂) (h : t (typeRed fr γ) ∈ (p.F.lv2.lvl false).P) (h' : γ ∈ grpHR fr),
      j ((lam ⟨t (typeRed fr γ), h⟩ : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) = (((chiHR fr ψ' ⟨γ, h'⟩)⁻¹ : (Y.d.c₂.F)ˣ) : Y.d.c₂.F) := by
    intro γ h h'
    rw [hv, map_inv₀, ← hψ, Units.val_inv_eq_inv_val, GlobalTheory.LevDesc.chiHR_apply]
  exact ⟨fun h γ => (h γ ((t3 _).2 γ.2)).trans (congrArg (· • _) (hc _ _ γ.2)),
    fun h γ hγ => (h ⟨γ, (t3 _).1 hγ⟩).trans (congrArg (· • _) (hc _ hγ _).symm)⟩

theorem log_card_le (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i) (hY : GoodCov p i Y) {PP A N : ℝ} (hN : HostNum D L PP A N)
    (S : Subgroup (LevelAut (dat p i) Y.d.l₂)) : Real.log (Nat.card S) ≤ 45 * zBase L ^ 2 := by
  have hL10 : 10 ≤ L.sc.L := hN.big.2.1
  have hgpos : ∀ k, (0 : ℝ) < (D.host.g k : ℝ) := fun k => by exact_mod_cast (D.host.g_prime k).pos
  have hlog3p : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * 15 ^ expL L.sc.L := by
    rw [hY.1.lev.1.2.1, hY.1.pd]
    congr 1
    exact p.fw.laws.pins.2.1.1
  have he : (expL L.sc.L : ℝ) * Real.log 3 ≤ 3 * L.sc.L := by
    have := Nat.floor_le (show 0 ≤ 3 * L.sc.L / Real.log 3 by positivity)
    unfold expL
    rwa [le_div_iff₀ hlog3p] at this
  have h15 : Real.log 15 ≤ 5 / 2 * Real.log 3 := by
    have : Real.log ((15 : ℝ) ^ 2) ≤ Real.log ((3 : ℝ) ^ 5) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  have hlogM : Real.log Y.d.l₂.M ≤ 30 * L.sc.L := by
    have he0 : (0 : ℝ) ≤ expL L.sc.L := Nat.cast_nonneg _
    rw [hM]
    push_cast
    rw [Real.log_mul (mul_pos (hgpos 0) (hgpos 1)).ne' (by positivity : (0 : ℝ) < 15 ^ expL L.sc.L).ne',
      Real.log_mul (hgpos 0).ne' (hgpos 1).ne', Real.log_pow]
    have g0 := hN.logg 0
    have g1 := hN.logg 1
    nlinarith
  have hr : (dat p i).p + (dat p i).q = D.R.r :=
    (GlobalTheory.Member.exists_iotaOK D p.T.Q p.fw.laws.pins _ ⟨Nat.succ_pos _, i.2⟩).2.1
  have h1 := (Subgroup.card_le_card_group S).trans (GlobalTheory.ShortDet.card_levelAut_le (dat p i) Y.d.l₂)
  rw [hr, hN.deg, Nat.mul_div_cancel_left _ two_pos] at h1
  have h0 : (0 : ℝ) < Nat.card S := by exact_mod_cast Nat.card_pos
  have h2 := Real.log_le_log h0 (Nat.cast_le.2 h1)
  rw [Nat.cast_pow, Real.log_pow] at h2
  push_cast at h2
  refine h2.trans ((mul_le_mul_of_nonneg_left hlogM (by positivity)).trans ?_)
  unfold zBase
  have h3 : (0 : ℝ) ≤ ((D.R.f : ℝ) * D.R.r) ^ 2 := by positivity
  rw [mul_pow, mul_pow _ L.sc.L]
  generalize ((D.R.f : ℝ) * D.R.r) ^ 2 = X at *
  nlinarith [mul_nonneg h3 (by linarith : (0 : ℝ) ≤ L.sc.L), mul_nonneg (mul_nonneg h3 (by linarith : (0 : ℝ) ≤ L.sc.L)) (by linarith : (0 : ℝ) ≤ L.sc.L - 10)]

end Point

section Main

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.LevDesc (TypeFrame grpHR latN)

theorem latDeep_eq_latN_covers : Hypotheses2 → Gram → DeepGood → Covers fun Fm x _ ι p i Y _ _ => ∃ (fr : TypeFrame (dat p i) Y.d.l₂) (ψ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.Sq (Fm.D x ι).host, AddChar (ZMod ((Fm.D x ι).host.g v.1)) Y.d.c₂.F), (∀ v, ψ v ≠ 1) ∧ GlobalTheory.LevDesc.IsTypeLevel Y.d.l₂ ∧ latDeep p i Y = latN fr Y.U (Gk p i) ψ ∧ Real.log (Nat.card (grpHR fr)) ≤ 45 * zBase (Fm.L x ι) ^ 2 := by
  intro _ _ _
  refine GlobalTheory.CovTop.CovSz.covers_of_lifts (GlobalTheory.CovTop.Sizes.hostN 0) ?_
  intro eps Fm x hx ι p i C _ hN _ Y hY
  obtain ⟨fr, ψ, h1, h2, h3⟩ := latDeep_eq_latN p i Y hY.1
  exact ⟨fr, ψ, h1, h2, h3, log_card_le p i Y hY hN _⟩

end Main

end GlobalTheory.CovTop.TypeLattice
