import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairTAdjTLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateKernelAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFinrankOfCokernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedBasis
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsTangentChartOfIsUnivChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PlaceShiftSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsUnivRingBc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.PointMap
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PointSig

section Rank

open GlobalTheory.HodgeTateCompare GlobalTheory.EigenLieCompare GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeRankLie

variable {O C : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [Algebra O C] [IsFractionRing O C]
  {G : Over (Sp O)} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {Λ : Type} [CommRing Λ] (α : Out.RingAct G Λ)

theorem rTau_eq_of_lieMult (τ : Λ →+* O) {N : ℕ}
    (h : LieMult (ofRingAct α) (spMap (algebraMap O C)) ((algebraMap O C).comp τ) N) : AvDefs.rTau G α τ = N := by
  obtain ⟨n, x, hx⟩ := Chart.univChartLoc G
  have hB : LieLatCompare.CoordBC hx C :=
    (LieLatCompare.tangentBaseChange_iff_one.2 (LieLatCompare.tanBCOne_of_tanBCSt Chart.tanBC)) O G n x hx C
  rw [LieLatCompare.lieMult_iff hx hB] at h
  obtain ⟨h₁, h₂⟩ := finite_free_eigSub α τ
  rw [rTau_eq, eigRank_eq, Module.finrank_linearMap_self, ← h]
  choose f₀ hf₀ using fun c : Fin n → O =>
    (lieEquiv G).surjective ⟨Chart.tvec (x := x) c, Chart.isTan_tvec hx c⟩
  have hf : ∀ c, (lieEquiv G (f₀ c)).1 = Chart.tvec (x := x) c := fun c => congrArg Subtype.val (hf₀ c)
  let f : (Fin n → O) →ₗ[O] GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Lie G :=
    { toFun := f₀
      map_add' := fun c c' => lie_ext (by
        rw [lieEquiv_add, hf, hf, hf]
        exact Chart.tvec_add hx c c')
      map_smul' := fun a c => lie_ext (by
        rw [RingHom.id_apply, lieEquiv_smul, hf, hf]
        exact Chart.tvec_smul hx a c) }
  replace hf : ∀ c, (lieEquiv G (f c)).1 = Chart.tvec (x := x) c := hf
  let e : (Fin n → O) ≃ₗ[O] GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Lie G := LinearEquiv.ofBijective f
    ⟨fun c c' hc => Chart.tvec_inj hx (by rw [← hf, ← hf, hc]), fun y =>
      ⟨Chart.tcoord hx (lieEquiv G y).1 (lieEquiv G y).2, lie_ext (by
        rw [hf]; exact (Chart.tcoord_spec hx _ _).symm)⟩⟩
  have hmem : ∀ c, e c ∈ eigSub α τ ↔ ∀ a, lieAct hx (ofRingAct α) a c = τ a • c := fun c =>
    forall_congr' fun a => by
      haveI := α.hom a
      change (lieEquiv G (f c)).1 ≫ _ = (lieEquiv G (τ a • f c)).1 ↔ _
      rw [← map_smul, hf, hf, Chart.tvec_smul hx]
      exact Chart.tvec_eig_iff hx (α.act a) c (τ a)
  let B : eigSub α τ →ₗ[O] (Fin n → C) :=
    (Algebra.linearMap O C).compLeft (Fin n) ∘ₗ e.symm.toLinearMap ∘ₗ (eigSub α τ).subtype
  have hinj := IsFractionRing.injective O C
  have hBi : Function.Injective B := fun y y' hy =>
    Subtype.ext (e.symm.injective (funext fun k => hinj (congrFun hy k)))
  have key : ∀ (c : Fin n → O) (a : Λ), (extendLin C (lieAct hx (ofRingAct α) a) -
      (algebraMap O C).comp τ a • (LinearMap.id : (Fin n → C) →ₗ[C] _)) (algebraMap O C ∘ c) = 0 ↔
      lieAct hx (ofRingAct α) a c = τ a • c := fun c a => by
    rw [LinearMap.sub_apply, LieLatCompare.extendLin_comp, sub_eq_zero]
    refine ⟨fun hc => funext fun k => hinj ?_, fun hc => funext fun k => ?_⟩
    · simpa [Algebra.smul_def] using congrFun hc k
    · simp [hc, Algebra.smul_def]
  rw [← HodgeTateEigenRank.finrank_span_range (C := C) B hBi]
  refine congrArg (fun S : Submodule C (Fin n → C) => Module.finrank C S)
    (le_antisymm (Submodule.span_le.2 ?_) fun w hw => ?_)
  · rintro _ ⟨y, rfl⟩
    refine (Submodule.mem_iInf _).2 fun a => (key (e.symm y.1) a).2 ?_
    exact (hmem _).1 (by rw [e.apply_symm_apply]; exact y.2) a
  · obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) w
    choose c hc using hs
    have hs' : algebraMap O C s ≠ 0 := fun h0 => nonZeroDivisors.coe_ne_zero s (hinj (by rw [h0, map_zero]))
    have hc' : algebraMap O C ∘ c = algebraMap O C s • w := funext fun k => by
      simpa [Algebra.smul_def] using hc k
    have hm : e c ∈ eigSub α τ := (hmem c).2 fun a => (key c a).1 (by
      rw [hc']
      exact (Submodule.mem_iInf _).1 (Submodule.smul_mem _ _ hw) a)
    have : w = (algebraMap O C s)⁻¹ • B ⟨e c, hm⟩ := by
      have h1 : B ⟨e c, hm⟩ = algebraMap O C ∘ c := by
        change algebraMap O C ∘ e.symm (e c) = _
        rw [e.symm_apply_apply]
      rw [h1, hc', smul_smul, inv_mul_cancel₀ hs', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end Rank

section Frames

open GlobalTheory.HodgeTateCompare GlobalTheory.EigenLieCompare GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O]
  [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem bLie_injective (hcok : CokernelBound P) : Function.Injective P.bLie := by
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  obtain ⟨-, -, hb⟩ := Point.omega_free_finite_bijective p C v O Λ P
  have hp : algebraMap O C ((p : O) ^ 2) ≠ 0 := by
    rw [map_pow, map_natCast]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  intro x y hxy
  have h0 : ∀ t, (P.al₀ t).1 x = (P.al₀ t).1 y := fun t => P.integers.hom_inj (by
    rw [← P.pairV_bLie, ← P.pairV_bLie, hxy])
  have h1 : ∀ z, (P.al z).1 x = (P.al z).1 y := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, Submodule.coe_add, Pi.add_apply, hz, hz']
    | tmul c t => simp only [Point.al_tmul, Submodule.coe_smul, Pi.smul_apply, h0]
  refine hb.1 (LinearMap.ext fun f => ?_)
  obtain ⟨z, hz⟩ := hcok f
  have h2 := h1 z
  rw [hz] at h2
  exact mul_left_cancel₀ (fun h => hp (by rw [h, map_zero])) h2

theorem exists_basis_wRec (hinj : Function.Injective P.bLie) (τ : Λ →+* O) {n : ℕ}
    (hn : AvDefs.rTau P.Gt P.oGt τ = n) :
    ∃ x : Fin n → LieG P.Gt, (∀ j, AvDefs.IsEig P.Gt P.oGt τ (x j)) ∧
      LinearIndependent C (fun j => P.bLie (x j)) ∧
      Submodule.span O (Set.range fun j => P.bLie (x j)) = P.wRec τ := by
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v P.integers
  haveI : IsFractionRing O C := P.integers.isFractionRing
  haveI := (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ _ ⟨P.D⟩).1
  obtain ⟨h₁, h₂⟩ := finite_free_eigSub P.oGt τ
  rw [rTau_eq, eigRank_eq, Module.finrank_linearMap_self] at hn
  let B : eigSub P.oGt τ →ₗ[O] P.V :=
    { toFun := fun x => P.bLie (lieEquiv P.Gt x.1)
      map_add' := fun x y => by
        rw [← P.bLie_add]
        exact congrArg P.bLie (Subtype.ext (lieEquiv_add x.1 y.1))
      map_smul' := fun c x => by
        rw [RingHom.id_apply, ← P.bLie_scale]
        exact congrArg P.bLie (Subtype.ext (lieEquiv_smul c x.1)) }
  have hBi : Function.Injective B := fun x y h =>
    Subtype.ext ((lieEquiv P.Gt).injective (hinj h))
  have hr : LinearMap.range B = P.wRec τ := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(eigEquiv P.oGt τ).symm (subEquiv P.oGt τ x), rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨(subEquiv P.oGt τ).symm (eigEquiv P.oGt τ x), congrArg P.bLie ?_⟩
      exact (subEquiv_val P.oGt τ _).symm.trans
        (congrArg Subtype.val ((subEquiv P.oGt τ).apply_symm_apply _))
  let b := Module.finBasisOfFinrankEq O (eigSub P.oGt τ) hn
  refine ⟨fun j => lieEquiv P.Gt (b j).1, fun j => ((eigEquiv P.oGt τ).symm (subEquiv P.oGt τ (b j))).2,
    (LinearIndependent.iff_fractionRing O C).1 (b.linearIndependent.map' B (LinearMap.ker_eq_bot.2 hBi)), ?_⟩
  rw [← hr]
  change Submodule.span O (Set.range (B ∘ b)) = _
  rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top]

theorem exists_frame (hinj : Function.Injective P.bLie) (τ : Λ →+* O) {n : ℕ} (hn : AvDefs.rTau P.Gt P.oGt τ = n)
    {La : Submodule O P.V} (hfg : La.FG) (hle : P.wRec τ ≤ La) :
    ∃ (x : Fin n → LieG P.Gt) (g : Matrix (Fin n) (Fin n) C), (∀ j, AvDefs.IsEig P.Gt P.oGt τ (x j)) ∧
      LinearIndependent C (fun j => P.bLie (x j)) ∧
      Submodule.span O (Set.range fun j => P.bLie (x j)) = P.wRec τ ∧ g.det ≠ 0 ∧
      IsLatBasis C La fun i => ∑ j, g i j • P.bLie (x j) := by
  obtain ⟨x, h1, h2, h3⟩ := exists_basis_wRec P hinj τ hn
  obtain ⟨g, g1, g2, g3⟩ := FlagBasis.exists_adapted_basis O C P.V v P.integers n La hfg _ h2 fun j =>
    ⟨1, one_ne_zero, by rw [one_smul]; exact hle ⟨⟨x j, h1 j⟩, rfl⟩⟩
  refine ⟨x, g, h1, h2, h3, ?_, g3⟩
  rw [Matrix.det_of_lowerTriangular _ fun i j hij => g1 i j hij]
  exact Finset.prod_ne_zero_iff.2 fun i _ => g2 i

theorem span_eq_eigW (hcok : CokernelBound P) (hW : P.W = Submodule.span C (Set.range P.bLie)) (τ : Λ →+* O) {n : ℕ}
    (hn : AvDefs.rTau P.Gt P.oGt τ = n) {x : Fin n → LieG P.Gt} (h1 : ∀ j, AvDefs.IsEig P.Gt P.oGt τ (x j))
    (h2 : LinearIndependent C fun j => P.bLie (x j)) :
    Submodule.span C (Set.range fun j => P.bLie (x j)) = P.eigW τ := by
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨j, rfl⟩
    exact ⟨hW.ge (Submodule.subset_span ⟨_, rfl⟩), bLie_mem_eigV (h1 j)⟩
  · rw [finrank_span_eq_card h2, Fintype.card_fin, HodgeTateEigenRank.finrank_eigW p C v O Λ P hcok hW, hn]

end Frames

section Triples

open GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] [IsAlgClosed C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C)

omit [NumberField K] [IsAlgClosed C] in

theorem conj_rt_ne (H : Host E) : IsCMField.complexConj E (H.rt : E) ≠ (H.rt : E) := by
  intro h
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
  rw [h] at h1
  have h2 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, RingOfIntegers.coe_eq_algebraMap, ← map_pow, H.rt_sq]; simp
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h1.symm
  rw [hr] at h2
  have h3 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h2
  have h4 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

open Classical in

theorem rTau_patPoint (T : PAT H (Sp (𝓞 K))) {ρ : 𝓞 K} {p q : ℕ} (hT : HasType H T.t.act ρ p q) (τ : 𝓞 E →+* O) :
    letI := H.starRing
    AvDefs.rTau (patPoint hv ε i T).Gt (patPoint hv ε i T).oGt τ =
      if algebraMap O C (τ H.rt) = i (ρ : K) then p else q := by
  letI := H.starRing
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsFractionRing O C := hv.isFractionRing
  haveI := (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ _ ⟨(patPoint hv ε i T).D⟩).1
  have hβ : ∀ a, ((algebraMap O C).comp (embO hv i)) a = i (a : K) := fun a => algebraMap_embO hv i a
  have h := hT C ((algebraMap O C).comp (embO hv i)) (fun a b hab => by
    rw [hβ, hβ] at hab
    exact RingOfIntegers.coe_injective (i.injective hab)) ((algebraMap O C).comp τ)
  rw [hβ, ← spMap_spMap] at h
  refine rTau_eq_of_lieMult (C := C) _ τ ((LiePull.lieMult_pull (𝓞 E) _ _ T.t.G (patPoint hv ε i T).Gt (spMap (embO hv i))
    (pullback.fst T.t.G.hom _) T.t.act _ (isGrpPullback_pullback T.t.G _) (fun a => ?_) C _ _ _).2 ?_)
  · change ((patPoint hv ε i T).oGt.act a).left ≫ _ = _
    rw [goodPoint_oGt]
    exact pullback.lift_fst _ _ _
  · split_ifs with h0
    exacts [h.1 h0, h.2 h0]

end Triples

section Main

open GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] [Fact ¬IsUnit (ℓ : O)] [IsAdicComplete (Ideal.span {(ℓ : O)}) O] [Algebra ℤ_[ℓ] O]
  [Algebra ℤ_[ℓ] C] [IsScalarTower ℤ_[ℓ] O C]

open Classical in

def HasSigFrames [StarRing (𝓞 E)] (P : Point ℓ v O (𝓞 E)) (rt : 𝓞 E) (τ : E →+* C) (p q : ℕ) : Prop :=
  (∀ φ : E →+* C, Module.finrank C (P.eigW (embO P.integers φ)) = if φ (rt : E) = τ (rt : E) then p else q) ∧
    ∃ (x : Fin p → LieG P.Gt) (x' : Fin q → LieG P.Gt) (g : Matrix (Fin p) (Fin p) C) (g' : Matrix (Fin q) (Fin q) C),
      Submodule.span O (Set.range fun j => P.bLie (x j)) = P.wRec (embO P.integers τ) ∧
      Submodule.span O (Set.range fun j => P.bLie (x' j)) = P.wRec ((embO P.integers τ).comp (starRingEnd (𝓞 E))) ∧
      IsLatBasis C (P.latTQuot (σ := fun φ : E →+* C => embO P.integers φ) (isSplitting_embO P.integers) τ)
        (fun k => ∑ j, g k j • P.bLie (x j)) ∧
      IsLatBasis C (P.latTSub ((embO P.integers τ).comp (starRingEnd (𝓞 E)))) (fun k => ∑ j, g' k j • P.bLie (x' j)) ∧
      g.det ≠ 0 ∧ g'.det ≠ 0 ∧
      (∀ j, AvDefs.IsEig P.Gt P.oGt (embO P.integers τ) (x j)) ∧
      (∀ j, AvDefs.IsEig P.Gt P.oGt ((embO P.integers τ).comp (starRingEnd (𝓞 E))) (x' j)) ∧
      LinearIndependent C (fun j => P.bLie (x j)) ∧ LinearIndependent C (fun j => P.bLie (x' j)) ∧
      Submodule.span C (Set.range fun j => P.bLie (x j)) = P.eigW (embO P.integers τ) ∧
      Submodule.span C (Set.range fun j => P.bLie (x' j)) = P.eigW ((embO P.integers τ).comp (starRingEnd (𝓞 E)))

open Classical in

theorem hasSigFrames_of_rTau [StarRing (𝓞 E)] (P : Point ℓ v O (𝓞 E)) (hcok : CokernelBound P)
    (hW : P.W = Submodule.span C (Set.range P.bLie)) (rt : 𝓞 E) (τ : E →+* C) (hrt : τ ((star rt : 𝓞 E) : E) ≠ τ (rt : E))
    {p q : ℕ} (h : ∀ χ : 𝓞 E →+* O, AvDefs.rTau P.Gt P.oGt χ = if algebraMap O C (χ rt) = τ (rt : E) then p else q) :
    HasSigFrames P rt τ p q := by
  have hinj := bLie_injective P hcok
  have hp : AvDefs.rTau P.Gt P.oGt (embO P.integers τ) = p := by rw [h, algebraMap_embO, if_pos rfl]
  have hq : AvDefs.rTau P.Gt P.oGt ((embO P.integers τ).comp (starRingEnd (𝓞 E))) = q := by
    rw [h, RingHom.comp_apply, algebraMap_embO, starRingEnd_apply, if_neg hrt]
  obtain ⟨x, g, a1, a2, a3, a4, a5⟩ := exists_frame P hinj _ hp
    (P.fg_latTQuot (σ := fun φ : E →+* C => embO P.integers φ) (isSplitting_embO P.integers) τ)
    ((P.wRec_le_latTSub _).trans (P.latTSub_le_latTQuot (σ := fun φ : E →+* C => embO P.integers φ) _ τ))
  obtain ⟨x', g', b1, b2, b3, b4, b5⟩ := exists_frame P hinj _ hq (fg_inf P.integers P.fg_latT _) (P.wRec_le_latTSub _)
  refine ⟨fun φ => ?_, x, x', g, g', a3, b3, a5, b5, a4, b4, a1, b1, a2, b2, span_eq_eigW P hcok hW _ hp a1 a2,
    span_eq_eigW P hcok hW _ hq b1 b2⟩
  rw [HodgeTateEigenRank.finrank_eigW ℓ C v O _ P hcok hW, h, algebraMap_embO]

variable (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C)

end Main

end GlobalTheory.PointSig
