import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTangentReductionEqOrigin
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpTan

open GlobalTheory.HolHom GlobalTheory.TorusModel

theorem le_wchart_iff {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (x : Z ⟶ Y)
    (j : K → L.ι) : ⊤ ≤ LB.wchart L (fun k => x ≫ ψ k) j ↔ ⊤ ≤ x ⁻¹ᵁ LB.wchart L ψ j :=
  ⟨fun h _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h hy) k,
    fun h _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h hy) k⟩

theorem valR_of_corr {A : Type} [CommRing A] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Sp A ⟶ X)} {ψ : K → (Y ⟶ X)} {ε : K → ℤ} {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen)
    {t : LB.Gen (LB.LinComb L ψ ε)} (ht : t.IsGen) (x : Sp A ⟶ Y) (hφ : φ = fun k => x ≫ ψ k)
    (h : LB.Gen.Corr L _ _ _ _ u (LB.pullGen L _ _ t x)) (j : K → L.ι) :
    valR (𝟙 (Sp A)) (LB.wchart L φ j) (u.s j).val = valR x (LB.wchart L ψ j) (t.s j).val := by
  subst hφ
  obtain rfl := TorusCoord.gen_eq_of_corr hL hu (DVR.pullGen_isGen _ _ _ _ ht x) h
  by_cases hj : ⊤ ≤ x ⁻¹ᵁ LB.wchart L ψ j
  · have hj' : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart L (fun k => x ≫ ψ k) j := (le_wchart_iff L ψ x j).2 hj
    refine (valR_res (U := x ⁻¹ᵁ LB.wchart L ψ j) (𝟙 (Sp A)) _ _ hj').trans ?_
    exact (valR_comp (𝟙 (Sp A)) x (LB.wchart L ψ j) _).symm.trans (by rw [Category.id_comp])
  · have h₀ : valR x (LB.wchart L ψ j) (t.s j).val = 0 := dif_neg hj
    exact (dif_neg (fun h => hj ((le_wchart_iff L ψ x j).1 h))).trans h₀.symm

section Coord

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (c : GtCoord I D e G)
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

open CoordToExt in

theorem holAt_of_coord {x : V → (Sp ℂ ⟶ (thickObj R I e G).left)} {z : V}
    (hb : HolAt (fun t => x t ≫ c.q.left) z)
    (hs : ∀ χ a, ⊤ ≤ x z ⁻¹ᵁ LB.wchart D.P.L (D.Oφ c.pG χ) a →
      DifferentiableAt ℂ (fun t => valAt' (x t) (LB.wchart D.P.L (D.Oφ c.pG χ) a) ((c.t χ).s a).val) z) :
    HolAt x z := by
  let b := Module.Free.chooseBasis ℤ D.X
  let p := (x z ≫ c.q.left) (default : PrimeSpectrum ℂ)
  choose a ha using fun k => exists_chart (DVR.linComb_isLB (Y := (thickObj R I e D.P.A).left) D.P.L D.P.isLB
    (D.Oφ (D.prBe I e) (b k)) Oε) p
  have hW : ⊤ ≤ (x z ≫ c.q.left) ⁻¹ᵁ ⨅ k, (bundle I D e (b k)).U (a k) := by
    rw [le_preimage_iff, ← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.2 ha
  obtain ⟨P, hP, hxP, hle⟩ := exists_affine _ hW
  have hl : ∀ k, c.q.left ⁻¹ᵁ P ≤ c.q.left ⁻¹ᵁ (bundle I D e (b k)).U (a k) := fun k =>
    Scheme.Hom.preimage_mono _ (hle.trans (iInf_le _ k))
  let u : ∀ k, Γ((thickObj R I e G).left, c.q.left ⁻¹ᵁ P)ˣ := fun k => res (hl k) (coordUnit c (b k) (a k))
  have := c.q_hom
  have := c.q_affine
  have bij := bijective_of_basis b c.q c.i c.q_hom c.i_hom c.q_flat c.q_surj c.q_affine c.isKernel P hP u
    (fun k Z t g w hw => by
      have hw' := GtBaseChange.translate_mem c.q c.i c.isKernel t g P w hw
      exact (gm_res _ w (hl k) hw' _).trans ((coordUnit_weight c (b k) (a k) Z t g w (hl k hw)).trans
        (congrArg _ (gm_res _ w (hl k) hw _).symm)))
  have ev : ∀ᶠ t in 𝓝 z, ⊤ ≤ x t ⁻¹ᵁ (c.q.left ⁻¹ᵁ P) := (hb P hxP).1
  let S : Subring Γ((thickObj R I e G).left, c.q.left ⁻¹ᵁ P) :=
    { carrier := {f | DifferentiableAt ℂ (fun t => valAt' (x t) _ f) z}
      mul_mem' := fun {f f'} h h' => (h.mul h').congr_of_eventuallyEq (ev.mono fun t ht => by
        simp only [valAt'_eq_valR, valR_eq _ _ ht, map_mul, Pi.mul_apply])
      add_mem' := fun {f f'} h h' => (h.add h').congr_of_eventuallyEq (ev.mono fun t ht => by
        simp only [valAt'_eq_valR, valR_eq _ _ ht, map_add, Pi.add_apply])
      neg_mem' := fun {f} h => h.neg.congr_of_eventuallyEq (ev.mono fun t ht => by
        simp only [valAt'_eq_valR, valR_eq _ _ ht, map_neg, Pi.neg_apply])
      one_mem' := (differentiableAt_const (1 : ℂ)).congr_of_eventuallyEq (ev.mono fun t ht => by
        simp only [valAt'_eq_valR, valR_eq _ _ ht, map_one])
      zero_mem' := (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq (ev.mono fun t ht => by
        simp only [valAt'_eq_valR, valR_eq _ _ ht, map_zero]) }
  have hu : ∀ k, (u k).val ∈ S := fun k => by
    have h₁ := hs (b k) (a k) (fun y hy => mem_chart c _ _ _ (hl k (hxP hy)))
    refine h₁.congr_of_eventuallyEq (ev.mono fun t ht => ?_)
    exact (valR_res (x t) (hl k) _ ht).trans (valR_res (x t) _ _ (fun y hy => hl k (ht hy)))
  have hi : ∀ w : Γ((thickObj R I e G).left, c.q.left ⁻¹ᵁ P)ˣ, w.val ∈ S → (w⁻¹).val ∈ S := fun w hw => by
    have hne : valAt' (x z) _ w.val ≠ 0 := by
      rw [valAt'_eq_valR, valR_eq (x z) (c.q.left ⁻¹ᵁ P) hxP]
      exact (w.isUnit.map _).ne_zero
    refine (DifferentiableAt.inv hw hne).congr_of_eventuallyEq (ev.mono fun t ht => ?_)
    simp only [valAt'_eq_valR, valR_eq _ _ ht, Pi.inv_apply, map_units_inv]
  refine holAt_of_affine (hP.preimage c.q.left) hxP ev fun f => ?_
  obtain ⟨f, rfl⟩ := bij.2 f
  change _ ∈ S
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; exact zero_mem _
  | add f f' h h' => rw [map_add]; exact add_mem h h'
  | single χ r =>
    have hχ : ∀ χ : D.X, ((b.constr ℤ (fun k => Additive.ofMul (u k)) χ).toMul).val ∈ S := fun χ => by
      have : χ ∈ Submodule.span ℤ (Set.range b) := b.mem_span χ
      induction this using Submodule.span_induction with
      | mem _ h => obtain ⟨k, rfl⟩ := h; rw [b.constr_basis]; exact hu k
      | zero => rw [map_zero]; exact one_mem _
      | add _ _ _ _ h h' => rw [map_add]; exact mul_mem h h'
      | smul n w _ h =>
        rw [map_smul, toMul_zsmul]
        cases n with
        | ofNat n => simpa using pow_mem h n
        | negSucc n => rw [zpow_negSucc]; exact hi _ (by simpa using pow_mem h (n + 1))
    rw [AddMonoidAlgebra.liftNCRingHom_single]
    refine mul_mem ?_ (hχ χ)
    exact ((hb P hxP).2 r).congr_of_eventuallyEq (Eventually.of_forall fun t => (valR_comp (x t) c.q.left P r).symm)

end Coord

theorem exists_represents {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {H : Over (Spec (CommRingCat.of R))}
    [GrpObj H] [IsCommMonObj H] (hG : GlobalFnsSt) (c : GtCoord ⊥ D 0 H) :
    ∃ Φ : ∀ T, (T ⟶ H) ≃ GtPt D T, Represents Φ ∧
      ∀ T (x : T ⟶ H), TorusCoord.IsPointOf c (x.left ≫ inv (fstG (⊥ : Ideal R) 0 H).left) (Φ T x) := by
  let j := inv (fstG (⊥ : Ideal R) 0 H).left
  have hj : j ≫ (thickObj R ⊥ 0 H).hom ≫ thick R ⊥ 0 = H.hom :=
    (congrArg (j ≫ ·) (Over.w (fstG (⊥ : Ideal R) 0 H)).symm).trans (IsIso.inv_hom_id_assoc _ _)
  choose φ hφ using fun T (x : T ⟶ H) => TorusCoord.exists_isPointOf c (T := T) (x.left ≫ j)
    (by rw [Category.assoc, hj, Over.w])
  have bij : ∀ T, Function.Bijective (φ T) := fun T => by
    refine ⟨fun x x' e => Over.OverMorphism.ext ((cancel_mono j).1
      ((hφ T x).unique_left c (e ▸ hφ T x'))), fun ξ => ?_⟩
    obtain ⟨y, hy⟩ := TorusCoord.exists_point c (T.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
    refine ⟨Over.homMk (y ≫ (fstG (⊥ : Ideal R) 0 H).left) ((Category.assoc _ _ _).trans
      ((congrArg (y ≫ ·) (Over.w (fstG (⊥ : Ideal R) 0 H))).trans (hy.comp_hom c))), (hφ T _).unique_right c ?_⟩
    have : (y ≫ (fstG (⊥ : Ideal R) 0 H).left) ≫ j = y := by simp [j]
    exact this.symm ▸ hy
  refine ⟨fun T => Equiv.ofBijective _ (bij T), ⟨fun T' T k x => (hφ T x).isPull c ?_, fun T x x' => ?_⟩, hφ⟩
  · have := hφ T' (k ≫ x)
    rwa [Over.comp_left, Category.assoc] at this
  · obtain ⟨T, ⟨⟨⟩⟩, s⟩ := T
    change T ⟶ Spec (CommRingCat.of R) at s
    obtain ⟨σ, rfl⟩ : ∃ σ, s = σ ≫ thick R ⊥ 0 := ⟨s ≫ inv (thick R ⊥ 0), by simp⟩
    let Z : Over (Spec (CommRingCat.of (R ⧸ (⊥ : Ideal R) ^ (0 + 1)))) := Over.mk σ
    obtain ⟨a, ha⟩ := FormalPoint.exists_lift_fstG (Z := Z) x
    obtain ⟨a', ha'⟩ := FormalPoint.exists_lift_fstG (Z := Z) x'
    have key : ∀ (b : Z ⟶ thickObj R ⊥ 0 H) (w : (Over.map (thick R ⊥ 0)).obj Z ⟶ H),
        (Over.map (thick R ⊥ 0)).map b ≫ fstG ⊥ 0 H = w → φ _ w = TorusCoord.pointsEquiv c Z b := by
      rintro b _ rfl
      refine ((TorusCoord.toGtPt_eq_iff c b _).2 ?_).symm
      have e : ((Over.map (thick R ⊥ 0)).map b ≫ fstG ⊥ 0 H).left ≫ j = b.left := by
        rw [Over.comp_left, Category.assoc, IsIso.hom_inv_id, Category.comp_id]; rfl
      exact e ▸ hφ _ _
    have e₁ := key a x ha
    have e₂ := key a' x' ha'
    have e₃ := key (a * a') (x * x') (by rw [FormalPoint.map_mul_fstG, ha, ha'])
    have := TorusCoord.isAdd_pointsEquiv c hG a a'
    rw [← e₁, ← e₂, ← e₃] at this
    exact this

theorem exists_model (hG : GlobalFnsSt) (D : DegPre ℂ) :
    ∃ (H : Over (Sp ℂ)) (_ : GrpObj H) (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T), Smooth H.hom ∧ Represents Φ ∧
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (y : Sp ℂ ⟶ Sp ℂ) (e : V → (Over.mk y ⟶ H)) (z : V),
        HolAt (fun t => (show Sp ℂ ⟶ _ from (Φ _ (e t)).b.left)) z →
        (∀ χ j, ⊤ ≤ LB.wchart D.P.L (DegPre.gtφT D _ (Φ _ (e z)).b χ) j → DifferentiableAt ℂ (fun t =>
          valR (A := ℂ) (𝟙 _) (LB.wchart D.P.L (DegPre.gtφT D _ (Φ _ (e t)).b χ) j)
            (((Φ _ (e t)).s χ).s j).val) z) →
        HolAt (fun t => (show Sp ℂ ⟶ _ from (e t).left)) z := by
  obtain ⟨H, _, _, h⟩ := exists_isGt hG (splitExt D)
  obtain ⟨c⟩ := nonempty_gtCoord hG h ⊥ 0
  obtain ⟨Φ, h₁, h₂⟩ := exists_represents hG c
  refine ⟨H, inferInstance, Φ, (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ H h).1, h₁, fun V _ _ y e z hb hs => ?_⟩
  let j := inv (fstG (⊥ : Ideal ℂ) 0 H).left
  have hφ : ∀ t χ, DegPre.gtφT D _ (Φ _ (e t)).b χ = fun k => ((e t).left ≫ j) ≫ D.Oφ c.pG χ k := fun t χ =>
    funext fun k => (Category.id_comp _).symm.trans ((TorusCoord.comp_eq_of_left (Φ _ (e t)).b c.pG (𝟙 _)
      ((e t).left ≫ j) ((Category.id_comp _).trans (h₂ _ (e t)).1)).1 χ k)
  have H₁ : HolAt (fun t => (show Sp ℂ ⟶ _ from (e t).left ≫ j)) z := by
    refine holAt_of_coord c ?_ fun χ a ha => ?_
    · have := hb.comp (inv (fstG (⊥ : Ideal ℂ) 0 D.P.A).left)
      refine (congrArg (fun q => HolAt q z) (funext fun t => ?_)).mp this
      exact ((IsIso.eq_comp_inv (fstG (⊥ : Ideal ℂ) 0 D.P.A).left).2
        ((h₂ _ (e t)).1.trans (Category.assoc _ _ _).symm).symm).symm
    · have := hs χ a (by rw [hφ]; exact (le_wchart_iff _ _ _ a).2 ha)
      convert this using 2 with t
      exact (valR_of_corr (A := ℂ) D.P.isLB ((Φ _ (e t)).isGen χ) (c.t_gen χ) _ (hφ t χ) ((h₂ _ (e t)).2 χ) a).symm
  have := H₁.comp (fstG (⊥ : Ideal ℂ) 0 H).left
  convert this using 2 with t
  simp [j]

end GlobalTheory.ExpTan
