import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicPeriodsAdapted

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
open Filter GlobalTheory.HolHom

namespace GlobalTheory.ShFam.HorLift

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isHolTo_of_comp_open {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] {B : Set V} {y : V → (Sp ℂ ⟶ X)}
    (h : IsHolTo B fun b => y b ≫ i) : IsHolTo B y := by
  intro U f
  have key : ∀ (U' : X.Opens) (_ : i ⁻¹ᵁ (i ''ᵁ U) = U') (f : Γ(X, U')), IsOpen {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} ∧
      DifferentiableOn ℂ (fun b => valAt' (y b) U' f) {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} := by
    rintro _ rfl f
    have : IsIso (i.app (i ''ᵁ U)) := i.isIso_app _ (i.image_le_opensRange U)
    obtain ⟨g, rfl⟩ := (ConcreteCategory.bijective_of_isIso (i.app (i ''ᵁ U))).2 f
    have := h (i ''ᵁ U) g
    simp only [valAt'_eq_valR, valR_comp] at this
    exact this
  exact key U (i.preimage_image_eq U) f

theorem differentiableAt_dir [FiniteDimensional ℂ V] {G' G₀ G₁ S' S₀ S₁ : Scheme.{0}} {φ₀ : G' ⟶ G₀} {φ₁ : G' ⟶ G₁}
    {p : G' ⟶ S'} {p₀ : G₀ ⟶ S₀} {p₁ : G₁ ⟶ S₁} {f₀ : S' ⟶ S₀} {f₁ : S' ⟶ S₁} (H₀ : IsPullback φ₀ p p₀ f₀)
    (H₁ : IsPullback φ₁ p p₁ f₁) {g : ℕ} {B : Set V} {y : V → (Sp ℂ ⟶ S')} (hy : IsHolTo B y)
    {ex : V → (Fin g → ℂ) → (Sp ℂ ⟶ G₀)}
    (hex : IsHolTo (B ×ˢ Set.univ) fun bz : V × (Fin g → ℂ) => ex bz.1 bz.2)
    (hover : ∀ b ∈ B, ∀ w, ex b w ≫ p₀ = y b ≫ f₀) {b₀ : V} (hb₀ : b₀ ∈ B)
    (hinj : ∀ w, IsDerivAt (ex b₀) 0 w (constVec (ex b₀ 0)) → w = 0) {v : V → (Sp (DualNumber ℂ) ⟶ G₁)}
    (hv : HolTan B v) {W : V → Fin g → ℂ}
    (hW : ∀ b ∈ B, ∃ v₀ : Sp (DualNumber ℂ) ⟶ G', v₀ ≫ p = constVec (y b) ∧ v₀ ≫ φ₁ = v b ∧
      IsDerivAt0 (ex b) (W b) (v₀ ≫ φ₀)) : DifferentiableAt ℂ W b₀ := by
  haveI : Nonempty (Sp ℂ ⟶ G') := ⟨H₀.lift _ _ (hover b₀ hb₀ 0)⟩
  choose! e h₀ hp using fun b (hb : b ∈ B) w =>
    (⟨H₀.lift _ _ (hover b hb w), H₀.lift_fst _ _ _, H₀.lift_snd _ _ _⟩ :
      ∃ x : Sp ℂ ⟶ G', x ≫ φ₀ = ex b w ∧ x ≫ p = y b)
  have hO := isOpen_of_isHolTo hex
  have he : IsHolTo (B ×ˢ Set.univ) fun bz : V × (Fin g → ℂ) => e bz.1 bz.2 := by
    have h1 := LocLift.isHolTo_congr (y' := fun bz : V × (Fin g → ℂ) => e bz.1 bz.2 ≫ φ₀) hex
      fun bz hb => h₀ _ hb.1 _
    have h2 := LocLift.isHolTo_congr (y' := fun bz : V × (Fin g → ℂ) => e bz.1 bz.2 ≫ p)
      (LocLift.isHolTo_comp hy hO differentiableOn_fst fun _ hb => hb.1) fun bz hb => hp _ hb.1 _
    exact isHolTo_of_holAt hO fun z hz =>
      holAt_of_isPullback H₀ (holAt_of_isHolTo h1 hz) (holAt_of_isHolTo h2 hz)
  have hsl : ∀ b ∈ B, HolAt (e b) 0 := fun b hb =>
    (holAt_of_isHolTo he (z := (b, 0)) ⟨hb, trivial⟩).precomp (k := fun z => (b, z)) (by fun_prop)
  have hder : ∀ b ∈ B, ∀ w, ∃ u, IsDerivAt (e b) 0 w u ∧ IsDerivAt (ex b) 0 w (u ≫ φ₀) ∧
      u ≫ p = constVec (y b) := fun b hb w => by
    obtain ⟨u, hu⟩ := (hsl b hb).exists_isDerivAt w
    have h1 := hu.comp φ₀
    have h2 := hu.comp p
    simp only [h₀ b hb, hp b hb] at h1 h2
    exact ⟨u, hu, h1, h2.unique (isDerivAt_const _ _ _)⟩
  have hv' : ∀ b ∈ B, IsDerivAt (fun w => e b w ≫ φ₁) 0 (W b) (v b) := fun b hb => by
    obtain ⟨v₀, a1, a2, a3⟩ := hW b hb
    obtain ⟨u, hu, h1, h2⟩ := hder b hb (W b)
    obtain rfl : u = v₀ := H₀.hom_ext (h1.unique ((isDerivAt0_iff _ _ _).1 a3)) (h2.trans a1.symm)
    exact a2 ▸ hu.comp φ₁
  have he₁ := LocLift.isHolTo_comp_hom he φ₁
  refine HolLieFrame.differentiableAt_of_forms _ b₀ fun w hw => hinj w ?_
  obtain ⟨u, hu, h1, h2⟩ := hder b₀ hb₀ w
  have h3 : IsDerivAt (fun w => e b₀ w ≫ φ₁) 0 w (constVec (e b₀ 0 ≫ φ₁)) := by
    refine (isDerivAt_constVec_iff (c := fun w => e b₀ w ≫ φ₁)).2 fun U hU f => ?_
    refine hw (fun b => fderiv ℂ (fun z => valAt' (e b z ≫ φ₁) U f) 0)
      (differentiableAt_partial (he₁ U f).1 (he₁ U f).2 ⟨⟨hb₀, trivial⟩, hU⟩) ?_
    have hc : ContinuousAt (fun b : V => (b, (0 : Fin g → ℂ))) b₀ := by fun_prop
    have hn := hc.eventually ((he₁ U f).1.mem_nhds ⟨⟨hb₀, trivial⟩, hU⟩)
    refine ((hv U f).differentiableAt (hn.mono fun b hb =>
      ⟨hb.1.1, (le_preimage_dual_iff (hv' b hb.1.1).1 U).2 hb.2⟩)).congr_of_eventuallyEq ?_
    exact hn.mono fun b hb => ((hv' b hb.1.1).2 U hb.2 f).symm
  obtain rfl : u = constVec (e b₀ 0) := H₁.hom_ext ((hu.comp φ₁).unique h3)
    (by rw [h2, Category.assoc, hp b₀ hb₀])
  rwa [Category.assoc, h₀ b₀ hb₀] at h1

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw}

theorem exists_inner_lift (x : CxPts (genStr Z) σ) (hx : Inner x) : ∃ y : Sp ℂ ⟶ Xo.XF c, y ≫ Z.jQ = x.1 := by
  haveI := Z.jQ_open
  refine ⟨IsOpenImmersion.lift Z.jQ x.1 ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨p, rfl⟩
  obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact not_not.1 hx

theorem exists_dirs (Fu : Fam Xo c σ e) (a : CxFr Z σ) (y : Sp ℂ ⟶ Xo.XF c) (hy : y ≫ Z.jQ = a.1.1) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    (hu : Fu.u i P = y ≫ pullback.fst _ _) :
    ∃ (w : Fin g → Fin g → ℂ) (M : Matrix (Fin g) (Fin g) ℂ), (∀ j, M *ᵥ w j = Pi.single j 1) ∧
      ∀ z : Letter Dw, ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
        v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = a.2.v z.1 z.2 ∧
        IsDerivAt0 (fun w => (Fu.ex i P w).left) (w (e.symm z)) (v₀ ≫ Z.m0.toSABMap.φ) := by
  have hs : y ≫ pullback.snd _ _ = spMap σ := by
    rw [← Z.jQ_over, ← Category.assoc, hy]; exact a.1.2
  obtain ⟨y', v, hx, hv⟩ := @OpenReg.exists_frPt_of_eigFrame E _ _ _ H Dw l Xo c O _ β Z (CAt σ) inferInstance
    (inferInstanceAs (IsLocalRing ℂ)) inferInstance y hs (a.1.1 ≫ genι Z)
    (by rw [← hy]; exact (Category.assoc _ _ _).symm) a.2
  obtain ⟨w, M, -, hw, hM, -⟩ := AdaptedPeriods.exists_adapted E H Dw l Xo c σ g e Fu y' i P hP (hu.trans hx.symm)
  refine ⟨w, M, hM, fun z => ⟨v z.1 z.2, (hv _ _).1, (hv _ _).2.2, ?_⟩⟩
  have := hw (e.symm z)
  rw [Equiv.apply_symm_apply, ← (hv _ _).2.1] at this
  exact this

theorem exists_hol_per : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, Inner (a b).1) → ∀ b₀ ∈ B, ∃ (B' : Set V) (i : Fin Fu.n) (Q : V → ((Fu.Di i).La →+ (Letter Dw → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ (∀ b ∈ B', Per Fu (a b) i (Q b)) ∧ ∀ v z, DifferentiableOn ℂ (fun b => Q b v z) B' := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu V _ _ _ B a hB ha hI b₀ hb₀
  haveI := Z.jQ_open
  haveI : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨(exists_inner_lift _ (hI b₀ hb₀)).choose⟩
  choose! y hy using fun b (hb : b ∈ B) => exists_inner_lift _ (hI b hb)
  have hyh : IsHolTo B y := isHolTo_of_comp_open Z.jQ (LocLift.isHolTo_congr ha.1 hy)
  let φ : V ≃L[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hBφ : IsOpen (φ.symm ⁻¹' B) := hB.preimage φ.symm.continuous
  obtain ⟨B₁, i, P₁, hB₁, hb₁, hsub, hP₁, hu₁⟩ := Fu.lift _ (φ.symm ⁻¹' B) (fun t => y (φ.symm t) ≫ pullback.fst _ _) hBφ
    (fun t ht => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, ← Z.jQ_over, ← Category.assoc, hy _ ht,
        ← OpenReg.spMap_comp]
      exact congrArg (· ≫ _) (a _).1.2)
    (LocLift.isHolTo_comp (LocLift.isHolTo_comp_hom hyh _) hBφ φ.symm.differentiableOn fun _ h => h) (φ b₀)
    (by simpa using hb₀)
  have hB' : IsOpen (φ ⁻¹' B₁) := hB₁.preimage φ.continuous
  have hsub' : φ ⁻¹' B₁ ⊆ B := fun b hb => by simpa using hsub hb
  have hu : ∀ b ∈ φ ⁻¹' B₁, Fu.u i (P₁ (φ b)) = y b ≫ pullback.fst _ _ := fun b hb => by simpa using hu₁ _ hb
  have hex : IsHolTo ((φ ⁻¹' B₁) ×ˢ Set.univ) fun bz : V × (Fin g → ℂ) => (Fu.ex i (P₁ (φ bz.1)) bz.2).left :=
    LocLift.isHolTo_comp (β := fun bz : V × (Fin g → ℂ) => (φ bz.1, bz.2)) (Fu.hol i _ B₁ P₁ hB₁ hP₁).2
      (hB'.prod isOpen_univ) (by fun_prop) fun _ h => ⟨h.1, trivial⟩
  choose! w M hM hw using fun b (hb : b ∈ φ ⁻¹' B₁) =>
    exists_dirs Fu (a b) (y b) (hy b (hsub' hb)) i (P₁ (φ b)) (hP₁.1 _ hb) (hu b hb)
  have hM' : ∀ b ∈ φ ⁻¹' B₁, M b * (Matrix.of fun i j => w b j i) = 1 := fun b hb => by
    ext i j
    have := congrFun (hM b hb j) i
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  let Q : V → ((Fu.Di i).La →+ (Letter Dw → ℂ)) := fun b =>
    AddMonoidHom.mk' (fun v z => (M b *ᵥ P₁ (φ b) v) (e.symm z)) fun v v' => by
      funext z
      simp [Matrix.mulVec_add]
  refine ⟨φ ⁻¹' B₁, i, Q, hB', hb₁, hsub', fun b hb => ⟨P₁ (φ b), fun z => w b (e.symm z), y b, hP₁.1 _ hb,
    (hu b hb).symm, hy b (hsub' hb), hw b hb, fun v => ?_⟩, fun v z b hb => ?_⟩
  · have h1 := congrArg (· *ᵥ P₁ (φ b) v) (mul_eq_one_comm.1 (hM' b hb))
    simp only [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at h1
    rw [← h1]
    refine Eq.trans ?_ (Equiv.sum_comp e.symm fun j => (M b *ᵥ P₁ (φ b) v) j • w b j).symm
    funext k
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  · have hwd : ∀ j, DifferentiableAt ℂ (fun b => w b j) b := fun j => by
      obtain ⟨z, rfl⟩ := e.symm.surjective j
      refine differentiableAt_dir Z.m0.toSABMap.cart.1 Z.m.cart.1 (LocLift.isHolTo_mono hyh hB' hsub')
        (ex := fun b u => (Fu.ex i (P₁ (φ b)) u).left) hex
        (fun b hb u => (Over.w (Fu.ex i (P₁ (φ b)) u)).trans (hu b hb)) hb (fun u h => ?_)
        (v := fun b => (a b).2.v z.1 z.2) (fun U f => (ha.2 z.1 z.2 U f).mono fun _ h => ⟨hsub' h.1, h.2⟩)
        fun b hb => hw b hb z
      have h0 : IsDerivAt (fun u => (Fu.ex i (P₁ (φ b)) u).left) 0 0 (constVec (Fu.ex i (P₁ (φ b)) 0).left) :=
        (isDerivAt_constVec_iff (c := fun u => (Fu.ex i (P₁ (φ b)) u).left)).2 fun _ _ _ => map_zero _
      exact ((Fu.ex_diff i _ (hP₁.1 _ hb)).2 (Over.homMk _ h.over) h.1).unique ((isDerivAt0_iff _ _ _).2 h)
        ((isDerivAt0_iff _ _ _).2 h0)
    have hMd : ∀ i j, DifferentiableAt ℂ (fun b => M b i j) b :=
      HolFrameMatrix.differentiableAt_of_mul_eq_one M (fun b => Matrix.of fun i j => w b j i) b
        (fun i j => differentiableAt_pi.1 (hwd j) i) (eventually_of_mem (hB'.mem_nhds hb) hM')
    have hPd : DifferentiableAt ℂ (fun b => P₁ (φ b) v) b :=
      ((hP₁.2 v).differentiableAt (hB₁.mem_nhds hb)).comp b φ.differentiableAt
    refine DifferentiableAt.differentiableWithinAt ?_
    show DifferentiableAt ℂ (fun b => ∑ j, M b (e.symm z) j * P₁ (φ b) v j) b
    exact DifferentiableAt.fun_sum fun j _ => (hMd _ j).mul (differentiableAt_pi.1 hPd j)

end GlobalTheory.ShFam.HorLift
