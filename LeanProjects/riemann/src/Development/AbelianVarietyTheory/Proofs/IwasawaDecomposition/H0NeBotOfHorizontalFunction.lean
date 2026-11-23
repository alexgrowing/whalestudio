import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsNonemptyDenseVarietyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRochNeBotOfHolomorphicSectionNeBotStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionOfLogGrowthStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
open Set GlobalTheory.CxPts GlobalTheory.Cartier.CartierDiv

namespace GlobalTheory.ShFam.Hor.Sec

section General

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ} {R : AnRead p σ d}
  {A : Set (CxPts p σ)}

theorem eqOn_of_dense (hA : Dense A) {T : Set (CxPts p σ)} (hT : IsOpen T) {f g : CxPts p σ → ℂ}
    (hf : R.HoloOn T f) (hg : R.HoloOn T g) (h : EqOn f g (T ∩ A)) : EqOn f g T :=
  h.of_subset_closure (hf.continuousOn hT) (hg.continuousOn hT) inter_subset_left (hA.open_subset_closure_inter hT)

theorem exists_holoOn_of_local (hA : Dense A) {S : Set (CxPts p σ)} {u : CxPts p σ → ℂ}
    (h : ∀ y ∈ S, ∃ (T : Set (CxPts p σ)) (f : CxPts p σ → ℂ), IsOpen T ∧ y ∈ T ∧ R.HoloOn T f ∧ EqOn f u (T ∩ A)) :
    ∃ f, R.HoloOn S f ∧ EqOn f u (S ∩ A) := by
  choose! T f hT hy hf he using h
  refine ⟨fun y => f y y, AnRead.holoOn_of_cover (T := fun y : S => T y) (fun y => hT y y.2)
    (fun y hS => ⟨⟨y, hS⟩, hy y hS⟩) fun y => ((hf y y.2).mono inter_subset_right).congr fun z hz => ?_,
    fun y hS => he y hS.1 ⟨hy y hS.1, hS.2⟩⟩
  exact eqOn_of_dense hA ((hT z hz.1).inter (hT y y.2)) ((hf z hz.1).mono inter_subset_left)
    ((hf y y.2).mono inter_subset_right)
    (fun w hw => (he z hz.1 ⟨hw.1.1, hw.2⟩).trans (he y y.2 ⟨hw.1.2, hw.2⟩).symm) ⟨hy z hz.1, hz.2⟩

theorem isHolTo_symm (c : AlgChart p σ d) {B : Set (ReciprocityTheory.L2DbarEstimates.V d)} (hB : IsOpen B) (h : B ⊆ c.e.target) :
    IsHolTo B fun b => (c.e.symm b).1 := fun U f => by
  refine ⟨?_, (c.holo U f).mono fun b hb => ⟨h hb.1, hb.2⟩⟩
  exact (c.e.continuousOn_symm.mono h).isOpen_inter_preimage hB (isOpen_ptsIn U)

variable [IsIntegral Y]

theorem ev_mul_eq {U V W : Y.Opens} {a : Γ(Y, U)} {b : Γ(Y, V)} {c : Γ(Y, W)} {y : CxPts p σ}
    (hU : y ∈ ptsIn p σ U) (hV : y ∈ ptsIn p σ V) (hW : y ∈ ptsIn p σ W)
    (h : ∀ h₁ h₂ h₃, fnOf U h₁ a * fnOf V h₂ b = fnOf W h₃ c) : ev p σ U a y * ev p σ V b y = ev p σ W c y := by
  have hy : y ∈ ptsIn p σ (U ⊓ V ⊓ W) := mem_ptsIn_inf.2 ⟨mem_ptsIn_inf.2 ⟨hU, hV⟩, hW⟩
  rw [← ev_res (inf_le_left.trans inf_le_left) hy, ← ev_res (inf_le_left.trans inf_le_right) hy,
    ← ev_res inf_le_right hy, ← ev_mul]
  congr 1
  exact fn_ext fun _ => by rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, h]

theorem holSec_ne_bot [Nonempty (CxPts p σ)] (hA : Dense A) (D : CartierDiv Y) (W : Y → Y.Opens)
    (δ : Y → Y.functionFieldˣ) (hW : ∀ y, y ∈ W y) (hδ : ∀ y, ∀ y' ∈ W y, D.IsEqn y' (δ y))
    (u : Y → CxPts p σ → ℂ) (hu : ∀ y, R.HoloOn (ptsIn p σ (W y)) (u y))
    (h0 : ∀ y, ∀ z ∈ ptsIn p σ (W y) ∩ A, u y z ≠ 0)
    (hc : ∀ y y' (r : Γ(Y, W y ⊓ W y')), (∀ h, fnOf _ h r = (δ y : Y.functionField) / (δ y' : Y.functionField)) →
      ∀ z ∈ ptsIn p σ (W y ⊓ W y') ∩ A, u y z = ev p σ _ r z * u y' z) :
    R.holSec (toLB D) ≠ ⊥ := by
  choose r hr using fun (i : (toLB D).ι) (y : Y) => exists_unit_fnOf_eq (U := (toLB D).U i ⊓ W y)
    (f := (i.1.2 : Y.functionField) / (δ y : Y.functionField))
    fun x hx => (hδ y x hx.2).iff_unitAt.1 (i.2.2 x hx.1)
  let pt (z : CxPts p σ) : Y := z.1 (IsLocalRing.closedPoint ℂ)
  have hpt (z : CxPts p σ) : z ∈ ptsIn p σ (W (pt z)) := mem_ptsIn.2 (hW _)
  let s (i : (toLB D).ι) (z : CxPts p σ) : ℂ := ev p σ _ (r i (pt z)).val z * u (pt z) z
  have key {i y z} (hi : z ∈ ptsIn p σ ((toLB D).U i)) (hy : z ∈ ptsIn p σ (W y)) :
      s i z = ev p σ _ (r i y).val z * u y z := by
    obtain ⟨t, ht⟩ := exists_unit_fnOf_eq (U := W (pt z) ⊓ W y)
      (f := (δ (pt z) : Y.functionField) / (δ y : Y.functionField))
      fun x hx => (hδ y x hx.2).iff_unitAt.1 (hδ _ x hx.1)
    have hz := mem_ptsIn_inf.2 ⟨hpt z, hy⟩
    have e : u (pt z) z = ev p σ _ t.val z * u y z :=
      eqOn_of_dense (R := R) hA (isOpen_ptsIn _) ((hu _).mono (ptsIn_mono inf_le_left))
        ((R.holoOn_ev _ t.val).mul ((hu y).mono (ptsIn_mono inf_le_right))) (hc _ _ _ ht) hz
    rw [← ev_mul_eq (a := (r i (pt z)).val) (b := t.val) (mem_ptsIn_inf.2 ⟨hi, hpt z⟩) hz (mem_ptsIn_inf.2 ⟨hi, hy⟩)
      fun _ _ _ => by rw [hr, hr, ht, div_mul_div_cancel₀ (Units.ne_zero _)], _root_.mul_assoc, ← e]
  have hs : s ∈ R.holSec (toLB D) := by
    refine ⟨⟨fun i j z hi hj => ?_, fun i z hi => ?_⟩, fun i => ?_⟩
    · have e := ev_mul_eq (a := ((toLB D).g i j).val) (b := (r j (pt z)).val) (c := (r i (pt z)).val)
        (mem_ptsIn_inf.2 ⟨hi, hj⟩) (mem_ptsIn_inf.2 ⟨hj, hpt z⟩) (mem_ptsIn_inf.2 ⟨hi, hpt z⟩)
        fun _ _ _ => by rw [hr, hr, fnOf_toLB_g, div_mul_div_cancel₀ (Units.ne_zero _)]
      simp only [s]
      rw [← e, _root_.mul_assoc]
      rfl
    · simp only [s]
      rw [ev_of_notMem (fun h => hi (mem_ptsIn_inf.1 h).1), zero_mul]
    · exact AnRead.holoOn_of_cover (T := fun y => ptsIn p σ (W y)) (fun y => isOpen_ptsIn _)
        (fun z _ => ⟨_, hpt z⟩) fun y =>
        ((AnRead.holoOn_ev_of_subset (r i y).val fun _ => mem_ptsIn_inf.2).mul
          ((hu y).mono inter_subset_right)).congr fun z hz => key hz.1 hz.2
  obtain ⟨z, hz⟩ := hA.nonempty
  intro hb
  rw [hb, Submodule.mem_bot] at hs
  let i : (toLB D).ι := ⟨(W (pt z), δ (pt z)), gen_mem (hW _), hδ _⟩
  exact mul_ne_zero (ev_ne_zero (mem_ptsIn_inf.2 ⟨hpt z, hpt z⟩) (r i (pt z)).isUnit) (h0 _ z ⟨hpt z, hz⟩)
    (congrFun (congrFun hs i) z)

end General

section Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ}

theorem logGrowth_inv {h : CxFr Z σ → ℂ} (hg : LogGrowth h) : LogGrowth fun a => (h a)⁻¹ := fun x₀ => by
  obtain ⟨N, φ, h₁, h₂, h₃, h₄, h₅⟩ := hg x₀
  refine ⟨N, φ, h₁, h₂, h₃, h₄, fun V _ _ _ B a hB ha hN b₀ hb => ?_⟩
  obtain ⟨C, k, hk⟩ := h₅ V B a hB ha hN b₀ hb
  exact ⟨C, k, hk.mono fun b hb hi => ⟨(hb hi).2, by rw [inv_inv]; exact (hb hi).1⟩⟩

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ' : k →+* ℂ} {d : ℕ}

theorem inner_iff {π : Y ⟶ gen Z} {z : CxPts p σ'} {x : CxPts (genStr Z) σ} (h : x.1 = z.1 ≫ π) :
    Inner x ↔ z ∈ ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl) := by
  rw [Inner, h, mem_ptsIn]
  rfl

theorem exists_extension (R : AnRead p σ' d) (π : Y ⟶ gen Z)
    (hA : Dense (ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl))) {S : Set (CxPts p σ')} (hS : IsOpen S)
    {a : CxPts p σ' → CxFr Z σ} (ha : ∀ z ∈ S, (a z).1.1 = z.1 ≫ π)
    (hf : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V)
      (x : V → CxPts p σ'), IsOpen B → IsHolTo B (fun b => (x b).1) → MapsTo x B S → HolFam B fun b => a (x b))
    {h : CxFr Z σ → ℂ}
    (hh : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V)
      (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, Inner (a b).1) → DifferentiableOn ℂ (fun b => h (a b)) B)
    (hg : LogGrowth h) :
    ∃ f, R.HoloOn S f ∧ EqOn f (fun z => h (a z)) (S ∩ ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl)) := by
  refine exists_holoOn_of_local hA fun y hy => ?_
  obtain ⟨N, φ, hN, hyN, hφ, hφ0, hgr⟩ := hg (a y).1
  obtain ⟨N', hN', rfl⟩ := isOpen_induced_iff.1 hN
  obtain ⟨i, hi⟩ := R.cover y
  set c := R.chart i
  let T : Set (CxPts p σ') := S ∩ (fun z => z.1 ≫ π) ⁻¹' N'
  have hT : IsOpen T := hS.inter (hN'.preimage ((Points.continuous_comp π).comp continuous_subtype_val))
  have hTN (z) (hz : z ∈ T) : (a z).1 ∈ Subtype.val ⁻¹' N' := by
    rw [mem_preimage, ha z hz.1]; exact hz.2
  have hyT : y ∈ T := ⟨hy, by rw [mem_preimage, ← ha y hy]; exact hyN⟩
  let B := c.e.target ∩ c.e.symm ⁻¹' T
  have hB : IsOpen B := ChartGlue.isOpen_over c.e hT
  have hfam {B' : Set (ReciprocityTheory.L2DbarEstimates.V d)} (hB' : IsOpen B') (e : B' ⊆ B) : HolFam B' fun b => a (c.e.symm b) :=
    hf _ B' c.e.symm hB' (isHolTo_symm c hB' (e.trans inter_subset_left)) fun b hb => (e hb).2.1
  have hφB : DifferentiableOn ℂ (fun b => φ (a (c.e.symm b)).1) B :=
    hφ _ B (fun b => (a (c.e.symm b)).1) hB (hfam hB subset_rfl).1 fun b hb => hTN _ hb.2
  have hin (z) (hz : z ∈ T) : φ (a z).1 ≠ 0 ↔ z ∈ ptsIn p σ' (π ⁻¹ᵁ (genBd Z).compl) :=
    (hφ0 _ (hTN z hz)).trans (inner_iff (ha z hz.1))
  have hB' : IsOpen {b ∈ B | φ (a (c.e.symm b)).1 ≠ 0} :=
    hφB.continuousOn.isOpen_inter_preimage hB isOpen_ne
  obtain ⟨u, hu, he⟩ := GlobalTheory.T.riemann_extension_of_log_growth _ B _ (fun b => h (a (c.e.symm b))) hB hφB
    (hh _ _ _ hB' (hfam hB' (sep_subset _ _)) fun b hb => (hφ0 _ (hTN _ hb.1.2)).1 hb.2)
    (fun b hb => by
      have hs := c.e.map_target hb.1
      have h₁ := hA.open_subset_closure_inter (c.e.open_source.inter hT) ⟨hs, hb.2⟩
      have h₂ := (c.e.continuousAt hs).continuousWithinAt.mem_closure_image h₁
      rw [c.e.right_inv hb.1] at h₂
      refine closure_mono ?_ h₂
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨ChartGlue.mem_over c.e hz.1.1 hz.1.2, ?_⟩
      rw [c.e.left_inv hz.1.1]
      exact (hin z hz.1.2).2 hz.2)
    fun b hb => by
      obtain ⟨C, n, hn⟩ := hgr _ B _ hB (hfam hB subset_rfl) (fun b hb => hTN _ hb.2) b hb
      refine ⟨C, n, ?_⟩
      filter_upwards [hn, hB.mem_nhds hb] with b' h₁ h₂ h₃
      exact (h₁ ((hφ0 _ (hTN _ h₂.2)).1 h₃)).1
  refine ⟨c.e.source ∩ T, u ∘ c.e, c.e.open_source.inter hT, ⟨hi, hyT⟩,
    AnRead.holoOn_of_chart c (hu.congr fun b hb => congrArg u (c.e.right_inv hb.1)), fun z hz => ?_⟩
  have := he (x := c.e z) ⟨ChartGlue.mem_over c.e hz.1.1 hz.1.2, by
    rw [c.e.left_inv hz.1.1]; exact (hin z hz.1.2).2 hz.2⟩
  simpa only [c.e.left_inv hz.1.1, Function.comp_apply] using this

end Flag

theorem H0_ne_bot_of_horFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (τ : E →+* ℂ) (h : CxFr Z σ → ℂ), τ (H.rt : E) = H.rt0 → HorFn τ h → (C.Y.H0 (divOf C (expo Dw (detSym Dw (fun _ => false) none τ))) ≠ ⊥ ∧ C.Y.H0 (-divOf C (expo Dw (detSym Dw (fun _ => false) none τ))) ≠ ⊥) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ F _ _ e C τ h hτ hh
  obtain ⟨W, δ, a, hW, hδ, ha, hf, hc⟩ := GlobalTheory.T.exists_local_equation_complex_points E H Dw l Xo c O β Z σ F e C τ hτ
  obtain ⟨hne, hd⟩ := GlobalTheory.T.complexPoints_nonempty_dense_variety F C.Y (σ.comp e.toRingHom)
  have hA := hd (C.π ⁻¹ᵁ (genBd Z).compl) ⟨genericPt C.Y (IsLocalRing.closedPoint C.Y.Fn), fun hb =>
    hb ⟨_, congrArg (fun g => g (IsLocalRing.closedPoint C.Y.Fn)) C.y0_x⟩⟩
  let R := AnRead.all C.Y.str (σ.comp e.toRingHom) C.Y.dim
  choose u hu he using fun y => exists_extension R C.π hA (isOpen_ptsIn (W y)) (ha y) (hf y) hh.2.2.1 hh.2.2.2
  choose u' hu' he' using fun y => exists_extension R C.π hA (isOpen_ptsIn (W y)) (ha y) (hf y)
    (h := fun a => (h a)⁻¹) (fun V _ _ _ B a hB ha hi => (hh.2.2.1 V B a hB ha hi).inv fun b hb => hh.1 _ (hi b hb))
    (logGrowth_inv hh.2.2.2)
  have h0 (y) (z) (hz : z ∈ ptsIn _ _ (W y) ∩ ptsIn _ _ (C.π ⁻¹ᵁ (genBd Z).compl)) : h (a y z) ≠ 0 :=
    hh.1 _ ((inner_iff (ha y z hz.1)).2 hz.2)
  have hr (y y') (U : C.Y.X.Opens) (r : Γ(C.Y.X, U)) (hr : ∀ hU, fnOf U hU r = (δ y : C.Y.Fn) / (δ y' : C.Y.Fn)) (z)
      (hy : z ∈ ptsIn _ _ (W y)) (hy' : z ∈ ptsIn _ _ (W y')) (hU : z ∈ ptsIn _ _ U)
      (hz : z ∈ ptsIn _ _ (C.π ⁻¹ᵁ (genBd Z).compl)) : h (a y z) = ev _ _ U r z * h (a y' z) := by
    obtain ⟨M, N, hM, hN, hM0, hMN⟩ := hc y y' U (gen_mem (mem_ptsIn.1 hU)) r (hr _) z
      (mem_ptsIn_inf.2 ⟨mem_ptsIn_inf.2 ⟨hy, hy'⟩, hU⟩)
    refine mul_right_cancel₀ hM0 ?_
    rw [hh.2.1 _ _ M N ((inner_iff (ha y' z hy')).2 hz) hM hN, ← hMN]
    ring
  refine ⟨GlobalTheory.T.H0_ne_bot_of_holSec_ne_bot F C.Y _ R _ (holSec_ne_bot hA _ W δ hW hδ u hu (fun y z hz => ?_) fun y y' r hr' z hz => ?_),
    GlobalTheory.T.H0_ne_bot_of_holSec_ne_bot F C.Y _ R _ (holSec_ne_bot hA _ W (fun y => (δ y)⁻¹) hW (fun y y' hy => (hδ y y' hy).neg) u' hu'
      (fun y z hz => ?_) fun y y' r hr' z hz => ?_)⟩
  · rw [he y hz]; exact h0 y z hz
  · have hz' := mem_ptsIn_inf.1 hz.1
    rw [he y ⟨hz'.1, hz.2⟩, he y' ⟨hz'.2, hz.2⟩]
    exact hr y y' _ r hr' z hz'.1 hz'.2 hz.1 hz.2
  · rw [he' y hz]; exact inv_ne_zero (h0 y z hz)
  · have hz' := mem_ptsIn_inf.1 hz.1
    have e := hr y' y _ r (fun hU => by
      rw [hr', Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, inv_div_inv]) z hz'.2 hz'.1 hz.1 hz.2
    rw [he' y ⟨hz'.1, hz.2⟩, he' y' ⟨hz'.2, hz.2⟩]
    have h₁ := h0 y' z ⟨hz'.2, hz.2⟩
    rw [eq_mul_inv_iff_mul_eq₀ h₁, e, _root_.mul_comm, mul_inv_cancel_right₀ (h0 y z ⟨hz'.1, hz.2⟩)]

end GlobalTheory.ShFam.Hor.Sec
