import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AutomorphicArithmetic.DivisorFrames.ExistsAdaptedFlagCharts
import Development.AutomorphicArithmetic.DivisorFrames.ChartFrameDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMax
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTangentOrigin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem lin_key {K : Type} [NormedField K] {m : ℕ} (σ : Fin m → Fin m) (hσ : Function.Surjective σ)
    {R : Matrix (Fin m) (Fin m) K} (hR : IsTri (R.submatrix σ id)) (hd : ∀ a, R (σ a) a ≠ 0) (b : Fin m) :
    IsLeast {r : ℝ | ∃ cf : Fin m → K, cf b ≠ 0 ∧ (∀ k, b < k → cf k = 0) ∧ (∀ j, ‖(R *ᵥ cf) j‖ ≤ 1) ∧ r = ‖cf b‖⁻¹}
      ‖R (σ b) b‖ := by
  have hA : (R.submatrix σ id).BlockTriangular id := fun a i h => hR a i h
  have e (cf : Fin m → K) (j) : (R.submatrix σ id *ᵥ cf) j = (R *ᵥ cf) (σ j) := rfl
  have hdet : IsUnit (R.submatrix σ id).det := by
    rw [det_of_upperTriangular hA]
    exact (Finset.prod_ne_zero_iff.2 fun k _ => hd k).isUnit
  have := invertibleOfIsUnitDet _ hdet
  constructor
  · obtain ⟨e1, -⟩ := Guard.tri_mulVec (blockTriangular_inv_of_blockTriangular hA) (i := b) (cf := Pi.single b 1)
      (fun k hk => Pi.single_eq_of_ne hk.ne' _)
    have e3 : R.submatrix σ id *ᵥ ((R.submatrix σ id)⁻¹ *ᵥ Pi.single b 1) = Pi.single b 1 := by
      rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    have e2 := (Guard.tri_mulVec hA e1).2
    rw [e3, Pi.single_eq_same] at e2
    refine ⟨_, right_ne_zero_of_mul_eq_one e2.symm, e1, fun j => ?_, ?_⟩
    · obtain ⟨j, rfl⟩ := hσ j
      rw [← e, e3]
      by_cases h : j = b
      · subst h; simp
      · simp [h]
    · rw [← norm_inv, ← eq_inv_of_mul_eq_one_left e2.symm]; rfl
  · rintro _ ⟨cf, h0, h1, h2, rfl⟩
    have h3 := h2 (σ b)
    rw [← e, (Guard.tri_mulVec hA h1).2, norm_mul] at h3
    rw [← one_div, le_div_iff₀ (norm_pos_iff.2 h0)]
    exact h3

private theorem lin_lie {K : Type} [Field K] {m : ℕ} (dual : Bool) {Q : Matrix (Fin m) (Fin m) K} (hQ : IsUnit Q.det)
    (h : IsTri ((lieMat dual Q).submatrix (pos dual) id)) (hd : ∀ a, lieMat dual Q (pos dual a) a ≠ 0) :
    IsTri (Q⁻¹.submatrix (pos dual) id) ∧ ∀ a,
      Q⁻¹ a (pos dual a) ^ (cond dual (-1) 1 : ℤ) * lieMat dual Q (pos dual a) a = 1 := by
  cases dual
  · have := invertibleOfIsUnitDet _ hQ
    have hA : Q.BlockTriangular id := fun a i hi => h a i hi
    have hB := blockTriangular_inv_of_blockTriangular hA
    refine ⟨fun a i hi => hB hi, fun a => ?_⟩
    have h1 := (Guard.tri_mulVec hB (i := a) (cf := fun k => Q k a) (fun k hk => hA hk)).2
    have h2 : (Q⁻¹ *ᵥ fun k => Q k a) a = (Q⁻¹ * Q) a a := rfl
    rw [h2, nonsing_inv_mul _ hQ, one_apply_eq] at h1
    simpa [pos, lieMat] using h1.symm
  · refine ⟨fun a i hi => ?_, fun a => ?_⟩
    · have := h i.rev a.rev (Fin.rev_lt_rev.2 hi)
      simpa [pos, lieMat] using this
    · have := hd a
      simp only [pos, lieMat, cond_true, transpose_apply] at this ⊢
      rw [_root_.zpow_neg_one, inv_mul_cancel₀ this]

private theorem gr_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} {t : SAB H X} {K : Type} [NontriviallyNormedField K] {x : Sp K ⟶ X}
    {Λ : Set (Sp (DualNumber K) ⟶ t.G.left)} {m : ℕ} {u u' : Fin m → (Sp (DualNumber K) ⟶ t.G.left)}
    (hu : ∀ k, IsTanAtG t x (u k)) (hu' : ∀ k, IsTanAtG t x (u' k))
    (hΛ : ∀ a w, IsCombAtG t x u' a w → (w ∈ Λ ↔ ∀ i, ‖a i‖ ≤ 1))
    (σ : Fin m → Fin m) (hσ : Function.Surjective σ)
    {R : Matrix (Fin m) (Fin m) K} (h : ∀ i, IsCombAtG t x u' (fun j => R j i) (u i))
    (hR : IsTri (R.submatrix σ id)) (hd : ∀ a, R (σ a) a ≠ 0) (b : Fin m) :
    grNorm t x Λ u b = ‖R (σ b) b‖ := by
  rw [← (lin_key σ hσ hR hd b).csInf_eq, grNorm]
  congr 1
  ext r
  refine exists_congr fun cf => and_congr_right fun _ => and_congr_right fun _ => and_congr_left fun _ => ?_
  constructor
  · rintro ⟨w, hw, hc⟩
    exact (hΛ _ w (tanLinG u' hu' u R cf w h hc)).1 hw
  · intro hc
    obtain ⟨w, -, hw⟩ := Guard.exists_comb hu cf
    exact ⟨w, (hΛ _ w (tanLinG u' hu' u R cf w h hw)).2 hc, hw⟩

private theorem w_div_le {F : Type} [Field F] [NumberField F] {Y : Var F} (N : GlobalTheory.TrueGeo.Model Y) {L : LB N.X}
    {s : (L.pull N.j).ι → Y.Fnˣ} (hs : Cartier.IsRatSec (L.pull N.j) s) {v : HeightOneSpectrum (𝓞 F)} {ε : Ext v}
    {y : AlgPt Y} {yt : Sp ε.O ⟶ N.X} (hy : spMap ε.O.subtype ≫ yt = y.1 ≫ N.j) (k k' : (L.pull N.j).ι)
    (h : ⊤ ≤ yt ⁻¹ᵁ L.U (k PUnit.unit)) (h' : ⊤ ≤ yt ⁻¹ᵁ L.U (k' PUnit.unit)) :
    RegAt (below y.1) ((s k : Y.Fn) / s k') ∧ ε.w (valAt y.1 ((s k : Y.Fn) / s k')) ≤ 1 := by
  have hW : ⊤ ≤ yt ⁻¹ᵁ (L.U (k PUnit.unit) ⊓ L.U (k' PUnit.unit)) := le_inf_pre h h'
  have hb := Glue.below_mem N hy hW
  have hb' : below y.1 ∈ (L.pull N.j).U k ⊓ (L.pull N.j).U k' :=
    ⟨Set.mem_iInter.2 fun _ => hb.1, Set.mem_iInter.2 fun _ => hb.2⟩
  have l : (L.pull N.j).U k ⊓ (L.pull N.j).U k' ≤ N.j ⁻¹ᵁ (L.U (k PUnit.unit) ⊓ L.U (k' PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have hp : ((L.pull N.j).g k k').val =
      resG Y.X l (N.j.app _ (L.g (k PUnit.unit) (k' PUnit.unit)).val) := by
    have : (L.pull N.j).g k k' = res l (pullU N.j _ (L.g (k PUnit.unit) (k' PUnit.unit))) := by
      change ∏ _k : PUnit, _ = _
      exact (Fintype.prod_unique _).trans (zpow_one _)
    rw [this]
    rfl
  have e := hs k k' (gen_mem hb')
  rw [hp, fnOf_resG] at e
  rw [e, mul_div_cancel_right₀ _ (s k').ne_zero]
  exact ⟨regAt_fnOf (U := N.j ⁻¹ᵁ (L.U (k PUnit.unit) ⊓ L.U (k' PUnit.unit))) hb _ _, Glue.w_le_one N hy hW _ _⟩

private theorem w_div_eq {F : Type} [Field F] [NumberField F] {Y : Var F} (N : GlobalTheory.TrueGeo.Model Y) {L : LB N.X}
    {s : (L.pull N.j).ι → Y.Fnˣ} (hs : Cartier.IsRatSec (L.pull N.j) s) {v : HeightOneSpectrum (𝓞 F)} {ε : Ext v}
    {y : AlgPt Y} {yt : Sp ε.O ⟶ N.X} (hy : spMap ε.O.subtype ≫ yt = y.1 ≫ N.j) (k k' : (L.pull N.j).ι)
    (h : ⊤ ≤ yt ⁻¹ᵁ L.U (k PUnit.unit)) (h' : ⊤ ≤ yt ⁻¹ᵁ L.U (k' PUnit.unit)) :
    RegAt (below y.1) ((s k : Y.Fn) / s k') ∧ ε.w (valAt y.1 ((s k : Y.Fn) / s k')) = 1 := by
  obtain ⟨a, a'⟩ := w_div_le N hs hy k k' h h'
  obtain ⟨b, b'⟩ := w_div_le N hs hy k' k h' h
  refine ⟨a, le_antisymm a' ?_⟩
  have e := CutModel.valAt_mul y.1 a b
  rw [div_mul_div_cancel₀ (s k').ne_zero, div_self (s k).ne_zero,
    ← map_one (algebraMap (Y.X.presheaf.stalk (below y.1)) Y.X.functionField), CutModel.valAt_algebraMap, map_one] at e
  have e' := congrArg ε.w e
  rw [map_one, map_mul] at e'
  rw [e']
  exact mul_le_of_le_one_right (ε.w.nonneg _) b'

private theorem step_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {X : Scheme.{0}} (t : SAB H X) {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]
    (x : Sp K ⟶ X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber K) ⟶ t.G.left)) (p : ℕ) {b : Bool}
    (hb : b = false) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    lnStep t x u p b (Sum.inl (τ, (i : ℕ))) = Real.log (grNorm t x (latDR t x) (u τ) i) := by
  subst hb
  simp [lnStep, lat]

private theorem core :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (N : GlobalTheory.TrueGeo.Model C.Y) (τ : E →+* ℂ) (M : N.X.Modules) (dual : Bool) (A : Chart M (Dw.mult τ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) C.Y.Fn) (fl : Vert.Flag M (Dw.mult τ)) (i : Fin (Dw.mult τ)) (s : ((fl.root i).pull N.j).ι → C.Y.Fnˣ) (kind : ℕ → Bool) (Ro : Option ℝ) (w : Pad.Sym E →₀ ℤ), w = Finsupp.single (kind, Ro, Sum.inl (τ, (pos dual i : ℕ))) (cond dual (-1) 1) → IsLie C.f0 τ N.j dual A → IsFlag (genericPt C.Y ≫ N.j) dual A fl → IsGrSec N.j dual A fl i s → IsLat C.f0 τ N.j dual A → (∀ p, kind p = false) → ∀ (v : HeightOneSpectrum (𝓞 F)) [Fact (resP v).Prime] (ε : Ext v) (y : AlgPt C.Y) (yt : Sp ε.O ⟶ N.X) (k : ((fl.root i).pull N.j).ι), spMap ε.O.subtype ≫ yt = y.1 ≫ N.j → ⊤ ≤ yt ⁻¹ᵁ (fl.root i).U (k PUnit.unit) →
      ∀ (φ : c.F →+* C.Y.X.presheaf.stalk (below y.1)) (f : StalkFrame C.π (below y.1) φ)
      (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ)
      (ψ : C.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v]), ψ = valP ε y → f.Tri (toFn (below y.1)) C.f0 t →
      (∀ τ i, (C.gr τ i).IsEqn (below y.1) (t τ i)) →
      Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w x) *
        (eqn (divOf C (expo Dw w)) (below y.1))⁻¹ : C.Y.Fnˣ) : C.Y.Fn))) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        (w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap ψ ≫ stalkPt C.Y (below y.1) ≫ C.π ≫ genι Z)
          (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) (a.1 (resP v)) a.2.2) =
      Real.log (ε.w (valAt y.1 (((eqn (divOf C (expo Dw w)) (below y.1))⁻¹ * s k : C.Y.Fnˣ) : C.Y.Fn))) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e C N τ M dual A fl i s kind Ro w hw hL hF hS hLat hk v _ ε y yt k hy hU
  classical
  obtain ⟨hp, -, hlog⟩ := ioOf_spec F v ε
  obtain ⟨ch, hx, hch⟩ := (UpperTheory.exists_adapted_flag_charts N.X M _ fl).1 (yt (IsLocalRing.closedPoint ε.O))
  have hc : ⊤ ≤ yt ⁻¹ᵁ ch.U := (Scheme.preimage_eq_top_of_closedPoint_mem yt hx).ge
  have hb := Glue.below_mem N hy hc
  obtain ⟨t0, ht0⟩ := hch i
  have hfr := (UpperTheory.exists_adapted_flag_charts N.X M _ fl).2 ch hch i t0 ht0
  have hs := hS.2 ch hch (gen_le N.j hb) t0 ht0 hfr
  obtain ⟨a1, a2⟩ := w_div_eq N hS.1 hy k (fun _ => (⟨ch.U, _, hfr⟩ : Chart (fl.gr i) 1)) hU hc
  generalize s (fun _ => (⟨ch.U, _, hfr⟩ : Chart (fl.gr i) 1)) = sg at hs a1 a2
  obtain ⟨φ', f', hf'⟩ := hL.2 ch _ hb
  have hn : (cond dual (-1) 1 : ℤ) ≠ 0 := by cases dual <;> simp
  have hexp : expo Dw w = Pi.single (⟨τ, pos dual i⟩ : Letter Dw) (cond dual (-1) 1) := by
    funext x
    rw [hw, expo, Finsupp.sum_single_index (by simp)]
    simp [letterOf, Pi.single_apply, eq_comm]
  intro φ f t ψ hψ hT hE
  have hsum : (w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap ψ ≫ stalkPt C.Y (below y.1) ≫ C.π ≫ genι Z)
      (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) (a.1 (resP v)) a.2.2) = ((cond dual (-1) 1 : ℤ) : ℝ) *
      Real.log (grNorm Z.t (spMap ψ ≫ stalkPt C.Y (below y.1) ≫ C.π ≫ genι Z)
        (latDR Z.t (spMap ψ ≫ stalkPt C.Y (below y.1) ≫ C.π ≫ genι Z))
        (fun j => spMap (dualMap ψ) ≫ f.v τ j) (pos dual i)) := by
    rw [hw]
    exact (Finsupp.sum_single_index (by simp)).trans (congrArg _ (step_eq _ _ _ _ (hk _) τ (pos dual i)))
  rw [hsum]
  subst hψ
  obtain rfl : φ' = φ :=
    RingHom.ext fun a => toFn_injective _ ((RingHom.congr_fun hf'.1 a).symm.trans (RingHom.congr_fun hT.2.1 a))
  obtain ⟨h1, h2⟩ := UpperTheory.chart_frame_divisor E H Dw l Xo c O β Z F e C τ N.X N.j M dual A fl hL hF ch hch _ hb φ' f f' t hT hf'
  have hQ := f.isUnit_det_co f' τ
  have hQ' : IsUnit ((f.co f' τ).map (valP ε y)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hQ.map _
  have hm := lieMat_map dual (valP ε y) hQ
  have hne : ∀ a, valP ε y (lieMat dual (f.co f' τ) (pos dual a) a) ≠ 0 := fun a => ((h2 a).1.map _).ne_zero
  obtain ⟨h3, h4⟩ := lin_lie dual hQ' (fun a j h => by
    rw [hm]; exact (congrArg (valP ε y) (h1 a j h)).trans (map_zero _)) (fun a => by rw [hm]; exact hne a)
  have hR : ((f.co f' τ).map (valP ε y))⁻¹ = (f'.co f τ).map (valP ε y) := inv_eq_left_inv (by
    rw [← Matrix.map_mul, EigFrame.co_mul, EigFrame.co_self, Matrix.map_one _ (map_zero _) (map_one _)])
  have h5 := gr_eq (fun j => FactorDepth.isTanAtG_map Z.t (valP ε y) (f.tan τ j))
    (fun j => FactorDepth.isTanAtG_map Z.t (valP ε y) (f'.tan τ j))
    (hLat ch v ε y yt hy hc φ' f' hf') (pos dual) (fun a => ⟨_, pos_pos dual a⟩)
    (R := ((f.co f' τ).map (valP ε y))⁻¹)
    (fun j => by rw [hR]; exact LatDRFree.comb_map Z.t (valP ε y) (f'.co_spec f τ j)) h3
    (fun a h0 => by
      have := h4 (pos dual a)
      rw [pos_pos, h0, _root_.zero_zpow _ hn, zero_mul] at this
      exact zero_ne_one this) (pos dual i)
  have h6 := congrArg (fun z => Real.log ‖z‖) (h4 i)
  have h7 := left_ne_zero_of_mul_eq_one (h4 i)
  rw [hm, map_apply] at h6
  simp only [norm_mul, norm_one, Real.log_one] at h6
  rw [Real.log_mul (norm_ne_zero_iff.2 h7) (norm_ne_zero_iff.2 (hne i)), norm_zpow, Real.log_zpow] at h6
  rw [h5, pos_pos, eq_neg_of_add_eq_zero_left h6]
  have hP : (∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w x) = t τ (pos dual i) ^ (cond dual (-1) 1 : ℤ) := by
    rw [hexp, Finset.prod_eq_single ⟨τ, pos dual i⟩ (fun b _ hb => by simp [hb]) (by simp), Pi.single_eq_same]
  have hD : divOf C (expo Dw w) = (cond dual (-1) 1 : ℤ) • C.gr τ (pos dual i) := by
    rw [hexp, divOf, Finset.sum_eq_single ⟨τ, pos dual i⟩ (fun b _ hb => by simp [hb]) (by simp), Pi.single_eq_same]
  have hg : (divOf C (expo Dw w)).IsEqn (below y.1) (eqn (divOf C (expo Dw w)) (below y.1)) :=
    (CartierDiv.exists_isEqn _ _).choose_spec
  have hu := hg.iff_unitAt.1 (hD ▸ (hE τ (pos dual i)).zsmul _)
  obtain ⟨⟨V, hV⟩, h8⟩ := h2 i
  rw [hP]
  generalize t τ (pos dual i) ^ (cond dual (-1) 1 : ℤ) = T at h8 hu ⊢
  generalize eqn (divOf C (expo Dw w)) (below y.1) = g at hu ⊢
  rw [← hV] at h8 ⊢
  have hV0 : toFn (below y.1) (V : C.Y.X.presheaf.stalk (below y.1)) * toFn (below y.1) (V⁻¹ : _ˣ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have e1 : ((g⁻¹ * s k : C.Y.Fnˣ) : C.Y.Fn) = (T : C.Y.Fn) / g * ((s k : C.Y.Fn) / sg * toFn (below y.1) (V⁻¹ : _ˣ)) := by
    have : (sg : C.Y.Fn) = T * toFn (below y.1) (V⁻¹ : _ˣ) := by
      linear_combination (-(sg : C.Y.Fn)) * hV0 - sg * toFn (below y.1) (V⁻¹ : _ˣ) * h8 + T * toFn (below y.1) (V⁻¹ : _ˣ) * hs
    have h9 := sg.ne_zero
    rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_left_comm, div_mul_eq_mul_div (T : C.Y.Fn), ← this]
    field_simp
  have r1 : RegAt (below y.1) (toFn (below y.1) (V⁻¹ : _ˣ)) := ⟨_, rfl⟩
  have n1 : valAt y.1 ((T : C.Y.Fn) / g) ≠ 0 := fun h => (CutModel.valAt_eq_zero_iff y.1 hu.regAt).1 h hu
  have n2 : (Scheme.stalkClosedPointTo y.1).hom (V⁻¹ : _ˣ) = ((Scheme.stalkClosedPointTo y.1).hom V)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  have n3 : (Scheme.stalkClosedPointTo y.1).hom V ≠ 0 := (V.isUnit.map _).ne_zero
  rw [e1, CutModel.valAt_mul y.1 hu.regAt (a1.mul r1), CutModel.valAt_mul y.1 a1 r1, CutModel.valAt_algebraMap, n2,
    map_mul, map_mul, a2, one_mul, Real.log_mul (ε.w.ne_zero n1) (ε.w.ne_zero (inv_ne_zero n3)), map_inv₀,
    Real.log_inv, hlog ((Scheme.stalkClosedPointTo y.1).hom V), Units.val_mul, Units.val_inv_eq_inv_val,
    ← div_eq_mul_inv, mul_neg]
  rfl

theorem UpperTheory.true_model_chart_divisor_alt :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (N : GlobalTheory.TrueGeo.Model C.Y) (τ : E →+* ℂ) (M : N.X.Modules) (dual : Bool) (A : Chart M (Dw.mult τ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) C.Y.Fn) (fl : Vert.Flag M (Dw.mult τ)) (i : Fin (Dw.mult τ)) (s : ((fl.root i).pull N.j).ι → C.Y.Fnˣ) (kind : ℕ → Bool) (Ro : Option ℝ) (w : Pad.Sym E →₀ ℤ), w = Finsupp.single (kind, Ro, Sum.inl (τ, (pos dual i : ℕ))) (cond dual (-1) 1) → IsLie C.f0 τ N.j dual A → IsFlag (genericPt C.Y ≫ N.j) dual A fl → IsGrSec N.j dual A fl i s → IsLat C.f0 τ N.j dual A → (∀ p, kind p = false) → ∀ (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt C.Y) (yt : Sp ε.O ⟶ N.X) (k : ((fl.root i).pull N.j).ι), spMap ε.O.subtype ≫ yt = y.1 ≫ N.j → ⊤ ≤ yt ⁻¹ᵁ (fl.root i).U (k PUnit.unit) → lgOf C w v ε y = Real.log (ε.w (valAt y.1 (((eqn (divOf C (expo Dw w)) (below y.1))⁻¹ * s k : C.Y.Fnˣ) : C.Y.Fn))) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e C N τ M dual A fl i s kind Ro w hw hL hF hS hLat hk v ε y yt k hy hU
  have spec := (C.gr_spec (below y.1)).choose_spec.choose_spec.choose_spec
  exact (dif_pos (residueCharacteristic_prime v)).trans (@core E _ _ _ H Dw l Xo c O _ β Z F _ _ e C N τ M dual A fl i s kind Ro w hw hL hF
    hS hLat hk v (_) ε y yt k hy hU _ _ _ _ rfl spec.1 spec.2)
