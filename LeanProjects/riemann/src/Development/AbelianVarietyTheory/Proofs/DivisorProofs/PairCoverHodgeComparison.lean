import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticBundleGenericFibreData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRootTransitionFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedSectionLiftsLocally
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRootDivisorRelation
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairCovRat

open GlobalTheory.FlagCovDivCore

theorem isUnit_diag_block {R : Type} [CommRing R] {n : ℕ} {S : Matrix (Fin n) (Fin n) R} (hS : IsUnit S.det) (i : Fin n)
    (h1 : ∀ a k, k < i → i ≤ a → S a k = 0) (h2 : ∀ a, i < a → S a i = 0) : IsUnit (S i i) := by
  let b : Fin n → ℕ := fun a => if a < i then 0 else if a = i then 1 else 2
  have hb : S.BlockTriangular b := fun a k hak => by
    simp only [b] at hak
    by_cases hk : k < i
    · exact h1 a k hk (not_lt.1 fun ha => by simp [ha] at hak)
    · by_cases hki : k = i
      · subst hki
        refine h2 a (lt_of_le_of_ne (not_lt.1 fun ha => by simp [ha] at hak) fun ha => by simp [← ha] at hak)
      · exfalso
        simp only [hk, hki, if_false] at hak
        split_ifs at hak <;> omega
  have := Matrix.invertibleOfIsUnitDet S hS
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hb
  have e := congrFun (congrFun (Matrix.mul_nonsing_inv S hS) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at e
  · exact IsUnit.of_mul_eq_one _ e
  · intro a _ ha
    rcases ha.lt_or_gt with h | h
    · rw [h1 i a h le_rfl, zero_mul]
    · rw [hi (by simp [b, h.not_gt, h.ne']), mul_zero]
  · simp

theorem exists_app_ι_eq {X : Scheme.{0}} {M : X.Modules} {N : ℕ} (fl : Vert.Flag M N) {W : X.Opens} (k : Fin (N + 1))
    (s : Γ(fl.F k, W)) (l : Fin (N + 1)) : k ≤ l → ∃ s' : Γ(fl.F l, W), (fl.ι l).app W s' = (fl.ι k).app W s := by
  induction l using Fin.induction with
  | zero =>
    intro h
    obtain rfl : k = 0 := le_antisymm h (Fin.zero_le _)
    exact ⟨s, rfl⟩
  | succ l ih =>
    intro h
    rcases h.eq_or_lt with rfl | h
    · exact ⟨s, rfl⟩
    · obtain ⟨s', hs'⟩ := ih (Fin.le_castSucc_iff.2 h)
      refine ⟨(fl.step l).app W s', Eq.trans ?_ hs'⟩
      rw [← fl.step_ι l]
      rfl

theorem exists_ker {X : Scheme.{0}} {M : X.Modules} {N : ℕ} (fl : Vert.Flag M N) {W : X.Opens} {k i : Fin N} (h : k < i)
    (s : Γ(fl.F k.succ, W)) : ∃ s' : Γ(fl.F i.succ, W), (fl.π i).app W s' = 0 ∧
      (fl.ι i.succ).app W s' = (fl.ι k.succ).app W s := by
  obtain ⟨s', hs'⟩ := exists_app_ι_eq fl k.succ s i.castSucc (Fin.succ_le_castSucc_iff.2 h)
  refine ⟨(fl.step i).app W s', ?_, Eq.trans ?_ hs'⟩
  · have : fl.step i ≫ fl.π i = 0 := Limits.cokernel.condition _
    change (fl.step i ≫ fl.π i).app W s' = 0
    rw [this]
    rfl
  · rw [← fl.step_ι i]
    rfl

section Free

open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

theorem exists_coord_form {K : Type} [CommRing K] {χ : c.F →+* K} {x : Sp K ⟶ Z.X} (g : EigFrame Z χ x)
    (τ : E →+* ℂ) {m : ℕ} {uu : Fin m → (Sp (DualNumber K) ⟶ Z.t.G.left)} (hu : ∀ b, IsEigTan Z χ x τ (uu b))
    (k : Fin (Dw.mult τ)) : ∃ d : Fin m → K, ∀ (a : Fin m → K) (w : Sp (DualNumber K) ⟶ Z.t.G.left)
      (cf : Fin (Dw.mult τ) → K), IsCombAtG Z.t x uu a w → IsCombAtG Z.t x (g.v τ) cf w → cf k = ∑ b, a b * d b := by
  choose T hT using fun b => (g.basis τ _ (hu b).1 (hu b).2).exists
  refine ⟨fun b => T b k, fun a w cf h1 h2 => ?_⟩
  let U : Fin m → TanM x Z.t.G := fun b => tanOf (hu b).1
  have e1 : ∀ b, U b = ∑ j, T b j • g.vec τ j := fun b => (isComb_iff (g.vec τ) _ (U b)).1 (hT b)
  have h3 : IsCombAtG Z.t x uu a (tv (∑ b, a b • U b)).left := (isComb_iff U a _).2 rfl
  rw [comb_unique h1 h3] at h2
  have e2 := (isComb_iff (g.vec τ) cf _).1 h2
  have e3 : ∑ j, cf j • g.vec τ j = ∑ j, (∑ b, a b * T b j) • g.vec τ j := by
    rw [← e2]
    simp only [e1, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  exact Fintype.linearIndependent_iffₛ.1 (g.linearIndependent_vec τ) _ _ e3 k

theorem genericPt_π_genStr {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) :
    genericPt C.Y ≫ C.π ≫ genStr Z = spMap (constF e C.Y) := by
  letI := (constF e C.Y).toAlgebra
  rw [← Category.assoc, ← C.y0_x, Category.assoc, genStr, Z.jQ_over]
  exact GlobalTheory.ShFam.ptF_snd _

theorem unit_of_block {R K : Type} [CommRing R] [Field K] {ψ : R →+* K} (hψ : Function.Injective ψ) {φ : c.F →+* R}
    {x : Sp R ⟶ Z.X} {φ' : c.F →+* K} {x' : Sp K ⟶ Z.X} {f : EigFrame Z φ x} {v : EigFrame Z φ' x'}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ} (hf : f.Tri ψ v t) {τ : E →+* ℂ}
    {u : Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Z.t.G.left)} (hu : IsEigBasis Z φ x τ u)
    {A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R} (hA : IsUnit A.det) (ρ : Kˣ) (i : Fin (Dw.mult τ))
    (h : ∀ a : Fin (Dw.mult τ) → R, (a = 0 ∨ ∃ k < i, a = fun b => A b k) →
      ∃ (w : Sp (DualNumber K) ⟶ Z.t.G.left) (cf : Fin (Dw.mult τ) → K),
      IsCombAtG Z.t x' (fun b => spMap (dualMap ψ) ≫ u b) (fun b => ψ (A b i + a b)) w ∧
        IsCombAtG Z.t x' (v.v τ) cf w ∧ cf i = (ρ⁻¹ : Kˣ) ∧ ∀ k, i < k → cf k = 0) :
    ∃ a : R, IsUnit a ∧ ψ a = t τ i * (ρ⁻¹ : Kˣ) := by
  obtain ⟨g, rfl⟩ := exists_frame_of_basis f hu
  obtain ⟨f', hf'⟩ := f.exists_isMap ψ hf.2.1 hf.1
  obtain ⟨g', hg'⟩ := g.exists_isMap ψ hf.2.1 hf.1
  obtain ⟨T1, T2⟩ := hf.co τ hf'
  have key (a : Fin (Dw.mult τ) → R) (ha : a = 0 ∨ ∃ k < i, a = fun b => A b k) (b : Fin (Dw.mult τ)) (hb : i ≤ b) :
      ψ ((f.co g τ * A) b i + (f.co g τ).mulVec a b) = if b = i then (t τ i * (ρ⁻¹ : Kˣ) : K) else 0 := by
    obtain ⟨w, cf, h1, h2, h3, h4⟩ := h a ha
    rw [← funext (hg' τ)] at h1
    have e := congrFun (co_mulVec f' g' v τ h1 h2) b
    rw [hf'.co τ hg' hf.1] at e
    have e' : ψ ((f.co g τ * A) b i + (f.co g τ).mulVec a b) = (f'.co v τ).mulVec cf b := by
      rw [← e]
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
    rw [e', Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
    · split_ifs with hbi
      · rw [hbi, T2, h3]
      · rw [T1 b i (lt_of_le_of_ne hb (Ne.symm hbi)), zero_mul]
    · intro k _ hk
      rcases hk.lt_or_gt with h | h
      · rw [T1 b k (h.trans_le hb), zero_mul]
      · rw [h4 k h, mul_zero]
    · simp
  have k0 (b) (hb : i ≤ b) := key 0 (Or.inl rfl) b hb
  simp only [Matrix.mulVec_zero, Pi.zero_apply, add_zero] at k0
  refine ⟨_, isUnit_diag_block (S := f.co g τ * A) (by rw [Matrix.det_mul]; exact (f.isUnit_det_co g τ).mul hA) i
    (fun a k hk ha => ?_) fun a ha => hψ ?_, by rw [k0 i le_rfl, if_pos rfl]⟩
  · have := hψ ((key _ (Or.inr ⟨k, hk, rfl⟩) a ha).trans (k0 a ha).symm)
    exact add_eq_left.1 this
  · rw [k0 a ha.le, if_neg ha.ne', map_zero]

end Free

theorem top_le_genPt {G Y : Scheme.{0}} [IsIntegral G] (j : G ⟶ Y) {W : Y.Opens} (h : j (genericPoint G) ∈ W) :
    ⊤ ≤ (genPt G ≫ j) ⁻¹ᵁ W := by
  intro p _
  have h1 : genPt G p ⤳ genericPoint G := by
    have : genPt G p ∈ Set.range (G.fromSpecStalk (genericPoint G)) := ⟨p, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have h2 : genPt G p ∈ j ⁻¹ᵁ W := h1.mem_open (j ⁻¹ᵁ W).isOpen h
  simpa using h2

theorem isRatSec_frameSec (D : D7) (O : Setup D) (c : O.s.Comp) {Bs : Scheme.{0}} {Bg : Scheme.{0}} (jB : Bg ⟶ Bs)
    (πB : Bg ⟶ gen O.s.T.Z) {Y X Gs : Scheme.{0}} [IsIntegral Gs] (π : Y ⟶ Bs) (ρ : X ⟶ Y) (j : Gs ⟶ X)
    (πG : Gs ⟶ (O.var c).X) (φ : (O.var c).Fn →+* Gs.functionField) (jG : Gs ⟶ Bg)
    (φs : Gs.fromSpecStalk (genericPoint Gs) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X))
    (c1 : jG ≫ jB = j ≫ ρ ≫ π) (c2 : jG ≫ πB = πG ≫ (O.Φ.C c).π)
    (σ : D.host.E →+* ℂ) {M : Bs.Modules} (hM : IsVB M (O.S.Dw.mult σ))
    (u : FrAssign O.s.T.Z M (O.S.Dw.mult σ) jB) (frB : IsLieFrames O.s.T.Z O.κ.e jB πB M _ σ false u)
    (F : Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj M)) (O.S.Dw.mult σ))
    (i : Fin (O.S.Dw.mult σ)) (r : ((F.root i).pull j).ι → Gs.functionFieldˣ)
    (c3 : GlobalTheory.PairCov.IsFrameSecX (O := O) (c := c) σ hM jB πB u π ρ F j φ jG i r) :
    IsRatSec ((F.root i).pull j) r := by
  refine GlobalTheory.FlagCov.isRatSec_pull_root_of_scaling j F i r fun ch ch' hη => ?_
  haveI := hM.isQuasicoherent
  haveI := (hM.pullback π).isQuasicoherent
  obtain ⟨V, f, hV, hf⟩ := hM (π (ρ (j (genericPoint Gs))))
  have m1 : j (genericPoint Gs) ∈ (ch PUnit.unit).U :=
    LB.wchart_le (F.root i) (fun _ : PUnit.{1} => j) ch PUnit.unit hη.1
  have m2 : j (genericPoint Gs) ∈ (ch' PUnit.unit).U :=
    LB.wchart_le (F.root i) (fun _ : PUnit.{1} => j) ch' PUnit.unit hη.2
  obtain ⟨W, hW, t₀, hηW, ht₀⟩ := GlobalTheory.Vert.Flag.exists_local_lift_gr F i
    (((ch PUnit.unit).U ⊓ (ch' PUnit.unit).U) ⊓ ρ ⁻¹ᵁ (π ⁻¹ᵁ V))
    (Twist.resM _ (inf_le_left.trans inf_le_left) ((ch PUnit.unit).e 0)) (j (genericPoint Gs)) ⟨⟨m1, m2⟩, hV⟩
  have hWV : W ≤ ρ ⁻¹ᵁ (π ⁻¹ᵁ V) := hW.trans inf_le_right
  have hx : ⊤ ≤ (genPt Gs ≫ j) ⁻¹ᵁ W := top_le_genPt j hηW
  have hxV : ⊤ ≤ ((genPt Gs ≫ jG) ≫ jB) ⁻¹ᵁ V := by
    rw [Category.assoc, c1]
    exact top_le_genPt _ (by simpa using hV)
  have hpt : genPt Gs ≫ jG ≫ πB = spMap φ ≫ genericPt (O.var c) ≫ (O.Φ.C c).π := by
    rw [c2, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ (O.Φ.C c).π) φs
  obtain ⟨g, hg⟩ := (O.Φ.C c).f0.exists_isMap φ (φ' := φ.comp (constF O.κ.e (O.var c)))
    (x' := genPt Gs ≫ jG ≫ πB ≫ genι O.s.T.Z) rfl (by
      have := congrArg (· ≫ genι O.s.T.Z) hpt
      simpa only [Category.assoc] using this)
  have hu : IsEigBasis O.s.T.Z (φ.comp (constF O.κ.e (O.var c))) (genPt Gs ≫ jG ≫ πB ≫ genι O.s.T.Z) σ
      (u V f hf Gs.functionField (genPt Gs ≫ jG) hxV) := by
    have := frB.1 V f hf Gs.functionField (genPt Gs ≫ jG) hxV (φ.comp (algebraMap _ (O.var c).Fn)) (by
      have h1 := congrArg (· ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) hpt
      simp only [Category.assoc] at h1 ⊢
      rw [h1, ← Category.assoc (O.Φ.C c).π, ← Category.assoc (genericPt _), genericPt_π_genStr,
        ← Spec.map_comp, ← Spec.map_comp]
      refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun z => ?_))
      simp [constF])
    rw [Category.assoc] at this
    exact this
  let aG : Γ(F.F i.succ, W) → Fin (O.S.Dw.mult σ) → Gs.functionField := fun t b =>
    TangentOrigin.evalPt (genPt Gs ≫ j) W hx
      ((((hf.pullback π).pullback ρ).basis hWV).repr ((F.ι i.succ).app W t) b)
  have key : ∃ d : Fin (O.S.Dw.mult σ) → Gs.functionField,
      ∀ (c₁ : ((F.root i).pull j).ι) (hW₁ : W ≤ (c₁ PUnit.unit).U) (t : Γ(F.F i.succ, W)),
        (F.π i).app W t = Twist.resM _ hW₁ ((c₁ PUnit.unit).e 0) →
          ∑ b, aG t b * d b = ((r c₁)⁻¹ : Gs.functionFieldˣ) := by
    have hv := funext (hg σ)
    obtain ⟨d, hd⟩ := exists_coord_form g _ hu.1 i
    refine ⟨d, fun c₁ hW₁ t ht => ?_⟩
    obtain ⟨w, cf, h1, h2, h3, -⟩ := c3 c₁ V f hf W hW₁ hWV t ht hx hxV
    rw [← h3]
    exact (hd _ w cf h1 (hv ▸ h2)).symm
  obtain ⟨d, hd⟩ := key
  refine ⟨W, hW.trans inf_le_left, hx, fun t => ∑ b, aG t b * d b, fun s t => ?_, ⟨t₀, ?_⟩,
    fun t ht => hd ch _ t ht, fun t ht => hd ch' _ t ht⟩
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [aG]
    rw [Scheme.Modules.Hom.app_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, mul_assoc]
  · rw [ht₀, Twist.resM_resM]

theorem unitAt_frameSec (D : D7) (O : Setup D) (c : O.s.Comp) {Bs : Scheme.{0}} {Bg : Scheme.{0}} (jB : Bg ⟶ Bs)
    (πB : Bg ⟶ gen O.s.T.Z) {Y X Gs : Scheme.{0}} [IsIntegral Gs] (π : Y ⟶ Bs) (ρ : X ⟶ Y) (j : Gs ⟶ X)
    (πG : Gs ⟶ (O.var c).X) (φ : (O.var c).Fn →+* Gs.functionField) (jG : Gs ⟶ Bg)
    (φs : Gs.fromSpecStalk (genericPoint Gs) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X))
    (c1 : jG ≫ jB = j ≫ ρ ≫ π) (c2 : jG ≫ πB = πG ≫ (O.Φ.C c).π)
    (σ : D.host.E →+* ℂ) {M : Bs.Modules} (hM : IsVB M (O.S.Dw.mult σ))
    (u : FrAssign O.s.T.Z M (O.S.Dw.mult σ) jB) (frB : IsLieFrames O.s.T.Z O.κ.e jB πB M _ σ false u)
    (F : Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj M)) (O.S.Dw.mult σ))
    (i : Fin (O.S.Dw.mult σ)) (r : ((F.root i).pull j).ι → Gs.functionFieldˣ)
    (c3 : GlobalTheory.PairCov.IsFrameSecX (O := O) (c := c) σ hM jB πB u π ρ F j φ jG i r)
    (ch : ((F.root i).pull j).ι) (x : Gs) (hx : x ∈ ((F.root i).pull j).U ch) (t : (O.var c).Fnˣ)
    (ht : ((O.Φ.C c).gr σ i).IsEqn (πG x) t) :
    UnitAt x ((φ (t : (O.var c).Fn))⁻¹ * (r ch : Gs.functionField)) := by
  have hqc := hM.isQuasicoherent
  have hqc' := (hM.pullback π).isQuasicoherent
  obtain ⟨cc, hci, hcc⟩ : ∃ cc : ∀ k, ((F.root k).pull j).ι, cc i = ch ∧
      ∀ k, j x ∈ (cc k PUnit.unit).U := by
    choose U e hU he using fun k => F.isVB_gr k (j x)
    let c₀ : ∀ k, ((F.root k).pull j).ι := fun k _ => ⟨U k, e k, he k⟩
    refine ⟨Function.update c₀ i ch, Function.update_self _ _ _, fun k => ?_⟩
    by_cases hk : k = i
    · subst hk
      rw [Function.update_self]
      exact LB.pull_U_le j ch hx
    · rw [Function.update_of_ne hk]
      exact hU k
  subst hci
  obtain ⟨V, f, hV, hf⟩ := hM (π (ρ (j x)))
  obtain ⟨W, hWV, hW, s, hxW, hs, hfr⟩ := exists_lifts_isFrame F (fun k => cc k PUnit.unit) hcc
    (U := ρ ⁻¹ᵁ (π ⁻¹ᵁ V)) hV
  let ψ := algebraMap (Gs.presheaf.stalk x) Gs.functionField
  have hψ : Function.Injective ψ := IsFractionRing.injective _ _
  have hg : FlagCov.genPt Gs = spMap ψ ≫ Gs.fromSpecStalk x := (spMap_fromSpecStalk Gs x).symm
  have hst {U : Gs.Opens} (hU : x ∈ U) : ⊤ ≤ Gs.fromSpecStalk x ⁻¹ᵁ U := fun w _ => by
    have : Gs.fromSpecStalk x w ∈ Set.range (Gs.fromSpecStalk x) := ⟨w, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open (x := Gs.fromSpecStalk x w) this U.isOpen hU
  have hRW : ⊤ ≤ (Gs.fromSpecStalk x ≫ j) ⁻¹ᵁ W := hst (U := j ⁻¹ᵁ W) hxW
  have hRV : ⊤ ≤ ((Gs.fromSpecStalk x ≫ jG) ≫ jB) ⁻¹ᵁ V := by
    rw [Category.assoc, c1]
    exact hst (U := (j ≫ ρ ≫ π) ⁻¹ᵁ V) hV
  have hKW : ⊤ ≤ (FlagCov.genPt Gs ≫ j) ⁻¹ᵁ W := by
    rw [hg, Category.assoc]
    exact fun w _ => hRW (x := spMap ψ w) trivial
  have hKV' : ⊤ ≤ ((spMap ψ ≫ Gs.fromSpecStalk x ≫ jG) ≫ jB) ⁻¹ᵁ V := by
    rw [Category.assoc]
    exact fun w _ => hRV (x := spMap ψ w) trivial
  have hgj : FlagCov.genPt Gs ≫ jG = spMap ψ ≫ Gs.fromSpecStalk x ≫ jG := by rw [hg, Category.assoc]
  have hKV : ⊤ ≤ ((FlagCov.genPt Gs ≫ jG) ≫ jB) ⁻¹ᵁ V := hgj ▸ hKV'
  obtain ⟨ψ₀, fR, v, tY, e1, e2, e3, e4⟩ := exists_frame (O.Φ.C c) πG φ φs x
    (xR := (Gs.fromSpecStalk x ≫ jG) ≫ πB ≫ genι O.s.T.Z)
    (by rw [Category.assoc, ← Category.assoc jG, c2, Category.assoc])
    (xK := FlagCov.genPt Gs ≫ jG ≫ πB ≫ genι O.s.T.Z) (by rw [← Category.assoc jG, c2, Category.assoc]; rfl)
  have hu := frB.1 V f hf _ (Gs.fromSpecStalk x ≫ jG) hRV ψ₀ (by
    refine Eq.trans ?_ e1
    refine (Category.assoc _ _ _).trans (congrArg _ ((Category.assoc _ _ _).symm.trans ?_))
    rw [c2]
    exact (Category.assoc _ _ _).trans (congrArg _ (O.Φ.C c).π_str))
  have hu' : u V f hf Gs.functionField (FlagCov.genPt Gs ≫ jG) hKV =
      fun b => spMap (dualMap ψ) ≫ u V f hf _ (Gs.fromSpecStalk x ≫ jG) hRV b := by
    have key : ∀ (y : Sp Gs.functionField ⟶ Bg) (hy : ⊤ ≤ (y ≫ jB) ⁻¹ᵁ V), y = spMap ψ ≫ Gs.fromSpecStalk x ≫ jG →
        u V f hf Gs.functionField y hy = fun b => spMap (dualMap ψ) ≫ u V f hf _ (Gs.fromSpecStalk x ≫ jG) hRV b := by
      rintro y hy rfl
      exact funext (frB.2.2 V f hf _ _ ψ _ hRV hy)
    exact key _ _ hgj
  let A₀ := (((hf.pullback π).pullback ρ).basis hWV).toMatrix fun k => (F.ι k.succ).app W (s k)
  have hA₀ : IsUnit A₀.det := by
    have := (((hf.pullback π).pullback ρ).detUnit hfr hWV le_rfl).isUnit
    simpa only [IsFrame.val_detUnit, Twist.resM_self, Module.Basis.det_apply] using this
  let A := A₀.map (TangentOrigin.evalPt (Gs.fromSpecStalk x ≫ j) W hRW)
  have hA : IsUnit A.det := by
    have := hA₀.map (TangentOrigin.evalPt (Gs.fromSpecStalk x ≫ j) W hRW)
    rwa [RingHom.map_det] at this
  have hev (z) : TangentOrigin.evalPt (FlagCov.genPt Gs ≫ j) W hKW z =
      ψ (TangentOrigin.evalPt (Gs.fromSpecStalk x ≫ j) W hRW z) := by
    have key : ∀ (y : Sp Gs.functionField ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ W), y = spMap ψ ≫ Gs.fromSpecStalk x ≫ j → ∀ z,
        TangentOrigin.evalPt y W hy z = ψ (TangentOrigin.evalPt (Gs.fromSpecStalk x ≫ j) W hRW z) := by
      rintro y hy rfl z
      exact TangentOrigin.evalPt_spMap_comp ψ _ W hRW hy z
    exact key _ _ (by rw [hg, Category.assoc]) _
  have hv : (fun k => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v σ k) = v.v σ := (funext (e2 _)).symm
  obtain ⟨b, hb, eb⟩ := (e4 _ _).iff_unitAt.1 ht
  have hb' : UnitAt x (φ (t : (O.var c).Fn) / φ (tY σ i)) :=
    ⟨_, hb.map (πG.stalkMap x).hom, (RingHom.congr_fun (comp_stalkMap πG φ φs x) b).trans
      ((congrArg φ eb).trans (map_div₀ φ _ _))⟩
  have ht0 : φ (t : (O.var c).Fn) ≠ 0 := (map_ne_zero φ).2 t.ne_zero
  have ht1 : φ (tY σ i : (O.var c).Fn) ≠ 0 := (map_ne_zero φ).2 (tY σ i).ne_zero
  have hr0 : (r (cc i) : Gs.functionField) ≠ 0 := Units.ne_zero _
  obtain ⟨d, hd, ed⟩ := unit_of_block hψ e3 hu hA (r (cc i)) i (fun a ha => by
    obtain ⟨s', hs1, hs2⟩ : ∃ s' : Γ(F.F i.succ, W), (F.π i).app W s' = 0 ∧ ∀ b,
        TangentOrigin.evalPt (Gs.fromSpecStalk x ≫ j) W hRW
          ((((hf.pullback π).pullback ρ).basis hWV).repr ((F.ι i.succ).app W s') b) = a b := by
      rcases ha with rfl | ⟨k, hk, rfl⟩
      · exact ⟨0, map_zero _, fun b => by
          rw [map_zero, map_zero, Finsupp.zero_apply, map_zero]
          rfl⟩
      · obtain ⟨s', h1, h2⟩ := exists_ker F hk (s k)
        exact ⟨s', h1, fun b => by rw [h2]; rfl⟩
    have := c3 (cc i) V f hf W (hW i) hWV (s i + s') (by rw [map_add, hs1, add_zero, hs]) hKW hKV
    simp only [hev, map_add, Finsupp.add_apply, hs2] at this
    rw [hu', hv] at this
    exact this)
  have h1 : UnitAt x (ψ d) := ⟨d, hd, rfl⟩
  convert hb'.inv.mul h1.inv using 1
  have ed' : ψ d = φ (tY σ i) * (r (cc i) : Gs.functionField)⁻¹ :=
    ed.trans (congrArg _ (Units.val_inv_eq_inv_val _))
  rw [ed']
  field_simp

theorem lineAdl_D {D : D7} (O : Setup D) (R : ℝ) (c : O.s.Comp) (σ : D.host.E →+* ℂ) (i : Fin (O.S.Dw.mult σ))
    (st : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ) (h : letterOf O.S.Dw st = some ⟨σ, i⟩) :
    (lineAdl O R c st 1).D = (O.Φ.C c).gr σ i := by
  change divOf _ (expo _ _) = _
  have e : ∀ x, expo O.S.Dw (Finsupp.single (ArIn.ind ∅, some R, st) 1) x = if x = ⟨σ, i⟩ then 1 else 0 := by
    intro x
    rw [expo, Finsupp.sum_single_index (by simp)]
    simp only [h, Option.some.injEq, eq_comm]
  rw [divOf]
  simp_rw [e, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq']
  simp

theorem isRatSec_and_unitAt : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration →
  ∀ (D : D7) (O : Setup D) (hO : O.Core) (R : ℝ) (hR : 2 ≤ R) (c : O.s.Comp) (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL))
    (arq : IsArithVar q (dimGr D.what₂.Tau O.N O.j)) (nBs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs)
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z) (G : ∀ σ', EigMet O.s.T.Z σ')
    (Y X Gs : Scheme.{0}) [IsIntegral Y] [IsIntegral X] [IsIntegral Gs] (π : Y ⟶ Bs) (ρ : X ⟶ Y) (j : Gs ⟶ X)
    (πG : Gs ⟶ (O.var c).X) (φ : (O.var c).Fn →+* Gs.functionField) (jG : Gs ⟶ Bg),
    IsArithVar (ρ ≫ π ≫ q) (O.var c).dim → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    GlobalTheory.PairCov.CovCommon O R c q jB πB G π ρ j πG φ jG →
    ∀ (σ : D.host.E →+* ℂ) (M : Bs.Modules) (hM : VMetric q M (O.S.Dw.mult σ)) (HM : hM.IsCInf)
      (t : FrAssign O.s.T.Z M (O.S.Dw.mult σ) jB), IsLieFrames O.s.T.Z O.κ.e jB πB M _ σ false t →
    ∀ (F : Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj M)) (O.S.Dw.mult σ))
      (i : Fin (O.S.Dw.mult σ)) (r : ((F.root i).pull j).ι → Gs.functionFieldˣ),
      GlobalTheory.PairCov.IsFrameSecX (O := O) (c := c) σ hM.isVB jB πB t π ρ F j φ jG i r →
    ∀ st, letterOf O.S.Dw st = some ⟨σ, i⟩ →
      IsRatSec ((VMetric.grLB F i ((HM.pull π rfl).pull ρ rfl)).B.pull j) r ∧
      ∀ ch, ∀ x ∈ ((VMetric.grLB F i ((HM.pull π rfl).pull ρ rfl)).B.pull j).U ch, UnitAt x (φ (genAt (lineAdl O R c st 1).D (πG x)) ^ 1 * r ch) := by
  intro _ _ _ D O hO R hR c Bs _ q arq nBs Bg jB πB G Y X Gs _ _ _ π ρ j πG φ jG _ _ hc σ M hM HM t ht F i r hr st hst
  obtain ⟨-, -, -, -, -, -, -, φs, c1, c2⟩ := hc
  refine ⟨isRatSec_frameSec D O c jB πB π ρ j πG φ jG φs c1 c2 σ hM.isVB t ht F i r hr, fun ch x hx => ?_⟩
  have he := Base.isEqn_eqn (lineAdl O R c st 1).D (πG x)
  have := unitAt_frameSec D O c jB πB π ρ j πG φ jG φs c1 c2 σ hM.isVB t ht F i r hr ch x hx
    (eqn (lineAdl O R c st 1).D (πG x)) (by
      rw [← lineAdl_D O R c σ i st hst]
      exact he)
  simpa only [pow_one, genAt, Units.val_inv_eq_inv_val, map_inv₀] using this

end GlobalTheory.PairCovRat

end
