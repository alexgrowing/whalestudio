import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageConnectedComponentMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatDRSubsetLatHT
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad.Guard

attribute [local instance] Over.cartesianMonoidalCategory

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {X : Scheme.{0}}

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem sp_epsMul_one (R : Type) [CommRing R] : spMap (epsMul (1 : R)) = 𝟙 _ := by
  rw [← Spec.map_id]
  congr 1
  ext r <;> simp [epsMul]

abbrev torus (X : Scheme.{0}) : SAB H X :=
  GlobalTheory.Models.Inhab.trivTriple H (splitTorus X (𝓞 E)) (GlobalTheory.Diag.isSemiAbelian _ _) (GlobalTheory.Diag.diagAct _ _ _)

def charUnit {A : Type} [CommRing A] {g : Sp A ⟶ X} (w : Over.mk g ⟶ splitTorus X (𝓞 E)) (a : 𝓞 E) : Aˣ :=
  ⟨GlobalTheory.Diag.charVal w a, GlobalTheory.Diag.charVal w (-a), by rw [← GlobalTheory.Diag.charVal_add, add_neg_cancel, GlobalTheory.Diag.charVal_zero],
    by rw [← GlobalTheory.Diag.charVal_add, neg_add_cancel, GlobalTheory.Diag.charVal_zero]⟩

def torusChar {O : Type} [CommRing O] (x : Sp O ⟶ X) (q : ℕ) (a : 𝓞 E) : TorsChar (torus H X) x q where
  χ _ _ _ _ g := charUnit g a
  mul _ _ _ _ g g' _ _ := Units.ext (GlobalTheory.Diag.charVal_mul g g' a)
  nat B B' _ _ _ _ _ _ φ g g' _ h :=
    (GlobalTheory.Diag.left_eq_iff φ.toRingHom (by rw [← Category.assoc, sp_comp]; congr 2; exact φ.comp_algebraMap.symm) g' g).1 h a

theorem torusChar_epsVec {O : Type} [CommRing O] (x : Sp O ⟶ X) (q : ℕ) (a : 𝓞 E) (I : Ideal O) (c : 𝓞 E →+ O ⧸ I) :
    (((torusChar H x q a).χ (DualNumber (O ⧸ I)) (GlobalTheory.Diag.epsVec _ c) : (DualNumber (O ⧸ I))ˣ) :
      DualNumber (O ⧸ I)).snd = c a := by
  refine (congrArg TrivSqZeroExt.snd (GlobalTheory.Diag.charVal_epsVec c a)).trans ?_
  simp

end Lat

section Norm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

section Comb

variable {R : Type} [CommRing R] {x : Sp R ⟶ X} {m : ℕ} {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)}

theorem exists_comb (hu : ∀ k, IsTanAtG t x (u k)) (cf : Fin m → R) : ∃ w, IsTanAtG t x w ∧ IsCombAtG t x u cf w :=
  ⟨_, isTanAtG_of _ (combT_tan _ (fun j => ovT (hu j)) (fun _ => smT_zero_ovT _) cf),
    (isCombAtG_iff t x (fun j => ovT (hu j)) cf _).2 rfl⟩

theorem comb_unique (hu : ∀ k, IsTanAtG t x (u k)) {cf : Fin m → R} {w w' : Sp (DualNumber R) ⟶ t.G.left}
    (h : IsCombAtG t x u cf w) (h' : IsCombAtG t x u cf w') : w = w' :=
  ((isCombAtG_iff t x (fun j => ovT (hu j)) _ _).1 h).symm.trans ((isCombAtG_iff t x (fun j => ovT (hu j)) _ _).1 h')

theorem comb_tan (hu : ∀ k, IsTanAtG t x (u k)) {cf : Fin m → R} {w : Sp (DualNumber R) ⟶ t.G.left}
    (h : IsCombAtG t x u cf w) : IsTanAtG t x w := by
  obtain ⟨w', h1, h2⟩ := exists_comb hu cf
  exact comb_unique hu h2 h ▸ h1

theorem comb_smul (hu : ∀ k, IsTanAtG t x (u k)) {cf : Fin m → R} {w : Sp (DualNumber R) ⟶ t.G.left}
    (h : IsCombAtG t x u cf w) (a : R) : IsCombAtG t x u (fun k => a * cf k) (spMap (epsMul a) ≫ w) := by
  rw [← (isCombAtG_iff t x (fun j => ovT (hu j)) _ _).1 h]
  exact (isCombAtG_iff t x (fun j => ovT (hu j)) _ _).2 (by rw [← smT_combT]; rfl)

variable (t x u) in

def Indep : Prop := ∀ cf cf' w, IsCombAtG t x u cf w → IsCombAtG t x u cf' w → cf = cf'

theorem indep_iff {n : ℕ} {v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} (hv : ∀ k, IsTanAtG t x (v k))
    (hi : Indep t x v) (A : Matrix (Fin n) (Fin m) R) (hA : ∀ i, IsCombAtG t x v (fun j => A j i) (u i)) :
    Indep t x u ↔ Function.Injective A.mulVec := by
  have hu := fun i => comb_tan hv (hA i)
  refine ⟨fun h cf cf' e => ?_, fun h cf cf' w h1 h2 => h (hi _ _ w (tanLinG v hv u A cf w hA h1)
    (tanLinG v hv u A cf' w hA h2))⟩
  obtain ⟨w, -, h1⟩ := exists_comb hu cf
  obtain ⟨w', -, h2⟩ := exists_comb hu cf'
  have h3 := comb_unique hv (tanLinG v hv u A cf w hA h1) (e ▸ tanLinG v hv u A cf' w' hA h2)
  exact h cf cf' w h1 (h3 ▸ h2)

theorem indep_of_basis (hu : ∀ k, IsTanAtG t x (u k))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x u cf w) : Indep t x u :=
  fun _ _ w h1 h2 => (hb w (comb_tan hu h1)).unique h1 h2

end Comb

theorem exists_left_inv {K : Type} [Field K] {n m : ℕ} (A : Matrix (Fin n) (Fin m) K) (h : Function.Injective A.mulVec) :
    ∃ B : Matrix (Fin m) (Fin n) K, B * A = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A) (LinearMap.ker_eq_bot.2 h)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' A, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

theorem Indep.map {K K' : Type} [Field K] [Field K'] (io : K →+* K') {x : Sp K ⟶ X} {m : ℕ}
    {u : Fin m → (Sp (DualNumber K) ⟶ t.G.left)} (hu : ∀ k, IsTanAtG t x (u k)) (h : Indep t x u) :
    Indep t (spMap io ≫ x) fun k => spMap (dualMap io) ≫ u k := by
  obtain ⟨n, v, hv, hb⟩ := GlobalTheory.LieLocBasis.exists_lie_basis_stable E H X t K x
  have h1 : spMap (RingHom.id K) = 𝟙 _ := Spec.map_id _
  have h3 : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have hb0 := hb K (RingHom.id K)
  simp only [h1, h3, Category.id_comp] at hb0
  choose a ha using fun i => (hb0 _ (hu i)).exists
  let A : Matrix (Fin n) (Fin m) K := fun j i => a i j
  obtain ⟨B, hB⟩ := exists_left_inv A ((indep_iff hv (indep_of_basis hv hb0) A ha).1 h)
  have hv' := fun j => GlobalTheory.FactorDepth.isTanAtG_map t io (hv j)
  refine (indep_iff hv' (indep_of_basis hv' (hb K' io)) (A.map io) fun i => GlobalTheory.LatDRFree.comb_map t io (ha i)).2
    fun c c' e => ?_
  have h4 := congrArg (B.map io).mulVec e
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, hB, Matrix.map_one _ (map_zero io) (map_one io),
    Matrix.one_mulVec, Matrix.one_mulVec] at h4

variable {C : Type} [NontriviallyNormedField C] {x : Sp C ⟶ X} {Λ : Set (Sp (DualNumber C) ⟶ t.G.left)} {m : ℕ}
  {u u' : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}

variable (t x Λ u) in

def grSet (i : Fin m) : Set ℝ :=
  {r | ∃ cf : Fin m → C, cf i ≠ 0 ∧ (∀ k, i < k → cf k = 0) ∧ (∃ w ∈ Λ, IsCombAtG t x u cf w) ∧ r = ‖cf i‖⁻¹}

theorem grNorm_eq (i : Fin m) : grNorm t x Λ u i = sInf (grSet t x Λ u i) := rfl

theorem grNorm_pos_of_basis {n : ℕ} {v : Fin n → (Sp (DualNumber C) ⟶ t.G.left)} (hv : ∀ k, IsTanAtG t x (v k))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x v cf w)
    (h1 : ∀ cf w, IsCombAtG t x v cf w → (∀ j, ‖cf j‖ ≤ 1) → w ∈ Λ) {b : ℝ}
    (h2 : ∀ cf w, IsCombAtG t x v cf w → w ∈ Λ → ∀ j, ‖cf j‖ ≤ b) (hu : ∀ k, IsTanAtG t x (u k)) (hi : Indep t x u)
    (i : Fin m) : (grSet t x Λ u i).Nonempty ∧ 0 < grNorm t x Λ u i := by
  choose a ha using fun i => (hb _ (hu i)).exists
  let A : Matrix (Fin n) (Fin m) C := fun j i => a i j
  obtain ⟨B, hB⟩ := exists_left_inv A ((indep_iff hv (indep_of_basis hv hb) A ha).1 hi)
  have hne : (grSet t x Λ u i).Nonempty := by
    have hs : 0 < 1 + ∑ j, ‖a i j‖ := by positivity
    obtain ⟨c, hc0, hc⟩ := NormedField.exists_norm_lt C (inv_pos.2 hs)
    obtain ⟨w, -, hw⟩ := exists_comb hu (Pi.single i c)
    refine ⟨_, Pi.single i c, by simpa using norm_pos_iff.1 hc0, fun k hk => Pi.single_eq_of_ne hk.ne' _,
      ⟨w, h1 _ w (tanLinG v hv u A _ w ha hw) fun j => ?_, hw⟩, rfl⟩
    have h5 : ‖a i j‖ ≤ 1 + ∑ j, ‖a i j‖ :=
      (Finset.single_le_sum (f := fun j => ‖a i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans (by linarith)
    have h6 : A.mulVec (Pi.single i c) j = a i j * c := by
      rw [Matrix.mulVec_single]
      rfl
    rw [h6, norm_mul]
    calc _ ≤ (1 + ∑ j, ‖a i j‖) * (1 + ∑ j, ‖a i j‖)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hs.ne'
  refine ⟨hne, ?_⟩
  have hK : ∀ r ∈ grSet t x Λ u i, 0 < ∑ j, ‖B i j‖ * b ∧ (∑ j, ‖B i j‖ * b)⁻¹ ≤ r := by
    rintro _ ⟨cf, h0, -, ⟨w, hw, hc⟩, rfl⟩
    have h7 := h2 _ w (tanLinG v hv u A cf w ha hc) hw
    have h8 : cf i = ∑ j, B i j * A.mulVec cf j := by
      have := congrFun (Matrix.mulVec_mulVec cf B A) i
      rw [hB, Matrix.one_mulVec] at this
      exact this.symm
    have h9 : ‖cf i‖ ≤ ∑ j, ‖B i j‖ * b := by
      rw [h8]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (h7 j) (norm_nonneg _)
    have h10 := norm_pos_iff.2 h0
    exact ⟨h10.trans_le h9, inv_anti₀ h10 h9⟩
  obtain ⟨r, hr⟩ := hne
  exact (inv_pos.2 (hK r hr).1).trans_le (le_csInf ⟨r, hr⟩ fun r hr => (hK r hr).2)

theorem tri_mulVec {K : Type} [Field K] {A : Matrix (Fin m) (Fin m) K} (hA : A.BlockTriangular id) {i : Fin m}
    {cf : Fin m → K} (h : ∀ k, i < k → cf k = 0) :
    (∀ k, i < k → A.mulVec cf k = 0) ∧ A.mulVec cf i = A i i * cf i := by
  have e : ∀ k, A.mulVec cf k = ∑ j, A k j * cf j := fun _ => rfl
  simp only [e]
  refine ⟨fun k hk => Finset.sum_eq_zero fun j _ => ?_, Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)⟩
  · rcases le_or_gt j i with hj | hj
    · rw [hA (show id j < id k from hj.trans_lt hk), zero_mul]
    · rw [h j hj, mul_zero]
  · rcases lt_or_gt_of_ne hj with hj | hj
    · rw [hA (show id j < id i from hj), zero_mul]
    · rw [h j hj, mul_zero]

open Pointwise in

theorem grNorm_tri (hu : ∀ k, IsTanAtG t x (u k)) {d : Fin m → C} (hd : ∀ i, d i ≠ 0)
    (h : ∀ i, ∃ cf : Fin m → C, cf i = d i ∧ (∀ k, i < k → cf k = 0) ∧ IsCombAtG t x u cf (u' i)) (i : Fin m) :
    grNorm t x Λ u' i = ‖d i‖ * grNorm t x Λ u i := by
  choose a h1 h2 h3 using h
  let A : Matrix (Fin m) (Fin m) C := fun j i => a i j
  have hA : A.BlockTriangular id := fun j k hk => h2 k j hk
  have hdet : IsUnit A.det := by
    rw [Matrix.det_of_upperTriangular hA]
    exact (Finset.prod_ne_zero_iff.2 fun k _ => (h1 k).trans_ne (hd k)).isUnit
  let _ := Matrix.invertibleOfIsUnitDet A hdet
  have hn : ‖d i‖ ≠ 0 := norm_ne_zero_iff.2 (hd i)
  have key : grSet t x Λ u' i = ‖d i‖ • grSet t x Λ u i := by
    ext r
    constructor
    · rintro ⟨cf, h0, hz, ⟨w, hw, hc⟩, rfl⟩
      obtain ⟨e1, e2⟩ := tri_mulVec hA hz
      rw [show A i i = d i from h1 i] at e2
      refine ⟨_, ⟨A.mulVec cf, e2 ▸ mul_ne_zero (hd i) h0, e1, ⟨w, hw, tanLinG u hu u' A cf w h3 hc⟩, rfl⟩, ?_⟩
      simp only [e2, norm_mul, smul_eq_mul, mul_inv, mul_inv_cancel_left₀ hn]
    · rintro ⟨_, ⟨cf, h0, hz, ⟨w, hw, hc⟩, rfl⟩, rfl⟩
      obtain ⟨e1, -⟩ := tri_mulVec (Matrix.blockTriangular_inv_of_blockTriangular hA) hz
      have e3 : A.mulVec (A⁻¹.mulVec cf) = cf := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
      have e2 := (tri_mulVec hA e1).2
      rw [e3, show A i i = d i from h1 i] at e2
      obtain ⟨w', -, hw'⟩ := exists_comb (fun k => comb_tan hu (h3 k)) (A⁻¹.mulVec cf)
      have e4 : w' = w := comb_unique hu (e3 ▸ tanLinG u hu u' A _ w' h3 hw') hc
      refine ⟨A⁻¹.mulVec cf, fun e => h0 (by rw [e2, e, mul_zero]), e1, ⟨w, hw, e4 ▸ hw'⟩, ?_⟩
      simp only [e2, norm_mul, smul_eq_mul, mul_inv, mul_inv_cancel_left₀ hn]
  rw [grNorm_eq, grNorm_eq, key, Real.sInf_smul_of_nonneg (norm_nonneg _), smul_eq_mul]

end Norm

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section AnyBase

variable {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) (Ω : Type) [Field Ω]

def flagPtEquiv : FlagPt Z Ω ≃
    Σ (φ : c.F →+* Ω) (y : {y : Sp Ω ⟶ gen Z // y ≫ genStr Z = spMap φ}), EigFrame Z φ (y.1 ≫ genι Z) where
  toFun y := ⟨y.fK, ⟨y.y, y.y_over⟩, y.frame⟩
  invFun z := ⟨z.1, z.2.1.1, z.2.1.2, z.2.2.v, z.2.2.tan, z.2.2.eig, z.2.2.basis⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem exists_flagPt (y : Sp Ω ⟶ gen Z) : ∃ z : FlagPt Z Ω, z.y = y := by
  have h : y ≫ genStr Z = spMap (Spec.preimage (y ≫ genStr Z)).hom := (Spec.map_preimage _).symm
  obtain ⟨f⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z Ω _ y h
  exact ⟨(flagPtEquiv Z Ω).symm ⟨_, ⟨y, h⟩, f⟩, rfl⟩

variable {Z Ω}

theorem indep_u (y : FlagPt Z Ω) (τ : E →+* ℂ) : Indep Z.t (y.y ≫ genι Z) (y.u τ) := by
  intro cf cf' w h1 h2
  refine (y.basis τ w (comb_tan (y.tan τ) h1) fun a => ?_).unique h1 h2
  rw [← (isCombAtG_iff Z.t _ (fun j => ovT (y.tan τ j)) _ _).1 h1]
  have := Z.t.act.hom a
  exact congrArg (fun f => f.left) (combT_eig _ (fun j => ovT (y.tan τ j)) (Z.t.act.act a) _
    (fun j => Over.OverMorphism.ext (y.eig τ j a)) cf)

def SameFlags (y y' : FlagPt Z Ω) (d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Ωˣ) : Prop :=
  y'.y = y.y ∧ y.frame.Tri (RingHom.id Ω) y'.frame d

theorem SameFlags.refl (y : FlagPt Z Ω) : SameFlags y y 1 := ⟨rfl, y.frame.tri_refl⟩

theorem SameFlags.grNorm {y y' : FlagPt Z Ω} {d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Ωˣ} (h : SameFlags y y' d)
    {C : Type} [NontriviallyNormedField C] (io : Ω →+* C) (Λ : Set (Sp (DualNumber C) ⟶ Z.t.G.left)) (τ : E →+* ℂ)
    (i : Fin (Dw.mult τ)) :
    grNorm Z.t (spMap io ≫ y'.y ≫ genι Z) Λ (fun k => spMap (dualMap io) ≫ y'.u τ k) i =
      ‖io (d τ i)‖ * grNorm Z.t (spMap io ≫ y.y ≫ genι Z) Λ (fun k => spMap (dualMap io) ≫ y.u τ k) i := by
  have h3 : spMap (dualMap (RingHom.id Ω)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  rw [h.1]
  refine grNorm_tri (d := fun k => io (d τ k)) (fun k => GlobalTheory.FactorDepth.isTanAtG_map _ io (y.tan τ k))
    (fun k => (map_ne_zero io).2 (d τ k).ne_zero) (fun k => ?_) i
  obtain ⟨cf, e1, e2, e3⟩ := h.2.2.2 τ k
  simp only [h3, Category.id_comp, h.1] at e3
  exact ⟨fun a => io (cf a), congrArg io e1, fun a ha => (congrArg io (e2 a ha)).trans (map_zero io), GlobalTheory.LatDRFree.comb_map _ io e3⟩

end AnyBase

theorem intO_valRing (C : Type) [NormedField C] [IsUltrametricDist C] : ValuationRing (intO C) := by
  refine @ValuationRing.mk _ _ _ ⟨fun a b => ?_⟩
  by_cases h : ‖(a : C)‖ ≤ ‖(b : C)‖
  · by_cases hb : (b : C) = 0
    · refine ⟨1, Or.inr (Subtype.ext ?_)⟩
      rw [hb, norm_zero, norm_le_zero_iff] at h
      simp [h, hb]
    · refine ⟨⟨a / b, show ‖(a / b : C)‖ ≤ 1 by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)⟩,
        Or.inr (Subtype.ext ?_)⟩
      simp [mul_div_cancel₀ _ hb]
  · have ha : (a : C) ≠ 0 := fun h0 => h (by simp [h0])
    refine ⟨⟨b / a, show ‖(b / a : C)‖ ≤ 1 by rw [norm_div]; exact div_le_one_of_le₀ (le_of_not_ge h) (norm_nonneg _)⟩,
      Or.inl (Subtype.ext ?_)⟩
    simp [mul_div_cancel₀ _ ha]

theorem intO_frac (C : Type) [NormedField C] [IsUltrametricDist C] : IsFractionRing (intO C) C := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  by_cases h : ‖z‖ ≤ 1
  · exact ⟨⟨z, h⟩, 1, by rw [map_one, div_one]; rfl⟩
  · exact ⟨1, ⟨z⁻¹, show ‖z⁻¹‖ ≤ 1 by rw [norm_inv]; exact inv_le_one_of_one_le₀ (le_of_not_ge h)⟩,
      by rw [map_one, one_div]; exact (inv_inv z).symm⟩

variable (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

theorem existsUnique_ext (x : Sp C ⟶ Z.X) : ∃! xO : Sp ↥(intO C) ⟶ Z.X, spMap (intO C).subtype ≫ xO = x := by
  have := isProper_toroidalModel_structureMap Z
  have := intO_valRing C
  have := intO_frac C
  let φ : 𝓞 c.F →+* C := (Spec.preimage (x ≫ Z.s)).hom
  have hφ : ∀ a, φ a ∈ intO C := fun a => by
    have h1 : IsIntegral (intO C) (φ a) := (RingOfIntegers.isIntegral a).map_of_comp_eq (Int.castRingHom _) φ
      (RingHom.ext_int _ _)
    classical
    let _ : GCDMonoid (intO C) := IsBezout.toGCDDomain _
    have : IsIntegrallyClosed (intO C) := GCDMonoid.toIsIntegrallyClosed
    obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := intO C) (K := C)).1 h1
    exact hb ▸ b.2
  have hv : ValuativeCriterion.Existence Z.s := by
    have h := (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed Z.s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact : MorphismProperty Scheme) Z.s)
    exact h.1
  let S : ValuativeCommSq Z.s :=
    { R := intO C, K := C, i₁ := x, i₂ := spMap (φ.codRestrict _ hφ)
      commSq := ⟨by
        rw [← Spec.map_preimage (x ≫ Z.s)]
        exact Spec.map_comp (CommRingCat.ofHom (φ.codRestrict _ hφ)) (CommRingCat.ofHom (intO C).subtype)⟩ }
  have hs : ∀ a : Sp ↥(intO C) ⟶ Z.X, spMap (intO C).subtype ≫ a = x → a ≫ Z.s = S.i₂ := fun a ha => by
    rw [← Spec.map_preimage (a ≫ Z.s)]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext ?_))
    have e : Spec.preimage (x ≫ Z.s) = Spec.preimage (a ≫ Z.s) ≫ CommRingCat.ofHom (intO C).subtype := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, ← ha, Category.assoc]
    exact (congrArg (fun f => f.hom r) e).symm
  obtain ⟨⟨xO, h1, h2⟩⟩ := (hv S).exists_lift
  refine ⟨xO, h1, fun a ha => ?_⟩
  exact congrArg CommSq.LiftStruct.l ((IsSeparated.valuativeCriterion Z.s S).elim ⟨a, ha, hs a ha⟩ ⟨xO, h1, h2⟩)

theorem grNorm_latDR_pos (x : Sp C ⟶ Z.X) {m : ℕ} {u : Fin m → (Sp (DualNumber C) ⟶ Z.t.G.left)}
    (hu : ∀ k, IsTanAtG Z.t x (u k)) (hi : Indep Z.t x u) (i : Fin m) :
    (grSet Z.t x (latDR Z.t x) u i).Nonempty ∧ 0 < grNorm Z.t x (latDR Z.t x) u i := by
  obtain ⟨xO, rfl, hx⟩ := existsUnique_ext Z x
  obtain ⟨g, v, hv, hb, hL⟩ := GlobalTheory.LatDRFree.latDR_free E H _ Z.t C xO hx
  exact grNorm_pos_of_basis hv hb (fun cf w h => (hL cf w h).2) (fun cf w h => (hL cf w h).1) hu hi i

theorem grNorm_latHT_pos (hB : HTBoundSt) (p : ℕ) [hp : Fact p.Prime] (x : Sp ℂ_[p] ⟶ Z.X) {m : ℕ}
    {u : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left)} (hu : ∀ k, IsTanAtG Z.t x (u k)) (hi : Indep Z.t x u)
    (i : Fin m) : (grSet Z.t x (latHT Z.t p x) u i).Nonempty ∧ 0 < grNorm Z.t x (latHT Z.t p x) u i := by
  obtain ⟨xO, rfl, hx⟩ := existsUnique_ext Z x
  obtain ⟨g, v, hv, hb, hL⟩ := GlobalTheory.LatDRFree.latDR_free E H _ Z.t ℂ_[p] xO hx
  have hn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by simpa using PadicComplex.norm_extends' p (p : ℚ_[p])
  obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt ℂ_[p]
    (Real.rpow_pos_of_pos (Nat.cast_pos.2 hp.out.pos : (0 : ℝ) < p) (-(1 / ((p : ℝ) - 1))))
  refine grNorm_pos_of_basis (b := ‖a‖⁻¹) hv hb
    (fun cf w h h' => latDR_subset_latHT _ _ _ _ _ p _ ((hL cf w h).2 h')) (fun cf w h hw j => ?_) hu hi i
  have h1 := (hL _ _ (comb_smul hv h a)).1 (hB E H _ Z.t p ℂ_[p] hn xO hx w hw a ha.le) j
  rw [norm_mul] at h1
  rw [← one_div, le_div_iff₀ ha0, mul_comm]
  exact h1

theorem grNorm_lat_pos {Ω : Type} [Field Ω] (y : FlagPt Z Ω) (p : ℕ) [Fact p.Prime] (io : Ω →+* ℂ_[p]) (b : Bool)
    (hB : b = true → HTBoundSt) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    0 < grNorm Z.t (spMap io ≫ y.y ≫ genι Z) (lat Z.t p (spMap io ≫ y.y ≫ genι Z) b)
      (fun k => spMap (dualMap io) ≫ y.u τ k) i := by
  have hu := fun k => GlobalTheory.FactorDepth.isTanAtG_map _ io (y.tan τ k)
  have hi := (indep_u y τ).map io (y.tan τ)
  cases b
  · exact (grNorm_latDR_pos Z _ hu hi i).2
  · exact (grNorm_latHT_pos Z (hB rfl) p _ hu hi i).2

variable {Z}

def diagAt {Ω : Type} [Field Ω] (d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Ωˣ) (τ : E →+* ℂ) (k : ℕ) : Ωˣ :=
  if h : k < Dw.mult τ then d τ ⟨k, h⟩ else 1

def rootFac {Ω : Type} [Field Ω] (d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Ωˣ) (τ : E →+* ℂ) (i : ℕ) : Ωˣ :=
  if i < Dw.p then diagAt d τ i else (diagAt d (conjEmb τ) (Dw.p + Dw.q - 1 - i))⁻¹

variable {Ω : Type} [Field Ω] {y y' : FlagPt Z Ω} {d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Ωˣ} (h : SameFlags y y' d)
  (p : ℕ) [Fact p.Prime] (io : Ω →+* ℂ_[p]) (b : Bool) (hB : b = true → HTBoundSt) (τ : E →+* ℂ)
include h hB

theorem SameFlags.lnLie (k : ℕ) : y'.lnLie io p b τ k = y.lnLie io p b τ k + Real.log ‖io (diagAt d τ k)‖ := by
  unfold FlagPt.lnLie diagAt
  split_ifs with hk
  · rw [h.grNorm, h.1, Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero io).2 (d τ _).ne_zero))
      (grNorm_lat_pos Z y p io b hB τ _).ne', add_comm]
  · simp

theorem SameFlags.lnRoot (i : ℕ) : y'.lnRoot io p b τ i = y.lnRoot io p b τ i + Real.log ‖io (rootFac d τ i)‖ := by
  unfold FlagPt.lnRoot rootFac
  by_cases hi : i < Dw.p
  · simp only [if_pos hi, h.lnLie p io b hB]
    ring
  · simp only [if_neg hi, h.lnLie p io b hB, Units.val_inv_eq_inv_val, map_inv₀, norm_inv, Real.log_inv]
    ring

end Pts

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

theorem exists_pt (k : s.Comp) : ∃ y : Pt s, compPt s y = k := PtComp.compPt_surjective s k

instance nonempty_pt : Nonempty (Pt s) := (exists_pt s (compNe s).some).nonempty

theorem lnAt_eq (p : ℕ) [hp : Fact p.Prime] (b : Bool) (y : Pt s) (x : DV.Rt D.what₂.Tau N) :
    lnAt s p b y x = y.lnRoot (iotaP p) p b (DV.tauEmb D x.1) x.2 := dif_pos hp.out

def detFac (d : ∀ τ, Fin (S.Dw.mult τ) → Qbˣ) (τ : D.what₂.Tau) : Qbˣ := ∏ i : Fin N, rootFac d (DV.tauEmb D τ) i

def IsSec (sv : D.what₂.Tau → Pt s → Qb) : Prop :=
  (∀ τ y, sv τ y ≠ 0) ∧ ∀ τ y y' d, SameFlags y y' d → sv τ y' * detFac d τ = sv τ y

end GlobalTheory.ShFam.Pad.Guard
