import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameComposeRingHomBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagLocallyAdaptedAffineFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelCarriesSameFlagsSpecialiseValuationRing
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BcRead.FinPl

open GlobalTheory.ShFam.Pad.Guard

section Alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

theorem grNorm_of_tri {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {x : Sp C ⟶ X}
    {Λ : Set (Sp (DualNumber C) ⟶ t.G.left)} {m : ℕ} {f u : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}
    (hf : ∀ k, IsTanAtG t x (f k)) (hi : Indep t x f) {M Q Q' : Matrix (Fin m) (Fin m) C}
    (hM : ∀ b, IsCombAtG t x f (fun k => M k b) (u b)) (hQ : ∀ a b, ‖Q a b‖ ≤ 1) (hQ' : ∀ a b, ‖Q' a b‖ ≤ 1)
    (hQQ : Q * Q' = 1) (hN : (M * Q).BlockTriangular id) (hN0 : ∀ k, (M * Q) k k ≠ 0) {δ : C} (hδ : δ ≠ 0)
    (hΛ : ∀ cf w, IsCombAtG t x f cf w →
      ((∃ a : Fin m → C, (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG t x u a w) ↔ spMap (epsMul δ) ≫ w ∈ Λ)) (k : Fin m) :
    grNorm t x Λ f k = (‖δ‖ * ‖(M * Q) k k‖)⁻¹ := by
  have bd : ∀ (A : Matrix (Fin m) (Fin m) C) (a : Fin m → C), (∀ i j, ‖A i j‖ ≤ 1) → (∀ i, ‖a i‖ ≤ 1) →
      ∀ i, ‖A.mulVec a i‖ ≤ 1 := fun A a hA ha i => by
    change ‖∑ j, A i j * a j‖ ≤ 1
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
    rw [norm_mul]; exact mul_le_one₀ (hA _ _) (norm_nonneg _) (ha _)
  have hdet : IsUnit (M * Q).det := by
    rw [Matrix.det_of_isUpperTriangular hN]
    exact (Finset.prod_ne_zero_iff.2 fun k _ => hN0 k).isUnit
  have hMd : IsUnit M.det := isUnit_of_mul_isUnit_left (by rwa [Matrix.det_mul] at hdet)
  have hu := fun b => comb_tan hf (hM b)
  choose g hgt hg using fun i => exists_comb hf (fun j => δ * (M * Q) j i)
  have key : ∀ cf w, IsCombAtG t x g cf w → (w ∈ Λ ↔ ∀ i, ‖cf i‖ ≤ 1) := fun cf w hw => by
    have h1 := tanLinG f hf g (δ • (M * Q)) cf w hg hw
    obtain ⟨w', -, hw'⟩ := exists_comb hu (Q.mulVec cf)
    have h2 := tanLinG f hf u M _ w' hM hw'
    have h3 : w = spMap (epsMul δ) ≫ w' := by
      refine comb_unique hf h1 ?_
      convert comb_smul hf h2 δ using 1
      rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec]
      rfl
    rw [h3, ← hΛ _ w' h2]
    refine ⟨fun ⟨a, ha, hc⟩ => ?_, fun h => ⟨_, bd Q cf hQ h, hw'⟩⟩
    have h4 := hi _ _ _ (tanLinG f hf u M _ w' hM hc) h2
    have h5 : a = Q.mulVec cf := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hMd) h4
    have h6 : Q'.mulVec a = cf := by
      rw [h5, Matrix.mulVec_mulVec, mul_eq_one_comm.1 hQQ, Matrix.one_mulVec]
    exact h6 ▸ bd Q' a hQ' ha
  have h1 : grNorm t x Λ g k = 1 := by
    refine IsLeast.csInf_eq ⟨⟨Pi.single k 1, by simp, fun j hj => by simp [hj.ne'], ?_, by simp⟩, ?_⟩
    · obtain ⟨w, -, hw⟩ := exists_comb hgt (Pi.single k 1)
      refine ⟨w, (key _ w hw).2 fun i => ?_, hw⟩
      by_cases hi : i = k
      · subst hi; simp
      · simp [hi]
    · rintro r ⟨cf, h0, -, ⟨w, hw, hc⟩, rfl⟩
      exact one_le_inv₀ (norm_pos_iff.2 h0) |>.2 ((key cf w hc).1 hw k)
  have h2 := grNorm_tri (Λ := Λ) hf (d := fun i => δ * (M * Q) i i) (fun i => mul_ne_zero hδ (hN0 i))
    (fun i => ⟨_, rfl, fun k hk => by rw [hN hk, mul_zero], hg i⟩) k
  rw [h1, norm_mul] at h2
  exact eq_inv_of_mul_eq_one_right h2.symm

theorem tri_mul_diag {R : Type} [CommRing R] {m : ℕ} {A B : Matrix (Fin m) (Fin m) R} (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (k : Fin m) : (A * B) k k = A k k * B k k := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single k (fun j _ hj => ?_) (by simp)
  rcases lt_or_gt_of_ne hj with hj | hj
  · rw [hA (show id j < id k from hj), zero_mul]
  · rw [hB (show id k < id j from hj), mul_zero]

theorem exists_tri {S K R : Type} [CommRing S] [Field K] [CommRing R] (ι : S →+* K) (hι : Function.Injective ι)
    (ev : R →+* S) {x : Sp S ⟶ X} {m : ℕ} {f u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    (hf : ∀ k, IsTanAtG t x (f k)) (hi : Indep t x f)
    (hiK : Indep t (spMap ι ≫ x) fun k => spMap (Formalism.L2.Pj.dualMap ι) ≫ f k) {M M' : Matrix (Fin m) (Fin m) S}
    (hM : ∀ b, IsCombAtG t x f (fun k => M k b) (u b)) (hM' : ∀ b, IsCombAtG t x u (fun k => M' k b) (f b))
    {v : Fin m → (Sp (DualNumber K) ⟶ t.G.left)} {d : Fin m → Kˣ}
    (hv : ∀ i, ∃ cf : Fin m → K, cf i = d i ∧ (∀ k, i < k → cf k = 0) ∧
      IsCombAtG t (spMap ι ≫ x) (fun k => spMap (Formalism.L2.Pj.dualMap ι) ≫ f k) cf (v i))
    (A : Matrix (Fin m) (Fin m) R) (hA : IsUnit A.det) (r : Fin m → Kˣ) (b : Bool)
    (h : ∀ i, cond b
      (∃ (w : Sp (DualNumber K) ⟶ t.G.left) (cf : Fin m → K),
        IsCombAtG t (spMap ι ≫ x) (fun k => spMap (Formalism.L2.Pj.dualMap ι) ≫ u k) (fun c => ι (ev (A c i))) w ∧
          IsCombAtG t (spMap ι ≫ x) v cf w ∧ cf i = ((r i)⁻¹ : Kˣ) ∧ ∀ k, i < k → cf k = 0)
      (∀ (k : Fin m) (e : Fin m → K), IsCombAtG t (spMap ι ≫ x) (fun k => spMap (Formalism.L2.Pj.dualMap ι) ≫ u k) e (v k) →
        ((k : ℕ) + i + 1 < m → ∑ c, ι (ev (A c i)) * e c = 0) ∧
        ((k : ℕ) + i + 1 = m → ∑ c, ι (ev (A c i)) * e c = ((r i)⁻¹ : Kˣ)))) :
    ∃ Q Q' : Matrix (Fin m) (Fin m) R, Q * Q' = 1 ∧ (M * Q.map ev).BlockTriangular id ∧ IsUnit (M * Q.map ev).det ∧
      ∀ k, ι ((M * Q.map ev) k k) = d k * (cond b (r k)⁻¹ (r k.rev) : Kˣ) := by
  have hu := fun b => comb_tan hf (hM b)
  have hfK := fun k => GlobalTheory.FactorDepth.isTanAtG_map t ι (hf k)
  have huK := fun k => GlobalTheory.FactorDepth.isTanAtG_map t ι (hu k)
  have hMM : M * M' = 1 := by
    ext a c
    have := congrFun (hi _ _ _ (tanLinG f hf u M _ _ hM (hM' c)) (isCombAtG_single t x hf c)) a
    rw [Matrix.one_apply, ← Pi.single_apply c (1 : S) a, ← this]
    rfl
  have hMd : IsUnit M.det := Matrix.isUnit_det_of_right_inverse hMM
  choose T hT1 hT2 hT3 using hv
  let T' : Matrix (Fin m) (Fin m) K := fun j i => T i j
  have hT' : T'.BlockTriangular id := fun j k hk => hT2 k j hk
  have dm : ∀ B : Matrix (Fin m) (Fin m) R, IsUnit B.det → IsUnit (M * B.map ev).det := fun B hB => by
    rw [Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hMd.mul (hB.map _)
  cases b with
  | true =>
    have key : ∀ i, (∀ k, i < k → ι ((M * A.map ev) k i) = 0) ∧ ι ((M * A.map ev) i i) = d i * ((r i)⁻¹ : Kˣ) := fun i => by
      obtain ⟨w, cf, h1, h2, h3, h4⟩ := h i
      have e1 := hiK _ _ _ (tanLinG _ hfK _ (M.map ι) _ w (fun c => GlobalTheory.LatDRFree.comb_map t ι (hM c)) h1)
        (tanLinG _ hfK v T' cf w hT3 h2)
      have e2 : ∀ k, ι ((M * A.map ev) k i) = T'.mulVec cf k := fun k => by
        rw [← e1, Matrix.mul_apply, map_sum]
        simp only [map_mul]
        rfl
      obtain ⟨e3, e4⟩ := tri_mulVec hT' h4
      exact ⟨fun k hk => (e2 k).trans (e3 k hk), by rw [e2, e4, h3, ← hT1]⟩
    exact ⟨A, A⁻¹, A.mul_nonsing_inv hA, fun k i hk => hι (((key i).1 k hk).trans (map_zero ι).symm), dm A hA,
      fun k => (key k).2⟩
  | false =>
    let Q' : Matrix (Fin m) (Fin m) R := A.transpose.submatrix Fin.rev id
    have hQ' : IsUnit Q'.det := by
      have := Matrix.det_permute Fin.revPerm A.transpose
      rw [show Q' = A.transpose.submatrix Fin.revPerm id from rfl, this, Matrix.det_transpose]
      exact ((Equiv.Perm.sign Fin.revPerm).isUnit.map (Int.castRingHom R)).mul hA
    let P : Matrix (Fin m) (Fin m) S := Q'.map ev * M'
    have key : ∀ i k, (P.map ι * T') i k = ∑ c, ι (ev (A c i.rev)) * (M'.map ι).mulVec (T k) c := fun i k => by
      rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply]
      rfl
    have hc := fun i k => h i k _ (tanLinG _ huK _ (M'.map ι) _ _ (fun c => GlobalTheory.LatDRFree.comb_map t ι (hM' c)) (hT3 k))
    have hB : (P.map ι * T').BlockTriangular id := fun i k hk => by
      rw [key]
      refine (hc _ k).1 ?_
      have : (k : ℕ) < i := hk
      have := i.2
      rw [Fin.val_rev]; omega
    have hTd : IsUnit T'.det := by
      rw [Matrix.det_of_isUpperTriangular hT']
      exact (Finset.prod_ne_zero_iff.2 fun k _ => (hT1 k).trans_ne (d k).ne_zero).isUnit
    have hPK : (P.map ι).BlockTriangular id := by
      let _ := Matrix.invertibleOfIsUnitDet T' hTd
      have := hB.mul (Matrix.blockTriangular_inv_of_blockTriangular hT')
      rwa [Matrix.mul_nonsing_inv_cancel_right _ _ hTd] at this
    have hP : P.BlockTriangular id := fun i k hk => hι ((hPK hk).trans (map_zero ι).symm)
    have hPN : P * (M * Q'⁻¹.map ev) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc M', mul_eq_one_comm.1 hMM, Matrix.one_mul, ← Matrix.map_mul,
        Q'.mul_nonsing_inv hQ', Matrix.map_one _ (map_zero ev) (map_one ev)]
    have hN : (M * Q'⁻¹.map ev).BlockTriangular id := by
      let _ := invertibleOfRightInverse _ _ hPN
      rw [← Matrix.inv_eq_right_inv hPN]
      exact Matrix.blockTriangular_inv_of_blockTriangular hP
    refine ⟨Q'⁻¹, Q', Q'.nonsing_inv_mul hQ', hN, dm _ (Q'.isUnit_nonsing_inv_det hQ'), fun k => ?_⟩
    have e1 := tri_mul_diag hPK hT' k
    rw [key, (hc _ k).2 (by have := k.2; rw [Fin.val_rev]; omega), show T' k k = d k from hT1 k] at e1
    have e2 := congrArg ι (tri_mul_diag hP hN k)
    rw [hPN, Matrix.one_apply_eq, map_one, map_mul] at e2
    rw [Matrix.map_apply, Units.val_inv_eq_inv_val] at e1
    have h0 := (r k.rev).ne_zero
    have e3 : ι (P k k) * (d k * r k.rev) = 1 := by rw [← mul_assoc, ← e1, inv_mul_cancel₀ h0]
    calc _ = ι ((M * Q'⁻¹.map ev) k k) * (ι (P k k) * (d k * r k.rev)) := by rw [e3, mul_one]
      _ = _ := by rw [← mul_assoc, mul_comm _ (ι (P k k)), ← e2, one_mul]; rfl

end Alg

theorem exists_lifts {X : Scheme.{0}} {M : X.Modules} {n : ℕ} (fl : Vert.Flag M n) (x : X)
    (c : ∀ k, Chart (fl.gr k) 1) (hc : ∀ k, x ∈ (c k).U) (V : X.Opens) (hV : x ∈ V) :
    ∃ (W : X.Opens) (_ : x ∈ W) (_ : W ≤ V) (hW : ∀ k, W ≤ (c k).U) (t : ∀ k : Fin n, Γ(fl.F k.succ, W)),
      (∀ k, (fl.π k).app W (t k) = Twist.resM _ (hW k) ((c k).e 0)) ∧
        VB.IsFrame fun k => (fl.ι k.succ).app W (t k) := by
  choose U hU hx b hb using fun k => exists_app_eq_of_epi (fl.π k) ((c k).e 0) (hc k)
  obtain ⟨V₀, e₀, hV₀, he₀⟩ := fl.isVB 0 x
  obtain ⟨W, hxW, hWV, hW₀, hW⟩ : ∃ W : X.Opens, x ∈ W ∧ W ≤ V ∧ W ≤ V₀ ∧ ∀ k, W ≤ U k :=
    ⟨V ⊓ V₀ ⊓ Finset.univ.inf U, ⟨⟨hV, hV₀⟩, by
      rw [TopologicalSpace.Opens.coe_finset_inf]
      simpa using hx⟩, inf_le_left.trans inf_le_left, inf_le_left.trans inf_le_right,
      fun k => inf_le_right.trans (Finset.inf_le (Finset.mem_univ k))⟩
  let t : ∀ k : Fin n, Γ(fl.F k.succ, W) := fun k => Twist.resM _ (hW k) (b k)
  have ht : ∀ k, (fl.π k).app W (t k) = Twist.resM _ ((hW k).trans (hU k)) ((c k).e 0) := fun k => by
    rw [Twist.app_resM, hb, Twist.resM_resM]
  refine ⟨W, hxW, hWV, fun k => (hW k).trans (hU k), t, ht, ?_⟩
  have key : ∀ l : Fin (n + 1), ∃ s : Fin l → Γ(fl.F l, W), VB.IsFrame s ∧
      ∀ j, (fl.ι l).app W (s j) = (fl.ι (Fin.castLE l.is_le j).succ).app W (t (Fin.castLE l.is_le j)) := fun l => by
    induction l using Fin.induction with
    | zero => exact ⟨_, he₀.res hW₀, fun j => j.elim0⟩
    | succ i ih =>
      obtain ⟨s, hs, hj⟩ := ih
      let S := ShortComplex.mk (fl.step i) (fl.π i) (Limits.cokernel.condition _)
      have hS : S.Exact := ShortComplex.exact_cokernel (fl.step i)
      have hbf : VB.IsFrame fun _ : Fin 1 => S.g.app W (t i) := by
        convert (c i).isFrame.res ((hW i).trans (hU i)) using 1
        funext j
        rw [Fin.fin_one_eq_zero j]
        exact ht i
      refine ⟨_, FlagZ.Loc.isFrame_snoc_of_exact (S := S) hS s (t i) hs hbf, fun j => ?_⟩
      refine Fin.lastCases (n := i) ?_ (fun j => ?_) j
      · exact congrArg _ (Fin.snoc_last _ _)
      · refine (congrArg _ (Fin.snoc_castSucc _ _ _)).trans ?_
        exact ((QCoh.app_app _ _ _ _).trans (by rw [fl.step_ι])).trans (hj j)
  obtain ⟨s, hs, hj⟩ := key (Fin.last n)
  have e : (fun k => (fl.ι k.succ).app W (t k)) = fun k : Fin n => (fl.ι (Fin.last n)).app W (s k) :=
    _root_.funext fun k => (hj k).symm
  rw [e]
  exact hs.map_iso (fl.ι (Fin.last n))

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

attribute [local instance] Over.cartesianMonoidalCategory in

theorem eig_comb {K : Type} [CommRing K] {φ : c.F →+* K} {x : Sp K ⟶ Z.X} {τ : E →+* ℂ} {m : ℕ}
    {u : Fin m → (Sp (DualNumber K) ⟶ Z.t.G.left)} (hu : ∀ k, IsEigTan Z φ x τ (u k)) {cf : Fin m → K}
    {w : Sp (DualNumber K) ⟶ Z.t.G.left} (h : IsCombAtG Z.t x u cf w) : IsEigTan Z φ x τ w := by
  refine ⟨comb_tan (fun k => (hu k).1) h, fun a => ?_⟩
  have := Z.t.act.hom a
  rw [← (isCombAtG_iff Z.t _ (fun j => ovT (hu j).1) cf w).1 h]
  exact congrArg (fun q => q.left) (combT_eig _ (fun j => ovT (hu j).1) (Z.t.act.act a) _
    (fun j => Over.OverMorphism.ext ((hu j).2 a)) cf)

theorem indep_of_eig {K : Type} [CommRing K] {φ : c.F →+* K} {x : Sp K ⟶ Z.X} {τ : E →+* ℂ} {m : ℕ}
    {u : Fin m → (Sp (DualNumber K) ⟶ Z.t.G.left)} (hu : IsEigBasis Z φ x τ u) : Indep Z.t x u :=
  fun _ _ w h h' => (hu.2 w (eig_comb hu.1 h)).unique h h'

theorem eigBasis_bc {R K : Type} [CommRing R] [CommRing K] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x)
    (ψ : R →+* K) (τ : E →+* ℂ) :
    IsEigBasis Z (ψ.comp φ) (spMap ψ ≫ x) τ fun i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ i :=
  have h := GlobalTheory.ShFam.Pad.isFrame_baseChange E H Dw l c Z.X Z.t _ K _ ψ _ f.v
    ⟨fun τ i => ⟨f.tan τ i, f.eig τ i⟩, f.basis⟩
  ⟨fun i => h.1 τ i, fun w hw => h.2 τ w hw.1 hw.2⟩

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) {Y : Scheme.{0}}
    (w : Sp (DualNumber R) ⟶ Y) : spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (Formalism.L2.Pj.dualMap φ) ≫ w =
      spMap (Formalism.L2.Pj.dualMap (ψ.comp φ)) ≫ w := by
  rw [← Category.assoc, sp_comp]
  congr 2
  refine RingHom.ext fun r => ?_
  ext <;> simp [Formalism.L2.Pj.dualMap]

theorem sp_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) {Y : Scheme.{0}}
    (w : Sp R ⟶ Y) : spMap ψ ≫ spMap φ ≫ w = spMap (ψ.comp φ) ≫ w := by
  rw [← Category.assoc, sp_comp]

theorem le_pre {R : Type} [CommRing R] [IsLocalRing R] {Y : Scheme.{0}} (x : Sp R ⟶ Y) (U : Y.Opens)
    (h : x (IsLocalRing.closedPoint R) ∈ U) : ⊤ ≤ x ⁻¹ᵁ U :=
  ((IsLocalRing.closedPoint_mem_iff (R := R) (x ⁻¹ᵁ U)).1 h).ge

theorem evalPt_eq {R R' : Type} [CommRing R] [CommRing R'] {Y : Scheme.{0}} (ψ : R →+* R') (x : Sp R ⟶ Y)
    {x' : Sp R' ⟶ Y} (e : x' = spMap ψ ≫ x) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x' ⁻¹ᵁ U) (a : Γ(Y, U)) :
    TangentOrigin.evalPt x' U h' a = ψ (TangentOrigin.evalPt x U h a) := by
  subst e
  exact TangentOrigin.evalPt_spMap_comp ψ x U h h' a

variable {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (C : FlagCpt Z e)

theorem lnStep_core {Bs Bg Y₀ G : Scheme.{0}} [IsIntegral G] {jB : Bg ⟶ Bs} {πB : Bg ⟶ gen Z} {M : Bs.Modules} {m : ℕ}
    {τ : E →+* ℂ} (hr : m = Dw.mult τ) (b : Bool) {u : FrAssign Z M m jB} (hu : IsLieFrames Z e jB πB M m τ (!b) u)
    {π₀ : Y₀ ⟶ Bs} {j : G ⟶ Y₀}
    {πG : G ⟶ C.Y.X} {φ : C.Y.Fn →+* G.functionField} {jG : G ⟶ Bg}
    (h₁ : jG ≫ jB = j ≫ π₀) (h₂ : jG ≫ πB = πG ≫ C.π) {V : Bs.Opens} {f : Fin m → Γ(M, V)} (hf : VB.IsFrame f)
    {W : Y₀.Opens} (hWV : W ≤ π₀ ⁻¹ᵁ V) (A : Matrix (Fin m) (Fin m) Γ(Y₀, W)) (hA : IsUnit A.det)
    (r : Fin m → G.functionFieldˣ) (hx : ⊤ ≤ (FlagCov.genPt G ≫ j) ⁻¹ᵁ W)
    (hxV : ⊤ ≤ ((FlagCov.genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V)
    (h : ∀ i : Fin m,
      let aG : Fin m → G.functionField := fun c => TangentOrigin.evalPt (FlagCov.genPt G ≫ j) W hx (A c i)
      let uu := u V f hf G.functionField (FlagCov.genPt G ≫ jG) hxV
      let v : Fin (Dw.mult τ) → (Sp (DualNumber G.functionField) ⟶ Z.t.G.left) :=
        fun k => spMap (Formalism.L2.Pj.dualMap φ) ≫ C.f0.v τ k
      let x := FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z
      cond b
        (∃ (w : Sp (DualNumber G.functionField) ⟶ Z.t.G.left) (cf : Fin (Dw.mult τ) → G.functionField),
          IsCombAtG Z.t x uu aG w ∧ IsCombAtG Z.t x v cf w ∧
            cf (Fin.cast hr i) = ((r i)⁻¹ : G.functionFieldˣ) ∧ ∀ k, Fin.cast hr i < k → cf k = 0)
        (∀ (k : Fin (Dw.mult τ)) (d : Fin m → G.functionField), IsCombAtG Z.t x uu d (v k) →
          ((k : ℕ) + i + 1 < m → ∑ b, aG b * d b = 0) ∧
          ((k : ℕ) + i + 1 = m → ∑ b, aG b * d b = ((r i)⁻¹ : G.functionFieldˣ))))
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (ε : Ext v)
    (z : Sp (AlgebraicClosure F) ⟶ G) (hz : (z ≫ πG) ≫ C.Y.str = spMap (algebraMap F (AlgebraicClosure F)))
    (yt : Sp ε.O ⟶ Y₀) (hyt : spMap ε.O.subtype ≫ yt = z ≫ j) (hW : ⊤ ≤ yt ⁻¹ᵁ W) (k : Fin m)
    {S R : Type} [CommRing S] [CommRing R] {s : Sp S ⟶ G} {ι : S →+* G.functionField} (hι : Function.Injective ι)
    {χ : S →+* AlgebraicClosure F} {σ : R →+* S} {al : R →+* C.Y.Fn} {χ' : R →+* AlgebraicClosure F} {y : Sp R ⟶ C.Y.X}
    {φ₁ : c.F →+* R} (fr : EigFrame Z φ₁ (y ≫ C.π ≫ genι Z)) {d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ}
    (hT : fr.Tri al C.f0 d) (a₁ : spMap χ ≫ s = z) (a₂ : spMap ι ≫ s = FlagCov.genPt G) (a₃ : spMap σ ≫ y = s ≫ πG)
    (a₄ : spMap al ≫ y = genericPt C.Y) (b₁ : χ.comp σ = χ') (b₂ : ι.comp σ = φ.comp al)
    (c₁ : y ≫ C.π ≫ genStr Z = spMap φ₁) (hsW : ⊤ ≤ (s ≫ j) ⁻¹ᵁ W)
    {Ω : Type} [NontriviallyNormedField Ω] [IsUltrametricDist Ω] (io : AlgebraicClosure F →+* Ω)
    (hio : ∀ a, ‖io a‖ ≤ 1 ↔ a ∈ ε.O) {p : ℕ} (hp : 0 < p) (kd : Bool) (hzV : ⊤ ≤ ((z ≫ jG) ≫ jB) ⁻¹ᵁ V) {δ : Ω}
    (hδ : ‖δ‖ = (p : ℝ) ^ (-(if kd = true ∧ τ (H.rt : E) = H.rt0 then vDiff E p else 0)))
    (hΛ : ∀ w, IsEigTan Z ((io.comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
        (spMap io ≫ (z ≫ jG) ≫ πB ≫ genι Z) τ w →
      ((∃ a : Fin m → Ω, (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG Z.t (spMap io ≫ (z ≫ jG) ≫ πB ≫ genι Z)
          (fun i => spMap (Formalism.L2.Pj.dualMap io) ≫ u V f hf _ (z ≫ jG) hzV i) a w) ↔
        spMap (epsMul δ) ≫ w ∈ Pad.lat Z.t p (spMap io ≫ (z ≫ jG) ≫ πB ≫ genι Z) kd))
    (ψ' : R →+* Ω) (hψ : ∀ a, ψ' a = io (χ' a)) :
    ∃ n : Sˣ, ι n.1 = φ (d τ (Fin.cast hr k) : C.Y.Fnˣ) * (cond b (r k)⁻¹ (r k.rev) : G.functionFieldˣ) ∧
      lnStep Z.t (spMap ψ' ≫ y ≫ C.π ≫ genι Z)
        (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ') ≫ fr.v τ i) p kd
          (.inl (τ, k)) = -Real.log ‖io (χ n.1)‖ := by
  subst hr
  have a₅ : spMap χ' ≫ y = z ≫ πG := by rw [← b₁, ← sp_comp', a₃, reassoc_of% a₁]
  have hzW : ⊤ ≤ (z ≫ j) ⁻¹ᵁ W := hyt ▸ fun q _ => hW (Set.mem_univ (spMap ε.O.subtype q))
  have hV : ∀ {K : Type} [CommRing K] (w : Sp K ⟶ G), ⊤ ≤ (w ≫ j) ⁻¹ᵁ W → ⊤ ≤ ((w ≫ jG) ≫ jB) ⁻¹ᵁ V := fun w hy => by
    rw [Category.assoc, h₁, ← Category.assoc]
    exact fun q _ => hWV (hy (Set.mem_univ q))
  let x := spMap σ ≫ y ≫ C.π ≫ genι Z
  have d₀ : ∀ {T : Scheme.{0}} (g : gen Z ⟶ T),
      (s ≫ jG) ≫ πB ≫ g = spMap σ ≫ y ≫ C.π ≫ g := fun g => by
    rw [Category.assoc, reassoc_of% h₂, reassoc_of% a₃]
  have hub := hu.1 V f hf S (s ≫ jG) (hV s hsW) ((σ.comp φ₁).comp e.toRingHom) (by
    rw [d₀, reassoc_of% c₁, sp_comp', sp_comp])
  rw [d₀, show ((σ.comp φ₁).comp e.toRingHom).comp e.symm.toRingHom = σ.comp φ₁ from RingHom.ext fun a => by simp] at hub
  have nat : ∀ {K : Type} [CommRing K] (ψ : S →+* K) (y : Sp K ⟶ G) (_ : spMap ψ ≫ s = y) (hy),
      u V f hf K (y ≫ jG) hy = fun i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ u V f hf S (s ≫ jG) (hV s hsW) i := by
    rintro K _ ψ _ rfl hy
    exact _root_.funext fun i => hu.2.2 V f hf S K ψ (s ≫ jG) _ hy i
  generalize u V f hf S (s ≫ jG) (hV s hsW) = uS at hub nat
  have hfb := eigBasis_bc fr σ τ
  choose Mc hM using fun i => (hfb.2 _ (hub.1 i)).exists
  choose Mc' hM' using fun i => (hub.2 _ (hfb.1 i)).exists
  have hiK : ∀ {K : Type} [CommRing K] (ψ : S →+* K), IsEigBasis Z ((ψ.comp σ).comp φ₁) (spMap ψ ≫ x) τ fun k =>
      spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (Formalism.L2.Pj.dualMap σ) ≫ fr.v τ k := fun ψ => by
    simp only [x, dual_comp]
    rw [sp_comp']
    exact eigBasis_bc fr _ τ
  have e₁ : FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z = spMap ι ≫ x := by
    rw [← a₂, show x = _ from (d₀ _).symm]; simp only [Category.assoc]
  obtain ⟨Q, Q', hQ, hN, hdet, hd⟩ := exists_tri ι hι (TangentOrigin.evalPt (s ≫ j) W hsW) (fun k => (hfb.1 k).1)
    (indep_of_eig hfb) (indep_of_eig (hiK ι)) (M := fun a b => Mc b a) (M' := fun a b => Mc' b a) hM hM'
    (v := fun k => spMap (Formalism.L2.Pj.dualMap φ) ≫ C.f0.v τ k) (d := fun k => Units.map φ.toMonoidHom (d τ k))
    (fun i => by
      obtain ⟨cf, g₁, g₂, g₃⟩ := hT.2.2 τ i
      refine ⟨fun k => φ (cf k), congrArg φ g₁, fun k hk => (congrArg φ (g₂ k hk)).trans (map_zero φ), ?_⟩
      have g₄ := GlobalTheory.LatDRFree.comb_map Z.t φ g₃
      simp only [dual_comp, x] at g₄ ⊢
      rw [sp_comp', b₂, ← sp_comp', reassoc_of% a₄]
      exact g₄) A hA r b (fun i => by
      have g := h i
      simp only [e₁, nat ι _ a₂, evalPt_eq ι (s ≫ j) (x' := FlagCov.genPt G ≫ j) (by rw [← a₂, Category.assoc]) W hsW] at g
      exact g)
  have hun : ∀ k, IsUnit ((Matrix.of (fun a b => Mc b a) * Q.map (TangentOrigin.evalPt (s ≫ j) W hsW)) k k) := fun k => by
    rw [Matrix.det_of_isUpperTriangular hN] at hdet
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => (Matrix.of (fun a b => Mc b a) *
      Q.map (TangentOrigin.evalPt (s ≫ j) W hsW)) i i) (Finset.mem_univ k)) hdet
  refine ⟨(hun k).unit, hd k, ?_⟩
  let ψ := io.comp χ
  have e₂ : spMap io ≫ (z ≫ jG) ≫ πB ≫ genι Z = spMap ψ ≫ x := by
    rw [show x = _ from (d₀ _).symm, ← sp_comp']
    simp only [Category.assoc, reassoc_of% a₁]
  have e₃ : ((io.comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom) = (ψ.comp σ).comp φ₁ := by
    have : algebraMap F (AlgebraicClosure F) = (χ'.comp φ₁).comp e.toRingHom := EigLoc.spMap_inj (by
      rw [← sp_comp, ← sp_comp, ← c₁, ← hz, ← C.π_str]
      simp only [Category.assoc, reassoc_of% a₅])
    rw [this, ← b₁]
    refine RingHom.ext fun a => ?_
    change io (χ (σ (φ₁ (e (e.symm a))))) = io (χ (σ (φ₁ a)))
    rw [e.apply_symm_apply]
  have e₄ : ψ' = ψ.comp σ := RingHom.ext fun a => by rw [hψ, ← b₁]; rfl
  rw [e₂, e₃, nat χ z a₁] at hΛ
  simp only [dual_comp] at hΛ
  have hint : ∀ a, ‖ψ (TangentOrigin.evalPt (s ≫ j) W hsW a)‖ ≤ 1 := fun a => by
    have g₁ := evalPt_eq χ (s ≫ j) (x' := z ≫ j) (by rw [reassoc_of% a₁]) W hsW hzW a
    have g₂ := evalPt_eq ε.O.subtype yt hyt.symm W hW hzW a
    exact (hio _).2 (g₁ ▸ g₂ ▸ (TangentOrigin.evalPt yt W hW a).2)
  have hδ0 : 0 < ‖δ‖ := hδ ▸ Real.rpow_pos_of_pos (by exact_mod_cast hp) _
  have mm : (Matrix.of fun a b => Mc b a).map ψ * (Q.map (TangentOrigin.evalPt (s ≫ j) W hsW)).map ψ =
      (Matrix.of (fun a b => Mc b a) * Q.map (TangentOrigin.evalPt (s ≫ j) W hsW)).map ψ := Matrix.map_mul.symm
  have hg := grNorm_of_tri (Λ := Pad.lat Z.t p (spMap ψ ≫ x) kd) (fun k => ((hiK ψ).1 k).1)
    (indep_of_eig (hiK ψ)) (M := (Matrix.of fun a b => Mc b a).map ψ)
    (Q := (Q.map (TangentOrigin.evalPt (s ≫ j) W hsW)).map ψ)
    (Q' := (Q'.map (TangentOrigin.evalPt (s ≫ j) W hsW)).map ψ)
    (fun b => GlobalTheory.LatDRFree.comb_map Z.t ψ (hM b)) (fun _ _ => hint _) (fun _ _ => hint _)
    (by rw [← Matrix.map_mul, ← Matrix.map_mul, hQ, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [mm]; exact fun a b hab => (congrArg ψ (hN hab)).trans (map_zero ψ))
    (fun k => by rw [mm]; exact ((hun k).map ψ).ne_zero) (norm_pos_iff.1 hδ0)
    (fun cf w hw => hΛ w (eig_comb (hiK ψ).1 hw)) k
  rw [mm] at hg
  simp only [dual_comp, x] at hg
  rw [sp_comp', ← e₄] at hg
  have hn0 : ‖ψ ((Matrix.of (fun a b => Mc b a) * Q.map (TangentOrigin.evalPt (s ≫ j) W hsW)) k k)‖ ≠ 0 :=
    norm_ne_zero_iff.2 ((hun k).map ψ).ne_zero
  simp only [lnStep, dif_pos k.2]
  refine (congrArg (fun r => Real.log r - _) hg).trans ?_
  rw [Matrix.map_apply, Real.log_inv, Real.log_mul hδ0.ne' hn0, hδ, Real.log_rpow (by exact_mod_cast hp)]
  change _ = -Real.log ‖ψ ((Matrix.of (fun a b => Mc b a) * Q.map (TangentOrigin.evalPt (s ≫ j) W hsW)) k k)‖
  split_ifs <;> ring

theorem lnStep_padic {Bs Bg Y₀ G : Scheme.{0}} [IsIntegral G] {jB : Bg ⟶ Bs} {πB : Bg ⟶ gen Z} {M : Bs.Modules} {m : ℕ}
    {τ : E →+* ℂ} (hr : m = Dw.mult τ) (b : Bool) {u : FrAssign Z M m jB} (hu : IsLieFrames Z e jB πB M m τ (!b) u)
    {π₀ : Y₀ ⟶ Bs} {j : G ⟶ Y₀}
    {πG : G ⟶ C.Y.X} {φ : C.Y.Fn →+* G.functionField} {jG : G ⟶ Bg}
    (h₁ : jG ≫ jB = j ≫ π₀) (h₂ : jG ≫ πB = πG ≫ C.π) {V : Bs.Opens} {f : Fin m → Γ(M, V)} (hf : VB.IsFrame f)
    {W : Y₀.Opens} (hWV : W ≤ π₀ ⁻¹ᵁ V) (A : Matrix (Fin m) (Fin m) Γ(Y₀, W)) (hA : IsUnit A.det)
    (r : Fin m → G.functionFieldˣ) (hx : ⊤ ≤ (FlagCov.genPt G ≫ j) ⁻¹ᵁ W)
    (hxV : ⊤ ≤ ((FlagCov.genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V)
    (h : ∀ i : Fin m,
      let aG : Fin m → G.functionField := fun c => TangentOrigin.evalPt (FlagCov.genPt G ≫ j) W hx (A c i)
      let uu := u V f hf G.functionField (FlagCov.genPt G ≫ jG) hxV
      let v : Fin (Dw.mult τ) → (Sp (DualNumber G.functionField) ⟶ Z.t.G.left) :=
        fun k => spMap (Formalism.L2.Pj.dualMap φ) ≫ C.f0.v τ k
      let x := FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z
      cond b
        (∃ (w : Sp (DualNumber G.functionField) ⟶ Z.t.G.left) (cf : Fin (Dw.mult τ) → G.functionField),
          IsCombAtG Z.t x uu aG w ∧ IsCombAtG Z.t x v cf w ∧
            cf (Fin.cast hr i) = ((r i)⁻¹ : G.functionFieldˣ) ∧ ∀ k, Fin.cast hr i < k → cf k = 0)
        (∀ (k : Fin (Dw.mult τ)) (d : Fin m → G.functionField), IsCombAtG Z.t x uu d (v k) →
          ((k : ℕ) + i + 1 < m → ∑ b, aG b * d b = 0) ∧
          ((k : ℕ) + i + 1 = m → ∑ b, aG b * d b = ((r i)⁻¹ : G.functionFieldˣ))))
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (ε : Ext v)
    (z : Sp (AlgebraicClosure F) ⟶ G) (hz : (z ≫ πG) ≫ C.Y.str = spMap (algebraMap F (AlgebraicClosure F)))
    (yt : Sp ε.O ⟶ Y₀) (hyt : spMap ε.O.subtype ≫ yt = z ≫ j) (hW : ⊤ ≤ yt ⁻¹ᵁ W) (k : Fin m)
    {S R : Type} [CommRing S] [CommRing R] {s : Sp S ⟶ G} {ι : S →+* G.functionField} (hι : Function.Injective ι)
    {χ : S →+* AlgebraicClosure F} {σ : R →+* S} {al : R →+* C.Y.Fn} {χ' : R →+* AlgebraicClosure F} {y : Sp R ⟶ C.Y.X}
    {φ₁ : c.F →+* R} (fr : EigFrame Z φ₁ (y ≫ C.π ≫ genι Z)) {d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ}
    (hT : fr.Tri al C.f0 d) (a₁ : spMap χ ≫ s = z) (a₂ : spMap ι ≫ s = FlagCov.genPt G) (a₃ : spMap σ ≫ y = s ≫ πG)
    (a₄ : spMap al ≫ y = genericPt C.Y) (b₁ : χ.comp σ = χ') (b₂ : ι.comp σ = φ.comp al)
    (c₁ : y ≫ C.π ≫ genStr Z = spMap φ₁) (hsW : ⊤ ≤ (s ≫ j) ⁻¹ᵁ W)
    {p : ℕ} {i : Fact p.Prime} (i' : Fact p.Prime) (kd : Bool) (hzV : ⊤ ≤ ((z ≫ jG) ≫ jB) ⁻¹ᵁ V)
    (hΛ : haveI := i
      ∃ δ : ℂ_[p], ‖δ‖ = (p : ℝ) ^ (-(if kd = true ∧ τ (H.rt : E) = H.rt0 then vDiff E p else 0)) ∧
        ∀ w, IsEigTan Z (((ioOf p ε).comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
            (spMap (ioOf p ε) ≫ (z ≫ jG) ≫ πB ≫ genι Z) τ w →
          ((∃ a : Fin m → ℂ_[p], (∀ i, ‖a i‖ ≤ 1) ∧
              IsCombAtG Z.t (spMap (ioOf p ε) ≫ (z ≫ jG) ≫ πB ≫ genι Z)
                (fun i => spMap (Formalism.L2.Pj.dualMap (ioOf p ε)) ≫ u V f hf _ (z ≫ jG) hzV i) a w) ↔
            spMap (epsMul δ) ≫ w ∈ Pad.lat Z.t p (spMap (ioOf p ε) ≫ (z ≫ jG) ≫ πB ≫ genι Z) kd))
    (hio : ∀ a, ‖ioOf p ε a‖ ≤ 1 ↔ a ∈ ε.O) (ψ' : R →+* ℂ_[p]) (hψ : ∀ a, ψ' a = ioOf p ε (χ' a)) :
    ∃ n : Sˣ, ι n.1 = φ (d τ (Fin.cast hr k) : C.Y.Fnˣ) * (cond b (r k)⁻¹ (r k.rev) : G.functionFieldˣ) ∧
      lnStep Z.t (spMap ψ' ≫ y ≫ C.π ≫ genι Z)
        (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ') ≫ fr.v τ i) p kd
          (.inl (τ, k)) = -Real.log ‖ioOf p ε (χ n.1)‖ := by
  obtain rfl : i = i' := rfl
  obtain ⟨δ, hδ, hΛ⟩ := hΛ
  exact lnStep_core C hr b hu h₁ h₂ hf hWV A hA r hx hxV h ε z hz yt hyt hW k hι fr hT a₁ a₂ a₃ a₄ b₁ b₂ c₁ hsW _ hio
    i.out.pos kd hzV hδ hΛ ψ' hψ

theorem symLog_eq {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (hp : (resP v).Prime) (ε : Ext v) (y : AlgPt C.Y)
    (kind : ℕ → Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : LineNorm.symLog C kind st v ε y = haveI := Fact.mk hp
    let ψ : C.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
    (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
      lnStep Z.t (spMap ψ ≫ stalkPt C.Y (below y.1) ≫ C.π ≫ genι Z)
        (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ (C.gr_spec (below y.1)).choose_spec.choose.v τ i) (resP v)
        (kind (resP v)) st := dif_pos hp

theorem lnStep_eq {Bs Bg Y₀ G : Scheme.{0}} [IsIntegral G] {jB : Bg ⟶ Bs} {πB : Bg ⟶ gen Z} {M : Bs.Modules} {m : ℕ}
    {τ : E →+* ℂ} (hr : m = Dw.mult τ) (b : Bool) {u : FrAssign Z M m jB} (hu : IsLieFrames Z e jB πB M m τ (!b) u)
    {kind : ℕ → Bool} (hl : IsLieLat Z e jB πB M m τ kind (fun _ => True) u) {π₀ : Y₀ ⟶ Bs} {j : G ⟶ Y₀}
    {πG : G ⟶ C.Y.X} {φ : C.Y.Fn →+* G.functionField}
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ C.Y.X.fromSpecStalk (genericPoint C.Y.X)) {jG : G ⟶ Bg}
    (h₁ : jG ≫ jB = j ≫ π₀) (h₂ : jG ≫ πB = πG ≫ C.π) {V : Bs.Opens} {f : Fin m → Γ(M, V)} (hf : VB.IsFrame f)
    {W : Y₀.Opens} (hWV : W ≤ π₀ ⁻¹ᵁ V) (A : Matrix (Fin m) (Fin m) Γ(Y₀, W)) (hA : IsUnit A.det)
    (r : Fin m → G.functionFieldˣ) (hx : ⊤ ≤ (FlagCov.genPt G ≫ j) ⁻¹ᵁ W)
    (hxV : ⊤ ≤ ((FlagCov.genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V)
    (h : ∀ i : Fin m,
      let aG : Fin m → G.functionField := fun c => TangentOrigin.evalPt (FlagCov.genPt G ≫ j) W hx (A c i)
      let uu := u V f hf G.functionField (FlagCov.genPt G ≫ jG) hxV
      let v : Fin (Dw.mult τ) → (Sp (DualNumber G.functionField) ⟶ Z.t.G.left) :=
        fun k => spMap (Formalism.L2.Pj.dualMap φ) ≫ C.f0.v τ k
      let x := FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z
      cond b
        (∃ (w : Sp (DualNumber G.functionField) ⟶ Z.t.G.left) (cf : Fin (Dw.mult τ) → G.functionField),
          IsCombAtG Z.t x uu aG w ∧ IsCombAtG Z.t x v cf w ∧
            cf (Fin.cast hr i) = ((r i)⁻¹ : G.functionFieldˣ) ∧ ∀ k, Fin.cast hr i < k → cf k = 0)
        (∀ (k : Fin (Dw.mult τ)) (d : Fin m → G.functionField), IsCombAtG Z.t x uu d (v k) →
          ((k : ℕ) + i + 1 < m → ∑ b, aG b * d b = 0) ∧
          ((k : ℕ) + i + 1 = m → ∑ b, aG b * d b = ((r i)⁻¹ : G.functionFieldˣ))))
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (hp : (resP v).Prime) (ε : Ext v)
    (z : Sp (AlgebraicClosure F) ⟶ G) (hz : (z ≫ πG) ≫ C.Y.str = spMap (algebraMap F (AlgebraicClosure F)))
    (yt : Sp ε.O ⟶ Y₀) (hyt : spMap ε.O.subtype ≫ yt = z ≫ j) (hW : ⊤ ≤ yt ⁻¹ᵁ W) (k : Fin m) :
    (∀ a : C.Y.X.presheaf.stalk (below (z ≫ πG)), ∃ a' : G.presheaf.stalk (below z),
      algebraMap _ G.functionField a' = φ (algebraMap _ C.Y.X.functionField a) ∧
        (Scheme.stalkClosedPointTo z).hom a' = (Scheme.stalkClosedPointTo (z ≫ πG)).hom a) ∧
    ∃ n : (G.presheaf.stalk (below z))ˣ, algebraMap _ G.functionField n.1 =
        φ ((C.gr_spec (below (z ≫ πG))).choose_spec.choose_spec.choose τ (Fin.cast hr k) : C.Y.Fnˣ) *
          (cond b (r k)⁻¹ (r k.rev) : G.functionFieldˣ) ∧
      haveI := Fact.mk hp
      LineNorm.symLog C kind (.inl (τ, k)) v ε ⟨z ≫ πG, hz⟩ = (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        -Real.log ‖ioOf (resP v) ε ((Scheme.stalkClosedPointTo z).hom n.1)‖ := by
  obtain ⟨hT, -⟩ := (C.gr_spec (below (z ≫ πG))).choose_spec.choose_spec.choose_spec
  obtain ⟨σ, a₃⟩ : ∃ σ : C.Y.X.presheaf.stalk (below (z ≫ πG)) →+* G.presheaf.stalk (below z),
      spMap σ ≫ stalkPt C.Y (below (z ≫ πG)) = G.fromSpecStalk (below z) ≫ πG :=
    ⟨(πG.stalkMap (below z)).hom, Scheme.SpecMap_stalkMap_fromSpecStalk πG⟩
  have a₁ : spMap (Scheme.stalkClosedPointTo z).hom ≫ G.fromSpecStalk (below z) = z :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of _) z
  have a₂ : spMap (algebraMap (G.presheaf.stalk (below z)) G.functionField) ≫ G.fromSpecStalk (below z) =
      FlagCov.genPt G :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes (below z))
  have a₄ : spMap (algebraMap (C.Y.X.presheaf.stalk (below (z ≫ πG))) C.Y.X.functionField) ≫
      stalkPt C.Y (below (z ≫ πG)) = genericPt C.Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes _)
  have a₅ : spMap (Scheme.stalkClosedPointTo (z ≫ πG)).hom ≫ stalkPt C.Y (below (z ≫ πG)) = z ≫ πG :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of _) (z ≫ πG)
  have : Mono (stalkPt C.Y (below (z ≫ πG))) := inferInstanceAs (Mono (C.Y.X.fromSpecStalk _))
  have b₁ : (Scheme.stalkClosedPointTo z).hom.comp σ = (Scheme.stalkClosedPointTo (z ≫ πG)).hom :=
    EigLoc.spMap_inj ((cancel_mono (stalkPt C.Y (below (z ≫ πG)))).1
      ((sp_comp' _ _ _).symm.trans <| (congrArg (_ ≫ ·) a₃).trans <| (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ πG) a₁).trans a₅.symm))
  have b₂ : (algebraMap (G.presheaf.stalk (below z)) G.functionField).comp σ =
      φ.comp (algebraMap (C.Y.X.presheaf.stalk (below (z ≫ πG))) C.Y.X.functionField) :=
    EigLoc.spMap_inj ((cancel_mono (stalkPt C.Y (below (z ≫ πG)))).1
      ((sp_comp' _ _ _).symm.trans <| (congrArg (_ ≫ ·) a₃).trans <| (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ πG) a₂).trans <| φs.trans <| (congrArg (_ ≫ ·) a₄.symm).trans (sp_comp' _ _ _)))
  refine ⟨fun a => ⟨σ a, RingHom.congr_fun b₂ a, RingHom.congr_fun b₁ a⟩, ?_⟩
  have c₁ : stalkPt C.Y (below (z ≫ πG)) ≫ C.π ≫ genStr Z = spMap (C.gr_spec (below (z ≫ πG))).choose :=
    VarFlagSpec.eq_spMap_of_comp (IsFractionRing.injective _ C.Y.X.functionField)
      ((Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) a₄).trans <| (VarFlagSpec.genericPt_genStr C).trans <|
        congrArg spMap hT.2.1)
  have hzW : ⊤ ≤ (z ≫ j) ⁻¹ᵁ W := hyt ▸ fun q _ => hW (Set.mem_univ (spMap ε.O.subtype q))
  have hsW : ⊤ ≤ (G.fromSpecStalk (below z) ≫ j) ⁻¹ᵁ W := le_pre (R := G.presheaf.stalk (below z)) _ _
    ((congrArg (fun q => j q ∈ W) Scheme.fromSpecStalk_closedPoint).mpr
      (hzW (Set.mem_univ (IsLocalRing.closedPoint _))))
  have hzV : ⊤ ≤ ((z ≫ jG) ≫ jB) ⁻¹ᵁ V := by
    rw [Category.assoc, h₁, ← Category.assoc]
    exact fun q _ => hWV (hzW (Set.mem_univ q))
  obtain ⟨hp', hio, -⟩ := ioOf_spec F v ε
  obtain rfl : hp = hp' := rfl
  have hΛ := hl v trivial hp ε (z ≫ jG) (yt ≫ π₀) (by
      rw [Category.assoc, reassoc_of% h₂, C.π_str, ← hz, Category.assoc])
    (by rw [reassoc_of% hyt, Category.assoc, h₁]) V f hf (fun q _ => hWV (hW (Set.mem_univ q))) hzV
  obtain ⟨n, k₁, k₂⟩ := lnStep_padic C hr b hu h₁ h₂ hf hWV A hA r hx hxV h ε z hz yt hyt hW k
    (IsFractionRing.injective (G.presheaf.stalk (below z)) G.functionField) _ hT a₁ a₂ a₃ a₄ b₁ b₂ c₁ hsW
    (Fact.mk hp) _ hzV hΛ hio _ (fun _ => RingHom.comp_apply _ _ _)
  exact ⟨n, k₁, (symLog_eq C hp ε _ kind _).trans (congrArg _ k₂)⟩

theorem lgOf_single {G : Scheme.{0}} [IsIntegral G] {πG : G ⟶ C.Y.X} {φ : C.Y.Fn →+* G.functionField}
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (hp : (resP v).Prime) (ε : Ext v)
    (z : Sp (AlgebraicClosure F) ⟶ G) (hz : (z ≫ πG) ≫ C.Y.str = spMap (algebraMap F (AlgebraicClosure F)))
    (kind : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) (s : ℤ) (hs : s = 1 ∨ s = -1)
    {A : CxSt F} (hm : Mets C A) {w : Pad.Sym E →₀ ℤ} (hw₀ : w = Finsupp.single (kind, R, .inl (τ, k)) s)
    (ρ : G.functionFieldˣ)
    (h₁ : ∀ a : C.Y.X.presheaf.stalk (below (z ≫ πG)), ∃ a' : G.presheaf.stalk (below z),
      algebraMap _ G.functionField a' = φ (algebraMap _ C.Y.X.functionField a) ∧
        (Scheme.stalkClosedPointTo z).hom a' = (Scheme.stalkClosedPointTo (z ≫ πG)).hom a)
    {ρ' : G.functionFieldˣ} (hρ : ρ' = ρ ^ (-s)) (n : (G.presheaf.stalk (below z))ˣ) (h₂ : algebraMap _ G.functionField n.1 =
        φ ((C.gr_spec (below (z ≫ πG))).choose_spec.choose_spec.choose τ k : C.Y.Fnˣ) * ρ')
    (h₄ : haveI := Fact.mk hp
      LineNorm.symLog C kind (.inl (τ, k)) v ε ⟨z ≫ πG, hz⟩ = (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        -Real.log ‖ioOf (resP v) ε ((Scheme.stalkClosedPointTo z).hom n.1)‖) :
    (adlOf C hm w).lg v ε ⟨z ≫ πG, hz⟩ = Real.log (ε.w (valAt z
      (φ (genAt (adlOf C hm w).D (below (z ≫ πG))) ^ 1 * (ρ : G.functionField)))) := by
  subst hw₀ hρ
  dsimp only [adlOf]
  obtain ⟨hp', -, hw⟩ := ioOf_spec F v ε
  obtain rfl : hp = hp' := rfl
  have hx : ∀ x, expo Dw (Finsupp.single ((kind, R, .inl (τ, k)) : Pad.Sym E) s) x = if (⟨τ, k⟩ : Letter Dw) = x then s else 0 :=
    fun x => by
      rw [expo, Finsupp.sum_single_index (by simp)]
      simp [letterOf]
  have hD : divOf C (expo Dw (Finsupp.single ((kind, R, .inl (τ, k)) : Pad.Sym E) s)) = s • C.gr τ k := by
    simp [divOf, hx]
  have hE := (C.gr_spec (below (z ≫ πG))).choose_spec.choose_spec.choose_spec.2 τ k
  rw [LineNorm.lgOf_eq_lgCopy]
  refine (LineNorm.lgCopy_eq C _ v ε ⟨z ≫ πG, hz⟩).trans ?_
  rw [Finsupp.support_single _ (by omega), Finset.sum_singleton,
    Finsupp.single_eq_same]
  dsimp only [LineNorm.dg]
  rw [h₄]
  clear h₄
  generalize (C.gr_spec (below (z ≫ πG))).choose_spec.choose_spec.choose = d at h₂ hE ⊢
  have hP : ∏ x : Letter Dw, d x.1 x.2 ^ expo Dw (Finsupp.single ((kind, R, .inl (τ, k)) : Pad.Sym E) s) x = d τ k ^ s := by
    simp only [hx]
    rw [Finset.prod_eq_single (⟨τ, k⟩ : Letter Dw) (fun b _ hb => by rw [if_neg hb.symm, zpow_zero]) (by simp), if_pos rfl]
  have hq := Base.isEqn_eqn (s • C.gr τ k) (below (z ≫ πG))
  rw [hP, genAt, hD]
  generalize eqn (s • C.gr τ k) (below (z ≫ πG)) = g at hq ⊢
  have hE' : (s • C.gr τ k).IsEqn (below (z ≫ πG)) (d τ k ^ s) := by
    rcases hs with rfl | rfl
    · simpa using hE
    · simpa using hE.neg
  obtain ⟨a, ha, ea⟩ : UnitAt (below (z ≫ πG)) ((d τ k ^ s * g⁻¹ : C.Y.Fnˣ) : C.Y.Fn) := by
    simpa [div_eq_mul_inv] using hq.iff_unitAt.1 hE'
  obtain ⟨a', e₁, e₂⟩ := h₁ a
  have e {T : Type} [Field T] (ψ : G.presheaf.stalk (below z) →+* T) : ψ (n ^ (-s) : _ˣ) = ψ n ^ (-s) :=
    (congrArg Units.val (map_zpow (Units.map ψ.toMonoidHom) n (-s))).trans (Units.val_zpow_eq_zpow_val _ _)
  have e₃ : φ ((g⁻¹ : C.Y.Fnˣ) : C.Y.Fn) ^ 1 * (ρ : G.functionField) =
      algebraMap _ G.functionField (a' * (n ^ (-s) : _ˣ)) := by
    have h0 : φ (d τ k : C.Y.Fnˣ) ≠ 0 := (map_ne_zero φ).2 (d τ k).ne_zero
    have h1 := ρ.ne_zero
    rw [map_mul, e, h₂, e₁, ea]
    rcases hs with rfl | rfl
    · simp
      field_simp
    · simp
      field_simp
  have n₁ : ε.w ((Scheme.stalkClosedPointTo (z ≫ πG)).hom a) ≠ 0 := ε.w.ne_zero (ha.map _).ne_zero
  have n₂ : ε.w ((Scheme.stalkClosedPointTo z).hom n.1) ≠ 0 := ε.w.ne_zero (n.isUnit.map _).ne_zero
  rw [e₃, ← ea, Base.valAt_stalk, Base.valAt_stalk, map_mul, e, e₂, map_mul, map_zpow₀,
    Real.log_mul n₁ (zpow_ne_zero _ n₂), Real.log_zpow, hw ((Scheme.stalkClosedPointTo z).hom n.1)]
  push_cast
  ring

end Free

theorem lg_root_eq : Hypotheses2 → HypothesesH → RegularAlteration →
  ∀ (D : D7) (O : Setup D) (hO : O.Core) (P : Finset ℕ) (R : ℝ) (hR : 2 ≤ R) (c : O.s.Comp)
    (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (arq : IsArithVar q (dimGr D.what₂.Tau O.N O.j))
    (nBs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs) (E : D.what₂.Tau × Bool → Bs.Modules)
    (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) (H : ∀ a, (h a).IsCInf)
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB)
    (hG : GlobalTheory.BcRead.LieGen O c q E jB πB u) (hF : GlobalTheory.BcRead.LieFin O P E jB πB u)
    (hI : GlobalTheory.BcRead.LieInf O R c q E h jB πB u)
    (Y₀ : Scheme.{0}) [IsIntegral Y₀] (π₀ : Y₀ ⟶ Bs)
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    (hfb : IsFlagBundle π₀ E (rkB D.what₂.Tau O.N O.j) fl₀) (ar₀ : IsArithVar (π₀ ≫ q) (O.var c).dim)
    (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀) (G : Scheme.{0}) [IsIntegral G] (j : G ⟶ Y₀) (πG : G ⟶ (O.var c).X)
    (pb : IsPullback j (πG ≫ (O.var c).str) (π₀ ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)))
    [IsFinite πG] [Surjective πG] (φ : (O.var c).Fn →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X))
    (jG : G ⟶ Bg) (r : ∀ a i, (((fl₀ a).root i).pull j).ι → G.functionFieldˣ)
    (hc : GlobalTheory.FlagCov.FlagCover (fun a => (h a).isVB) jB πB u π₀ fl₀ j πG φ jG r)
    (a : D.what₂.Tau × Bool) (i : Fin (rkB D.what₂.Tau O.N O.j a))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL)) (e : Ext v) (y : AlgPt (O.var c))
    (z : Sp (AlgebraicClosure D.what₂.LL) ⟶ G) (yt : Sp e.O ⟶ Y₀) (ch : ((VMetric.grLB (fl₀ a) i ((H a).pull π₀ rfl)).B.pull j).ι),
    z ≫ πG = y.1 → spMap e.O.subtype ≫ yt = z ≫ j → ⊤ ≤ yt ⁻¹ᵁ (VMetric.grLB (fl₀ a) i ((H a).pull π₀ rfl)).B.U (ch PUnit.unit) →
      ((1 : ℕ) : ℝ) * (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))).lg v e y = Real.log (e.w (valAt z (φ (genAt (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))).D (below y.1)) ^ 1 * (r a i ch : G.functionField)))) := by
  intro _ _ _ D O _ P R _ c Bs _ q _ _ E h H Bg jB πB u hG hF hI Y₀ _ π₀ fl₀ _ _ _ G _ j πG _ _ _ φ φs jG r hc a i v e
    y z yt ch hz hyt hU
  obtain ⟨_, -, hI⟩ := hI
  obtain ⟨hr, -⟩ := hI a
  obtain ⟨hp, -⟩ := ioOf_spec _ v e
  have := (h a).isVB.isQuasicoherent
  obtain ⟨y, hy⟩ := y
  obtain rfl : z ≫ πG = y := hz
  have hch : ∃ ck : ∀ k, Chart ((fl₀ a).gr k) 1, ck i = ch PUnit.unit ∧
      ∀ k, yt (IsLocalRing.closedPoint e.O) ∈ (ck k).U := by
    choose U f hx hf using fun k => (fl₀ a).isVB_gr k (yt (IsLocalRing.closedPoint e.O))
    obtain ⟨c₀, hc₀, hU'⟩ : ∃ c₀ : Chart ((fl₀ a).gr i) 1, c₀ = ch PUnit.unit ∧
      yt (IsLocalRing.closedPoint e.O) ∈ c₀.U := ⟨_, rfl, hU (Set.mem_univ _)⟩
    refine ⟨Function.update (fun k => ⟨U k, f k, hf k⟩) i c₀, (Function.update_self ..).trans hc₀, fun k => ?_⟩
    by_cases hk : k = i
    · subst hk
      rw [Function.update_self]
      exact hU'
    · rw [Function.update_of_ne hk]
      exact hx k
  obtain ⟨ck, hck, hx⟩ := hch
  obtain ⟨V, f, hV, hf⟩ := (h a).isVB (π₀ (yt (IsLocalRing.closedPoint e.O)))
  obtain ⟨W, hxW, hWV, hW, t, ht, hfr⟩ := exists_lifts (fl₀ a) _ ck hx (π₀ ⁻¹ᵁ V) hV
  have hyW := le_pre yt W hxW
  have hgW : ⊤ ≤ (FlagCov.genPt G ≫ j) ⁻¹ᵁ W := le_pre (R := G.functionField) _ _ (by
    have h0 : ⊤ ≤ (z ≫ j) ⁻¹ᵁ W := hyt ▸ fun q _ => hyW (Set.mem_univ (spMap e.O.subtype q))
    have h1 : FlagCov.genPt G (IsLocalRing.closedPoint _) = genericPoint G := Scheme.fromSpecStalk_closedPoint
    exact (congrArg (fun q => j q ∈ W) h1).mpr ((genericPoint_specializes (below z)).mem_open (j ⁻¹ᵁ W).isOpen
      (h0 (Set.mem_univ (IsLocalRing.closedPoint _)))))
  have hgV : ⊤ ≤ ((FlagCov.genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V := by
    rw [Category.assoc, hc.1, ← Category.assoc]
    exact fun q _ => hWV (hgW (Set.mem_univ q))
  have hA : IsUnit (Matrix.det (Matrix.of fun b k =>
      ((hf.pullback π₀).basis hWV).repr (((fl₀ a).ι k.succ).app W (t k)) b)) := by
    have := ((hf.pullback π₀).basis hWV).isUnit_det (hfr.basis le_rfl)
    rw [Module.Basis.det_apply] at this
    convert this using 2
    ext b k
    rw [Module.Basis.toMatrix_apply, IsFrame.basis_apply, Twist.resM_self]
    rfl
  have key := fun k => lnStep_eq (O.Φ.C c) hr a.2 (hG.2.2.2 a) (hF a) φs hc.1 hc.2.1 hf hWV _ hA
    (fun k => r a k fun _ => ck k) hgW hgV
    (fun k => hc.2.2 a k hr (fun _ => ck k) V f hf W (hW k) hWV (t k) (ht k) hgW hgV) hp e z hy yt hyt hyW k
  have hri : (r a i fun _ => ck i) = r a i ch := congrArg _ (_root_.funext fun _ => hck)
  rw [Nat.cast_one, one_mul, ← hri]
  have hp' := O.S.p_eq
  have hq' := O.S.rank_eq
  obtain ⟨τ, b⟩ := a
  cases b with
  | true =>
    obtain ⟨k₁, n, k₂, k₃⟩ := key i
    have hi : (i : ℕ) < O.j := i.2
    have e₀ : rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D τ) (cond true 0 O.j + i) =
        Finsupp.single (ArIn.ind P, some R, .inl (embB D (τ, true), Fin.cast hr i)) 1 := by
      rw [rootSym, if_pos (by simp only [cond_true]; omega)]
      rw [show cond true 0 O.j + i = (Fin.cast hr i : ℕ) from zero_add _]
      rfl
    exact lgOf_single (O.Φ.C c) hp e z hy _ _ _ (Fin.cast hr i) 1 (.inl rfl) _ e₀ _ k₁
      ((cond_true _ _).trans (zpow_neg_one _).symm) n k₂ k₃
  | false =>
    obtain ⟨k₁, n, k₂, k₃⟩ := key i.rev
    have hi : (i : ℕ) < O.N - O.j := i.2
    have e₀ : rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D τ) (cond false 0 O.j + i) =
        Finsupp.single (ArIn.ind P, some R, .inl (embB D (τ, false), Fin.cast hr i.rev)) (-1) := by
      rw [rootSym, if_neg (by simp only [cond_false]; omega)]
      have : O.S.Dw.p + O.S.Dw.q - 1 - (cond false 0 O.j + i) = (Fin.cast hr i.rev : ℕ) := by
        change _ - (O.j + i) = O.N - O.j - (i + 1)
        omega
      rw [this]
      rfl
    exact lgOf_single (O.Φ.C c) hp e z hy _ _ _ (Fin.cast hr i.rev) (-1) (.inr rfl) _ e₀ _ k₁
      ((cond_false _ _).trans (by rw [neg_neg, zpow_one, Fin.rev_rev])) n k₂ k₃

end GlobalTheory.BcRead.FinPl

end
