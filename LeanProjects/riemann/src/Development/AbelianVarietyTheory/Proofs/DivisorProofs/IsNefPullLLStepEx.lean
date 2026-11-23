import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTangentEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCohSubDegEqSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameOfProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExOfHeadWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeB

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv sabT sabM)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.FlagMod GlobalTheory.LocM GlobalTheory.NefCurveTest
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)

namespace GlobalTheory.NefStep

section Span

variable {X : Scheme.{0}} {F : X.Modules} {J : Type} {T : J → X.Opens} {r : ℕ}
  (w : ∀ j, Fin r → Γ(F, T j)) (l : ∀ j, Fin r → Γ(VB.dual F, T j))

def spanSub : Sub F where
  sec V :=
    { carrier := {s | ∀ j (W : X.Opens) (h₁ : W ≤ V) (h₂ : W ≤ T j),
        resM F h₁ s = ∑ a, dualApp (l j a) h₂ (resM F h₁ s) • resM F h₂ (w j a)}
      add_mem' := fun hs ht j W h₁ h₂ => by
        simp only [map_add, add_smul, Finset.sum_add_distrib]
        rw [← hs j W h₁ h₂, ← ht j W h₁ h₂]
      zero_mem' := fun j W h₁ h₂ => by simp
      smul_mem' := fun a s hs j W h₁ h₂ => by
        simp only [resM_smul, map_smul, smul_assoc, ← Finset.smul_sum]
        rw [← hs j W h₁ h₂] }
  res_mem h s hs j W h₁ h₂ := by rw [resM_resM]; exact hs j W _ h₂
  mem_of_local {V s} H j W h₁ h₂ := by
    choose U hU hx hs using fun x : W => H x (h₁ x.2)
    refine Twist.sec_ext_of_cover (fun x => W ⊓ U x) (fun _ => inf_le_left)
      (fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx', hx _⟩) fun x => ?_
    have := hs x j (W ⊓ U x) inf_le_right (inf_le_left.trans h₂)
    simp only [map_sum, resM_smul, ← dualApp_resM, resM_resM] at this ⊢
    exact this

theorem exists_sub_det {L : LB X} (hL : L.IsLB) (w : ∀ j, Fin r → Γ(F, L.U j)) (l : ∀ j, Fin r → Γ(VB.dual F, L.U j))
    (hl : ∀ j a b, dualApp (l j a) le_rfl (w j b) = if a = b then 1 else 0)
    (B : ∀ j j', Matrix (Fin r) (Fin r) Γ(X, L.U j ⊓ L.U j'))
    (hB : ∀ j j' b, resM F inf_le_right (w j' b) = ∑ a, B j j' a b • resM F inf_le_left (w j a))
    (hg : ∀ j j', (L.g j j').val = (B j j').det) :
    ∃ (W : X.Modules) (i : W ⟶ F), Mono i ∧ IsVB W r ∧ LBIso L (det W r) := by
  have hl' (j) {V : X.Opens} (h : V ≤ L.U j) (c : Fin r → Γ(X, V)) (a) :
      dualApp (l j a) h (∑ b, c b • resM F h (w j b)) = c a := by
    have e (b) : dualApp (l j a) h (resM F h (w j b)) = if a = b then 1 else 0 := by
      rw [dualApp_resM (l j a) le_rfl h, hl]; split_ifs <;> simp
    simp [e]
  let N := spanSub w l
  have hm (j) (b) : w j b ∈ N.sec (L.U j) := fun j' V h₁ h₂ => by
    have e := congrArg (resM F (le_inf h₂ h₁)) (hB j' j b)
    simp only [map_sum, resM_smul, resM_resM] at e
    rw [e]
    simp only [hl']
  have hi (j) {V : X.Opens} (h : V ≤ L.U j) (c : Fin r → Γ(X, V)) :
      N.incl.app V (∑ b, c b • resM _ h (N.mkSec _ (hm j b))) = ∑ b, c b • resM F h (w j b) := by
    simp only [map_sum, Scheme.Modules.Hom.app_smul, app_resM, Sub.incl_app_mkSec]
  have he (j) : IsFrame fun b => N.mkSec _ (hm j b) := isFrame_iff.2 fun V h => by
    refine ⟨Fintype.linearIndependent_iff.2 fun c hc a => ?_, fun s _ =>
      (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun a => dualApp (l j a) h (resM F le_rfl (N.incl.app V s)),
        N.incl_app_injective V ((hi j h _).trans ?_)⟩⟩
    · rw [← hl' j h c a, ← hi, hc, map_zero, map_zero]
    · exact (N.incl_app_mem s j V le_rfl h).symm.trans (resM_self _ _)
  refine ⟨N.toMod, N.incl, inferInstance, lbIso_det_of_frames hL _ he fun j j' => Units.ext ?_⟩
  rw [hg, IsFrame.val_detUnit, Module.Basis.det_apply]
  congr 1
  ext a b
  have e : resM _ inf_le_right (N.mkSec _ (hm j' b)) =
      ∑ a, B j j' a b • (he j).basis (inf_le_left : L.U j ⊓ L.U j' ≤ _) a := by
    simp only [IsFrame.basis_apply]
    refine N.incl_app_injective _ (Eq.trans ?_ (hi j _ _).symm)
    rw [app_resM, Sub.incl_app_mkSec, hB]
  rw [Module.Basis.toMatrix_apply, e, Module.Basis.repr_sum_self]

end Span

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)

open Classical in

theorem LL_stepEx_g_inv (σ : E →+* ℂ) {n : ℕ} (hn : n ≤ Dw.mult σ) (k k' : F.J) :
    ((show Γ(Z, F.U k ⊓ F.U k')ˣ from (F.LL (stepEx σ n)).g k k')⁻¹).val =
      ∏ a : Fin n, F.B k k' σ (a.castLE hn) (a.castLE hn) := by
  have e : (∏ ix, F.T k k' ix ^ (-stepEx σ n ix))⁻¹ = ∏ a : Fin n, F.T k k' (some ⟨σ, a.castLE hn⟩) := by
    rw [← Finset.prod_inv_distrib]
    refine (Finset.prod_of_injOn (fun a : Fin n => (some ⟨σ, a.castLE hn⟩ : Ix Dw)) (fun a _ b _ h => ?_)
      (fun _ _ => Finset.mem_univ _) (fun ix _ h => ?_) fun a _ => ?_).symm
    · simpa using h
    · rcases ix with _ | ⟨σ', i⟩
      · simp [stepEx]
      · have : ¬ (σ' = σ ∧ (i : ℕ) < n) := by
          rintro ⟨rfl, hi⟩
          exact h ⟨⟨i, hi⟩, by simp, rfl⟩
        simp [stepEx, this]
    · simp [stepEx]
  refine (congrArg Units.val e).trans ?_
  rw [Units.coe_prod]
  rfl

theorem left_vecAt {S S' : Type} [CommRing S] [CommRing S'] (k : F.J) (φ : S →+* S') {z : Sp S ⟶ Z} {z' : Sp S' ⟶ Z}
    (e : spMap φ ≫ z = z') (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (hz' : ⊤ ≤ z' ⁻¹ᵁ F.U k) (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) :
    (tv (F.vecAt k z' hz' rfl σ a)).left = spMap (Formalism.L2.Pj.dualMap φ) ≫ (tv (F.vecAt k z hz rfl σ a)).left := by
  subst e
  rw [← F.tanPull_vecAt k φ z hz hz' rfl rfl (Category.assoc _ _ _).symm, tanPull_left]

theorem exists_step_sub {C : Scheme.{0}} [C.IsSeparated] [PreconnectedSpace C] (g : C ⟶ Z) {t : SAB H C}
    (m : SABMap t Y.t (g ≫ π)) (σ : E →+* ℂ) {n : ℕ} (hn : n ≤ Dw.mult σ) :
    ∃ (W : C.Modules) (i : W ⟶ Lie t.G), Mono i ∧ IsVB W n ∧
      LBIso (CechPic.dual ((F.LL (stepEx σ n)).pull g)) (det W n) := by
  have := t.semi
  obtain ⟨Ψ, hΨ⟩ := exists_tangent_equiv m
  obtain ⟨d, -, hd⟩ := exists_isVB_of_isSemiAbelian t.G
  have := hd.isQuasicoherent
  let J := {q : C.Opens × F.J // CoordOpen t q.1 ∧ q.1 ≤ g ⁻¹ᵁ F.U q.2}
  have hin {T : C.Opens} (hT : IsAffineOpen T) {U : Z.Opens} (h : T ≤ g ⁻¹ᵁ U) : ⊤ ≤ (affPt hT ≫ g) ⁻¹ᵁ U :=
    fun z hz => h (le_preimage_affPt hT hz)
  have hc : ⨆ j : J, j.1.1 = ⊤ := top_unique fun x _ => by
    obtain ⟨q, hq⟩ := Opens.mem_iSup.1 (F.cover.ge (Set.mem_univ (g x)))
    obtain ⟨T, hT, hx, hle⟩ := exists_coordOpen t (V := g ⁻¹ᵁ F.U q) hq
    exact Opens.mem_iSup.2 ⟨⟨(T, q), hT, hle⟩, hx⟩
  let M := CechPic.dual ((F.LL (stepEx σ n)).pull g)
  have hM : M.IsLB := isLB_dual (LB.isLB_pull (F.isLB_LL _) g)
  have hle (j : J) : j.1.1 ≤ M.U fun _ => j.1.2 := j.2.2.trans (GlobalTheory.LB.pull_U (L := F.LL _) g fun _ => j.1.2).ge
  have hL := TriangularFrames.isLB_refine hc hM (fun j : J => fun _ => j.1.2) hle
  let ψ (j : J) := Ψ _ j.2.1 ((affPt j.2.1.1 ≫ g) ≫ π) (Category.assoc _ _ _).symm
  let b (j : J) := (lieBasis (F.M j.1.2).toMChart _ (F.inM (hin j.2.1.1 j.2.2) rfl)).map (ψ j)
  have hb (j : J) : IsFrame (b j) := Summand.isFrame_of_affine_basis j.2.1.1 _
  choose p hp using fun j : J => F.uAt_split j.1.2 _ (hin j.2.1.1 j.2.2) σ
  have hT (j j' : J) : CoordOpen t (j.1.1 ⊓ j'.1.1) := j.2.1.mono (j.2.1.1.inf j'.2.1.1) inf_le_left
  have hh (j j' : J) := hin (hT j j').1 ((inf_le_inf j.2.2 j'.2.2).trans (Scheme.Hom.preimage_inf g).ge)
  have hres (j : J) {T : C.Opens} (hT : CoordOpen t T) (h : T ≤ j.1.1) (a : Fin (Dw.mult σ)) :
      resM (Lie t.G) h (ψ j (F.vecAt j.1.2 _ (hin j.2.1.1 j.2.2) rfl σ a)) =
        Ψ T hT _ (Category.assoc _ _ _).symm (F.vecAt j.1.2 _ (hin hT.1 (h.trans j.2.2)) rfl σ a) := by
    exact (hΨ _ _ _ _ _ _ _ _ h _ _ (left_vecAt F _ _ (by rw [← Category.assoc, spMap_affPt]) _ _ _ _)).symm
  let w (j : J) (a : Fin n) : Γ(Lie t.G, j.1.1) := ψ j (F.vecAt j.1.2 _ (hin j.2.1.1 j.2.2) rfl σ (a.castLE hn))
  let f (j : J) (a : Fin n) : Γ(VB.dual (Lie t.G), j.1.1) := ∑ s, p j (a.castLE hn) s • (hb j).coord s
  let B (j j' : J) : Matrix (Fin n) (Fin n) Γ(C, j.1.1 ⊓ j'.1.1) :=
    ((F.B j.1.2 j'.1.2 σ).map (ev _ _ (hh j j'))).submatrix (Fin.castLE hn) (Fin.castLE hn)
  have h₁ (j : J) (a a' : Fin n) : dualApp (f j a) le_rfl (w j a') = if a = a' then 1 else 0 := by
    have e := congrFun (congrFun (hp j) (a.castLE hn)) (a'.castLE hn)
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    simp only [Fin.castLE_inj] at e
    rw [← e, dualApp_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    have e' : w j a' = ∑ s, F.uAt j.1.2 _ (hin j.2.1.1 j.2.2) σ s (a'.castLE hn) • (hb j).basis le_rfl s := by
      simp only [w, Frames.vecAt, vec_apply, map_sum, map_smul, IsFrame.basis_apply, resM_self, b,
        Module.Basis.map_apply]
    rw [dualApp_smul, LinearMap.smul_apply, IsFrame.dualApp_coord, e', Module.Basis.repr_sum_self, GlobalTheory.LB.resG_self,
      smul_eq_mul]
  have h₂ (j j' : J) (a : Fin n) : resM (Lie t.G) (inf_le_right : j.1.1 ⊓ j'.1.1 ≤ _) (w j' a) =
      ∑ s, B j j' s a • resM (Lie t.G) inf_le_left (w j s) := by
    refine (hres j' (hT j j') inf_le_right _).trans ?_
    rw [F.vecAt_eq_sum j.1.2 j'.1.2 _ (hin (hT j j').1 (inf_le_left.trans j.2.2)) _ (hh j j'), map_sum]
    refine (Finset.sum_of_injOn (Fin.castLE hn) (Fin.castLE_injective hn).injOn (fun _ _ => Finset.mem_univ _)
      (fun s _ h => ?_) fun s _ => ?_).symm
    · have hs : a.castLE hn < s := lt_of_not_ge fun h' => h ⟨⟨s, lt_of_le_of_lt h' a.2⟩, by simp, rfl⟩
      have h0 : (F.B j.1.2 j'.1.2 σ).map (ev _ _ (hh j j')) s (a.castLE hn) = 0 := F.B_map_tri _ _ σ _ hs
      rw [h0, zero_smul, map_zero]
    · rw [map_smul, ← hres j (hT j j') inf_le_left]
      rfl
  have h₃ (j j' : J) : resG C (inf_le_inf (hle j) (hle j')) (M.g (fun _ => j.1.2) fun _ => j'.1.2).val =
      (B j j').det := by
    have ht : (B j j').BlockTriangular id := fun s s' h =>
      F.B_map_tri j.1.2 j'.1.2 σ (ev _ _ (hh j j')) (i := s.castLE hn) (j := s'.castLE hn) h
    rw [Matrix.det_of_upperTriangular ht]
    simp only [B, Matrix.submatrix_apply, Matrix.map_apply, ← map_prod]
    rw [← LL_stepEx_g_inv F σ hn]
    refine left_inv_eq_right_inv (a := ev _ _ (hh j j') ((F.LL (stepEx σ n)).g j.1.2 j'.1.2).val) ?_
      ((map_mul _ _ _).symm.trans ((congrArg _ (Units.mul_inv _)).trans (map_one _)))
    have e : ev _ _ (hh j j') ((F.LL (stepEx σ n)).g j.1.2 j'.1.2).val = resG C (inf_le_inf (hle j) (hle j'))
        (((F.LL (stepEx σ n)).pull g).g (fun _ => j.1.2) fun _ => j'.1.2).val := by
      refine Eq.trans ?_ (GlobalTheory.LB.resG_pull_g (L := F.LL _) g _ _ _).symm
      refine (ev_appLE (affPt (hT j j').1) g ((inf_le_inf j.2.2 j'.2.2).trans (Scheme.Hom.preimage_inf g).ge)
        (le_preimage_affPt _) _ _).symm.trans ?_
      exact congr($(ev_tau_self (hT j j').1 _) _)
    refine (congrArg (_ * ·) e).trans ((map_mul _ _ _).symm.trans ?_)
    exact (congrArg _ (Units.inv_mul _)).trans (map_one _)
  obtain ⟨W, i, hi, hW, e⟩ := exists_sub_det (F := Lie t.G) hL w f h₁ B h₂ h₃
  exact ⟨W, i, hi, hW, (cls_eq_iff hM hW.isLB_det).1 (((cls_eq_iff hL hM).2
    (TriangularFrames.lbIso_refine hM _ hle)).symm.trans ((cls_eq_iff hL hW.isLB_det).2 e))⟩

theorem curveTest_LL_stepEx (h : Published.SemiAbelianLieSeminegative) (K : Type) [Field K] [CharZero K] (σ : E →+* ℂ)
    {n : ℕ} (hn : n ≤ Dw.mult σ) : CurveTest K (F.LL (stepEx σ n)) := fun C _ hs hp hc g => by
  have := LieSemineg.isIntegral_curve hs hc
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have : C.IsSeparated := ⟨by rw [← terminal.comp_from (strHom K C)]; infer_instance⟩
  obtain ⟨W, i, _, hW, e⟩ := exists_step_sub F g (sabM Out.proved_CubePullSt (g ≫ π) Y.t) σ hn
  have := (sabT Out.proved_CubePullSt (g ≫ π) Y.t).semi
  have hM := LB.isLB_pull (F.isLB_LL (stepEx σ n)) g
  refine (h.dual_det_nonneg hs hp hc _ hW i).trans_eq (interNum_congr_cls K _ (isLB_vecOne (isLB_dual hW.isLB_det))
    (isLB_vecOne hM) fun j => ?_)
  fin_cases j
  change cls _ (isLB_dual hW.isLB_det) = cls _ hM
  rw [cls_dual hW.isLB_det, ← (cls_eq_iff (isLB_dual hM) hW.isLB_det).2 e, cls_dual hM, neg_neg]

theorem isNef_pull_LL_stepEx (h : Published.SemiAbelianLieSeminegative) (hN : Published.NefProductNonneg) (k : Type) [Field k]
    [CharZero k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] (g : X ⟶ Z) (σ : E →+* ℂ) {n : ℕ} (hn : n ≤ Dw.mult σ) :
    IsNef k ((F.LL (stepEx σ n)).pull g) :=
  ((curveTest_LL_stepEx F h (AlgebraicClosure k) σ hn).pull (F.isLB_LL _) g).isNef hN (LB.isLB_pull (F.isLB_LL _) g)

end GlobalTheory.NefStep
