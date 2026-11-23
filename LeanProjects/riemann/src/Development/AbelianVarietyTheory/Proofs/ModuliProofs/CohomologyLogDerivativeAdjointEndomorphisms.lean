import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsAlongGroupHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningFieldStructure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueInvariantVectorFieldOfTangent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.AdjDlog

section Cech
variable {X Y Z : Scheme.{0}}

theorem pbT_pbT (h : Z ⟶ Y) (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {O : Z.Opens} (h₁ : V ≤ f ⁻¹ᵁ U)
    (h₂ : O ≤ h ⁻¹ᵁ V) (s : Γ(X, U)) : pbT h (pbT f s V) O = pbT (h ≫ f) s O := by
  rw [pbT_of_le f h₁, pbT_of_le h h₂, pbT_of_le (h ≫ f) (h₂.trans (h.preimage_mono h₁))]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_comp_appLE h f U V O h₁ h₂)

theorem app_eq_pbT (f : Z ⟶ Y) (U : Y.Opens) (s : Γ(Y, U)) : (f.app U).hom s = pbT f s (f ⁻¹ᵁ U) := by
  rw [pbT_of_le f le_rfl, Scheme.Hom.app_eq_appLE]

theorem val_res {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) : (res h u).val = rsT u.val V := (rsT_of_le h _).symm

theorem val_res_pullU (f : Z ⟶ X) {U : X.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    (res h (pullU f U u)).val = pbT f u.val O := by
  rw [val_res, ← rsT_pbT f le_rfl h, ← app_eq_pbT]; rfl

theorem isUnit_pbT (f : Z ⟶ X) {U : X.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    IsUnit (pbT f u.val O) := by
  rw [← val_res_pullU f h]; exact Units.isUnit _

theorem res_res' {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (u : Γ(X, U)ˣ) :
    res h₂ (res h₁ u) = res (h₂.trans h₁) u := by
  ext; rw [val_res, val_res, val_res, rsT_rsT h₁ h₂]

theorem pbT_g_self {L : LB X} (hL : L.IsLB) (f : Z ⟶ X) (i : L.ι) {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ L.U i) :
    pbT f (L.g i i).val O = 1 := by
  have e := congrArg Units.val (hL.g_self i)
  rw [val_res] at e
  rw [← pbT_rsT f (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) h, e, Units.val_one, pbT_one f h]

theorem iso_rel {L M : LB X} (w : LB.Iso L M) (hw : w.IsGen) (i i' : M.ι) (k k' : L.ι) {O : X.Opens}
    (h₁ : O ≤ M.U i ⊓ M.U i') (h₂ : O ≤ L.U k ⊓ L.U k') :
    rsT (w.s (i, k)).val O * (res h₂ (L.g k k')).val = (res h₁ (M.g i i')).val * rsT (w.s (i', k')).val O := by
  have a : O ≤ M.U i ⊓ L.U k := le_inf (h₁.trans inf_le_left) (h₂.trans inf_le_left)
  have a' : O ≤ M.U i' ⊓ L.U k' := le_inf (h₁.trans inf_le_right) (h₂.trans inf_le_right)
  have aux : ∀ (s : Γ(X, M.U i ⊓ L.U k)ˣ) (s' : Γ(X, M.U i' ⊓ L.U k')ˣ) l₁ l₂,
      res (inf_le_left : M.U i ⊓ L.U k ⊓ (M.U i' ⊓ L.U k') ≤ _) s =
        res l₁ (M.g i i') * (res l₂ (L.g k k'))⁻¹ * res inf_le_right s' →
      res a s = res h₁ (M.g i i') * (res h₂ (L.g k k'))⁻¹ * res a' s' := by
    intro s s' l₁ l₂ h
    have e := congrArg (res (le_inf a a')) h
    rwa [map_mul, map_mul, map_inv, res_res', res_res', res_res', res_res'] at e
  have e := aux _ _ _ _ (hw (i, k) (i', k'))
  have e' : res a (w.s (i, k)) * res h₂ (L.g k k') = res h₁ (M.g i i') * res a' (w.s (i', k')) := by
    refine (congrArg (· * res h₂ (L.g k k')) e).trans ?_
    exact (mul_right_comm _ _ _).trans (congrArg (· * _) (inv_mul_cancel_right _ _))
  have e₂ := congrArg Units.val e'
  exact (congrArg (· * (res h₂ (L.g k k')).val) (val_res a _)).symm.trans
    (e₂.trans (congrArg ((res h₁ (M.g i i')).val * ·) (val_res a' _)))

abbrev Sq : Type := ULift.{0} (Finset (Fin 2))

abbrev sqε : Sq → ℤ := fun I => (-1) ^ (2 - I.down.card)

theorem sq_g (L : LB X) (ψ : Sq → (Z ⟶ X)) (J J' : Sq → L.ι) {O : Z.Opens}
    (h : O ≤ LB.wchart L ψ J ⊓ LB.wchart L ψ J') :
    (res h ((LB.LinComb L ψ sqε).g J J')).val * pbT (ψ ⟨{0}⟩) (L.g (J ⟨{0}⟩) (J' ⟨{0}⟩)).val O *
      pbT (ψ ⟨{1}⟩) (L.g (J ⟨{1}⟩) (J' ⟨{1}⟩)).val O =
      pbT (ψ ⟨∅⟩) (L.g (J ⟨∅⟩) (J' ⟨∅⟩)).val O * pbT (ψ ⟨{0, 1}⟩) (L.g (J ⟨{0, 1}⟩) (J' ⟨{0, 1}⟩)).val O := by
  have le : ∀ k, O ≤ ψ k ⁻¹ᵁ (L.U (J k) ⊓ L.U (J' k)) := fun k =>
    le_inf ((h.trans inf_le_left).trans (LB.wchart_le L ψ J k)) ((h.trans inf_le_right).trans (LB.wchart_le L ψ J' k))
  have e : res h ((LB.LinComb L ψ sqε).g J J') = ∏ k, res (le k) (pullU (ψ k) _ (L.g (J k) (J' k))) ^ sqε k := by
    refine (map_prod (res h) _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow (res h) _ _).trans ?_)
    exact congrArg (fun u : Γ(Z, O)ˣ => u ^ sqε k) (res_res' _ h _)
  have hu : (Finset.univ : Finset Sq) = {⟨∅⟩, ⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} := by decide
  rw [e, hu, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, ← val_res_pullU _ (le _), ← val_res_pullU _ (le _), ← val_res_pullU _ (le _),
    ← val_res_pullU _ (le _), ← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
  congr 1
  have h0 : sqε ⟨∅⟩ = 1 := by decide
  have h1 : sqε ⟨{0}⟩ = -1 := by decide
  have h2 : sqε ⟨{1}⟩ = -1 := by decide
  have h3 : sqε ⟨{0, 1}⟩ = 1 := by decide
  rw [h0, h1, h2, h3, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one]
  generalize res (le ⟨∅⟩) _ = a
  generalize res (le ⟨{0}⟩) _ = b
  generalize res (le ⟨{1}⟩) _ = c
  generalize res (le ⟨{0,1}⟩) _ = d
  rw [show a * (b⁻¹ * (c⁻¹ * d)) * b * c = a * d * (b⁻¹ * b) * (c⁻¹ * c) by ac_rfl]
  simp

def idx {T : Type} (i₀ i : T) : Sq → T := fun I => if 0 ∈ I.down then i else i₀

theorem le_wchart (L : LB X) (ψ : Sq → (Z ⟶ X)) (i₀ i : L.ι) {O : Z.Opens} (h₀ : ⊤ ≤ ψ ⟨∅⟩ ⁻¹ᵁ L.U i₀)
    (h₁ : ⊤ ≤ ψ ⟨{1}⟩ ⁻¹ᵁ L.U i₀) (h₂ : O ≤ ψ ⟨{0}⟩ ⁻¹ᵁ L.U i) (h₃ : O ≤ ψ ⟨{0, 1}⟩ ⁻¹ᵁ L.U i) :
    O ≤ LB.wchart L ψ (idx i₀ i) := by
  intro y hy
  refine Set.mem_iInter.2 fun k => ?_
  have hu : k ∈ ({⟨∅⟩, ⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} : Finset Sq) := by revert k; decide
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact h₀ trivial
  · exact h₂ hy
  · exact h₁ trivial
  · exact h₃ hy

theorem exists_units {L : LB X} (hL : L.IsLB) (ψ ψ' : Sq → (Z ⟶ X)) (i₀ : L.ι)
    (H : LBIso (LB.LinComb L ψ sqε) (LB.LinComb L ψ' sqε))
    (h₀ : ⊤ ≤ ψ ⟨∅⟩ ⁻¹ᵁ L.U i₀) (h₁ : ⊤ ≤ ψ ⟨{1}⟩ ⁻¹ᵁ L.U i₀)
    (h₀' : ⊤ ≤ ψ' ⟨∅⟩ ⁻¹ᵁ L.U i₀) (h₁' : ⊤ ≤ ψ' ⟨{1}⟩ ⁻¹ᵁ L.U i₀)
    (V V' : L.ι → Z.Opens) (h₂ : ∀ i, V i ≤ ψ ⟨{0}⟩ ⁻¹ᵁ L.U i) (h₃ : ∀ i, V i ≤ ψ ⟨{0, 1}⟩ ⁻¹ᵁ L.U i)
    (h₂' : ∀ i, V' i ≤ ψ' ⟨{0}⟩ ⁻¹ᵁ L.U i) (h₃' : ∀ i, V' i ≤ ψ' ⟨{0, 1}⟩ ⁻¹ᵁ L.U i) :
    ∃ W : ∀ i k, Γ(Z, V' i ⊓ V k)ˣ, ∀ i k i' k' (O : Z.Opens), O ≤ V' i ⊓ V k → O ≤ V' i' ⊓ V k' →
      rsT (W i k).val O * pbT (ψ' ⟨{0}⟩) (L.g i i').val O * pbT (ψ ⟨{0, 1}⟩) (L.g k k').val O =
        pbT (ψ' ⟨{0, 1}⟩) (L.g i i').val O * pbT (ψ ⟨{0}⟩) (L.g k k').val O * rsT (W i' k').val O := by
  obtain ⟨w, hw⟩ := H
  have a := fun i => le_wchart L ψ i₀ i h₀ h₁ (h₂ i) (h₃ i)
  have a' := fun i => le_wchart L ψ' i₀ i h₀' h₁' (h₂' i) (h₃' i)
  have b : ∀ i k, V' i ⊓ V k ≤ LB.wchart L ψ' (idx i₀ i) ⊓ LB.wchart L ψ (idx i₀ k) := fun i k =>
    inf_le_inf (a' i) (a k)
  refine ⟨fun i k => res (b i k) (w.s (idx i₀ i, idx i₀ k)), fun i k i' k' O hO hO' => ?_⟩
  have c : O ≤ (LB.wchart L ψ' (idx i₀ i) ⊓ LB.wchart L ψ (idx i₀ k)) ⊓
      (LB.wchart L ψ' (idx i₀ i') ⊓ LB.wchart L ψ (idx i₀ k')) := le_inf (hO.trans (b i k)) (hO'.trans (b i' k'))
  have c₁ : O ≤ LB.wchart L ψ (idx i₀ k) ⊓ LB.wchart L ψ (idx i₀ k') :=
    c.trans (inf_le_inf inf_le_right inf_le_right)
  have c₂ : O ≤ LB.wchart L ψ' (idx i₀ i) ⊓ LB.wchart L ψ' (idx i₀ i') :=
    c.trans (inf_le_inf inf_le_left inf_le_left)
  have e₂ := iso_rel w hw (idx i₀ i) (idx i₀ i') (idx i₀ k) (idx i₀ k') c₂ c₁
  have r₁ : rsT (res (b i k) (w.s (idx i₀ i, idx i₀ k))).val O = rsT (w.s (idx i₀ i, idx i₀ k)).val O :=
    (congrArg (rsT · O) (val_res (b i k) _)).trans (rsT_rsT (b i k) hO _)
  have r₂ : rsT (res (b i' k') (w.s (idx i₀ i', idx i₀ k'))).val O = rsT (w.s (idx i₀ i', idx i₀ k')).val O :=
    (congrArg (rsT · O) (val_res (b i' k') _)).trans (rsT_rsT (b i' k') hO' _)
  have g₁ := sq_g L ψ _ _ c₁
  have g₂ := sq_g L ψ' _ _ c₂
  change _ * pbT _ (L.g k k').val O * pbT _ (L.g i₀ i₀).val O = pbT _ (L.g i₀ i₀).val O * pbT _ (L.g k k').val O at g₁
  change _ * pbT _ (L.g i i').val O * pbT _ (L.g i₀ i₀).val O = pbT _ (L.g i₀ i₀).val O * pbT _ (L.g i i').val O at g₂
  rw [pbT_g_self hL _ _ (le_top.trans h₀), pbT_g_self hL _ _ (le_top.trans h₁), _root_.mul_one, _root_.one_mul] at g₁
  rw [pbT_g_self hL _ _ (le_top.trans h₀'), pbT_g_self hL _ _ (le_top.trans h₁'), _root_.mul_one, _root_.one_mul] at g₂
  have alg : ∀ y y' x x' a a' b b' d d' : Γ(Z, O), y = x → y' = x' → x * a = a' * x' → a * b = d → a' * b' = d' →
      y * b' * d = d' * b * y' := by
    rintro y y' _ _ a a' b b' _ _ rfl rfl h rfl rfl
    linear_combination (b * b') * h
  exact alg _ _ _ _ _ _ _ _ _ _ r₁ r₂ e₂ g₁ g₂

end Cech

section Alg
variable {R S : Type} [CommRing R] [CommRing S] (r : R →+* S) (e : S)

theorem alg_unit (he : e * e = 0) (inj : ∀ a b a' b', r a + e * r b = r a' + e * r b' → a = a' ∧ b = b')
    (sur : ∀ F, ∃ a b, F = r a + e * r b) (F : S) (hF : IsUnit F) :
    ∃ a β, IsUnit a ∧ F = r a + e * r (a * β) := by
  obtain ⟨F', hF'⟩ := hF.exists_right_inv
  obtain ⟨a, b, rfl⟩ := sur F
  obtain ⟨a', b', rfl⟩ := sur F'
  have h := (inj (a * a') (a * b' + b * a') 1 0 (by
    simp only [map_mul, map_add, map_one, map_zero]
    linear_combination hF' - (r b * r b') * he)).1
  refine ⟨a, a' * b, IsUnit.of_mul_eq_one _ h, ?_⟩
  rw [← _root_.mul_assoc, h, _root_.one_mul]

theorem alg_dlog (he : e * e = 0) (inj : ∀ a b a' b', r a + e * r b = r a' + e * r b' → a = a' ∧ b = b')
    {a β a' β' G c H φ : R} (ha : IsUnit a) (hG : IsUnit G) (hH : IsUnit H)
    (h : (r a + e * r (a * β)) * r G * (r H + e * r (H * φ)) =
      (r G + e * r (G * c)) * r H * (r a' + e * r (a' * β'))) : β + φ = c + β' := by
  obtain ⟨h₁, h₂⟩ := inj (a * G * H) (a * G * H * (β + φ)) (a' * G * H) (a' * G * H * (c + β')) (by
    simp only [map_mul, map_add] at h ⊢
    linear_combination h - (r a * r β * r G * r H * r φ - r G * r c * r H * r a' * r β') * he)
  rw [← h₁] at h₂
  exact ((ha.mul hG).mul hH).mul_left_cancel h₂

end Alg

section Thick
variable {K : Type} [Field K] (A : Over (Sp K))

def zpt (K : Type) [Field K] : 𝟙_ (Over (Sp K)) ⟶ epsR K :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change spMap _ ≫ spMap _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)

def zsec : A ⟶ epsR K ⊗ A := lift (toUnit A ≫ zpt K) (𝟙 A)

abbrev eF (O : (epsR K ⊗ A).left.Opens) : Γ((epsR K ⊗ A).left, O) :=
  constFn (R := DualNumber K) (fst (epsR K) A).left O DualNumber.eps

theorem eF_sq (O : (epsR K ⊗ A).left.Opens) : eF A O * eF A O = 0 := by
  unfold eF constFn
  rw [← map_mul, ← map_mul, DualNumber.eps_mul_eps, map_zero, map_zero]

theorem thick : (∀ O : (epsR K ⊗ A).left.Opens, (snd (epsR K) A).left ⁻¹ᵁ ((zsec A).left ⁻¹ᵁ O) = O) ∧
    ∀ (O : A.left.Opens) (F : Γ((epsR K ⊗ A).left, (snd (epsR K) A).left ⁻¹ᵁ O)), ∃! ab : Γ(A.left, O) × Γ(A.left, O),
      F = ((snd (epsR K) A).left.app O).hom ab.1 + eF A _ * ((snd (epsR K) A).left.app O).hom ab.2 := by
  have h := GlobalTheory.ConstThickening.structure_dualNumber K A.left (epsR K ⊗ A).left A.hom (fst (epsR K) A).left (snd (epsR K) A).left (zsec A).left
    (IsPullback.of_hasPullback (epsR K).hom A.hom).flip
    (by rw [← Over.comp_left, zsec, lift_snd]; rfl)
    (by
      refine (Over.comp_left _ _ _ _ _).symm.trans ?_
      rw [zsec, lift_fst]
      simp [zpt])
  exact ⟨h.1, h.2.2⟩

theorem preimage_eq {X : Scheme.{0}} {h h' : (epsR K ⊗ A).left ⟶ X} (e : (zsec A).left ≫ h = (zsec A).left ≫ h')
    (W : X.Opens) : h ⁻¹ᵁ W = h' ⁻¹ᵁ W := by
  rw [← (thick A).1 (h ⁻¹ᵁ W), ← (thick A).1 (h' ⁻¹ᵁ W), ← Scheme.Hom.comp_preimage (zsec A).left h,
    ← Scheme.Hom.comp_preimage (zsec A).left h', e]

variable [GrpObj A]

theorem zsec_tangent {v : epsR K ⟶ A} (hv : IsTangent v) : zsec A ≫ fst (epsR K) A ≫ v = 1 := by
  have : zpt K ≫ v = η[A] := Over.OverMorphism.ext hv
  rw [zsec, lift_fst_assoc, Category.assoc, this, Hom.one_def]

theorem zsec_transl {v : epsR K ⟶ A} (hv : IsTangent v) (f : A ⟶ A) :
    zsec A ≫ ((fst (epsR K) A ≫ v) * (snd (epsR K) A ≫ f)) = zsec A ≫ snd (epsR K) A ≫ f := by
  rw [MonObj.comp_mul, zsec_tangent A hv, _root_.one_mul]

theorem transl_preimage {v : epsR K ⟶ A} (hv : IsTangent v) (f : A ⟶ A) (W : A.left.Opens) :
    ((fst (epsR K) A ≫ v) * (snd (epsR K) A ≫ f)).left ⁻¹ᵁ W = (snd (epsR K) A).left ⁻¹ᵁ f.left ⁻¹ᵁ W :=
  preimage_eq A (h' := (snd (epsR K) A ≫ f).left) (congrArg (fun z => z.left) (zsec_transl A hv f)) W

theorem pbT_transl {v : epsR K ⟶ A} (hv : IsTangent v) {dd} (hd : IsInvDer v dd) (f : A ⟶ A) (W O : A.left.Opens)
    (h : O ≤ f.left ⁻¹ᵁ W) (s : Γ(A.left, W)) :
    pbT ((fst (epsR K) A ≫ v) * (snd (epsR K) A ≫ f)).left s ((snd (epsR K) A).left ⁻¹ᵁ O) =
      ((snd (epsR K) A).left.app O).hom (pbT f.left s O) +
        eF A _ * ((snd (epsR K) A).left.app O).hom (pbT f.left (dd W s) O) := by
  have e₁ : (epsR K ◁ f).left ≫ (snd (epsR K) A).left = (snd (epsR K) A).left ≫ f.left := by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  have e₂ : (epsR K ◁ f).left ≫ (fst (epsR K) A).left = (fst (epsR K) A).left := by
    rw [← Over.comp_left, whiskerLeft_fst]
  have e₃ : (epsR K ◁ f).left ≫ ((fst (epsR K) A ≫ v) * snd (epsR K) A).left =
      ((fst (epsR K) A ≫ v) * (snd (epsR K) A ≫ f)).left := by
    rw [← Over.comp_left, MonObj.comp_mul, whiskerLeft_snd, whiskerLeft_fst_assoc]
  have l₁ : (snd (epsR K) A).left ⁻¹ᵁ O ≤ (epsR K ◁ f).left ⁻¹ᵁ (snd (epsR K) A).left ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, e₁]
    exact (snd (epsR K) A).left.preimage_mono h
  have l₂ : (snd (epsR K) A).left ⁻¹ᵁ W ≤ ((fst (epsR K) A ≫ v) * snd (epsR K) A).left ⁻¹ᵁ W := by
    have := transl_preimage A hv (𝟙 A) W
    rw [Category.comp_id] at this
    rw [this]; exact le_rfl
  have e := congrArg (fun F => pbT (epsR K ◁ f).left F ((snd (epsR K) A).left ⁻¹ᵁ O)) (hd W s)
  simp only [pbT_add, pbT_mul] at e
  rw [pbT_pbT _ _ l₂ l₁, pbT_pbT _ _ le_rfl l₁, pbT_pbT _ _ le_rfl l₁, e₃, e₁] at e
  rw [e, app_eq_pbT, app_eq_pbT, pbT_pbT _ _ h le_rfl, pbT_pbT _ _ h le_rfl]
  congr 2
  refine (pbT_constFn (R := DualNumber K) _ _ l₁ _).trans ?_
  exact congrArg (fun q => constFn (R := DualNumber K) q _ DualNumber.eps) e₂

end Thick

section Main
variable {K : Type} [Field K] (A : Over (Sp K))

theorem exists_prim {I : Type} (U U' : I → A.left.Opens)
    (W : ∀ i k, Γ((epsR K ⊗ A).left, (snd (epsR K) A).left ⁻¹ᵁ U i ⊓ (snd (epsR K) A).left ⁻¹ᵁ U' k)ˣ) :
    ∃ β : ∀ i k, Γ(A.left, U i ⊓ U' k), ∀ i k i' k' (O : A.left.Opens), O ≤ U i ⊓ U' k → O ≤ U i' ⊓ U' k' →
      ∀ G c H φ : Γ(A.left, O), IsUnit G → IsUnit H →
      rsT (W i k).val ((snd (epsR K) A).left ⁻¹ᵁ O) * ((snd (epsR K) A).left.app O).hom G *
          (((snd (epsR K) A).left.app O).hom H + eF A _ * ((snd (epsR K) A).left.app O).hom (H * φ)) =
        (((snd (epsR K) A).left.app O).hom G + eF A _ * ((snd (epsR K) A).left.app O).hom (G * c)) *
          ((snd (epsR K) A).left.app O).hom H * rsT (W i' k').val ((snd (epsR K) A).left ⁻¹ᵁ O) →
      rsT (β i k) O + φ = c + rsT (β i' k') O := by
  have inj : ∀ (O : A.left.Opens) a b a' b',
      ((snd (epsR K) A).left.app O).hom a + eF A _ * ((snd (epsR K) A).left.app O).hom b =
      ((snd (epsR K) A).left.app O).hom a' + eF A _ * ((snd (epsR K) A).left.app O).hom b' → a = a' ∧ b = b' :=
    fun O a b a' b' h => Prod.ext_iff.1 (((thick A).2 O _).unique (y₁ := (a, b)) (y₂ := (a', b')) rfl h)
  have le : ∀ i k, (snd (epsR K) A).left ⁻¹ᵁ (U i ⊓ U' k) ≤
      (snd (epsR K) A).left ⁻¹ᵁ U i ⊓ (snd (epsR K) A).left ⁻¹ᵁ U' k := fun i k =>
    le_inf ((snd (epsR K) A).left.preimage_mono inf_le_left) ((snd (epsR K) A).left.preimage_mono inf_le_right)
  choose a β ha hab using fun i k => alg_unit ((snd (epsR K) A).left.app (U i ⊓ U' k)).hom (eF A _) (eF_sq A _)
    (inj _) (fun F => by obtain ⟨ab, h, -⟩ := (thick A).2 _ F; exact ⟨ab.1, ab.2, h⟩)
    (res (le i k) (W i k)).val (Units.isUnit _)
  have key : ∀ i k (O : A.left.Opens), O ≤ U i ⊓ U' k → rsT (W i k).val ((snd (epsR K) A).left ⁻¹ᵁ O) =
      ((snd (epsR K) A).left.app O).hom (rsT (a i k) O) +
        eF A _ * ((snd (epsR K) A).left.app O).hom (rsT (a i k) O * rsT (β i k) O) := by
    intro i k O hO
    have l := (snd (epsR K) A).left.preimage_mono hO
    have e := congrArg (rsT · ((snd (epsR K) A).left ⁻¹ᵁ O)) (hab i k)
    simp only [rsT_add, rsT_mul] at e
    rw [val_res, rsT_rsT (le i k) l, app_eq_pbT, app_eq_pbT, rsT_pbT _ le_rfl l, rsT_pbT _ le_rfl l,
      rsT_constFn (R := DualNumber K) _ l] at e
    rw [e, ← rsT_mul, app_eq_pbT, app_eq_pbT, pbT_rsT _ hO le_rfl, pbT_rsT _ hO le_rfl]
  refine ⟨β, fun i k i' k' O hO hO' G c H φ hG hH h => ?_⟩
  rw [key i k O hO, key i' k' O hO'] at h
  refine alg_dlog _ _ (eF_sq A _) (inj O) ?_ hG hH h
  rw [rsT_of_le hO]
  exact (ha i k).map _

variable [GrpObj A] [IsCommMonObj A]

theorem psum_two {T : Over (Sp K)} (a b : T ⟶ A) :
    psum A ![a, b] ∅ = 1 ∧ psum A ![a, b] {0} = a ∧ psum A ![a, b] {1} = b ∧ psum A ![a, b] {0, 1} = b * a := by
  refine ⟨rfl, _root_.mul_one a, _root_.mul_one b, ?_⟩
  change a * (b * 1) = b * a
  rw [_root_.mul_one, mul_comm]

end Main

section Final
variable {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]

theorem exists_units_thick {X : Scheme.{0}} (m : A.left ⟶ X) {L : LB X} (hL : L.IsLB) (M : LB A.left) (hM : M.IsLB)
    (hML : LBIso M (L.pull m)) (f f' : A ⟶ A) [IsMonHom f] [IsMonHom f'] {v : epsR K ⟶ A} (hv : IsTangent v)
    (H : LBIso (cubeLB A ![fst A A ≫ f, snd A A] M) (cubeLB A ![fst A A, snd A A ≫ f'] M)) :
    ∃ W : ∀ i k, Γ((epsR K ⊗ A).left, (snd (epsR K) A).left ⁻¹ᵁ (m ⁻¹ᵁ L.U i) ⊓
        (snd (epsR K) A).left ⁻¹ᵁ (f.left ⁻¹ᵁ m ⁻¹ᵁ L.U k))ˣ,
      ∀ i k i' k' (O : (epsR K ⊗ A).left.Opens),
        O ≤ (snd (epsR K) A).left ⁻¹ᵁ (m ⁻¹ᵁ L.U i) ⊓ (snd (epsR K) A).left ⁻¹ᵁ (f.left ⁻¹ᵁ m ⁻¹ᵁ L.U k) →
        O ≤ (snd (epsR K) A).left ⁻¹ᵁ (m ⁻¹ᵁ L.U i') ⊓ (snd (epsR K) A).left ⁻¹ᵁ (f.left ⁻¹ᵁ m ⁻¹ᵁ L.U k') →
      rsT (W i k).val O * pbT ((snd (epsR K) A ≫ 𝟙 A).left ≫ m) (L.g i i').val O *
          pbT (((fst (epsR K) A ≫ v) * (snd (epsR K) A ≫ f)).left ≫ m) (L.g k k').val O =
        pbT (((fst (epsR K) A ≫ v ≫ f') * (snd (epsR K) A ≫ 𝟙 A)).left ≫ m) (L.g i i').val O *
          pbT ((snd (epsR K) A ≫ f).left ≫ m) (L.g k k').val O * rsT (W i' k').val O := by
  have hv' : IsTangent (v ≫ f') := by
    have h₁ : zpt K ≫ v = η[A] := Over.OverMorphism.ext hv
    have h₂ : zpt K ≫ v ≫ f' = η[A] := by rw [← Category.assoc, h₁, IsMonHom.one_hom]
    exact congrArg (fun z => z.left) h₂
  obtain ⟨w, hw⟩ := hML
  let h : epsR K ⊗ A ⟶ A ⊗ A := lift (snd (epsR K) A) (fst (epsR K) A ≫ v)
  let x : Fin 2 → (epsR K ⊗ A ⟶ A) := ![snd (epsR K) A ≫ f, fst (epsR K) A ≫ v]
  let x' : Fin 2 → (epsR K ⊗ A ⟶ A) := ![snd (epsR K) A ≫ 𝟙 A, fst (epsR K) A ≫ v ≫ f']
  have pull : ∀ (y : Fin 2 → (A ⊗ A ⟶ A)) (z : Fin 2 → (epsR K ⊗ A ⟶ A)), (∀ i, h ≫ y i = z i) → ∀ I : Sq,
      (psum A z I.down).left = h.left ≫ (psum A y I.down).left := fun y z e I =>
    congrArg (fun t => t.left) ((congrArg (fun t => psum A t I.down) (funext e).symm).trans
      (psum_hom (preHom h) y I.down).symm)
  have H₁ : LBIso (cubeLB A x M) (cubeLB A x' M) :=
    H.chartPull (chartPullSame M _ _ sqε h.left (pull _ x fun i => by fin_cases i <;> simp [h, x]))
      (chartPullSame M _ _ sqε h.left (pull _ x' fun i => by fin_cases i <;> simp [h, x']))
  have a := iso_linComb ((isGen_iff w).1 hw) (fun I : Sq => (psum A x I.down).left) sqε
  have a' := iso_linComb ((isGen_iff w).1 hw) (fun I : Sq => (psum A x' I.down).left) sqε
  have H₂ := LBIso.trans (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hM _ _) (DVR.linComb_isLB _ hL _ _) a.symm
    (LBIso.trans (DVR.linComb_isLB _ hM _ _) (DVR.linComb_isLB _ hM _ _) (DVR.linComb_isLB _ hL _ _) H₁ a')
  let pt : (𝟙_ (Over (Sp K))).left := (⊥ : PrimeSpectrum K)
  obtain ⟨i₀, hi₀⟩ := exists_chart hL ((η[A].left ≫ m) pt)
  have top : ∀ t : epsR K ⊗ A ⟶ A, zsec A ≫ t = 1 → ⊤ ≤ (t.left ≫ m) ⁻¹ᵁ L.U i₀ := by
    intro t ht
    have e : zsec A ≫ t = zsec A ≫ toUnit _ ≫ η[A] := by
      rw [ht, Hom.one_def, ← Category.assoc, toUnit_unique (zsec A ≫ toUnit _) (toUnit _)]
    rw [preimage_eq A (h' := (toUnit (epsR K ⊗ A)).left ≫ η[A].left ≫ m)
      (congrArg (fun z => z.left ≫ m) e)]
    intro y _
    have : (toUnit (epsR K ⊗ A)).left y = pt := Subsingleton.elim (α := PrimeSpectrum K) _ _
    change (η[A].left ≫ m) ((toUnit (epsR K ⊗ A)).left y) ∈ L.U i₀
    rw [this]; exact hi₀
  obtain ⟨p₀, p₁, p₂, p₃⟩ := psum_two A (snd (epsR K) A ≫ f) (fst (epsR K) A ≫ v)
  obtain ⟨p₀', p₁', p₂', p₃'⟩ := psum_two A (snd (epsR K) A ≫ 𝟙 A) (fst (epsR K) A ≫ v ≫ f')
  have R := exists_units hL _ _ i₀ H₂ (top _ (by rw [p₀, MonObj.comp_one])) (top _ (by rw [p₂, zsec_tangent A hv]))
    (top _ (by rw [p₀', MonObj.comp_one])) (top _ (by rw [p₂', zsec_tangent A hv']))
    (fun k => (snd (epsR K) A).left ⁻¹ᵁ (f.left ⁻¹ᵁ m ⁻¹ᵁ L.U k)) (fun i => (snd (epsR K) A).left ⁻¹ᵁ (m ⁻¹ᵁ L.U i))
    (fun k => by
      change _ ≤ (psum A _ _).left ⁻¹ᵁ m ⁻¹ᵁ L.U k
      rw [p₁]; exact le_rfl)
    (fun k => by
      change _ ≤ (psum A _ _).left ⁻¹ᵁ m ⁻¹ᵁ L.U k
      rw [p₃, transl_preimage A hv])
    (fun k => by
      change _ ≤ (psum A _ _).left ⁻¹ᵁ m ⁻¹ᵁ L.U k
      rw [p₁', Category.comp_id])
    (fun k => by
      change _ ≤ (psum A _ _).left ⁻¹ᵁ m ⁻¹ᵁ L.U k
      rw [p₃', transl_preimage A hv']; exact le_rfl)
  obtain ⟨W, hW⟩ := R
  refine ⟨W, fun i k i' k' O hO hO' => ?_⟩
  have r := hW i k i' k' O hO hO'
  dsimp only at r
  rw [show psum A x {0} = _ from p₁, show psum A x {0, 1} = _ from p₃, show psum A x' {0} = _ from p₁',
    show psum A x' {0, 1} = _ from p₃'] at r
  exact r

omit [IsCommMonObj A] in

theorem pbT_g_transl {X : Scheme.{0}} (m : A.left ⟶ X) (L : LB X) {v : epsR K ⟶ A} (hv : IsTangent v) {dd}
    (hd : IsInvDer v dd) (f : A ⟶ A) (i i' : L.ι) (c : Γ(A.left, m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U i'))
    (hc : pbT m (L.g i i').val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U i') * c =
      dd _ (pbT m (L.g i i').val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U i')))
    (O : A.left.Opens) (h : O ≤ f.left ⁻¹ᵁ (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U i')) :
    ∃ G : Γ(A.left, O), IsUnit G ∧
      pbT ((snd (epsR K) A ≫ f).left ≫ m) (L.g i i').val ((snd (epsR K) A).left ⁻¹ᵁ O) =
        ((snd (epsR K) A).left.app O).hom G ∧
      pbT (((fst (epsR K) A ≫ v) * (snd (epsR K) A ≫ f)).left ≫ m) (L.g i i').val ((snd (epsR K) A).left ⁻¹ᵁ O) =
        ((snd (epsR K) A).left.app O).hom G + eF A _ * ((snd (epsR K) A).left.app O).hom (G * pbT f.left c O) := by
  have l : m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U i' ≤ m ⁻¹ᵁ (L.U i ⊓ L.U i') := fun _ hy => hy
  refine ⟨pbT f.left (pbT m (L.g i i').val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U i')) O, ?_, ?_, ?_⟩
  · rw [pbT_pbT _ _ l h]
    exact isUnit_pbT (f.left ≫ m) (U := L.U i ⊓ L.U i') (h.trans (f.left.preimage_mono l)) _
  · rw [app_eq_pbT, pbT_pbT _ _ h le_rfl, pbT_pbT ((snd (epsR K) A).left ≫ f.left) m l ((snd (epsR K) A).left.preimage_mono h)]
    rfl
  · rw [← pbT_mul, hc, ← pbT_transl A hv hd f _ O h, pbT_pbT _ _ l]
    rw [transl_preimage A hv]
    exact (snd (epsR K) A).left.preimage_mono h

theorem pbT_id {Y : Scheme.{0}} {U : Y.Opens} (s : Γ(Y, U)) (O : Y.Opens) (h : O ≤ U) : pbT (𝟙 Y) s O = rsT s O := by
  rw [pbT_of_le (𝟙 Y) h, rsT_of_le h]
  simp only [Scheme.Hom.appLE, resG, Scheme.Hom.id_app]
  rfl

theorem mul_congr {S : Type} [CommRing S] {x a b c d y a' b' c' d' : S} (h : x * a * b = c * d * y) (ha : a = a')
    (hb : b = b') (hc : c = c') (hd : d = d') : x * a' * b' = c' * d' * y := by
  rw [← ha, ← hb, ← hc, ← hd]; exact h

theorem one_eq {R S : Type} [CommRing R] [CommRing S] (r : R →+* S) (e : S) : 1 = r 1 + e * r (1 * 0) := by simp

end Final

theorem cohom_dlog_of_adjoint : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (X : Scheme.{0}) (m : P₀.A.left ⟶ X) (L : LB X) φ (f₀ f₀' : P₀.A ⟶ P₀.A) (F' : Matrix (Fin g) (Fin g) K), L.IsLB → LBIso P₀.L (L.pull m) → IsDlog m L dd φ → IsMonHom f₀ → IsMonHom f₀' → LBIso (cubeLB P₀.A ![fst P₀.A P₀.A ≫ f₀, snd P₀.A P₀.A] P₀.L) (cubeLB P₀.A ![fst P₀.A P₀.A, snd P₀.A P₀.A ≫ f₀'] P₀.L) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → ∀ x, Cohom f₀.left _ (lc P₀.A.hom (fun y => F' y x) φ) (φ x) := by
  intro K _ P₀ g v dd hv hdd X m L φ f₀ f₀' F' hL hML hφ hf hf' H hF x
  have hw : IsTangent (v x ≫ f₀') := by
    have h₁ : zpt K ≫ v x = η[P₀.A] := Over.OverMorphism.ext (hv.1 x)
    have h₂ : zpt K ≫ v x ≫ f₀' = η[P₀.A] := by rw [← Category.assoc, h₁, IsMonHom.one_hom]
    exact congrArg (fun z => z.left) h₂
  obtain ⟨dw, hdw⟩ := (GlobalTheory.KS.InvField.main K P₀.A _ hw).1
  have hsum : ∀ (O : P₀.A.left.Opens) (s : Γ(P₀.A.left, O)),
      dw O s = ∑ a, constFn P₀.A.hom O (F' a x) * dd a O s := by
    intro O s
    have e := GlobalTheory.KS.InvHom.invDer_along_hom K P₀.A P₀.A (𝟙 _) g v dd _ dw (fun a => F' a x) inferInstance hv.1 hw hdd hdw
      (by rw [Category.comp_id]; exact hF x) O s
    have id : ∀ t : Γ(P₀.A.left, O), ((𝟙 P₀.A : P₀.A ⟶ P₀.A).left.app O).hom t = t := fun t => by
      exact (app_eq_pbT _ _ _).trans ((pbT_id t O le_rfl).trans (rsT_self t))
    simp only [id] at e
    exact e
  have hc : ∀ i i', pbT m (L.g i i').val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U i') * lc P₀.A.hom (fun y => F' y x) φ i i' =
      dw _ (pbT m (L.g i i').val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U i')) := by
    intro i i'
    rw [hsum, lc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hφ a i i', mul_left_comm]
  obtain ⟨W, hW⟩ := exists_units_thick P₀.A m hL P₀.L P₀.isLB hML f₀ f₀' (hv.1 x) H
  obtain ⟨β, hβ⟩ := exists_prim P₀.A (fun i => m ⁻¹ᵁ L.U i) (fun k => f₀.left ⁻¹ᵁ m ⁻¹ᵁ L.U k) W
  have le : ∀ i k (O : P₀.A.left.Opens), O ≤ m ⁻¹ᵁ L.U i ⊓ f₀.left ⁻¹ᵁ m ⁻¹ᵁ L.U k →
      (snd (epsR K) P₀.A).left ⁻¹ᵁ O ≤ (snd (epsR K) P₀.A).left ⁻¹ᵁ (m ⁻¹ᵁ L.U i) ⊓
        (snd (epsR K) P₀.A).left ⁻¹ᵁ (f₀.left ⁻¹ᵁ m ⁻¹ᵁ L.U k) := fun i k O h =>
    le_inf ((snd (epsR K) P₀.A).left.preimage_mono (h.trans inf_le_left))
      ((snd (epsR K) P₀.A).left.preimage_mono (h.trans inf_le_right))
  refine ⟨fun i k => -β i k, fun i i' k => ?_, fun i k k' => ?_⟩
  · beta_reduce
    obtain ⟨O, hO⟩ : ∃ O, O = m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U i' ⊓ f₀.left ⁻¹ᵁ m ⁻¹ᵁ L.U k := ⟨_, rfl⟩
    rw [← hO]
    have h₁ : O ≤ m ⁻¹ᵁ L.U i ⊓ f₀.left ⁻¹ᵁ m ⁻¹ᵁ L.U k := hO.le.trans (inf_le_inf inf_le_left le_rfl)
    have h₂ : O ≤ m ⁻¹ᵁ L.U i' ⊓ f₀.left ⁻¹ᵁ m ⁻¹ᵁ L.U k := hO.le.trans (inf_le_inf inf_le_right le_rfl)
    obtain ⟨G, hG, e₁, e₂⟩ := pbT_g_transl P₀.A m L hw hdw (𝟙 _) i i' _ (hc i i') O (hO.le.trans inf_le_left)
    have r := hW i k i' k _ (le i k O h₁) (le i' k O h₂)
    have u₁ := pbT_g_self hL (((fst (epsR K) P₀.A ≫ v x) * (snd (epsR K) P₀.A ≫ f₀)).left ≫ m) k
      ((le i k O h₁).trans (inf_le_right.trans (transl_preimage P₀.A (hv.1 x) f₀ (m ⁻¹ᵁ L.U k)).ge))
    have u₂ := pbT_g_self hL ((snd (epsR K) P₀.A ≫ f₀).left ≫ m) k ((le i k O h₁).trans inf_le_right)
    have s := hβ i k i' k O h₁ h₂ G _ 1 0 hG isUnit_one
      (mul_congr r e₁ (u₁.trans (one_eq _ _)) e₂ (u₂.trans (map_one _).symm))
    rw [show pbT (𝟙 P₀.A : P₀.A ⟶ P₀.A).left (lc P₀.A.hom (fun y => F' y x) φ i i') O = _ from
      pbT_id _ O (hO.le.trans inf_le_left)] at s
    rw [rsT_neg, rsT_neg]
    linear_combination s
  · beta_reduce
    obtain ⟨O, hO⟩ : ∃ O, O = m ⁻¹ᵁ L.U i ⊓ f₀.left ⁻¹ᵁ m ⁻¹ᵁ L.U k ⊓ f₀.left ⁻¹ᵁ m ⁻¹ᵁ L.U k' := ⟨_, rfl⟩
    rw [← hO]
    have h₁ : O ≤ m ⁻¹ᵁ L.U i ⊓ f₀.left ⁻¹ᵁ m ⁻¹ᵁ L.U k := hO.le.trans inf_le_left
    have h₂ : O ≤ m ⁻¹ᵁ L.U i ⊓ f₀.left ⁻¹ᵁ m ⁻¹ᵁ L.U k' := hO.le.trans (inf_le_inf inf_le_left le_rfl)
    obtain ⟨G, hG, e₁, e₂⟩ := pbT_g_transl P₀.A m L (hv.1 x) (hdd x) f₀ k k' _ (hφ x k k') O
      (hO.le.trans fun _ hy => ⟨hy.1.2, hy.2⟩)
    have r := hW i k i k' _ (le i k O h₁) (le i k' O h₂)
    have u₁ := pbT_g_self hL (((fst (epsR K) P₀.A ≫ v x ≫ f₀') * (snd (epsR K) P₀.A ≫ 𝟙 P₀.A)).left ≫ m) i
      ((le i k O h₁).trans (inf_le_left.trans (transl_preimage P₀.A hw (𝟙 _) (m ⁻¹ᵁ L.U i)).ge))
    have u₂ := pbT_g_self hL ((snd (epsR K) P₀.A ≫ 𝟙 P₀.A).left ≫ m) i
      ((le i k O h₁).trans (inf_le_left.trans (by rw [Category.comp_id]; exact le_rfl)))
    have s := hβ i k i k' O h₁ h₂ 1 0 G _ isUnit_one hG
      (mul_congr r (u₂.trans (map_one _).symm) e₂ (u₁.trans (one_eq _ _)) e₁)
    rw [rsT_neg, rsT_neg]
    linear_combination -s

end GlobalTheory.KS.AdjDlog
end
