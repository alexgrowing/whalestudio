import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningFieldStructure
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS GlobalTheory.TangentOrigin GlobalTheory.SqZero GlobalTheory.LieBaseChange
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD pushR pullR fB)
open TrivSqZeroExt (inl inr)

noncomputable section

namespace GlobalTheory.InvFieldBasis

variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] {n : ℕ}

def expPt {B : Type} [CommRing B] [Algebra K B] (v : Fin n → (epsR K ⟶ G)) (e : Fin n → B)
    (he : ∀ i, e i * e i = 0) : sp (R₀ := K) B ⟶ G :=
  (List.ofFn fun i => (Chart.spMap (epsTo K (e i) (he i)) ≫ v i : sp (R₀ := K) B ⟶ G)).prod

variable {C : Type} [CommRing C] [Algebra K C]

theorem pushR_prodPts' (v : Fin n → (epsR K ⟶ G)) (c : Fin n → C) :
    pushR G (Chart.prodPts c (bcVec C v)) =
      expPt v (fun i => (inr (c i) : DualNumber C)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) := by
  unfold Chart.prodPts expPt
  have key : ∀ i, pushR G (Chart.spMap (Chart.scaleD (c i)) ≫ bcVec C v i) =
      (Chart.spMap (epsTo K (inr (c i) : DualNumber C) (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ v i :
        sp (R₀ := K) (DualNumber C) ⟶ G) := by
    intro i
    rw [Chart.pushR_spMap, pushR_bcVec, ← Category.assoc, Chart.spMap_comp]
    congr 2
    apply DualNumber.algHom_ext
    change Chart.scaleD (c i) (Chart.dualMapA K C (inr 1)) = epsTo K (inr (c i) : DualNumber C) _ (inr 1)
    rw [Chart.dualMapA_inr, map_one]
    simp only [Chart.scaleD]
    rw [show (inr 1 : DualNumber K) = DualNumber.eps from rfl, epsTo_eps, TrivSqZeroExt.map_inr,
      LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, _root_.mul_one]
  calc pushR G _ = pushRHom G (DualNumber C)
        (List.ofFn fun i => Chart.spMap (Chart.scaleD (c i)) ≫ bcVec C v i).prod := rfl
    _ = _ := by
      rw [map_list_prod, List.map_ofFn]
      exact congrArg List.prod (List.ofFn_inj.mpr (funext key))

theorem existsUnique_expPt [Smooth G.hom] {v : Fin n → (epsR K ⟶ G)} (hv : IsLieBasis v)
    (w : sp (R₀ := K) (DualNumber C) ⟶ G) (hw : Chart.spMap ((fstD C).restrictScalars K) ≫ w = 1) :
    ∃! c : Fin n → C,
      w = expPt v (fun i => (inr (c i) : DualNumber C)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) := by
  have hb : IsLieBasis (bcVec C v) :=
    Chart.isLieBasis_baseChange (algebraMap K C) (isGrpPullback_pullback G (fB K C)) hv
      (fun j => bcVec_left_fst v j)
  have hwT : Chart.IsTan (pullR (R' := C) G w) := by
    rw [isTan_iff_mem, Chart.pushR_pullR]
    exact mem_redKer_of_section _ ((Algebra.ofId C (DualNumber C)).restrictScalars K) (fun a => by simp) hw
  have hT : IsTangent (pullR (R' := C) G w) := (Chart.isTan_iff _).1 hwT
  have key : ∀ c : Fin n → C, IsLieComb c (bcVec C v) (pullR (R' := C) G w) ↔
      w = expPt v (fun i => (inr (c i) : DualNumber C)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) := by
    intro c
    rw [Chart.isLieComb_iff, ← pushR_prodPts']
    constructor
    · intro h'
      rw [← h', Chart.pushR_pullR]
    · intro h'
      apply Chart.pushR_inj (G := G)
      rw [Chart.pushR_pullR, h']
  obtain ⟨c, hc, hu⟩ := hb.2 _ hT
  exact ⟨c, (key c).1 hc, fun c' hc' => hu c' ((key c').2 hc')⟩

theorem preimage_translate {v : epsR K ⟶ G} (hv : IsTangent v) (W : G.left.Opens) :
    ((fst (epsR K) G ≫ v) * snd (epsR K) G).left ⁻¹ᵁ W = (snd (epsR K) G).left ⁻¹ᵁ W := by
  have e0w : Geo.Tor.spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (epsR K).hom = (𝟙_ (Over (Sp K))).hom := by
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  let e0 : 𝟙_ (Over (Sp K)) ⟶ epsR K := Over.homMk (Geo.Tor.spMap (TrivSqZeroExt.fstHom K K K).toRingHom) e0w
  have hev : e0 ≫ v = η := Over.OverMorphism.ext hv
  let J : G ⟶ epsR K ⊗ G := lift (toUnit G ≫ e0) (𝟙 G)
  have hJ1 : J ≫ ((fst (epsR K) G ≫ v) * snd (epsR K) G) = 𝟙 G := by
    rw [MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd, Category.assoc, hev]
    exact _root_.one_mul (𝟙 G)
  have hJ2 : J ≫ snd (epsR K) G = 𝟙 G := lift_snd _ _
  have hpb : IsPullback (snd (epsR K) G).left (fst (epsR K) G).left G.hom (epsR K).hom :=
    (IsPullback.of_hasPullback (epsR K).hom G.hom).flip
  have hs := GlobalTheory.ConstThickening.structure_dualNumber K G.left (epsR K ⊗ G).left G.hom (fst (epsR K) G).left
    (snd (epsR K) G).left J.left hpb
    (by simpa using congrArg (fun f => f.left) hJ2)
    (by simp [J, e0]; exact pullback.lift_fst _ _ _)
  have hc : ∀ {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens), f ⁻¹ᵁ (g ⁻¹ᵁ U) = (f ≫ g) ⁻¹ᵁ U :=
    fun _ _ _ => rfl
  have h3 : J.left ⁻¹ᵁ (((fst (epsR K) G ≫ v) * snd (epsR K) G).left ⁻¹ᵁ W) =
      J.left ⁻¹ᵁ ((snd (epsR K) G).left ⁻¹ᵁ W) := by
    rw [hc, hc, ← Over.comp_left, ← Over.comp_left, hJ1, hJ2]
  rw [← hs.1 (((fst (epsR K) G ≫ v) * snd (epsR K) G).left ⁻¹ᵁ W), h3, hs.1]

theorem evalPt_pbT {B : Type} [CommRing B] {Y Z : Scheme.{0}} (x : Sp B ⟶ Z) (f : Z ⟶ Y) {O : Y.Opens}
    {O' : Z.Opens} (h : O' ≤ f ⁻¹ᵁ O) (h' : ⊤ ≤ x ⁻¹ᵁ O') (y : Sp B ⟶ Y) (hy : x ≫ f = y)
    (h'' : ⊤ ≤ y ⁻¹ᵁ O) (s : Γ(Y, O)) : evalPt x O' h' (pbT f s O') = evalPt y O h'' s := by
  subst hy
  simp only [evalPt, pbT, dif_pos h]
  rw [← Scheme.Hom.appLE_comp_appLE (e₁ := h) (e₂ := h')]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]

private lemma evalPt_add {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Sp B ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a b : Γ(Z, O)) : evalPt x O h (a + b) = evalPt x O h a + evalPt x O h b := by
  unfold evalPt
  exact map_add _ a b

private lemma evalPt_mul {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Sp B ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a b : Γ(Z, O)) : evalPt x O h (a * b) = evalPt x O h a * evalPt x O h b := by
  unfold evalPt
  exact map_mul _ a b

private lemma evalPt_constFn' {B A : Type} [CommRing B] [CommRing A] {Z : Scheme.{0}} (x : Sp B ⟶ Z)
    (q : Z ⟶ Sp A) (φ : A →+* B) (hq : x ≫ q = Spec.map (CommRingCat.ofHom φ)) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a : A) : evalPt x O h (constFn q O a) = φ a := by
  unfold evalPt constFn
  have e1 : ∀ (g : Sp B ⟶ Sp A) (e : ⊤ ≤ g ⁻¹ᵁ ⊤), g.appLE ⊤ ⊤ e = g.appTop := fun g e => by
    simp only [Scheme.Hom.appLE]
    rw [show (homOfLE e).op = 𝟙 _ from Subsingleton.elim _ _]
    exact Category.comp_id _
  rw [← CommRingCat.comp_apply, ← Category.assoc]
  erw [Scheme.Hom.appLE_comp_appLE]
  rw [e1, hq, Scheme.ΓSpecIso_naturality]
  simp

variable {B : Type} [CommRing B] [Algebra K B]

theorem evalPt_translate {v : epsR K ⟶ G} (hv : IsTangent v)
    {dd : ∀ O : G.left.Opens, Γ(G.left, O) → Γ(G.left, O)} (hd : IsInvDer v dd) (e : B) (he : e * e = 0)
    (z : sp (R₀ := K) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O) :
    ∃ h' : ⊤ ≤ ((Chart.spMap (epsTo K e he) ≫ v : sp (R₀ := K) B ⟶ G) * z).left ⁻¹ᵁ O, ∀ f,
      evalPt _ O h' f = evalPt z.left O h f + e * evalPt z.left O h (dd O f) := by
  let t : sp (R₀ := K) B ⟶ epsR K ⊗ G := lift (Chart.spMap (epsTo K e he)) z
  have ht1 : t ≫ ((fst (epsR K) G ≫ v) * snd (epsR K) G) =
      (Chart.spMap (epsTo K e he) ≫ v : sp (R₀ := K) B ⟶ G) * z := by
    rw [MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd]
  have ht2 : t ≫ snd (epsR K) G = z := lift_snd _ _
  have ht3 : t ≫ fst (epsR K) G = Chart.spMap (epsTo K e he) := lift_fst _ _
  have hP := preimage_translate hv O
  have hc : ∀ {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens), f ⁻¹ᵁ (g ⁻¹ᵁ U) = (f ≫ g) ⁻¹ᵁ U :=
    fun _ _ _ => rfl
  have hO : t.left ⁻¹ᵁ ((snd (epsR K) G).left ⁻¹ᵁ O) = z.left ⁻¹ᵁ O := by
    rw [hc, ← Over.comp_left, ht2]
  have hO' : ((Chart.spMap (epsTo K e he) ≫ v : sp (R₀ := K) B ⟶ G) * z).left ⁻¹ᵁ O = z.left ⁻¹ᵁ O := by
    rw [← ht1, Over.comp_left, ← hc, hP, hO]
  have hT : ⊤ ≤ t.left ⁻¹ᵁ ((snd (epsR K) G).left ⁻¹ᵁ O) := hO ▸ h
  refine ⟨hO' ▸ h, fun f => ?_⟩
  have e1 : evalPt t.left _ hT (pbT (snd (epsR K) G).left f ((snd (epsR K) G).left ⁻¹ᵁ O)) =
      evalPt z.left O h f :=
    evalPt_pbT t.left _ le_rfl hT z.left (by rw [← Over.comp_left, ht2]) h f
  have e2 : evalPt t.left _ hT (pbT (snd (epsR K) G).left (dd O f) ((snd (epsR K) G).left ⁻¹ᵁ O)) =
      evalPt z.left O h (dd O f) :=
    evalPt_pbT t.left _ le_rfl hT z.left (by rw [← Over.comp_left, ht2]) h (dd O f)
  have e3 : evalPt t.left _ hT (constFn (R := DualNumber K) (fst (epsR K) G).left
      ((snd (epsR K) G).left ⁻¹ᵁ O) DualNumber.eps) = e := by
    rw [evalPt_constFn' t.left (fst (epsR K) G).left (epsTo K e he : DualNumber K →+* B)]
    · simp
    · rw [← Over.comp_left, ht3]
      rfl
  rw [← evalPt_pbT t.left ((fst (epsR K) G ≫ v) * snd (epsR K) G).left hP.ge hT
    ((Chart.spMap (epsTo K e he) ≫ v : sp (R₀ := K) B ⟶ G) * z).left (by rw [← Over.comp_left, ht1]) _ f,
    hd O f, evalPt_add, evalPt_mul, e1, e2, e3]

private lemma evalPt_congr' {B : Type} [CommRing B] {Z : Scheme.{0}} {x y : Sp B ⟶ Z} (hxy : x = y)
    (O : Z.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ O) (hy : ⊤ ≤ y ⁻¹ᵁ O) (s : Γ(Z, O)) : evalPt x O hx s = evalPt y O hy s := by
  subst hxy
  rfl

theorem evalPt_expPt {v : Fin n → (epsR K ⟶ G)} (hv : ∀ i, IsTangent (v i))
    {dd : Fin n → ∀ O : G.left.Opens, Γ(G.left, O) → Γ(G.left, O)} (hd : ∀ i, IsInvDer (v i) (dd i))
    (e : Fin n → B) (he : ∀ i j, e i * e j = 0)
    (z : sp (R₀ := K) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O) :
    ∃ h' : ⊤ ≤ (expPt v e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
      evalPt _ O h' f = evalPt z.left O h f + ∑ i, e i * evalPt z.left O h (dd i O f) := by
  induction n with
  | zero =>
    have h1 : expPt v e (fun i => he i i) * z = z := by
      simp only [expPt, List.ofFn_zero, List.prod_nil]
      exact _root_.one_mul z
    refine ⟨by rw [h1]; exact h, fun f => ?_⟩
    have hx : (expPt v e (fun i => he i i) * z).left = z.left := congrArg (fun w => w.left) h1
    exact (evalPt_congr' hx O _ h f).trans (by simp)
  | succ n ih =>
    have hs : expPt v e (fun i => he i i) * z =
        (Chart.spMap (epsTo K (e 0) (he 0 0)) ≫ v 0 : sp (R₀ := K) B ⟶ G) *
          (expPt (fun i => v i.succ) (fun i => e i.succ) (fun i => he i.succ i.succ) * z) := by
      rw [← _root_.mul_assoc]
      congr 1
      simp only [expPt, List.ofFn_succ, List.prod_cons]
    obtain ⟨h1, H1⟩ := ih (v := fun i => v i.succ) (hv := fun i => hv i.succ) (dd := fun i => dd i.succ)
      (hd := fun i => hd i.succ) (e := fun i => e i.succ) (he := fun i j => he i.succ j.succ)
    obtain ⟨h2, H2⟩ := evalPt_translate (hv 0) (hd 0) (e 0) (he 0 0) _ O h1
    refine ⟨by rw [hs]; exact h2, fun f => ?_⟩
    have hx : (expPt v e (fun i => he i i) * z).left =
        ((Chart.spMap (epsTo K (e 0) (he 0 0)) ≫ v 0 : sp (R₀ := K) B ⟶ G) *
          (expPt (fun i => v i.succ) (fun i => e i.succ) (fun i => he i.succ i.succ) * z)).left :=
      congrArg (fun w => w.left) hs
    rw [evalPt_congr' hx O _ h2 f, H2 f, H1 f, H1 (dd 0 O f), Fin.sum_univ_succ]
    have hz : e 0 * ∑ i : Fin n, e i.succ * evalPt z.left O h (dd i.succ O (dd 0 O f)) = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun i _ => by rw [← _root_.mul_assoc, he 0 i.succ]; simp
    rw [_root_.mul_add, hz]
    ring

end GlobalTheory.InvFieldBasis
