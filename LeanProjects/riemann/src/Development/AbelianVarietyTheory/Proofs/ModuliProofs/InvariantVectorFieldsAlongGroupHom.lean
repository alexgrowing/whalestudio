import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningFieldStructure
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieCombIffProd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory.PowLie (sc zeroPt isTangent_iff)
noncomputable section
namespace GlobalTheory.KS.InvHom

theorem pbT_pbT {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) {O₀ : X.Opens} {O₁ : Y.Opens} {O₂ : Z.Opens}
    (h₁ : O₁ ≤ g ⁻¹ᵁ O₀) (h₂ : O₂ ≤ f ⁻¹ᵁ O₁) (s : Γ(X, O₀)) :
    pbT f (pbT g s O₁) O₂ = pbT (f ≫ g) s O₂ := by
  have h₃ : O₂ ≤ (f ≫ g) ⁻¹ᵁ O₀ := h₂.trans (f.preimage_mono h₁)
  rw [pbT_of_le g h₁, pbT_of_le f h₂, pbT_of_le _ h₃]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_comp_appLE f g O₀ O₁ O₂ h₁ h₂)

theorem pbT_app {Y Z : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) :
    pbT f s (f ⁻¹ᵁ O₀) = (f.app O₀).hom s := by
  rw [pbT_of_le f le_rfl, Scheme.Hom.app_eq_appLE]

theorem constFn_spMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {Y : Scheme.{0}}
    (q : Y ⟶ Sp R') (O : Y.Opens) (a : R) : constFn (q ≫ spMap φ) O a = constFn q O (φ a) := by
  have h1 := congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE q (spMap φ) ⊤ ⊤ O (fun _ _ => trivial) (fun _ _ => trivial))
  have h2 := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  refine h1.symm.trans ?_
  exact congrArg (fun t => (q.appLE ⊤ O (fun _ _ => trivial)).hom t) h2.symm

theorem constFn_mul {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) (O : Y.Opens) (a b : R) :
    constFn q O (a * b) = constFn q O a * constFn q O b := by
  simp [constFn]

theorem constFn_zero {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Sp R) (O : Y.Opens) :
    constFn q O (0 : R) = 0 := by
  simp [constFn]

variable {K : Type} [Field K]

def jA (A : Over (Sp K)) : A ⟶ epsR K ⊗ A := lift (toUnit A ≫ zeroPt K) (𝟙 A)

theorem thick (A : Over (Sp K)) :
    (∀ O : (epsR K ⊗ A).left.Opens, (snd (epsR K) A).left ⁻¹ᵁ ((jA A).left ⁻¹ᵁ O) = O) ∧
    ∀ (O : A.left.Opens) (F : Γ((epsR K ⊗ A).left, (snd (epsR K) A).left ⁻¹ᵁ O)),
      ∃! ab : Γ(A.left, O) × Γ(A.left, O), F = ((snd (epsR K) A).left.app O).hom ab.1 +
        constFn (R := DualNumber K) (fst (epsR K) A).left _ DualNumber.eps *
          ((snd (epsR K) A).left.app O).hom ab.2 := by
  have h := GlobalTheory.ConstThickening.structure_dualNumber K A.left (epsR K ⊗ A).left A.hom (fst (epsR K) A).left (snd (epsR K) A).left
    (jA A).left (IsPullback.of_hasPullback (epsR K).hom A.hom).flip
    (by rw [← Over.comp_left, jA, lift_snd]; rfl)
    (by
      have : jA A ≫ fst (epsR K) A = toUnit A ≫ zeroPt K := by rw [jA, lift_fst]
      exact congrArg CommaMorphism.left this)
  exact ⟨h.1, h.2.2⟩

abbrev tr {A : Over (Sp K)} [GrpObj A] (v : epsR K ⟶ A) : epsR K ⊗ A ⟶ A :=
  (fst (epsR K) A ≫ v) * snd (epsR K) A

variable {A : Over (Sp K)} [GrpObj A]

theorem tr_preimage {v : epsR K ⟶ A} (hv : IsTangent v) (W : A.left.Opens) :
    (tr v).left ⁻¹ᵁ W = (snd (epsR K) A).left ⁻¹ᵁ W := by
  have h : jA A ≫ tr v = 𝟙 A := by
    rw [MonObj.comp_mul, ← Category.assoc, jA, lift_fst, lift_snd, Category.assoc,
      (isTangent_iff v).1 hv]
    exact _root_.one_mul (𝟙 A)
  rw [← (thick A).1 ((tr v).left ⁻¹ᵁ W), ← Scheme.Hom.comp_preimage (jA A).left, ← Over.comp_left, h]
  rfl

theorem pull {v : epsR K ⟶ A} (hv : IsTangent v) {dd} (hd : IsInvDer v dd) {Z : Over (Sp K)}
    (S : Z ⟶ epsR K ⊗ A) (W : A.left.Opens) (f : Γ(A.left, W)) (O : Z.left.Opens)
    (hO : O ≤ (S ≫ snd (epsR K) A).left ⁻¹ᵁ W) :
    pbT (S ≫ tr v).left f O = pbT (S ≫ snd (epsR K) A).left f O +
      constFn (R := DualNumber K) (S ≫ fst (epsR K) A).left O DualNumber.eps *
        pbT (S ≫ snd (epsR K) A).left (dd W f) O := by
  have hO' : O ≤ S.left ⁻¹ᵁ ((snd (epsR K) A).left ⁻¹ᵁ W) := hO
  have h := congrArg (fun s => pbT S.left s O) (hd W f)
  simp only [pbT_add, pbT_mul] at h
  rw [pbT_pbT _ _ (tr_preimage hv W).ge hO', pbT_pbT _ _ le_rfl hO', pbT_pbT _ _ le_rfl hO',
    pbT_constFn _ _ hO'] at h
  exact h

theorem tan_one : IsTangent (1 : epsR K ⟶ A) := by
  rw [isTangent_iff, MonObj.comp_one]
  simp [Hom.one_def]

theorem tan_mul {u u' : epsR K ⟶ A} (hu : IsTangent u) (hu' : IsTangent u') : IsTangent (u * u') := by
  have e : (η[A] : _ ⟶ A) = 1 := by simp [Hom.one_def]
  rw [isTangent_iff] at *
  rw [MonObj.comp_mul, hu, hu', e, _root_.one_mul]

theorem tan_sc {v : epsR K ⟶ A} (hv : IsTangent v) (c : K) : IsTangent (sc c ≫ v) := by
  have e : zeroPt K ≫ sc c = zeroPt K := by
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  rw [isTangent_iff] at *
  rw [← Category.assoc, e, hv]

theorem inv_one : IsInvDer (1 : epsR K ⟶ A) (fun _ _ => 0) := by
  intro W f
  rw [MonObj.comp_one, _root_.one_mul, pbT_zero, mul_zero, add_zero]

theorem inv_mul {u u' : epsR K ⟶ A} (hu : IsTangent u) (hu' : IsTangent u') {d d'}
    (hd : IsInvDer u d) (hd' : IsInvDer u' d') : IsInvDer (u * u') (fun W f => d W f + d' W f) := by
  intro W f
  have e : (fst (epsR K) A ≫ (u * u')) * snd (epsR K) A = lift (fst _ _) (tr u') ≫ tr u := by
    rw [MonObj.comp_mul, MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst, _root_.mul_assoc]
  have h := pull hu hd (lift (fst _ _) (tr u')) W f ((snd (epsR K) A).left ⁻¹ᵁ W)
    (by rw [lift_snd]; exact (tr_preimage hu' W).ge)
  rw [lift_snd, lift_fst, hd' W f, hd' W (d W f)] at h
  rw [e, h, pbT_add]
  have h2 : constFn (R := DualNumber K) (fst (epsR K) A).left ((snd (epsR K) A).left ⁻¹ᵁ W) DualNumber.eps *
      constFn (R := DualNumber K) (fst (epsR K) A).left ((snd (epsR K) A).left ⁻¹ᵁ W) DualNumber.eps = 0 := by
    rw [← constFn_mul, DualNumber.eps_mul_eps, constFn_zero]
  linear_combination (pbT (snd (epsR K) A).left (d' W (d W f)) ((snd (epsR K) A).left ⁻¹ᵁ W)) * h2

theorem inv_sc {v : epsR K ⟶ A} (hv : IsTangent v) {d} (hd : IsInvDer v d) (c : K) :
    IsInvDer (sc c ≫ v) (fun W f => constFn A.hom W c * d W f) := by
  intro W f
  have e : (fst (epsR K) A ≫ (sc c ≫ v)) * snd (epsR K) A = (sc c ▷ A) ≫ tr v := by
    rw [MonObj.comp_mul, whiskerRight_snd, whiskerRight_fst_assoc]
  have h := pull hv hd (sc c ▷ A) W f ((snd (epsR K) A).left ⁻¹ᵁ W) (by rw [whiskerRight_snd])
  rw [whiskerRight_snd, whiskerRight_fst] at h
  rw [e, h, pbT_mul, pbT_constFn _ _ le_rfl, ← _root_.mul_assoc]
  congr 2
  have w : (snd (epsR K) A).left ≫ A.hom = (fst (epsR K) A).left ≫ spMap (algebraMap K (DualNumber K)) :=
    (Over.w (snd (epsR K) A)).trans (Over.w (fst (epsR K) A)).symm
  have e2 : epsScaleR c (DualNumber.eps : DualNumber K) = DualNumber.eps * algebraMap K (DualNumber K) c := by
    ext <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  rw [w]
  refine (constFn_spMap (epsScaleR c) (fst (epsR K) A).left _ _).trans ?_
  rw [e2]
  refine (constFn_mul _ _ _ _).trans ?_
  congr 1
  exact (constFn_spMap _ _ _ _).symm

theorem inv_prod : ∀ {n : ℕ} (u : Fin n → (epsR K ⟶ A))
    (d : Fin n → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), (∀ i, IsTangent (u i)) →
    (∀ i, IsInvDer (u i) (d i)) →
      IsTangent (List.ofFn u).prod ∧ IsInvDer (List.ofFn u).prod (fun W f => ∑ i, d i W f)
  | 0, u, d, _, _ => by
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨tan_one, inv_one⟩
  | n + 1, u, d, hu, hd => by
    obtain ⟨h₁, h₂⟩ := inv_prod (fun i => u i.succ) (fun i => d i.succ) (fun i => hu _) (fun i => hd _)
    simp only [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact ⟨tan_mul (hu 0) h₁, inv_mul (hu 0) h₁ (hd 0) h₂⟩

theorem inv_comb {n : ℕ} {c : Fin n → K} {v : Fin n → (epsR K ⟶ A)} {w : epsR K ⟶ A}
    {d : Fin n → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)} (hv : ∀ i, IsTangent (v i))
    (hd : ∀ i, IsInvDer (v i) (d i)) (hw : IsLieComb c v w) :
    IsTangent w ∧ IsInvDer w (fun W f => ∑ i, constFn A.hom W (c i) * d i W f) := by
  obtain ⟨u, hu, rfl⟩ := hw
  have e : ∀ i, u i = sc (c i) ≫ v i := fun i => Over.OverMorphism.ext (hu i)
  exact inv_prod u (fun i W f => constFn A.hom W (c i) * d i W f) (fun i => e i ▸ tan_sc (hv i) _)
    (fun i => e i ▸ inv_sc (hv i) (hd i) _)

theorem inv_hom {A₁ : Over (Sp K)} [GrpObj A₁] (f : A₁ ⟶ A) [IsMonHom f] {w : epsR K ⟶ A₁}
    (hw : IsTangent w) (hwf : IsTangent (w ≫ f)) {dw D} (hdw : IsInvDer w dw) (hD : IsInvDer (w ≫ f) D)
    (W : A.left.Opens) (h : Γ(A.left, W)) :
    dw (f.left ⁻¹ᵁ W) ((f.left.app W).hom h) = (f.left.app W).hom (D W h) := by
  have e : (epsR K ◁ f) ≫ tr (w ≫ f) = tr w ≫ f := by
    rw [MonObj.comp_mul, MonObj.mul_comp, whiskerLeft_snd, whiskerLeft_fst_assoc, Category.assoc]
  have h1 := pull hwf hD (epsR K ◁ f) W h ((snd (epsR K) A₁).left ⁻¹ᵁ (f.left ⁻¹ᵁ W))
    (by rw [whiskerLeft_snd]; exact le_rfl)
  rw [e, whiskerLeft_snd, whiskerLeft_fst, Over.comp_left, Over.comp_left,
    ← pbT_pbT _ _ le_rfl (tr_preimage hw _).ge, ← pbT_pbT _ _ le_rfl le_rfl h,
    ← pbT_pbT _ _ le_rfl le_rfl (D W h), pbT_app f.left, pbT_app f.left, pbT_app, pbT_app] at h1
  have h2 := hdw (f.left ⁻¹ᵁ W) ((f.left.app W).hom h)
  rw [pbT_app, pbT_app] at h2
  have := ((thick A₁).2 (f.left ⁻¹ᵁ W) _).unique (y₁ := (_, _)) (y₂ := (_, _)) h2 h1
  exact congrArg Prod.snd this

theorem invDer_along_hom : ∀ (K : Type) [Field K] (A₁ A₀ : Over (Sp K)) [GrpObj A₁] [GrpObj A₀] (f : A₁ ⟶ A₀) (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)) (w : epsR K ⟶ A₁) (dw : ∀ O : A₁.left.Opens, Γ(A₁.left, O) → Γ(A₁.left, O)) (c : Fin g → K), IsMonHom f → (∀ a, IsTangent (v a)) → IsTangent w → (∀ a, IsInvDer (v a) (dd a)) → IsInvDer w dw → IsLieComb c v (w ≫ f) → ∀ (W : A₀.left.Opens) (h : Γ(A₀.left, W)), dw (f.left ⁻¹ᵁ W) ((f.left.app W).hom h) = ∑ a, constFn A₁.hom _ (c a) * (f.left.app W).hom (dd a W h) := by
  intro K _ A₁ A₀ _ _ f g v dd w dw c hf hv hw hdd hdw hc W h
  obtain ⟨h₁, h₂⟩ := inv_comb hv hdd hc
  rw [inv_hom f hw h₁ hdw h₂, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, ← pbT_app f.left (constFn A₀.hom W (c a)), pbT_constFn _ _ le_rfl, Over.w f]

end GlobalTheory.KS.InvHom
end
